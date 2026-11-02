import calendar
from datetime import datetime, timedelta, timezone
from difflib import SequenceMatcher
import html
import ipaddress
import json
import logging
import os
from pathlib import Path
import random
import re
import socket
import sys
import time
from typing import Literal
import unicodedata
from urllib.parse import parse_qsl, urlencode, urljoin, urlsplit

import feedparser
from google import genai
from google.genai import errors as genai_errors
from google.genai import types
from pydantic import BaseModel, Field, ValidationError, field_validator
import trafilatura
import urllib3

# Nastavení logování
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S",
)
logger = logging.getLogger(__name__)

# =====================================================================
# KONFIGURACE A ZDROJE
# =====================================================================

RSS_FEEDS = {
    "BleepingComputer": "https://www.bleepingcomputer.com/feed/",
    "The Hacker News": "https://feeds.feedburner.com/TheHackersNews",
    "CISA Advisories": "https://www.cisa.gov/cybersecurity-advisories/all.xml",
    "SANS ISC": "https://isc.sans.edu/rssfeed_full.xml",
    "Dark Reading": "https://www.darkreading.com/rss.xml",
    "Krebs on Security": "https://krebsonsecurity.com/feed/",
}

# Povolené domény pro stahování i výsledné odkazy (zabraňuje DNS rebindingu a podvrženým URL).
ALLOWED_DOMAINS = (
    "bleepingcomputer.com",
    "thehackernews.com",
    "feedburner.com",
    "feedproxy.google.com",
    "cisa.gov",
    "sans.edu",
    "darkreading.com",
    "krebsonsecurity.com",
)

HOURS_LOOKBACK = 36
MAX_CHARS_PER_ARTICLE = 4200  # Pokryje celý běžný článek pro věrný překlad bez přetížení TPM limitu
DOCS_DIR = Path("docs")
ARCHIVE_DIR = DOCS_DIR / "archive"
PROMPT_FILE = Path("prompt.txt")

# Kaskáda modelů s aktivní Free Tier kvótou
MODELS = (
    "gemini-3.6-flash",
    "gemini-3.5-flash-lite",
    "gemini-3.1-flash-lite",
)
RETRYABLE_HTTP_CODES = {429, 500, 502, 503, 504}

# --- Bezpečnostní limity (ochrana proti resource exhaustion) ---
MAX_ENTRIES_PER_FEED = 20
MAX_REDIRECTS = 3
CONNECT_TIMEOUT = 5              # s
READ_TIMEOUT = 10                # s (na jedno čtení ze socketu)
TOTAL_TIMEOUT = 20               # s (celkový strop na jedno stažení včetně redirectů)
MAX_ARTICLE_BYTES = 2 * 1024 * 1024
MAX_FEED_BYTES = 5 * 1024 * 1024
MAX_ZPRAV = 25
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/152.0.0.0 Safari/537.36"
)
CVE_RE = re.compile(r"^CVE-\d{4}-\d{4,7}$")
_TRACKING_RE = re.compile(r"^(utm_.+|fbclid|gclid|mc_cid|mc_eid)$", re.IGNORECASE)

# =====================================================================
# BEZPEČNOSTNÍ POMOCNÉ FUNKCE (URL validace, SSRF, sanitizace)
# =====================================================================

def is_http_url(url: str) -> bool:
  """Povolí pouze http(s) URL bez řídicích znaků, mezer, <>\"'` a bez user:pass@."""
  if not isinstance(url, str) or len(url) > 2048 or re.search(r"[\x00-\x20\x7f\\<>\"'`]", url):
    return False
  try:
    p = urlsplit(url)
    return (p.scheme.lower() in ("http", "https") and bool(p.hostname)
            and p.username is None and p.password is None)
  except ValueError:
    return False


def is_allowed_host(hostname: str | None) -> bool:
  """Povolí jen domény a subdomény ze seznamu ALLOWED_DOMAINS."""
  if not hostname:
    return False
  h = hostname.lower().rstrip(".")
  return any(h == d or h.endswith("." + d) for d in ALLOWED_DOMAINS)


def is_allowed_url(url: str) -> bool:
  """Ověří, že URL je platná http(s) adresa a její host patří do ALLOWED_DOMAINS."""
  if not is_http_url(url):
    return False
  try:
    return is_allowed_host(urlsplit(url).hostname)
  except ValueError:
    return False


def is_public_ip(ip_str: str) -> bool:
  ip = ipaddress.ip_address(ip_str.split("%")[0])
  if isinstance(ip, ipaddress.IPv6Address) and ip.ipv4_mapped:
    ip = ip.ipv4_mapped
  return ip.is_global and not ip.is_multicast


def is_safe_url(url: str) -> bool:
  """http(s), povolená doména, port 80/443 a VŠECHNY IP, na které host překládá, jsou veřejné."""
  if not is_allowed_url(url):
    return False
  try:
    p = urlsplit(url)
    if p.port not in (None, 80, 443):
      return False
    infos = socket.getaddrinfo(
        p.hostname,
        p.port or (443 if p.scheme.lower() == "https" else 80),
        type=socket.SOCK_STREAM,
    )
  except (ValueError, UnicodeError, OSError):
    return False
  addrs = {i[4][0] for i in infos}
  return bool(addrs) and all(is_public_ip(a) for a in addrs)


_HEADERS = urllib3.util.make_headers(user_agent=USER_AGENT, accept_encoding=True)
_HEADERS["Accept"] = "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"
_HEADERS["Accept-Language"] = "en-US,en;q=0.9,cs;q=0.8"

_HTTP = urllib3.PoolManager(
    timeout=urllib3.Timeout(connect=CONNECT_TIMEOUT, read=READ_TIMEOUT),
    retries=False,
    headers=_HEADERS,
)


def safe_fetch(url: str, max_bytes: int = MAX_ARTICLE_BYTES) -> bytes | None:
  """Stažení s celkovým deadline, ruční kontrolou KAŽDÉHO redirectu a limitem velikosti."""
  deadline = time.monotonic() + TOTAL_TIMEOUT
  for _ in range(MAX_REDIRECTS + 1):
    remaining = deadline - time.monotonic()
    if remaining <= 0:
      logger.warning(f"Vypršel celkový časový limit (deadline): {url[:120]}")
      return None
    if not is_safe_url(url):
      logger.warning(f"Zablokováno (nebezpečná nebo nepovolená URL): {url[:120]}")
      return None
    req_timeout = urllib3.Timeout(
        connect=min(CONNECT_TIMEOUT, remaining),
        read=min(READ_TIMEOUT, remaining),
    )
    try:
      resp = _HTTP.request("GET", url, redirect=False, preload_content=False, timeout=req_timeout)
    except (urllib3.exceptions.HTTPError, ValueError) as e:
      logger.warning(f"Chyba stahování {url[:120]}: {e}")
      return None
    try:
      if resp.status in (301, 302, 303, 307, 308):
        location = resp.headers.get("Location")
        if not location:
          return None
        url = urljoin(url, location)
        continue  # další hop se znovu validuje (allowlist domén + veřejná IP)
      if resp.status != 200:
        logger.warning(f"HTTP status {resp.status} pro {url[:120]}")
        return None
      ctype = resp.headers.get("Content-Type", "").lower()
      if ctype and not any(t in ctype for t in ("html", "xml", "text/", "rss", "atom", "octet-stream")):
        logger.warning(f"Nepovolený Content-Type '{ctype}' pro {url[:120]}")
        return None
      clen = resp.headers.get("Content-Length")
      if clen and clen.isdigit() and int(clen) > max_bytes:
        logger.warning(f"Odpověď odmítnuta podle Content-Length ({clen} B > {max_bytes} B): {url[:120]}")
        return None
      chunks, size = [], 0
      for chunk in resp.stream(65536, decode_content=True):
        size += len(chunk)
        if size > max_bytes or time.monotonic() > deadline:
          logger.warning(f"Překročen limit velikosti/času při čtení: {url[:120]}")
          return None
        chunks.append(chunk)
      return b"".join(chunks)
    except (urllib3.exceptions.HTTPError, OSError) as e:
      logger.warning(f"Chyba čtení {url[:120]}: {e}")
      return None
    finally:
      resp.close()
      resp.release_conn()
  logger.warning("Příliš mnoho redirectů.")
  return None


_INJECTION_RE = re.compile(
    r"(?:ignore|disregard|forget|override)\s+(?:all\s+|any\s+|the\s+)?(?:previous|prior|above|earlier)\s+(?:instructions?|prompts?|rules?)"
    r"|system\s+prompt|developer\s+message|you\s+are\s+now|new\s+instructions?"
    r"|ignoruj\s+(?:všechny\s+)?(?:předchozí|předešlé)|zapomeň\s+(?:na\s+)?(?:předchozí|instrukce)|nové\s+instrukce"
    r"|(?:^|\n)\s*(?:system|assistant|user)\s*:",
    re.IGNORECASE,
)


def sanitize_untrusted(text: str, max_len: int) -> str:
  """Sanitizace nedůvěryhodného textu z internetu před vložením do promptu."""
  text = unicodedata.normalize("NFKC", text)
  text = "".join(c for c in text
                 if c in "\n\t" or unicodedata.category(c) not in ("Cc", "Cf", "Co", "Cs"))
  text = text.replace("<", "‹").replace(">", "›")
  text, n = _INJECTION_RE.subn("[REDACTED]", text)
  if n:
    logger.warning(f"Sanitizace: vyřazeno {n} podezřelých frází (možná prompt injection).")
  text = re.sub(r"[ \t]+", " ", text)
  text = re.sub(r"\n{3,}", "\n\n", text)
  return text.strip()[:max_len]

# =====================================================================
# PYDANTIC SCHÉMATA (pro Gemini response_schema)
# =====================================================================

class Zdroj(BaseModel):
  nazev: str = Field(description="Název portálu nebo zdroje (např. BleepingComputer, CISA).")
  url: str = Field(description="Přesná URL článku, doslova opsaná z tagu <url> ve vstupu.")

  @field_validator("url")
  @classmethod
  def _only_http(cls, v: str) -> str:
    if not is_http_url(v):
      raise ValueError("URL musí mít schéma http:// nebo https://")
    return v

class RychlyVycuc(BaseModel):
  podstata: str = Field(description="Stručné shrnutí (1-2 věty), o co přesně jde a co se stalo.")
  cil: str = Field(description="Kdo nebo co je cílem (konkrétní OS, enterprise služba, sektor).")
  dopad_laici: str = Field(description="1-2 věty bez žargonu pro člověka bez IT znalostí: co hrozba znamená pro běžné lidi, firmy a služby, a zda mají něco dělat.")

class TechnickyKontext(BaseModel):
  detailni_preklad: str = Field(description="Věrný, přímý a plynulý český překlad samotného zdrojového článku (3 až 6 odstavců oddělených prázdným řádkem). Přelož vše, co se v článku píše, včetně citací, časové osy, verzí a detailů.")
  jak_to_funguje: str = Field(description="Technický rozbor útoku nebo zranitelnosti na úrovni architektury/kódu/systému.")
  mitre: list[str] = Field(description="Seznam relevantních MITRE ATT&CK technik (jen explicitně uvedené nebo si jsi jistý).")
  mitigace: list[str] = Field(description="Konkrétní technická doporučení k obraně, patchování nebo detekci.")

class PolozkaSlovnicku(BaseModel):
  pojem: str = Field(description="Odborný termín nebo zkratka, která je reálně použitá ve vygenerovaném textu této zprávy.")
  vysvetleni: str = Field(description="Srozumitelné vysvětlení pojmu v kontextu zprávy.")

class Zprava(BaseModel):
  poradi: int = Field(description="Pořadí zprávy dle závažnosti (od 1).")
  titulek: str = Field(description="Výstižný český titulek události.")
  kategorie: Literal["zero-day", "malware", "apt", "data-breach"] = Field(description="Kategorie hrozby.")
  zavaznost_skore: int = Field(ge=1, le=10, description="Vypočtené skóre závažnosti v rozsahu 1 až 10, přesně podle rozpisu bodů.")
  zavaznost_slova: Literal["NÍZKÁ", "STŘEDNÍ", "VYSOKÁ", "KRITICKÁ"] = Field(description="Slovní vyjádření odvozené ze skóre.")
  zavaznost_zduvodneni: str = Field(description="Transparentní rozpad bodů (např. '+3 In the wild...').")
  aktivne_zneuzivano: bool = Field(description="True POUZE pokud zdrojový článek výslovně uvádí zneužívání v praxi.")
  cve: list[str] = Field(description="Seznam CVE, která doslova stojí ve vstupu.")
  zdroje: list[Zdroj] = Field(description="Seznam zdrojových článků.")
  rychly_vycuc: RychlyVycuc
  technicky_kontext: TechnickyKontext
  slovnicek: list[PolozkaSlovnicku] = Field(description="Slovníček VŠECH odborných pojmů a zkratek použitých v textu zprávy.")
  jistota_extrakce: Literal["VYSOKÁ", "STŘEDNÍ", "NÍZKÁ"] = Field(description="Míra jistoty modelu ohledně extrahovaných dat.")

  @field_validator("zdroje", mode="before")
  @classmethod
  def _drop_bad_sources(cls, v):
    ok = []
    for item in v or []:
      try:
        ok.append(Zdroj.model_validate(item))
      except ValidationError:
        logger.warning("Zahazuji zdroj s nevalidní URL.")
    return ok

  @field_validator("cve")
  @classmethod
  def _valid_cve(cls, v: list[str]) -> list[str]:
    return [c.strip().upper() for c in v if CVE_RE.match(c.strip().upper())]

class DenniSvodka(BaseModel):
  zpravy: list[Zprava] = Field(description="Seznam zpracovaných a deduplikovaných bezpečnostních zpráv.")

# =====================================================================
# KROK 1 & 2: STAŽENÍ RSS A EXTRAKCE TEXTU (TRAFILATURA)
# =====================================================================

def parse_entry_date(entry) -> datetime | None:
  time_struct = getattr(entry, "published_parsed", None) or getattr(entry, "updated_parsed", None)
  if time_struct:
    timestamp = calendar.timegm(time_struct)
    return datetime.fromtimestamp(timestamp, tz=timezone.utc)
  return None

def fetch_articles() -> list[dict]:
  cutoff_time = datetime.now(timezone.utc) - timedelta(hours=HOURS_LOOKBACK)
  raw_articles = []

  for source_name, feed_url in RSS_FEEDS.items():
    logger.info(f"Stahuji RSS: {source_name} ({feed_url})")
    kept_for_feed = 0
    try:
      feed_bytes = safe_fetch(feed_url, MAX_FEED_BYTES)
      if not feed_bytes:
        logger.warning(f"Feed {source_name} se nepodařilo bezpečně stáhnout.")
        continue
      feed = feedparser.parse(feed_bytes)

      for entry in feed.entries[:MAX_ENTRIES_PER_FEED]:
        pub_date = parse_entry_date(entry)
        if pub_date and pub_date < cutoff_time:
          continue

        url = str(getattr(entry, "link", "")).strip()
        title = str(getattr(entry, "title", "Bez názvu")).strip()
        if not is_allowed_url(url):
          logger.warning(f"Přeskakuji článek s nepovolenou URL: {url[:120]}")
          continue

        downloaded = safe_fetch(url)
        full_text = ""
        if downloaded:
          full_text = trafilatura.extract(downloaded, include_comments=False, include_tables=True, no_fallback=False) or ""

        if not full_text:
          summary = str(getattr(entry, "summary", ""))[:20000]
          full_text = re.sub(r"<[^>]+>", " ", summary).strip()

        if len(full_text) < 100:
          continue

        cves = sorted(set(c.upper() for c in re.findall(r"CVE-\d{4}-\d{4,7}", f"{title} {full_text}", re.IGNORECASE)))

        raw_articles.append({
            "source": source_name,
            "title": sanitize_untrusted(title, 200),
            "url": url,
            "text": sanitize_untrusted(full_text, MAX_CHARS_PER_ARTICLE),
            "cves": cves,
        })
        kept_for_feed += 1

      logger.info(f"Feed {source_name}: použito {kept_for_feed} článků (celkem v RSS: {len(feed.entries)}).")
    except Exception as e:
      logger.error(f"Chyba při zpracování feedu {source_name}: {e}")

  return raw_articles

# =====================================================================
# KROK 3: DEDUPLIKACE A SESTAVENÍ SUROVÉHO TEXTU
# =====================================================================

def are_articles_similar(a1: dict, a2: dict) -> bool:
  if a1["cves"] and a2["cves"]:
    if set(a1["cves"]).intersection(set(a2["cves"])):
      return True
  ratio = SequenceMatcher(None, a1["title"].lower(), a2["title"].lower()).ratio()
  return ratio >= 0.68

def deduplicate_and_format(articles: list[dict]) -> str:
  clusters: list[list[dict]] = []
  for article in articles:
    placed = False
    for cluster in clusters:
      if any(are_articles_similar(article, existing) for existing in cluster):
        cluster.append(article)
        placed = True
        break
    if not placed:
      clusters.append([article])

  blocks = []
  for idx, cluster in enumerate(clusters, start=1):
    all_cves = sorted({cve for art in cluster for cve in art["cves"]})
    items = [
        f'<clanek zdroj="{art["source"]}">\n<titulek>{art["title"]}</titulek>\n'
        f'<url>{art["url"]}</url>\n<text>\n{art["text"]}\n</text>\n</clanek>'
        for art in cluster
    ]
    blocks.append(f'<udalost id="{idx}" detekovana_cve="{", ".join(all_cves) or "žádná"}">\n'
                  + "\n".join(items) + "\n</udalost>")

  return "\n\n".join(blocks)

# =====================================================================
# KROK 4: VOLÁNÍ GEMINI API (kaskáda modelů + exponenciální backoff)
# =====================================================================

def _is_retryable(e: Exception) -> bool:
  if isinstance(e, genai_errors.ServerError):
    return True
  return getattr(e, "code", None) in RETRYABLE_HTTP_CODES


def analyze_with_gemini(raw_rss_text: str, today_display: str) -> DenniSvodka:
  api_key = os.environ.get("GEMINI_API_KEY")
  if not api_key:
    logger.error("Kritická chyba: Chybí proměnná prostředí GEMINI_API_KEY.")
