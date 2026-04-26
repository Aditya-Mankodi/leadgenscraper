"""
Multi-source B2B lead engine for small digital-marketing agencies (US / UK / CA).

Sources: public directory listing pages + Google Maps. No paid APIs.
Enriches from agency homepages (email, phone, owner hints).

Requires: pip install playwright && playwright install chromium
"""

from __future__ import annotations

import asyncio
import csv
import logging
import random
import re
import time
from dataclasses import dataclass, field
from typing import Any, Optional
from urllib.parse import quote_plus, urlparse, urlunparse

from playwright.async_api import (
    BrowserContext,
    Page,
    TimeoutError as PWTimeout,
    async_playwright,
)

# ── Logging ─────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger(__name__)

# ── Config ───────────────────────────────────────────────────────────────────
OUTPUT_FILE = "leads.csv"
DELAY_MIN = 1.0
DELAY_MAX = 3.0
MAX_SCROLL_ATTEMPTS = 40
WEBSITE_TIMEOUT = 15_000
MAPS_TIMEOUT = 20_000
DIRECTORY_TIMEOUT = 25_000
MAX_DIRECTORY_PAGES = 10
MAX_PROFILE_FOLLOWS_PER_LIST_PAGE = 12  # keep polite / modular

# ── Source registry ─────────────────────────────────────────────────────────
SOURCES: list[dict[str, Any]] = [
    {
        "name": "clutch",
        "base_url": "https://clutch.co/agencies/digital-marketing?page=%d",
        "market": "digital-marketing",
    },
    {
        "name": "clutch_seo",
        "base_url": "https://clutch.co/agencies/search-engine-optimization?page=%d",
        "market": "seo",
    },
    {
        "name": "clutch_ppc",
        "base_url": "https://clutch.co/agencies/ppc-advertising?page=%d",
        "market": "ppc",
    },
    {
        "name": "goodfirms",
        "base_url": "https://www.goodfirms.co/marketing-agencies?page=%d",
    },
    {
        "name": "agencyspotter",
        "base_url": "https://www.agencyspotter.com/agencies/digital-marketing?page=%d",
    },
    {
        "name": "g2",
        "base_url": "https://www.g2.com/markets/digital-marketing-agencies?page=%d",
    },
    {
        "name": "google_maps",
        "searches": [
            "digital marketing agency usa",
            "seo agency uk",
            "ppc agency canada",
        ],
    },
]

# Map free-text Maps search → (ISO country, Google gl= param)
MAPS_SEARCH_GEO: dict[str, tuple[str, str]] = {
    "digital marketing agency usa": ("US", "us"),
    "seo agency uk": ("UK", "uk"),
    "ppc agency canada": ("CA", "ca"),
}

BLOCKED_GEO_KEYWORDS = (
    "dubai",
    "uae",
    "abu dhabi",
    "sharjah",
    "middle east",
    "gcc",
    "saudi",
    "riyadh",
    "jeddah",
    "qatar",
    "kuwait",
    "bahrain",
    "oman",
    "india",
    "mumbai",
    "delhi",
    "bangalore",
    "bengaluru",
    "hyderabad",
    "chennai",
    "pakistan",
    "karachi",
    "lahore",
    "philippines",
    "manila",
    "nigeria",
    "egypt",
    "cairo",
)

# ── Data model ───────────────────────────────────────────────────────────────
@dataclass
class Lead:
    business_name: str = ""
    owner_name: str = ""
    website: str = ""
    email: str = ""
    phone: str = ""
    country: str = ""  # US | UK | CA
    directory_source: str = ""

    # Internal / enrichment (not written to CSV)
    maps_link: str = ""
    _profile_url: str = field(default="", repr=False, compare=False)
    _snippet_text: str = field(default="", repr=False, compare=False)


# ── Helpers ──────────────────────────────────────────────────────────────────
def delay(lo: float = DELAY_MIN, hi: float = DELAY_MAX) -> None:
    time.sleep(random.uniform(lo, hi))


def norm_name(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "").lower().strip())


def norm_site(url: str) -> str:
    u = (url or "").strip().lower().rstrip("/")
    if u.startswith("http://"):
        u = "https://" + u[7:]
    try:
        p = urlparse(u)
        host = (p.netloc or "").lower().removeprefix("www.")
        if not host:
            return ""
        path = p.path or ""
        return f"{host}{path}".rstrip("/")
    except Exception:
        return u


def text_has_blocked_geo(text: str) -> bool:
    t = (text or "").lower()
    return any(k in t for k in BLOCKED_GEO_KEYWORDS)


def infer_country_from_blob(*parts: str) -> str:
    blob = " ".join(p for p in parts if p).lower()
    if not blob:
        return ""
    if "united kingdom" in blob or re.search(r"\buk\b", blob) or "england" in blob or "scotland" in blob or "wales" in blob or "northern ireland" in blob:
        return "UK"
    if "canada" in blob:
        return "CA"
    ca_cities = (
        "toronto",
        "vancouver",
        "montreal",
        "calgary",
        "ottawa",
        "edmonton",
        "winnipeg",
        "mississauga",
        "halifax",
    )
    if any(c in blob for c in ca_cities):
        return "CA"
    if "united states" in blob or blob.endswith(" usa") or " usa" in blob or ", us" in blob or re.search(r",\s*[a-z]{2}\s+\d{5}", blob):
        return "US"
    if re.search(r"\b(us|usa|u\.s\.a\.|u\.s\.|america)\b", blob):
        return "US"
    uk_cities = (
        "london",
        "manchester",
        "birmingham",
        "leeds",
        "glasgow",
        "liverpool",
        "bristol",
        "edinburgh",
        "cardiff",
        "belfast",
    )
    if any(c in blob for c in uk_cities):
        return "UK"
    return ""


def country_from_tld(url: str) -> str:
    try:
        host = (urlparse(url).netloc or "").lower()
        if host.endswith(".co.uk") or host.endswith(".uk"):
            return "UK"
        if host.endswith(".ca"):
            return "CA"
        if host.endswith(".us") or host.endswith(".com") or host.endswith(".io"):
            return ""
    except Exception:
        pass
    return ""


RE_EMAIL = re.compile(
    r"[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}", re.I
)
RE_PHONE = re.compile(r"(?:\+?\d[\d\s\-().]{6,}\d)")
RE_WA = re.compile(
    r"(?:wa\.me/|whatsapp\.com/send\?phone=|api\.whatsapp\.com/send\?phone=)([\d+]+)", re.I
)

JUNK_EMAILS = (
    "example",
    "domain",
    "email",
    "user",
    "info@sentry",
    "noreply",
    "no-reply",
    "wix.com",
    "sentry.io",
)


def clean_email(m: str) -> Optional[str]:
    lower = m.lower()
    if any(j in lower for j in JUNK_EMAILS):
        return None
    return lower


RE_OWNER_LINE = re.compile(
    r"(?:^|[\n\r•\|\-])\s*"
    r"(Founder|Managing Director|MD|CEO|Owner|President|Co-Owner|Principal|Partner)"
    r"\s*[:\-]\s*"
    r"([A-Z][a-zA-Z'\-]+(?:\s+[A-Z][a-zA-Z'\-]+){0,3})",
    re.I | re.M,
)
RE_OWNER_AFTER_NAME = re.compile(
    r"\b([A-Z][a-zA-Z'\-]+(?:\s+[A-Z][a-zA-Z'\-]+){1,3})\s*,\s*"
    r"(Founder|Managing Director|CEO|Owner|President)\b",
    re.I,
)


def extract_owner_from_html(html: str) -> str:
    m = RE_OWNER_LINE.search(html)
    if m:
        return m.group(2).strip()
    m2 = RE_OWNER_AFTER_NAME.search(html)
    if m2:
        return m2.group(1).strip()
    return ""


def extract_from_html(html: str) -> dict[str, str]:
    result: dict[str, str] = {}
    emails = [e for e in (clean_email(x) for x in RE_EMAIL.findall(html)) if e]
    if emails:
        result["email"] = emails[0]
    phones = RE_PHONE.findall(html)
    if phones:
        result["_site_phone"] = phones[0].strip()
    wa = RE_WA.search(html)
    if wa:
        result["_site_phone"] = result.get("_site_phone") or f"https://wa.me/{wa.group(1)}"
    own = extract_owner_from_html(html)
    if own:
        result["owner_name"] = own
    return result


def passes_filter(lead: Lead) -> bool:
    if not (lead.website or "").strip():
        return False
    if lead.country not in {"US", "UK", "CA"}:
        return False
    return True


def _dedup_secondary_key(lead: Lead) -> str:
    w = norm_site(lead.website)
    if w:
        return w
    if lead.maps_link:
        return lead.maps_link.lower().strip()
    pu = getattr(lead, "_profile_url", "") or ""
    if pu:
        return pu.lower().strip()
    return ""


def dedup(leads: list[Lead]) -> list[Lead]:
    seen: set[tuple[str, str]] = set()
    unique: list[Lead] = []
    for lead in leads:
        key = (norm_name(lead.business_name), _dedup_secondary_key(lead))
        if key in seen:
            continue
        if not key[0] and not key[1]:
            continue
        seen.add(key)
        unique.append(lead)
    return unique


def lead_should_skip_geo(lead: Lead) -> bool:
    blob = " ".join(
        [
            lead.business_name,
            lead.website,
            getattr(lead, "_snippet_text", "") or "",
            lead.maps_link,
        ]
    )
    return text_has_blocked_geo(blob)


# ── Directory: shared page load ─────────────────────────────────────────────
async def _goto_directory(page: Page, url: str) -> bool:
    try:
        await page.goto(
            url,
            timeout=DIRECTORY_TIMEOUT,
            wait_until="domcontentloaded",
        )
        await page.wait_for_timeout(int(random.uniform(900, 1600)))
        return True
    except Exception as e:
        log.warning("Directory navigation failed %s: %s", url, e)
        return False


async def _maybe_accept_cookies(page: Page) -> None:
    try:
        accept = page.locator(
            'button:has-text("Accept"), button:has-text("I Accept"), '
            'button:has-text("Accept all"), button:has-text("Agree"), '
            'button:has-text("Got it")'
        )
        if await accept.first.is_visible(timeout=2500):
            await accept.first.click()
            await page.wait_for_timeout(600)
    except Exception:
        pass


# ── Clutch (listing + optional public profile) ─────────────────────────────
_CLUTCH_PROFILE_JS = r"""
() => {
  const out = [];
  const seen = new Set();
  const rows = Array.from(document.querySelectorAll('a[href*="/profile/"]'));
  for (const a of rows) {
    let href = a.getAttribute("href") || "";
    if (!href.includes("/profile/")) continue;
    if (href.startsWith("/")) href = "https://clutch.co" + href;
    try {
      const u = new URL(href);
      const path = u.pathname.replace(/\/+$/, "");
      if (seen.has(path)) continue;
      seen.add(path);
      const card = a.closest("li") || a.closest("[class*='provider']") || a.closest("article") || a.parentElement;
      let business = (a.textContent || "").trim();
      if (!business && card) {
        const h = card.querySelector("h3, h2, [class*='title']");
        if (h) business = (h.textContent || "").trim();
      }
      let website = "";
      let phone = "";
      let location = "";
      let owner = "";
      if (card) {
        const ext = Array.from(card.querySelectorAll('a[href^="http"]')).find(x => {
          const h = x.getAttribute("href") || "";
          return !h.includes("clutch.co") && !h.includes("google.") && !h.includes("facebook.com") && !h.includes("linkedin.com");
        });
        if (ext) website = ext.getAttribute("href") || "";
        const t = (card.innerText || "").replace(/\s+/g, " ").trim();
        location = t;
        const m = t.match(/(Founder|Managing Director|CEO|Owner)\s*[:\-]\s*([A-Z][a-z]+(?:\s+[A-Z][a-z]+){0,3})/i);
        if (m) owner = m[2].trim();
        const ph = t.match(/(\+?\d[\d\s\-().]{8,}\d)/);
        if (ph) phone = ph[1].trim();
      }
      out.push({ profile_url: href.split("#")[0], business_name: business, website, phone, location, owner_name: owner });
    } catch (e) {}
  }
  return out;
}
"""


async def _clutch_profile_details(page: Page, profile_url: str) -> dict[str, str]:
    data: dict[str, str] = {}
    try:
        await page.goto(profile_url, timeout=DIRECTORY_TIMEOUT, wait_until="domcontentloaded")
        await page.wait_for_timeout(int(random.uniform(700, 1400)))
        html = await page.content()
        # Website: high-signal anchors
        for sel in (
            'a[data-link_text="Visit Website"]',
            'a[href*="website"]',
            'a.provider__website-link',
            'a[class*="website"]',
        ):
            try:
                loc = page.locator(sel).first
                if await loc.is_visible(timeout=800):
                    href = await loc.get_attribute("href")
                    if href and "clutch.co" not in href and href.startswith("http"):
                        data["website"] = href.strip()
                        break
            except Exception:
                continue
        if not data.get("website"):
            m = re.search(
                r'href="(https?://[^"]+)"[^>]*(?:visit website|website|provider__website)',
                html,
                re.I,
            )
            if m and "clutch.co" not in m.group(1).lower():
                data["website"] = m.group(1)
        # Location / HQ
        try:
            hq = page.locator('[itemprop="address"], [class*="location"], text=/Headquarters/i').first
            txt = await hq.inner_text(timeout=2000)
            if txt:
                data["location"] = txt
        except Exception:
            pass
        # Contact name
        try:
            staff = page.locator("text=/Founder|Managing Director|CEO|Owner/i").first
            if await staff.is_visible(timeout=1200):
                block = await staff.evaluate("el => el.closest('section, div, li')?.innerText || ''")
                mm = RE_OWNER_LINE.search(block)
                if mm:
                    data["owner_name"] = mm.group(2).strip()
        except Exception:
            pass
        ph = RE_PHONE.search(html)
        if ph:
            data["phone"] = ph.group(0).strip()
    except Exception as e:
        log.debug("Clutch profile scrape failed %s: %s", profile_url, e)
    return data


async def extract_clutch_page(context: BrowserContext, page: Page, source_name: str) -> list[Lead]:
    leads: list[Lead] = []
    try:
        raw = await page.evaluate(_CLUTCH_PROFILE_JS)
        if not isinstance(raw, list):
            raw = []
    except Exception as e:
        log.warning("Clutch list JS extract failed (%s): %s", source_name, e)
        return leads

    profile_page = await context.new_page()
    try:
        for i, row in enumerate(raw):
            if not isinstance(row, dict):
                continue
            name = (row.get("business_name") or "").strip()
            if not name:
                continue
            website = (row.get("website") or "").strip()
            phone = (row.get("phone") or "").strip()
            loc = (row.get("location") or "").strip()
            owner = (row.get("owner_name") or "").strip()
            profile_url = (row.get("profile_url") or "").strip()
            country = infer_country_from_blob(loc, website) or country_from_tld(website)

            if not website and profile_url and i < MAX_PROFILE_FOLLOWS_PER_LIST_PAGE:
                extra = await _clutch_profile_details(profile_page, profile_url)
                website = website or (extra.get("website") or "").strip()
                phone = phone or (extra.get("phone") or "").strip()
                loc = loc or (extra.get("location") or "").strip()
                owner = owner or (extra.get("owner_name") or "").strip()
                country = country or infer_country_from_blob(loc, website) or country_from_tld(website)
                delay(0.4, 1.1)

            ld = Lead(
                business_name=name,
                owner_name=owner,
                website=website,
                phone=phone,
                country=country,
                directory_source=source_name,
                _profile_url=profile_url,
                _snippet_text=loc[:500],
            )
            if not lead_should_skip_geo(ld):
                leads.append(ld)
    finally:
        await profile_page.close()

    return leads


# ── GoodFirms (heuristic) ───────────────────────────────────────────────────
_GOODFIRMS_JS = r"""
() => {
  const out = [];
  const seen = new Set();
  document.querySelectorAll('a[href*="/agency/"], a[href*="/marketing-companies/"]').forEach(a => {
    const href = a.href || "";
    const name = (a.textContent || "").trim();
    if (!name || name.length < 2) return;
    const card = a.closest("div[class*='firm'], div[class*='company'], li, article, tr") || a.parentElement;
    let website = "";
    let loc = "";
    if (card) {
      const t = (card.innerText || "").replace(/\s+/g, " ").trim();
      loc = t;
      const ext = Array.from(card.querySelectorAll('a[href^="http"]')).find(x => {
        const h = x.href || "";
        return !h.includes("goodfirms.co");
      });
      if (ext) website = ext.href || "";
    }
    const key = name + "|" + href;
    if (seen.has(key)) return;
    seen.add(key);
    out.push({ business_name: name, website, location: loc, profile_url: href });
  });
  return out;
}
"""


async def extract_goodfirms_page(page: Page) -> list[Lead]:
    leads: list[Lead] = []
    try:
        raw = await page.evaluate(_GOODFIRMS_JS)
        if not isinstance(raw, list):
            raw = []
    except Exception as e:
        log.warning("GoodFirms extract failed: %s", e)
        return leads
    for row in raw:
        if not isinstance(row, dict):
            continue
        name = (row.get("business_name") or "").strip()
        if not name:
            continue
        website = (row.get("website") or "").strip()
        loc = (row.get("location") or "").strip()
        country = infer_country_from_blob(loc, website) or country_from_tld(website)
        ld = Lead(
            business_name=name,
            website=website,
            country=country,
            directory_source="goodfirms",
            _profile_url=(row.get("profile_url") or "").strip(),
            _snippet_text=loc[:500],
        )
        if not lead_should_skip_geo(ld):
            leads.append(ld)
    return leads


# ── AgencySpotter (heuristic) ───────────────────────────────────────────────
_AGENCYSPOTTER_JS = r"""
() => {
  const out = [];
  const seen = new Set();
  document.querySelectorAll('a[href*="/agency/"]').forEach(a => {
    const href = a.href || "";
    if (!href.includes("/agency/")) return;
    const name = (a.textContent || "").trim();
    if (!name || name.length < 2) return;
    const card = a.closest("article, li, div[class*='card']") || a.parentElement;
    let website = "";
    let loc = "";
    if (card) {
      const t = (card.innerText || "").replace(/\s+/g, " ").trim();
      loc = t;
      const ext = Array.from(card.querySelectorAll('a[href^="http"]')).find(x => {
        const h = x.href || "";
        return !h.includes("agencyspotter.com");
      });
      if (ext) website = ext.href || "";
    }
    const key = href;
    if (seen.has(key)) return;
    seen.add(key);
    out.push({ business_name: name, website, location: loc, profile_url: href });
  });
  return out;
}
"""


async def extract_agencyspotter_page(page: Page) -> list[Lead]:
    leads: list[Lead] = []
    try:
        raw = await page.evaluate(_AGENCYSPOTTER_JS)
        if not isinstance(raw, list):
            raw = []
    except Exception as e:
        log.warning("AgencySpotter extract failed: %s", e)
        return leads
    for row in raw:
        if not isinstance(row, dict):
            continue
        name = (row.get("business_name") or "").strip()
        if not name:
            continue
        website = (row.get("website") or "").strip()
        loc = (row.get("location") or "").strip()
        country = infer_country_from_blob(loc, website) or country_from_tld(website)
        ld = Lead(
            business_name=name,
            website=website,
            country=country,
            directory_source="agencyspotter",
            _profile_url=(row.get("profile_url") or "").strip(),
            _snippet_text=loc[:500],
        )
        if not lead_should_skip_geo(ld):
            leads.append(ld)
    return leads


# ── G2 (heuristic — DOM varies; JSON-LD / Nuxt payloads as fallback) ────────
_G2_VENDOR_JS = r"""
() => {
  const out = [];
  const seen = new Set();
  const add = (name, website, loc) => {
    name = (name || "").trim();
    if (!name || name.length < 2) return;
    const key = name + "|" + (website || "");
    if (seen.has(key)) return;
    seen.add(key);
    out.push({ business_name: name, website: website || "", location: loc || "" });
  };
  document.querySelectorAll('a[href*="/products/"][href*="/reviews"]').forEach(a => {
    const name = (a.textContent || "").trim();
    const card = a.closest("div[data-product-id], div[class*='product'], li, article") || a.parentElement;
    let website = "";
    let loc = "";
    if (card) {
      loc = (card.innerText || "").replace(/\s+/g, " ").trim();
      const ext = Array.from(card.querySelectorAll('a[href^="http"]')).find(x => {
        const h = x.href || "";
        return !h.includes("g2.com") && !h.includes("linkedin.com");
      });
      if (ext) website = ext.href || "";
    }
    add(name, website, loc);
  });
  document.querySelectorAll('[data-product-slug], [data-vendor-name]').forEach(el => {
    const name = el.getAttribute("data-vendor-name") || el.getAttribute("data-product-name") || (el.textContent || "").trim();
    add(name, "", "");
  });
  return out;
}
"""


async def extract_g2_page(page: Page) -> list[Lead]:
    leads: list[Lead] = []
    try:
        raw = await page.evaluate(_G2_VENDOR_JS)
        if not isinstance(raw, list):
            raw = []
    except Exception as e:
        log.warning("G2 DOM extract failed: %s", e)
        raw = []

    if not raw:
        try:
            html = await page.content()
            for m in re.finditer(
                r'"vendor_name"\s*:\s*"([^"\\]+)"|"name"\s*:\s*"([^"\\]+)"\s*,\s*"url"',
                html,
            ):
                name = (m.group(1) or m.group(2) or "").strip()
                if len(name) > 2:
                    raw.append({"business_name": name, "website": "", "location": ""})
        except Exception:
            pass

    seen: set[tuple[str, str]] = set()
    for row in raw:
        if not isinstance(row, dict):
            continue
        name = (row.get("business_name") or "").strip()
        if not name:
            continue
        website = (row.get("website") or "").strip()
        loc = (row.get("location") or "").strip()
        key = (norm_name(name), norm_site(website))
        if key in seen:
            continue
        seen.add(key)
        country = infer_country_from_blob(loc, website) or country_from_tld(website)
        ld = Lead(
            business_name=name,
            website=website,
            country=country,
            directory_source="g2",
            _snippet_text=loc[:500],
        )
        if not lead_should_skip_geo(ld):
            leads.append(ld)
    return leads


async def scrape_directory_page(
    context: BrowserContext, source: dict[str, Any], page_num: int
) -> list[Lead]:
    name = str(source.get("name", "unknown"))
    base = source.get("base_url")
    if not base or "%d" not in str(base):
        return []
    url = str(base) % page_num
    log.info("📂 Directory %s page %s → %s", name, page_num, url)
    page = await context.new_page()
    leads: list[Lead] = []
    try:
        ok = await _goto_directory(page, url)
        if not ok:
            return leads
        await _maybe_accept_cookies(page)

        if name in ("clutch", "clutch_seo", "clutch_ppc"):
            leads = await extract_clutch_page(context, page, name)
        elif name == "goodfirms":
            leads = await extract_goodfirms_page(page)
        elif name == "agencyspotter":
            leads = await extract_agencyspotter_page(page)
        elif name == "g2":
            leads = await extract_g2_page(page)
        else:
            log.info("No extractor registered for source %s — skipping", name)

        log.info("  → %s rows from %s p%s", len(leads), name, page_num)
    except Exception as e:
        log.warning("Directory scrape error %s p%s: %s", name, page_num, e)
    finally:
        await page.close()
    return leads


# ── Google Maps ─────────────────────────────────────────────────────────────
def maps_url_for_query(query: str) -> tuple[str, str, str]:
    q = query.strip().lower()
    country, gl = MAPS_SEARCH_GEO.get(q, ("", "us"))
    encoded = quote_plus(query)
    u = f"https://www.google.com/maps/search/{encoded}?hl=en&gl={gl}"
    return u, country, gl


async def scrape_maps_query(
    context: BrowserContext,
    query: str,
    *,
    country_hint: str = "",
) -> list[Lead]:
    maps_url, mapped_country, _ = maps_url_for_query(query)
    country_hint = country_hint or mapped_country

    log.info("🔍 Maps: %s (%s)", query, maps_url)
    page = await context.new_page()
    leads: list[Lead] = []

    try:
        await page.goto(maps_url, timeout=MAPS_TIMEOUT, wait_until="domcontentloaded")
        await page.wait_for_timeout(2000)

        try:
            accept = page.locator(
                'button:has-text("Accept all"), button:has-text("Reject all")'
            )
            if await accept.first.is_visible(timeout=3000):
                await accept.first.click()
                await page.wait_for_timeout(1000)
        except Exception:
            pass

        results_panel = page.locator('div[role="feed"]')
        try:
            await results_panel.wait_for(timeout=MAPS_TIMEOUT)
        except PWTimeout:
            log.warning("Maps results panel not found — skipping query")
            return leads

        prev_count = 0
        stall_count = 0
        for attempt in range(MAX_SCROLL_ATTEMPTS):
            items = await page.locator('div[role="feed"] > div > div[jsaction]').all()
            curr_count = len(items)
            log.info("  Scroll %s: %s listings", attempt + 1, curr_count)

            end_marker = page.locator('text="You\'ve reached the end of the list"')
            if await end_marker.is_visible(timeout=500):
                log.info("  End of Maps list.")
                break

            if curr_count == prev_count:
                stall_count += 1
                if stall_count >= 3:
                    log.info("  No new listings — stop scroll.")
                    break
            else:
                stall_count = 0

            prev_count = curr_count
            await results_panel.evaluate("el => el.scrollBy(0, 1000)")
            await page.wait_for_timeout(int(random.uniform(1200, 2200)))

        listing_links = await page.locator('div[role="feed"] a[href*="/maps/place/"]').all()
        hrefs: list[str] = []
        for link in listing_links:
            href = await link.get_attribute("href")
            if href and href not in hrefs:
                hrefs.append(href)

        log.info("  Found %s unique listing URLs", len(hrefs))

        for i, href in enumerate(hrefs, 1):
            lead = await scrape_listing(
                context,
                href,
                i,
                len(hrefs),
                directory_source="google_maps",
                country_hint=country_hint,
            )
            if lead and not lead_should_skip_geo(lead):
                leads.append(lead)
            delay()

    except Exception as e:
        log.error("Maps query error %r: %s", query, e)
    finally:
        await page.close()

    return leads


async def scrape_listing(
    context: BrowserContext,
    href: str,
    idx: int,
    total: int,
    *,
    directory_source: str = "google_maps",
    country_hint: str = "",
) -> Optional[Lead]:
    page = await context.new_page()
    lead = Lead(directory_source=directory_source)
    try:
        full_url = href if href.startswith("http") else f"https://www.google.com{href}"
        lead.maps_link = full_url
        await page.goto(full_url, timeout=MAPS_TIMEOUT, wait_until="domcontentloaded")
        await page.wait_for_timeout(1500)

        try:
            name_el = page.locator('h1.DUwDvf, h1[class*="fontHeadlineLarge"]').first
            lead.business_name = (await name_el.inner_text(timeout=5000)).strip()
        except Exception:
            lead.business_name = ""

        if not lead.business_name:
            log.debug("  [%s/%s] no name — skip", idx, total)
            return None

        log.info("  [%s/%s] %s", idx, total, lead.business_name)

        addr = ""
        try:
            addr_btn = page.locator('button[data-item-id="address"]').first
            addr = (await addr_btn.inner_text(timeout=3000)).strip()
        except Exception:
            pass
        lead._snippet_text = addr

        phone = ""
        try:
            phone_btn = page.locator('button[data-item-id*="phone:tel"]').first
            if await phone_btn.is_visible(timeout=2000):
                phone = (
                    (await phone_btn.get_attribute("aria-label") or "")
                    .replace("Phone:", "")
                    .strip()
                )
        except Exception:
            pass
        lead.phone = phone

        website = ""
        try:
            web_btn = page.locator('a[data-item-id="authority"]').first
            if await web_btn.is_visible(timeout=2000):
                website = (await web_btn.get_attribute("href") or "").strip()
        except Exception:
            pass
        lead.website = website

        inferred = infer_country_from_blob(addr, lead.business_name, website) or country_hint
        lead.country = inferred or ""

    except Exception as e:
        log.warning("  listing error %s: %s", href, e)
    finally:
        await page.close()

    return lead


# ── Website enrichment ───────────────────────────────────────────────────────
async def scrape_website(context: BrowserContext, lead: Lead) -> Lead:
    if not lead.website:
        return lead

    url = lead.website
    if not url.startswith("http"):
        url = "https://" + url

    parsed = urlparse(url)
    homepage = urlunparse((parsed.scheme or "https", parsed.netloc, "/", "", "", ""))

    page = await context.new_page()
    try:
        await page.goto(homepage, timeout=WEBSITE_TIMEOUT, wait_until="domcontentloaded")
        await page.wait_for_timeout(1000)
        html = await page.content()
        data = extract_from_html(html)
        if data.get("email"):
            lead.email = data["email"]
        site_phone = data.get("_site_phone", "")
        if site_phone and not lead.phone:
            lead.phone = site_phone
        if data.get("owner_name") and not lead.owner_name:
            lead.owner_name = data["owner_name"]
        if not lead.country:
            lead.country = infer_country_from_blob(html[:4000], lead.country) or country_from_tld(
                homepage
            )
        log.info(
            "    🌐 %s: email=%s owner=%s phone=%s",
            lead.business_name[:48],
            bool(lead.email),
            bool(lead.owner_name),
            bool(lead.phone),
        )
    except Exception as e:
        log.debug("Website error %s: %s", lead.website, e)
    finally:
        await page.close()

    return lead


# ── CSV (only declared Lead fields) ──────────────────────────────────────────
CSV_FIELDNAMES = [
    "business_name",
    "owner_name",
    "website",
    "email",
    "phone",
    "country",
    "directory_source",
]


def write_leads_csv(path: str, leads: list[Lead]) -> None:
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=CSV_FIELDNAMES, extrasaction="ignore")
        w.writeheader()
        for lead in leads:
            row = {k: getattr(lead, k, "") for k in CSV_FIELDNAMES}
            w.writerow(row)


# ── Main ─────────────────────────────────────────────────────────────────────
async def main() -> None:
    all_leads: list[Lead] = []

    async with async_playwright() as p:
        browser = await p.chromium.launch(
            headless=True,
            args=["--disable-blink-features=AutomationControlled"],
        )
        context = await browser.new_context(
            viewport={"width": 1360, "height": 900},
            user_agent=(
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/122.0.0.0 Safari/537.36"
            ),
            locale="en-US",
        )

        for source in SOURCES:
            sname = source.get("name")
            if sname == "google_maps":
                continue
            for page_num in range(1, MAX_DIRECTORY_PAGES + 1):
                rows = await scrape_directory_page(context, source, page_num)
                if not rows:
                    log.info("  Stopping %s: empty page %s", sname, page_num)
                    break
                all_leads.extend(rows)
                delay(1.2, 2.8)

        gmaps = next((s for s in SOURCES if s.get("name") == "google_maps"), None)
        if gmaps:
            for q in gmaps.get("searches") or []:
                maps_leads = await scrape_maps_query(context, str(q))
                all_leads.extend(maps_leads)
                delay(2.0, 4.0)

        log.info("Raw combined: %s", len(all_leads))
        all_leads = dedup(all_leads)
        log.info("After dedup: %s", len(all_leads))

        log.info("🌐 Visiting websites…")
        for i in range(len(all_leads)):
            if all_leads[i].website:
                all_leads[i] = await scrape_website(context, all_leads[i])
                delay()

        await browser.close()

    filtered = [l for l in all_leads if passes_filter(l)]
    log.info("Passes filter: %s / %s", len(filtered), len(all_leads))
    filtered = dedup(filtered)
    log.info("Final dedup: %s", len(filtered))

    if not filtered:
        log.warning("No leads to export.")
        return

    write_leads_csv(OUTPUT_FILE, filtered)
    log.info("💾 Saved %s leads → %s", len(filtered), OUTPUT_FILE)


if __name__ == "__main__":
    asyncio.run(main())
