#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
NBA Meccsradar
==============
Az NBA következő 7 napjának meccseit elemzi: ki nyer, hány pontot dob a két
csapat külön-külön és összesen. A becslés több forrásból áll össze:

  * statisztikai modellek (ellenfél-korrigált erősség, szezonátlag, utolsó 10 meccs),
  * pihenőnapok (back-to-back), sérültlista, a csapatokról szóló hírek hangulata,
  * fogadóirodák vonalai kulcs nélkül: ESPN, Pinnacle, DraftKings, Bovada, Unibet (Kambi),
    Action Network (FanDuel, BetMGM, Caesars, bet365…), FanDuel, Paf (Kambi), SportsbookReview,
    Polymarket és Kalshi előrejelző piac, opcionálisan The Odds API,
  * hírek, pletykák 22 amerikai NBA-portálról (RSS, ahol nincs: Google News).

Az oldal percenként újraszámol, a menetrendet / eredményeket 5 percenként,
a sérültlistát 15 percenként, a híreket 30 percenként frissíti.

Telepítés:
    pip install numpy tzdata

Futtatás:
    python nba_meccsradar.py                     # élő adatok (ESPN + Google News)
    python nba_meccsradar.py --odds-key KULCS    # + több fogadóiroda (the-odds-api.com, ingyenes kulcs)
    python nba_meccsradar.py --demo              # kitalált adatok, internet nélkül
    python nba_meccsradar.py --port 9000 --no-browser
    python nba_meccsradar.py --build site --data data   # egyszeri futás, statikus oldal (GitHub Actions/Pages)

Az Odds API kulcs környezeti változóból is jöhet:  ODDS_API_KEY=...

FONTOS: ez szabályalapú elemző eszköz, nem fogadási tanács. A sportfogadás
pénzvesztéssel jár; a fogadóirodák vonalai átlagosan pontosabbak bármely
egyszerű statisztikai modellnél. Csak 18 év felett, csak olyan összeggel,
amelynek elvesztését megengedheted magadnak.
"""
from __future__ import annotations

import argparse
import bisect
import json
import math
import os
import re
import threading
import time
import traceback
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import xml.etree.ElementTree as ET
from collections import defaultdict, deque
from datetime import date, datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from statistics import NormalDist, median
from zoneinfo import ZoneInfo

import numpy as np

# ---------------------------------------------------------------------------
# Beállítások
# ---------------------------------------------------------------------------
CONFIG = {
    "port": 8766,
    "days_ahead": 7,
    "sched_refresh_s": 300,        # menetrend, élő eredmények, ESPN-szorzó
    "injury_refresh_s": 900,       # sérültlista
    "news_refresh_s": 1800,        # hírek
    "stats_refresh_s": 12 * 3600,  # játékosátlagok (a sérülések súlyozásához)
    "odds_refresh_s": 6 * 3600,    # The Odds API: az ingyenes csomag 500 kredit/hó, egy lekérés ~3 kredit
    "odds_free_refresh_s": 600,    # a kulcs nélküli fogadóirodai források (Pinnacle, DraftKings, Bovada, Unibet, Action Network)
    "kambi_ops": [("ub", "Unibet", "GB"), ("paf", "Paf", "FI")],  # Kambi-alapú irodák (kód, név, piac)
    "min_sources": 10,             # ennél kevesebb működő szorzóforrásnál figyelmeztet az oldal
    "feed_refresh_s": 600,         # az amerikai NBA-portálok hírfolyamai
    "sbr_days": 4,                 # SportsbookReview: ennyi napra előre (később ritkán van már vonal)
    "odds_regions": "eu",          # eu = európai irodák (Unibet, Pinnacle, Betfair, William Hill…)
    "odds_api_key": os.environ.get("ODDS_API_KEY", ""),
    # modell
    "half_life_days": 75,          # ennyi nap alatt feleződik egy meccs súlya
    "prev_season_weight": 0.5,     # az előző szezon meccsei ennyivel kisebb súlyt kapnak
    "ridge": 4.0,                  # visszahúzás az átlag felé (szezon elején fontos)
    "hca": 2.3,                    # hazai pálya előnye pontban, ha nincs elég adat a becsléséhez
    "b2b_pen": 1.8,                # back-to-back (előző nap is játszott) büntetés pontban
    "margin_sd": 12.5,             # a pontkülönbség szórása NBA-ben
    "total_sd": 17.5,              # az összpontszám szórása
    "market_weight": 0.6,          # a végső becslésben a fogadóirodák súlya (0–1)
    "news_max_pts": 1.0,           # a hírhangulat legfeljebb ennyi pontot mozdít
    "value_edge": 0.04,            # ennyi várható érték felett jelöljük "értékesnek" a szorzót
    "pred_file": "nba_predikciok.json",
}

TZ = ZoneInfo("Europe/Budapest")
UA = "Mozilla/5.0 (NBA-Meccsradar)"
SITE = "https://site.api.espn.com/apis/site/v2/sports/basketball/nba"
STATS_URL = "https://site.web.api.espn.com/apis/common/v3/sports/basketball/nba/statistics/byathlete"
ODDS_URL = "https://api.the-odds-api.com/v4/sports/basketball_nba/odds"
ND = NormalDist()

MODEL_NAMES = {
    "rating": "Erősség-modell",
    "season": "Szezonátlag",
    "form": "Forma (utolsó 10)",
    "stat": "Statisztika + sérülés/pihenő/hírek",
    "market": "Fogadóirodák (konszenzus)",
    "final": "Végső becslés",
}
STATUS_W = {"out": 1.0, "doubtful": 0.75, "questionable": 0.4, "day-to-day": 0.35, "probable": 0.1}


# ---------------------------------------------------------------------------
# Segédfüggvények
# ---------------------------------------------------------------------------
def http_get(url, params=None, timeout=15, headers=None):
    if params:
        url = url + ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
    h = {"User-Agent": UA, "Accept": "application/json, text/plain, */*"}
    if headers:
        h.update(headers)
    req = urllib.request.Request(url, headers=h)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        body = r.read()
        hdr = {k.lower(): v for k, v in r.headers.items()}
    return body, hdr


def get_json(url, params=None, timeout=15, headers=None):
    body, hdr = http_get(url, params, timeout, headers)
    return json.loads(body.decode("utf-8")), hdr


def num(x):
    try:
        v = float(str(x).replace(",", ""))
        return None if math.isnan(v) else v
    except (TypeError, ValueError):
        return None


def nick(name: str) -> str:
    """Csapatbecenév (utolsó szó) – így egyezik az ESPN és a fogadóirodák elnevezése."""
    n = re.sub(r"\(.*?\)", "", name or "").strip()
    return n.split(" ")[-1].lower() if n else ""


def norm_name(n: str) -> str:
    n = unicodedata.normalize("NFKD", n or "").encode("ascii", "ignore").decode().lower()
    n = re.sub(r"\b(jr|sr|ii|iii|iv)\b\.?", "", n)
    return re.sub(r"[^a-z]", "", n)


def parse_iso(s):
    try:
        return datetime.fromisoformat(str(s).replace("Z", "+00:00")).timestamp()
    except Exception:
        return None


def parse_ts(v):
    """ISO-szöveg, '2026-11-02 00:30:00+00' alak vagy unix (s / ms) -> unix másodperc."""
    if v is None or v == "":
        return None
    if isinstance(v, (int, float)):
        return v / 1000 if v > 1e11 else float(v)
    t = str(v).strip().replace(" ", "T")
    t = re.sub(r"([+-]\d{2})$", r"\1:00", t)
    return parse_iso(t)


# Csapatok egyéb nevei: a fogadóirodák, tőzsdék és hírportálok így hivatkoznak rájuk.
# Kulcs = a nick() által adott becenév.
NBA_ALIASES = {
    "hawks": ["Atlanta"], "celtics": ["Boston", "Celts"], "nets": ["Brooklyn"], "hornets": ["Charlotte"],
    "bulls": ["Chicago"], "cavaliers": ["Cleveland", "Cavs"], "mavericks": ["Dallas", "Mavs"], "nuggets": ["Denver"],
    "pistons": ["Detroit"], "warriors": ["Golden State", "Dubs"], "rockets": ["Houston"], "pacers": ["Indiana"],
    "clippers": ["Clips"], "lakers": [], "grizzlies": ["Memphis", "Grizz"], "heat": ["Miami"],
    "bucks": ["Milwaukee"], "timberwolves": ["Minnesota", "Wolves", "T-Wolves"], "pelicans": ["New Orleans", "Pels"],
    "knicks": ["New York"], "thunder": ["Oklahoma City", "OKC"], "magic": ["Orlando"],
    "76ers": ["Philadelphia", "Sixers", "Philly"], "suns": ["Phoenix"], "blazers": ["Portland", "Trail Blazers"],
    "kings": ["Sacramento"], "spurs": ["San Antonio"], "raptors": ["Toronto", "Raps"], "jazz": ["Utah"],
    "wizards": ["Washington", "Wiz"],
}
NBA_ABBR = {
    "ATL": "hawks", "BOS": "celtics", "BKN": "nets", "BRK": "nets", "CHA": "hornets", "CHO": "hornets", "CHI": "bulls",
    "CLE": "cavaliers", "DAL": "mavericks", "DEN": "nuggets", "DET": "pistons", "GS": "warriors", "GSW": "warriors",
    "HOU": "rockets", "IND": "pacers", "LAC": "clippers", "LAL": "lakers", "MEM": "grizzlies", "MIA": "heat",
    "MIL": "bucks", "MIN": "timberwolves", "NO": "pelicans", "NOP": "pelicans", "NY": "knicks", "NYK": "knicks",
    "OKC": "thunder", "ORL": "magic", "PHI": "76ers", "PHX": "suns", "PHO": "suns", "POR": "blazers",
    "SAC": "kings", "SA": "spurs", "SAS": "spurs", "TOR": "raptors", "UTA": "jazz", "UTAH": "jazz",
    "WAS": "wizards", "WSH": "wizards",
}


def resolve_nick(text):
    """Szabad szövegből (becenév, város, rövidítés) a csapat beceneve, vagy None."""
    t = (text or "").strip()
    if not t:
        return None
    if t.upper() in NBA_ABBR:
        return NBA_ABBR[t.upper()]
    low = t.lower()
    for nk in NBA_ALIASES:
        if re.search(rf"\b{re.escape(nk)}\b", low):
            return nk
    for nk, al in NBA_ALIASES.items():
        for a in al:
            if re.search(rf"\b{re.escape(a.lower())}\b", low):
                return nk
    return None


def season_of(d: date) -> int:
    """ESPN-féle szezonév: a 2026/27-es szezon = 2027."""
    return d.year + 1 if d.month >= 8 else d.year


def season_label(y: int) -> str:
    return f"{y - 1}/{str(y)[2:]}"


def us_date(ts: float) -> date:
    """Amerikai (keleti parti) játéknap – az esti meccsek így egy naphoz tartoznak."""
    return (datetime.fromtimestamp(ts, timezone.utc) - timedelta(hours=5)).date()


def now_str():
    return datetime.now(TZ).strftime("%Y-%m-%d %H:%M:%S")


HU_DAYS = ["hétfő", "kedd", "szerda", "csütörtök", "péntek", "szombat", "vasárnap"]
HU_MON = ["jan.", "febr.", "márc.", "ápr.", "máj.", "jún.", "júl.", "aug.", "szept.", "okt.", "nov.", "dec."]


def hu_day(d: date) -> str:
    return f"{HU_MON[d.month - 1]} {d.day}. ({HU_DAYS[d.weekday()]})"


def am_to_dec(a):
    a = num(a)
    if a is None or a == 0:
        return None
    return round(1 + a / 100, 3) if a > 0 else round(1 + 100 / abs(a), 3)


def clean(o):
    if isinstance(o, dict):
        return {str(k): clean(v) for k, v in o.items()}
    if isinstance(o, (list, tuple, deque)):
        return [clean(v) for v in o]
    if isinstance(o, (np.floating, float)):
        v = float(o)
        return None if (math.isnan(v) or math.isinf(v)) else v
    if isinstance(o, np.integer):
        return int(o)
    if isinstance(o, np.bool_):
        return bool(o)
    if isinstance(o, date):
        return o.isoformat()
    return o


def mk_pred(hp, ap, sd):
    m = hp - ap
    return {"hp": hp, "ap": ap, "margin": m, "total": hp + ap, "p": ND.cdf(m / sd)}


def player_value(ppg, mpg):
    """Durva becslés: hány ponttal gyengül a csapat, ha a játékos kiesik (0–6)."""
    if ppg is None:
        return 1.0
    mpg = mpg or 0
    return float(min(6.0, max(0.0, 0.3 * (ppg - 6)) + 0.03 * max(mpg - 12, 0)))


# ---------------------------------------------------------------------------
# Hírek: hangulat és címkék
# ---------------------------------------------------------------------------
POS_PATTERNS = [
    r"\bwins?\b", r"\bwon\b", r"\bbeats?\b", r"\brout", r"\bdominat", r"\bwinning streak", r"\breturns?\b",
    r"\breturning\b", r"\bcleared\b", r"\bextension\b", r"\bcareer[- ]high", r"\btriple[- ]double", r"\bcomeback",
    r"\bhealthy\b", r"\bsurg(e|es|ing)\b", r"\bupgraded\b", r"\bstrong", r"\bstreak\b", r"\bboost", r"\bback in",
    r"\bgyőz", r"\bvisszatér", r"\bnyer",
]
NEG_PATTERNS = [
    r"\bloss(es)?\b", r"\blos(e|es|ing)\b", r"\blost\b", r"\binjur", r"\bout for\b", r"\bsurgery", r"\btorn\b",
    r"\bsprain", r"\bstrain", r"\bsuspend", r"\bslump", r"\bskid", r"\bstruggl", r"\bbenched", r"\beject",
    r"\bfined?\b", r"\btrade request", r"\bturmoil", r"\bsidelined", r"\bsetback", r"\bruled out", r"\bmiss(es|ing)?\b",
    r"\bfracture", r"\bconcussion", r"\bdoubtful\b", r"\bquestionable\b", r"\bsérül", r"\bkiesik", r"\bvereség",
]
POS_RE = [re.compile(p, re.I) for p in POS_PATTERNS]
NEG_RE = [re.compile(p, re.I) for p in NEG_PATTERNS]
TAGS = {
    "Sérülés": r"injur|sprain|strain|surgery|torn|fracture|concussion|hamstring|ankle|knee|achilles|\bacl\b|\bmri\b|sidelined|ruled out|questionable|doubtful|day-to-day|sérül",
    "Visszatér": r"\breturn|cleared|back in (the )?lineup|activated|upgraded|available|visszatér",
    "Pletyka/átigazolás": r"trade|rumou?r|sources|reportedly|linked|interest in|free agen|\bsign(s|ed|ing)?\b|waive|buyout|átigazol|pletyk",
    "Eltiltás": r"suspend|suspension|\bfined?\b|eltilt",
    "Pihentetés": r"\brest(ing|ed|s)?\b|load management|minutes restriction|pihen",
    "Edző/vezetés": r"\bcoach|\bfired\b|\bhired?\b|general manager|front office",
}
TAG_RE = {k: re.compile(v, re.I) for k, v in TAGS.items()}


def headline_sentiment(title: str) -> float:
    p = sum(1 for r in POS_RE if r.search(title))
    n = sum(1 for r in NEG_RE if r.search(title))
    return 0.0 if p + n == 0 else (p - n) / (p + n)


def headline_tags(title: str) -> list[str]:
    return [k for k, r in TAG_RE.items() if r.search(title)]


def aggregate_sentiment(items):
    """Időben súlyozott átlag (2 napos felezési idő)."""
    now = time.time()
    num_, den = 0.0, 0.0
    for it in items:
        w = 0.5 ** (max(0.0, (now - (it.get("ts") or now)) / 86400) / 2.0)
        num_ += w * it["s"]
        den += w
    return (num_ / den if den else None), len(items)


# ---------------------------------------------------------------------------
# Adatforrások
# ---------------------------------------------------------------------------
def team_rec(t, nba=True):
    logos = t.get("logos") or []
    return {"id": str(t.get("id")), "abbr": t.get("abbreviation") or "?", "name": t.get("displayName") or "?",
            "short": t.get("shortDisplayName") or t.get("name") or t.get("displayName") or "?",
            "nick": nick(t.get("name") or t.get("displayName")),
            "logo": (logos[0].get("href") if logos else None) or t.get("logo"), "nba": nba}


def parse_event(ev):
    try:
        comp = ev["competitions"][0]
        cs = comp.get("competitors", [])
        home = next(c for c in cs if c.get("homeAway") == "home")
        away = next(c for c in cs if c.get("homeAway") == "away")
    except (KeyError, IndexError, StopIteration):
        return None, []
    st = ev.get("status", {}).get("type", {})
    state = st.get("state", "pre")
    hs, as_ = num(home.get("score")), num(away.get("score"))
    g = {
        "id": str(ev["id"]), "ts": parse_iso(ev.get("date")), "stype": ev.get("season", {}).get("type", 2),
        "season": ev.get("season", {}).get("year"), "home": str(home["team"]["id"]), "away": str(away["team"]["id"]),
        "hs": hs if state != "pre" else None, "as": as_ if state != "pre" else None,
        "state": state, "completed": bool(st.get("completed")), "detail": st.get("shortDetail") or "",
        "neutral": bool(comp.get("neutralSite")), "espn_odds": None,
    }
    if g["ts"] is None:
        return None, []
    if g["season"] is None:
        g["season"] = season_of(us_date(g["ts"]))
    odds = comp.get("odds") or []
    if odds:
        o = odds[0]
        ho, ao = o.get("homeTeamOdds") or {}, o.get("awayTeamOdds") or {}
        row = {"book": (o.get("provider") or {}).get("name") or "ESPN", "src": "ESPN"}
        sp = num(o.get("spread"))
        if sp is not None:
            home_fav = ho.get("favorite")
            if home_fav is None:
                home_fav = sp < 0
            row["spread_h"] = -abs(sp) if home_fav else abs(sp)
        row["total"] = num(o.get("overUnder"))
        row["ml_h"], row["ml_a"] = am_to_dec(ho.get("moneyLine")), am_to_dec(ao.get("moneyLine"))
        if row.get("spread_h") is not None or row.get("total") or row.get("ml_h"):
            g["espn_odds"] = row
    teams = [team_rec(home["team"], nba=False), team_rec(away["team"], nba=False)]
    return g, teams


class LiveSource:
    def __init__(self, cfg):
        self.cfg = cfg
        self.odds_left = None
        self.name = "élő (ESPN, 22 hírportál, 11 szorzóforrás" + (" + The Odds API)" if cfg["odds_api_key"] else ")")

    def teams(self):
        d, _ = get_json(SITE + "/teams", {"limit": 50})
        out = {}
        for sp in d.get("sports", []):
            for lg in sp.get("leagues", []):
                for t in lg.get("teams", []):
                    r = team_rec(t.get("team", t), nba=True)
                    out[r["id"]] = r
        return out

    # Az ESPN nem minden paraméter-kombinációt fogad el (400 Bad Request).
    # Sorban kipróbáljuk a változatokat, és az elsőt, ami működik, megjegyezzük.
    SB_VARIANTS = [{"limit": 1000}, {"limit": 300}, {"limit": 100}, {}]

    def scoreboard(self, d1: date, d2: date):
        rng = f"{d1:%Y%m%d}" if d1 == d2 else f"{d1:%Y%m%d}-{d2:%Y%m%d}"
        order = ([self._sb_ok] if getattr(self, "_sb_ok", None) is not None else []) + \
            [v for v in self.SB_VARIANTS if v != getattr(self, "_sb_ok", None)]
        last = None
        for extra in order:
            try:
                d, _ = get_json(SITE + "/scoreboard", {"dates": rng, **extra}, timeout=25)
                self._sb_ok = extra
                return d.get("events", [])
            except urllib.error.HTTPError as e:
                last = e
                if e.code != 400:
                    raise
        raise last

    def injuries(self):
        d, _ = get_json(SITE + "/injuries")
        out = []
        for tm in d.get("injuries", []):
            for inj in tm.get("injuries", []):
                ath = inj.get("athlete") or {}
                det = inj.get("details") or {}
                out.append({"team_id": str(tm.get("id") or (ath.get("team") or {}).get("id") or ""),
                            "team_name": tm.get("displayName") or "",
                            "player": ath.get("displayName") or "?", "status": inj.get("status") or "",
                            "comment": inj.get("shortComment") or inj.get("longComment") or "",
                            "type": det.get("type") or "", "ret": det.get("returnDate") or "",
                            "ts": parse_iso(inj.get("date"))})
        return out

    def player_stats(self, season):
        out = {}
        for page in range(1, 16):
            d, _ = get_json(STATS_URL, {"region": "us", "lang": "en", "contentorigin": "espn", "isqualified": "false",
                                        "page": page, "limit": 100, "season": season, "seasontype": 2,
                                        "sort": "offensive.avgPoints:desc"}, timeout=20)
            cats = {c.get("name"): c.get("names") or [] for c in d.get("categories", [])}
            aths = d.get("athletes") or []
            if not aths:
                break
            for a in aths:
                ath = a.get("athlete") or {}
                vals = {}
                for c in a.get("categories", []):
                    names = cats.get(c.get("name")) or c.get("names") or []
                    for k, v in zip(names, c.get("totals") or c.get("values") or []):
                        vals[k] = v
                name = ath.get("displayName")
                if not name:
                    continue
                out[norm_name(name)] = {"name": name, "ppg": num(vals.get("avgPoints")),
                                        "mpg": num(vals.get("avgMinutes")), "gp": num(vals.get("gamesPlayed")),
                                        "team": ath.get("teamShortName") or ""}
            pg = d.get("pagination") or {}
            if pg.get("pages") and page >= int(pg["pages"]):
                break
        return out

    def news(self, team):
        items = []
        try:
            d, _ = get_json(SITE + "/news", {"team": team["id"], "limit": 15})
            for a in d.get("articles", []):
                title = a.get("headline")
                if title:
                    items.append({"title": title, "url": ((a.get("links") or {}).get("web") or {}).get("href"),
                                  "src": "ESPN", "ts": parse_iso(a.get("published"))})
        except Exception:
            pass
        try:
            items += self._google_news(f'"{team["name"]}" when:7d')
        except Exception:
            pass
        seen, out = set(), []
        for it in sorted(items, key=lambda x: -(x.get("ts") or 0)):
            key = re.sub(r"\W+", "", it["title"].lower())[:60]
            if key not in seen:
                seen.add(key)
                out.append(it)
        return out[:20]

    @staticmethod
    def _google_news(query):
        params = {"q": query, "hl": "en-US", "gl": "US", "ceid": "US:en"}
        body, _ = http_get("https://news.google.com/rss/search", params, timeout=10)
        root = ET.fromstring(body)
        out = []
        for item in list(root.iter("item"))[:25]:
            title = (item.findtext("title") or "").strip()
            src = item.findtext("source") or "Google News"
            if title.endswith(" - " + src):
                title = title[: -len(src) - 3]
            try:
                ts = parsedate_to_datetime(item.findtext("pubDate")).timestamp()
            except Exception:
                ts = None
            out.append({"title": title, "url": item.findtext("link"), "src": src, "ts": ts})
        return out

    def odds_sources(self):
        cfg = self.cfg
        # sorrend számít: ha egy iroda több forrásból is jön, az elsőként szereplő marad meg
        src = [("Pinnacle", lambda: odds_pinnacle(cfg)), ("DraftKings", lambda: odds_draftkings(cfg)),
               ("FanDuel", lambda: odds_fanduel(cfg)), ("Bovada", lambda: odds_bovada(cfg))]
        for op, title, mkt in cfg["kambi_ops"]:
            src.append((f"{title} (Kambi)", lambda op=op, title=title, mkt=mkt: odds_kambi(cfg, op, title, mkt)))
        src += [("Action Network", lambda: odds_action(cfg)), ("SportsbookReview", lambda: odds_sbr(cfg)),
                ("Polymarket", lambda: odds_polymarket(cfg)), ("Kalshi", lambda: odds_kalshi(cfg))]
        return src

    def portal_news(self, portal):
        name, rss, domain = portal
        if rss:
            try:
                body, _ = http_get(rss, timeout=12, headers={"Accept": "application/rss+xml, application/xml, text/xml, */*"})
                items = parse_feed(body, name)
                if items:
                    return items[:40], "RSS"
            except Exception:
                pass
        items = self._google_news(f"site:{domain} NBA when:3d")
        for it in items:
            it["src"] = name
        return items, "Google News"

    def odds(self):
        key = self.cfg["odds_api_key"]
        if not key:
            return None
        d, hdr = get_json(ODDS_URL, {"apiKey": key, "regions": self.cfg["odds_regions"],
                                     "markets": "h2h,spreads,totals", "oddsFormat": "decimal", "dateFormat": "iso"})
        self.odds_left = hdr.get("x-requests-remaining")
        return parse_odds_api(d)


def parse_odds_api(data):
    out = []
    for ev in data:
        h, a = ev.get("home_team"), ev.get("away_team")
        books = []
        for b in ev.get("bookmakers", []):
            row = {"book": b.get("title") or b.get("key"), "src": "Odds API", "upd": b.get("last_update")}
            for m in b.get("markets", []):
                for o in m.get("outcomes", []):
                    if m["key"] == "h2h":
                        if o["name"] == h:
                            row["ml_h"] = o["price"]
                        elif o["name"] == a:
                            row["ml_a"] = o["price"]
                    elif m["key"] == "spreads":
                        if o["name"] == h:
                            row["spread_h"], row["sp_h"] = o.get("point"), o["price"]
                        elif o["name"] == a:
                            row["sp_a"] = o["price"]
                    elif m["key"] == "totals":
                        if o["name"] == "Over":
                            row["total"], row["over"] = o.get("point"), o["price"]
                        elif o["name"] == "Under":
                            row["under"] = o["price"]
            books.append(row)
        out.append({"home": nick(h), "away": nick(a), "ts": parse_iso(ev.get("commence_time")), "books": books})
    return out


# ---------------------------------------------------------------------------
# Fogadóirodai források kulcs nélkül
# Mindegyik ugyanolyan listát ad vissza: [{"home": becenév, "away": becenév, "ts": unix, "books": [sor, ...]}]
# Egy sor: book, src, ml_h, ml_a (tizedes szorzó), spread_h (hazai hendikep), sp_h, sp_a, total, over, under.
# Ezek nem hivatalos, nyilvános végpontok: ha valamelyik megváltozik, csak az a forrás esik ki.
# ---------------------------------------------------------------------------
def _fix_row(r):
    for k in ("ml_h", "ml_a", "sp_h", "sp_a", "over", "under"):
        v = r.get(k)
        if v is not None and not (1.01 <= v <= 30):
            r[k] = None
    if r.get("spread_h") is not None and abs(r["spread_h"]) > 30:
        r["spread_h"] = None
    if r.get("total") is not None and not (170 <= r["total"] <= 290):
        r["total"] = None
    return any(r.get(k) is not None for k in ("ml_h", "spread_h", "total"))


def odds_event(home, away, ts, books):
    books = [b for b in books if _fix_row(b)]
    if not books or not home or not away or not ts:
        return None
    return {"home": nick(home), "away": nick(away), "ts": ts, "books": books}


PIN_URL = "https://guest.api.arcadia.pinnacle.com/0.1/leagues/487"
PIN_HDR = {"X-API-Key": "CmX2KcMrXuFmNg6YFbmTxE0y9CIrOi0R", "Origin": "https://www.pinnacle.com",
           "Referer": "https://www.pinnacle.com/"}


def odds_pinnacle(cfg):
    mus, _ = get_json(PIN_URL + "/matchups", headers=PIN_HDR)
    mks, _ = get_json(PIN_URL + "/markets/straight", headers=PIN_HDR)
    games = {}
    for m in mus:
        if m.get("type") != "matchup" or m.get("parentId") or m.get("special"):
            continue
        ps = {p.get("alignment"): p.get("name") for p in m.get("participants", [])}
        if ps.get("home") and ps.get("away"):
            games[m["id"]] = (ps["home"], ps["away"], parse_iso(m.get("startTime")), {"book": "Pinnacle", "src": "Pinnacle"})
    for k in mks:
        g = games.get(k.get("matchupId"))
        if not g or k.get("period") != 0 or k.get("isAlternate"):
            continue
        r = g[3]
        pr = {x.get("designation"): x for x in k.get("prices", [])}
        t = k.get("type")
        if t == "moneyline":
            r["ml_h"], r["ml_a"] = am_to_dec((pr.get("home") or {}).get("price")), am_to_dec((pr.get("away") or {}).get("price"))
        elif t == "spread" and pr.get("home"):
            r["spread_h"] = num(pr["home"].get("points"))
            r["sp_h"], r["sp_a"] = am_to_dec(pr["home"].get("price")), am_to_dec((pr.get("away") or {}).get("price"))
        elif t == "total" and pr.get("over"):
            r["total"] = num(pr["over"].get("points"))
            r["over"], r["under"] = am_to_dec(pr["over"].get("price")), am_to_dec((pr.get("under") or {}).get("price"))
    return [e for e in (odds_event(h, a, ts, [r]) for h, a, ts, r in games.values()) if e]


DK_URL = "https://sportsbook-nash.draftkings.com/api/sportscontent/dkusnj/v1/leagues/42648"


def odds_draftkings(cfg):
    d, _ = get_json(DK_URL)
    evs = {str(e.get("id")): e for e in d.get("events", [])}
    mks = {str(m.get("id")): m for m in d.get("markets", [])}
    rows = {}
    for sel in d.get("selections", []):
        m = mks.get(str(sel.get("marketId")))
        ev = evs.get(str(m.get("eventId"))) if m else None
        if not ev:
            continue
        name = ((m.get("marketType") or {}).get("name") or m.get("name") or "").strip().lower()
        if name not in ("moneyline", "spread", "total"):
            continue
        r = rows.setdefault(str(ev["id"]), {"book": "DraftKings", "src": "DraftKings"})
        ot = (sel.get("outcomeType") or "").lower()
        dec = num(sel.get("trueOdds")) or num((sel.get("displayOdds") or {}).get("decimal"))
        pts = num(sel.get("points"))
        if name == "moneyline":
            r["ml_h" if ot == "home" else "ml_a" if ot == "away" else "_"] = dec
        elif name == "spread":
            if ot == "home":
                r["spread_h"], r["sp_h"] = pts, dec
            elif ot == "away":
                r["sp_a"] = dec
        elif name == "total":
            if ot == "over":
                r["total"], r["over"] = pts, dec
            elif ot == "under":
                r["under"] = dec
    out = []
    for eid, r in rows.items():
        ev = evs[eid]
        ps = {(p.get("venueRole") or "").lower(): p.get("name") for p in ev.get("participants", [])}
        r.pop("_", None)
        e = odds_event(ps.get("home"), ps.get("away"), parse_iso(ev.get("startEventDate")), [r])
        if e:
            out.append(e)
    return out


BOV_URL = "https://www.bovada.lv/services/sports/event/coupon/events/A/description/basketball/nba"


def odds_bovada(cfg):
    d, _ = get_json(BOV_URL, {"marketFilterId": "def", "preMatchOnly": "true", "lang": "en"})
    out = []
    for grp in d if isinstance(d, list) else []:
        for ev in grp.get("events", []):
            comp = {bool(c.get("home")): c.get("name") for c in ev.get("competitors", [])}
            r = {"book": "Bovada", "src": "Bovada"}
            for dg in ev.get("displayGroups", []):
                for mk in dg.get("markets", []):
                    per = mk.get("period") or {}
                    if not (per.get("main") or per.get("abbreviation") == "G"):
                        continue
                    desc = (mk.get("description") or "").strip().lower()
                    oc = {o.get("type"): (o.get("price") or {}) for o in mk.get("outcomes", [])}
                    dec = lambda x: num(x.get("decimal")) or am_to_dec(x.get("american"))  # noqa: E731
                    if desc in ("moneyline", "money line") and "H" in oc and "ml_h" not in r:
                        r["ml_h"], r["ml_a"] = dec(oc["H"]), dec(oc.get("A", {}))
                    elif desc in ("point spread", "spread") and "H" in oc and "spread_h" not in r:
                        r["spread_h"], r["sp_h"], r["sp_a"] = num(oc["H"].get("handicap")), dec(oc["H"]), dec(oc.get("A", {}))
                    elif desc in ("total", "total points") and "O" in oc and "total" not in r:
                        r["total"], r["over"], r["under"] = num(oc["O"].get("handicap")), dec(oc["O"]), dec(oc.get("U", {}))
            ts = (num(ev.get("startTime")) or 0) / 1000
            e = odds_event(comp.get(True), comp.get(False), ts, [r])
            if e:
                out.append(e)
    return out


KAMBI_URL = "https://eu-offering-api.kambicdn.com/offering/v2018/{op}/listView/basketball/nba/all/all/matches.json"


def odds_kambi(cfg, op="ub", title="Unibet", market="GB"):
    d, _ = get_json(KAMBI_URL.format(op=op), {"lang": "en_GB", "market": market, "useCombined": "true",
                                              "client_id": 2, "channel_id": 1, "ncid": int(time.time() * 1000)})
    out = []
    for item in d.get("events", []):
        ev = item.get("event") or {}
        r = {"book": title, "src": f"Kambi ({title})"}
        for bo in item.get("betOffers", []):
            lab = ((bo.get("criterion") or {}).get("englishLabel") or (bo.get("criterion") or {}).get("label") or "").lower()
            if any(w in lab for w in ("half", "quarter", " by ", "player")):
                continue
            bt = bo.get("betOfferType") or {}
            typ = (bt.get("englishName") or bt.get("name") or "").lower()
            oc = {o.get("type"): o for o in bo.get("outcomes", [])}
            k = lambda o: (num((o or {}).get("odds")) or 0) / 1000 or None  # noqa: E731
            ln = lambda o: (num((o or {}).get("line")) / 1000) if num((o or {}).get("line")) is not None else None  # noqa: E731
            if (typ == "match" or "moneyline" in lab) and "OT_ONE" in oc and "ml_h" not in r:
                r["ml_h"], r["ml_a"] = k(oc["OT_ONE"]), k(oc.get("OT_TWO"))
            elif typ == "handicap" and "OT_ONE" in oc and "spread_h" not in r:
                r["spread_h"], r["sp_h"], r["sp_a"] = ln(oc["OT_ONE"]), k(oc["OT_ONE"]), k(oc.get("OT_TWO"))
            elif "over/under" in typ and "OT_OVER" in oc and "total" not in r:
                r["total"], r["over"], r["under"] = ln(oc["OT_OVER"]), k(oc["OT_OVER"]), k(oc.get("OT_UNDER"))
        e = odds_event(ev.get("homeName"), ev.get("awayName"), parse_iso(ev.get("start")), [r])
        if e:
            out.append(e)
    return out


AN_URL = "https://api.actionnetwork.com/web"
AN_BOOK_IDS = "15,30,68,69,71,75,79,123,247,972,973,974"
AN_FALLBACK = {68: "DraftKings", 69: "FanDuel", 75: "BetMGM", 79: "bet365", 123: "Caesars"}
AN_SKIP = {15, 30}   # konszenzus és nyitóvonal, nem iroda
_AN_BOOKS: dict = {}


def odds_action(cfg):
    if not _AN_BOOKS:
        try:
            b, _ = get_json(AN_URL + "/v1/books")
            for x in b.get("books", []):
                _AN_BOOKS[int(x["id"])] = x.get("display_name") or x.get("name")
        except Exception:
            _AN_BOOKS[-1] = ""
    names = {**AN_FALLBACK, **{k: v for k, v in _AN_BOOKS.items() if v}}
    seen, out = set(), []
    today = datetime.now(TZ).date()
    for k in range(cfg["days_ahead"] + 1):
        ds = f"{today + timedelta(days=k):%Y%m%d}"
        try:
            data, _ = get_json(AN_URL + "/v2/scoreboard/nba", {"bookIds": AN_BOOK_IDS, "date": ds, "periods": "event"})
        except urllib.error.HTTPError:
            data, _ = get_json(AN_URL + "/v1/scoreboard/nba", {"bookIds": AN_BOOK_IDS, "date": ds, "period": "game"})
        for g in data.get("games", []):
            if g.get("id") in seen:
                continue
            seen.add(g.get("id"))
            tm = {t.get("id"): t for t in g.get("teams", [])}
            h, a = tm.get(g.get("home_team_id")) or {}, tm.get(g.get("away_team_id")) or {}
            books = []
            for bid, mk in (g.get("markets") or {}).items():        # v2 formátum
                bid = int(bid)
                nm = names.get(bid, f"AN #{bid}")
                if bid in AN_SKIP or re.search(r"consensus|open", nm or "", re.I):
                    continue
                e = (mk or {}).get("event") or {}
                r = {"book": nm, "src": "Action Network"}
                for o in e.get("moneyline") or []:
                    if o.get("side") in ("home", "away"):
                        r["ml_h" if o["side"] == "home" else "ml_a"] = am_to_dec(o.get("odds"))
                for o in e.get("spread") or []:
                    if o.get("side") == "home":
                        r["spread_h"], r["sp_h"] = num(o.get("value")), am_to_dec(o.get("odds"))
                    elif o.get("side") == "away":
                        r["sp_a"] = am_to_dec(o.get("odds"))
                for o in e.get("total") or []:
                    if o.get("side") == "over":
                        r["total"], r["over"] = num(o.get("value")), am_to_dec(o.get("odds"))
                    elif o.get("side") == "under":
                        r["under"] = am_to_dec(o.get("odds"))
                books.append(r)
            for o in g.get("odds") or []:                           # v1 formátum
                bid = o.get("book_id")
                nm = names.get(bid, f"AN #{bid}")
                if bid in AN_SKIP or o.get("type", "game") != "game" or re.search(r"consensus|open", nm or "", re.I):
                    continue
                books.append({"book": nm, "src": "Action Network",
                              "ml_h": am_to_dec(o.get("ml_home")), "ml_a": am_to_dec(o.get("ml_away")),
                              "spread_h": num(o.get("spread_home")), "sp_h": am_to_dec(o.get("spread_home_line")),
                              "sp_a": am_to_dec(o.get("spread_away_line")), "total": num(o.get("total")),
                              "over": am_to_dec(o.get("over")), "under": am_to_dec(o.get("under"))})
            ev = odds_event(h.get("full_name") or h.get("display_name"), a.get("full_name") or a.get("display_name"),
                            parse_iso(g.get("start_time")), books)
            if ev:
                out.append(ev)
    return out


FD_URL = "https://sbapi.nj.sportsbook.fanduel.com/api/content-managed-page"


def odds_fanduel(cfg):
    d, _ = get_json(FD_URL, {"page": "CUSTOM", "customPageId": "nba", "pbHorizontal": "false",
                             "_ak": "FhMFpcPWXMeyZxOx", "timezone": "America/New_York"})
    att = d.get("attachments") or {}
    evs, mks = att.get("events") or {}, att.get("markets") or {}
    rows = {}
    for mk in mks.values():
        ev = evs.get(str(mk.get("eventId")))
        if not ev or " @ " not in (ev.get("name") or ""):
            continue
        away, home = [x.strip() for x in ev["name"].split(" @ ", 1)]
        mt = (mk.get("marketType") or "").upper()
        if mt not in ("MONEY_LINE", "MATCH_HANDICAP_(2-WAY)", "TOTAL_POINTS_(OVER/UNDER)"):
            continue
        r = rows.setdefault(str(mk.get("eventId")), {"_h": home, "_a": away, "_ts": parse_ts(ev.get("openDate")),
                                                      "book": "FanDuel", "src": "FanDuel"})
        for ru in mk.get("runners") or []:
            o = ru.get("winRunnerOdds") or {}
            am = o.get("americanDisplayOdds") or {}
            dec = num(((o.get("trueOdds") or {}).get("decimalOdds") or {}).get("decimalOdds")) or \
                am_to_dec(am.get("americanOddsInt") or am.get("americanOdds"))
            nm = (ru.get("runnerName") or "").strip()
            side = ((ru.get("result") or {}).get("type") or "").upper()
            if side not in ("HOME", "AWAY", "OVER", "UNDER"):
                side = ("HOME" if nm == home else "AWAY" if nm == away else
                        "OVER" if nm.lower().startswith("over") else "UNDER" if nm.lower().startswith("under") else "")
            hc = num(ru.get("handicap"))
            if mt == "MONEY_LINE":
                if side in ("HOME", "AWAY"):
                    r["ml_h" if side == "HOME" else "ml_a"] = dec
            elif mt.startswith("MATCH_HANDICAP"):
                if side == "HOME":
                    r["spread_h"], r["sp_h"] = hc, dec
                elif side == "AWAY":
                    r["sp_a"] = dec
            else:
                if side == "OVER":
                    r["total"], r["over"] = hc, dec
                elif side == "UNDER":
                    r["under"] = dec
    out = []
    for r in rows.values():
        h, a, ts = r.pop("_h"), r.pop("_a"), r.pop("_ts")
        e = odds_event(h, a, ts, [r])
        if e:
            out.append(e)
    return out


SBR_URL = "https://www.sportsbookreview.com/betting-odds/nba-basketball/{path}?date={d}"
SBR_BOOKS = {"bet365": "bet365", "betmgm": "BetMGM", "caesars": "Caesars", "draftkings": "DraftKings",
             "fanduel": "FanDuel", "betrivers": "BetRivers", "fanatics": "Fanatics", "espnbet": "ESPN BET",
             "hardrock": "Hard Rock Bet", "hardrockbet": "Hard Rock Bet", "bovada": "Bovada", "unibet": "Unibet",
             "betonline": "BetOnline", "pointsbet": "PointsBet", "wynnbet": "WynnBET", "betway": "Betway"}


def _next_data(url):
    body, _ = http_get(url, headers={"Accept": "text/html,application/xhtml+xml"}, timeout=20)
    m = re.search(rb'<script id="__NEXT_DATA__" type="application/json"[^>]*>(.*?)</script>', body, re.S)
    if not m:
        raise ValueError("az oldalon nincs __NEXT_DATA__ (valószínűleg bot-védelem)")
    return json.loads(m.group(1))


def odds_sbr(cfg):
    """SportsbookReview összesítő: bet365, BetMGM, Caesars, BetRivers, Fanatics, ESPN BET stb. egy helyen."""
    rows = {}
    today = datetime.now(TZ).date()
    pages = [("", "spread"), ("money-line/full-game/", "ml"), ("totals/full-game/", "total")]
    for k in range(min(cfg["days_ahead"], cfg.get("sbr_days", 4)) + 1):
        ds = f"{today + timedelta(days=k):%Y-%m-%d}"
        for path, kind in pages:
            try:
                nd = _next_data(SBR_URL.format(path=path, d=ds))
            except urllib.error.HTTPError as e:
                if e.code == 404:
                    continue
                raise
            pp = (nd.get("props") or {}).get("pageProps") or {}
            for tb in pp.get("oddsTables") or []:
                for gr in (tb.get("oddsTableModel") or {}).get("gameRows") or []:
                    gv = gr.get("gameView") or {}
                    h, a = gv.get("homeTeam") or {}, gv.get("awayTeam") or {}
                    hn = h.get("fullName") or h.get("displayName") or h.get("name")
                    an = a.get("fullName") or a.get("displayName") or a.get("name")
                    gid = gv.get("gameId") or f"{hn}|{an}|{gv.get('startDate')}"
                    for ov in gr.get("oddsViews") or []:
                        if not ov:
                            continue
                        slug = (ov.get("sportsbook") or "").lower()
                        cl = ov.get("currentLine") or {}
                        r = rows.setdefault((gid, slug), {"_g": gid, "_h": hn, "_a": an,
                                                          "_ts": parse_ts(gv.get("startDate")),
                                                          "book": SBR_BOOKS.get(slug, slug.title()),
                                                          "src": "SportsbookReview"})
                        if kind == "ml":
                            r["ml_h"], r["ml_a"] = am_to_dec(cl.get("homeOdds")), am_to_dec(cl.get("awayOdds"))
                        elif kind == "spread":
                            r["spread_h"] = num(cl.get("homeSpread"))
                            r["sp_h"], r["sp_a"] = am_to_dec(cl.get("homeOdds")), am_to_dec(cl.get("awayOdds"))
                        else:
                            r["total"] = num(cl.get("total"))
                            r["over"], r["under"] = am_to_dec(cl.get("overOdds")), am_to_dec(cl.get("underOdds"))
    games = defaultdict(list)
    for r in rows.values():
        games[r["_g"]].append(r)
    out = []
    for lst in games.values():
        h, a, ts = lst[0]["_h"], lst[0]["_a"], lst[0]["_ts"]
        books = [{k: v for k, v in r.items() if not k.startswith("_")} for r in lst]
        e = odds_event(h, a, ts, books)
        if e:
            out.append(e)
    return out


PM_URL = "https://gamma-api.polymarket.com/events"


def odds_polymarket(cfg):
    """Polymarket előrejelző piac: csak győztes-valószínűség (árrés nélkül)."""
    d, _ = get_json(PM_URL, {"tag_slug": "nba", "closed": "false", "active": "true", "limit": 300})
    out = []
    for ev in d if isinstance(d, list) else d.get("data", []):
        for mk in ev.get("markets") or []:
            q = mk.get("question") or ""
            smt = (mk.get("sportsMarketType") or "moneyline").lower()
            if smt != "moneyline" or re.search(r"spread|o/u|over|under|1h|half|quarter|total|\(", q, re.I):
                continue
            try:
                outs = json.loads(mk.get("outcomes") or "[]")
                prices = [float(x) for x in json.loads(mk.get("outcomePrices") or "[]")]
            except Exception:
                continue
            if len(outs) != 2 or len(prices) != 2:
                continue
            n1, n2 = resolve_nick(outs[0]), resolve_nick(outs[1])
            if not n1 or not n2 or n1 == n2 or not (0.02 < prices[0] < 0.98):
                continue
            p1 = prices[0] / sum(prices)
            ts = parse_ts(mk.get("gameStartTime") or ev.get("startTime") or ev.get("endDate"))
            e = odds_event(n1, n2, ts, [{"book": "Polymarket", "src": "Polymarket", "exchange": True,
                                         "ml_h": round(1 / p1, 3), "ml_a": round(1 / (1 - p1), 3)}])
            if e:
                e["unordered"] = True
                out.append(e)
            break
    return out


KALSHI_URL = "https://api.elections.kalshi.com/trade-api/v2/events"
_MON = {m: i for i, m in enumerate(["JAN", "FEB", "MAR", "APR", "MAY", "JUN", "JUL", "AUG", "SEP", "OCT", "NOV", "DEC"], 1)}


def _kalshi_price(mk):
    def dollars(k):
        v = num(mk.get(k + "_dollars"))
        if v is None:
            c = num(mk.get(k))
            v = c / 100 if c is not None else None
        return v
    b, a, last = dollars("yes_bid"), dollars("yes_ask"), dollars("last_price")
    if b and a and 0 < b <= a and a - b <= 0.10:
        return (a + b) / 2
    return last if last and 0 < last < 1 else None


def odds_kalshi(cfg):
    """Kalshi (amerikai szabályozott előrejelző tőzsde): csak győztes-valószínűség."""
    d, _ = get_json(KALSHI_URL, {"series_ticker": "KXNBAGAME", "status": "open",
                                 "with_nested_markets": "true", "limit": 200})
    out = []
    for ev in d.get("events", []):
        probs = {}
        for mk in ev.get("markets") or []:
            nk = resolve_nick((mk.get("ticker") or "").rsplit("-", 1)[-1]) or resolve_nick(mk.get("yes_sub_title"))
            p = _kalshi_price(mk)
            if nk and p:
                probs[nk] = p
        m = re.search(r"-(\d{2})([A-Z]{3})(\d{2})", ev.get("event_ticker") or "")
        if len(probs) != 2 or not m or m.group(2) not in _MON:
            continue
        gd = datetime(2000 + int(m.group(1)), _MON[m.group(2)], int(m.group(3)), tzinfo=timezone.utc)
        ts = (gd + timedelta(hours=25)).timestamp()     # kb. este 8-9 keleti parti idő; a párosítás ±12 órát enged
        (n1, p1), (n2, p2) = probs.items()
        q = p1 / (p1 + p2)
        if not (0.02 < q < 0.98):
            continue
        e = odds_event(n1, n2, ts, [{"book": "Kalshi", "src": "Kalshi", "exchange": True,
                                     "ml_h": round(1 / q, 3), "ml_a": round(1 / (1 - q), 3)}])
        if e:
            e["unordered"] = True
            out.append(e)
    return out


# ---------------------------------------------------------------------------
# Amerikai NBA-hírportálok. Ha az RSS nem érhető el (vagy nincs), Google News "site:" kereséssel pótolja.
# ---------------------------------------------------------------------------
FOX_RSS = ("https://api.foxsports.com/v2/content/optimized-rss?partnerKey=MB0Wehpmuj2lUhuRhQaafhBjAJqaPU244mlTDK1i"
           "&size=30&tags=fs/nba")
NEWS_PORTALS = [
    ("ESPN", "https://www.espn.com/espn/rss/nba/news", "espn.com"),
    ("The Athletic", "https://www.nytimes.com/athletic/rss/nba/", "nytimes.com"),
    ("CBS Sports", "https://www.cbssports.com/rss/headlines/nba/", "cbssports.com"),
    ("Yahoo Sports", "https://sports.yahoo.com/nba/rss.xml", "sports.yahoo.com"),
    ("NBA.com", None, "nba.com"),
    ("Bleacher Report", None, "bleacherreport.com"),
    ("Fox Sports", FOX_RSS, "foxsports.com"),
    ("NBC Sports", None, "nbcsports.com"),
    ("Sports Illustrated", None, "si.com"),
    ("USA Today", "https://rssfeeds.usatoday.com/UsatodaycomNba-TopStories", "usatoday.com"),
    ("The Ringer", None, "theringer.com"),
    ("Sporting News", None, "sportingnews.com"),
    ("SB Nation", "https://www.sbnation.com/rss/nba/index.xml", "sbnation.com"),
    ("RotoWire", "https://www.rotowire.com/rss/news.php?sport=NBA", "rotowire.com"),
    ("Hoops Rumors", "https://www.hoopsrumors.com/feed", "hoopsrumors.com"),
    ("HoopsHype", "https://hoopshype.com/feed/", "hoopshype.com"),
    ("RealGM", "https://basketball.realgm.com/rss/wiretap/0/0.xml", "realgm.com"),
    ("ClutchPoints", None, "clutchpoints.com"),
    ("New York Post", "https://nypost.com/nba/feed/", "nypost.com"),
    ("Basketball Insiders", "https://www.basketballinsiders.com/feed/", "basketballinsiders.com"),
    ("Sportskeeda", None, "sportskeeda.com"),
    ("Fadeaway World", None, "fadeawayworld.net"),
]


def parse_feed(body, src):
    """RSS és Atom egyaránt."""
    root = ET.fromstring(body)
    out = []
    for el in root.iter():
        tag = el.tag.rsplit("}", 1)[-1]
        if tag not in ("item", "entry"):
            continue
        get = {c.tag.rsplit("}", 1)[-1]: c for c in el}
        title = (get["title"].text or "").strip() if "title" in get else ""
        if not title:
            continue
        link = None
        if "link" in get:
            link = get["link"].text or get["link"].get("href")
        ts = None
        for k in ("pubDate", "published", "updated", "date"):
            if k in get and get[k].text:
                try:
                    ts = parsedate_to_datetime(get[k].text.strip()).timestamp()
                except Exception:
                    ts = parse_ts(get[k].text.strip())
                if ts:
                    break
        out.append({"title": re.sub(r"\s+", " ", title), "url": (link or "").strip() or None, "src": src, "ts": ts})
    return out


def book_key(name):
    return re.sub(r"[^a-z0-9]", "", (name or "").lower()).replace("sportsbook", "")


# ---------------------------------------------------------------------------
# Demó adatforrás (internet nélkül)
# ---------------------------------------------------------------------------
DEMO_TEAMS = [
    ("ATL", "Atlanta Hawks"), ("BOS", "Boston Celtics"), ("BKN", "Brooklyn Nets"), ("CHA", "Charlotte Hornets"),
    ("CHI", "Chicago Bulls"), ("CLE", "Cleveland Cavaliers"), ("DAL", "Dallas Mavericks"), ("DEN", "Denver Nuggets"),
    ("DET", "Detroit Pistons"), ("GS", "Golden State Warriors"), ("HOU", "Houston Rockets"), ("IND", "Indiana Pacers"),
    ("LAC", "LA Clippers"), ("LAL", "Los Angeles Lakers"), ("MEM", "Memphis Grizzlies"), ("MIA", "Miami Heat"),
    ("MIL", "Milwaukee Bucks"), ("MIN", "Minnesota Timberwolves"), ("NO", "New Orleans Pelicans"),
    ("NY", "New York Knicks"), ("OKC", "Oklahoma City Thunder"), ("ORL", "Orlando Magic"),
    ("PHI", "Philadelphia 76ers"), ("PHX", "Phoenix Suns"), ("POR", "Portland Trail Blazers"),
    ("SAC", "Sacramento Kings"), ("SA", "San Antonio Spurs"), ("TOR", "Toronto Raptors"), ("UTAH", "Utah Jazz"),
    ("WSH", "Washington Wizards"),
]


class DemoSource:
    name = "DEMO (kitalált adatok)"

    def __init__(self, cfg):
        self.cfg = cfg
        self.odds_left = None
        self.rng = np.random.default_rng(11)
        self.T = {}
        for i, (ab, nm) in enumerate(DEMO_TEAMS, 1):
            nk = nm.split(" ")[-1]
            self.T[str(i)] = {"id": str(i), "abbreviation": ab, "displayName": nm, "shortDisplayName": nk, "name": nk}
        self.strength = {t: (float(self.rng.normal(0, 4)), float(self.rng.normal(0, 4))) for t in self.T}
        self.events = self._gen()

    def _exp(self, h, a):
        oh, dh = self.strength[h]
        oa, da = self.strength[a]
        return 113 + 1.2 + oh + da, 113 - 1.2 + oa + dh

    def _gen(self):
        now = time.time()
        today = datetime.now(timezone.utc).replace(hour=0, minute=0, second=0, microsecond=0)
        ids = list(self.T)
        cur = season_of(datetime.now(TZ).date())
        evs, gid = [], 900000
        for k in range(-150, self.cfg["days_ahead"] + 1):
            day = today + timedelta(days=k)
            perm = self.rng.permutation(ids)
            for i in range(int(self.rng.integers(4, 10))):
                h, a = str(perm[2 * i]), str(perm[2 * i + 1])
                ts = day + timedelta(hours=23, minutes=30 + 30 * int(self.rng.integers(0, 6)))
                eh, ea = self._exp(h, a)
                hp, ap = round(eh + self.rng.normal(0, 9)), round(ea + self.rng.normal(0, 9))
                if hp == ap:
                    hp += 1
                t0 = ts.timestamp()
                if now > t0 + 2.5 * 3600:
                    state, done, det, sh, sa = "post", True, "Final", hp, ap
                elif now > t0:
                    fr = (now - t0) / (2.5 * 3600)
                    state, done, det, sh, sa = "in", False, f"Q{1 + int(fr * 4)}", round(hp * fr), round(ap * fr)
                else:
                    state, done, det, sh, sa = "pre", False, ts.strftime("%m/%d %H:%M UTC"), 0, 0
                comp = {"neutralSite": False, "competitors": [
                    {"homeAway": "home", "team": self.T[h], "score": str(sh)},
                    {"homeAway": "away", "team": self.T[a], "score": str(sa)}]}
                if state == "pre":
                    m = eh - ea + self.rng.normal(0, 0.7)
                    sp = round(m * 2) / 2
                    p = ND.cdf(m / 12.5)
                    to_am = lambda q: int(-100 * q / (1 - q)) if q > 0.5 else int(100 * (1 - q) / q)  # noqa
                    comp["odds"] = [{"provider": {"name": "Demo Bet ESPN"}, "spread": -sp,
                                     "overUnder": round((eh + ea + self.rng.normal(0, 1.0)) * 2) / 2,
                                     "homeTeamOdds": {"favorite": sp > 0, "moneyLine": to_am(p * 1.02)},
                                     "awayTeamOdds": {"favorite": sp <= 0, "moneyLine": to_am((1 - p) * 1.02)}}]
                gid += 1
                evs.append({"id": str(gid), "date": ts.strftime("%Y-%m-%dT%H:%MZ"),
                            "season": {"year": cur, "type": 2},
                            "status": {"type": {"state": state, "completed": done, "shortDetail": det}},
                            "competitions": [comp]})
        return evs

    def teams(self):
        return {t: team_rec(v, nba=True) for t, v in self.T.items()}

    def scoreboard(self, d1, d2):
        return [e for e in self.events if d1 <= us_date(parse_iso(e["date"])) <= d2]

    def injuries(self):
        r = np.random.default_rng(int(time.time() // 900))
        out = []
        for t in r.choice(list(self.T), 10, replace=False):
            for k in range(int(r.integers(1, 3))):
                out.append({"team_id": str(t), "team_name": self.T[t]["displayName"],
                            "player": f"{self.T[t]['abbreviation']} Player {k + 1}",
                            "status": str(r.choice(["Out", "Questionable", "Doubtful", "Day-To-Day"])),
                            "comment": "Demo sérülés", "type": str(r.choice(["Ankle", "Knee", "Hamstring", "Back"])),
                            "ret": "", "ts": time.time() - float(r.uniform(0, 40)) * 86400})
        return out

    def player_stats(self, season):
        r = np.random.default_rng(3)
        return {norm_name(f"{v['abbreviation']} Player {k}"): {"name": f"{v['abbreviation']} Player {k}",
                                                               "ppg": float(r.uniform(4, 28)), "mpg": float(r.uniform(12, 36)),
                                                               "gp": 40, "team": v["abbreviation"]}
                for v in self.T.values() for k in (1, 2)}

    def news(self, team):
        nm = team["short"]
        pos = ["{n} win fourth straight", "{n} star cleared to return", "{n} rout division rival",
               "Career-high night lifts {n}"]
        neg = ["{n} guard sidelined with ankle sprain", "{n} lose third straight", "{n} forward ruled out vs rival",
               "{n} skid continues"]
        neu = ["{n} reportedly exploring trade options", "{n} coach talks rotation", "What to watch: {n} this week"]
        out = []
        for _ in range(int(self.rng.integers(2, 8))):
            u = self.rng.random()
            pool = pos if u > 0.62 else neg if u < 0.33 else neu
            out.append({"title": pool[int(self.rng.integers(len(pool)))].format(n=nm), "url": None, "src": "Demo",
                        "ts": time.time() - float(self.rng.uniform(0, 7 * 86400))})
        return out

    def odds_sources(self):
        spec = [("Pinnacle", ["Pinnacle"]), ("DraftKings", ["DraftKings"]), ("FanDuel", ["FanDuel"]),
                ("Bovada", ["Bovada"]), ("Unibet (Kambi)", ["Unibet"]), ("Paf (Kambi)", ["Paf"]),
                ("Action Network", ["FanDuel", "BetMGM", "Caesars", "DraftKings"]),
                ("SportsbookReview", ["bet365", "BetRivers", "Fanatics", "ESPN BET", "BetMGM"]),
                ("Polymarket", ["Polymarket"]), ("Kalshi", ["Kalshi"])]
        return [(n, (lambda n=n, b=b: self._demo_odds(b, n))) for n, b in spec]

    def portal_news(self, portal):
        name = portal[0]
        teams = list(self.T.values())
        tpl = ["{a} star ruled out vs {b} with ankle sprain", "{a} reportedly interested in trade for {b} guard",
               "{a} win fifth straight, beat {b}", "{a} coach on rotation changes", "{a} forward cleared to return",
               "Sources: {a} exploring buyout options", "{a} lose to {b} in overtime", "{a} rest starters on back-to-back"]
        out = []
        for _ in range(int(self.rng.integers(3, 9))):
            a, b = self.rng.choice(len(teams), 2, replace=False)
            out.append({"title": tpl[int(self.rng.integers(len(tpl)))].format(a=teams[a]["name"].split(" ")[-1],
                                                                             b=teams[b]["name"].split(" ")[-1]),
                        "url": None, "src": name, "ts": time.time() - float(self.rng.uniform(0, 3 * 86400))})
        return out, "Demo"

    def odds(self):
        return None

    def _demo_odds(self, book_names, src):
        out = []
        for e in self.events:
            if e["status"]["type"]["state"] != "pre":
                continue
            c = e["competitions"][0]["competitors"]
            h, a = c[0]["team"]["id"], c[1]["team"]["id"]
            eh, ea = self._exp(h, a)
            books = []
            for b in book_names:
                m = eh - ea + self.rng.normal(0, 0.7)
                p = ND.cdf(m / 12.5)
                tot = round((eh + ea + self.rng.normal(0, 1.0)) * 2) / 2
                if src in ("Polymarket", "Kalshi"):
                    books.append({"book": b, "src": src, "exchange": True, "ml_h": round(1 / p, 3),
                                  "ml_a": round(1 / (1 - p), 3)})
                    continue
                books.append({"book": b, "src": src, "ml_h": round(0.95 / p, 2), "ml_a": round(0.95 / (1 - p), 2),
                              "spread_h": -round(m * 2) / 2, "sp_h": 1.9, "sp_a": 1.9,
                              "total": tot, "over": 1.9, "under": 1.9})
            out.append({"home": nick(self.T[h]["name"]), "away": nick(self.T[a]["name"]),
                        "ts": parse_iso(e["date"]), "books": books})
        return out


# ---------------------------------------------------------------------------
# Elemző motor
# ---------------------------------------------------------------------------
class Engine:
    def __init__(self, src, cfg):
        self.src, self.cfg = src, cfg
        self.dlock = threading.RLock()
        self.clock = threading.Lock()
        self.slock = threading.Lock()
        self.teams: dict[str, dict] = {}
        self.games: dict[str, dict] = {}
        self.injuries: dict[str, list] = {}
        self.pstats: dict[str, dict] = {}
        self.news: dict[str, dict] = {}
        self.team_news_raw: dict[str, list] = {}   # csapatonkénti keresésekből
        self.feed_items: list = []                 # az összes portál ligaszintű hírei
        self.feed_status: dict = {}
        self.matchers: list = []                   # (regex, csapat id) a hírek csapathoz rendeléséhez
        self.odds_events: list = []          # The Odds API
        self.odds_src: dict = {}             # kulcs nélküli források: név -> {events, ok, err, games, books}
        self.ratings = None
        self.sched: dict[str, list] = {}
        self.status = {"phase": "Indulás…", "mode": src.name, "last_sched": None, "last_inj": None,
                       "last_news": None, "last_odds": None, "odds_left": None, "news_done": 0, "n": 30,
                       "players": 0, "errors": deque(maxlen=8)}
        self.pred_path = Path(cfg["pred_file"])
        try:
            self.preds = json.loads(self.pred_path.read_text(encoding="utf-8"))
        except Exception:
            self.preds = {}
        self.state = {"status": self.status}

    def err(self, msg):
        self.status["errors"].append(f"{now_str()} {msg}")

    # ----- adatgyűjtés -----
    def load_games(self, d1: date, d2: date, chunk=10):
        d = d1
        fails = []
        while d <= d2:
            if d.month in (7, 8, 9):          # nyári szünet: nincs NBA-meccs
                d = date(d.year, 10, 1)
                continue
            e = min(d + timedelta(days=chunk - 1), d2)
            if e.month in (7, 8, 9):
                e = date(e.year, 6, 30)
            try:
                evs = self.src.scoreboard(d, e)
            except Exception as ex:
                evs = []
                if chunk > 1:   # tartalék: napi lekérés
                    self.load_games(d, e, chunk=1)
                else:
                    fails.append((d, str(ex)[:80]))
            with self.dlock:
                for ev in evs:
                    g, tms = parse_event(ev)
                    if not g:
                        continue
                    self.games[g["id"]] = g
                    for t in tms:
                        if t["id"] not in self.teams:
                            self.teams[t["id"]] = t
            d = e + timedelta(days=1)
        if fails:
            self.err(f"Menetrend: {len(fails)} nap nem tölthető le ({fails[0][0]} … {fails[-1][0]}), utolsó hiba: {fails[-1][1]}")

    def load_history(self):
        today = datetime.now(TZ).date()
        start = date(season_of(today) - 2, 10, 1)
        done = [g["ts"] for g in self.games.values() if g["completed"]]
        if done:   # gyorsítótárból betöltött eredmények után csak a hiányzó napokat kéri le
            start = max(start, us_date(max(done)) - timedelta(days=3))
        self.status["phase"] = f"Eredmények letöltése {start} óta…"
        self.load_games(start, today + timedelta(days=self.cfg["days_ahead"] + 1))

    def n_completed(self):
        return sum(1 for g in self.games.values() if g["completed"])

    def fit_ratings(self):
        with self.dlock:
            games = [g for g in self.games.values()
                     if g["completed"] and g["stype"] in (2, 3) and g["hs"] is not None]
        if len(games) < 30:
            self.ratings = None
            return
        tids = sorted({g["home"] for g in games} | {g["away"] for g in games})
        ix = {t: i for i, t in enumerate(tids)}
        n, P = len(tids), 2 + 2 * len(tids)
        A = np.zeros((2 * len(games), P))
        y = np.zeros(2 * len(games))
        w = np.zeros(2 * len(games))
        now = time.time()
        cur = season_of(datetime.now(TZ).date())
        hl = self.cfg["half_life_days"]
        for k, g in enumerate(games):
            wt = 0.5 ** (max(0.0, now - g["ts"]) / 86400 / hl)
            if g["season"] < cur:
                wt *= self.cfg["prev_season_weight"]
            hv = 0.0 if g["neutral"] else 1.0
            h, a = ix[g["home"]], ix[g["away"]]
            r = 2 * k
            A[r, 0], A[r, 1], A[r, 2 + h], A[r, 2 + n + a], y[r] = 1, hv, 1, 1, g["hs"]
            A[r + 1, 0], A[r + 1, 1], A[r + 1, 2 + a], A[r + 1, 2 + n + h], y[r + 1] = 1, -hv, 1, 1, g["as"]
            w[r] = w[r + 1] = wt
        L = np.full(P, self.cfg["ridge"])
        L[:2] = 1e-6
        Aw = A * w[:, None]
        x = np.linalg.solve(A.T @ Aw + np.diag(L), Aw.T @ y)
        self.ratings = {"mu": float(x[0]), "hca": float(np.clip(2 * x[1], 0, 5)),
                        "o": {t: float(x[2 + ix[t]]) for t in tids},
                        "d": {t: float(x[2 + n + ix[t]]) for t in tids}, "n_games": len(games)}

    def refresh_injuries(self):
        try:
            lst = self.src.injuries()
        except Exception as e:
            self.err(f"Sérültlista: {str(e)[:80]}")
            return
        by_name = {t["name"]: tid for tid, t in self.teams.items()}
        out = defaultdict(list)
        for it in lst:
            tid = it["team_id"] if it["team_id"] in self.teams else by_name.get(it["team_name"])
            if tid:
                out[tid].append(it)
        with self.dlock:
            self.injuries = dict(out)
        self.status["last_inj"] = now_str()

    def refresh_stats(self):
        cur = season_of(datetime.now(TZ).date())
        for season in (cur, cur - 1):
            try:
                ps = self.src.player_stats(season)
            except Exception as e:
                self.err(f"Játékosstatisztika {season}: {str(e)[:80]}")
                continue
            if sum(1 for p in ps.values() if (p.get("gp") or 0) >= 3) >= 60 or season == cur - 1:
                if ps:
                    self.pstats = ps
                    self.build_matchers()
                    self.status["players"] = len(ps)
                    self.status["players_season"] = season_label(season)
                    return

    def refresh_odds(self):
        if time.time() - getattr(self, "_odds_ts", 0) < self.cfg["odds_refresh_s"] - 60:
            return        # a kreditkeret miatt ritkábban kérdezzük, mint ahogy a program fut
        try:
            ev = self.src.odds()
        except Exception as e:
            self.err(f"Odds API: {str(e)[:80]}")
            return
        if ev is None:
            return
        with self.dlock:
            self.odds_events = ev
        self._odds_ts = time.time()
        self.status["last_odds"] = now_str()
        self.status["odds_left"] = self.src.odds_left

    # ----- háttérciklusok -----
    def sched_loop(self):
        while True:
            time.sleep(self.cfg["sched_refresh_s"])
            try:
                before = self.n_completed()
                today = datetime.now(TZ).date()
                self.load_games(today - timedelta(days=3), today + timedelta(days=self.cfg["days_ahead"] + 1))
                self.status["last_sched"] = now_str()
                if self.n_completed() != before:
                    self.fit_ratings()
                self.compute()
            except Exception as e:
                self.err(f"Menetrend-frissítés: {e}")

    def injury_loop(self):
        while True:
            time.sleep(self.cfg["injury_refresh_s"])
            self.refresh_injuries()

    def stats_loop(self):
        while True:
            self.refresh_stats()
            time.sleep(self.cfg["stats_refresh_s"])

    def odds_loop(self):
        while True:
            self.refresh_odds()
            time.sleep(self.cfg["odds_refresh_s"])

    def free_odds_once(self):
        if not hasattr(self, "_sources"):
            self._sources = self.src.odds_sources()
        for name, fn in self._sources:
            rec = self.odds_src.get(name) or {"events": [], "ok": None, "err": None}
            try:
                ev = fn()
                rec = {**rec, "events": ev, "ok": now_str(), "err": None, "games": len(ev),
                       "books": len({b["book"] for e in ev for b in e["books"]})}
            except Exception as e:
                rec = {**rec, "err": f"{now_str()} {str(e)[:100]}"}
                self.err(f"Szorzók – {name}: {str(e)[:80]}")
            with self.dlock:
                self.odds_src[name] = rec
        self.compute()

    def free_odds_loop(self):
        while True:
            self.free_odds_once()
            time.sleep(self.cfg["odds_free_refresh_s"])

    # ----- hírek -----
    def build_matchers(self):
        ms = []
        abbr2id = {t["abbr"]: tid for tid, t in self.teams.items() if t["nba"]}
        for tid, t in self.teams.items():
            if not t["nba"]:
                continue
            names = {t["name"], t["short"]} | set(NBA_ALIASES.get(t["nick"], []))
            for n in names:
                if n and len(n) >= 3:
                    neg = r"(?! Johnson)" if n == "Magic" else ""
                    ms.append((re.compile(rf"(?<![\w-]){re.escape(n)}(?![\w-]){neg}"), tid))
        for p in self.pstats.values():   # ismert játékosok neve -> csapata (pl. "LeBron James out" -> Lakers)
            tid = abbr2id.get((p.get("team") or "").upper())
            if tid and (p.get("ppg") or 0) >= 9 and p.get("name"):
                ms.append((re.compile(rf"\b{re.escape(p['name'])}\b"), tid))
        self.matchers = ms

    def match_teams(self, title):
        hits = {}
        for rx, tid in self.matchers:
            m = rx.search(title)
            if m and (tid not in hits or m.start() < hits[tid]):
                hits[tid] = m.start()
        return [tid for tid, _ in sorted(hits.items(), key=lambda x: x[1])]

    def rebuild_news(self, tids=None):
        with self.dlock:
            feed = list(self.feed_items)
            raw = dict(self.team_news_raw)
        by_team = defaultdict(list)
        for it in feed:
            for i, tid in enumerate(it.get("teams", [])):
                # több csapatot említő címnél a hangulat csak az elsőként említett (alany) csapatra számít
                by_team[tid].append({**it, "s": it["s"] if i == 0 else 0.0})
        for tid in (tids or [t for t in self.teams if self.teams[t]["nba"]]):
            seen, items = set(), []
            for it in sorted(raw.get(tid, []) + by_team.get(tid, []), key=lambda x: -(x.get("ts") or 0)):
                key = re.sub(r"\W+", "", it["title"].lower())[:60]
                if key not in seen:
                    seen.add(key)
                    items.append(it)
            items = items[:50]
            score, n = aggregate_sentiment(items)
            with self.dlock:
                self.news[tid] = {"score": score, "n": n, "items": items}

    def feeds_once(self):
        if not self.matchers or len(self.matchers) < 100 and self.pstats:
            self.build_matchers()
        allit, seen = [], set()
        cutoff = time.time() - 7 * 86400
        for portal in NEWS_PORTALS:
            name = portal[0]
            try:
                items, via = self.src.portal_news(portal)
                n = 0
                for it in items:
                    if it.get("ts") and it["ts"] < cutoff:
                        continue
                    key = re.sub(r"\W+", "", it["title"].lower())[:60]
                    if key in seen:
                        continue
                    seen.add(key)
                    it["s"] = headline_sentiment(it["title"])
                    it["tags"] = headline_tags(it["title"])
                    it["teams"] = self.match_teams(it["title"])
                    allit.append(it)
                    n += 1
                self.feed_status[name] = {"ok": now_str(), "n": n, "via": via, "err": None}
            except Exception as e:
                self.feed_status[name] = {**self.feed_status.get(name, {}), "err": f"{now_str()} {str(e)[:90]}"}
            time.sleep(0.3)
        allit.sort(key=lambda x: -(x.get("ts") or 0))
        with self.dlock:
            if allit:
                self.feed_items = allit
        self.status["last_feed"] = now_str()
        self.rebuild_news()
        self.compute()

    def feeds_loop(self):
        while True:
            self.feeds_once()
            time.sleep(self.cfg["feed_refresh_s"])

    def team_news_once(self, pause=0.6):
        nba = [t for t in self.teams.values() if t["nba"]]
        self.status["n"] = len(nba)
        for i, t in enumerate(nba):
            try:
                items = self.src.news(t)
                for it in items:
                    it["s"] = headline_sentiment(it["title"])
                    it["tags"] = headline_tags(it["title"])
                with self.dlock:
                    self.team_news_raw[t["id"]] = items
                self.rebuild_news([t["id"]])
            except Exception as e:
                self.err(f"{t['abbr']} hírek: {str(e)[:80]}")
            self.status["news_done"] = i + 1
            time.sleep(pause)
        self.status["last_news"] = now_str()

    def news_loop(self):
        while True:
            self.team_news_once()
            time.sleep(self.cfg["news_refresh_s"])

    # ----- statisztikák -----
    def team_stats(self, games):
        cur = season_of(datetime.now(TZ).date())
        per = defaultdict(list)
        for g in sorted(games, key=lambda g: g["ts"]):
            if not g["completed"] or g["stype"] not in (2, 3) or g["hs"] is None:
                continue
            per[g["home"]].append((g["hs"], g["as"], g["season"], g["stype"]))
            per[g["away"]].append((g["as"], g["hs"], g["season"], g["stype"]))
        out = {}
        for tid, lst in per.items():
            reg = [x for x in lst if x[2] == cur and x[3] == 2]
            lab = season_label(cur)
            if len(reg) < 3:
                reg = [x for x in lst if x[2] == cur - 1 and x[3] == 2]
                lab = season_label(cur - 1) + " (előző)"
            l10 = lst[-10:]
            st = 0
            for pf, pa, *_ in reversed(lst):
                win = pf > pa
                if st == 0:
                    st = 1 if win else -1
                elif (st > 0) == win:
                    st += 1 if win else -1
                else:
                    break
            out[tid] = {
                "season_label": lab, "gp": len(reg),
                "w": sum(1 for x in reg if x[0] > x[1]), "l": sum(1 for x in reg if x[0] < x[1]),
                "pf": float(np.mean([x[0] for x in reg])) if reg else None,
                "pa": float(np.mean([x[1] for x in reg])) if reg else None,
                "l10_w": sum(1 for x in l10 if x[0] > x[1]), "l10_l": sum(1 for x in l10 if x[0] < x[1]),
                "l10_pf": float(np.mean([x[0] for x in l10])) if l10 else None,
                "l10_pa": float(np.mean([x[1] for x in l10])) if l10 else None,
                "streak": st,
            }
        return out

    def rest_days(self, tid, g):
        lst = self.sched.get(tid, [])
        i = bisect.bisect_left(lst, g["ts"] - 3600)
        if i == 0:
            return None
        return (us_date(g["ts"]) - us_date(lst[i - 1])).days

    def inj_impact(self, tid, injuries):
        total, rows = 0.0, []
        for it in injuries.get(tid, []):
            sw = STATUS_W.get((it["status"] or "").lower(), 0.5)
            ps = self.pstats.get(norm_name(it["player"]))
            val = player_value(ps["ppg"], ps["mpg"]) if ps else 1.0
            old = it.get("ts") and (time.time() - it["ts"]) > 30 * 86400
            imp = sw * val * (0.3 if old else 1.0)   # régóta tartó hiányt az eredmények már tartalmaznak
            total += imp
            rows.append({**it, "ppg": ps["ppg"] if ps else None, "mpg": ps["mpg"] if ps else None,
                         "impact": imp, "old": bool(old), "known": bool(ps),
                         "date": datetime.fromtimestamp(it["ts"], TZ).strftime("%Y-%m-%d") if it.get("ts") else ""})
        rows.sort(key=lambda r: -r["impact"])
        return total, rows

    # ----- becslés egy meccsre -----
    def predict(self, g, TS, injuries, news, books):
        cfg = self.cfg
        h, a = g["home"], g["away"]
        pre = g["stype"] == 1
        sd_m = cfg["margin_sd"] * (1.3 if pre else 1.0)
        sd_t = cfg["total_sd"] * (1.3 if pre else 1.0)
        R = self.ratings
        hca = 0.0 if g["neutral"] else (R["hca"] if R else cfg["hca"])
        models = {}
        if R and h in R["o"] and a in R["o"]:
            models["rating"] = mk_pred(R["mu"] + hca / 2 + R["o"][h] + R["d"][a],
                                       R["mu"] - hca / 2 + R["o"][a] + R["d"][h], sd_m)
        th, ta = TS.get(h), TS.get(a)
        for key, pf, pa in (("season", "pf", "pa"), ("form", "l10_pf", "l10_pa")):
            if th and ta and th.get(pf) is not None and ta.get(pf) is not None:
                models[key] = mk_pred((th[pf] + ta[pa]) / 2 + hca / 2, (ta[pf] + th[pa]) / 2 - hca / 2, sd_m)
        W = {"rating": 0.6, "season": 0.2, "form": 0.2}
        av = [k for k in W if k in models]
        factors = []
        if av:
            ws = sum(W[k] for k in av)
            eh = sum(W[k] * models[k]["hp"] for k in av) / ws
            ea = sum(W[k] * models[k]["ap"] for k in av) / ws
        else:
            mu = R["mu"] if R else 113.0
            eh, ea = mu + hca / 2, mu - hca / 2
            factors.append({"key": "nodata", "txt": "Nincs elég eredmény a csapatokról – ligaátlagból számol", "pts": 0})
        if hca:
            factors.append({"key": "hca", "txt": f"Hazai pálya ({self.teams[h]['abbr']})", "pts": hca})
        adj_h = adj_a = 0.0
        for side, tid in (("h", h), ("a", a)):
            ab = self.teams[tid]["abbr"]
            sign = 1 if side == "h" else -1
            rest = self.rest_days(tid, g)
            if rest == 1:
                pen = cfg["b2b_pen"]
                if side == "h":
                    adj_h -= pen / 2
                    adj_a += pen / 2
                else:
                    adj_a -= pen / 2
                    adj_h += pen / 2
                factors.append({"key": "b2b", "txt": f"{ab}: back-to-back (előző nap is játszott)", "pts": -sign * pen})
            imp, rows = self.inj_impact(tid, injuries)
            if imp > 0.05:
                if side == "h":
                    adj_h -= 0.6 * imp
                    adj_a += 0.4 * imp
                else:
                    adj_a -= 0.6 * imp
                    adj_h += 0.4 * imp
                top = ", ".join(f"{r['player']} ({r['status']})" for r in rows[:3])
                factors.append({"key": "inj", "txt": f"{ab} sérültjei: {top}", "pts": -sign * imp})
            nw = news.get(tid) or {}
            if nw.get("score") is not None and nw.get("n", 0) >= 2:
                x = cfg["news_max_pts"] * nw["score"]
                if abs(x) >= 0.05:
                    if side == "h":
                        adj_h += x / 2
                        adj_a -= x / 2
                    else:
                        adj_a += x / 2
                        adj_h -= x / 2
                    factors.append({"key": "news", "txt": f"{ab} hírhangulat ({nw['n']} cikk)", "pts": sign * x})
        stat = mk_pred(eh + adj_h, ea + adj_a, sd_m)
        models["stat"] = stat

        # fogadóirodák
        for b in books:
            if b.get("ml_h") and b.get("ml_a"):
                qh, qa = 1 / b["ml_h"], 1 / b["ml_a"]
                b["p_h"], b["vig"] = qh / (qh + qa), qh + qa - 1
        sp = [b["spread_h"] for b in books if b.get("spread_h") is not None]
        tt = [b["total"] for b in books if b.get("total")]
        ph = [b["p_h"] for b in books if b.get("p_h") is not None]
        mk_margin = -median(sp) if sp else (sd_m * ND.inv_cdf(min(max(float(np.mean(ph)), 0.02), 0.98)) if ph else None)
        mk_total = median(tt) if tt else None
        market = None
        if mk_margin is not None:
            mt = mk_total if mk_total is not None else stat["total"]
            models["market"] = mk_pred((mt + mk_margin) / 2, (mt - mk_margin) / 2, sd_m)
            if ph:
                models["market"]["p"] = float(np.mean(ph))
        if books:
            market = {"spread_h": median(sp) if sp else None, "total": mk_total,
                      "n_src": len({b.get("src") for b in books}),
                      "p_h": float(np.mean(ph)) if ph else None, "n": len(books)}
        mw = cfg["market_weight"]
        fm = mw * mk_margin + (1 - mw) * stat["margin"] if mk_margin is not None else stat["margin"]
        ft = mw * mk_total + (1 - mw) * stat["total"] if mk_total is not None else stat["total"]
        final = mk_pred((ft + fm) / 2, (ft - fm) / 2, sd_m)
        models["final"] = final

        # várható érték irodánként (a végső becslés valószínűségeivel)
        p = final["p"]
        p_over = lambda line: 1 - ND.cdf((line - final["total"]) / sd_t)  # noqa
        for b in books:
            if b.get("ml_h"):
                b["ev_ml_h"] = p * b["ml_h"] - 1
            if b.get("ml_a"):
                b["ev_ml_a"] = (1 - p) * b["ml_a"] - 1
            if b.get("spread_h") is not None:
                pc = ND.cdf((final["margin"] + b["spread_h"]) / sd_m)
                b["p_cover_h"] = pc
                if b.get("sp_h"):
                    b["ev_sp_h"] = pc * b["sp_h"] - 1
                if b.get("sp_a"):
                    b["ev_sp_a"] = (1 - pc) * b["sp_a"] - 1
            if b.get("total"):
                po = p_over(b["total"])
                b["p_over"] = po
                if b.get("over"):
                    b["ev_over"] = po * b["over"] - 1
                if b.get("under"):
                    b["ev_under"] = (1 - po) * b["under"] - 1
        # ugyanez a fogadóirodák konszenzusával (árrés nélkül): pozitív = jobb ár a piaci átlagnál
        mm = models.get("market")
        if mm and len(books) >= 2:
            pm, mt = mm["p"], (mk_total if mk_total is not None else None)
            for b in books:
                if b.get("ml_h"):
                    b["mev_ml_h"] = pm * b["ml_h"] - 1
                if b.get("ml_a"):
                    b["mev_ml_a"] = (1 - pm) * b["ml_a"] - 1
                if b.get("spread_h") is not None:
                    pc = ND.cdf((mm["margin"] + b["spread_h"]) / sd_m)
                    if b.get("sp_h"):
                        b["mev_sp_h"] = pc * b["sp_h"] - 1
                    if b.get("sp_a"):
                        b["mev_sp_a"] = (1 - pc) * b["sp_a"] - 1
                if b.get("total") and mt is not None:
                    po = 1 - ND.cdf((b["total"] - mt) / sd_t)
                    if b.get("over"):
                        b["mev_over"] = po * b["over"] - 1
                    if b.get("under"):
                        b["mev_under"] = (1 - po) * b["under"] - 1
        pw = max(p, 1 - p)
        conf ="Bizonytalan (előszezon)" if pre else ("Erős esély" if pw >= 0.72 else "Valószínű" if pw >= 0.6 else "Kiegyenlített")
        return {"models": models, "final": final, "factors": factors, "market": market, "books": books,
                "conf": conf, "sd_m": sd_m, "sd_t": sd_t}

    # ----- teljes újraszámolás -----
    def compute(self):
        if not self.clock.acquire(blocking=False):
            return
        try:
            self._compute()
        finally:
            self.clock.release()

    def _compute(self):
        with self.dlock:
            games = [dict(g) for g in self.games.values()]
            injuries = {k: list(v) for k, v in self.injuries.items()}
            news = {k: dict(v) for k, v in self.news.items()}
            odds_events = [e for r in self.odds_src.values() for e in r.get("events", [])] + list(self.odds_events)
            src_status = [{"name": n, **{k: v for k, v in r.items() if k != "events"}} for n, r in self.odds_src.items()]
        if not games:
            return
        sched = defaultdict(list)
        for g in games:
            sched[g["home"]].append(g["ts"])
            sched[g["away"]].append(g["ts"])
        self.sched = {k: sorted(v) for k, v in sched.items()}
        TS = self.team_stats(games)
        odx = defaultdict(list)
        for ev in odds_events:
            odx[(ev["home"], ev["away"])].append(ev)

        now = time.time()
        horizon = now + self.cfg["days_ahead"] * 86400
        window = [g for g in games if (now - 14 * 3600 <= g["ts"] <= horizon) or g["state"] == "in"]
        window.sort(key=lambda g: g["ts"])
        out_games, value, dirty = [], [], False
        espn_games = 0
        for g in window:
            if g["home"] not in self.teams or g["away"] not in self.teams:
                continue
            th, ta = self.teams[g["home"]], self.teams[g["away"]]
            raw = []
            cands = list(odx.get((th["nick"], ta["nick"]), []))
            for ev in odx.get((ta["nick"], th["nick"]), []):    # előrejelző piacoknál nem tudjuk, ki a hazai
                if ev.get("unordered"):
                    cands.append({**ev, "books": [{**b, "ml_h": b.get("ml_a"), "ml_a": b.get("ml_h")} for b in ev["books"]]})
            for ev in cands:
                if ev["ts"] and abs(ev["ts"] - g["ts"]) < 12 * 3600:
                    raw += [dict(b) for b in ev["books"]]
            if g.get("espn_odds"):
                raw.append(dict(g["espn_odds"]))
            books, seen_b = [], set()      # ugyanaz az iroda több forrásból: az első (közvetlen) marad
            for b in raw:
                k = book_key(b["book"])
                if k and k not in seen_b:
                    seen_b.add(k)
                    books.append(b)
            if g["state"] == "pre" and g["espn_odds"] is not None:
                espn_games += 1
            pr = self.predict(g, TS, injuries, news, books)
            f = pr["final"]
            saved = self.preds.get(g["id"])
            if g["state"] == "pre":
                rec = {"ts": g["ts"], "home": th["abbr"], "away": ta["abbr"], "stype": g["stype"],
                       "models": {k: {"margin": round(m["margin"], 2), "total": round(m["total"], 1),
                                      "p": round(m["p"], 4), "hp": round(m["hp"], 1), "ap": round(m["ap"], 1)}
                                  for k, m in pr["models"].items()}}
                if saved != rec:
                    self.preds[g["id"]] = rec
                    dirty = True
            hit = None
            if g["state"] == "post" and saved and g["hs"] is not None:
                sf = saved["models"].get("final")
                if sf:
                    hit = (sf["margin"] > 0) == (g["hs"] > g["as"])
            loc = datetime.fromtimestamp(g["ts"], TZ)
            ud = us_date(g["ts"])
            item = {
                "id": g["id"], "ts": g["ts"], "time": loc.strftime("%m.%d. %H:%M"), "day": ud.isoformat(),
                "day_label": hu_day(ud), "state": g["state"], "detail": g["detail"], "pre": g["stype"] == 1,
                "home": {k: th[k] for k in ("id", "abbr", "name", "short", "logo")},
                "away": {k: ta[k] for k in ("id", "abbr", "name", "short", "logo")},
                "hs": g["hs"], "as": g["as"], "models": pr["models"], "final": f, "conf": pr["conf"],
                "market": pr["market"], "books": pr["books"], "factors": pr["factors"], "hit": hit,
                "rest_h": self.rest_days(g["home"], g), "rest_a": self.rest_days(g["away"], g),
                "inj_h": self.inj_impact(g["home"], injuries)[1], "inj_a": self.inj_impact(g["away"], injuries)[1],
            }
            out_games.append(item)
            if g["state"] == "pre":
                match = f"{ta['abbr']} @ {th['abbr']}"
                for b in pr["books"]:
                    if b.get("exchange"):   # előrejelző piac: nem fogadóiroda, értékes-szorzó listába nem kerül
                        continue
                    cands = [("Győztes", th["abbr"], b.get("ml_h"), f["p"], b.get("ev_ml_h"), b.get("mev_ml_h")),
                             ("Győztes", ta["abbr"], b.get("ml_a"), 1 - f["p"], b.get("ev_ml_a"), b.get("mev_ml_a"))]
                    if b.get("spread_h") is not None:
                        s = b["spread_h"]
                        cands += [("Hendikep", f"{th['abbr']} {s:+g}", b.get("sp_h"), b.get("p_cover_h"), b.get("ev_sp_h"), b.get("mev_sp_h")),
                                  ("Hendikep", f"{ta['abbr']} {-s:+g}", b.get("sp_a"),
                                   1 - b["p_cover_h"] if b.get("p_cover_h") is not None else None, b.get("ev_sp_a"), b.get("mev_sp_a"))]
                    if b.get("total"):
                        cands += [("Összpont", f"Over {b['total']:g}", b.get("over"), b.get("p_over"), b.get("ev_over"), b.get("mev_over")),
                                  ("Összpont", f"Under {b['total']:g}", b.get("under"),
                                   1 - b["p_over"] if b.get("p_over") is not None else None, b.get("ev_under"), b.get("mev_under"))]
                    for mkt, pick, price, pp, ev, mev in cands:
                        # érték csak ott, ahol a modell szerint is megéri, ÉS az ár jobb a többi iroda konszenzusánál
                        if (ev is not None and mev is not None and price and 1.25 <= price <= 6
                                and ev >= self.cfg["value_edge"] and mev > 0):
                            value.append({"gid": g["id"], "match": match, "time": item["time"], "book": b["book"],
                                          "market": mkt, "pick": pick, "price": price, "p": pp, "ev": ev, "mev": mev,
                                          "pre": item["pre"]})
            if g["state"] == "post" and saved and "actual" not in saved and g["hs"] is not None:
                saved["actual"] = {"hs": g["hs"], "as": g["as"]}
                dirty = True
        # befejezett, már kikerült meccsek eredményének rögzítése
        by_id = {g["id"]: g for g in games}
        for gid, rec in self.preds.items():
            g = by_id.get(gid)
            if g and g["completed"] and "actual" not in rec and g["hs"] is not None:
                rec["actual"] = {"hs": g["hs"], "as": g["as"]}
                dirty = True
        if dirty:
            if len(self.preds) > 3000:
                for k in sorted(self.preds, key=lambda k: self.preds[k]["ts"])[:-3000]:
                    del self.preds[k]
            try:
                self.pred_path.write_text(json.dumps(clean(self.preds), ensure_ascii=False), encoding="utf-8")
            except Exception as e:
                self.err(f"Predikciók mentése: {e}")
        value.sort(key=lambda v: -v["ev"])

        # csapattáblázat
        R = self.ratings or {"o": {}, "d": {}}
        teams = []
        for tid, t in self.teams.items():
            if not t["nba"]:
                continue
            s = TS.get(tid, {})
            o, d = R["o"].get(tid), R["d"].get(tid)
            imp, rows = self.inj_impact(tid, injuries)
            nw = news.get(tid) or {}
            nxt = next((g for g in out_games if g["state"] == "pre" and tid in (g["home"]["id"], g["away"]["id"])), None)
            teams.append({"id": tid, "abbr": t["abbr"], "name": t["name"], "logo": t["logo"], **s,
                          "o": o, "d": d, "net": (o - d) if o is not None else None,
                          "inj_pts": imp, "inj_n": len(rows), "news_s": nw.get("score"), "news_n": nw.get("n", 0),
                          "next": (f"{nxt['away']['abbr']} @ {nxt['home']['abbr']} · {nxt['time']}" if nxt else None)})
        ranked = sorted([t for t in teams if t["net"] is not None], key=lambda t: -t["net"])
        for i, t in enumerate(ranked, 1):
            t["rank"] = i

        inj_list = []
        for tid, lst in injuries.items():
            if tid in self.teams:
                for r in self.inj_impact(tid, injuries)[1]:
                    inj_list.append({**r, "abbr": self.teams[tid]["abbr"], "tid": tid})
        inj_list.sort(key=lambda r: -r["impact"])

        state = {
            "status": {**self.status, "phase": "Fut", "errors": list(self.status["errors"]), "computed": now_str(),
                       "n_games": self.ratings["n_games"] if self.ratings else 0},
            "config": {k: self.cfg[k] for k in ("days_ahead", "market_weight", "value_edge", "b2b_pen", "margin_sd")},
            "hca": self.ratings["hca"] if self.ratings else self.cfg["hca"],
            "mu": self.ratings["mu"] if self.ratings else None, "has_odds_key": bool(self.cfg["odds_api_key"]),
            "sources": [{"name": "ESPN", "ok": self.status.get("last_sched"), "err": None, "games": espn_games,
                         "books": 1 if espn_games else 0}] + src_status
                       + ([{"name": "The Odds API", "ok": self.status.get("last_odds"), "err": None,
                            "games": len(self.odds_events),
                            "books": len({b["book"] for e in self.odds_events for b in e["books"]})}]
                          if self.cfg["odds_api_key"] else []),
            "min_sources": self.cfg["min_sources"],
            "feed": [{**{k: it.get(k) for k in ("title", "url", "src", "s", "tags")},
                      "teams": [self.teams[t]["abbr"] for t in it.get("teams", []) if t in self.teams],
                      "tids": it.get("teams", []),
                      "time": datetime.fromtimestamp(it["ts"], TZ).strftime("%m.%d. %H:%M") if it.get("ts") else ""}
                     for it in self.feed_items[:250]],
            "feed_status": [{"name": n, **self.feed_status.get(n, {})} for n, *_ in NEWS_PORTALS],
            "games": out_games, "value": value[:40], "teams": teams, "injuries": inj_list,
            "acc": self.accuracy(), "model_names": MODEL_NAMES,
        }
        state = clean(state)
        with self.slock:
            self.state = state

    def accuracy(self):
        acc = {k: {"n": 0, "hit": 0, "mae_m": 0.0, "mae_t": 0.0, "brier": 0.0} for k in MODEL_NAMES}
        recent = []
        for gid, rec in self.preds.items():
            act = rec.get("actual")
            if not act or rec.get("stype") == 1:
                continue
            am, at = act["hs"] - act["as"], act["hs"] + act["as"]
            for k, m in rec["models"].items():
                if k not in acc:
                    continue
                a = acc[k]
                a["n"] += 1
                a["hit"] += int((m["margin"] > 0) == (am > 0))
                a["mae_m"] += abs(m["margin"] - am)
                a["mae_t"] += abs(m["total"] - at)
                a["brier"] += (m["p"] - (1.0 if am > 0 else 0.0)) ** 2
            f = rec["models"].get("final")
            if f:
                recent.append({"ts": rec["ts"], "match": f"{rec['away']} @ {rec['home']}",
                               "pred": f"{f.get('ap', 0):.0f} – {f.get('hp', 0):.0f}",
                               "actual": f"{act['as']:.0f} – {act['hs']:.0f}",
                               "ok": (f["margin"] > 0) == (am > 0), "err_t": f["total"] - at,
                               "date": datetime.fromtimestamp(rec["ts"], TZ).strftime("%m.%d. %H:%M")})
        rows = []
        for k, a in acc.items():
            if a["n"]:
                rows.append({"key": k, "name": MODEL_NAMES[k], "n": a["n"], "hit": a["hit"] / a["n"],
                             "mae_m": a["mae_m"] / a["n"], "mae_t": a["mae_t"] / a["n"], "brier": a["brier"] / a["n"]})
        recent.sort(key=lambda r: -r["ts"])
        return {"models": rows, "recent": recent[:40]}

    def news_for(self, tid):
        nw = self.news.get(tid, {})
        items = sorted(nw.get("items", []), key=lambda x: -(x.get("ts") or 0))
        t = self.teams.get(tid, {})
        return {"id": tid, "name": t.get("name"), "abbr": t.get("abbr"), "score": nw.get("score"),
                "items": [{**it, "time": datetime.fromtimestamp(it["ts"], TZ).strftime("%m.%d. %H:%M")
                           if it.get("ts") else ""} for it in items]}

    def state_json(self):
        with self.slock:
            if "games" not in self.state:
                st = {**self.status, "errors": list(self.status["errors"])}
                return json.dumps(clean({"status": st}), ensure_ascii=False)
            return json.dumps(self.state, ensure_ascii=False)

    # ----- egyszeri futás (GitHub Actions) -----
    def load_cache(self, data_dir):
        try:
            c = json.loads((Path(data_dir) / "games.json").read_text(encoding="utf-8"))
        except Exception:
            return
        self.games = {g["id"]: g for g in c.get("games", [])}
        self.teams.update({t["id"]: t for t in c.get("teams", [])})
        self.odds_events = c.get("odds_events", [])
        self._odds_ts = c.get("odds_ts", 0)
        self.status["last_odds"] = c.get("last_odds")
        self.status["odds_left"] = c.get("odds_left")

    def save_cache(self, data_dir):
        d = Path(data_dir)
        d.mkdir(parents=True, exist_ok=True)
        cut = time.time() - 800 * 86400
        with self.dlock:
            c = {"saved": now_str(), "games": [g for g in self.games.values() if g["ts"] > cut],
                 "teams": list(self.teams.values()), "odds_events": self.odds_events,
                 "odds_ts": getattr(self, "_odds_ts", 0), "last_odds": self.status.get("last_odds"),
                 "odds_left": self.status.get("odds_left")}
        (d / "games.json").write_text(json.dumps(clean(c), ensure_ascii=False), encoding="utf-8")

    def run_once(self):
        steps = [
            ("Csapatok", lambda: self.teams.update(self.src.teams())),
            ("Menetrend és eredmények", self.load_history),
            ("Erősségi modell", self.fit_ratings),
            ("Sérültlista", self.refresh_injuries),
            ("Játékosstatisztika", self.refresh_stats),
            ("The Odds API", self.refresh_odds),
            ("Fogadóirodai források", self.free_odds_once),
            ("Csapathírek", lambda: self.team_news_once(pause=0.2)),
            ("NBA-portálok", self.feeds_once),
        ]
        for name, fn in steps:
            t0 = time.time()
            try:
                fn()
                if name == "Menetrend és eredmények":
                    self.status["last_sched"] = now_str()
                if name == "Játékosstatisztika":
                    self.build_matchers()
                print(f"  ✓ {name} ({time.time() - t0:.0f} mp)", flush=True)
            except Exception as e:
                self.err(f"{name}: {e}")
                print(f"  ✗ {name}: {e}", flush=True)
        while not self.clock.acquire(timeout=1):
            pass
        try:
            self._compute()
        finally:
            self.clock.release()

    # ----- fő ciklus -----
    def run(self):
        try:
            self.status["phase"] = "Csapatok betöltése…"
            try:
                self.teams = self.src.teams()
            except Exception as e:
                self.err(f"Csapatlista: {e}")
            self.load_history()
            self.status["last_sched"] = now_str()
            self.status["phase"] = "Erősségi modell illesztése…"
            self.fit_ratings()
            self.status["phase"] = "Sérültlista…"
            self.refresh_injuries()
            self.build_matchers()
            for fn in (self.stats_loop, self.odds_loop, self.free_odds_loop, self.feeds_loop, self.news_loop,
                       self.sched_loop, self.injury_loop):
                threading.Thread(target=fn, daemon=True).start()
            self.compute()
        except Exception as e:
            self.status["phase"] = f"Hiba indításkor: {e}"
            self.err(traceback.format_exc(limit=2))
            return
        while True:
            time.sleep(60)
            try:
                self.compute()
            except Exception as e:
                self.err(f"Számolási hiba: {e}")


# ---------------------------------------------------------------------------
# Webszerver
# ---------------------------------------------------------------------------
def make_handler(engine: Engine):
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def _send(self, code, body, ctype):
            b = body.encode("utf-8") if isinstance(body, str) else body
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(b)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(b)

        def do_GET(self):
            u = urllib.parse.urlparse(self.path)
            if u.path in ("/", "/index.html"):
                self._send(200, HTML, "text/html; charset=utf-8")
            elif u.path == "/api/state":
                self._send(200, engine.state_json(), "application/json; charset=utf-8")
            elif u.path == "/api/news":
                t = urllib.parse.parse_qs(u.query).get("team", [""])[0]
                self._send(200, json.dumps(clean(engine.news_for(t)), ensure_ascii=False),
                           "application/json; charset=utf-8")
            else:
                self._send(404, "Nem található", "text/plain; charset=utf-8")

    return Handler


HTML = r"""<!doctype html>
<html lang="hu">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>NBA Meccsradar</title>
<style>
:root{--bg:#f4f5f7;--card:#fff;--ink:#14171c;--mute:#667085;--line:#e4e7ec;--acc:#c2410c;--acc2:#fff1e8;
--pos:#14803c;--neg:#c0312b;--warn:#b25e09;--home:#c2410c;--away:#1d4ed8}
@media (prefers-color-scheme:dark){:root{--bg:#0e1013;--card:#171a1f;--ink:#e7e9ee;--mute:#98a1b2;--line:#262b33;
--acc:#fb923c;--acc2:#2a1a10;--pos:#4ade80;--neg:#f87171;--warn:#fbbf24;--home:#fb923c;--away:#60a5fa}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);font:14px/1.45 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif}
header{position:sticky;top:0;z-index:5;background:var(--card);border-bottom:1px solid var(--line);padding:10px 16px;
display:flex;flex-wrap:wrap;gap:10px 18px;align-items:center}
header h1{font-size:17px;margin:0;font-weight:700}
.chip{background:var(--bg);border:1px solid var(--line);border-radius:999px;padding:3px 10px;font-size:12.5px;color:var(--mute)}
.chip b{color:var(--ink);font-weight:600}
.dot{display:inline-block;width:8px;height:8px;border-radius:50%;background:var(--acc);margin-right:6px;animation:p 2s infinite}
@keyframes p{50%{opacity:.3}}
nav{display:flex;gap:4px;margin-left:auto;flex-wrap:wrap}
nav a{color:var(--mute);text-decoration:none;padding:4px 10px;border-radius:6px;font-size:13px}
nav a:hover{background:var(--bg);color:var(--ink)}
main{max-width:1320px;margin:0 auto;padding:16px}
section{margin-bottom:28px}
h2{font-size:15px;margin:0 0 10px;font-weight:700}
h3{font-size:13.5px;margin:14px 0 6px}
.sub{color:var(--mute);font-size:12.5px;margin:-6px 0 12px}
.card{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:12px 14px}
.grid{display:grid;gap:12px}
.g3{grid-template-columns:repeat(auto-fill,minmax(300px,1fr))}
.g2{grid-template-columns:1fr 1fr}
@media(max-width:860px){.g2{grid-template-columns:1fr}}
.pos{color:var(--pos)}.neg{color:var(--neg)}.mute{color:var(--mute)}
.badge{display:inline-block;padding:2px 8px;border-radius:999px;font-size:11.5px;font-weight:650;white-space:nowrap;background:var(--line);color:var(--mute)}
.b-strong{background:var(--pos);color:#fff}.b-mid{background:#3f9b6b;color:#fff}.b-even{background:#8b8f98;color:#fff}.b-pre{background:var(--warn);color:#fff}
.b-live{background:var(--neg);color:#fff}
@media (prefers-color-scheme:dark){.b-strong,.b-mid,.b-even,.b-pre,.b-live{color:#0e1013}}
.game{cursor:pointer}.game:hover{border-color:var(--acc)}
.gh{display:flex;justify-content:space-between;gap:6px;align-items:center;font-size:12.5px;margin-bottom:6px}
.tm{display:flex;align-items:center;gap:8px;padding:3px 0}
.tm img{width:24px;height:24px}
.tm .pts{margin-left:auto;font-size:20px;font-weight:750;letter-spacing:-.02em;color:var(--mute)}
.tm.win .pts{color:var(--ink)}
.tm .role{font-size:11px;color:var(--mute)}
.pbar{display:flex;height:8px;border-radius:4px;overflow:hidden;margin:8px 0 3px;background:var(--line)}
.pbar .pa{background:var(--away)}.pbar .ph{background:var(--home)}
.pl{display:flex;justify-content:space-between;font-size:12px;color:var(--mute)}
.pl b{color:var(--ink)}
.mk{font-size:12px;color:var(--mute);margin-top:6px}
.chips{display:flex;flex-wrap:wrap;gap:4px;margin-top:6px}
.fc{font-size:11.5px;border-radius:5px;padding:1px 6px;background:var(--bg);border:1px solid var(--line)}
.res{margin-top:8px;padding-top:6px;border-top:1px dashed var(--line);font-size:13px}
.tools{display:flex;flex-wrap:wrap;gap:8px;margin-bottom:10px;align-items:center}
input,select,button{font:inherit;color:var(--ink);background:var(--card);border:1px solid var(--line);border-radius:7px;padding:6px 10px}
button{cursor:pointer}button:hover{border-color:var(--acc)}
.tabs button.on{background:var(--acc);border-color:var(--acc);color:#fff}
.tw{overflow-x:auto;border:1px solid var(--line);border-radius:10px;background:var(--card)}
table{border-collapse:collapse;width:100%;font-size:13px}
th,td{padding:7px 9px;border-bottom:1px solid var(--line);text-align:right;white-space:nowrap}
th{position:sticky;top:0;background:var(--card);font-weight:600;color:var(--mute);font-size:12px}
th[data-k]{cursor:pointer;user-select:none}
th.l,td.l{text-align:left}
tbody tr.ck{cursor:pointer}tbody tr.ck:hover{background:var(--acc2)}
tr:last-child td{border-bottom:none}
td.wrap{white-space:normal;min-width:200px}
td img{width:20px;height:20px;vertical-align:middle;margin-right:6px}
.ev{display:block;font-size:11px}
.kpi{display:grid;grid-template-columns:repeat(auto-fill,minmax(130px,1fr));gap:10px;margin-bottom:12px}
.kpi div{background:var(--bg);border-radius:8px;padding:8px 10px}
.kpi small{display:block;color:var(--mute);font-size:11.5px}
.kpi b{font-size:16px}
dialog{border:1px solid var(--line);border-radius:12px;background:var(--card);color:var(--ink);width:min(1000px,96vw);padding:0}
dialog::backdrop{background:rgba(0,0,0,.45)}
.dh{display:flex;justify-content:space-between;align-items:start;padding:14px 16px;border-bottom:1px solid var(--line)}
.db{padding:14px 16px;max-height:76vh;overflow:auto}
.news a{color:var(--ink)}.news li{margin:5px 0}
.tag{font-size:10.5px;border:1px solid var(--line);border-radius:4px;padding:0 4px;margin-left:4px;color:var(--mute)}
.note{font-size:12px;color:var(--mute)}
footer{max-width:1320px;margin:0 auto;padding:6px 16px 30px;font-size:12px;color:var(--mute)}
.err{color:var(--warn);font-size:12px}
.load{padding:60px;text-align:center;color:var(--mute)}
.warn{background:var(--acc2);border:1px solid var(--line);border-radius:8px;padding:8px 12px;font-size:12.5px;margin-bottom:12px}
</style>
</head>
<body>
<header>
  <h1>NBA Meccsradar</h1>
  <span class="chip" id="st"><span class="dot"></span>betöltés…</span>
  <span class="chip">Hazai előny: <b id="hca">–</b></span>
  <nav><a href="#games">Meccsek</a><a href="#value">Értékes szorzók</a><a href="#teams">Csapatok</a><a href="#inj">Sérültek</a><a href="#feed">Hírek</a><a href="#acc">Pontosság</a></nav>
</header>
<main id="app"><div class="load">Adatok letöltése… az első indulás 1–2 percig tarthat (két szezon eredményei).</div></main>
<footer>
Ez szabályalapú elemzés, nem fogadási tanács. A sportfogadás pénzvesztéssel jár, a fogadóirodák vonalai hosszú távon pontosabbak
az egyszerű statisztikai modelleknél. Csak 18 év felett, és csak olyan összeggel, amelynek elvesztése nem okoz gondot.
Adatforrás: ESPN (menetrend, eredmények, sérültlista); hírek: 22 amerikai NBA-portál (ESPN, The Athletic, CBS, Yahoo, NBA.com, Bleacher Report, Fox, NBC, SI, USA Today, The Ringer, Sporting News, SB Nation, RotoWire, Hoops Rumors, HoopsHype, RealGM, ClutchPoints, NY Post stb.) és Google News; szorzók: ESPN, Pinnacle, DraftKings, FanDuel, Bovada, Unibet, Paf, Action Network, SportsbookReview (bet365, BetMGM, Caesars, BetRivers, Fanatics…), Polymarket és Kalshi előrejelző piac, opcionálisan The Odds API. A szorzóforrások nem hivatalos nyilvános végpontok, bármikor megváltozhatnak.
<div id="errs" class="err"></div>
</footer>
<dialog id="dlg"><div class="dh"><div id="dt"></div><button onclick="dlg.close()">Bezárás</button></div><div class="db" id="dbody"></div></dialog>
<script>
let S=null,built=false,day='',tsK='net',tsD=-1,onlyVal=false;
const $=s=>document.querySelector(s);
const esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const nf=(x,d=0)=>x==null?'–':Number(x).toLocaleString('hu-HU',{minimumFractionDigits:d,maximumFractionDigits:d});
const sg=(x,d=1)=>x==null?'–':(x>0?'+':'')+nf(x,d);
const p0=x=>x==null?'–':Math.round(x*100)+'%';
const cls=x=>x==null?'':x>0?'pos':x<0?'neg':'';
const logo=t=>t.logo?`<img src="${esc(t.logo)}" alt="" loading="lazy">`:'';
const confB=c=>{const k={'Erős esély':'b-strong','Valószínű':'b-mid','Kiegyenlített':'b-even'}[c]||'b-pre';return `<span class="badge ${k}">${esc(c)}</span>`;};
const evc=(price,ev)=>price==null?'–':`${nf(price,2)}${ev==null?'':`<span class="ev ${ev>=S.config.value_edge?'pos':ev<0?'mute':''}">EV ${sg(ev*100,1)}%</span>`}`;

async function load(){
  try{S=await (await fetch(window.STATIC?'state.json?t='+Date.now():'/api/state',{cache:'no-store'})).json();}
  catch(e){$('#st').textContent=window.STATIC?'Az adatfájl (state.json) még nem készült el':'Nincs kapcsolat a Python szerverrel';return;}
  try{render();}catch(e){console.error(e);}
}
function render(){
  const st=S.status||{};
  $('#st').innerHTML=`<span class="dot"></span>${window.STATIC?`Utolsó frissítés: <b>${esc(st.computed||'–')}</b> · `:''}${esc(st.mode||'')} · menetrend: <b>${esc(st.last_sched||'–')}</b> · sérültek: ${esc(st.last_inj||'–')} · hírek ${st.news_done||0}/${st.n||0}${st.last_odds?` · szorzók: ${esc(st.last_odds)}${st.odds_left?` (${esc(st.odds_left)} kredit maradt)`:''}`:''}`;
  $('#errs').innerHTML=(st.errors||[]).map(esc).join('<br>');
  if(!S.games){$('#app').innerHTML=`<div class="load">${esc(st.phase||'Betöltés…')}</div>`;return;}
  $('#hca').textContent=nf(S.hca,1)+' pont';
  if(!built)build();
  renderGames();renderValue();renderTeams();renderInj();renderFeed();renderAcc();
}
function build(){
  built=true;
  $('#app').innerHTML=`
  <section id="games"><h2>Következő ${S.config.days_ahead} nap meccsei</h2>
   <div class="sub">Az időpontok magyar idő szerint, a napok amerikai játéknap szerint csoportosítva. A becsült pontszám a végső becslés: statisztika (sérülés, pihenő, hírek beszámítva) és a fogadóirodák vonala ${Math.round(S.config.market_weight*100)}% súllyal. Kattints egy meccsre a részletekért.</div>
   <div class="tools" id="srcs"></div><div id="gwarn"></div><div class="tools tabs" id="days"></div><div class="grid g3" id="glist"></div></section>
  <section id="value"><h2>Értékes szorzók</h2>
   <div class="sub">Ahol a végső becslés szerinti esély és az iroda szorzója alapján a várható érték legalább ${Math.round(S.config.value_edge*100)}%. Csak az kerül ide, aminek az ára a többi iroda árrés nélküli átlagánál is jobb (Előny a piachoz &gt; 0), tehát legalább két iroda adata kell hozzá. A modell is tévedhet, ez nem biztos nyereség.</div>
   <div class="tw"><table><thead><tr><th class="l">Meccs</th><th class="l">Időpont</th><th class="l">Iroda</th><th class="l">Piac</th><th class="l">Tipp</th><th>Szorzó</th><th>Becsült esély</th><th>Várható érték</th><th>Előny a piachoz</th></tr></thead><tbody id="vtb"></tbody></table></div></section>
  <section id="teams"><h2>Csapatok</h2>
   <div class="sub">Támadás / védekezés: ellenfél-erősséggel korrigált pont a ligaátlaghoz képest (a frissebb meccsek többet számítanak; védekezésnél a negatív a jó). Nettó = támadás − védekezés.</div>
   <div class="tw"><table><thead><tr><th data-k="rank">#</th><th class="l" data-k="name">Csapat</th><th data-k="w">Mérleg</th><th data-k="pf">Dobott</th><th data-k="pa">Kapott</th>
   <th data-k="o">Támadás</th><th data-k="d">Védekezés</th><th data-k="net">Nettó</th><th data-k="l10_w">Utolsó 10</th><th data-k="streak">Sorozat</th>
   <th data-k="inj_pts">Sérülés-hatás</th><th data-k="news_s">Hírek</th><th class="l">Következő meccs</th></tr></thead><tbody id="ttb"></tbody></table></div></section>
  <section id="inj"><h2>Sérültlista</h2>
   <div class="sub">Hatás: hány ponttal gyengíti a csapatot a becslés szerint (a játékos pont- és percátlagából, a státusz valószínűségével szorozva). A 30 napnál régebbi hiányok csak 30%-kal számítanak, mert azokat az eredmények már tartalmazzák.</div>
   <div class="tw"><table><thead><tr><th class="l">Csapat</th><th class="l">Játékos</th><th class="l">Státusz</th><th>Pont/meccs</th><th>Perc</th><th>Hatás</th><th class="l">Mióta</th><th class="l">Megjegyzés</th></tr></thead><tbody id="itb"></tbody></table></div></section>
  <section id="feed"><h2>Hírek és pletykák – amerikai NBA-portálok</h2>
   <div class="sub">${S.feed_status.length} portál, 10 percenként frissül. Ahol nincs (vagy nem érhető el) RSS, ott a Google News keresi a portál cikkeit. A csapathoz rendelés a csapatnév, a város, a becenév és az ismert játékosok neve alapján történik; a hírek hangulata beszámít a csapat becslésébe.</div>
   <div class="tools" id="fsrc"></div>
   <div class="tools"><input id="fq" placeholder="Keresés (játékos, csapat…)" oninput="renderFeed()">
    <select id="fp" onchange="renderFeed()"><option value="">Minden portál</option></select>
    <select id="ft" onchange="renderFeed()"><option value="">Minden csapat</option></select>
    <select id="fg" onchange="renderFeed()"><option value="">Minden címke</option><option>Sérülés</option><option>Visszatér</option><option>Pletyka/átigazolás</option><option>Eltiltás</option><option>Pihentetés</option><option>Edző/vezetés</option></select></div>
   <div class="card"><ul class="news" id="flist" style="margin:0;padding-left:18px"></ul></div></section>
  <section id="acc"><h2>Pontosság – mennyire jöttek be a becslések</h2>
   <div class="sub">Minden meccs utolsó kezdés előtti becslése elmentődik, a végeredmény után itt értékelődik (előszezoni meccsek nélkül). Brier: a valószínűségek pontossága, kisebb a jobb (0,25 = pénzfeldobás).</div>
   <div class="grid g2"><div class="tw"><table><thead><tr><th class="l">Modell</th><th>Meccs</th><th>Győztes eltalálva</th><th>Átl. hiba (különbség)</th><th>Átl. hiba (összpont)</th><th>Brier</th></tr></thead><tbody id="atb"></tbody></table></div>
   <div class="tw"><table><thead><tr><th class="l">Meccs</th><th>Időpont</th><th>Becslés</th><th>Eredmény</th><th>Győztes</th><th>Összpont hiba</th></tr></thead><tbody id="rtb"></tbody></table></div></div></section>`;
  document.querySelectorAll('th[data-k]').forEach(th=>th.onclick=()=>{const k=th.dataset.k;tsD=(tsK===k)?-tsD:(k==='name'||k==='rank'||k==='d'||k==='pa'||k==='inj_pts'?1:-1);tsK=k;renderTeams();});
}

function renderGames(){
  const G=S.games;
  const days=[...new Map(G.map(g=>[g.day,g.day_label])).entries()];
  if(day&&!days.some(d=>d[0]===day))day='';
  $('#days').innerHTML=`<button class="${day?'':'on'}" onclick="day='';renderGames()">Mind (${G.length})</button>`+
    days.map(([d,l])=>`<button class="${day===d?'on':''}" onclick="day='${d}';renderGames()">${esc(l)} · ${G.filter(g=>g.day===d).length}</button>`).join('');
  const pre=G.some(g=>g.pre);
  $('#gwarn').innerHTML=(pre?`<div class="warn">Előszezoni meccsek: a csapatok gyakran tartalékokkal, rövid percekkel játszanak, ezért ezeknél a becslés sokkal bizonytalanabb. Az erősségi modell ilyenkor az előző szezon eredményeire épül.</div>`:'')+
    (()=>{const src=S.sources||[],ok=src.filter(x=>x.games>0),bad=src.filter(x=>!x.games);
      return ok.length<S.min_sources?`<div class="warn">Most ${ok.length} forrásból jön szorzó (cél: legalább ${S.min_sources}).${bad.length?' Nem ad adatot: '+bad.map(x=>esc(x.name)+(x.err?' – '+esc(x.err.slice(20)):x.ok?'':' (még tölt)')).join('; ')+'.':''}${S.has_odds_key?'':' Tartaléknak megadható egy ingyenes the-odds-api.com kulcs: <code>--odds-key KULCS</code>'}</div>`:'';})();
  $('#srcs').innerHTML='<span class="mute" style="font-size:12.5px">Szorzóforrások:</span>'+(S.sources||[]).map(x=>`<span class="chip" title="${esc(x.err||('frissítve: '+(x.ok||'–')))}"><b class="${x.games>0?'pos':x.err?'neg':'mute'}">●</b> ${esc(x.name)} <span class="mute">${x.games||0} meccs${x.books>1?' · '+x.books+' iroda':''}</span></span>`).join('');
  const list=G.filter(g=>!day||g.day===day);
  $('#glist').innerHTML=list.length?list.map(gcard).join(''):'<div class="mute">Erre az időszakra nincs meccs a menetrendben.</div>';
}
function gcard(g){
  const f=g.final,ph=f.p,live=g.state==='in',done=g.state==='post';
  const top=live?'<span class="badge b-live">ÉLŐ</span>':done?`<span class="badge">vége</span>`:confB(g.conf);
  const facs=g.factors.filter(x=>x.key!=='hca').map(x=>`<span class="fc ${cls(x.pts)}" title="${esc(x.txt)}">${esc(x.key==='b2b'?'B2B':x.key==='inj'?'sérült':x.key==='news'?'hírek':'adat')} ${x.key==='nodata'?'':sg(x.pts,1)}</span>`).join('');
  const m=g.market;
  const res=(live||done)?`<div class="res"><b>${esc(g.away.abbr)} ${nf(g.as)} – ${nf(g.hs)} ${esc(g.home.abbr)}</b> <span class="mute">${esc(g.detail)}</span>${g.hit==null?'':g.hit?' <span class="pos">✓ eltalálva</span>':' <span class="neg">✗ nem jött be</span>'}</div>`:'';
  return `<div class="card game" onclick="openG('${g.id}')">
   <div class="gh"><span class="mute">${esc(g.time)}${g.pre?' · előszezon':''}</span>${top}</div>
   <div class="tm ${f.margin<0?'win':''}">${logo(g.away)}<div><b>${esc(g.away.name)}</b><div class="role">vendég${g.rest_a===1?' · B2B':''}</div></div><span class="pts">${nf(f.ap)}</span></div>
   <div class="tm ${f.margin>0?'win':''}">${logo(g.home)}<div><b>${esc(g.home.name)}</b><div class="role">hazai${g.rest_h===1?' · B2B':''}</div></div><span class="pts">${nf(f.hp)}</span></div>
   <div class="pbar"><i class="pa" style="width:${(1-ph)*100}%"></i><i class="ph" style="width:${ph*100}%"></i></div>
   <div class="pl"><span>${esc(g.away.abbr)} ${p0(1-ph)}</span><span>Összpont: <b>${nf(f.total,1)}</b></span><span>${esc(g.home.abbr)} ${p0(ph)}</span></div>
   <div class="mk">${m?`Irodák: ${m.n} (${m.n_src} forrás) · ${m.spread_h!=null?esc(g.home.abbr)+' '+sg(m.spread_h,1):''}${m.total?' · O/U '+nf(m.total,1):''}${m.p_h!=null?' · hazai esély '+p0(m.p_h):''}`:'Nincs fogadóirodai vonal'}</div>
   ${facs?`<div class="chips">${facs}</div>`:''}${res}</div>`;
}

function renderValue(){
  const V=S.value;
  $('#vtb').innerHTML=V.length?V.map(v=>`<tr class="ck" onclick="openG('${v.gid}')"><td class="l"><b>${esc(v.match)}</b>${v.pre?' <span class="mute">(előszezon)</span>':''}</td><td class="l mute">${esc(v.time)}</td>
   <td class="l">${esc(v.book)}</td><td class="l">${esc(v.market)}</td><td class="l"><b>${esc(v.pick)}</b></td><td>${nf(v.price,2)}</td><td>${p0(v.p)}</td><td class="pos">${sg(v.ev*100,1)}%</td><td>${sg(v.mev*100,1)}%</td></tr>`).join('')
   :'<tr><td class="l mute" colspan="9">Most nincs a küszöb feletti szorzó (vagy nincs fogadóirodai adat).</td></tr>';
}

function renderTeams(){
  const T=S.teams.slice();
  T.sort((a,b)=>{let x=a[tsK],y=b[tsK];if(x==null)return 1;if(y==null)return -1;return (typeof x==='string'?x.localeCompare(y,'hu'):x-y)*tsD;});
  $('#ttb').innerHTML=T.map(t=>`<tr class="ck" onclick="openT('${t.id}')"><td>${t.rank??'–'}</td><td class="l">${logo(t)}<b>${esc(t.name)}</b></td>
   <td>${t.w??0}–${t.l??0}<div class="note">${esc(t.season_label||'')}</div></td><td>${nf(t.pf,1)}</td><td>${nf(t.pa,1)}</td>
   <td class="${cls(t.o)}">${sg(t.o,1)}</td><td class="${cls(t.d==null?null:-t.d)}">${sg(t.d,1)}</td><td class="${cls(t.net)}"><b>${sg(t.net,1)}</b></td>
   <td>${t.l10_w??0}–${t.l10_l??0}<div class="note">${t.l10_pf!=null?sg(t.l10_pf-t.l10_pa,1)+' pont':''}</div></td>
   <td class="${cls(t.streak)}">${t.streak?(t.streak>0?t.streak+' győzelem':(-t.streak)+' vereség'):'–'}</td>
   <td class="${t.inj_pts>0.5?'neg':''}">${t.inj_n?'−'+nf(t.inj_pts,1)+` <span class="mute">(${t.inj_n})</span>`:'–'}</td>
   <td class="${cls(t.news_s)}">${t.news_n>=2?sg(t.news_s,2)+` <span class="mute">(${t.news_n})</span>`:'–'}</td><td class="l mute">${esc(t.next||'–')}</td></tr>`).join('');
}

function renderFeed(){
  const F=S.feed||[],fs=S.feed_status||[];
  $('#fsrc').innerHTML=fs.map(x=>`<span class="chip" title="${esc(x.err||(x.ok?'frissítve: '+x.ok:'még tölt'))}"><b class="${x.n>0?'pos':x.err?'neg':'mute'}">●</b> ${esc(x.name)} <span class="mute">${x.n||0}${x.via?' · '+esc(x.via):''}</span></span>`).join('');
  const fp=$('#fp'),ft=$('#ft');
  if(fp.options.length<=1)fs.forEach(x=>fp.add(new Option(x.name,x.name)));
  if(ft.options.length<=1)S.teams.slice().sort((a,b)=>a.name.localeCompare(b.name)).forEach(t=>ft.add(new Option(t.name,t.id)));
  const q=$('#fq').value.trim().toLowerCase(),P=fp.value,T=ft.value,G=$('#fg').value;
  const L=F.filter(i=>(!q||i.title.toLowerCase().includes(q))&&(!P||i.src===P)&&(!T||(i.tids||[]).includes(T))&&(!G||(i.tags||[]).includes(G))).slice(0,120);
  $('#flist').innerHTML=L.length?L.map(i=>`<li><span class="${cls(i.s)}">${i.s>0?'▲':i.s<0?'▼':'•'}</span>
   ${i.url?`<a href="${esc(i.url)}" target="_blank" rel="noopener">${esc(i.title)}</a>`:esc(i.title)}
   ${(i.teams||[]).map(t=>`<span class="tag" style="font-weight:700">${esc(t)}</span>`).join('')}${(i.tags||[]).map(t=>`<span class="tag">${esc(t)}</span>`).join('')}
   <span class="mute"> – ${esc(i.src)} ${esc(i.time)}</span></li>`).join(''):'<li class="mute">Nincs találat (vagy még töltenek a hírfolyamok).</li>';
}
function renderInj(){
  const I=S.injuries;
  $('#itb').innerHTML=I.length?I.map(r=>`<tr class="ck" onclick="openT('${r.tid}')"><td class="l"><b>${esc(r.abbr)}</b></td><td class="l">${esc(r.player)}</td><td class="l">${esc(r.status)}</td>
   <td>${nf(r.ppg,1)}</td><td>${nf(r.mpg,0)}</td><td class="${r.impact>1?'neg':''}">−${nf(r.impact,1)}${r.known?'':' <span class="mute" title="nincs statisztika, alapérték">*</span>'}</td>
   <td class="l mute">${esc(r.date)}${r.old?' (régi)':''}</td><td class="l wrap mute">${esc(r.type?r.type+': ':'')}${esc(r.comment)}</td></tr>`).join('')
   :'<tr><td class="l mute" colspan="8">Nincs sérültadat (még tölt, vagy nincs bejelentett sérült).</td></tr>';
}

function renderAcc(){
  const A=S.acc;
  $('#atb').innerHTML=A.models.length?A.models.map(m=>`<tr><td class="l">${esc(m.name)}</td><td>${m.n}</td><td><b>${p0(m.hit)}</b></td><td>${nf(m.mae_m,1)}</td><td>${nf(m.mae_t,1)}</td><td>${nf(m.brier,3)}</td></tr>`).join('')
   :'<tr><td class="l mute" colspan="6">Még nincs kiértékelt meccs – az első lejátszott alapszakasz-meccsek után jelenik meg.</td></tr>';
  $('#rtb').innerHTML=A.recent.length?A.recent.map(r=>`<tr><td class="l">${esc(r.match)}</td><td class="mute">${esc(r.date)}</td><td>${esc(r.pred)}</td><td><b>${esc(r.actual)}</b></td>
   <td class="${r.ok?'pos':'neg'}">${r.ok?'✓':'✗'}</td><td>${sg(r.err_t,1)}</td></tr>`).join(''):'<tr><td class="l mute" colspan="6">–</td></tr>';
}

function injTable(rows){
  if(!rows||!rows.length)return '<div class="mute">Nincs bejelentett sérült.</div>';
  return `<div class="tw"><table><thead><tr><th class="l">Játékos</th><th class="l">Státusz</th><th>Pont</th><th>Hatás</th><th class="l">Megjegyzés</th></tr></thead><tbody>${rows.map(r=>`<tr>
   <td class="l">${esc(r.player)}</td><td class="l">${esc(r.status)}</td><td>${nf(r.ppg,1)}</td><td>−${nf(r.impact,1)}</td><td class="l wrap mute">${esc(r.comment)}</td></tr>`).join('')}</tbody></table></div>`;
}
function newsList(n){
  if(!n.items.length)return '<div class="mute">Még nincs összegyűjtött hír.</div>';
  return `<ul class="news">${n.items.map(i=>`<li><span class="${cls(i.s)}">${i.s>0?'▲':i.s<0?'▼':'•'}</span>
   ${i.url?`<a href="${esc(i.url)}" target="_blank" rel="noopener">${esc(i.title)}</a>`:esc(i.title)}${(i.tags||[]).map(t=>`<span class="tag">${esc(t)}</span>`).join('')}
   <span class="mute"> – ${esc(i.src)} ${esc(i.time)}</span></li>`).join('')}</ul>`;
}
async function newsInto(el,tid){
  try{const n=await (await fetch(window.STATIC?'news/'+encodeURIComponent(tid)+'.json?t='+Date.now():'/api/news?team='+encodeURIComponent(tid))).json();$(el).innerHTML=newsList(n);}catch(e){$(el).textContent='A hírek nem tölthetők be.';}
}

function openG(id){
  const g=S.games.find(x=>x.id===id);if(!g)return;
  const f=g.final,H=g.home.abbr,A=g.away.abbr;
  $('#dt').innerHTML=`<div style="font-weight:700;font-size:16px">${esc(g.away.name)} @ ${esc(g.home.name)} ${confB(g.conf)}</div><div class="mute">${esc(g.time)} (magyar idő)${g.pre?' · előszezon':''}${g.state!=='pre'?` · ${esc(A)} ${nf(g.as)} – ${nf(g.hs)} ${esc(H)} ${esc(g.detail)}`:''}</div>`;
  const order=['rating','season','form','stat','market','final'];
  const mrows=order.filter(k=>g.models[k]).map(k=>{const m=g.models[k];return `<tr${k==='final'?' style="font-weight:700"':''}><td class="l">${esc(S.model_names[k])}</td>
   <td>${nf(m.ap,1)}</td><td>${nf(m.hp,1)}</td><td>${(m.margin>0?H:A)} ${nf(Math.abs(m.margin),1)}</td><td>${nf(m.total,1)}</td><td>${p0(1-m.p)}</td><td>${p0(m.p)}</td></tr>`;}).join('');
  const brows=g.books.map(b=>`<tr><td class="l">${esc(b.book)} <span class="mute">${esc(b.src||'')}</span></td>
   <td>${evc(b.ml_a,b.ev_ml_a)}</td><td>${evc(b.ml_h,b.ev_ml_h)}</td><td>${b.p_h!=null?p0(b.p_h):'–'}</td>
   <td>${b.spread_h!=null?esc(H)+' '+sg(b.spread_h,1):'–'}</td><td>${evc(b.sp_h,b.ev_sp_h)}</td><td>${evc(b.sp_a,b.ev_sp_a)}</td>
   <td>${b.total?nf(b.total,1):'–'}</td><td>${evc(b.over,b.ev_over)}</td><td>${evc(b.under,b.ev_under)}</td></tr>`).join('');
  const k=(l,v)=>`<div><small>${l}</small><b>${v}</b></div>`;
  $('#dbody').innerHTML=`<div class="kpi">${k('Becsült eredmény',`${esc(A)} ${nf(f.ap)} – ${nf(f.hp)} ${esc(H)}`)}${k('Győztes',(f.margin>0?esc(H):esc(A))+' '+p0(Math.max(f.p,1-f.p)))}
   ${k('Összpont',nf(f.total,1))}${k('Különbség',nf(Math.abs(f.margin),1)+' pont')}${k('Pihenőnap',`${esc(A)}: ${g.rest_a??'–'} · ${esc(H)}: ${g.rest_h??'–'}`)}</div>
   <h3>Modellek összevetése</h3>
   <div class="tw"><table><thead><tr><th class="l">Modell</th><th>${esc(A)} pont</th><th>${esc(H)} pont</th><th>Különbség</th><th>Összpont</th><th>${esc(A)} esély</th><th>${esc(H)} esély</th></tr></thead><tbody>${mrows}</tbody></table></div>
   <h3>Mi mozgatja a becslést</h3>
   <ul>${g.factors.map(x=>`<li>${esc(x.txt)}${x.key==='nodata'?'':` <span class="${cls(x.pts)}">(${esc(H)} szemszögéből ${sg(x.pts,1)} pont)</span>`}</li>`).join('')||'<li class="mute">Nincs külön tényező.</li>'}</ul>
   <h3>Fogadóirodák</h3>
   ${g.books.length?`<div class="tw"><table><thead><tr><th class="l">Iroda / forrás</th><th>${esc(A)} győz</th><th>${esc(H)} győz</th><th>Hazai esély (árrés nélkül)</th><th>Hendikep</th><th>${esc(H)} hend.</th><th>${esc(A)} hend.</th><th>O/U vonal</th><th>Over</th><th>Under</th></tr></thead><tbody>${brows}</tbody></table></div>
   <div class="note">EV = várható érték egységnyi tétre a végső becslés szerinti esélyekkel. Az ESPN amerikai szorzóiból számolt tizedes szorzó kerekített.</div>`:'<div class="mute">Erre a meccsre még nincs fogadóirodai vonal.</div>'}
   <div class="grid g2"><div><h3>${esc(g.away.name)} – sérültek</h3>${injTable(g.inj_a)}<h3>Hírek</h3><div id="na" class="mute">Betöltés…</div></div>
   <div><h3>${esc(g.home.name)} – sérültek</h3>${injTable(g.inj_h)}<h3>Hírek</h3><div id="nh" class="mute">Betöltés…</div></div></div>`;
  dlg.showModal();newsInto('#na',g.away.id);newsInto('#nh',g.home.id);
}
function openT(id){
  const t=S.teams.find(x=>x.id===id);if(!t)return;
  $('#dt').innerHTML=`<div style="font-weight:700;font-size:16px">${logo(t)}${esc(t.name)}</div><div class="mute">${t.rank?`Erősségi rangsor: ${t.rank}. · `:''}${esc(t.season_label||'')}</div>`;
  const k=(l,v)=>`<div><small>${l}</small><b>${v}</b></div>`;
  const rows=S.injuries.filter(r=>r.tid===id);
  const games=S.games.filter(g=>g.home.id===id||g.away.id===id);
  $('#dbody').innerHTML=`<div class="kpi">${k('Mérleg',`${t.w??0}–${t.l??0}`)}${k('Dobott / kapott',`${nf(t.pf,1)} / ${nf(t.pa,1)}`)}${k('Nettó erősség',sg(t.net,1))}
   ${k('Utolsó 10',`${t.l10_w??0}–${t.l10_l??0}`)}${k('Sérülés-hatás',t.inj_n?'−'+nf(t.inj_pts,1)+' pont':'–')}${k('Hírhangulat',t.news_n>=2?sg(t.news_s,2):'–')}</div>
   ${games.length?`<h3>Meccsei a következő napokban</h3><ul>${games.map(g=>`<li><a href="#" onclick="openG('${g.id}');return false">${esc(g.away.abbr)} @ ${esc(g.home.abbr)}</a> <span class="mute">${esc(g.time)}</span> – becslés: ${esc(g.away.abbr)} ${nf(g.final.ap)} – ${nf(g.final.hp)} ${esc(g.home.abbr)}</li>`).join('')}</ul>`:''}
   <h3>Sérültek</h3>${injTable(rows)}<h3>Hírek, pletykák</h3><div id="nt" class="mute">Betöltés…</div>`;
  dlg.showModal();newsInto('#nt',id);
}

load();setInterval(load,window.STATIC?120000:20000);
</script>
</body>
</html>
"""


# ---------------------------------------------------------------------------
def write_static(engine, out_dir):
    out = Path(out_dir)
    (out / "news").mkdir(parents=True, exist_ok=True)
    (out / "index.html").write_text(HTML.replace("<head>", "<head>\n<script>window.STATIC=true</script>", 1),
                                    encoding="utf-8")
    (out / "state.json").write_text(engine.state_json(), encoding="utf-8")
    for tid, t in engine.teams.items():
        if t.get("nba"):
            (out / "news" / f"{tid}.json").write_text(json.dumps(clean(engine.news_for(tid)), ensure_ascii=False),
                                                      encoding="utf-8")
    (out / ".nojekyll").write_text("", encoding="utf-8")


def write_summary(engine):
    """GitHub Actions összefoglaló: a futás oldalán táblázatként jelenik meg."""
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    st = json.loads(engine.state_json())
    lines = ["## NBA Meccsradar – következő meccsek", "",
             "| Időpont (Budapest) | Meccs | Becslés | Győztes | Összpont | Irodák |", "|---|---|---|---|---|---|"]
    for g in [g for g in st.get("games", []) if g["state"] == "pre"][:40]:
        f = g["final"]
        win = g["home"]["abbr"] if f["margin"] > 0 else g["away"]["abbr"]
        n = (g.get("market") or {}).get("n", 0)
        lines.append(f"| {g['time']} | {g['away']['abbr']} @ {g['home']['abbr']} | {f['ap']:.0f} – {f['hp']:.0f} | "
                     f"{win} {max(f['p'], 1 - f['p']) * 100:.0f}% | {f['total']:.1f} | {n} |")
    src = st.get("sources", [])
    lines += ["", f"Működő szorzóforrások: {sum(1 for x in src if x.get('games'))}/{len(src)} – " +
              ", ".join(f"{x['name']} ({x.get('games') or 0})" for x in src)]
    fs = st.get("feed_status", [])
    lines += [f"Hírportálok: {sum(1 for x in fs if x.get('n'))}/{len(fs)} ad hírt, összesen {len(st.get('feed', []))} cím"]
    if st["status"].get("errors"):
        lines += ["", "Hibák:", ""] + [f"- {e}" for e in st["status"]["errors"]]
    text = "\n".join(lines)
    print(text)
    if path:
        with open(path, "a", encoding="utf-8") as fh:
            fh.write(text + "\n")


def main():
    ap = argparse.ArgumentParser(description="NBA Meccsradar")
    ap.add_argument("--demo", action="store_true", help="kitalált adatokkal fut (internet nélkül)")
    ap.add_argument("--port", type=int, default=CONFIG["port"])
    ap.add_argument("--no-browser", action="store_true")
    ap.add_argument("--odds-key", help="The Odds API kulcs (több fogadóiroda)")
    ap.add_argument("--days", type=int, help="hány napra előre (alapból 7)")
    ap.add_argument("--build", metavar="MAPPA", help="egyszer lefut, és statikus oldalt ír ebbe a mappába (GitHub Pages)")
    ap.add_argument("--data", metavar="MAPPA", default="data", help="--build módban az előzmények helye")
    args = ap.parse_args()

    cfg = dict(CONFIG)
    cfg["port"] = args.port
    if args.odds_key:
        cfg["odds_api_key"] = args.odds_key
    if args.days:
        cfg["days_ahead"] = args.days
    if args.demo:
        cfg["pred_file"] = "nba_predikciok_demo.json"
        cfg["sched_refresh_s"] = 60
        cfg["news_refresh_s"] = 300
        cfg["odds_refresh_s"] = 600
        cfg["odds_free_refresh_s"] = 120
        cfg["feed_refresh_s"] = 120
        src = DemoSource(cfg)
    else:
        src = LiveSource(cfg)

    if args.build:
        cfg["pred_file"] = str(Path(args.data) / ("nba_predikciok_demo.json" if args.demo else "nba_predikciok.json"))
        Path(args.data).mkdir(parents=True, exist_ok=True)
        src.name += " · GitHub Actions"
        engine = Engine(src, cfg)
        engine.load_cache(args.data)
        print(f"NBA Meccsradar – egyszeri futás ({now_str()})", flush=True)
        engine.run_once()
        engine.save_cache(args.data)
        write_static(engine, args.build)
        write_summary(engine)
        return

    engine = Engine(src, cfg)
    threading.Thread(target=engine.run, daemon=True).start()
    server = ThreadingHTTPServer(("127.0.0.1", cfg["port"]), make_handler(engine))
    url = f"http://localhost:{cfg['port']}"
    print(f"NBA Meccsradar fut: {url}   (leállítás: Ctrl+C)")
    if not args.no_browser:
        threading.Timer(1.0, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nLeállítva.")


if __name__ == "__main__":
    main()
