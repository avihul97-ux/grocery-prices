#!/usr/bin/env python3
"""
מושך מחירי סופרים ברמת גן והסביבה מקבצי "שקיפות המחירים" של הרשתות,
ומתאים אותם למוצרים שהמשפחה קונה. התוצאה: prices.json (קטן) ו-report.md (דוח מה עבד).

מריצים אוטומטית ב-GitHub Actions (ראו prices.yml). אין צורך לערוך כאן כלום:
את רשימת המוצרים הבוט שולח לבד (WANTED_URL), ואת הרשתות אפשר לשנות במשתנה CHAINS.
האזור: רמת גן, גבעתיים, בני ברק ותל אביב. אם יש הרבה סניפים ברשת, נלקחים קודם אלה שבערים
הראשונות ברשימה. אפשר לשנות במשתנה הסביבה CITIES (ערים מופרדות בפסיק, ניסוחים שונים של אותה עיר בלוכסן).
"""
import datetime
import gzip
import io
import json
import math
import os
import re
import subprocess
import sys
import tempfile
import time
import traceback
import urllib.request
import xml.etree.ElementTree as ET
import zipfile
from concurrent.futures import ThreadPoolExecutor

DEFAULT_CHAINS = ("SHUFERSAL,RAMI_LEVY,VICTORY_NEW_SOURCE,OSHER_AD,YOHANANOF,"
                  "YAYNO_BITAN_AND_CARREFOUR,HAZI_HINAM,TIV_TAAM,KESHET,MAHSANI_ASHUK_NEW_SOURCE")
# סדר הערים הוא גם סדר העדיפות כשיש לרשת יותר סניפים מהמותר (MAX_STORES)
HOME_CITIES = "רמת גן/ramat gan,גבעתיים/givatayim,בני ברק/bnei brak,תל אביב/tel aviv"
MAX_STORES = 8          # מקסימום סניפים לכל רשת (כדי לא להוריד עשרות קבצים גדולים)


def area_groups():
    """[[ניסוחים של עיר 1], [ניסוחים של עיר 2], ...] לפי סדר העדיפות."""
    raw = os.environ.get("CITIES") or HOME_CITIES
    groups = [[v.strip() for v in g.split("/") if v.strip()] for g in raw.split(",")]
    return [g for g in groups if g]


CHAIN_NAMES = {
    "SHUFERSAL": "שופרסל", "RAMI_LEVY": "רמי לוי", "VICTORY": "ויקטורי", "VICTORY_NEW_SOURCE": "ויקטורי",
    "OSHER_AD": "אושר עד", "YOHANANOF": "יוחננוף", "YAYNO_BITAN_AND_CARREFOUR": "יינות ביתן/קרפור",
    "HAZI_HINAM": "חצי חינם", "TIV_TAAM": "טיב טעם", "KESHET": "קשת טעמים",
    "MAHSANI_ASHUK": "מחסני השוק", "MAHSANI_ASHUK_NEW_SOURCE": "מחסני השוק", "DOR_ALON": "דור אלון",
    "STOP_MARKET": "סטופ מרקט", "ZOL_VEBEGADOL": "זול ובגדול", "SUPER_SAPIR": "סופר ספיר",
    "BAREKET": "ברקת", "CITY_MARKET_SHOPS": "סיטי מרקט", "YELLOW": "ילו",
}

# אם הבוט עוד לא שלח רשימה, מתחילים מסל בסיסי כדי שיהיה מה לראות
DEFAULT_WANTED = ["חלב", "ביצים", "לחם", "קוטג", "גבינה צהובה", "יוגורט", "שמנת", "חמאה", "עוף", "בשר טחון",
                  "אורז", "פסטה", "סוכר", "קמח", "שמן", "טחינה", "עגבניות", "מלפפונים", "בצל", "תפוחי אדמה",
                  "גזר", "בננות", "תפוחים", "לימון", "נייר טואלט", "נוזל כלים"]

# ---------------------------------------------------------------- Hebrew text helpers
_FINAL = str.maketrans({"ך": "כ", "ם": "מ", "ן": "נ", "ף": "פ", "ץ": "צ"})


def norm(s):
    s = str(s or "").lower().translate(_FINAL)
    s = re.sub(r"[׳'\"״`]", "", s)
    return re.sub(r"\s+", " ", s.replace("-", " ")).strip()


def tokens(s):
    return [t for t in re.split(r"[^\w%]+", norm(s)) if t]


def stem(w):
    if len(w) > 4 and w.endswith(("ות", "ים", "ימ")):   # norm() הופך ם לסופית ל-מ, לכן גם "ימ"
        return w[:-2]
    if len(w) > 4 and w.endswith("י"):                  # סמיכות ברבים: גרעיני, תפוחי
        return w[:-1]
    if len(w) > 3 and w.endswith("ה"):
        return w[:-1]
    return w


def tok_eq(q, p):
    sq, sp = stem(q), stem(p)
    return sq == sp or (len(sq) >= 4 and sp == sq + "ת")   # סמיכות: גבינה -> גבינת. בלי תחיליות רחבות (סוכר != סוכריות)


PRODUCE_WORDS = ("עגבניה עגבניות מלפפון בצל גזר תפוח תפוחי אדמה בננה לימון תפוז אשכולית קלמנטינה מנדרינה אבוקדו חסה כרוב "
                 "כרובית ברוקולי פלפל חציל קישוא דלעת בטטה פטרוזיליה כוסברה שמיר נענע שום אגס ענבים אפרסק נקטרינה שזיף "
                 "מנגו אבטיח מלון תות רימון פומלה סלק צנון צנונית קולרבי תרד סלרי כרפס אננס קיווי תמר תאנה פטריות").split()
PRODUCE_STEMS = {stem(norm(w)) for w in PRODUCE_WORDS}


def is_produce(qtoks):
    """שאילתה של פרי או ירק טרי (לפי המילה הראשונה, או 'תפוחי אדמה')."""
    return bool(qtoks) and (stem(qtoks[0]) in PRODUCE_STEMS or "אדמה" in qtoks)


PROCESSED = {"קפוא", "מוקפא", "בגריל", "גריל", "צלוי", "מעושן", "מבושל", "מטוגן", "מתובל", "ממולא", "שניצל", "קבב", "נקניק", "מרינדה"}


def processed(qtoks, ptoks):
    """האם בשם יש מילה של מוצר מעובד שלא ביקשו (חזה עוף קפוא, חזה עוף בגריל...)."""
    return any(norm(w) in PROCESSED and norm(w) not in qtoks for w in ptoks)


def is_fresh_item(qtoks, info):
    """מוצר במשקל שהשם שלו פשוט (עגבניה, בצל יבש...) ולא מוצר מעובד או אריזה."""
    ptoks = tokens(info["name"])
    if not info["weighted"] or not ptoks or len(ptoks) > len(qtoks) + 2:
        return False
    if "אדמה" in ptoks and "אדמה" not in qtoks:   # תפוחים != תפוחי אדמה
        return False
    if processed(qtoks, ptoks):
        return False
    return tok_eq(qtoks[0], ptoks[0])


def short_msg(msg):
    """מקצר הודעות שגיאה ארוכות של הסקרייפר, כדי שהדוח יהיה קריא."""
    m = str(msg or "")
    if "timeout" in m:
        return "האתר לא ענה בזמן, כנראה חסום מחוץ לישראל"
    if "Num of Files= 0" in m or "No files to download" in m:
        return "האתר לא החזיר קבצים"
    return m[-120:] if m else "אין פרטים"


def name_matches(qtoks, ptoks):
    return bool(qtoks) and all(any(tok_eq(q, p) for p in ptoks) for q in qtoks)


# ---------------------------------------------------------------- reading XML files (gz / zip / odd encodings)
def read_bytes(path):
    with open(path, "rb") as f:
        b = f.read()
    if b[:2] == b"\x1f\x8b":
        b = gzip.decompress(b)
    elif b[:2] == b"PK":
        z = zipfile.ZipFile(io.BytesIO(b))
        b = z.read(z.namelist()[0])
    return b


def _decode(b):
    if b[:2] in (b"\xff\xfe", b"\xfe\xff"):
        return b.decode("utf-16")
    for enc in ("utf-8-sig", "windows-1255"):
        try:
            return b.decode(enc)
        except UnicodeDecodeError:
            continue
    return b.decode("utf-8", errors="replace")


def iter_records(path, wanted_tags):
    """מחזיר לכל אלמנט בשם מבוקש מילון {שם-תג-באותיות-קטנות: טקסט}. עמיד לקידודים ולמרחבי שמות."""
    raw = read_bytes(path)
    sources = [raw]
    try:
        sources.append(re.sub(r"<\?xml[^>]*\?>", "", _decode(raw), count=1).encode("utf-8"))
    except Exception:
        pass
    last_err = None
    for src in sources:
        try:
            out = []
            for _, el in ET.iterparse(io.BytesIO(src), events=("end",)):
                tag = el.tag.rsplit("}", 1)[-1].lower()
                if tag in wanted_tags:
                    out.append({c.tag.rsplit("}", 1)[-1].lower(): (c.text or "").strip() for c in el})
                    el.clear()
            return out
        except ET.ParseError as e:
            last_err = e
    raise last_err


def to_float(x):
    try:
        return float(str(x).replace(",", ".").strip())
    except ValueError:
        return 0.0


# ---------------------------------------------------------------- stores in the city
def city_stores(files, groups):
    """מחזיר ({מספר סניף: שם}, {מספר סניף: דירוג עיר}, דוגמאות) לסניפים שבאחת הערים."""
    found, rank, sample = {}, {}, []
    for p in files:
        try:
            recs = iter_records(p, {"store", "branch"})
        except Exception:
            continue
        for r in recs:
            sid = re.sub(r"\D", "", r.get("storeid", ""))
            if not sid:
                continue
            blob = norm(" ".join([r.get("city", ""), r.get("address", ""), r.get("storename", "")]))
            if len(sample) < 4:
                sample.append(" / ".join(x for x in [r.get("storename", ""), r.get("city", "")] if x))
            for k, g in enumerate(groups):
                if any(norm(w) in blob for w in g):
                    found[int(sid)] = r.get("storename") or r.get("address") or ("סניף " + sid)
                    rank[int(sid)] = k
                    break
    return found, rank, sample


def price_file_info(path):
    m = re.search(r"-(\d+)-(\d{8,14})", os.path.basename(path))
    return (int(m.group(1)), m.group(2)) if m else (None, "")


def newest_per_store(files):
    best = {}
    for p in files:
        sid, ts = price_file_info(p)
        if sid is None:
            continue
        if sid not in best or ts > best[sid][0]:
            best[sid] = (ts, p)
    return {sid: v[1] for sid, v in best.items()}


# ---------------------------------------------------------------- prices
def collect(path, chain, store_name, queries, found, alts=None):
    """קורא קובץ מחירים של סניף ורושם מועמדים לכל מוצר מבוקש."""
    n = 0
    for r in iter_records(path, {"item", "product"}):
        price = to_float(r.get("itemprice") or r.get("price"))
        name = r.get("itemname") or r.get("itemnm") or r.get("productname") or ""
        code = r.get("itemcode") or r.get("itemid") or ""
        if not (name and code and 0 < price < 3000):
            continue
        ptoks = tokens(name)
        for q, qtoks in queries.items():
            if not (name_matches(qtoks, ptoks) or any(name_matches(v, ptoks) for v in (alts or {}).get(q, []))):
                continue
            weighted = r.get("bisweighted", "0").strip() in ("1", "true", "True")
            c = found.setdefault(q, {}).setdefault(code, {"name": name, "weighted": weighted, "chains": {}, "stores": set()})
            c["stores"].add((chain, store_name))
            if len(name) > len(c["name"]):
                c["name"] = name
            unit_raw = to_float(r.get("unitofmeasureprice"))
            unit = unit_raw or price
            cur = c["chains"].get(chain)
            if cur is None or price < cur["price"]:
                c["chains"][chain] = {"price": price, "unit": unit, "unit_raw": unit_raw, "store": store_name, "name": name}
            n += 1
    return n


def rank(q_toks, code, info, alt=None):
    ptoks = tokens(info["name"])
    head = 1 if ptoks and any(tok_eq(v[0], ptoks[0]) for v in [q_toks] + (alt or []) if v) else 0
    return (head, len(info["chains"]), len(info["stores"]), -len(ptoks))


def amount_of(v):
    """כמות המוצר ביחידת המידה שלו (מחיר חלקי מחיר ליחידת מידה), או None אם אין נתון."""
    u = v.get("unit_raw") or 0
    return v["price"] / u if u > 0 else None


def best_equivalent(info, code, cands, chain):
    """לרשת שאין לה את המוצר המדויק: מוצר דומה אצלה (שם דומה וגודל דומה). מחזיר (ברקוד, שם, נתוני מחיר) או None."""
    ref = min(info["chains"].values(), key=lambda v: v["price"])
    a_ref = amount_of(ref)
    ptoks = set(tokens(info["name"]))
    best = None
    for c2, i2 in cands.items():
        v = i2["chains"].get(chain)
        if c2 == code or v is None or i2["weighted"] != info["weighted"]:
            continue
        a = amount_of(v)
        ratio = (a / a_ref) if (a and a_ref) else None
        if ratio is not None and not (0.7 <= ratio <= 1.45):
            continue                       # גודל אריזה שונה מדי: לא משווים
        t2 = set(tokens(v["name"]))
        sim = len(ptoks & t2) / max(1, len(ptoks | t2))
        if sim < (0.5 if ratio is None else 0.2):
            continue
        key = (sim, -abs(math.log(ratio)) if ratio else -0.5, -len(t2))
        if best is None or key > best[0]:
            best = (key, c2, v["name"], v)
    return (best[1], best[2], best[3]) if best else None


def build_rows(queries, found, pinned, alts=None):
    rows, candidates, missing = [], {}, []
    for q, qtoks in queries.items():
        cands = found.get(q)
        if not cands:
            missing.append(q)
            continue
        fresh = {c: i for c, i in cands.items() if is_fresh_item(qtoks, i)} if is_produce(qtoks) else {}
        use_fresh = bool(fresh) and pinned.get(q) not in cands
        ranked = sorted(cands.items(), key=lambda kv: ((kv[0] in fresh) if use_fresh else 0,) + rank(qtoks, kv[0], kv[1], (alts or {}).get(q)), reverse=True)
        candidates[q] = [{"barcode": c, "name": i["name"], "chains": sorted(i["chains"]),
                          "min_price": min(v["price"] for v in i["chains"].values())} for c, i in ranked[:6]]
        code = pinned.get(q) if pinned.get(q) in cands else ranked[0][0]
        info = cands[code]
        if use_fresh or (info["weighted"] and code not in pinned.values()):
            # פירות וירקות במשקל: הקוד שונה בין רשתות, לכן בוחרים בכל רשת בנפרד את המוצר הכי "פשוט"
            per_chain = {}
            for c2, i2 in (fresh if use_fresh else cands).items():
                if not i2["weighted"] or processed(qtoks, tokens(i2["name"])):
                    continue
                for chain, v in i2["chains"].items():
                    key = (1 if tokens(i2["name"]) and tok_eq(qtoks[0], tokens(i2["name"])[0]) else 0,
                           -len(tokens(i2["name"])), -v["price"])
                    if chain not in per_chain or key > per_chain[chain][0]:
                        per_chain[chain] = (key, c2, i2["name"], v)
            for chain, (_, c2, nm, v) in per_chain.items():
                rows.append(row(q, nm + " (לק\"ג)", c2, chain, v))
        else:
            for chain, v in info["chains"].items():
                rows.append(row(q, info["name"], code, chain, v))
            if pinned.get(q) != code:      # לא נעול ידנית: ברשתות שאין להן את המוצר המדויק מחפשים מוצר דומה
                for chain in sorted({ch for i in cands.values() for ch in i["chains"]} - set(info["chains"])):
                    eq = best_equivalent(info, code, cands, chain)
                    if eq:
                        rows.append(row(q, "≈ " + eq[1], eq[0], chain, eq[2]))
    return rows, candidates, missing


def row(q, product, barcode, chain, v):
    return {"item": q, "product": product, "barcode": barcode, "chain": CHAIN_NAMES.get(chain, chain),
            "branch": v["store"], "price": round(v["price"], 2), "promo_price": None,
            "promo_desc": "", "unit_price": round(v["unit"], 2)}


# ---------------------------------------------------------------- downloading (uses the open-source scraper)
def scrape_in_subprocess(chain, regex, workdir, timeout):
    os.makedirs(workdir, exist_ok=True)
    cmd = [sys.executable, os.path.abspath(__file__), "--scrape", chain, regex]
    try:
        p = subprocess.run(cmd, cwd=workdir, capture_output=True, text=True, timeout=timeout)
        tail = (p.stdout + "\n" + p.stderr).strip().splitlines()[-6:]
        return p.returncode == 0, " | ".join(tail)
    except subprocess.TimeoutExpired:
        return False, "timeout after %d seconds (probably blocked from outside Israel)" % timeout


def scrape_main(chain, regex):
    from il_supermarket_scarper import ScarpingTask
    task = ScarpingTask(enabled_scrapers=[chain], file_name_regex=regex, multiprocessing=2)
    try:
        task.start(single_pass=True)
    except TypeError:
        task.start()
    if hasattr(task, "join"):
        task.join()


def list_files(workdir, prefix):
    out = []
    for root, _, names in os.walk(workdir):
        for n in names:
            if n.lower().startswith(prefix):
                out.append(os.path.join(root, n))
    return sorted(out)


def default_downloader(chain, regex, workdir):
    # קובצי סניפים קטנים: אם אין תשובה אחרי 5 דקות, כנראה שהרשת חוסמת כניסה מחוץ לישראל
    return scrape_in_subprocess(chain, regex, workdir, timeout=300 if "stores" in regex else 900)


# ---------------------------------------------------------------- orchestration
def fetch_wanted():
    url = os.environ.get("WANTED_URL", "").strip()
    items, pinned, alts, source = [], {}, {}, "ברירת מחדל (WANTED_URL לא הוגדר)"
    if url:
        try:
            with urllib.request.urlopen(url, timeout=60) as resp:
                j = json.loads(resp.read().decode("utf-8"))
            items = [str(x).strip() for x in j.get("items", []) if str(x).strip()]
            pinned = {str(k): str(v) for k, v in (j.get("pinned") or {}).items() if v}
            alts = {str(k): [str(a).strip() for a in v if str(a).strip()][:4]
                    for k, v in (j.get("alts") or {}).items() if isinstance(v, list)}
            source = "הבוט (%d מוצרים)" % len(items)
        except Exception as e:
            source = "ברירת מחדל (קריאת הרשימה מהבוט נכשלה: %s)" % e
    if not items:
        items = list(DEFAULT_WANTED)
    seen, out = set(), []
    for it in items:
        if norm(it) not in seen:
            seen.add(norm(it))
            out.append(it)
    return out[:80], pinned, alts, source


def merge(found, part):
    for q, cands in part.items():
        for code, info in cands.items():
            dst = found.setdefault(q, {}).setdefault(code, {"name": info["name"], "weighted": info["weighted"], "chains": {}, "stores": set()})
            dst["chains"].update(info["chains"])
            dst["stores"] |= info["stores"]
            if len(info["name"]) > len(dst["name"]):
                dst["name"] = info["name"]


RETRIES = 3        # אתרי הרשתות לפעמים לא עונים בפעם הראשונה (כך קרה לשופרסל), לכן מנסים שוב
RETRY_SLEEP = 10


def download_with_retries(downloader, chain, regex, wd, got_files):
    ok, msg = False, ""
    for i in range(RETRIES):
        ok, msg = downloader(chain, regex, wd)
        if got_files():
            break
        if i + 1 < RETRIES:
            time.sleep(RETRY_SLEEP)
    return ok, msg


def work_chain(chain, queries, downloader, base_dir, alts=None):
    line = {"chain": chain, "status": "", "stores": 0, "matched": 0}
    found = {}
    wd = os.path.join(base_dir, chain)
    try:
        ok, msg = download_with_retries(downloader, chain, r"(?i)stores", wd, lambda: bool(list_files(wd, "stores")))
        store_files = list_files(wd, "stores")
        if not store_files:
            line["status"] = "לא ירדו קבצי סניפים (%s)" % short_msg(msg)
            return line, found
        stores, rank, sample = city_stores(store_files, area_groups())
        if not stores:
            line["status"] = "אין סניפים ברמת גן והסביבה בקבצים. דוגמאות: " + "; ".join(sample)
            return line, found
        cap = int(os.environ.get("MAX_STORES") or MAX_STORES)
        keep = sorted(stores, key=lambda x: (rank[x], x))[:cap]   # קודם הערים הראשונות ברשימה
        stores = {k: stores[k] for k in keep}
        ids = "|".join(str(i) for i in sorted(stores))
        ok, msg = download_with_retries(downloader, chain, r"(?i)pricefull.*-0*(?:%s)-\d{8,}" % ids, wd,
                                        lambda: bool(newest_per_store(list_files(wd, "pricefull"))))
        files = newest_per_store(list_files(wd, "pricefull"))
        if not files:
            line["status"] = "יש %d סניפים באזור, אבל לא ירדו קבצי מחירים (%s)" % (len(stores), short_msg(msg))
            return line, found
        line["stores"] = len(files)
        for sid, path in files.items():
            line["matched"] += collect(path, chain, stores.get(sid, "סניף %d" % sid), queries, found, alts)
        line["status"] = "תקין"
    except Exception as e:  # רשת אחת שנכשלה לא מפילה את השאר
        line["status"] = "שגיאה: %s" % e
        traceback.print_exc()
    return line, found


def run(chains, wanted, pinned, downloader, base_dir, alts=None):
    queries = {q: tokens(q) for q in wanted if tokens(q)}
    alt_toks = {q: [t for t in (tokens(a) for a in (alts or {}).get(q, [])) if t] for q in queries}
    results = {}
    with ThreadPoolExecutor(max_workers=4) as ex:
        futs = {c: ex.submit(work_chain, c, queries, downloader, base_dir, alt_toks) for c in chains}
        for c, f in futs.items():
            results[c] = f.result()
    found, report = {}, []
    for c in chains:          # מיזוג בסדר קבוע, כדי שהתוצאה תהיה זהה בכל הרצה
        line, part = results[c]
        report.append(line)
        merge(found, part)
    rows, candidates, missing = build_rows(queries, found, pinned, alt_toks)
    return rows, candidates, missing, report


def write_report(path, report, wanted_source, wanted, missing, rows):
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
    lines = ["# דוח מחירים", "", "הרצה: %s" % now, "מקור רשימת המוצרים: %s" % wanted_source, "",
             "| רשת | סטטוס | סניפים באזור | מוצרים שנמצאו |", "|---|---|---|---|"]
    for r in report:
        lines.append("| %s | %s | %s | %s |" % (CHAIN_NAMES.get(r["chain"], r["chain"]), r["status"], r["stores"], r["matched"]))
    chains_ok = sorted({x["chain"] for x in rows})
    lines += ["", "רשתות עם מחירים: %s" % (", ".join(chains_ok) or "אין"),
              "מוצרים שלא נמצאו באף רשת: %s" % (", ".join(missing) or "אין"),
              "סה\"כ שורות מחיר: %d" % len(rows)]
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


MAX_STALE_DAYS = 4      # רשת שנכשלה בהרצה: משאירים את המחירים הקודמים שלה עד 4 ימים (מסומנים ב-as_of)


def carry_over(rows, report, prev, wanted_items, today):
    """אם רשת לא נגישה בהרצה הזו אבל היו לה מחירים בהרצה קודמת, משאירים אותם (עד MAX_STALE_DAYS)."""
    have = {(r["item"], r["chain"]) for r in rows}
    wanted = {norm(w) for w in wanted_items}
    prev_day = prev.get("updated", "")
    for line in report:
        if line.get("stores"):
            continue
        disp = CHAIN_NAMES.get(line["chain"], line["chain"])
        kept, oldest = 0, None
        for r in prev.get("prices", []):
            if r.get("chain") != disp or norm(r.get("item", "")) not in wanted or (r["item"], disp) in have:
                continue
            as_of = r.get("as_of") or prev_day
            try:
                age = (today - datetime.date.fromisoformat(as_of)).days
            except ValueError:
                continue
            if age > MAX_STALE_DAYS:
                continue
            rows.append(dict(r, as_of=as_of))
            have.add((r["item"], disp))
            kept += 1
            oldest = as_of if oldest is None or as_of < oldest else oldest
        if kept:
            line["status"] += " | נשארו %d מחירים ישנים מ-%s" % (kept, oldest)
    return rows


def main(downloader=default_downloader, out_dir="."):
    chains = [c.strip() for c in (os.environ.get("CHAINS") or DEFAULT_CHAINS).split(",") if c.strip()]
    wanted, pinned, alts, source = fetch_wanted()
    base = tempfile.mkdtemp(prefix="prices_")
    rows, candidates, missing, report = run(chains, wanted, pinned, downloader, base, alts)
    prices_path = os.path.join(out_dir, "prices.json")
    if not rows and os.path.exists(prices_path):
        write_report(os.path.join(out_dir, "report.md"), report, source, wanted, missing, rows)
        print("לא נמצאו מחירים בהרצה הזו, משאיר את הקובץ הקודם")  # לא דורסים נתונים טובים בריקים
        return 0
    if os.path.exists(prices_path):
        try:
            with open(prices_path, encoding="utf-8") as f:
                rows = carry_over(rows, report, json.load(f), wanted, datetime.date.today())
        except Exception:
            traceback.print_exc()
    write_report(os.path.join(out_dir, "report.md"), report, source, wanted, missing, rows)
    out = {"updated": datetime.date.today().isoformat(), "city": "רמת גן והסביבה",
           "report": [{"chain": CHAIN_NAMES.get(r["chain"], r["chain"]), "status": r["status"], "stores": r["stores"]} for r in report],
           "prices": rows, "candidates": candidates, "missing": missing}
    with open(os.path.join(out_dir, "prices.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)
    return 0


if __name__ == "__main__":
    if len(sys.argv) >= 4 and sys.argv[1] == "--scrape":
        scrape_main(sys.argv[2], sys.argv[3])
    else:
        sys.exit(main())
