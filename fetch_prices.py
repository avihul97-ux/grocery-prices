#!/usr/bin/env python3
"""
מושך מחירי סופרים בבית שמש מקבצי "שקיפות המחירים" של הרשתות,
ומתאים אותם למוצרים שהמשפחה קונה. התוצאה: prices.json (קטן) ו-report.md (דוח מה עבד).

מריצים אוטומטית ב-GitHub Actions (ראו prices.yml). אין צורך לערוך כאן כלום:
את רשימת המוצרים הבוט שולח לבד (WANTED_URL), ואת הרשתות אפשר לשנות במשתנה CHAINS.
"""
import datetime
import gzip
import io
import json
import os
import re
import subprocess
import sys
import tempfile
import traceback
import urllib.request
import xml.etree.ElementTree as ET
import zipfile
from concurrent.futures import ThreadPoolExecutor

DEFAULT_CHAINS = ("SHUFERSAL,RAMI_LEVY,VICTORY_NEW_SOURCE,OSHER_AD,YOHANANOF,"
                  "YAYNO_BITAN_AND_CARREFOUR,HAZI_HINAM,TIV_TAAM,KESHET,MAHSANI_ASHUK_NEW_SOURCE")
CITY_WORDS = ["בית שמש", "ביתשמש", "beit shemesh", "bet shemesh", "beth shemesh"]

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
    if len(w) > 4 and (w.endswith("ות") or w.endswith("ים")):
        return w[:-2]
    if len(w) > 3 and w.endswith("ה"):
        return w[:-1]
    return w


def tok_eq(q, p):
    sq, sp = stem(q), stem(p)
    return sq == sp or (len(sq) >= 4 and sp.startswith(sq))


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
def city_stores(files):
    """מחזיר {מספר סניף: שם} לסניפים שבעיר, ודוגמאות לדוח."""
    found, sample = {}, []
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
            if any(norm(w) in blob for w in CITY_WORDS):
                found[int(sid)] = r.get("storename") or r.get("address") or ("סניף " + sid)
    return found, sample


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
def collect(path, chain, store_name, queries, found):
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
            if not name_matches(qtoks, ptoks):
                continue
            weighted = r.get("bisweighted", "0").strip() in ("1", "true", "True")
            c = found.setdefault(q, {}).setdefault(code, {"name": name, "weighted": weighted, "chains": {}, "stores": set()})
            c["stores"].add((chain, store_name))
            unit = to_float(r.get("unitofmeasureprice")) or price
            cur = c["chains"].get(chain)
            if cur is None or price < cur["price"]:
                c["chains"][chain] = {"price": price, "unit": unit, "store": store_name, "name": name}
            n += 1
    return n


def rank(q_toks, code, info):
    ptoks = tokens(info["name"])
    head = 1 if ptoks and tok_eq(q_toks[0], ptoks[0]) else 0
    return (head, len(info["chains"]), len(info["stores"]), -len(ptoks))


def build_rows(queries, found, pinned):
    rows, candidates, missing = [], {}, []
    for q, qtoks in queries.items():
        cands = found.get(q)
        if not cands:
            missing.append(q)
            continue
        ranked = sorted(cands.items(), key=lambda kv: rank(qtoks, kv[0], kv[1]), reverse=True)
        candidates[q] = [{"barcode": c, "name": i["name"], "chains": sorted(i["chains"]),
                          "min_price": min(v["price"] for v in i["chains"].values())} for c, i in ranked[:6]]
        code = pinned.get(q) if pinned.get(q) in cands else ranked[0][0]
        info = cands[code]
        if info["weighted"] and code not in pinned.values():
            # פירות וירקות במשקל: הקוד שונה בין רשתות, לכן בוחרים בכל רשת בנפרד את המוצר הכי "פשוט"
            per_chain = {}
            for c2, i2 in cands.items():
                if not i2["weighted"]:
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
    items, pinned, source = [], {}, "ברירת מחדל (WANTED_URL לא הוגדר)"
    if url:
        try:
            with urllib.request.urlopen(url, timeout=60) as resp:
                j = json.loads(resp.read().decode("utf-8"))
            items = [str(x).strip() for x in j.get("items", []) if str(x).strip()]
            pinned = {str(k): str(v) for k, v in (j.get("pinned") or {}).items() if v}
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
    return out[:80], pinned, source


def merge(found, part):
    for q, cands in part.items():
        for code, info in cands.items():
            dst = found.setdefault(q, {}).setdefault(code, {"name": info["name"], "weighted": info["weighted"], "chains": {}, "stores": set()})
            dst["chains"].update(info["chains"])
            dst["stores"] |= info["stores"]


def work_chain(chain, queries, downloader, base_dir):
    line = {"chain": chain, "status": "", "stores": 0, "matched": 0}
    found = {}
    wd = os.path.join(base_dir, chain)
    try:
        ok, msg = downloader(chain, r"(?i)stores", wd)
        store_files = list_files(wd, "stores")
        if not store_files:
            line["status"] = "לא ירדו קבצי סניפים (%s)" % (msg or "אין פרטים")
            return line, found
        stores, sample = city_stores(store_files)
        if not stores:
            line["status"] = "אין סניפים בבית שמש בקבצים. דוגמאות: " + "; ".join(sample)
            return line, found
        ids = "|".join(str(i) for i in sorted(stores))
        ok, msg = downloader(chain, r"(?i)pricefull.*-0*(?:%s)-\d{8,}" % ids, wd)
        files = newest_per_store(list_files(wd, "pricefull"))
        if not files:
            line["status"] = "יש %d סניפים בעיר, אבל לא ירדו קבצי מחירים (%s)" % (len(stores), msg or "אין פרטים")
            return line, found
        line["stores"] = len(files)
        for sid, path in files.items():
            line["matched"] += collect(path, chain, stores.get(sid, "סניף %d" % sid), queries, found)
        line["status"] = "תקין"
    except Exception as e:  # רשת אחת שנכשלה לא מפילה את השאר
        line["status"] = "שגיאה: %s" % e
        traceback.print_exc()
    return line, found


def run(chains, wanted, pinned, downloader, base_dir):
    queries = {q: tokens(q) for q in wanted if tokens(q)}
    results = {}
    with ThreadPoolExecutor(max_workers=4) as ex:
        futs = {c: ex.submit(work_chain, c, queries, downloader, base_dir) for c in chains}
        for c, f in futs.items():
            results[c] = f.result()
    found, report = {}, []
    for c in chains:          # מיזוג בסדר קבוע, כדי שהתוצאה תהיה זהה בכל הרצה
        line, part = results[c]
        report.append(line)
        merge(found, part)
    rows, candidates, missing = build_rows(queries, found, pinned)
    return rows, candidates, missing, report


def write_report(path, report, wanted_source, wanted, missing, rows):
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
    lines = ["# דוח מחירים", "", "הרצה: %s" % now, "מקור רשימת המוצרים: %s" % wanted_source, "",
             "| רשת | סטטוס | סניפים בבית שמש | מוצרים שנמצאו |", "|---|---|---|---|"]
    for r in report:
        lines.append("| %s | %s | %s | %s |" % (CHAIN_NAMES.get(r["chain"], r["chain"]), r["status"], r["stores"], r["matched"]))
    chains_ok = sorted({x["chain"] for x in rows})
    lines += ["", "רשתות עם מחירים: %s" % (", ".join(chains_ok) or "אין"),
              "מוצרים שלא נמצאו באף רשת: %s" % (", ".join(missing) or "אין"),
              "סה\"כ שורות מחיר: %d" % len(rows)]
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


def main(downloader=default_downloader, out_dir="."):
    chains = [c.strip() for c in (os.environ.get("CHAINS") or DEFAULT_CHAINS).split(",") if c.strip()]
    wanted, pinned, source = fetch_wanted()
    base = tempfile.mkdtemp(prefix="prices_")
    rows, candidates, missing, report = run(chains, wanted, pinned, downloader, base)
    write_report(os.path.join(out_dir, "report.md"), report, source, wanted, missing, rows)
    if not rows and os.path.exists(os.path.join(out_dir, "prices.json")):
        print("לא נמצאו מחירים בהרצה הזו, משאיר את הקובץ הקודם")  # לא דורסים נתונים טובים בריקים
        return 0
    out = {"updated": datetime.date.today().isoformat(), "city": "בית שמש",
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
