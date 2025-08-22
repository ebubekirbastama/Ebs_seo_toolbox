#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SEO Toolbox — GUI + CLI (Modern Metro Style)

Özet
- Modern (Metro tarzı) PySide6 GUI ile hızlı SEO denetimi
- CLI modu korunur: on‑page metrikler, rapor ve sitemap üretimi
- Ekstra SEO kontrolleri: benzersiz title/description, kopya başlıklar, anahtar kelime yoğunluğu,
  ince içerik, eksik alt metin oranı, hreflang/OG/Twitter varlık kontrolü, robots.txt test aracı

Kurulum
  pip install requests beautifulsoup4 lxml tldextract PySide6

GUI Çalıştırma
  python seo_toolbox_gui.py --gui

CLI Örnekleri
  python seo_toolbox_gui.py audit --start https://www.example.com --max-pages 200 \
      --output audit.csv --md-out report.md --sitemap-out sitemap_generated.xml

  python seo_toolbox_gui.py audit --sitemap https://www.example.com/sitemap.xml \
      --output audit.csv
"""

import argparse
import csv
import json
import re
import sys
import time
import tldextract
from collections import deque, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from html import unescape
from typing import Dict, List, Optional, Set, Tuple
from urllib.parse import urljoin, urlparse, urlunparse
from urllib import robotparser

import requests
from bs4 import BeautifulSoup

# GUI gereksinimleri isteğe bağlı
try:
    from PySide6 import QtCore, QtWidgets, QtGui
    PYSIDE_AVAILABLE = True
except Exception:
    PYSIDE_AVAILABLE = False

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0 Safari/537.36 SEO-Toolbox/2.0"
    )
}
TIMEOUT = 15
MAX_WORKERS = 8

RECOMMENDED_TITLE = (50, 60)  # yaklaşık karakter aralığı
RECOMMENDED_DESC = (120, 160)
THIN_WORDS = 300

# ---------------------
# Yardımcılar
# ---------------------

def normalize_url(base: str, href: str) -> Optional[str]:
    if not href:
        return None
    href = href.strip()
    try:
        url = urljoin(base, href)
        parts = urlparse(url)
        if not parts.scheme or not parts.netloc:
            return None
        url = urlunparse((parts.scheme, parts.netloc, parts.path or "/", "", parts.query, ""))
        return url
    except Exception:
        return None


def same_domain(a: str, b: str) -> bool:
    ea = tldextract.extract(a)
    eb = tldextract.extract(b)
    return (ea.domain, ea.suffix) == (eb.domain, eb.suffix)


def fetch(url: str) -> Tuple[requests.Response, List[str], float]:
    session = requests.Session()
    session.max_redirects = 10
    redirects = []
    t0 = time.time()
    try:
        resp = session.get(url, headers=HEADERS, timeout=TIMEOUT, allow_redirects=True)
        for h in resp.history:
            redirects.append(h.url)
        elapsed_ms = int((time.time() - t0) * 1000)
        return resp, redirects, elapsed_ms
    except Exception as e:
        elapsed_ms = int((time.time() - t0) * 1000)
        dummy = requests.Response()
        dummy.status_code = 0
        dummy._content = str(e).encode("utf-8", errors="ignore")
        dummy.url = url
        return dummy, redirects, elapsed_ms


def visible_text(soup: BeautifulSoup) -> str:
    for tag in soup(["script", "style", "noscript", "template", "svg", "meta", "link"]):
        tag.decompose()
    text = soup.get_text(separator=" ")
    text = unescape(text)
    text = re.sub(r"\s+", " ", text)
    return text.strip()


def extract_jsonld_types(soup: BeautifulSoup) -> List[str]:
    types = []
    for s in soup.find_all("script", type=lambda t: t and "ld+json" in t):
        try:
            data = json.loads(s.string or s.text or "{}")
            def collect(d):
                if isinstance(d, dict):
                    t = d.get("@type")
                    if isinstance(t, str):
                        types.append(t)
                    elif isinstance(t, list):
                        types.extend([str(x) for x in t])
                    for v in d.values():
                        collect(v)
                elif isinstance(d, list):
                    for it in d:
                        collect(it)
            collect(data)
        except Exception:
            continue
    uniq = list(dict.fromkeys([t.strip() for t in types if t]))
    return uniq[:10]


def estimate_title_pixels(title: str) -> int:
    if not title:
        return 0
    width = 0
    for ch in title:
        if ch.isupper():
            width += 8
        elif ch in "il":
            width += 4
        elif ch in "MW@#%&":
            width += 10
        else:
            width += 7
    return width


def parse_page(url: str, html: bytes, status: int, elapsed_ms: int, redirects: List[str]) -> Dict:
    soup = BeautifulSoup(html, "lxml")
    title = (soup.title.string.strip() if soup.title and soup.title.string else "")
    meta_desc_tag = soup.find("meta", attrs={"name": re.compile(r"^description$", re.I)})
    meta_desc = meta_desc_tag.get("content", "").strip() if meta_desc_tag else ""
    meta_robots_tag = soup.find("meta", attrs={"name": re.compile(r"^robots$", re.I)})
    meta_robots = meta_robots_tag.get("content", "").strip() if meta_robots_tag else ""

    canonical_tag = soup.find("link", rel=lambda v: v and "canonical" in v)
    canonical = canonical_tag.get("href", "").strip() if canonical_tag else ""
    self_canonical = canonical.lower().rstrip("/") == url.lower().rstrip("/") if canonical else False

    h_counts = {}
    h_texts = {"h1": []}
    for lvl in [1, 2, 3, 4, 5, 6]:
        tags = soup.find_all(f"h{lvl}")
        h_counts[f"h{lvl}"] = len(tags)
        if lvl == 1:
            h_texts["h1"] = [re.sub(r"\s+", " ", t.get_text(strip=True)) for t in tags]

    imgs = soup.find_all("img")
    img_total = len(imgs)
    img_missing_alt = sum(1 for i in imgs if not i.get("alt"))

    links = soup.find_all("a", href=True)
    internal = external = nofollow = 0
    for a in links:
        href = normalize_url(url, a["href"]) or ""
        if not href:
            continue
        if same_domain(url, href):
            internal += 1
        else:
            external += 1
        rel = (a.get("rel") or [])
        if isinstance(rel, list):
            rel = " ".join(rel)
        if "nofollow" in (rel or "").lower():
            nofollow += 1

    og_present = bool(soup.find("meta", property=re.compile(r"^og:", re.I)))
    tw_present = bool(soup.find("meta", attrs={"name": re.compile(r"^twitter:", re.I)}))
    hreflangs = [l.get("href") for l in soup.find_all("link", rel=lambda v: v and "alternate" in v, hreflang=True)]
    jsonld_types = extract_jsonld_types(soup)

    text = visible_text(soup)
    word_count = len(text.split())

    title_px = estimate_title_pixels(title)

    return {
        "url": url,
        "status": status,
        "resp_ms": elapsed_ms,
        "redirects": " -> ".join(redirects) if redirects else "",
        "bytes_kb": round(len(html) / 1024.0, 1),
        "title": title,
        "title_len": len(title),
        "title_px": title_px,
        "title_ok": (RECOMMENDED_TITLE[0] <= len(title) <= RECOMMENDED_TITLE[1]) and (title_px <= 600),
        "meta_desc": meta_desc,
        "meta_desc_len": len(meta_desc),
        "meta_desc_ok": RECOMMENDED_DESC[0] <= len(meta_desc) <= RECOMMENDED_DESC[1],
        "meta_robots": meta_robots,
        "canonical": canonical,
        "self_canonical": self_canonical,
        "h1_count": h_counts.get("h1", 0),
        "h1_texts": " | ".join(h_texts.get("h1", [])[:5]),
        "h2_count": h_counts.get("h2", 0),
        "h3_count": h_counts.get("h3", 0),
        "h4_count": h_counts.get("h4", 0),
        "h5_count": h_counts.get("h5", 0),
        "h6_count": h_counts.get("h6", 0),
        "img_total": img_total,
        "img_missing_alt": img_missing_alt,
        "links_internal": internal,
        "links_external": external,
        "links_nofollow": nofollow,
        "open_graph": og_present,
        "twitter_card": tw_present,
        "hreflang_count": len(hreflangs),
        "jsonld_types": ", ".join(jsonld_types),
        "word_count": word_count,
    }


def load_sitemap(url: str) -> List[str]:
    try:
        r = requests.get(url, headers=HEADERS, timeout=TIMEOUT)
        r.raise_for_status()
        soup = BeautifulSoup(r.content, "xml")
        locs = [loc.get_text(strip=True) for loc in soup.find_all("loc")]
        return list(dict.fromkeys(locs))
    except Exception as e:
        print(f"[!] Sitemap okunamadı: {e}")
        return []


def get_robots_parser(start_url: str) -> robotparser.RobotFileParser:
    parts = urlparse(start_url)
    robots_url = f"{parts.scheme}://{parts.netloc}/robots.txt"
    rp = robotparser.RobotFileParser()
    try:
        rp.set_url(robots_url)
        rp.read()
    except Exception:
        pass
    return rp


def crawl(start: str, max_pages: int, same_site_only: bool = True) -> List[Tuple[str, requests.Response, List[str], int]]:
    visited: Set[str] = set()
    q = deque([start])
    rp = get_robots_parser(start)

    results = []
    while q and len(visited) < max_pages:
        url = q.popleft()
        if url in visited:
            continue
        visited.add(url)

        # robots izin kontrolü
        if not rp.can_fetch(HEADERS["User-Agent"], url):
            continue

        try:
            resp, redirects, elapsed_ms = fetch(url)
            results.append((url, resp, redirects, elapsed_ms))
            if resp.status_code == 200 and resp.headers.get("Content-Type", "").lower().startswith("text/html"):
                soup = BeautifulSoup(resp.content, "lxml")
                for a in soup.find_all("a", href=True):
                    href = normalize_url(url, a["href"]) or ""
                    if not href:
                        continue
                    if same_site_only and not same_domain(start, href):
                        continue
                    if href not in visited and len(visited) + len(q) < max_pages * 2:
                        q.append(href)
        except Exception:
            continue
    return results


# ---------------------
# Raporlama & Ek analizler
# ---------------------

def write_csv(rows: List[Dict], path: str):
    if not rows:
        print("[!] Yazılacak veri yok")
        return
    fieldnames = list(rows[0].keys())
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for r in rows:
            w.writerow(r)


def collect_issues(rows: List[Dict]) -> Dict[str, List[Dict]]:
    title_map = defaultdict(list)
    desc_map = defaultdict(list)
    for r in rows:
        if r.get("title"):
            title_map[r["title"].strip().lower()].append(r)
        if r.get("meta_desc"):
            desc_map[r["meta_desc"].strip().lower()].append(r)

    duplicates_title = [item for key, lst in title_map.items() if len(lst) > 1 for item in lst]
    duplicates_desc = [item for key, lst in desc_map.items() if len(lst) > 1 for item in lst]

    issues = {
        "no_title": [r for r in rows if not r["title"]],
        "long_title": [r for r in rows if r["title_px"] > 600 or r["title_len"] > RECOMMENDED_TITLE[1]],
        "short_title": [r for r in rows if 0 < r["title_len"] < RECOMMENDED_TITLE[0]],
        "duplicate_title": duplicates_title,
        "no_desc": [r for r in rows if not r["meta_desc"]],
        "duplicate_desc": duplicates_desc,
        "no_canonical": [r for r in rows if not r["canonical"]],
        "bad_h1": [r for r in rows if r["h1_count"] != 1],
        "img_alt_missing": [r for r in rows if r["img_missing_alt"] > 0],
        "no_og": [r for r in rows if not r["open_graph"]],
        "no_twitter": [r for r in rows if not r["twitter_card"]],
        "no_jsonld": [r for r in rows if not r["jsonld_types"]],
        "thin_content": [r for r in rows if r["word_count"] < THIN_WORDS],
        "noindex": [r for r in rows if "noindex" in r["meta_robots"].lower()],
        "slow": sorted([r for r in rows if r["resp_ms"] >= 1000], key=lambda x: x["resp_ms"], reverse=True),
    }
    return issues


def write_md_summary(rows: List[Dict], path: str, top_n: int = 20):
    if not rows:
        return
    issues = collect_issues(rows)
    total = len(rows)
    with open(path, "w", encoding="utf-8") as f:
        f.write(f"# SEO Denetim Özeti (Toplam Sayfa: {total})\n\n")
        for key, items in issues.items():
            if not items:
                continue
            label = key.replace("_", " ").title()
            f.write(f"## {label} — {len(items)} sayfa\n\n")
            for r in items[:top_n]:
                f.write(f"- {r['url']}\n")
            if len(items) > top_n:
                f.write(f"\n… ve {len(items) - top_n} daha.\n\n")
        slow = sorted(rows, key=lambda r: r["resp_ms"], reverse=True)[:10]
        f.write("\n## En Yavaş 10 Sayfa (ms)\n\n")
        for r in slow:
            f.write(f"- {r['resp_ms']:>6} ms — {r['url']}\n")


def build_sitemap(urls: List[str]) -> str:
    from datetime import datetime
    now = datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ")
    lines = [
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
        "<urlset xmlns=\"http://www.sitemaps.org/schemas/sitemap/0.9\">",
    ]
    uniq = list(dict.fromkeys(urls))
    for u in uniq:
        lines.append("  <url>")
        lines.append(f"    <loc>{u}</loc>")
        lines.append(f"    <lastmod>{now}</lastmod>")
        lines.append("  </url>")
    lines.append("</urlset>")
    return "\n".join(lines)


def keyword_density(text: str, keyword: str) -> float:
    if not text or not keyword:
        return 0.0
    words = re.findall(r"[\wğüşöçıİĞÜŞÖÇ]+", text.lower())
    if not words:
        return 0.0
    total = len(words)
    k = keyword.lower()
    count = sum(1 for w in words if w == k)
    return (count / max(total, 1)) * 100.0


# ---------------------
# CLI akışı
# ---------------------

def run_audit(start: Optional[str], sitemap: Optional[str], max_pages: int, cross_domain: bool=False) -> Tuple[List[Dict], List[str]]:
    urls_from_sitemap: List[str] = []
    if sitemap:
        urls_from_sitemap = load_sitemap(sitemap)
        if urls_from_sitemap:
            start = urls_from_sitemap[0]
    if not start:
        raise SystemExit("--start veya --sitemap vermelisiniz")

    crawled = []
    if urls_from_sitemap:
        targets = urls_from_sitemap[: max_pages]
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as ex:
            futs = {ex.submit(fetch, u): u for u in targets}
            for fut in as_completed(futs):
                resp, redirects, elapsed_ms = fut.result()
                crawled.append((resp.url, resp, redirects, elapsed_ms))
    else:
        crawled = crawl(start, max_pages, same_site_only=not cross_domain)

    rows: List[Dict] = []
    scanned_urls: List[str] = []
    for url, resp, redirects, elapsed_ms in crawled:
        scanned_urls.append(url)
        status = resp.status_code
        html = resp.content if status == 200 else resp.content or b""
        try:
            row = parse_page(url, html, status, elapsed_ms, redirects)
        except Exception:
            row = {
                "url": url,
                "status": status,
                "resp_ms": elapsed_ms,
                "redirects": " -> ".join(redirects) if redirects else "",
                "bytes_kb": round(len(html) / 1024.0, 1),
                "title": "",
                "title_len": 0,
                "title_px": 0,
                "title_ok": False,
                "meta_desc": "",
                "meta_desc_len": 0,
                "meta_desc_ok": False,
                "meta_robots": "",
                "canonical": "",
                "self_canonical": False,
                "h1_count": 0,
                "h1_texts": "",
                "h2_count": 0,
                "h3_count": 0,
                "h4_count": 0,
                "h5_count": 0,
                "h6_count": 0,
                "img_total": 0,
                "img_missing_alt": 0,
                "links_internal": 0,
                "links_external": 0,
                "links_nofollow": 0,
                "open_graph": False,
                "twitter_card": False,
                "hreflang_count": 0,
                "jsonld_types": "",
                "word_count": 0,
            }
        rows.append(row)
    return rows, scanned_urls


def cmd_audit(args):
    rows, crawled_urls = run_audit(args.start, args.sitemap, args.max_pages, args.cross_domain)
    if args.output:
        write_csv(rows, args.output)
        print(f"[✓] CSV yazıldı: {args.output}")
    if args.md_out:
        write_md_summary(rows, args.md_out)
        print(f"[✓] Markdown rapor yazıldı: {args.md_out}")
    if args.sitemap_out:
        sm = build_sitemap(crawled_urls)
        with open(args.sitemap_out, "w", encoding="utf-8") as f:
            f.write(sm)
        print(f"[✓] sitemap.xml yazıldı: {args.sitemap_out}")


# ---------------------
# GUI (Modern Metro Style)
# ---------------------
if PYSIDE_AVAILABLE:
    class Worker(QtCore.QObject):
        progress = QtCore.Signal(int)
        finished = QtCore.Signal(list, list)
        status = QtCore.Signal(str)

        def __init__(self, start: Optional[str], sitemap: Optional[str], max_pages: int, cross_domain: bool=False):
            super().__init__()
            self.start = start
            self.sitemap = sitemap
            self.max_pages = max_pages
            self.cross_domain = cross_domain

        @QtCore.Slot()
        def run(self):
            try:
                rows, urls = run_audit(self.start, self.sitemap, self.max_pages, self.cross_domain)
                self.finished.emit(rows, urls)
            except SystemExit as e:
                self.status.emit(str(e))
                self.finished.emit([], [])
            except Exception as e:
                self.status.emit(f"Hata: {e}")
                self.finished.emit([], [])

    class MetroButton(QtWidgets.QPushButton):
        def __init__(self, text: str, icon: Optional[QtGui.QIcon]=None):
            super().__init__(text)
            if icon:
                self.setIcon(icon)
            self.setCursor(QtGui.QCursor(QtCore.Qt.PointingHandCursor))
            self.setMinimumHeight(36)
            self.setStyleSheet(
                """
                QPushButton { background: #1f6feb; color: white; border: none; padding: 8px 14px; border-radius: 8px; font-weight:600; }
                QPushButton:hover { background: #266ee6; }
                QPushButton:pressed { background: #1a5ccc; }
                """
            )

    class MetroLineEdit(QtWidgets.QLineEdit):
        def __init__(self, placeholder: str=""):
            super().__init__()
            self.setPlaceholderText(placeholder)
            self.setMinimumHeight(36)
            self.setStyleSheet(
                """
                QLineEdit { padding: 8px 12px; border: 2px solid #2d333b; border-radius: 10px; background: #0d1117; color:#c9d1d9; }
                QLineEdit:focus { border-color: #1f6feb; }
                """
            )

    class MetroSpinBox(QtWidgets.QSpinBox):
        def __init__(self, minimum=1, maximum=10000, value=200):
            super().__init__()
            self.setRange(minimum, maximum)
            self.setValue(value)
            self.setStyleSheet(
                """
                QSpinBox { padding: 6px 10px; border: 2px solid #2d333b; border-radius: 10px; background: #0d1117; color:#c9d1d9; }
                QSpinBox:focus { border-color: #1f6feb; }
                """
            )

    class TagLabel(QtWidgets.QLabel):
        def __init__(self, text: str, color: str="#30363d"):
            super().__init__(text)
            self.setStyleSheet(f"background:{color}; color:#c9d1d9; padding:4px 8px; border-radius:8px;")

    class ResultsTable(QtWidgets.QTableWidget):
        def __init__(self):
            super().__init__(0, 12)
            headers = [
                "URL", "Status", "ms", "KB", "TitleLen", "TitlePx", "H1", "ImgAlt-",
                "Int", "Ext", "OG", "JSON-LD"
            ]
            self.setHorizontalHeaderLabels(headers)
            self.horizontalHeader().setStretchLastSection(True)
            self.setAlternatingRowColors(True)
            self.setStyleSheet(
                """
                QTableWidget { background:#0d1117; color:#c9d1d9; gridline-color:#21262d; }
                QHeaderView::section { background:#161b22; color:#c9d1d9; padding:6px; border:0; }
                QTableWidget::item:selected { background:#1f6feb; color:white; }
                """
            )

        def load(self, rows: List[Dict]):
            self.setRowCount(0)
            for r in rows:
                row = self.rowCount()
                self.insertRow(row)
                vals = [
                    r.get("url", ""), r.get("status", 0), r.get("resp_ms", 0), r.get("bytes_kb", 0.0),
                    r.get("title_len", 0), r.get("title_px", 0), r.get("h1_count", 0), r.get("img_missing_alt", 0),
                    r.get("links_internal", 0), r.get("links_external", 0), "✓" if r.get("open_graph") else "-",
                    r.get("jsonld_types", "-") or "-",
                ]
                for col, v in enumerate(vals):
                    item = QtWidgets.QTableWidgetItem(str(v))
                    if col in (1,2,3,4,5,6,7,8,9):
                        item.setTextAlignment(QtCore.Qt.AlignRight | QtCore.Qt.AlignVCenter)
                    self.setItem(row, col, item)

    class IssuesList(QtWidgets.QListWidget):
        def load(self, issues: Dict[str, List[Dict]]):
            self.clear()
            for k, lst in issues.items():
                if not lst:
                    continue
                self.addItem(f"{k} — {len(lst)}")

    class RobotsTester(QtWidgets.QWidget):
        def __init__(self):
            super().__init__()
            self.urlEdit = MetroLineEdit("Site ana URL (https://…)")
            self.pathEdit = MetroLineEdit("/test/slug")
            self.uaEdit = MetroLineEdit(HEADERS["User-Agent"])
            self.resultLbl = TagLabel("—", "#161b22")
            btn = MetroButton("Kontrol Et")
            btn.clicked.connect(self.check)
            lay = QtWidgets.QFormLayout(self)
            lay.addRow("Site:", self.urlEdit)
            lay.addRow("Path:", self.pathEdit)
            lay.addRow("User‑Agent:", self.uaEdit)
            lay.addRow(btn)
            lay.addRow("Sonuç:", self.resultLbl)

        def check(self):
            base = self.urlEdit.text().strip()
            path = self.pathEdit.text().strip() or "/"
            if not base:
                self.resultLbl.setText("Site boş")
                return
            rp = get_robots_parser(base)
            allowed = rp.can_fetch(self.uaEdit.text().strip() or HEADERS["User-Agent"], urljoin(base, path))
            self.resultLbl.setText("ALLOW" if allowed else "DISALLOW")
            self.resultLbl.setStyleSheet(f"background:{'#238636' if allowed else '#da3633'}; color:white; padding:6px 10px; border-radius:8px;")

    class MainWindow(QtWidgets.QMainWindow):
        def __init__(self):
            super().__init__()
            self.setWindowTitle("SEO Toolbox — GUI")
            self.resize(1200, 720)
            self.setStyleSheet("""
                QMainWindow { background:#0d1117; }
                QLabel { color:#c9d1d9; }
                QTabWidget::pane { border: 1px solid #21262d; border-radius: 10px; }
                QTabBar::tab { background:#161b22; color:#c9d1d9; padding:10px 16px; margin-right:4px; border-top-left-radius:10px; border-top-right-radius:10px; }
                QTabBar::tab:selected { background:#1f6feb; color:white; }
                QProgressBar { border: 1px solid #30363d; border-radius: 8px; text-align: center; color:#c9d1d9; }
                QProgressBar::chunk { background-color: #1f6feb; border-radius: 8px; }
                QCheckBox { color:#c9d1d9; }
            """)

            # Üst panel (ayarlar)
            self.startEdit = MetroLineEdit("Başlangıç URL — https://…")
            self.sitemapEdit = MetroLineEdit("Sitemap URL — https://…/sitemap.xml (opsiyonel)")
            self.maxSpin = MetroSpinBox(1, 20000, 200)
            self.crossDomain = QtWidgets.QCheckBox("Cross‑domain" )
            self.keywordEdit = MetroLineEdit("Anahtar kelime (opsiyonel) — yoğunluk için")

            self.startBtn = MetroButton("Denetimi Başlat")
            self.exportCsvBtn = MetroButton("CSV Dışa Aktar")
            self.exportMdBtn = MetroButton("Markdown Rapor")
            self.exportSmBtn = MetroButton("Sitemap Üret")
            self.statusBar().showMessage("Hazır")

            self.startBtn.clicked.connect(self.start_audit)
            self.exportCsvBtn.clicked.connect(self.export_csv)
            self.exportMdBtn.clicked.connect(self.export_md)
            self.exportSmBtn.clicked.connect(self.export_sitemap)

            top = QtWidgets.QGridLayout()
            top.addWidget(QtWidgets.QLabel("Start URL"), 0, 0)
            top.addWidget(self.startEdit,                    0, 1, 1, 3)
            top.addWidget(QtWidgets.QLabel("Sitemap"),   1, 0)
            top.addWidget(self.sitemapEdit,                 1, 1, 1, 3)
            top.addWidget(QtWidgets.QLabel("Max Pages"), 2, 0)
            top.addWidget(self.maxSpin,                     2, 1)
            top.addWidget(self.crossDomain,                 2, 2)
            top.addWidget(self.keywordEdit,                 2, 3)
            top.addWidget(self.startBtn,                    3, 1)
            top.addWidget(self.exportCsvBtn,                3, 2)
            top.addWidget(self.exportMdBtn,                 3, 3)

            topWrap = QtWidgets.QWidget()
            topWrap.setLayout(top)

            # Orta: Tablar
            self.tabs = QtWidgets.QTabWidget()
            self.table = ResultsTable()
            self.issues = IssuesList()
            self.log = QtWidgets.QPlainTextEdit(); self.log.setReadOnly(True)
            self.progress = QtWidgets.QProgressBar(); self.progress.setRange(0, 0); self.progress.hide()

            resTab = QtWidgets.QWidget(); resLay = QtWidgets.QVBoxLayout(resTab); resLay.addWidget(self.table)
            issTab = QtWidgets.QWidget(); issLay = QtWidgets.QVBoxLayout(issTab); issLay.addWidget(self.issues)
            logTab = QtWidgets.QWidget(); logLay = QtWidgets.QVBoxLayout(logTab); logLay.addWidget(self.log)

            self.tabs.addTab(resTab, "Sonuçlar")
            self.tabs.addTab(issTab, "Sorunlar")
            self.tabs.addTab(logTab, "Log")

            # Alt: robots tester ve sitemap export butonu
            self.robots = RobotsTester()
            bottom = QtWidgets.QHBoxLayout()
            bottom.addWidget(self.robots)
            bottom.addStretch(1)
            bottom.addWidget(self.exportSmBtn)
            bottomWrap = QtWidgets.QWidget(); bottomWrap.setLayout(bottom)

            central = QtWidgets.QVBoxLayout()
            central.addWidget(topWrap)
            central.addWidget(self.tabs)
            central.addWidget(self.progress)
            central.addWidget(bottomWrap)

            w = QtWidgets.QWidget(); w.setLayout(central); self.setCentralWidget(w)

            self.rows: List[Dict] = []
            self.scanned_urls: List[str] = []

        def start_audit(self):
            start = self.startEdit.text().strip() or None
            site = self.sitemapEdit.text().strip() or None
            max_pages = int(self.maxSpin.value())
            cross = bool(self.crossDomain.isChecked())
            self.log.appendPlainText(f"[i] Denetim başlıyor… start={start} sitemap={site} max={max_pages}")
            self.progress.show()

            self.thread = QtCore.QThread()
            self.worker = Worker(start, site, max_pages, cross)
            self.worker.moveToThread(self.thread)
            self.thread.started.connect(self.worker.run)
            self.worker.finished.connect(self.on_finished)
            self.worker.status.connect(lambda s: self.log.appendPlainText(s))
            self.worker.finished.connect(self.thread.quit)
            self.worker.finished.connect(self.worker.deleteLater)
            self.thread.finished.connect(self.thread.deleteLater)
            self.thread.start()

        def on_finished(self, rows: List[Dict], urls: List[str]):
            self.progress.hide()
            self.rows = rows
            self.scanned_urls = urls
            self.table.load(rows)
            iss = collect_issues(rows)
            self.issues.load(iss)
            self.statusBar().showMessage(f"Bitti — {len(rows)} sayfa")
            # Anahtar kelime yoğunluğu (opsiyonel)
            kw = self.keywordEdit.text().strip()
            if kw:
                densities = []
                for r in rows:
                    text = " ".join([r.get("title",""), r.get("meta_desc",""), r.get("h1_texts","")])
                    densities.append(keyword_density(text, kw))
                if densities:
                    avg = sum(densities)/len(densities)
                    self.log.appendPlainText(f"[kw] '{kw}' ort. yoğunluk (title+desc+h1): {avg:.2f}%")

        def export_csv(self):
            if not self.rows:
                self.statusBar().showMessage("Önce tarama yapın")
                return
            path, _ = QtWidgets.QFileDialog.getSaveFileName(self, "CSV kaydet", "audit.csv", "CSV (*.csv)")
            if path:
                write_csv(self.rows, path)
                self.statusBar().showMessage(f"CSV kaydedildi: {path}")

        def export_md(self):
            if not self.rows:
                self.statusBar().showMessage("Önce tarama yapın")
                return
            path, _ = QtWidgets.QFileDialog.getSaveFileName(self, "Markdown kaydet", "report.md", "Markdown (*.md)")
            if path:
                write_md_summary(self.rows, path)
                self.statusBar().showMessage(f"Rapor kaydedildi: {path}")

        def export_sitemap(self):
            if not self.scanned_urls:
                self.statusBar().showMessage("Önce tarama yapın")
                return
            path, _ = QtWidgets.QFileDialog.getSaveFileName(self, "sitemap.xml kaydet", "sitemap.xml", "XML (*.xml)")
            if path:
                sm = build_sitemap(self.scanned_urls)
                with open(path, "w", encoding="utf-8") as f:
                    f.write(sm)
                self.statusBar().showMessage(f"Sitemap yazıldı: {path}")


# ---------------------
# main
# ---------------------

def main():
    p = argparse.ArgumentParser(description="SEO Toolbox — GUI + CLI on‑page denetim")
    p.add_argument("--gui", action="store_true", help="GUI'yi başlat")

    sub = p.add_subparsers(dest="cmd")
    a = sub.add_parser("audit", help="Siteyi tara ve SEO metriklerini CSV olarak çıkar")
    a.add_argument("--start", help="Başlangıç URL'i (https://...)")
    a.add_argument("--sitemap", help="Sitemap URL'i (https://.../sitemap.xml)")
    a.add_argument("--max-pages", type=int, default=200, help="Maksimum sayfa sayısı")
    a.add_argument("--cross-domain", action="store_true", help="Aynı domain kısıtını kaldır (önerilmez)")
    a.add_argument("--output", default="audit.csv", help="CSV çıktı yolu")
    a.add_argument("--md-out", default=None, help="Özet Markdown rapor yolu")
    a.add_argument("--sitemap-out", default=None, help="Taranan URL'lerden sitemap üret ve kaydet")
    a.set_defaults(func=cmd_audit)

    args = p.parse_args()

    if args.gui:
        if not PYSIDE_AVAILABLE:
            print("PySide6 kurulu değil. 'pip install PySide6' ile kurun.")
            sys.exit(2)
        app = QtWidgets.QApplication(sys.argv)
        app.setWindowIcon(QtGui.QIcon())
        win = MainWindow()
        win.show()
        sys.exit(app.exec())

    if not args.cmd:
        p.print_help()
        sys.exit(1)
    args.func(args)


if __name__ == "__main__":
    main()
