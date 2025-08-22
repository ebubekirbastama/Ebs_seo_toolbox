#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SEO Toolbox — Hızlı On‑Page SEO Denetimi ve Basit Site Haritası Üretici

Ne yapar?
- Bir başlangıç URL'inden (veya bir sitemap.xml'den) sayfaları tarar
- robots.txt kurallarına uyar, sadece aynı etki alanını (domain) gezer
- Her sayfa için şu metrikleri çıkarır:
  * HTTP durum kodu, yönlendirme zinciri, yanıt süresi (ms), içerik boyutu (KB)
  * Title ve uzunluğu; meta description ve uzunluğu; meta robots (index/nofollow)
  * Canonical, self‑canonical kontrolü
  * H1 sayısı ve H1 metinleri; H2‑H6 adetleri
  * Görseller: toplam ve alt (alt) metni eksik görsel sayısı
  * İç link / dış link sayıları; nofollow link sayısı
  * Open Graph, Twitter Card, hreflang varlığı
  * JSON‑LD yapılandırılmış veri tipleri (Article, Product, Organization vb.)
  * Sayfa görünen metin kelime sayısı
- Sonuçları CSV olarak kaydeder; özet bir Markdown raporu oluşturur
- İsterseniz taranan URL’lerden sitemap.xml üretir

Kullanım örnekleri:
  python ebs_seo_toolbox.py audit --start https://www.beykozunsesi.com --max-pages 200 \
      --output audit.csv --md-out report.md --sitemap-out sitemap_generated.xml

  python ebs_seo_toolbox.py audit --sitemap https://www.beykozunsesi.com/sitemap.xml --output audit.csv

Gereksinimler (pip):
  pip install requests beautifulsoup4 lxml tldextract

Notlar:
- Bu araç Core Web Vitals ölçmez; ancak yanıt süresi gibi basit göstergeler sağlar.
- Çok büyük sitelerde --max-pages ile sınırlandırmanız önerilir.
"""

import argparse
import csv
import json
import re
import sys
import time
import tldextract
from collections import deque, Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from html import unescape
from io import BytesIO
from typing import Dict, List, Optional, Set, Tuple
from urllib.parse import urljoin, urlparse, urlunparse
from urllib import robotparser

import requests
from bs4 import BeautifulSoup

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0 Safari/537.36 SEO-Toolbox/1.0"
    )
}
TIMEOUT = 15
MAX_WORKERS = 8

RECOMMENDED_TITLE = (50, 60)  # yaklaşık karakter aralığı
RECOMMENDED_DESC = (120, 160)


def normalize_url(base: str, href: str) -> Optional[str]:
    if not href:
        return None
    href = href.strip()
    try:
        url = urljoin(base, href)
        parts = urlparse(url)
        if not parts.scheme or not parts.netloc:
            return None
        # Fragmanları sil
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
    # temizle ve kısalt
    uniq = list(dict.fromkeys([t.strip() for t in types if t]))
    return uniq[:10]


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
    domain = urlparse(url).netloc
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

    return {
        "url": url,
        "status": status,
        "resp_ms": elapsed_ms,
        "redirects": " -> ".join(redirects) if redirects else "",
        "bytes_kb": round(len(html) / 1024.0, 1),
        "title": title,
        "title_len": len(title),
        "title_ok": RECOMMENDED_TITLE[0] <= len(title) <= RECOMMENDED_TITLE[1],
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


def crawl(start: str, max_pages: int, same_site_only: bool = True) -> List[str]:
    visited: Set[str] = set()
    q = deque([start])
    base_host = urlparse(start).netloc
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


def write_md_summary(rows: List[Dict], path: str, top_n: int = 20):
    if not rows:
        return
    issues = {
        "no_title": [r for r in rows if not r["title"]],
        "long_title": [r for r in rows if r["title_len"] > RECOMMENDED_TITLE[1]],
        "short_title": [r for r in rows if 0 < r["title_len"] < RECOMMENDED_TITLE[0]],
        "no_desc": [r for r in rows if not r["meta_desc"]],
        "no_canonical": [r for r in rows if not r["canonical"]],
        "bad_h1": [r for r in rows if r["h1_count"] != 1],
        "img_alt_missing": [r for r in rows if r["img_missing_alt"] > 0],
        "no_og": [r for r in rows if not r["open_graph"]],
        "no_twitter": [r for r in rows if not r["twitter_card"]],
        "no_jsonld": [r for r in rows if not r["jsonld_types"]],
        "thin_content": [r for r in rows if r["word_count"] < 300],
        "noindex": [r for r in rows if "noindex" in r["meta_robots"].lower()],
    }
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
        # En yavaş ilk 10
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


def cmd_audit(args):
    start = args.start
    urls_from_sitemap: List[str] = []
    if args.sitemap:
        urls_from_sitemap = load_sitemap(args.sitemap)
        if urls_from_sitemap:
            start = urls_from_sitemap[0]
    if not start:
        print("--start veya --sitemap vermelisiniz", file=sys.stderr)
        sys.exit(2)

    print(f"[i] Taranıyor: {start}")

    crawled = []
    if urls_from_sitemap:
        print(f"[i] Sitemap'ten {len(urls_from_sitemap)} URL bulundu")
        # Sitemap URL'lerini GET edip parse edelim (max_pages sınırla)
        targets = urls_from_sitemap[: args.max_pages]
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as ex:
            futs = {ex.submit(fetch, u): u for u in targets}
            for fut in as_completed(futs):
                resp, redirects, elapsed_ms = fut.result()
                crawled.append((resp.url, resp, redirects, elapsed_ms))
    else:
        crawled = crawl(start, args.max_pages, same_site_only=not args.cross_domain)

    rows: List[Dict] = []
    for url, resp, redirects, elapsed_ms in crawled:
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

    if args.output:
        write_csv(rows, args.output)
        print(f"[✓] CSV yazıldı: {args.output}")
    if args.md_out:
        write_md_summary(rows, args.md_out)
        print(f"[✓] Markdown rapor yazıldı: {args.md_out}")
    if args.sitemap_out:
        sm = build_sitemap([r[0] for r in crawled])
        with open(args.sitemap_out, "w", encoding="utf-8") as f:
            f.write(sm)
        print(f"[✓] sitemap.xml yazıldı: {args.sitemap_out}")


def main():
    p = argparse.ArgumentParser(description="SEO Toolbox — On‑Page denetim ve sitemap üretici")
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
    if not args.cmd:
        p.print_help()
        sys.exit(1)
    args.func(args)


if __name__ == "__main__":
    main()
