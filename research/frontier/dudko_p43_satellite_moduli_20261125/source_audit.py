"""Fetch versioned inputs, hash original bytes, locate pages; never commit PDFs."""
import argparse
import hashlib
import io
import json
import re
import time
import unicodedata
import urllib.request
from pathlib import Path
from pypdf import PdfReader

SOURCES = [
    ("Dudko survey", "arXiv:2512.24171v1",
     "https://arxiv.org/pdf/2512.24171v1", {
         "Problem 4.3": r"Establish\s*pseudo[\s\-–]*Siegel\s*a\s*priori\s*bounds\s*in\s*the\s*remaining\s*unbounded\s*satellite\s*ql\s*cases",
         "Problem 4.4": r"Develop\s*a\s*Virtual\s*Molecule\s*version\s*of\s*the\s*Near[\s\-–]*Degenerate\s*Regime",
         "section 4.5 start": r"4\s*\.\s*5\s*\.?\s*Virtual\s+near[\s\-–]*Molecule\s+Renormalization",
         "section 4.5 end": r"develop\s*such\s*control\s*a\s*priori",
         "Theorem 4.2": r"Theorem\s*4\s*\.\s*2",
     }),
    ("Dudko–Lyubich", "arXiv:2210.09280v2",
     "https://arxiv.org/pdf/2210.09280v2", {
         "Uniform Bounds Theorem 1.1": r"Uniform\s+Bounds\s+Theorem\s*1\s*\.\s*1",
         "Mother Hedgehog Theorem 1.2": r"Mother\s+Hedgehog\s+Theorem\s*1\s*\.\s*2",
         "Quasidisk Approximation Theorem 1.3": r"Quasidisk\s+Approximation\s+Theorem\s*1\s*\.\s*3",
     }),
    ("BLOT", "CMP 406:141 (2025), version of record",
     "https://publications.hse.ru/pubs/share/direct/1052158150.pdf", {
         "Main Theorem": r"Main\s+Theorem\s*\.\s*Let",
         "Definition 2.3": r"Definition\s*2\s*\.\s*3",
         "Definition 2.4": r"Definition\s*2\s*\.\s*4",
     }),
    ("Kahn–Lyubich", "arXiv:2601.21905v1",
     "https://arxiv.org/pdf/2601.21905v1", {
         "section 4.0.1": r"4\s*\.\s*0\s*\.\s*1\s*\.?\s*Description\s+of\s+the\s+combinatorics",
         "Theorem 7.1": r"Theorem\s*7\s*\.\s*1\s*\.\s*For",
         "section 8": r"8\s*\.\s*Local\s+connectivity",
     }),
]


def fetch(url):
    for attempt in range(2):
        try:
            req = urllib.request.Request(url, headers={"User-Agent":"P43-source-audit/1.0"})
            with urllib.request.urlopen(req, timeout=35) as stream:
                data = stream.read(64*1024*1024+1)
            if not data.startswith(b"%PDF-") or len(data)>64*1024*1024:
                raise ValueError("not a PDF or exceeds 64 MiB")
            return data
        except Exception:
            if attempt:
                raise
            time.sleep(3)


def normalized(s):
    # PDF extraction can join italic words (notably "control a priori")
    # or insert layout hyphenation at a line break. Keep the same words;
    # only normalize typography, never substitute a different marker.
    s = unicodedata.normalize("NFKC", s).replace("\u00ad", "")
    s = re.sub(r"(?<=\w)[\-\u2010][ \t]*\r?\n[ \t]*(?=\w)", "", s)
    return re.sub(r"\s+", " ", s).strip()


def audit():
    records=[]
    for name, version, url, markers in SOURCES:
        rec={"name":name,"version":version,"url":url,"sha256":None,"pages":{},"status":"unverified"}
        try:
            data=fetch(url)
            rec["sha256"]=hashlib.sha256(data).hexdigest()
            rec["bytes"]=len(data)
            pdf=PdfReader(io.BytesIO(data))
            rec["pdf_page_count"]=len(pdf.pages)
            pages=[normalized(p.extract_text() or "") for p in pdf.pages]
            for label, pattern in markers.items():
                rec["pages"][label]=[i+1 for i,p in enumerate(pages) if re.search(pattern,p,re.I)]
            # Detect a marker split across a page break; record both pages
            # only if no within-page match was found.
            for label, pattern in markers.items():
                if not rec["pages"][label]:
                    for i in range(len(pages)-1):
                        if re.search(pattern,pages[i][-600:]+" "+pages[i+1][:600],re.I):
                            rec["pages"][label].extend([i+1,i+2])
            if name == "Dudko survey":
                start = rec["pages"]["section 4.5 start"]
                end = rec["pages"]["section 4.5 end"]
                if start and end and not any(a <= b for a in start for b in end):
                    raise ValueError("section 4.5 end precedes start")
            missing=[k for k,v in rec["pages"].items() if not v]
            rec["status"]="ok" if not missing else "marker_missing"
            if missing:
                rec["missing_markers"]=missing
        except Exception as e:
            rec["status"]="error"
            rec["error"]=f"{type(e).__name__}: {e}"
        records.append(rec)
    return {"schema":1,"page_convention":"1-based PDF physical pages; marker occurrences, not inferred printed numbers",
            "sources":records,"all_verified":all(r["status"]=="ok" for r in records)}


def update_note(path,data):
    start="<!-- SOURCE_AUDIT_BEGIN -->"
    end="<!-- SOURCE_AUDIT_END -->"
    lines=["Source audit (downloaded bytes; page numbers are 1-based PDF pages).",
           "", "| Input/version | SHA-256 | Page markers (all matches) | Status |",
           "|---|---|---|---|"]
    for r in data["sources"]:
        loc="; ".join(f"{k}: {', '.join(map(str,v)) if v else 'not found'}" for k,v in r["pages"].items())
        lines.append(f"| [{r['name']} {r['version']}]({r['url']}) | {r['sha256'] or 'unavailable'} | {loc or 'unavailable'} | {r['status']} |")
    lines.extend(["", "See sources.json for byte counts, extraction errors, and all marker locations. Multiple page matches may include cross-references; review the source itself. SHA-256 records the fetched bytes, not an independent author signature."])
    text=path.read_text(encoding="utf-8")
    before,rest=text.split(start,1)
    _,after=rest.split(end,1)
    path.write_text(before+start+"\n"+"\n".join(lines)+"\n"+end+after,encoding="utf-8")


if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--output",type=Path,default=Path("sources.json"))
    ap.add_argument("--update-note",type=Path)
    args=ap.parse_args()
    data=audit()
    args.output.write_text(json.dumps(data,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    if args.update_note:
        update_note(args.update_note,data)
    print(json.dumps(data, indent=2, sort_keys=True))
    raise SystemExit(0 if data["all_verified"] else 1)
