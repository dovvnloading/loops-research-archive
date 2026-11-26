"""Lock versioned primary PDFs, locate source statements, and update NOTE.
Requires pypdf==5.9.0. PDF physical page numbers are one-based.
No downloaded PDFs or full copyrighted source text are committed.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import time
import unicodedata
from urllib.request import Request, urlopen
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parent
SOURCES = {
    "Dudko": ("2512.24171v1", {
        "Problem 4.4": ["interpolationproblem44developavirtualmoleculeversionofthenear degenerateregime"],
        "Section 4.5": ["45virtualnearmoleculerenormalization"],
    }),
    "DLS": ("1703.01206v3", {
        "Theorem 1.1": ["theorem11hyperbolicity"],
        "Theorem 3.16": ["theorem316analyticoperator"],
        "Lemma 3.18": ["lemma318let"],
        "Remark 3.19": ["remark319"],
        "Theorem 7.7": ["theorem77hyperbolicity", "theorem77therenormalization"],
        "C.3 Molecule Conjecture": ["c3themoleculeconjecture"],
        "C.4 following heading": ["c4conjectureontheuppersemicontinuity"],
    }),
    "DL": ("1808.10425v4", {
        "Lemma 3.1 / multiplier derivative": ["lemma31"],
        "Proposition 5.41": ["proposition541thepacmanrenormalizationoperator"],
    }),
}

def norm(text):
    return "".join(c for c in unicodedata.normalize("NFKC",text).lower() if c.isalnum())

def download(url):
    urls=[url,url.replace("https://arxiv.org/","https://export.arxiv.org/"),url]
    for i,endpoint in enumerate(urls):
        try:
            req=Request(endpoint,headers={"User-Agent":"research-source-lock/1.0 (versioned arXiv citations)"})
            with urlopen(req,timeout=55) as f:
                data=f.read(30_000_001)
            if not data.startswith(b"%PDF-") or len(data)>30_000_000:
                raise ValueError("response not a PDF of allowed size")
            return data, endpoint
        except Exception:
            if i==len(urls)-1:
                raise
            time.sleep(3)

def locate(pages, alternatives):
    # Include two-page windows in case the anchor crosses a page break.
    keys=[norm(x) for x in alternatives]
    direct=[i+1 for i,s in enumerate(pages) if any(k in s for k in keys)]
    if direct:
        return direct
    return [i+1 for i in range(len(pages)-1)
            if any(k in pages[i]+pages[i+1] for k in keys)]

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--update-note",action="store_true")
    ap.add_argument("--show-statements",action="store_true",
                    help="Print original PDF page text locally; not included in generated files")
    ap.add_argument("--pdf-dir",type=Path,
                    help="Optional directory with exact versioned PDFs named <arXiv-id>vN.pdf")
    args=ap.parse_args()
    out={"schema":1,"page_numbering":"one-based physical PDF pages; candidate anchors, not verified printed labels","sources":{}}
    missing=[]
    for name,(version,anchors) in SOURCES.items():
        url="https://arxiv.org/pdf/"+version
        try:
            data,download_url=((args.pdf_dir/(version+".pdf")).read_bytes(),url) if args.pdf_dir else download(url)
        except Exception as exc:
            missing.append(name+": PDF download")
            out["sources"][name]={"version":version,"url":url,"error":type(exc).__name__+": "+str(exc)}
            continue
        fingerprint={"version":version,"url":url,"download_url":download_url,"sha256":hashlib.sha256(data).hexdigest(),"bytes":len(data)}
        try:
            reader=PdfReader(io.BytesIO(data))
            raw=[page.extract_text() or "" for page in reader.pages]
        except Exception as exc:
            missing.append(name+": PDF text extraction")
            out["sources"][name]={**fingerprint,"error":type(exc).__name__+": "+str(exc)}
            continue
        pages=[norm(x) for x in raw]
        refs={label:locate(pages,alts) for label,alts in anchors.items()}
        # Resolve TOC headings by requiring statement text on same or next page.
        if name=="DLS":
            for label,needle in [
                ("C.3 Molecule Conjecture","givenarenormalizationoperator"),
                ("C.4 following heading","acloselyrelatedconjecture")]:
                candidates=refs[label]
                filtered=[i for i in candidates if needle in "".join(pages[i-1:i+1])]
                if filtered:
                    refs[label]=filtered
            if refs["C.3 Molecule Conjecture"] and refs["C.4 following heading"]:
                start=refs["C.3 Molecule Conjecture"][-1]
                end=refs["C.4 following heading"][-1]
                if start<=end:
                    refs["C.3 statement page range"]=list(range(start,max(start+1,end)))  # v3 C.4 begins on next page
        if name=="DL":
            candidates=refs["Lemma 3.1 / multiplier derivative"]
            filtered=[i for i in candidates if "unstableeigenvalue" in "".join(pages[i-1:i+1])]
            if filtered:
                refs["Lemma 3.1 / multiplier derivative"]=filtered
        if args.show_statements:
            labels={"Dudko":"Problem 4.4","DLS":"C.3 statement page range"}
            if name in labels:
                for i in refs.get(labels[name],[]):
                    print(f"--- {name} {version} PDF page {i} ---")
                    print(raw[i-1])
        for label,found in refs.items():
            if not found:
                missing.append(name+": "+label)
        out["sources"][name]={**fingerprint,"pdf_pages":len(raw),"anchor_pages":refs}
    out["missing_anchors"]=missing
    (ROOT/"sources.json").write_text(json.dumps(out,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    if args.update_note:
        rows=["<!-- SOURCE LOCK BEGIN -->",
              "Generated by source_lock.py. Physical PDF pages are one-based. "
              "Anchor matches are locators, not independent theorem verification.",""]
        for name,entry in out["sources"].items():
            if "sha256" not in entry:
                rows.append(f"- **{name} {entry['version']}**: download failed; SHA-256 unavailable. {entry.get('error','')}")
                continue
            rows.append(f"- **{name} {entry['version']}**: SHA-256 `{entry['sha256']}` ({entry['bytes']} bytes); "
                        f"[PDF]({entry['url']}).")
            for label,found in entry.get("anchor_pages",{}).items():
                links=", ".join(f"[{i}]({entry['url']}#page={i})" for i in found) or "NOT LOCATED"
                rows.append(f"  - {label}: {links}.")
        if missing:
            rows.append("\nUnresolved anchors: "+", ".join(missing)+".")
        rows.append("<!-- SOURCE LOCK END -->")
        note=ROOT/"NOTE.md"
        before=note.read_text(encoding="utf-8")
        after,n=re.subn(r"<!-- SOURCE LOCK BEGIN -->.*?<!-- SOURCE LOCK END -->",
                        lambda _: "\n".join(rows),before,flags=re.S)
        if n!=1:
            raise ValueError("NOTE must contain exactly one source-lock block")
        note.write_text(after,encoding="utf-8")
    print(json.dumps(out,indent=2,sort_keys=True))
    if missing:
        raise SystemExit("Source locator incomplete: "+", ".join(missing))

if __name__=="__main__":
    main()
