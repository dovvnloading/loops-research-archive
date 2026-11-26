"""Exact scalar sensitivity and source audit; never an EE configuration."""
import argparse
import hashlib
import io
import json
from fractions import Fraction as Q
from pathlib import Path
import re
import time
import unicodedata
from urllib.request import Request, urlopen

HERE = Path(__file__).resolve().parent

def sensitivity():
    cases = 0
    for m in range(5, 130, 2):
        for i in range(101):
            t = Q(i, 100)
            # Normalize the two loss bounds by M*W0/4.
            vals = [max(t-r, t-4*(1-r)) for r in (Q(j,100) for j in range(50,101))]
            assert min(vals) == t-Q(4,5)
            assert (min(vals) > 0) == (t > Q(4,5))
            assert max(t-Q(4,5), t-4*(1-Q(4,5))) == t-Q(4,5)
            # A single packet is at best t=1/M in this accounting.
            assert max(Q(1,m)-Q(4,5), Q(1,m)-4*(1-Q(4,5))) < 0
            cases += 1
    # Explicit strict margin after replacing M with M-k and epsilon.
    for n in range(10,100):
        m=2*n+1
        for k in range(0,5):
            t=(1-Q(k,m))*(1-Q(1,20))
            if t>Q(4,5):
                a=((1-t)+t/4)/2
                assert 1-t < a < t/4
                assert min(t-1+a,t-4*a)>0
    print(json.dumps({"status":"PASS","scalar_cases":cases,"threshold":"4/5","scope":"conditional accounting only"}),flush=True)

def fetch(url):
    for i in range(3):
        try:
            with urlopen(Request(url,headers={"User-Agent":"loops-research-archive source audit/1.0"}),timeout=45) as f:
                data=f.read()
            assert data.startswith(b"%PDF-"), url
            return data
        except Exception:
            if i==2:
                raise
            time.sleep(2*(i+1))

def provenance():
    from pypdf import PdfReader
    locks=json.loads((HERE/"sources.lock.json").read_text())
    for name, rec in locks.items():
        data=fetch(rec["url"])
        sha=hashlib.sha256(data).hexdigest()
        print(f"SOURCE {name} sha256={sha} bytes={len(data)}",flush=True)
        assert isinstance(rec["sha256"], str) and len(rec["sha256"]) == 64, name
        assert isinstance(rec["bytes"], int) and rec["bytes"] > 0, name
        assert sha == rec["sha256"], name
        assert len(data) == rec["bytes"], name
        pdf=PdfReader(io.BytesIO(data))
        for page, marker in rec["locators"]:
            s=re.sub(r"\s+","",unicodedata.normalize("NFKC",pdf.pages[page-1].extract_text()))
            assert marker in s, (name,page,marker)
    print("PASS: source bytes and page locators, not proof verification",flush=True)

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--offline",action="store_true")
    args=ap.parse_args()
    sensitivity()
    if not args.offline:
        provenance()
