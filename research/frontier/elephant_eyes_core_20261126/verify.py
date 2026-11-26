"""Source provenance and exact scalar diagnostics, NOT a dynamical model."""
import argparse
from collections import Counter
from fractions import Fraction as Q
import hashlib
import io
import json
from pathlib import Path
import re
import time
import unicodedata
from urllib.request import Request, urlopen

HERE = Path(__file__).resolve().parent

def arithmetic():
    eps = Q(1, 10)
    cases = 0
    for n in range(2, 65):
        m = 2*n + 1
        for w0 in (Q(1), Q(100), Q(10**9)):
            source = [w0/2, w0/2]
            target = {0: w0/2}
            destinations = [0, 0]
            assert max(Counter(destinations).values()) <= 2
            assert all(target[t] >= w for t, w in zip(destinations, source))
            event_rows = [target[0]] + [Q(0)]*(m-1)
            assert sum(event_rows) >= sum(source)/2
            assert sum(event_rows) < m*(1-eps)*w0/2
            # Conditional tagged-packet interface: M packets, distinct events.
            mass = (1-eps)*w0
            targets = {i: mass/2 for i in range(m)}
            tagged = [(i, mass/2) for i in range(m) for _ in range(2)]
            assert max(Counter(i for i, _ in tagged).values()) <= 2
            assert all(targets[i] >= weight for i, weight in tagged)
            assert sum(targets.values()) == m*(1-eps)*w0/2
            # Equations (7.3), (7.6) without additive error.
            w1 = w0/2
            nu = sum(targets.values())
            eta = m*w1
            assert nu - (2*nu+eta)/4 == nu/2-eta/4
            assert nu/2-eta/4 == m*((1-eps)*w0-w1)/4
            cases += 1
    print(f"PASS: {cases} exact rational incidence/accounting cases (not EE maps)")

def fetch(url):
    for attempt in range(3):
        try:
            req = Request(url, headers={"User-Agent": "loops-research-archive source audit/1.0"})
            with urlopen(req, timeout=90) as response:
                data = response.read()
            assert data.startswith(b"%PDF-"), url
            return data
        except Exception:
            if attempt == 2:
                raise
            time.sleep(2*(attempt+1))

def compact(text):
    return re.sub(r"\s+", "", unicodedata.normalize("NFKC", text))

def provenance():
    from pypdf import PdfReader
    locks = json.loads((HERE / "sources.lock.json").read_text())
    for name, record in locks.items():
        data = fetch(record["url"])
        digest = hashlib.sha256(data).hexdigest()
        print(f"SOURCE {name} sha256={digest} bytes={len(data)}", flush=True)
        if record["sha256"] is not None:
            assert digest == record["sha256"], name
            assert len(data) == record["bytes"], name
        else:
            print(f"PROVISIONAL {name}: digest measured, not yet locked")
        if name == "EE":
            reader = PdfReader(io.BytesIO(data))
            assert len(reader.pages) == 20
            for page, marker in [(10,"Lemma4.3"),(16,"Theorem7.1"),(17,"Lemma7.3"),(18,"(7.5)")]:
                assert marker in compact(reader.pages[page-1].extract_text()), (page, marker)
    print("PASS: PDF provenance and EE locators (not proof verification)")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--offline", action="store_true")
    args = parser.parse_args()
    arithmetic()
    if not args.offline:
        provenance()
