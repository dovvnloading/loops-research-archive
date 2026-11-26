"""METADATA only: byte locks, exact seam arithmetic, finite certificate comparison."""
import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[3]
LOCKS = {
    "CONTRIBUTING.md": "814723c308086d5e27780d016c18eed3e56f0e776c90efb255e81ba929e6d75a",
    "research/frontier/pl_yoccoz_radial_20261126/NOTE.md": "7febfbfb784bac7c164db97c73809d53c7b5631d11ed83e55f543c1721eac0b9",
    "research/frontier/is_local_dilatation_20261126/NOTE.md": "b93de77f3533d5637b0723bceb8fba48eb32af2535c2110b0afaa5fc4097a195",
    "research/frontier/cs_multiplier_locus_extended_20261126/NOTE.md": "742ea6af8f531a3f61839075c19d664db3bd47f2a3ee8bfa21b0c88e7ccb16ac",
    "research/frontier/cs_multiplier_locus_extended_20261126/results.json": "81d1f21db9392418bf0300d9f7c04f00c6362c95c72c2968aef62df159d69d39",
}
RESULTS = "research/frontier/cs_multiplier_locus_extended_20261126/results.json"
EXPECTED = [
    (3,1,3,959058421740,1043275477879,0),
    (4,3,12,965910582461,1034755847983,0),
    (5,12,60,972025343526,1028253396118,0),
    (6,60,360,976343206977,1023796328257,0),
    (7,360,2520,979509071354,1020573657154,0),
    (8,2520,20160,981925946823,1018130454618,0),
    (9,20160,181440,983831119554,1016211685416,2),
]
SOURCES = {
    "CS_v1": ("https://arxiv.org/pdf/1509.07843v1", "71c03718203b91ae81f5b7e138620a086cdf038b345cf689a24ed2932d72384f"),
    "Hubbard": ("https://pi.math.cornell.edu/~hubbard/Yoccoz.pdf", "eb28f6376e63683007fee394dee1b4e217d1b8d4fbd43118c2fa7e7f1754bf5d"),
    "IS": ("https://www.math.kyoto-u.ac.jp/~mitsu/pararenorm/ParabolicRenormalization.pdf", "7ca4bf1341991f6d02331a121d715d50e0282d84a30520766193830ef96de00c"),
    "Levin": ("https://www.ma.huji.ac.il/~levin/Levin1990_Article_BoundariesForMultipliersOfPeri", None),
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check():
    for path, expected in LOCKS.items():
        assert sha((ROOT / path).read_bytes()) == expected, path
    data = json.loads((ROOT / RESULTS).read_bytes())
    assert data["verdict"] == "INCONCLUSIVE"
    assert data["conservative_ply_guard"] is True
    assert data["certificate_units"] == "1e-12"
    assert data["certificate_columns"] == [
        "period", "gap_lower_1e12", "rho_box_1e12",
        "selfmap_upper_1e12", "scaled_norm_1e12"]
    rows = []
    parent = 1
    for q, row in enumerate(data["levels"], 3):
        d = dict(zip(data["columns"], row))
        assert d["q"] == q and d["p"] == parent and d["P"] == parent*q
        cert = d["certificates"]
        assert len(cert) == 7
        selected = [cert[2]] + [pair[1] for pair in cert[3:]]
        assert len(selected) == 5
        for record in selected:
            assert record[0] == parent
            lo, hi = record[4]
            assert isinstance(lo, int) and isinstance(hi, int) and 0 < lo <= hi
        rows.append((q, parent, parent*q,
                     min(r[4][0] for r in selected),
                     max(r[4][1] for r in selected),
                     d["ply_ambiguous_primary"]))
        parent *= q
    assert rows == EXPECTED
    b = math.log(2)/(2*math.pi)
    envelope = math.hypot(1,b)+b
    assert 1.11638 < envelope < 1.11639
    # Rounded interval endpoints are integers; the comparison has ample margin.
    assert all(row[4] < 1116380000000 for row in rows)
    seam = []
    for q in (3, 4, 7, 9, 32, 100, 1000):
        period = Fraction(1,q)
        gap = Fraction(1,q*q)
        jump = Fraction(1,q)
        slope_up = jump/gap
        slope_down = -jump/(period-gap)
        assert slope_up == q and slope_down == Fraction(-q,q-1)
        assert max(abs(slope_up),abs(slope_down)) == q
        assert 2*slope_up*slope_up >= 1  # sqrt(2)*L >= 1, B is infinite
        seam.append({"q":q,"gap":str(gap),"jump":str(jump),
                     "L":str(slope_up),"criterion":"FAILS FOR THIS TRACE"})
    out = {"status":"METADATA; T OPEN; no marked K measured",
           "certificate_columns":["q","p","P","min_lower_1e12","max_upper_1e12","ambiguous_primary"],
           "certificate_rows":rows,"K1_radial_envelope":envelope,
           "model":seam,"sha256":LOCKS}
    print(json.dumps(out,indent=2),flush=True)
    return out


def fingerprint(item):
    name,(url,expected) = item
    r = {"url":url,"expected_sha256":expected}
    try:
        with urlopen(Request(url,headers={"User-Agent":"research-source-audit/1.0"}),timeout=15) as response:
            data = response.read(25_000_001)
            r["final_url"] = response.geturl()
        if not data.startswith(b"%PDF-") or len(data)>25_000_000:
            raise ValueError("not a PDF within byte limit")
    except (OSError, ValueError) as exc:
        r.update(status="UNVERIFIED",error=str(exc))
        return name,r
    actual=sha(data)
    r.update(sha256=actual,bytes=len(data),status=(
        "NEW_FINGERPRINT" if expected is None else "MATCH" if actual==expected else "MISMATCH"))
    return name,r


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--sources",type=Path)
    args=p.parse_args()
    out=check()
    if args.sources:
        with ThreadPoolExecutor(max_workers=4) as pool:
            sources=dict(pool.map(fingerprint,SOURCES.items()))
        manifest={"arithmetic":out,"source_fingerprints":sources}
        args.sources.write_text(json.dumps(manifest,indent=2,sort_keys=True)+"\n",encoding="utf-8")
        print(json.dumps(sources,indent=2),flush=True)
        assert not any(s["status"]=="MISMATCH" for s in sources.values())


if __name__=="__main__":
    main()
