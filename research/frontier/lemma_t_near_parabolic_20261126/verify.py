"""Finite arithmetic/source-lock audit, not a physical trace or admission proof."""
import argparse
import cmath
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import subprocess
import urllib.request

ROOT = Path(__file__).resolve().parents[3]
REF = "0c97cfc87fe2bcc751ec28320ef50095bb9ce248"
INPUTS = {
    "CONTRIBUTING.md": "d218e12ba518a3fb193590a126e638836ce18a5ea5ccabf121f83ef6f6fafdd3",
    "RESEARCH_MAP.md": "0f8c6984283e404b820da9b83d85dca071513a4288b3fd041e15bb44b8f3dea6",
}
INPUTS.update({
    "research/frontier/" + d + "/NOTE.md": h for d, h in {
        "local_dilatation_construction_20261126": "0f5169927bf3b8a5f78303171c0007632d55d1a3b6c07193dd2113615a27824a",
        "is_local_dilatation_20261126": "b93de77f3533d5637b0723bceb8fba48eb32af2535c2110b0afaa5fc4097a195",
        "pl_yoccoz_radial_20261126": "7febfbfb784bac7c164db97c73809d53c7b5631d11ed83e55f543c1721eac0b9",
        "residual_satellite_status_20261126": "99d7c409e6d57bd34b784156b6e52bdc8d4c137775f67a551e2755adc2404921",
        "cs_multiplier_locus_numerics_20261126": "648cb202497dcf4bcb333c1770bb7d840016278dd4b6625d6ecc430a9c67df79",
        "cs_multiplier_locus_extended_20261126": "742ea6af8f531a3f61839075c19d664db3bd47f2a3ee8bfa21b0c88e7ccb16ac",
        "cs_prop_6_10_angular_20261126": "bdb8f6d8440b178adeb880a69638c77c4a08fd7f4f4ce848e898bd47b31c9f83",
    }.items()
})
PDFS = {
    "https://arxiv.org/pdf/1509.07843v1": "71c03718203b91ae81f5b7e138620a086cdf038b345cf689a24ed2932d72384f",
    "https://www.math.kyoto-u.ac.jp/~mitsu/pararenorm/ParabolicRenormalization.pdf": "7ca4bf1341991f6d02331a121d715d50e0282d84a30520766193830ef96de00c",
    "https://pi.math.cornell.edu/~hubbard/Yoccoz.pdf": "eb28f6376e63683007fee394dee1b4e217d1b8d4fbd43118c2fa7e7f1754bf5d",
}

def check(ok, what):
    if not ok:
        raise RuntimeError(what)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def inputs():
    for path, digest in INPUTS.items():
        data = subprocess.check_output(["git", "show", f"{REF}:{path}"], cwd=ROOT)
        check(sha(data) == digest, f"repository input mismatch: {path}")
        print("MATCH", path, digest)

def sources():
    for url, digest in PDFS.items():
        req = urllib.request.Request(url, headers={"User-Agent": "loops-research-source-audit/1.0"})
        with urllib.request.urlopen(req, timeout=90) as res:
            check(res.geturl().startswith("https://"), "non-HTTPS redirect")
            data = res.read(32 * 1024 * 1024 + 1)
        check(data.startswith(b"%PDF") and len(data) <= 32 * 1024 * 1024, f"bad PDF: {url}")
        check(sha(data) == digest, f"source mismatch: {url}: {sha(data)}")
        print("MATCH", url, digest, len(data))

def arithmetic():
    cases = 0
    for q in list(range(3, 401)) + [1000, 10000, 1000000]:
        # coordinates scaled by 2pi, so v=(0,1)
        x = F(q)-F(1,q)
        ds = [x*x + F(1,q**(2*j)) for j in (1,2)]
        a, ap = [F(1,q**j)/ds[j-1] for j in (1,2)]
        b, bp = [x/d for d in ds]
        r, s = ap/a, (bp-b)/a
        check(a/ap == q*ds[1]/ds[0] >= F(q,2), "relative real-part ratio")
        check(r > 0 and r <= F(2,q), "determinant")
        # exact affine and marking preservation; ell=q*y-(q*b-1)*x/a
        def A(w):
            u,v=w
            return (r*u,s*u+v)
        def ell(w, aa, bb):
            u,v=w
            return q*v-(q*bb-1)*u/aa
        check(A((F(0),F(1))) == (F(0),F(1)), "meridian")
        check(A((a,b)) == (ap,bp), "return")
        for w in ((F(0),F(1)), (a,b), (q*a,q*b-1), (F(7,11),F(-5,13))):
            check(ell(w,a,b) == ell(A(w),ap,bp), "label")
        check(ell((a,b),a,b) == 1 and ell((F(0),F(1)),a,b) == q, "increments")
        check((r*r+s*s+1)/r >= 1/r, "condition sum lower bound")
        for p in (-1,1):
            k=p*q
            # in target basis (v,tau'), old v -> (-k,1), old tau -> (-1,0)
            mv, mt = (-k,1),(-1,0)
            check(mv[0]*mt[1]-mv[1]*mt[0] == 1, "SL2Z")
            core = (q*mt[0]-p*mv[0],q*mt[1]-p*mv[1])
            check(core == (0,-p), "reciprocal core")
            check(core not in ((-p,q+1),(p,-q-1)), "not next core")
        for d in ds:
            check(F(q*q)/d <= (F(q)/x)**2, "radial upper bound squared")
        cases += 1
    # Numerical diagnostic only: small rotations, elementary analytic fixed point.
    for q in (100,1000,10000):
        for j in (1,2):
            gamma=1/q-1j/q**j
            beta=1/(q-gamma)
            lam=cmath.exp(2j*math.pi*beta)
            t=(3-lam)/2
            alpha=cmath.log(t)/(1j*math.pi)
            scale=cmath.exp(2j*math.pi*alpha)
            z=(1/t-1)/scale
            P=lambda w:w*(1+w)**2
            check(abs(P(scale*z)-z)<1e-13, "numeric fixed point")
            check(abs(scale*(1+scale*z)*(1+3*scale*z)-lam)<1e-13, "numeric derivative")
            check(alpha.real<0 and abs(alpha.imag)<-alpha.real and beta.imag<0, "numeric input cone")
            check(abs(-1/(-beta.conjugate())-q+gamma.conjugate())<1e-10, "numeric bottom digit")
    print(json.dumps({"exact_grid_cases":cases,"numeric_cases":6,"scope":"synthetic one-step only; physical T OPEN"}))

if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch",action="store_true",help="strictly verify inherited primary PDF fingerprints")
    args=parser.parse_args()
    inputs()
    arithmetic()
    if args.fetch:
        sources()
    else:
        print("PDF bytes NOT CHECKED (use --fetch)")
