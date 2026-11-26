"""Exact scalar diagnostics and read-only primary-source fingerprint check."""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
from urllib.request import Request, urlopen

HERE = Path(__file__).resolve().parent
GAMMA_LOWER = F(1, 16)  # log(2)>1/2 and pi<4

def disk(x, y, t, radius):
    return (x-t)**2+y*y <= -2*radius*y

def witnesses():
    for L in (17, 100, 1000):
        q = L
        k = 1
        for i in range(1, 6):
            assert F(k,q) == F(1,L)
            x, y = F(1,q), -F(k,16*q)
            assert disk(x,y,x,GAMMA_LOWER*k/q)
            if i >= 2:
                assert abs(y)>abs(x)
            assert x+abs(y)<=F(17,16*L)
            k *= q
            q *= q
    for b in (17,100,1000):
        d=b*b
        q=b*d+1
        A, B=F(q,d), F(2,d)
        t=1/A
        x,y=A/(A*A+B*B), -B/(A*A+B*B)
        assert abs(y)<=abs(x)
        assert disk(x,y,t,GAMMA_LOWER/q)
        assert ((x-t)**2+y*y)/(-2*y)==F(d,q*q)
        assert t<GAMMA_LOWER
        # G(z)=-1/z+b; nearest integer to -A is -b.
        assert round(-A)==-b
        wx,wy=-x/(x*x+y*y)+b, y/(x*x+y*y)
        assert (wx,wy)==(-F(1,d),-F(2,d))
        assert abs(wy)>abs(wx)
        assert wx*wx+wy*wy==F(5,d*d)
        assert -1/F(-1,d)-d==0
    # Exact real-part identity for sample nonattracting multipliers,
    # with distinct-from-one prerequisite explicitly checked.
    for x in (F(-2),F(-1),F(0),F(1),F(2)):
        for y in (F(0),F(1,3),F(2)):
            denom=(1-x)**2+y*y
            if denom==0 or x*x+y*y<1:
                continue
            deficit=F(1,2)-(1-x)/denom
            assert deficit==(x*x+y*y-1)/(2*denom)>=0
    print("Exact full-disk witnesses and index algebra: OK (not dynamical counterexamples)")

def lock_check(fetch):
    lock=json.loads((HERE/"sources.lock.json").read_text())
    assert set(lock)=={"CS-arxiv","CS-author","Levin"}
    for name, expected in lock.items():
        assert expected["url"].startswith("https://")
        assert len(bytes.fromhex(expected["sha256"]))==32
        assert expected["bytes"]>0
        if fetch:
            req=Request(expected["url"],headers={"User-Agent":"loops-source-audit/1.0"})
            with urlopen(req,timeout=60) as response:
                data=response.read()
                actual={"url":expected["url"],"resolved_url":response.geturl(),
                        "bytes":len(data),"sha256":hashlib.sha256(data).hexdigest()}
            print(name, json.dumps(actual,sort_keys=True),flush=True)
            assert data.startswith(b"%PDF")
            assert actual==expected, (name,actual,expected)
    print("Source locks:", "independently downloaded and matched" if fetch else "schema OK; bytes not fetched")

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--fetch",action="store_true")
    args=parser.parse_args()
    witnesses()
    lock_check(args.fetch)
