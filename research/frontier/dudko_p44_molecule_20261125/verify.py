"""Exact P44-GM-1 arithmetic. No float, no third-party dependency."""
import argparse
import json
from fractions import Fraction as F
from pathlib import Path

# Elements a+b*t of Q[t]/(t*t+t-1), t=(sqrt(5)-1)/2.
def q(a, b=0):
    return (F(a), F(b))

def add(x, y):
    return q(x[0]+y[0], x[1]+y[1])

def neg(x):
    return q(-x[0], -x[1])

def mul(x, y):
    a,b=x
    c,d=y
    return q(a*c+b*d, a*d+b*c-b*d)

def inv(x):
    a,b=x
    norm=a*a-a*b-b*b
    if norm == 0:
        raise ZeroDivisionError(x)
    y=q((a-b)/norm, -b/norm)
    assert mul(x,y)==q(1)
    return y

def div(x,y):
    return mul(x,inv(y))

def sub(x,y):
    return add(x,neg(y))

def check():
    one,t=q(1),q(0,1)
    lo,hi=F(618033,1000000),F(618034,1000000)
    assert F(1,2)<lo<hi<1
    poly=lambda x:x*x+x-1
    assert poly(lo)<0<poly(hi)
    assert add(add(mul(t,t),t),q(-1))==q(0)
    # At t use the upper branch; at u=1-t use the lower branch.
    u=sub(one,t)
    assert 0<1-hi<1-lo<F(1,2)
    upper=lambda x:div(sub(mul(q(2),x),one),x)
    lower=lambda x:div(x,sub(one,x))
    assert upper(t)==u and lower(u)==t and u!=t
    du=inv(mul(t,t))
    dl=inv(mul(sub(one,u),sub(one,u)))
    eigen=mul(dl,du)
    assert du==dl==q(2,1)
    assert eigen==q(5,3)
    assert sub(sub(mul(eigen,eigen),mul(q(7),eigen)),q(-1))==q(0)
    # Independent Mobius matrix: L*U = [[2,-1],[-1,1]], determinant 1.
    L=((1,0),(-1,1))
    U=((2,-1),(1,0))
    M=tuple(tuple(sum(L[i][k]*U[k][j] for k in range(2))
                  for j in range(2)) for i in range(2))
    assert M==((2,-1),(-1,1))
    a,b=M[0]; c,d=M[1]
    assert a*d-b*c==1
    den=add(mul(q(c),t),q(d))
    assert inv(mul(den,den))==eigen
    lam_lo,lam_hi=5+3*lo,5+3*hi
    assert 1<lam_lo<lam_hi
    # Hostile test: a one-step eigenvalue is not the two-step eigenvalue,
    # and a four-step clock cannot have the claimed two-step eigenvalue.
    assert du!=eigen and mul(eigen,eigen)!=eigen
    return {
        "claim_id":"P44-GM-1",
        "arithmetic_status":"proved",
        "certificate_type":"exact rational polynomial identities and strict rational bracket",
        "basis":"a+b*t, t^2+t-1=0, t>1/2",
        "rotation_bracket":[str(lo),str(hi)],
        "prime_cycle_coefficients":[[0,1],[1,-1],[0,1]],
        "minimal_prime_period":2,
        "branch_order":["upper","lower"],
        "branch_derivative_coefficients":[[2,1],[2,1]],
        "return_mobius_matrix":[list(row) for row in M],
        "unstable_eigenvalue_coefficients":[5,3],
        "unstable_eigenvalue_exact":"(7+3*sqrt(5))/2",
        "unstable_eigenvalue_polynomial":"x^2-7*x+1",
        "unstable_eigenvalue_bracket":[str(lam_lo),str(lam_hi)],
        "unstable_dimension_complex":1,
        "dimension_basis":"imported DLS Theorem 7.7 and DL Proposition 5.41, not checked by arithmetic",
        "clock_basis":"DL Proposition 5.41 for a suitably constructed operator, not every DLS normalization",
        "virtual_geometry_established":False,
        "global_molecule_hyperbolicity_established":False,
        "mlc_established":False
    }

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--output",type=Path)
    a=p.parse_args()
    out=json.dumps(check(),indent=2,sort_keys=True)+"\n"
    if a.output:
        a.output.write_text(out,encoding="utf-8")
    print(out,end="")
