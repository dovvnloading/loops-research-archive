# Verification and adversarial proof audit

These checks accompany [the ground-transfer proof](NOTE.md) and [the spectral-clock proof](MISIUREWICZ.md). Base main 47806d64c64688bdf27c817f036cfdbfa85ce1d5. Analytic deductions are written proofs, not machine-formalized theorems.

## Failure modes checked

- Green normalization: the parameter Green function is twice the dynamical Green function at 0, equivalently the dynamical Green function at c. For the Misiurewicz entrance time m this yields 2^(1-m) in the positive-level limiting profile.
- The two Green minimizers need not coincide. Both are used in opposite variational comparisons; the positive-semidefinite identity is proved before taking extrema. Point charges are never assigned finite self-energy.
- The global optimum concerns a supremum over nondegenerate actual continua, not over polar singletons. Boundary bumping and continuity give genuine witnesses without invoking MLC.
- The conformal-radius inversion is reciprocal to logarithmic capacity. The integrated schlicht ratio is valid for any two interior radial levels, not just for the Koebe extremal function or a starlike image.
- The cusp's upper escape estimate controls a whole complex disk via the positive real majorant, not merely a real ray. The lower estimate supplies an escaping point, then the Koebe quarter inequality bounds the radius.
- Tan's entrance derivative is nonzero by her Lemma 5.4; the local Koenigs iteration stays in its chart. The extension to arbitrary compact windows uses a fixed number of polynomial returns.
- Locally uniform convergence of Green functions alone does not guarantee kernel convergence at an arbitrary level. Here the strict positivity and nonconstancy on the positive-level set exclude a plateau at every v>0. The argument for the basepoint component applies to every subsequence. Uniformity in v is proved using continuity and monotonicity, not a hidden assumption of monotonicity in the renormalization index.
- The explicit Chebyshev profile at -2 is squared through the odd strip-to-disk bijection; the derivative is taken in the actual parameter rescaling variable, not the square-root coordinate.
- None of these results constructs the H4 connected relative neighborhoods, certifies the required gain schedule, or proves uniform Misiurewicz estimates at infinitely renormalizable limits. An arbitrary small physical continuum is not automatically a relative neighborhood.

## Reproducible finite arithmetic audit

The following standalone Python 3 snippet was executed successfully during this PR. The recurrence enclosure uses only integers and exact fractions, with outward rounding at each step on the grid of denominator 2^128. Finite examples are sanity checks, **not** the proof of the general inequalities or analytic limit. Copy the code block into Python or a temporary file; no third-party dependency is required.

```python
from fractions import Fraction as Q
S = 1 << 128

def floorq(v):
    return v.numerator // v.denominator

def ceilq(v):
    return -floorq(-v)

def enclose(q):
    return floorq(q*S), ceilq(q*S)

def step(box, c):
    l, h = box
    assert 0 <= l <= h
    cl, ch = enclose(c)
    return l*l//S + cl, (h*h+S-1)//S + ch

assert Q(8,3)*Q(10,13)**2 > 1
assert Q(13,16) < 1
assert 3*Q(22,7)+Q(1,2) < 10
assert 1600*64 == 102400
ntip = 0
for k in range(2, 41):
    d = Q(1, 2**k)
    c = -2-d
    v = Q(8,3)*d
    j_bound = 2
    while v < 1:
        v *= 4
        j_bound += 1
    x = enclose(c*c+c)
    j = 2
    while x[0] < 3*S and j < j_bound:
        x = step(x,c)
        j += 1
    assert x[0] >= 3*S and j <= j_bound
    ntip += 1
ncusp = 0
for k in (8,12,16,24,32,48,64,96,128,192,256,384,512,768,1024):
    c = Q(1,4)+Q(1,k*k)
    x = (0,0)
    for _ in range(k//4):
        x = step(x,c)
    assert x[1] < S//2
    j = k//4
    while x[0] < 2*S and j < 10*k:
        x = step(x,c)
        j += 1
    assert x[0] >= 2*S and j <= 10*k
    ncusp += 1
nratio=0
for r0 in (Q(1,10), Q(1,4), Q(1,2), Q(3,4), Q(9,10)):
    for r1 in (Q(1,4), Q(1,2), Q(3,4), Q(9,10), Q(99,100)):
        if r0 >= r1: continue
        koebe=lambda r:r/(1-r)**2
        assert koebe(r1)/koebe(r0) == (r1/r0)*((1-r0)/(1-r1))**2
        assert (1-r0*r0)/(1-r1*r1) <= ((1-r0)/(1-r1))**2
        nratio+=1
for ell in (Q(1,100),Q(1),Q(10),Q(1000)):
    delta=1/(16*(1+ell))
    a=(1-delta)/(1+delta)
    assert 1-a*a <= 4*delta and 8*delta*ell <= Q(1,2)

def add(a,b): return (a[0]+b[0],a[1]+b[1])
def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
c=(0,1); z=(0,0); orbit=[z]
for _ in range(4):
    z=add(mul(z,z),c); orbit.append(z)
assert orbit == [(0,0),(0,1),(-1,1),(0,-1),(-1,1)]
lam=mul((4,0),mul(orbit[2],orbit[3]))
assert lam == (4,4) and sum(v*v for v in lam)==32
assert Q(64,1)/Q(8,3)==24
print(f'PASS: {ntip} tip escape intervals; {ncusp} cusp transit intervals; {nratio} radial-ratio identities; 4 Harnack witness inequalities; exact Gaussian orbit and tip normalization.')
```

Observed output:

```text
PASS: 39 tip escape intervals; 15 cusp transit intervals; 15 radial-ratio identities; 4 Harnack witness inequalities; exact Gaussian orbit and tip normalization.
```

The source comparison included Saff's Green-energy discussion and Tan Lei's published parameter linearization/transversality statements. Neither the original general results nor the present deductions are certified by the finite arithmetic audit. The analytic argument still needs independent specialist review; no priority or new MLC case is claimed.

## Next noncircular target

The exact formula identifies the relevant local cost but does not automatically transfer pointwise costs to a moving tower. One would need physical escape-profile/radius estimates uniform on the actual H4 relative neighborhoods, or an alternative weighted comparison on their equilibrium measures, together with the divergent net gain and neighborhood construction. Merely assuming that all tower compacts already lie in shrinking disks would risk assuming the desired conclusion. The claim ledger remains unchanged.

AI assistance: ChatGPT GPT-6.2, including proof derivation, source reading, adversarial audit, and execution of the exact arithmetic snippet. No independent specialist or Lean verification.
