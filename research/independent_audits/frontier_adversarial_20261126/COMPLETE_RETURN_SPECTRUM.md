# Complete physical return spectrum at the certified 3/9 tip

Base: 47806d64c64688bdf27c817f036cfdbfa85ce1d5.
Continuation of [sharp clock degree](SHARP_CLOCK_DEGREE.md), with independent arithmetic premises in [check_clock_arithmetic.py](check_clock_arithmetic.py).
Status: written analytic/continuum theorem for this exact polynomial, pending mathematical review. No change to the global ledger.

## 1. Statement: all integer times and all degrees, not just the minimum

Let c be the real root of P18(c)+P9(c)=0 in the adjacent dyadic bracket used in the archive, where P0=0 and P_(j+1)=P_j²+c. Let f(z)=z²+c, X=K(f)=J(f), and retain its actual filled sets K3,K9. For every integer m≥1, the connected filled sets of *all* polynomial-like restrictions of f^m which contain 0 are precisely:

| Filled set | Allowed physical times | Return degree |
|---|---|---|
| X | every m | 2^m |
| K3 | 3 divides m | 2^(m/3) |
| K9 | 9 divides m | 2^(m/9) |

There are no others, including higher-degree intermediate restrictions. This concerns filled sets, not uniqueness of their open domain representatives. Each listed set is realized by an actual proper restriction. For the entire second-decoration inventory U, only the first two rows survive because its hull I strictly contains K9. In particular the degree spectrum of f⁹ through 0 is exactly {2,8,512}, and only degrees 8 and 512 carry U. At time 6 the spectrum is exactly {4,64}; there is no degree-two restriction through 0 at that time, even if the inventory is not prescribed.

No numerical search over possible periods or degrees is involved.

## 2. Independently checked physical inputs

Write x_j=f^j(0). The checker uses outward integer arithmetic at scale 2^256 on the adjacent rational parameter endpoints
    N/2^128 < c < (N+1)/2^128,
    N = -607918036626757496169199575185708826140.
It certifies opposite strict signs of x18+x9 at the endpoints, a strictly negative parameter derivative on the entire bracket, disjoint enclosures for x0,...,x18, and multiplier of the eventual nine-cycle with modulus greater than one. Thus the unique root exists; x18=-x9 and x19=x10 exactly. The distinctness and subsequent equality give exact preperiod 10 and exact repelling period 9. The classical Misiurewicz conclusion gives connected K(f)=J(f) of empty interior (the bounded critical orbit gives connectedness, and the strictly preperiodic repelling critical orbit gives the subhyperbolic nonattracting case). This uses the same standard PCF/Misiurewicz input as the archive.

Here are direct proofs of the physical premises of SHARP_CLOCK_DEGREE.md which need neither the full KL access construction nor a finite sample of inverse branches.

### 2.1. Period three by one exact polynomial expansion

Set G=f³, R=1/4, U3={|z|<R}. The identity
    G(z)=x3+4cx2 z²+(4c²+2x2) z⁴+4c z⁶+z⁸
follows by expanding f²(z)=x2+2cz²+z⁴. The checker independently evaluates the strict lower margin
    4|c|x2 R² - (4c²+2x2)R⁴ - 4|c|R⁶ - R⁸ - |x3| - R > 0.127132476
through rational outward enclosures (x2>0). For every |w|<R, Rouché on |z|=R gives exactly two roots of G(z)=w inside U3, counted with multiplicity; no root on the boundary for |w|≤R. The bounds |c|>R² and x2>2|c|R²+R⁴ exclude additional zeros of f and f² on the closed source disk, so G has exactly the one simple critical point 0 there. Also |x3|<R.

The component V of G⁻¹(U3) inside U3 containing 0 maps properly onto U3 and has degree at least two by the simple critical point; the total count is two. For detail, compact containment follows from the strict source-boundary estimate and continuity; a component's restriction is proper, its image both open and closed in U3, so is onto. There can be no other component inside U3. Its boundary is a finite union of analytic Jordan curves because the preimage of |w|=R is regular inside U3 and compactly separated from |z|=R. Riemann–Hurwitz for the proper branched map with one simple critical point gives Euler characteristic 1; the connected planar bordered domain is a disk. Thus G:V→U3 is quadratic-like.

The checker proves
    -R < x6 < x9 < 0 < x3 < R.
On the real source interval, the intermediate factors f(z)<0 and f²(z)>0 by the same critical-exclusion estimates and their signs at 0. The derivative G'(z)=8z f(z) f²(z) is positive for z<0 and negative for z>0. Hence on I3=[x6,x3] the maximum is G(0)=x3, and the minimum is G(x3)=x6 because G(x6)=x9>x6. Thus G(I3)=I3. Since I3 lies inside U3 and maps there, it lies in the central component V, and all its returns stay in V. In particular the critical orbit is nonescaping for this restriction; the connectedness criterion for quadratic-like maps gives connected filled set K3 containing I3. The exact disk gap check for the three phase images is >0.927889313, which also verifies primitive phase separation, although the classification below needs only the degree word.

### 2.2. Period nine by an exact real saturated cycle

Set J0=[x9,x18], with symmetric endpoints and 0 in its interior. For j=0,...,8 the following table gives the endpoint-index pairs of J_j:
    (9,18), (1,10), (11,2), (12,3), (13,4),
    (5,14), (6,15), (16,7), (8,17).
The checker certifies their order, disjointness, nonzero phases' strict avoidance of [-1/10,1/10], and the exact endpoint-index maps for j≥1. At phase 0 the symmetric endpoints map to x10 and 0 maps to c=x1, so f(J0)=J1=[c,x10]. At all other phases f is strictly monotone and the endpoint map gives exactly J_(j+1). Every orbit value other than x1 is strictly above c (for real iterates this also follows from f(x)=x²+c and distinctness).

All intervals lie in X because their cyclic orbit is bounded. At step 0, f⁻¹([c,x10]) is exactly the real symmetric interval J0: the square of a complex number in [0,x10-c] is realized only by real roots, including the double root at 0. At the other steps the target lies strictly above c, so its inverse is exactly two disjoint real intervals, and J_j is one of them by its monotone surjection. Thus this is a saturated 9-cycle with degree word (2,1,...,1). The recognition theorem in CYCLIC_RIGIDITY.md proves it is an actual quadratic-like return, with filled set K9=J0 by uniqueness. This independently avoids the earlier period-nine Rouché calculation. Strict containment K9⊂I3 is in the arithmetic, and K9⊂K3 also follows from PERIOD_INTERSECTION.md Theorem 1.

### 2.3. The clock-cover condition from the intermediate value theorem alone

Let a be the unique real root of G(a)=a in (3/32,1/10). Strict signs at the endpoints and G'<-1 throughout that interval are independently certified. The checker proves x6<-1/10 and x3>1/10, hence I=[-a,a]⊂I3⊂K3. Also |x9|,|x18|<1/32, so K9⊊I. Because
    f⁶(a)=a,    f⁶(0)=x6<-a,
continuity on [0,a] gives f⁶(I)⊃I. This establishes the actual covering containment with no reliance on the source inverse-branch identification. The identification of this a with the native dividing root and of the inventory U with hull I is still imported from the [cell-tree audit](../h1_cell_tree_extraction_20261126/NOTE.md), §§4.1–4.2, and its source KL dependencies. The all-return spectrum below is already a theorem for this real I and the polynomial, independent of that native identification.

## 3. Exact classification for carriers containing I

Use the fixed-time inclusion law (1) and clock forcing theorem in SHARP_CLOCK_DEGREE.md. Any saturated m-cycle H containing I at phase 0 contains the repeated minimal carrier: X when 3 does not divide m, and K3 when 3 divides m. In the first case there is no alternative. In the second case its critical word D contains all multiples of 3, and its jth phase contains the genuine A³_(j mod 3).

We need one additional fact about real subcontinua. With β=(1+sqrt(1-4c))/2, the full real interval [-β,β] maps into itself because c=β-β²≥-β and β≤2 at this parameter. Hence it lies in X. In particular the real interval between any of the specified real orbit points, or their negatives, lies in X. If H_j contains two such points, it contains the interval between them, by hereditary unicoherence: its intersection with that real interval is connected and contains both endpoints. At a critical source H_j is the entire one-step preimage of its target, hence invariant under z→-z.

Suppose now D contains j not divisible by 3. There are two cases.

* j≡1 mod 3. H_j contains c from A³_1 and 0 by its critical membership. Symmetry and the real-hull fact put I in H_j since |c|>a. Its image H_(j+1) contains c=f(0) and x2=f(c), so the interval [c,x2] contains I (c<-a, x2>a).
* j≡2 mod 3. H_j contains x2 and 0, hence I by symmetry and x2>a. Its image contains c and x3=f(x2)>a, hence I; the next image contains c and x2, hence I again.

The inequalities c<-a, x2>a and x3>a follow from the checked sign and strict nonzero-phase gap tests, and the fixed-point bracket. In each case the rotated clock-forcing theorem applied at these I-containing phases forces all residues in the remaining cosets modulo 3 to be critical. Together with the original multiples of 3, this gives D=Z/mZ. Fixed-time rigidity then identifies H_j=X for every j. If no extra critical residue occurs, D is precisely the multiples of 3 and fixed-time rigidity identifies H with the repeated K3 cycle.

We have proved the stronger statement: every saturated m-cycle containing I has filled set either X or K3, with the latter allowed only when 3 divides m. Thus the minimum in SHARP_CLOCK_DEGREE.md is not merely a lower envelope; there is no intermediate degree.

## 4. Classification without prescribing I: any carrier through 0

Let H be an arbitrary saturated m-cycle with 0∈H_0. Necessarily H_0 is symmetric and contains x_(km)=f^(km)(0) for every k≥0.

If 9 does not divide m, then gcd(m,9) is either 1 or 3. The eventual nine-cycle is exactly periodic and every residue divisible by gcd(m,9) is visited by km mod 9 for arbitrarily large k. In particular H_0 contains x12, where x12>1/10 follows from the ordered positive phase-three interval and its strict avoidance of [-1/10,1/10]. Symmetry and the real-hull fact give I⊂H_0. Section 3 now gives exactly X or, when 3 divides m, K3.

If 9 divides m, then x_m is either x9 (m=9) or x18 (m≥18); these are opposite symmetric endpoints of K9. H_0 contains 0 and x_m and is symmetric, hence contains K9. The repeated K9 cycle is therefore contained phasewise in H, and D contains all multiples of 9 (use f⁹(K9)=K9). If these are the only critical phases, fixed-time rigidity gives H_0=K9.

Otherwise pick a critical source j not divisible by 9. Its phase contains the genuine nonzero phase A⁹_(j mod 9), which by the exact phase check contains real points of absolute value >1/10>a. Because H_j is critical, symmetry and the real-hull fact give I⊂H_j. Apply §3 to the rotated cycle starting at j: its filled carrier is either X or K3. If it is X, all original phases equal X. If it is K3, the original phase zero is f^(m-j)(K3) (indices modulo m). This phase contains 0 by hypothesis, so it is the critical phase of the three-cycle, namely K3. Thus H_0 is one of the listed sets and no intermediate critical word exists.

The recognition equivalence and one-step decomposition in SHARP_CLOCK_DEGREE.md §3 apply to any polynomial-like restriction of f^m with connected filled set containing 0, so the argument classifies those analytic filled sets as well. Conversely the listed cycles exist for their divisibility times, and BOPT or the usual composition of actual polynomial-like returns supplies their proper restrictions. This proves §1 for all times and all degrees. QED.

## 5. Reproduction, trust boundary, and review

Run from repository root:
    python -B research/independent_audits/frontier_adversarial_20261126/check_clock_arithmetic.py

The standard-library checker was executed locally under Python 3.13.5. The committed script's Git blob SHA f112e7a9d58118ade698a9b9cdc61549f4adb981 matches the locally executed bytes. Output: opposite root signs [1,-1], exact preperiod 10 and repelling period 9, strict Rouché margin floor 127132476/10^9, phase gap floor 927889313/10^9, and 512 exact finite gcd residue regressions. There are no floating-point tests or random seeds. The arithmetic establishes the finite inequalities used above; the all-time classification is the written proof, not the finite residue census.

Inputs and limits: BOPT Theorem B as independently inspected in CYCLIC_RIGIDITY.md; Douady–Hubbard straightening and connectedness criterion; classical Misiurewicz theorem; Janiszewski, Rouché, Riemann–Hurwitz and IVT. The actual native inventory's identification still uses the cited archive source proof; the classification of f itself does not use that identification. No general classification of all infinitely renormalizable quadratics, no proof of MLC, no H1 promotion, no uniform modulus or access identification. The local environment cannot resolve github.com, so the complete repository-wide validator is delegated to the PR workflow, not claimed as a local run.

AI disclosure: GPT-6.2 derived the proof, rechecked the source interfaces, wrote and executed the independent arithmetic diagnostic. No human specialist or Lean-kernel review has occurred. The theorem is submitted for independent scrutiny.
