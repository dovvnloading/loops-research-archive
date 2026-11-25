# A single prefix-potential charge for every deep stationary encounter

2026-11-25. Written modulus theorem and finite orbit/weight kernel.
This replaces the separate deep-collar calibration of
[DOUBLE_CROSSING_CHARGE.md](DOUBLE_CROSSING_CHARGE.md) by a single
base-domain variational quantity. It uses the actual quadratic
prefix degrees and the selected critical-limb count. It does not
prove a uniform estimate for that quantity or the native occurrence
assertion.

## 1. The native bounded-stay consequence

Let F:K→K be the filled-set dynamics of the actual pseudo-quadratic-like
map in a hyperbolic conformal disk U. Use the graph theorem
[filled-set graph naturality](../../mlc_unified/pql_iterate_filled_graph_naturality.md):
for each finite j there are an actual immersion I_j:U^j→U, a proper
holomorphic map P_j:U^j→U of degree 2^j, and a filled graph Γ_j satisfying

\[
 I_j^{-1}(K)=K^j,\qquad I_j|_{K^j}:K^j\cong K,\qquad
 P_j\Gamma_j=F^j\text{ on }K.
 \tag{1}
\]

Use I_0=P_0=Γ_0=id. No global inverse of I_j is required.

Let Ω_0 be the relatively open critical filled limb, φ its unique
critical-limb inverse branch, Ω_n=φ^n(Ω_0), and
C_n=closure(Ω_n) for n≥1. The
[selected predecessor theorem](../../mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md),
Theorem 4.3, proves the singleton closure boundary and the selected
inverse relation; the C_n are nested and C_1⊂Ω_0, as checked in
Section 4 of the double-crossing note. In particular
F(C_n)=C_(n−1) for n≥2.

Let T be the actual forward-invariant carrier containing the complete
small-Julia cycle. Assume the full-hull/singleton-cut incidence hypotheses
of [CUTPOINT_PRUNING.md](../maximal_global_closure_20261123/CUTPOINT_PRUNING.md),
with primitive period P≥q>b and at most b cycle components in the critical
limb. Its Section 6 and the double-crossing note prove T∩Ω_b=∅.
Only this disjointness and the selected inverse relation are needed
in the following deduction:

\[
 \boxed{\forall x\in T,\ \exists j\in\{0,\ldots,b\}:
                  F^j(x)\notin\Omega_0.}
 \tag{2}
\]

Indeed, if all b+1 orbit points remained in Ω_0, uniqueness of the
inverse branch inside Ω_0 would give
x=φ^b(F^b(x))∈Ω_b, a contradiction. This argument applies to
*every point* of the carrier, including the edges, not just marked
small-Julia vertices. It uses neither a countable endpoint set nor a
finite approximation of the physical curve. Conversely,

\[
 x\in C_n,\quad n\ge b+1
 \quad\Longrightarrow\quad
 F^j(x)\in C_1\quad(0\le j\le b).
 \tag{3}
\]

For (3), use F^j(C_n)=C_(n−j) and the nesting, including the actual
added boundary points. In the intended high-type applications the
horizons are finite and below q; no iteration past the available
selected sheets is implicit. The finite logic behind (2) and (3)
is isolated in the companion [Lean module](../../../formalization/weighted/StationaryPrefixCharge.lean).
The critical predicate in (2) is the open limb; the backward
nest in (3) uses its closed extension. Confusing them would
lose the endpoint at the dividing point.

## 2. One base potential and the prefix energy theorem

Put Z=K minus Ω_0, a compact set. Choose any smooth real
u on U with compact support, 0≤u≤1, identically 1 on a
neighborhood of C_1 and identically 0 on a neighborhood of Z.
Such a function exists qualitatively because these are disjoint
compacta in U. Write

\[
 E(u)=\int_U |\nabla u|^2\,dA,\qquad
 \mathfrak S(F)=\inf_u E(u)
 \tag{4}
\]

over precisely those functions. This is a three-conductor
Dirichlet response: C_1 at one, Z and the ambient outer boundary
at zero. The outer condition is supplied by compact support.
Dirichlet energy is conformally invariant. This is not a WAD
coefficient or a cyclic local width; the electrode sets and
boundary condition are explicit.

**Theorem.** For any family A of simple proper parents in U minus T
such that every parent hits some C_n with n≥b+1 at an interior time,
one has

\[
 \boxed{
 W(A)\le\frac{2^{b+1}-1}{4}\mathfrak S(F).
 }
 \tag{5}
\]

The same estimate applies to the union of all such encounter families,
even for different depths n. No number-of-banks factor is necessary.
No collar around a deep selected component is chosen. No proper final
exit or common-horizon lift is assumed.

### Proof

Work in unit-disk coordinates on the ambient surfaces. For each
0≤j≤b define the smooth source potential u_j=u∘P_j on U^j.
It is compactly supported because P_j is proper. Its energy is exactly

\[
 \int_{U^j}|\nabla u_j|^2\,dA
   =2^j E(u).
 \tag{6}
\]

Indeed the conformal derivative formula and area change for a
proper holomorphic map give the degree factor outside its finite
critical-value set; critical points contribute zero area.

On U put

\[
 f_j(w)=\left(
       \sum_{z\in I_j^{-1}(w)}
        \frac{|\nabla u_j(z)|^2}{|I_j'(z)|^2}
                \right)^{1/2},
 \qquad f=\left(\sum_{j=0}^b f_j^2\right)^{1/2}.
 \tag{7}
\]

The nonnegative sums are Borel (indeed lower semicontinuous, using
local inverse charts and finite subsums). The countable injective
chart partition and area formula of the exceptional-width note
apply to each immersion. In fact the nonzero terms occur in a
compact source set. Thus

\[
 \int_U f^2\,dA
   =\sum_{j=0}^b2^jE(u)
   =(2^{b+1}-1)E(u).
 \tag{8}
\]

First take a parent α of finite Euclidean length in the disk
coordinate. Both physical endpoints exist in the closed disk.
Properness in U minus T forces each endpoint to be in T or on
the outer disk boundary. Fix one actual encounter time t_0
with x=α(t_0)∈C_n. By (3), for each prefix j its canonical
lift point Γ_j(x) satisfies u_j(Γ_j(x))=1.

Consider the right half of the parent. If its physical endpoint
p is in T, use (2) to choose j≤b with F^j(p)∈Z. If the endpoint
is on the outer disk boundary, choose j=0. Start the actual
unpunctured I_j-lift at Γ_j(x), and continue it toward this
parent endpoint for its maximal lifetime. The lift is locally
rectifiable by local inverse charts. There are three possibilities.

* A finite interior-time stop forces compact escape, by the local
  inverse-chart argument of Lemma 6.3 of
  [the exit-transfer note](../maximal_exit_transfer_20261123/NOTE.md).
  Properness of P_j and compact support of u imply u_j tends to 0.
* At the original endpoint time, if the lift escapes every compact
  of U^j, the same compact-support argument gives limit 0.
* Otherwise there is an interior source accumulation point z.
  By continuity I_j(z)=p. Such an accumulation is impossible
  when p is on the outer boundary. If p∈T⊂K, (1) forces
  z=Γ_j(p), and u_j(z)=u(F^j(p))=0 by the selected index.
  It is enough that the potential tends to 0 along this subsequence;
  no uniqueness of an ideal limit is needed.

In every case variation from 1 to values arbitrarily near 0
implies the lifted gradient length is at least one. Formally
on compact time subintervals use the chain rule for the smooth
potential on the rectifiable lift, then exhaust toward its
lifetime endpoint. By the summand in (7), the f_j-length of
the corresponding literal parent subarc is at least that length,
and hence the f-length of the entire right half is at least one.

The same argument on the left half chooses a possibly
*different prefix j*. The parent-time halves are disjoint.
Consequently f-length of every finite-Euclidean-length parent
is at least two. The density f/2 is admissible for these parents.
In unit-disk coordinates add the positive constant ε to handle
all parents of infinite Euclidean length, then let ε↓0 in L².
This proves W(A)≤(2^{b+1}−1)E(u)/4 by (8).
Taking the infimum over u proves (5). QED.

This proof is valid for arbitrary proper path families with the
stated encounter, whether or not their widths add as a transverse
measure. It does not require measurable choice of a preferred
prefix, time, or lift: the single density (7) handles all of them
pointwise. It also does not identify properness of a lift in a
punctured surface with compact escape of an unpunctured lift.

### Open-neighborhood version

For each j, the canonical graph extends holomorphically to a
neighborhood of K by the cited filled-graph Lemma 3.4.
Since u is one on a neighborhood of C_1, for each fixed finite
deep C_n there is an open neighborhood O_n of C_n in U on
which all the canonical graph potentials u∘P_j∘Γ_j equal one.
Use the common intersection of those finitely many neighborhoods.
The proof of (5) works for a parent hitting this O_n, even if its
trace does not physically touch K. The same density works for
all such O_n chosen for the *fixed* potential u. Optimizing u
changes the neighborhoods; thus one may not take the infimum
in (5) for a family specified only by a single fixed O_n unless
its plateau condition persists for every candidate.

## 3. Quadratic endpoint-index cover and a cheaper special case

For a finite-length parent assign the first exit index of each
physical T endpoint as in (2), and index zero for an ambient
outer endpoint. Let E_pair be the actual set of unordered pairs
of indices, allowing equal indices. Given s_j≥0 such that

\[
 s_i+s_j\ge1\quad\text{for every pair }\{i,j\}\in E_{\rm pair},
 \tag{9}
\]

use f_s=(sum_j s_j² f_j²)^(1/2) rather than f/2.
The two disjoint parent halves give lengths at least s_i and s_j.
The exact energy bound now reads

\[
 W(A)\le E(u)\sum_{j=0}^b2^j s_j^2 .
 \tag{10}
\]

No factor of two is charged for a loop in E_pair beyond its two
actual time halves. Unlike the previous linear endpoint graph
problem, this is a quadratic weighted cover. Constant half-weights
prove (5). If every index can occur paired with itself, (9) forces
s_j≥1/2, so the uniform half choice minimizes (10) for that
worst-case index set; it is not a claim of extremal sharpness
for actual native curves.

If one physical parent end is always outside Ω_0 (or ambient
outer), and the other first exit has index 1,...,b, choose one
amplitude a at 0 and a common amplitude c at the other indices.
Set B=2^(b+1)−2 (b≥1). The constraints and objective are

\[
 a+c\ge1,\quad a,c\ge0,\qquad E(u)(a^2+Bc^2).
\]

The exact optimum is a=B/(B+1), c=1/(B+1), by completing
the square, and gives

\[
 W(A)\le \frac{B}{B+1}\mathfrak S(F)<\mathfrak S(F)
 \quad\text{if }\mathfrak S(F)>0.
 \tag{11}
\]

If both ends may have index zero but there is always at least
one zero-index end, the simpler s_0=1,s_j=0 for j>0 gives
W(A)≤\mathfrak S(F). In fact the latter bound is just one
ordinary base-potential crossing, and needs no prefix.
The source's phrase "Wave ending at BL_0" by itself only says
at least one end is somewhere in that multi-interval; it does
not prove the outside-end property for every leaf. Use (5)
unless the stronger physical endpoint classification is checked.
The Lean module verifies the finite budget, optimality of the
half weights when self-pairs occur, and the two-cost series
optimum; the analytic length/area transport remains written.

## 4. A genuine one-sided occurrence is enough to enter the bound

The companion [simultaneous finite-energy core](EXCEPTIONAL_WIDTH_REDUCTION.md)
can also include the source's actual full carrier T_h=P_h^(-1)(T)
as one compact full continuum at each prefix. This ensures that,
outside a single width-zero parent family, every raw lift has
finite disk-coordinate length and a physical endpoint limit.
For the following argument even the Euclidean term of that
envelope suffices.

Suppose a proper raw restriction of the parent in U^h minus T_h
ends at an inner ideal access e whose physical impression lies
in Γ_h(C_h), where h≥b+1. Its physical source limit z belongs
to that impression and hence to Γ_h(C_h)⊂K^h. (The limit is
obtained outside the width-zero family just described.)
Since I_h is continuous at z, the corresponding parent-time
limit is I_h(z)∈C_h. It cannot be an original parent endpoint:
C_h⊂Ω_b is disjoint from T and compactly contained in U.
It is therefore an actual interior encounter. Formula (5)
charges that parent without any need for a second restriction,
endpoint pairing, or noncollision.

Only the *one* actual proper raw restriction and its physical
access locality are needed. In the saturated-carrier model, the
latter locality has a source-specific check: the
[monotone boundary extension, Theorem 1](../issue40_monotone_model_prime_end_bridge_20261124.md)
gives M(Imp(e))={L_model(m(e))}. The physical T_h is the
full inverse of the corresponding model preimage hull under
the transported plane quotient, by saturation and the
semiconjugacy. The model contour of its selected terminal
branch lands in the closure of that branch. At the preperiodic
cut α^h the fiber is a singleton; the one-cut component
correspondence of CUTPOINT_PRUNING identifies the inverse of
that closed branch as a subset of the actual C_h. The
impression formula then supplies the required locality for
the inverse image of that model contour, including its cut
ends. These statements concern the actual topological contour
of the saturated carrier. They do not identify it with the
printed unrestricted maximal-subset immersion action, which
the [canonical-localization counterexample](../issue40_canonical_localization_uniqueness_failure_20261124.md)
shows is a separate problem. For an independently specified
native carrier the same saturated-model identification must
be verified, not assumed.

An alternative sufficient locality certificate is an actual
pair of disjoint crosscuts of U^h minus T_h, from distinct
outer ideal points to the two accesses of the selected
preperiodic cut. The closure of the intervening component
must meet T_h only in Γ_h(C_h). Every ideal access strictly
between the two inner cut ends has its impression in that
closure (in annular coordinates the component contains a
neighborhood of that open ideal interval). The two gate
accesses themselves can be discarded at zero parent width
if necessary: put the finite-energy logarithmic point
singularity of the exceptional-width note at the ideal
point in annular coordinates, transport it into U^h, and
push it to U by the same all-sheet square sum. Any actual
lift landing there has infinite pushed length. Finitely or
countably many such gates are negligible by subadditivity.
This avoids inferring singleton impressions merely from
the existence of a planar root.

The source's line 1600 still needs to supply an actual
restriction ending in this contour (or an independent physical
encounter). The preceding implication does not construct that
restriction from untagged sequential Wave outputs. In particular
no unsupported one-shot/sequential equality is used.

## 5. How to certify the remaining one-step response

The variational target is now a *single* normalized
three-conductor energy on U:

\[
 \boxed{\mathfrak S(F)\le C_b\,(R(F)+V(F)+1).}
 \tag{12}
\]

Here R(F)=W(RF) and V(F)=W(U minus T). If (12) and actual
deep encounters modulo zero hold, (5) supplies the needed
O_b(R+V+1) terminal charge. In the physically typed
outside-end subclass (11) the coefficient need not be
exponential in b. A separate relative telescope, and any
required response/terminality transfer, remain independent.
No QSDB or global ledger status is promoted.

An explicit blockwise sufficient certificate for (12) is
available in disk coordinates. Suppose there is a center a
and radii 0<r<R0 with C_1 contained in the closed disk of
radius r, and the closed disk of radius R0 compactly
contained in U minus Z. The logarithmic potential, one up
to r and zero beyond R0, gives

\[
 \mathfrak S(F)\le 2\pi/\log(R0/r).
 \tag{13}
\]

Approximate by smooth cutoffs with the required neighborhoods:
enlarge the inner radius and shrink the outer slightly,
smooth the radial transitions and take their energy limit.
Thus e.g. R0/r≥1+η gives a uniform finite bound.
If no single enclosing disk works, let δ be the distance
from C_1 to Z union ∂U and let d be its diameter in a fixed
disk coordinate. For every sufficiently small ε>0 the
distance cutoff that equals one within ε of C_1, decreases
linearly to zero at distance δ/2−ε, and vanishes beyond
has Lipschitz constant 1/(δ/2−2ε). Convolve with a smooth
positive approximate identity of radius smaller than ε;
this preserves the electrode neighborhoods, and Jensen's
inequality for the weak gradient does not increase energy.
Its support before convolution is in a disk of radius
d+δ/2 about any point of C_1. Letting ε↓0 yields

\[
 \mathfrak S(F)\le \pi(1+2d/\delta)^2 .
 \tag{14}
\]

This gives a scale-relative geometric acceptance test for
the base pair, not a uniform bound on its ratio. Neither the
source's qualitative inverse-branch neighborhood nor its
occupancy bound establishes (12), (13) with fixed η, or
uniform control of d/δ. The prior fixed-final-surface rectangle
countermodel prevents promoting general qualitative clearance
to a linear width bound, but it has no native critical-limb
dynamics and does not refute (12).

## 6. Exact verification scope

The separate Lean finite layer verifies critical-stay recovery,
bounded exit from the forbidden inverse nest, prefix cancellation
and deep-hit membership, the geometric series budget, and
quadratic endpoint index weight inequalities. The companion
exact arithmetic regression enumerates finite partial-inverse
models and tests the sharp weights. A total inverse branch
on a finite invariant critical set would be a permutation,
so a strictly shrinking native nest cannot be inferred from
such a finite model; the discrete enumeration tests the
implication only.

The actual conformal energy identity, first-exit argument,
source-contour locality and variational calibration criteria
are written mathematical reasoning. No new proof of the
native line-1600 encounter assertion, uniform bound (12),
stationary telescope, H1–H4, UPTCR or MLC is claimed.
Prepared with ChatGPT assistance; specialist review remains pending.
