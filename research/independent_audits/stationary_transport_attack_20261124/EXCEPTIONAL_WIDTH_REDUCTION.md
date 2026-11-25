# Simultaneous finite-length core and the carrier-edge residual

2026-11-25. Written modulus argument continuing
[ONE_HIT_LANDING_REDUCTION.md](ONE_HIT_LANDING_REDUCTION.md) and
[VARIABLE_END_EXIT_TRANSFER.md](VARIABLE_END_EXIT_TRANSFER.md).
The objective is to isolate the exceptional *geometric* family, not
declare that family negligible. No change to the canonical ledger.

## 1. One finite-energy metric controls all raw lifts

Let i:S→U be a holomorphic immersion between hyperbolic disks, and
let H_1,...,H_k be pairwise disjoint nondegenerate full continua compactly
contained in S. Work in Riemann-map coordinates S=U=D; i is now a
disk-valued holomorphic map with nowhere-zero derivative. Let X_f be
the complement of the H_j in S. In the target use any Borel family
of simple proper parents in an open subdomain X of U (for the native
application X=U minus the full carrier T). Width is 2-modulus, the
infimum of area of admissible nonnegative Borel conformal densities.

Choose pairwise disjoint Jordan neighborhoods E_j compactly contained
in S of the H_j. By the exterior Riemann map construction in §6.1 of
[the exit-transfer note](../maximal_exit_transfer_20261123/NOTE.md),
E_j minus H_j is a finite annulus, with its inner ideal circle the
same as that in X_f. Uniformize it conformally by g_j onto a round
annulus contained in D. On the entire source disk define

\[
 \lambda(z)=1+\sum_{j=1}^k {\bf1}_{E_j\setminus H_j}(z)|g'_j(z)|.
\]

The indicator is zero off the indicated open collar; no derivative
at an ideal boundary is used. This positive density is lower
semicontinuous. By disjointness of the collars and conformal area
change,

\[
 \int_S\lambda^2\,dA
 \le 2\,\mathrm{area}(S)
   +2\sum_j\mathrm{area}(g_j(E_j\setminus H_j))
 \le 2\pi(1+k).
 \tag{1}
\]

On the entire target disk define the all-sheet square-sum density

\[
 \rho(w)=1+
  \left(\sum_{z\in i^{-1}(w)}
       \frac{\lambda(z)^2}{|i'(z)|^2}\right)^{1/2}.
 \tag{2}
\]

Fibers are discrete and countable; they need not be finite or uniformly
bounded. The square-sum is lower semicontinuous: for any finite
subsum at w, use pairwise disjoint local inverse charts around its
preimages to continue the summands near w, and take the supremum over
finite subsums. The value +∞ is permitted. Alternatively measurability
follows by a countable Borel partition subordinate to injective
inverse charts. Change of variables on that partition and Tonelli
give the exact area identity for the square-sum in (2), without counting
any source point twice. Thus

\[
 \int_U \rho^2\,dA\le 2\pi+2\int_S\lambda^2\,dA
 \le (6+4k)\pi.
 \tag{3}
\]

For any locally rectifiable parent α and any actual lift σ on any
interval J of parent times, local inverse charts give local
rectifiability and the conformal line-integral identity. The summand
of (2) at σ(t) yields

\[
 \ell_\lambda(\sigma|_J)\le \ell_\rho(\alpha|_J)
 \le \ell_\rho(\alpha).
 \tag{4}
\]

Exhaust by compact subintervals if the lengths are improper.
Nonrectifiable parent subpaths already have infinite ρ-length
because ρ≥1. In particular no choice of a preferred lift, measurable
selection, or global injectivity of i enters (4).

Let Z be the subfamily of parents of infinite ρ-length. For every
ε>0, ερ restricted to X is admissible for Z, with area at most
ε²(6+4k)π. Hence W_X(Z)=0. This is a conformal-modulus statement,
not a statement about a chosen transverse measure.

For the Borel path presentation, length for a positive lower
semicontinuous density is a Borel function on compact path pieces:
approximate the density from below by positive continuous
densities, take their increasing weighted lengths (lower
semicontinuous in the uniform path topology), and take the
supremum over a countable compact exhaustion of the parameter
interval. The continuous-density length assertion follows from
the ordinary metric-length partition formula on compact
neighborhoods (or by lower sums of density times increments);
nonrectifiable pieces have infinite length since the density
has a positive lower bound. Thus the rectifiable finite-ρ core
and Z are Borel in the archive's Borel leaf atlas. The null
statement itself does not require this extra Borel assertion.

### Consequences

Every parent outside Z has finite disk-coordinate length and
therefore a physical limit in the closed target disk at both ends.
Every one of its actual lifts, whether punctured or unpunctured,
has finite λ-length and hence a unique disk-coordinate limit at each
end of its lifetime. This includes all competing lifts simultaneously.

For a maximal unpunctured lift, a finite interior-time endpoint
cannot have a limit in S: the local inverse chart there extends
the lifetime. If its limit is on ∂S, it is an actual ambient outer
ideal point, also an outer ideal point in X_f.

For a maximal punctured lift with physical endpoint on H_j, the
tail lies in E_j minus H_j. Inequality (4) gives finite
g_j-coordinate length on that tail; it converges in the closed
round annulus to its inner ideal circle, not to an interior point
or the outer collar boundary. Thus physical landing on H_j
produces actual ideal landing. A lift whose endpoint at an original
parent endpoint is in the interior of X_f is *not* made proper
by this argument. This distinction is the remaining obstruction.

The same construction works simultaneously for countably many
immersions into a fixed target disk and their respective finite
deleted-continuum packages. If ρ_n is the density (2) for package n,
use ρ_* = sum_n 2^(-n-1) ρ_n/(1+||ρ_n||_2), for n=0,1,...
The L² triangle inequality gives finite energy, and finite
ρ_*-length forces finite ρ_n-length for every n. The sum is lower
semicontinuous and a single zero-width exception suffices. This
does not construct a compatible infinite tower or identify its
marks.

The archive already removes infinite Euclidean length parents in
[the N1 rectifiable-core argument](../../mlc_unified/kkl_stationary_n1_dl_relative_discard_bound_frozen_audit_20260726.md).
Its [multicurve comparison](../../mlc_unified/terminal_dense_obstacle_and_submulticurve_replacement.md)
also uses all-sheet metric pushforward. The extra point here is
the common finite-energy envelope for the parent, *every* raw
unpunctured lift, and all its final ideal collar lengths. It
gives an alternative modulo-zero argument, not a replacement
for the earlier pointwise landing theorems.

## 2. The exact remaining exceptional geometry after a bank hit

Use the filled-set assumptions of the one-hit note: compact C⊂S
and K⊂U with i^(-1)(K)=C, i|C a homeomorphism onto K, and every
H_j contained in C. Assume T⊂K is an actual full carrier
containing the original little Julia cycle. Parents are proper
in U minus T.

Work outside Z of §1. Each parent endpoint physically lands either
on T or on the ambient outer circle. Indeed a limit in U minus T
would contradict parent properness.

Let C_bank be a chosen subset of the H_j. Suppose a parent hits
i(Q) at some interior time for Q∈C_bank, but has no actual eligible
maximal X_f exit incident to any member of the bank. Start the
canonical unpunctured lift at that hit.

* A second hit in a different H_j would give an inner-to-inner
  exit using the last Q hit and first different-component hit.
  The collar finite-length limits in §1 prove ideal properness.
* If the unpunctured lifetime stops at a finite interior parent
  time in either direction, §1 supplies an outer limit. Its
  last Q hit in that direction exists by compact escape. If it
  hits no other H_j first, the last Q departure to the outer
  limit is a proper inner-to-outer exit. Both possibilities
  contradict failure.
* Hence the unpunctured lift continues over the entire open
  parent interval. Neither endpoint can lie on the outer
  ambient circle: continuity of i in S would force an interior
  image at an interior source limit, so the lift would escape,
  yielding the same eligible exit.
* Both parent endpoints therefore lie on T⊂K. A source outer
  limit would again give an eligible exit. The remaining
  interior source limits equal the unique filled-graph
  preimages of these endpoints. If either belonged to a
  different H_j, the last departure from Q would give an
  eligible exit. Thus both endpoints lie outside
  i(union_{H_j≠Q} H_j). Along the full lift there are also
  no interior hits in any of those other continua.

Full continuation and filled-set bijectivity further show that
the parent itself never hits any i(H_j) with H_j≠Q at an
interior time. The conclusions apply in particular to any
actual bank hit, not only to a selected tagged occurrence.

For the high-type native predecessor bank b≤n<m<P, §2 of the
one-hit note proves that bank members are disjoint from the
original cycle and that its canonical graph lifts belong to
different final components. Consequently the residual after a
bank hit has *both* physical endpoints in

\[
 T\setminus\mathcal K,\qquad \mathcal K=\bigcup_j K_j,
\]

and no hit on the image of any final deleted component different
from its hit bank member. This is a necessary condition for
failure, not an equivalence about all possible competing lifts.
In particular the argument does not construct a bank hit for a
retained parent that has none.

If the relevant Borel family of residual leaves is D and the
good family is G, the previous Borel atlas and bank accounting give

\[
 W(A_m)\le W(G)+W(D)\le 2r W(RF)+W(D).
 \tag{5}
\]

The zero-width Z has already been discarded. Formula (5) remains
valid with the original infinite-width convention by subadditivity;
when W(D)=0 it recovers the desired terminal bound. The new
reduction permits the residual to be bounded by a family of
no-hit parents together with parents having both carrier-only
ends and at most one deleted-component hit. It does not show
that either family is negligible.

### A useful narrower exception: countably many physical gates

If actual native geometry restricts either physical endpoint of
some residual family to a specified countable set of points in
the closed ambient disk, that subfamily has width zero. For a
single point p use the density
\(\tau_p(z)={\bf1}_{0<|z-p|<e^{-1}}/(|z-p|\log(1/|z-p|))\).
Its squared area on the plane punctured disk is at most
\(2\pi\int_0^{e^{-1}}dr/(r\log^2(1/r))=2\pi\).
Any nonconstant rectifiable path approaching p has infinite
τ_p-length by radial variation, since
\(\int_0^{r_0}dr/(r\log(1/r))=\infty\).
Nonrectifiable parents may first be removed by §1. Scaling the
density to arbitrarily small area proves zero width for that
point; countable subadditivity gives the claim. For points in
the carrier the density is used only on the ambient open
complement. A countable set of *ideal* endpoints is handled
in the uniformized target annulus by the same argument.
No assertion is made about general angular measure-zero or
uncountable endpoint sets.

## 3. Positive-width obstruction to deleting all carrier-only ends

Strengthen §3 of the one-hit note from one leaf to a whole
rectangular lamination. Take S=U={|z|<5}, i the identity,
C=K={|z|≤4}, Q={|z|≤1/2}, and H={|z−3|≤1/4}. Let the full
carrier T consist of H, the three sides of the polygonal U-shaped
arc with consecutive vertices (−1,−1),(−1,1),(1,1),(1,−1),
and the branch from (1,1) to (3,1) to (3,1/4).
This is a compact full continuum: a disk with a finite embedded
tree attached at one point, which creates no closed complementary
cycle. It is disjoint from Q. For every y in [−1/4,1/4], take
the horizontal open segment

\[
 \alpha_y=\{x+iy:-1<x<1\}.
\]

The two endpoint accesses are ordinary side accesses to the
vertical carrier edges, and the paths are simple, proper,
mutually disjoint and Borel presented in U minus T. They all
hit Q and never hit H. In the final surface S minus (Q union H)
their maximal restrictions are two open segments separated
by Q. Each has one Q ideal end and one endpoint lying in the
interior of the final surface. None is an eligible proper exit.

Their full extremal width in U minus T is exactly 1/4.
For any admissible density f, each horizontal line has
\(\int_{-1}^1 f(x+iy)\,dx\ge1\). Cauchy–Schwarz gives
\(\int_{-1}^1 f(x+iy)^2\,dx\ge1/2\).
Integrating over the height 1/2 yields area at least 1/4.
Conversely the density 1/2 on the width-2, height-1/2
rectangle and zero outside is admissible with area 1/4.
All computations here are exact; the width is the modulus
of the actual continuum of leaves, not a discrete sample.

This planar example is not a primitive quadratic dynamical
or KKL stationary counterexample. It refutes only a generic
inference that all carrier-edge endpoint failures are width-zero
from the continuum, immersion and proper-parent hypotheses.
A genuine native argument must use more dynamics or a separate
quantitative width bound.

## 4. Next native target

For the actual retained stationary Waves, prove that no-hit
parents and the above one-component, carrier-only residual
have a sufficiently small combined width, or force genuine
additional physical hits/eligible exits. In particular
countability of their possible gates would be sufficient
for the corresponding landing subfamily, but countability
is not established by the archive's finite abstract contour
labels. Full pass-through, native marking retention, H1–H4,
UPTCR and MLC remain open.

Prepared with ChatGPT assistance. The finite-energy and
rectangle arguments are written proofs, not Lean-verified
analysis or human specialist review.
