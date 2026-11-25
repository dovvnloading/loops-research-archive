# Proper middle graph-side ancestry and the remaining angular margin

This is a source-facing supplement to
[ASYMMETRIC_BANK_GAP](ASYMMETRIC_BANK_GAP.md). It isolates a sufficient
native certificate for the marked subdivision factor S=1, and states
exactly which quantitative condition remains if that certificate is
verified. No independent source-wide contour identification or angular
margin bound is claimed.

The source-locked inputs used here are the vertex/contact description
in [the marked realization audit](../issue40_native_marked_realization_local_gates_20261124.md)
sections 1--2 and the component equality of the proper middle corridor
recorded in [the occupancy audit](../../mlc_unified/kkl_virtual_occupancy_source_audit.md)
and [the retained-realization audit](../../mlc_unified/kkl_stationary_retained_realization_source_audit.md).
The live v1 arXiv HTML and PDF mirror were not retrievable in this
session; the following is a mathematical implication of the explicit
hypotheses, not a newly verified verbatim reading of the source.

## 1. Exact graph-side hypotheses

Use the actual saturated model dendrite K_model, its full minimal hull
A of the original little Julia cycle, and the actual degree-two planar
model map Q, with B=Q^(-1)(A). Retain the monotone physical/model
prime-end covering square and the corrected geometric contour action.

For one noncritical open limb Omega_j in the proper-middle range
BL_[b,q-b-2], require these source-specific facts:

(G1) Q maps its closed limb (including the dividing fixed point alpha)
homeomorphically, with orientation inherited from the actual unbranched
planar map away from alpha, to the next closed limb. Its restriction
maps B intersect that limb onto A intersect the next limb; B and A
agree in this old closed limb. The open limb ideal blocks and their
dividing-cut endpoints agree with the exact geometric marking; the
boundary covering is injective on the old-proper pulled limb block.

(G2) Each complete inverse component of an original target little
Julia vertex in this old open limb is an original whole little Julia
vertex. Conversely the original cycle maps forward to the original
cycle, and every target whole little vertex in the next open limb
has its full inverse there. This is the component assertion used in
the source proper-middle argument, stronger than the mere assertion
that the old and pulled hulls have equal underlying sets.

(G3) The original graph-side marking is exactly the access-complete
marking at the finitely many little-vertex contacts and singleton
graph vertices: the latter, away from the little bodies, are the
intrinsic branch vertices of the minimal hull and the dividing point.
If any additional valence-two or orbit-labelled subdivision vertices
are included, require their exact forward and backward correspondence
on this limb as well. No arbitrary extra preperiodic cuts are added.
For a model marked landing every actual access over it is in the
marking, and the saturated physical/model prime-end correspondence
has a singleton fiber over each such marked access, as in the
source-locked marked realization audit.

These are sufficient hypotheses. In particular a bare topological
translation of limb *labels* or a forward-invariant marking cut set
alone does not imply (G2) or the backward cut completeness in (G3).

## 2. Atom-to-atom conclusion under these hypotheses

**Proposition.** Under (G1)--(G3) every original open marking atom
in the proper noncritical limb has exactly one pulled fine atom in
its geometric coarse pullback, and its actual boundary-covering
image is exactly one original atom in the next limb. The same holds
for any finite sequence remaining in the proper-middle range.

Proof. By (G1), Q induces a homeomorphism from the entire old model
hull in the closed limb onto the entire target model hull in the
next closed limb. By (G2) it maps the family of original whole
little bodies bijectively to the target family of whole little
bodies. Therefore removing or collapsing those distinguished
vertex bodies gives the same finite connecting graph on either
side, with a graph homeomorphism preserving incidence.

For a little body L in the open limb, its contact set is
L intersect closure(A minus L). The local topology near L is
entirely in the open limb; the homeomorphism of the hull and of
the distinguished bodies maps this set exactly to the contact
set of Q(L), not merely into it. Intrinsic branch vertices off
the bodies are characterized by the number of incident arms of
the hull and are mapped bijectively as well. The dividing point
and its incident sides at the two limiting cuts are already
matched by (G1). Any other graph subdivisions are matched by
the extra condition in (G3). This proves equality of the marked
landing inventories on these open limbs.

For the **access** inventory, use the actual orientation-preserving
local plane homeomorphism of Q at each marked point in the open
noncritical limb. The actual pulled hull agrees with the old
hull in a neighborhood of that point, by (G1) and the open-limb
locality. The local map identifies the full set of side accesses
to that marked point in the source hull with the corresponding
target accesses. Equivalently, use the actual boundary covering
on the pulled inner circle: it is injective on this limb block,
and each target marked access has one preimage there, whose model
landing is the corresponding old marked point just proved. The
access-completeness in (G3) marks that preimage. Thus every target
marking cut lifts to a coarse old cut, and every old cut maps to
a target cut. The limiting dividing cuts have the actual
specified matching accesses by (G1). The physical marked
accesses correspond by the singleton fibers and the commuting
actual covering square of (G3); no numerical conformal width
identity is claimed for the model map.

Hence the fine cut set of the covering on the old-proper limb
is precisely the geometric coarse cut set. A connected open
atom between consecutive coarse cuts therefore contains no
additional fine cut and maps homeomorphically onto one original
target atom. Repeating within the proper range and using the
actual full-tower chart compatibility proves the finite-iterate
claim. QED.

This proof checks backward incidence, not just forward cut
invariance. For example, if an extra target subdivision is
inserted in the interior of an edge but the corresponding
preimage point is not an old cut, an old atom will map to
multiple atoms despite the same underlying graph homeomorphism.
That is excluded by the exact graph-side hypothesis (G3), not
by properness alone.

## 3. Consequence for the asymmetric expansion-gap test

Use c=2b+20, h=b+2, H=h+2, t=H+2,
B=BL_[-c,c], B^+=BL_[-c,c+t], as in ASYMMETRIC_BANK_GAP.
In the high-type range q>=2(c+t)+4, if the minimizing atom
of B^+ belongs to B the gap is at most C_env already.
Otherwise it lies in limb k=c+r with 1<=r<=t.
The bounded proper backward chart of that note translates
the full old band BL_[b,q-b-1-r] to
BL_[b+r,q-b-1]. When (G1)--(G3) are verified at each
step, the old marked ancestor in BL_c is one whole
original atom whose image is exactly the minimizing
target atom. Thus S=1 and the previous bound becomes

    Delta_+ <= C_env + log(16)/pi + 6 V + log(1/G)/pi,

where G is the minimum of the two actual conformal angular
distances from the midpoint of that target atom to the
limiting dividing cuts of BL_[b+r,q-b-1].
All distances are in the normalized original annulus,
not model external angles or counts of marked atoms.

Consequently the conditional fixed-control width theorem
of ASYMMETRIC_BANK_GAP would follow at the required
absolute scale from the remaining quantitative bound

    log(1/G) <= C_b (R+V+1)

on this one bounded actual chart, together with the
standing geometric and initial witness hypotheses.
The graph-side argument does not supply this bound.

If G is small, the left or right margin contains the
whole old-bank limb BL_c or BL_(q-c), respectively.
The explicit radial witness over that whole limb then
has width >=log_+(2s/G)/pi, s=min(1/4,M_X/2).
This is an actual near-bank nonshort witness, not an
unmarked path or symbolic entropy estimate. It supplies
the relative bound

    Delta_+ <= M_B + C_env + O(V+1)

under (G1)--(G3), but does not give the absolute
margin charge required to remove Delta_+ from the
strict anchored comparison. A further native argument
must turn the extreme-margin witness into a charge
or width response, or directly estimate the margin.
No such argument is claimed here.

## 4. Acceptance checks

On the actual proper-middle graph the following checks
are now separate and falsifiable:

* match complete original and inverse little Julia bodies
  in each used noncritical limb, not just their occupancy;
* match all original singleton vertices, vertex-contact
  points, and access tags in both directions, including
  any extra marked subdivisions;
* verify the actual old-proper full-chart correspondence;
* measure the two conformal angular margins of the
  minimizing atom in the bounded positive strip, and
  prove the needed absolute logarithmic margin estimate.

The first three are the precise sufficient atom-ancestry
certificate proved above. The fourth is still open here.
The source's unrestricted literal A.3.2 operation is not
reinstated, and the other saturated-carrier and two-bank
geometric and downstream hypotheses from the preceding
notes remain explicit. This is a conditional geometric
proof, with independent specialist review pending, not a
ledger promotion, native stationary closure or MLC proof.
AI-assisted written mathematics.
