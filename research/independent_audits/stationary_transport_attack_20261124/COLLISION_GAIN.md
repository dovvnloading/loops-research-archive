# Multiplicative retained-collision gain along complete stationary chains

2026-11-25. This is a metric response theorem for actual simple
retained chains, continuing [CANONICAL_LIFT_AND_DIRECTION.md](CANONICAL_LIFT_AND_DIRECTION.md)
and [SYMMETRIC_SEPARATOR.md](SYMMETRIC_SEPARATOR.md). It converts
some deck collisions into strict width amplification rather than
requiring their exclusion. The native frequency of the collisions
and the complete repaired marking remain open.

## 1. All-path metric estimate with disjoint windows

Use the actual finite Kahn tower I_h,P_h:U^h→U, T_h=P_h^(-1)(T)
and X_h=U^h minus T_h, X=U minus T, under the annular
properness and filled-graph hypotheses of the canonical-lift
note. P_h:X_h→X is a degree 2^h covering. Suppose every
simple parent α in a family A contains r pairwise
parameter-disjoint open subarcs, each with an actual lift
Θ in X_h whose P_h image is an entire member of an output
family D. No choice of a preferred witness, univalent global
immersion, or injectivity of the output family is assumed.
The number r≥1 is a uniform integer lower bound.

Then

\[
 \boxed{W_X(A)\le {2^h\over r^2}\,W_X(D).} \tag{1}
\]

Proof. Given an admissible conformal metric ρ for D, pull it
back by P_h. Its squared area on X_h is exactly 2^h times
the area on X, by finite covering area change. Push this
metric to X by the all-sheet square-sum rule for I_h,
as in EXCEPTIONAL_WIDTH_REDUCTION, §1. The squared area
does not increase, and the length of each chosen literal
parent window is at least the length of its lifted
subpath in the pulled metric, hence at least one. The
windows are disjoint in time, so the parent length is at
least r. Divide the pushed metric by r and take the
infimum over admissible metrics. If necessary first
remove nonrectifiable parent paths at zero width using
constant densities in the disk coordinate. The resulting
inequality also follows by adding a vanishing positive
constant to the divided metric. QED.

The factor r² comes from length addition followed by
quadratic area scaling. It is not a factor for the
number of tagged paths counted without actual disjoint
windows. The elementary two-rectangle series example
is sharp for this algebra: a horizontal rectangle
of length 2 and height H has width H/2; each of its
two length-one halves maps by translation to the same
unit-length target rectangle of height H. The energy
cost of the two copies is 2 and both half-lengths add.
This is an abstract flat metric example, not a native
global cover.

## 2. Multiplication of actual windows

Suppose α has a stationary chain of simple proper
inner-ended singleton outputs δ_0=α,...,δ_h, in the
geometric retained-component interpretation. Work
outside the zero-width finite-length exception and
the incomplete canonical-lift family E_h of Theorem 1
of CANONICAL_LIFT_AND_DIRECTION. The latter has width
at most 2^h V(F).

At stage j, let r_j be the number of distinct retained
maximal simple inner-ended restrictions of δ_(j-1)
whose f-image is the entire δ_j. Unbreakability
ensures r_j≥1, and the degree-two cover gives r_j≤2:
evaluation at a fixed interior point of δ_j distinguishes
lifts in its two-point covering fiber.

Completeness of the parent at h gives a complete
unpunctured canonical one-step lift of every δ_(j-1).
Indeed reconstruct any earlier occurrence window using
the segmented-prefix theorem, identify its prefix lift
with the canonical lift by Theorem 2 of the canonical
note, and restrict the next coordinate of the complete
tower lift to that closed window. The commuting equations
give its I_1 projection equal to the entire δ_(j-1).
At each endpoint its image is the actual physical
landing in T. The filled-set inverse identity forces
the canonical one-step initial and terminal points.
Local lifting uniqueness gives the claimed complete
one-step lift. All such output paths are rectifiable
if α has finite length: the finite chart continuation
over a compact lifted path gives finite length, and
each holomorphic projection is locally Lipschitz there.

Hence every retained inner-ended one-step restriction
is a gap on the same complete canonical one-step lift.
Different retained restrictions occupy disjoint open
time windows, by Theorem 2 of the canonical note.
There may be remote outer-ended restrictions, but the
present r_j does not count them.

Starting with the whole parent window, subdivide each
chosen stage-(j-1) occurrence into the r_j preimages
of the actual one-step windows of δ_(j-1). Each preceding
parametrization of δ_(j-1) is a homeomorphism onto its
occurrence window because the output is simple. Thus
the child windows are open, nonempty, pairwise disjoint
within that parent, and disjoint across different
parents. The segmented reconstruction gives an actual
Θ_j in U^j for every resulting finite window, with
P_j projection the full δ_j. Its interior is in X_j
because δ_j avoids T. Properness of earlier truncated
coordinates is not needed. Repeating through h gives

\[
 R_h(\alpha)=\prod_{j=1}^h r_j(\alpha)
\]

pairwise time-disjoint windows witnessing the SAME
full singleton output δ_h. This is a product of actual
window multiplicities, not a product of unconstrained
covering degrees. For h=0 use the empty product one.

In particular, if a complete family A has at least k
stages with two retained restrictions for every parent,
then by (1)

\[
 \boxed{W(A)\le 2^{h-2k} W(D_h),} \tag{2}
\]

where D_h is the union of the actual full output paths.
The inequality holds for arbitrary such curve families,
even if different parents have identical outputs or D_h
is not a lamination. If an actual native output Wave
containing D_h has been supplied, its width is at least
W(D_h). If the family has not been restricted to complete
parents, the additional error 2^h V(F) suffices by
subadditivity. The kernel does not prove the geometric
multiplicity assumptions.

## 3. Quantitative response thresholds

For a complete subfamily S of an ambient family A with
W(S)≥η W(A)>0, suppose it has at least k duplicate stages
through horizon h. If its full singleton output family
is contained in one actually realized controllable Wave
C, (2) gives

\[
 W(C)\ge 2^{2k-h}\eta W(A).
\]

Thus strict gain by a factor at least λ>1 follows once

\[
 2^{2k-h}\eta\ge\lambda. \tag{3}
\]

For all parents in the complete family (η=1), any
2k>h gives at least a factor two. A sufficient integer
threshold for an arbitrary η is
k≥ceil((h+log_2(λ/η))/2), if this does not exceed h.
The width response does not invoke the false broad
coefficient-one Wave lemma. It still requires the
actual Wave containment and controllability certificate
for C before being called native terminality.

For example, if the original family A has at least a
fraction η of its width in an actual collision-rich
subfamily before the complete-lift restriction, the
complete part has width at least ηW(A)-2^h V by
subadditivity. The resulting response is
W(C)≥2^(2k-h)(ηW(A)-2^h V), provided C contains the
actual outputs of that complete subfamily. No general
modulus additivity is being used. A negative lower
bound makes no gain claim.

More generally partition by first certified response
horizon j and an integer k_j such that the chosen
complete subfamily A_j has at least k_j double stages
in that prefix. Then

\[
 W(\bigcup_j A_j)\le\sum_j 2^{j-2k_j}W(D_j). \tag{4}
\]

This follows from subadditivity, and does not require
a Borel choice of a unique lift. If the union has width
at least η W(A)>0 and every D_j is contained in a
genuine output Wave C_j, then some C_j has width at
least η W(A)/(sum_j 2^(j-2k_j)), assuming the finite
index list is nonempty. It is not enough to show only
that every parent has some stage with two lifts:
the degree cost and the widths of all output families
are essential.

## 4. A geometric sufficient test for a duplicate stage

Use the one-step complete lift θ and actual annular
covering of CANONICAL_LIFT_AND_DIRECTION, §4. Suppose
there are two inner ideal accesses e_1 and e_2 with
e_2=τ_*(e_1), where τ is the actual degree-two deck
involution. Suppose both accesses lie in protected
blocks satisfying conditions 1–3 of that section
(for the same full parent cap), and the singleton
output satisfies condition 4, with a proper disk-cap
base. These blocks can be different; neither is
assumed to consist of just one atom.

The signed-crossing theorem gives a unique positively
oriented retained component with each e_i in its
base. They cannot be the same component: its base
maps homeomorphically to the proper output base,
whereas f_*(e_1)=f_*(e_2) and e_1≠e_2. Thus there
are exactly two retained components, and their
parameter windows are disjoint by complete-lift
exhaustion. Both map to the same singleton output.
This is the actual r_j=2 certificate, not a
claim that a selected pair of symbolic endpoints
must produce different output paths.

The antipodal separator hosts of SYMMETRIC_SEPARATOR
are geometrically distinguished, but they need NOT
be protected blocks in the sense needed here.
In particular an entire added branch can lie inside
one coarse attachment fiber; its raw paths may be
filtered. The host theorem alone does not establish
a duplicate stage. A concrete sufficient follow-up
is to find two deck-opposed whole protected atom
blocks, one in each lifted cap packet, for the
actual stationary parent. At most one of the two
may be needed for direction recovery, but both
are required for this gain certificate.

This narrows a second alternative to the unresolved
free-condenser bound: demonstrate that the remaining
edge-end stationary family has enough actual
duplicate stages, or produces large output width
at a suitable prefix. The finite gain estimate
then gives a response with no noncollision premise.
A single duplicate late in a long chain does not
by itself imply ambient amplification.

## 5. Verification boundary

StationaryDeckSeparator.lean formalizes the real
interval fixed-point step, abstract retraction
separation, degree/multiplicity energy inequality,
doubling exponent and finite response algebra.
The conformal area and length argument, the actual
fiber-product reconstruction, and the native
marking/anchor hypotheses are written mathematics.
The finite regressions test products, thresholds,
and the symmetric narrow-gap obstruction. No
native duplication frequency, uniform free
response, stationary closure or MLC is asserted.

Prepared with ChatGPT assistance; specialist review pending.
