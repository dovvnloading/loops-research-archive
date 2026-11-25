# Degree-independent sector confinement and finite phase assembly

Continuation of [COHERENT_PACKET_GAIN](COHERENT_PACKET_GAIN.md),
[AWAY_ENDPOINT_SHIFT](AWAY_ENDPOINT_SHIFT.md), and
[AMBIENT_SHARED_CREST_RESPONSE](AMBIENT_SHARED_CREST_RESPONSE.md).

**New result.** Actual covering-image intersections between a bounded
number of anchored packets can be removed at an explicit bounded
width cost. The only possibly large loss in the construction is a
quantified choice between different covering phases of the same
directed target endpoint-cell pair. This is a sufficient replacement
theorem for compatible sectors, and a reduction of the general
multi-packet problem to a finite phase deficit. It is not a theorem
that this deficit is always small in native KKL dynamics.

Use width W=2-modulus, conformal metrics, and the actual Borel
lamination and disjoint-support additivity conventions of the
preceding notes. The elementary annular statements below do not
require any dynamical marking.

## 1. Two uniform radial tests

In the upper half-plane fix a real center e and radius r>0.
Put the density 1/|z-e| on the closed half-annulus

    r/2 <= |z-e| <= 2r

and zero elsewhere. Divide it by log 2. Its area is

    c_* = pi log(4)/(log 2)^2 = 2pi/log 2.

Consider a simple proper path with real ideal endpoints x_-<e<x_+.
Either of these conditions is sufficient for metric length >=1:

(A) at least one endpoint has distance <=r from e, and the
    supremum of the path radius is >=r;

(B) both endpoints have distance >=r from e, and the
    infimum of the path radius is <=r.

For (A), if the path enters radius <r/2, radial variation to
radius >=r supplies log 2. If it reaches radius >2r, start
from the endpoint of radius <=r and use the traversal of
[r,2r]. Otherwise it stays in the support and its continuous
argument in (0,pi) changes by pi. For (B), if it enters
radius <r/2, start from either endpoint of radius >=r.
If it reaches radius >2r, use a traversal between that
point and a point of radius <=r. Otherwise angular variation
again gives pi. Suprema, infima and equality cases use
compact exhaustion; no monotonicity of a trace is assumed.
All radial and angular length comparisons are before
division by log 2.

These tests apply on any universal annular strip by restricting
the metric to the strip and pushing it through its covering
by all-sheet square-sum. Its area does not increase, and it
dominates the length of the chosen lift. Nonrectifiable
curves can be handled by a vanishing positive constant in
the finite-area cylinder. Put

    L_* = 2c_* = 4pi/log 2.

## 2. Uniform confinement to an arbitrarily narrow covering sector

Let Y be the normalized cylinder (R/Z)x(0,M_Y), and
p:Y→X an actual degree-d annular covering. In the universal
strip p scales both coordinates by d, up to angular
translation. Let J=(l,u) be one lifted angular interval of
length <=1/d, and e in J a fixed anchor. Let B be a packet
of simple proper inner-ended crosscuts whose actual oriented
disk-cap bases contain e and have their two endpoints
strictly in J, with the indicated lift (not the opposite
long cap route).

**Sector confinement theorem.** Discarding width at most L_*
makes every path lie in the open vertical slab
J x (0,M_Y) of this chosen lift. The discarded bound is
independent of d, u-l, M_Y, and the distances of e to the
two sides.

Indeed a path hitting or crossing the line x=l reaches
radius >=e-l from e. Its left endpoint, being in J and
left of e, has radius <=e-l. Apply test (A) with r=e-l.
The same test with r=u-e handles hitting the other side.
Use subadditivity and push down the two metrics.
All remaining traces are in the slab, on which the
composite strip-to-X covering is injective: horizontal
separations are strictly less than 1/d. Their base arcs
also map injectively, including the endpoints which lie
strictly inside the interval. Hence each output is a
simple proper inner-ended crosscut with a proper disk cap.

More generally, for a finite collection of sectors on
whose union the boundary covering is injective, the
covering is injective on the union of their open slabs.
The theorem applied to m fixed-anchor packets in those
sectors costs <=m L_*, even when the different packets
approach the sector ends at arbitrarily small angular
scales. No lower bound on the unused angular margin
is needed.

For the actual immersion I and selected raw gaps of
disjoint simple parents, push the bad metric through I
by square-sum. Every affected parent has a literal
subarc witnessing that metric, so the same parent
discard bound applies. On the good family a metric on
the union of output paths pulls back through the
injective union of slab charts and pushes through I
with area no larger than the output area. This gives
coefficient-one width transfer for every subfamily,
on actual parent time windows.

This replaces the logarithmic-in-d confinement cost
when an actual sector endpoint certificate is available.
It does not prove a degree-independent cost for obtaining
complete canonical lifts or for forcing a selected
gap's endpoints into such a sector.

## 3. Half-disk corridors with fixed electrodes

Let an actual target packet have lifted endpoint
intervals L=[a,b], R=[c,d] in the real line with

    a < b < c < d <= a+1,

and all its actual cap bases directed between these two
intervals. Endpoint hulls of finite-width families can
be closed: a fiber of a fixed ideal endpoint has width
zero by the logarithmic point singularity metric.
Thus endpoints at the finitely many hull bounds can be
removed at width zero. We will allow other packets'
electrodes to meet at hull endpoints but not in their
interiors.

Write H(s,t) for the open upper half-disk of diameter
[s,t], and put

    U(L,R) = H(a,d) minus closure(H(b,c)),

intersected with the universal strip of the target.
The closure here is relative to the upper half-plane.

**Corridor confinement theorem.** The family can be
confined to U(L,R) by discarding width <=L_*.
For the outer boundary, choose any e in (b,c), and
r=min(e-a,d-e). At least one endpoint has distance
<=r from e. The distance from e to the upper semicircle
of diameter [a,d] is r (the nearest point on the full
circle is one of the two real endpoints). Any path
meeting or leaving that semicircle satisfies test (A).
For the inner disk use e=(b+c)/2, r=(c-b)/2:
both endpoints are outside radius r, and entering
or touching the closed disk implies test (B).
Apply the two tests in the strip and push down.
No prescribed conformal rectangle or uniform size of
either electrode or of the separating gap is required.

These corridors give an actual disjointization rule.
For two pairs of electrode intervals with mutually
disjoint interiors, lift both, including all integer
translates of the second pair. If in every such lift
the two ordered pairs of intervals do not alternate,
their outer diameter intervals are either disjoint or
one lies inside the other's inner gap. Indeed partial
overlap of the hulls with their four endpoint intervals
separated is exactly the alternating order. Containment
of the outer hull, with neither of the other endpoint
intervals meeting an end electrode of the containing
hull, places it inside the inner gap. The corresponding
half-disks are disjoint or nested in the deleted inner
disk. This follows directly from
|center_1-center_2|+radius_small<=radius_big
for nested real diameter intervals. Hence the open
corridors have disjoint interiors after projection.
Each individual outer half-disk has angular diameter
<=1, so its own translates are disjoint in the
open strip. This proves assembly of the confined
actual trajectories, not only of their homotopy tags.

## 4. Alternating electrodes and the shared-cell order cut

For later use the following two estimates apply to
two possibly intersecting target packets, each of
which is internally a Borel lamination.

If four fixed endpoint intervals alternate in the
real lifts, choose the four real dividing points
between the intervals and form the full upper-half-
plane quadrilateral. The two pairs of electrodes
are opposite pairs. Its two curve-family widths
are reciprocal. Restricting each quadrilateral metric
to the strip and pushing to the annulus gives

    W(B_1) W(B_2) <= 1.                            (1)

The lifts must be the actual oriented cap lifts;
one cannot use only the unordered endpoint labels
on the circle. Thus at least one whole packet has
width <=1 and can be removed at that cost.

A more useful version applies when the endpoint
intervals are cells of a fixed finite partition of
the circle, and the two distinct directed pairs
share a cell. Align the corresponding lifts of
that shared cell. When both endpoints there are
initial ends, the one whose terminal cell is
earlier on the real line must have its initial
endpoint later to avoid alternation. When both
are terminal ends, the same reverse ordering
holds relative to the two initial cells. When
one is terminal and the other initial, the
terminal endpoint must precede the initial.
The other cells in each of these aligned tests
are distinct as lifted intervals, except if the
directed pairs and lifts coincide.

**Order-cut lemma.** Enforce any one of these
required orders by discarding total width at
most 2 from the two packets. For example, if
the desired order is all endpoints of P before
all endpoints of Q in the shared cell, discard
P endpoints above a cut t and Q endpoints below t.
If W(P)<=1 discard P. Otherwise the distribution
of P endpoints in the cell is a finite atomless
measure: Borel disjoint-support modulus is
countably additive, and a fixed ideal endpoint
fiber has width zero. Choose t with width exactly
1 above it. The P-above and Q-below subfamilies
have strictly alternating lifted electrodes, so
(1) bounds the Q-below width by 1. Endpoints at
t have width zero. This proves the claim.
The reversed order is the same argument with
P and Q exchanged. This is a fixed-coordinate
quantile argument, not a claim that pairwise
intersecting arbitrary curves have reciprocal
width.

Order restrictions already achieved persist after
further subfamily deletions. For two distinct
directed cell pairs, consider relative lifts with
integer shifts -2,-1,0,1,2; no other shift can
overlap their full outer hulls when initial
cells are lifted in [0,1) and the terminal cell
in the next forward turn. For each such shift:

* four distinct lifted cells in alternating order
  give the small-packet removal (1);
* an aligned shared cell gives the order-cut
  lemma (if the two pairs share both cells in
  opposite directions, handle their respective
  alignments separately);
* four nonalternating distinct cells need no cut.

Both aligned cells with the same roles would
be the same directed cell pair, excluded here.
This finite list exhausts the possibilities
because actual endpoints are interior to their
cells. After processing all pairs, the actual
endpoint hulls of distinct remaining packets
have disjoint interiors, and their lifted
orders are nonalternating. Their semicircle
corridors therefore assemble by section 3.
With T distinct directed pairs a safe total
cost for these order and crossing deletions is

    10 * binomial(T,2),

followed by <=T L_* for corridor confinement.
Using five shifts is conservative.

## 5. The finite phase-assembly theorem

Let A be a finite-positive-width Borel lamination
of simple proper parents. Partition it into m
Borel packets. In an actual annular covering/
immersion step, suppose every parent in packet i
has an actual simple raw gap, with its oriented
cap above a fixed source anchor e_i. Choose a gap
by the first eligible code in the Borel occurrence
atlas. Require actual proper distinct-ended
selected gaps and marked admissibility of their
simple covering images (for the stationary
application the old-proper end fine atom
criterion supplies both filters).
The selected source paths are disjoint in their
interiors: their immersion images are literal
subarcs of disjoint parent paths.

First perform the fixed-anchor half-disk
confinement of COHERENT_PACKET_GAIN for each
packet. Charge <=m C_d on the original parents,
where C_d=pi log(16d)/(log 2)^2. Omit this term
if the packets are already in those charts.
All surviving selected paths have simple
covering images, with base span <1/2 and with
a_i=p(e_i) in the open cap base. They also
have coefficient-one width transfer within
their individual packets. The input packets
remain separate for accounting; their output
images need not be disjoint.

Cut the target inner circle at all the a_i
and their antipodes. There are n<=2m distinct
cuts, and n open cells. Every cell has angular
length <=1/2. Remove output endpoints at
these cuts at width zero, descending through
the good individual charts. Every actual
output has its two endpoints in distinct
cells: a cap within one cell would not contain
a cut a_i, and the complementary long route
has span >=1/2, impossible. Thus there are
at most T=n(n-1)<=4m^2 directed cell pairs.

For a pair (A_-,A_+), lift its full target
interval from the beginning of A_- to the
end of A_+ in the positive cap direction.
It has length <=1 (it may equal one if the
two cells exhaust the cut circle in that
direction). Its open inverse under p has d
disjoint intervals of length <=1/d. The
entire selected raw cap base lies in exactly
one such lifted interval, since it maps
homeomorphically onto the actual target
base with both endpoints interior to the
specified cells. This is its **phase** for
this directed pair.

There are at most min(d,m) occupied phases
for each pair. Indeed every selected gap
of original packet i contains its fixed
source anchor e_i, which selects at most
one phase interval for that pair. This
argument does not count arbitrary remote
covering sheets.

Let w_(c,s) be the width of the original
parent subfamily assigned to directed pair
c and phase s, after the first confinement
and zero-width exceptions. The labels are
finite Borel tests of the actual oriented
cap endpoints and the sheet. The partition
is disjoint on original supports, so these
widths add. Define the **phase-selection
deficit**

    Delta = sum_c (sum_s w_(c,s) - max_s w_(c,s)).

Use zero for empty pairs. Retain one phase
of maximal original-parent width for each
pair; the lost original width is exactly
Delta. This selection is an accounting
choice, not a proof that images of the
discarded phases were equal to the retained
one. Different phases could have disjoint
output supports; Delta is a conservative
sufficient loss budget.

All surviving source gaps of a given
pair and phase contain the lift of one
fixed target cut strictly between the
two endpoint cells (their endpoints are
interior to the cells). They have their
base in that phase interval. Apply the
sector confinement of section 2 with
this fixed anchor, even if it is not
one of the original marked anchors.
Charge <=T L_* on the original parents.
The covering is now injective on the
union of paths **within each phase group**.
It gives an actual Borel output packet
with coefficient-one metric transfer.
This step also combines gaps contributed
by several different original anchor
packets in the same phase, without
paying one width loss per fine marking
atom.

There is now only one actual packet per
directed target cell pair. Apply section 4
to these packets and then section 3 to
their endpoint hulls. Descend the discarded
output-family metrics to the original
parents through their individual injective
phase slabs. This costs at most

    10*binomial(T,2) + T L_*.

The remaining actual output paths form
one disjoint Borel lamination. In particular
p is injective on the union of the selected
source supports: each selected path maps
injectively, and its output is disjoint
from the outputs of all other paths.
The supports are Borel by the actual
Borel leaf/occurrence atlas and the
injective interior-time evaluation.
Pulling a metric on the assembled output
back on this union and pushing it through
the immersion gives coefficient-one
area and literal-window transport for
**every** subfamily. Alternatively the
individual phase bounds and disjoint
output addition give the width inequality.
We have never added widths of intersecting
output families.

The conclusion, with one optional control
prune in section 6, is:

    W(A minus G) <= m C_d + Delta
                      + 2T L_* + 10*binomial(T,2) + 1,
    W(D) >= W(G),

where D is the actual assembled output of
the good original parents G, with an
injective leaf correspondence. In particular
the non-phase part of the loss is O(m^4)
at a fixed one-step degree, independent of
q, angular atom sizes, and the number of
all remote endpoint labels. If the initial
packets are already confined the overhead
is independent even of the covering degree.

## 6. Controllability and the noncritical sector case

If each of the m original output packets
has a certificate of at most k_i localized
modules plus one leafwise over-critical
module, the assembled output has control
at most sum_i k_i+1, with one over-critical
module. To see this, first remove all output
leaves with actual angular base span >=1/2
at total width <=1 by COLLISION_GAIN,
section 5 (this is the optional +1 above).
Localized pieces inherit their end atoms.
All remaining over-critical leaves share
a fixed access in BL_0. Their base spans
<1/2 avoid its antipode. If the antipode
lies inside a marking atom H, assign
all such leaves having an endpoint in H
to one additional localized module.
The other leaves avoid H and thus have
a common proper connected marked base
on the cut circle. Their two ordered
end hulls lie on opposite sides of BL_0,
so their union has aggregate crest
over BL_0. If the antipode is a marking
cut no extra module is needed. All
classes are disjoint Borel subfamilies
of the actual assembled lamination.
The same argument was used for individual
packets in NEAR_CRITICAL_PACKET_CONTROL.

If there is one angular sector J on
which p is injective and some selected
raw caps are contained in J, then for
each target directed pair all such
caps belong to one phase: each contains
a preimage in J of the same intervening
target cut. In particular

    Delta <= W({parents whose selected base is not in J}).

If all bases stay in J there is no
phase loss, and the simpler sector
theorem applies directly.

There is an actual dynamical special case.
Assume the corrected geometric action,
old-proper first/last fine atoms, physical
limb locality, and signed endpoint-trap
hypotheses of AWAY_ENDPOINT_SHIFT.
Let an arbitrary Borel input lamination
be subordinate to the open noncritical
corridor, with one-step actual singleton
outputs and a finite crest-anchor cover
of m atoms. The paths need not be nonshort
or share one crest. After the canonical
one-step completion charge 2V and one
anchor confinement C_2 per packet,
the positive raw gap over each anchor
has a simple singleton image. The signed
inside/outside probe proof of
AWAY_ENDPOINT_SHIFT section 2 applies
leaf by leaf; it used only that the
chosen anchor is in the actual strict
crest, not that this crest contains
an entire limb. Every retained base
witnessing a crest probe stays in the
closed pulled marked parent hull, with
the two limiting dividing cuts excluded.
This is inside the full noncritical
pulled corridor. The latter covers
its translated interval injectively.
Thus the sector theorem gives one
actual aggregate output with

    W(D) >= W(A)-2V-m(C_2+L_*).

No unrelated packet widths are added.
Its endpoint limbs shift by one, by
the same signed endpoint trap. In
particular if the input has k localized
modules with endpoints in fixed old
atoms, the output is a union of at
most 6bk localized modules: each old
endpoint's limb translates, with at
most 6b atoms in that limb. The input
can be covered by m<=2k strict crest
atoms, by taking the next atom in the
actual cap direction from a localized
end (two directions). A proper marked
path cannot be subordinate to at most
two atoms. Coincident-end essential
inputs cannot be subordinate to the
noncritical corridor; the ordinary
point-cut exceptions have width zero.

This is a source-relative multi-packet
coefficient-one transport for the
noncritical singleton class, under
the stated exact geometric assumptions.
It does not assume the output endpoint
atoms are unchanged or that the paths
were confined to one chart initially.
A corresponding high-degree sector
estimate costs only L_* per packet
once actual full-tower cap containment
and complete occurrences are supplied.
It does not assert that sequential
unbreakability implies such a full-
tower certificate, nor remove the
2^r V incomplete-lift cost in a long
fast-forward.

## 7. A sharp obstruction to eliminating the phase deficit abstractly

In a target cylinder choose a fixed
small half-annulus around a real
anchor, with radii epsilon<r<r_0,
where r_0<1/8 and r_0 is below the
cylinder height. Its semicircular
crosscuts have width

    w = log(r_0/epsilon)/pi

by the log-coordinate rectangle.
Give the target a marking with an
anchor atom between -epsilon and
epsilon and one electrode atom
on either side covering the range
of endpoint radii. The leaves are
marked and strictly crest over the
anchor atom. Point boundaries are
irrelevant to width.

Take the two inverse copies of this
same packet under a genuine degree-
two annular covering. The copies
have disjoint source supports and
each has width w by conformal
invariance on its chart. Their
target images coincide as actual
path families, not only as homotopy
labels. With the two image anchors
and their antipodes the endpoints
fall in the same directed cell pair.
Each of the two phases has width w,
so Delta=w. The source union width
is 2w and any subfamily of the
specified covering images has width
<=w. Sending epsilon to zero rules
out a universal additive loss that
would preserve both copies by
selection from those images.

This is an annular countermodel to
an abstract phase-free assembly
claim. It is not a counterexample
to native KKL stationary dynamics
or a proof that arbitrary alternative
native replacement Waves cannot
exist. In particular different
phases of one directed cell pair
need not have coincident images.
The needed native improvement must
either bound the actual phase loss,
produce alternative physical windows,
or replace the competing packets by
a new admissible output with adequate
width. A bound on the number of
phase labels alone cannot do that.

## 8. Verification

The companion finite checker tests
all shared-cell order cases, integer
translates, disk containment and
disjointness inequalities, sector
injectivity and phase selection
bounds. The analytic radial, strip,
quadrilateral, Borel, and native
geometric arguments are written
mathematics; finite tests do not
establish those hypotheses.
Three finite accounting lemmas are
added to StationaryPacketGain.lean.
No canonical ledger promotion,
native stationary closure or MLC
claim is made. Independent specialist
review remains necessary. AI-assisted.
