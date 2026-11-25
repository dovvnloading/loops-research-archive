# Critical-bank localization and alternative-window phase selection

Continuation of [SECTOR_PHASE_ASSEMBLY](SECTOR_PHASE_ASSEMBLY.md) and
[MULTIPACKET_AMBIENT_DEFICIT](MULTIPACKET_AMBIENT_DEFICIT.md).

This narrows the potentially large phase deficit in the finite assembly
theorem. Under the actual saturated-hull/marking hypotheses of the
stationary program, every competing directed target cell pair crests
over a bounded near-critical atom bank. There is also a literal
additional raw window for an away-from-critical parent whose chosen
cap crosses the omitted limb of the translated corridor.

A finite configuration optimization can use such alternative windows
before deciding which parents to discard. Its remaining uncovered
width admits an exact local exchange certificate. This is a
replacement theorem with an explicitly identified residual, not a
proof that the residual always vanishes or that the literal native
marked action has been repaired.

## 1. Old critical hull maps to the near-critical bank

Use the actual native rotation 1/q, parabolic b-boundedness,
and the saturated monotone model of the previous notes. In the
source-locked terminology of
[the occupancy audit](../../mlc_unified/kkl_virtual_occupancy_source_audit.md)
section 2 (master lines 661--667), every original little Julia
component in the critical limb maps to a limb with index |j|<=b.
Let B_* be the union of these consecutive rotational limbs
BL_(-b),...,BL_b, including BL_0 and BL_1 (b>=1); take the whole
circle if the list wraps over all q limbs. It contains at most
6b(2b+1) distinct original marking atoms.

Here is a sufficient geometric proof that this component condition
also controls the image of the entire old critical hull, including
its edges. Use the model dendrite K_model, the full minimal hull A
of the small-Julia vertex bodies, the fixed dividing point alpha,
and the degree-two branched covering G preserving the dendrite
as in SYMMETRIC_SEPARATOR. Its deck involution on the dendrite
has the single critical point as its unique fixed point. For any
two distinct points x,y of the dendrite with G(x)=G(y), the
involution exchanges x,y and preserves their unique arc.
Consequently it has a fixed point on that arc, necessarily the
critical point. It follows that G is injective on an arc avoiding
the critical point, and on either half of an arc cut at that
point (the critical value has no other preimage).

Every point of the old hull in the open critical limb belongs
to some arc from alpha to a point of one of the original little
vertices in that limb. This is the dendrite hull property: a
component beyond the singleton dividing cut cannot occur in the
minimal hull without a marked vertex there; the arcs from alpha
to those vertices generate its intersection with that limb.
The image of such an arc, if it avoids the critical point, is
the unique arc from alpha to the vertex image point. If it
contains the critical point, its image is the union of the
two arcs from alpha to the critical value and from the critical
value to the vertex image point. The critical value is in
K_1, in BL_1. Each of those target points is in the bounded
bank by the source parabolic image hypothesis. Arcs joining
points of that bank and alpha remain in its union of limbs
and the dividing point, by the dendrite unique-arc property.

Therefore the entire old critical model hull maps into this
near-critical physical bank after saturation and the commuting
model/physical realization. This argument uses the minimal
full hull, the actual degree-two model deck involution, and
the actual critical-limb image condition, not just an occupancy
count or a label substitution. A separately specified physical
carrier still requires its saturated-hull identification.

In particular let e_i be an old-proper fine anchor of a one-step
packet, over an original open atom in BL_0. Its physical old
impression belongs to the critical old hull, and the actual
boundary covering image a_i=p(e_i) belongs to an original
marking atom of B_*, by the stated exact marking locality.
The fine atom maps to that whole original atom. The cut
exceptions have zero width as before. Thus all such selected
critical-side packets have a genuine near-critical crest
atom in their covering image. This is stronger than a bound
on the number of possible symbolic critical labels.

## 2. Every competing target cell pair is near-critical

In SECTOR_PHASE_ASSEMBLY refine the anchor/antipode target cut
set by the two dividing cuts delimiting BL_1 and by the endpoints
of every original atom of B_*. This uses at most

    B_c = 12b(2b+1)+2

additional cuts (a safe overcount). The cells still have
angular length <=1/2, and all the assembly and phase tests
are unchanged. With m actual source anchors use the bound

    T <= (2m+B_c)^2

on the number of directed cell pairs. The number of occupied
phases per pair is still <=min(d,m), because a fixed source
anchor belongs to at most one full inverse interval of the
chosen target cell arc.

Use now the one-step d=2 corrected geometric action. Let J be
the full pulled noncritical open corridor, excluding its two
limiting dividing cuts. The signed endpoint-shift note gives
p:J→J' as a homeomorphism onto the open target circle with
the closed BL_1 removed (including the internal limb cuts,
with the limiting two cuts excluded). In particular its two
extreme boundary accesses are the distinct preimages at
the two ends of that translated interval.

Fix a directed target cell pair c, and take the real lift I
of the full interval from the beginning of its first cell to
the end of its final cell, in the cap direction. Its length
is <=1. All selected raw bases contributing to c contain one
of the actual fixed source anchors, and are in a phase of
p^(-1)(I).

If any contributing source anchor is old-proper over a
critical old atom, its target fine-atom image A_* is a full
original atom of B_* by section 1. All cap bases of that
contributing packet contain the entire A_* strictly
between their endpoints. The endpoints of A_* and its
interior anchor are cuts of the refined target partition.
Consequently both end cells of c lie outside A_* and the
positive interval between them traverses A_*. Every
contributor to c, of either phase, therefore has this
same actual whole crest atom, not just an anchor point.

Otherwise all contributing anchors lie in J. If the real
lift I intersects the periodic copies of J' in just one
nonempty interval, that interval has a single continuous
inverse through J, contained in one inverse phase of I.
Thus all those anchors lie in the same phase, and there
is no competition. If the intersection has two components,
I traverses the whole omitted BL_1 between them. Because
the target cells respect the two boundaries of BL_1,
both endpoint cells are outside BL_1 and every actual
cap of c crests over the entire BL_1. This includes the
case of a lifted I of length exactly one; one must use
the oriented lift, not identify the two ends as an
unordered circular cell pair.

We conclude:

**Critical-bank conflict theorem.** Every directed target
pair with more than one occupied source phase has a common
actual whole crest atom in B_* for all of its contributors.

There is a useful quantitative version. After the initial
fixed-anchor confinement, let C_old be the original parents
whose chosen old-proper source anchor lies over BL_0, and
let C_1 be the parents whose chosen target cap crests over
the whole BL_1. The conservative phase-selection deficit
of SECTOR_PHASE_ASSEMBLY satisfies

    Delta <= W(C_old union C_1).                  (1)

Indeed for a pair not in the second case, all its noncritical
anchors lie in one phase. The maximal-width phase has width
at least that of the noncritical-anchor subfamily. Loss
therefore costs at most the critical-anchor width in that
pair. If the pair traverses the whole BL_1, bound the loss
by the entire mass in that pair. The original subfamilies
are disjoint and Borel, so their widths add. No inequality
adding intersecting target images is used.

There is also a uniform **control certificate for conflict
packets themselves**. For each phase of a competing pair,
apply its injective sector confinement as in the assembly
note. Its actual output lamination has the whole common
B_* atom and all its base spans are <1/2. Cut at the
antipode of one fixed access in that atom, allocate the
antipodal end atom if necessary, and allocate every
endpoint in B_* to its bank atom. The remaining bases
contain the whole consecutive B_* between their ends,
hence BL_0, with a common proper marked base. This is
the near-critical packet control proof, now with at most

    6b(2b+1)+1

localized modules plus one over-critical module.
It applies even to a phase group that combines different
original anchor packets. Thus the *competing* groups
are uniformly controlled without an arbitrary remote
endpoint count. This does not establish such a control
bound for every noncompeting group of an arbitrary
ambient Wave.

## 3. An actual extra window for an away parent entering BL_1

Use the exact signed probe hypotheses of AWAY_ENDPOINT_SHIFT,
including singleton limiting dividing-cut fibers, both
old-proper end fine atoms of every geometric coarse atom,
actual physical landing and complete canonical lifts.

Let a simple parent be subordinate to the old noncritical
corridor, so its actual disk cap avoids BL_0 and both
ends are in noncritical atoms. Choose a positive raw gap
over a fixed old-proper noncritical crest atom by the
signed-crossing construction, and confine it as in the
previous notes. Suppose its actual simple target cap
crests over the whole BL_1. The selected source base
cannot be contained in J, whose covering image is J'
and avoids BL_1. Starting from its noncritical anchor,
the connected source base must cross one of the limiting
dividing cuts into the pulled critical block.

At either such cut the adjacent critical-side fine atom
is an old-proper end fine atom of the first or last
critical coarse atom. This uses the exact singleton
dividing-cut fiber and the actual end-atom property:
there is no extra omitted attachment interval at the
dividing cut. The original parent has no raw endpoint
in that old-proper critical fine atom, since interior
parent times avoid T and its two original endpoints
are noncritical. Fine-cut endpoints are negligible.
Consequently the selected gap contains the whole adjacent
critical fine atom, not merely a part of its boundary.
Choose a fixed interior probe e at each of the two
possible critical fine atoms, once for the map.

The signed raw-gap sum at the encountered probe is zero:
its old-proper image is outside the old parent cap.
The chosen positive gap contributes +1. There must be
a distinct raw gap containing e with negative sign.
This is an actual different maximal contact-set gap
on the same complete parent lift. Both contain the
whole end fine atom strictly between their endpoints,
so both pass the geometric marking filters. Apply
the fixed-anchor confinement at the two possible
critical probes; all bad candidate gaps cost <=2C_2
on the original parents by the same square-sum push.
A good additional gap is simple after covering and
has an actual whole crest atom in B_* by section 1.
Its time window is disjoint from the chosen primary,
and it may be used as a separate auxiliary metric
witness or an alternative actual output choice.

This shows that in (1) the C_1 contribution from
old away parents has a concrete same-parent extra-window
mechanism, not just a covering phase of a different
parent. In particular if the parent is one-step
unbreakable with the corrected action, the two
retained gaps would have the same simple singleton
output, and hence disjoint lifted cap bases. They
cannot both contain the probe e. Thus the situation
is impossible on the good singleton-away family;
this recovers the relevant noncritical trap without
requiring a global cap atlas for arbitrary breakable
leaves.

For a breakable parent the two terminal images can
be different. No relation between their directed
cell pairs is inferred here. In particular a second
raw window is not automatically a candidate in the
opposite phase of the original target cell pair.
That distinction is essential for the selection
argument below.

## 4. Optimize phases over actual alternative raw windows

There is no need to choose one raw gap per parent
*before* optimizing the phase assignment. Here is
a general Borel finite-choice lemma, independent of
the native origin of the alternatives.

Start with a disjoint Borel parent lamination of
finite width, complete at the step in use, and a
finite inventory of fixed raw-gap anchors. For each
parent consider all actual eligible simple raw gaps
through these anchors (retained if required for the
application). Prune all bad candidates by the
fixed-anchor confinement: the charge is at most
m C_d for m anchors, even when a parent has several
candidates at the same anchor, since every such bad
gap supplies a literal metric witness. In a native
application one includes its guaranteed original
positive anchor and may additionally include the
two critical probes of section 3. After these charges
assume every surviving parent has a good candidate.
Remove candidate endpoint-cut exceptions at zero
width. These candidates have the exact Borel
contact-set enumeration and actual cap/phase codes;
no invented homotopy-only alternatives are allowed.

Use the same refined target cell partition and
phase intervals as in section 2. Each parent has
a nonempty finite set L(alpha) of eligible labels
(c,s), where c is an ordered target endpoint-cell
pair and s an actual inverse interval phase.
Multiple raw gaps with the same label are allowed.
The total label inventory is finite: per pair at
most min(d,m) phases occur. The finite membership
predicates are Borel by the countable enumeration.
The widths below use the finite measure on disjoint
original Borel supports; if an earlier good prefix
is present this can be the measure on the original
parents before that prefix.

A configuration chooses one occupied phase s(c)
for each nonempty directed pair c. A parent is
covered if some member of L(alpha) belongs to
the chosen configuration. Since there are finitely
many configurations, choose one maximizing the
covered original width. This is a finite variational
choice, not a new analytic maximum. Define

    Delta_opt = W(uncovered parents).

For every covered parent choose the first good
actual gap whose label is allowed. The selection
is Borel. One selected gap per parent gives
disjoint source paths, since their immersion
images lie on the original distinct parent
interiors. There is one phase per directed pair.
Apply sector confinement, shared-cell quantile
order cuts and half-disk corridor confinement as
in SECTOR_PHASE_ASSEMBLY. They give an actual
disjoint output lamination of width at least
the remaining original width, with the same
finite overhead using the enlarged cut inventory.
The selected supports are Borel and the union
covering is injective, so literal-window metric
transport is preserved for every surviving
subfamily. No formal replacement of parent paths
by unlabeled weights is made.

For any fixed choice of one eligible gap per
parent, largest-phase selection of that choice
is one feasible configuration which covers all
the parents retained by that choice. Hence

    Delta_opt <= Delta_fixed.

For a fixed label partition adding extra eligible
windows cannot increase Delta_opt. If a designated
compatible sector phase covers every parent,
Delta_opt=0. All these comparisons concern actual
candidate labels, not existence of a wider Wave.

### Exact local exchange certificate

For an optimal configuration let U_(c,t) consist
of uncovered parents having a candidate label
(c,t), where t is a nonselected occupied phase.
Let P_(c,s;t) consist of the currently covered
parents whose currently allowed candidates all
have label (c,s), where s=s(c), and who have no
candidate at (c,t). Changing the chosen phase of
c from s to t, keeping all other choices, gains
exactly U_(c,t) and loses exactly P_(c,s;t).
All are Borel subfamilies of the original
disjoint support. Optimality gives

    W(U_(c,t)) <= W(P_(c,s;t)).                    (2)

The equality of the gain/loss sets follows
pointwise: a parent with any other allowed
pair remains covered, and a parent with an
alternative in t remains covered after the
switch. Thus (2) is a genuine local exchange
inequality, not just comparison of the total
widths in two arbitrary phases.

Every uncovered parent has at least one eligible
label in an unselected phase; its pair has an
occupied selected phase as well. If Delta_opt>0,
one of the finitely many U_(c,t) has width at
least Delta_opt divided by the number of
eligible nonselected labels, by subadditivity.
Equation (2) supplies a comparably large
*pivotal* competing phase subfamily with no
other allowed candidate and no candidate at t.

In the native setting of section 2 every one
of these competing pairs has the common whole
near-critical crest atom of B_*. Thus any
residual of optimized phase selection is
localized to that bank and is accompanied by
a specific opposing candidate obstruction.
A count of two different phase labels alone
would not establish (2).

### A probabilistic bound, including duplicate singletons

At degree two choose independently at each
directed pair a uniformly random occupied
phase. If a parent has eligible candidates
in both phases of one pair, it is covered
by every configuration. If it has candidates
at r distinct pairs and at most one phase
per pair, the probability of being missed
is at most 2^(-r); single-occupied-phase
pairs only improve this. Integrating the
finite-configuration indicator against the
original width measure gives

    Delta_opt <= integral_{no double-phase pair} 2^(-r(alpha)) dW.

The optimum has at most the expected uncovered
width. In particular when a parent has two
actual good lifts of the same simple singleton
output and both are in the eligible inventory,
those lifts are the genuine deck pair with
the same directed target cell pair, in
different phases. It is covered in every
configuration. Distinct candidates over
different directed pairs give the corresponding
probability improvement. The extra raw window
of section 3 may or may not have this type
separation; do not infer it merely from its
disjoint parent time interval.

The abstract two-deck-copy counterexample
of SECTOR_PHASE_ASSEMBLY still applies if
each parent has only its one eligible label:
two packets on opposite phases of one pair
can have equal full target image support.
The optimization then necessarily loses
one packet. The missing native theorem
must exclude or respond to a large pivotal
conflict, not merely increase the candidate
inventory by a label that is never realized.

## 5. Application and remaining scope

In MULTIPACKET_AMBIENT_DEFICIT one may refine
the target cut set as above and use the
optimized phase deficit at each step, with

    T_m=(2m+B_c)^2

and the corresponding finite overhead.
All chosen candidates on the stationary
subset must pass the actual retained filters,
so singleton identity still holds there.
If an alternative choice differs from the
positive crest-testing gap, the two actual
singleton lifts already give the previous
double rule. On a tracked leaf with no such
double response the selected primary is
the positive gap used to advance the
crest. Background choices do not require
positive orientation for metric transport;
their windows must be literal and their
assembled paths simple, proper and Borel.
Under these requirements the same ambient
series and double inequalities and the
positive-crest suffix tracking apply.
The uniform output control and finite
anchor cover through all stages are still
explicit requirements.

Thus a large cumulative *optimized* deficit
at the absolute-scale threshold of that
note implies a positive-width collection
of actual uncovered and pivotal opposite
phases over a bounded near-critical atom
bank, or a strict ambient response already.
The exact exchange inequality (2) permits
a targeted native acceptance test: find
another eligible literal window for the
uncovered class, or for the pivotal class
so that switching phases no longer loses
it. This is narrower than trying to make
all projected Waves disjoint by default.

The full source marking (including the
saturated carrier identification and
literal A.3.2 discrepancy), arbitrary
ambient control independent of the input
control k, a native bound/response for
the remaining near-critical pivotal
conflicts, and downstream integration
remain open. Neither the finite selection
nor the near-critical localization
asserts a native global closure.

The companion checker exhausts finite
cell/phase localization, alternative-label
configurations, local exchanges, and
degree-two expected uncovered fractions.
The radial/prime-end/dendrite/width
arguments are written mathematics, not
proved by that enumeration. No ledger
status is promoted. AI-assisted research;
independent specialist review pending.
