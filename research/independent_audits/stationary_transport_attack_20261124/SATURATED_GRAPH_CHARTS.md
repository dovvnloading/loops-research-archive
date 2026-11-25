# Geometric marking on a saturated preimage graph: proper bands and end atoms

This is a native-geometry supplement to
[NO_FIXED_POINT_COMPRESSION](NO_FIXED_POINT_COMPRESSION.md).
It gives sufficient model/physical conditions for several chart
hypotheses of the gap-free conditional width theorem. In particular
the proper-middle chart and the old-proper first/last fine atom
property need not be separate assumptions once the actual
saturated finite graph-of-vertex-bodies description and its
complete marked access correspondence have been verified.

The argument works with the **geometric contour pullback** defined
by the nested carrier collapse. It does not claim that the source's
unrestricted maximal-subset A.3.2 definition equals that pullback.
The live v1 HTML source was again unavailable; the source-specific
graph inputs below are the explicit ones in the source-locked
[marked-realization audit](../issue40_native_marked_realization_local_gates_20261124.md),
[monotone prime-end bridge](../issue40_monotone_model_prime_end_bridge_20261124.md)
and [ambient-angle exactness audit](../issue40_ambient_angle_exactness_20261124.md).
No source claim is inferred from the conditional proof.

## 1. Exact geometric data required

Let K_m be the actual model dendrite of the periodically repelling
quadratic-like dynamics, with a degree-two planar branched-cover
map Q and its actual filled-set invariance. Use the monotone
physical-to-model plane map of the preceding audits, the saturated
old carrier A=H^(-1)(A_m) and its full pulled carrier
B=H^(-1)(B_m), where

    A_m = hull of the actual original whole little Julia bodies,
    B_m = Q^(-1)(A_m).

These are full connected dendrites in the model; the physical
carriers need not be locally connected. The full preimage
equality, saturation, and identification with the actual canonical
Kahn immersion near the filled graph are required. We do not
replace the physical carrier by an arbitrarily selected skeleton.

Assume the following explicit graph/marking input package.

(G1) The original model whole little Julia bodies are pairwise
disjoint, each is an entire component of the inverse of its
next body, and the critical body is the whole degree-two
preimage of the critical-value body. A_m is forward invariant.
Outside the bodies the original connecting graph is a finite
tree of edges and singleton vertices, including the fixed
dividing point alpha. Its marked landings are precisely the
specified whole-body contact points and singleton graph vertices.
The singleton vertices map into singleton original vertices
outside the little bodies; if an extra subdivision is included,
its images must be part of the marked landing inventory with
the same whole-vertex property. The marked contacts on original
bodies map to marked contacts of their image bodies.

(G2) The full inverse graph B_m is formed from the entire
preimage components of these vertex bodies and singleton
vertices, with their preimage edges. Each open preimage edge
is disjoint from all those vertices, has valence two in B_m,
and its endpoints are the corresponding marked preimage
contacts or singleton vertices. The entire set of such
preimage vertex bodies and connecting edges is the full
carrier, not a selected subgraph. All original whole bodies
are among these entire preimage vertices. The finite graph
description permits arbitrary nondegenerate dendrite
structure inside the vertex bodies.

(G3) The original side marking is access-complete at every
original marked landing: every model contour access at
each marked point is an original marked cut. In the full
inverse graph the fine cuts are the covering preimages of
these cuts, with their actual access tags; in particular all
preimage edge contact accesses are fine cuts. The saturated
monotone plane/prime-end transfer has singleton physical
boundary fibers over all these marked model accesses and
their preimages, and preserves the actual covering square.
The actual embedding near the filled graph identifies the
physical old carrier with its copy in the pulled carrier.
Use the canonical monotone degree-one nested-contour
collapse r_0:C_(B_m)→C_(A_m) and its physical model
commuting correspondence as in the ambient-angle theorem.
It collapses an attached component contour to its actual
old host access. The collapse fiber's two extreme gates
over a marked access have that old marked model landing.

(G4) The actual model dividing point alpha has q rotational
open limbs, in the native cyclic order, with the critical
point in Omega_0. Every open limb contains at least one
original whole little body. The map on a noncritical
limb takes values in the next limb, in the rotation 1/q
order. The model degree-two deck involution and its
unique critical fixed point are the ones in
SYMMETRIC_SEPARATOR. Use the parabolic condition that every
original little body in the critical limb has its image
in BL_[-b,b], and the bound of 6b actual original atoms
per limb. These are conditions on the actual native
model geometry, not the desired angular comparison.

These hypotheses are deliberately stated as full
saturated graph/marking data. The ordinary model
plane correspondence and its identification with
the source's complete graph require their own
verification. No inference from a finite synthetic
occupancy diagram is intended.

## 2. All-or-none incidence on a preimage edge

**Lemma.** Every open preimage edge e of B_m is either
contained in A_m or disjoint from it.

Proof. A_m is the minimal dendrite hull of the union of
the original whole bodies. In a dendrite that hull is
the union of those bodies and the unique arcs between
their points. Indeed this union is connected, contains
the bodies, and is contained in every connected carrier
containing them; here finitely many connecting arcs and
compact bodies give its compactness. A point in the hull
outside the bodies lies on an arc joining points in two
of the bodies.

All original bodies are entire preimage vertices by
(G1)--(G2), disjoint from the interior of e.
If A_m contains any interior point of e, some arc between
points in the original bodies passes through that point.
The open edge has valence two in B_m and connects its two
end vertices; an arc with both endpoints off that open
edge, passing through an interior point, must pass
through the entire edge. Otherwise it would terminate
inside the open edge or reverse along its unique arc.
Thus the whole edge is in A_m. QED.

In particular if e is included, A_m and B_m agree
locally at all interior points of e. If an excluded
edge has an endpoint x in A_m, its interior is in an
added component with root x. Its contour collapses
to an old access over x, not to arbitrary points of
the adjacent old contour atoms. This uses the actual
host-access property of the nested contour collapse.

## 3. The actual geometric coarse marking is fine-refined

Define the coarse geometric pull of an original open
atom I by

    J(I)=m_B^(-1)(r_0^(-1)(I_model)),

where m_A,m_B are the actual physical/model contour
maps and I=m_A^(-1)(I_model). Use exactly the inverse
image of the open interval, not the closure. For
closed intervals the closed inverse image is used.
The degree-one monotone collapse and the physical
maps are continuous surjections, so J(I) is a
connected nonempty open interval. A proper interval
with distinct end cuts has extreme gates at the two
corresponding marked-cut fibers.

Each extreme model gate over an old marked cut has the
old marked landing x by (G3). Its image under the
actual boundary covering has the marked model landing
Q(x) by (G1) and the actual covering square. Access
completeness at Q(x) marks that image as an original
cut; consequently the source gate is a fine cut.
The singleton physical marked/preimage fibers in
(G3) identify the corresponding physical cut exactly,
not just its model label. Thus the coarse open
interval J(I) consists of whole fine atoms and
intervening fine cuts. Its endpoints are distinct
because its proper nonempty original atom is
separated from other original atoms by the actual
coarse collapse; it contains at least one fine atom.
This proves the open whole-atom refinement used by
the gap-free proof. The fibers of omitted old cuts
are omitted on open input; the statement does not
assume those fibers are singletons.

This construction is independent of the maximal-subset
test in A.3.2. The earlier counterexample to the
unrestricted literal test remains valid.

## 4. First and last fine atoms are genuinely old-proper

**Lemma.** For each original open atom I, the actual first
and last fine atoms of J(I) have continuous proper old
boundary limits into I under the immersion. Locally this
is the actual inclusion chart of the two carrier
complements, after the embedding near the filled graph.

Proof. Work first with the model fine atom adjacent to
one extreme gate of the original marked-cut fiber,
on the inside of the open J(I). Its landing image
lies either in an open preimage edge or in a preimage
vertex body away from its preimage graph contacts:
the model landing map is continuous, and the full
fine marking contains every access at a preimage
contact or preimage singleton vertex, so the atom
cannot pass through any of those separating marked
landings. Its limiting landing at the extreme gate
is the old marked point x.

In the vertex case the preimage vertex body is closed
and contains x by this limit. If x is on an original
whole little body, that body is precisely its entire
preimage vertex (G1). If x is an original singleton
vertex, its image is an original singleton vertex
outside all little bodies (G1), so x cannot belong
to a preimage little body. Thus the vertex case
uses an original whole preimage body. At every
point of the fine atom its model landing is away
from the finite preimage graph contacts. All other
preimage vertex bodies are compact and disjoint,
and the finite incident edges attach only at
the listed contacts. Therefore the two model
carriers agree locally there.

In the edge case the open preimage edge has x as
one endpoint. If it were disjoint from A_m, its
added component would attach at x by section 2,
and its contour would collapse to one old access
over x. Every such access is an old marked cut
by (G3), so this contour cannot occur inside
the geometric pull of the *open* original atom I.
This contradicts its position. Hence the edge
is included in A_m and the two model carriers
agree locally along its interior by section 2.

We have proved local equality around the model landing
of every point in either end fine atom, not merely
a germ at the extreme gate. By saturation, taking
the inverse image of any such model neighborhood
under the monotone plane map gives an open
neighborhood of the entire corresponding physical
impression on which the physical carriers agree.
The physical/model impression correspondence is
part of (G3). Thus the actual complements coincide
near that impression after the embedded near-filled
identification. Their ideal ends there coincide
locally: a defining prime-end crosscut chain has
nested compact shadows whose intersection is the
impression, so sufficiently late shadows are in
the equality neighborhood. Those late crosscuts
and their cut-off sides are the same in both
complements (their boundary in that neighborhood
consists only of the crosscut and the identical
carrier). This gives the same old prime-end
limit and a local homeomorphism of the ideal
boundary charts. It does not require the physical
impression to be one point. The actual immersion
agrees with this embedded coordinate change
near the filled graph.

The resulting proper old limits have model
coordinates r_0 m_B, so they lie in the actual
old atom I by its defining inverse-image identity.
These local extensions agree on their overlaps.
This proves the claimed entire fine atom properness.
QED.

This establishes the signed inside/outside probe
hypothesis of the earlier analytic proofs under
(G1)--(G3). An interior parent time cannot be an
endpoint of a raw gap in such an atom if its old
limit belongs to the deleted old carrier; original
endpoint times cannot be there when the entire
old atom is in the strict crest or outside the
marked cap base. Those are the literal immersion
path-lift endpoint tests already used in the
signed-gap arguments. No assertion about the
interior of an arbitrary coarse pull block follows:
it may contain nonproper attached contours.

### The genuine critical deck pair

Take any whole original vertex-side atom on the
critical-value little body K_1. There are two
fine inverse atoms under the actual annular
degree-two covering. Both lie on the entire
critical preimage little body K_0 by (G1).
The preimage graph contacts are fine cuts;
away from them, the same whole-original-vertex
argument above gives local equality of the
carriers and proper old limits for the entire
fine atoms. They belong to the open critical
old limb by its saturated limb locality.
The degree-two deck involution exchanges these
actual two inverse accesses. This gives the
old-proper deck pair of the earlier critical
crest charge, assuming the stated original
vertex-side atom and the whole inverse body
in (G1), not a pair of abstract labels.

## 5. Proper middle chart from the native limb placement

First note the following model facts under (G4).
The restriction of Q to the closure of any
noncritical limb is injective. If distinct
points there have the same image, the actual
degree-two deck involution exchanges them and
preserves their unique connecting arc; it must
have a fixed point on that arc. Its unique
fixed point is the critical point, which is
outside this closed limb. This is impossible.
Its open-limb image is the entire next open
limb. In fact the restriction Q|K_m is
relatively open: for a relatively open set
of K_m, lift it to a plane open set and use
the openness of the planar branched cover and
full filled-set inverse invariance. The image
of the open noncritical limb is relatively
open in the indicated next limb. It is also
relatively closed there by compactness of the
closed limb and injectivity excluding other
preimages of alpha in that closed limb.
The target limb is connected and the image
nonempty, so equality follows. The closed
limbs are therefore homeomorphic under Q.

The two carriers have no added component
rooted at alpha. Every added point is in
some open limb, which already contains a
point of an original body in A_m; the unique
arc between them stays in that open limb,
so its unique old attachment is not alpha.
More explicitly the singleton inverse graph
vertex alpha has finitely many incident
preimage edges. Each arm of B_m at alpha
is in an open limb already meeting A_m, so
the initial incident edge is included by
section 2. Thus the carriers agree locally
at alpha in the model. Its physical fiber
and marked dividing accesses are the stated
singletons of (G3). The actual old/expanded
dividing cuts match without inserted fibers.
The positive boundary covering then maps
each full pulled noncritical limb block
homeomorphically to the next target limb
block: model limb homeomorphism gives its
landing locality; the endpoint access
matching at alpha follows from the actual
orientation-preserving local planar map
there and the native rotation. The proper
target image cannot wrap around the whole
circle. The closed critical pulled block
has full boundary image, since the union
of the other blocks is covered injectively
onto the translated noncritical corridor;
every target point has two covering
preimages, at least one outside that
injective open corridor.

Now take j in [b,q-b-2]. Its next limb j+1
is outside BL_[-b,b]. Every whole original
little body in that next limb has its
original cycle predecessor in the old
noncritical limb j: a critical predecessor
is excluded by the parabolic image condition,
and the noncritical limb rotation determines
j uniquely. Since Q on the entire closed
limb j is a homeomorphism, the entire
preimage of every target original little
body in this branch is precisely that
original predecessor body. There are no
extra preimage vertex bodies in this
noncritical limb.

The intersection of the old minimal hull
with the closed limb is exactly the hull
of alpha and the original bodies in that
limb. This follows from the unique arc
property: all connections to other limbs
pass through alpha, and all paths between
two bodies of the same open limb stay
within it. The same statement holds for
the target old hull in the next closed
limb. The model limb homeomorphism
preserves unique arcs and those entire
vertex bodies. Taking its inverse of the
target hull gives

    B_m intersect closure(Omega_j)
       = A_m intersect closure(Omega_j).

This proves the proper-middle **carrier
equality** (not just a proper cyclic
label shift). On the open limb it gives
local equality; the internal dividing
cuts match by the alpha argument. Saturation
transfers the equality neighborhoods to
the physical impressions. The actual
immersion's old-boundary chart on the
entire pulled middle band, including
internal cuts, is therefore a proper
homeomorphism onto its corresponding old
band by the same local ideal-end argument
as in section 4. Its covering is the
actual injective translated band map.
This is the chart needed for the Herglotz
no-fixed-point proof and the guard-free
long-jump chart construction. The finite
full-tower compatibility is supplied by
the actual tower squares as in the
preceding notes. QED.

## 6. Remaining source checks

The preceding deductions show that the
proper-middle chart, whole-atom refinement,
old-proper end fine atoms, matching
dividing cuts and critical deck pair
can be derived from the stated saturated
model graph and complete marked access
package. Thus one need not separately
postulate their angular properness
properties once those native inputs are
verified.

The package still requires substantial
native checks: identification of the
actual source carrier with the saturated
minimal hull and its whole preimage graph;
forward typing of the specified singleton
vertices and contact points; exact
access-complete marking and singleton
marked fibers; the physical/model
prime-end and covering correspondence;
and the actual selected-depth/two-bank
host-fine-side separation used elsewhere.
The geometric action's exact orbit
saturation follows only with the
commuting ambient-angle contour
identification of the earlier theorem.
The initial actual Borel localized or
leafwise-over-critical Wave witness and
downstream source licensing also remain
separate requirements.

No appeal to the false unrestricted
maximal-subset interpretation or to
numerical calibration of the model
angles is made. This is a conditional
geometric construction, not an
independent specialist confirmation of
all the native source hypotheses. No
new numerical checker or Lean declaration
is added here. No canonical ledger
status, native closure or MLC conclusion
is promoted. AI-assisted research;
independent mathematical review pending.
