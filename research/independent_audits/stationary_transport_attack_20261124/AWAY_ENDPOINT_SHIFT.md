# Away-from-critical shift by signed endpoint traps and quadrilateral reciprocity

Continuation of [POSITIVE_CREST_CONTINUATION](POSITIVE_CREST_CONTINUATION.md),
[SUFFIX_ANCHOR_RESPONSE](SUFFIX_ANCHOR_RESPONSE.md), and
[PRECRITICAL_TERMINAL_RESPONSE](PRECRITICAL_TERMINAL_RESPONSE.md).
This gives a replacement for the separate uniform (Away) hypothesis
on the same corrected geometric action. The cost is O(V+1), not an
absolute constant independent of V, and is sufficient for the stated
stationary width bound. The exact marked-action and old-proper
geometric inputs remain hypotheses. No appeal to the disputed broad
Wave pushforward lemma or to a Shift rectangle is made.

## 1. Setting

Use the actual one-step annuli X=U minus T, X_1=U^1 minus T_1,
the immersion I_1 and the genuine degree-two cover P_1. Put
V=1/mod(X), C=C_2=pi log(32)/(log 2)^2. Assume the canonical
lift, signed gap, Borel path, and full-hull graph hypotheses of
the preceding notes. Use the corrected geometric marking:
the original atoms are open arcs, their geometric coarse pulls
are the corresponding connected open contour-collapse intervals,
refined by the covering fine marking. The first and last fine
atoms of each such block have proper old-boundary limits in
that old atom. A raw gap passing the fine and coarse filters
is counted by the actual covering pushforward, even if its
projection is not embedded. A one-step unbreakable leaf has
one untagged path output in this action; path identity includes
its traversal, not merely equality of compact traces.

Write r for the physical/model-induced degree-one contour
collapse to the old circle. At a regular old-proper fine
atom its value agrees with the actual old boundary limit.
Assume the limb blocks have their native connected cyclic
order BL_0,...,BL_(q-1) and physical locality, and the
geometric noncritical translation p(r^(-1)(BL_i))=BL_(i+1)
for i noncritical, where p is the actual boundary covering.

Use the open noncritical corridor B=BL_1 through BL_(q-1),
including intermediate dividing-point cuts, but excluding
the two limiting critical-limb cuts. Its full geometric
pullback is one interval, and p on this interval is injective
with image BL_2 through BL_(q-1), BL_0, including intermediate
cuts. This is a consequence of the stated exact saturated
limb realization: at a dividing-point access there can be
no inserted branch hosted at that point. In the model hull
each open limb already contains an old cycle vertex. An
added point in that limb connects to that vertex along an
arc avoiding the dividing point, so its old attachment is
within that limb. The singleton dividing fiber and its
singleton boundary-access fibers transfer this to the
physical contours. Thus the junctions between limb blocks
are single cuts, the noncritical block translation is
continuous across them, and the union of translated blocks
omits the open BL_1. A connected interval with proper image
under the positive circle covering is injectively covered.
This is a check on the actual saturated realization, not an
assumption that every ordinary marked cut has singleton
contour-collapse fiber. Ordinary within-limb cut fibers may
contain attachments.

Let A be a proper Borel lamination of finite width consisting
of marked simple inner-ended paths, subordinate leaf by leaf
to B, ending in one fixed atom E of BL_k (1<=k<q), nonshort
(its leafwise crest contains a whole limb), and one-step
unbreakable. In this setting each base is a proper oriented
arc of the linearly cut corridor. A coincident-end contractible
path is subordinate to its single ending atom, and an
essential same-end loop is not subordinate to B. Marking-cut
ends are removed at width zero. Thus the inputs are genuine
distinct-ended disk-cap paths; we do not assume their
singleton outputs are simple in advance.

**Theorem.** With the displayed geometric hypotheses,

    W(A) <= 4V+2C+4.                              (1)

If a fixed limb crest determines one direction away from E
for every leaf, the bound is 2V+C+2. If the canonical lifts
are already complete, the corresponding 4V or 2V term can
be omitted.

## 2. Signed probes on both sides of a cap

First restrict to one of the two directions in the corridor.
A nonshort leaf starting or ending at E in BL_k must crest
over the entire next limb BL_(k+1) in the positive direction,
or the entire preceding limb BL_(k-1) in the negative
direction. This follows from the linear order and the
requirement that a whole limb be strictly between the two
ending atoms. No such direction is present if its neighboring
limb is the excluded BL_0. Assign the classes by their actual
base arcs, not a formal aggregate crest.

Charge incomplete one-step canonical lifts by 2V.
Fix the first old-proper fine atom of one old crest atom
in the full adjacent limb. Its anchor is in the strict
crest of every leaf of this directional class. The signed
crossing identity supplies a positive raw gap over the
anchor. Prune all bad raw gaps there at cost C. Every good
one is simple after covering, contains the whole fine atom
strictly between its ends, passes both filters, and gives the
actual unique singleton output. Thus on the good family the
output is now known to be a simple proper distinct-ended
path. The common chart gives an injective Borel output
lamination and coefficient-one width transfer on every
subfamily. This recovers, rather than assumes, output
simplicity at this step.

Fix a surviving parent. For every old atom I that is not
one of its two ending atoms, use both the first and last
fine atoms in its geometric coarse block as probes. All
their interior accesses have proper old limits in I, so
no raw endpoint is there (an interior parent time avoids
T and an original endpoint is in an ending atom). Remove
the fine-cut landing exceptions at width zero, simultaneously
for the finite marking of the given map. There is no
positive-width cost per probe.

For either probe e, the signed gap sum is

    sum_(raw gap bases containing e) sign(gap)
       = 1 if I is a strict crest atom, 0 if I is outside
           the marked base.                      (2)

For the outside case take the proper old-limit tail on the
outside of the old disk cap, and join it to the outer collar.
The transverse signed total is zero rather than one.
The same finite-crossing argument of the suffix note applies.
Contractible equal-end loops have empty base. An essential
equal-end loop has the punctured full circle as base and,
if it contains this probe, passes both filters as well.
In fact every counted gap over either end-fine probe must
pass both filters: its ends are outside the probe atom,
the base traverses that whole atom, and it cannot fit
inside its coarse block because that atom is first or last
in the block. This includes the long same-atom class.
The retained output is the already recovered simple
singleton, so an essential loop cannot be among these
retained gaps. Indeed its projected ideal ends coincide,
whereas those of the singleton are distinct.

All counted gaps are now lifts of that same simple output;
their disk-cap bases are disjoint lifts of one proper
base. At most one contains the given probe. Hence (2)
is an exact Boolean membership test: every crest probe
is in a unique positive retained base, and no outside
probe is in any retained base.

Let J be the closed marked base hull of this parent,
from the start of its initial ending atom to the end of
its terminal ending atom, in the linear corridor. It is
important to keep omitted-cut attachment fibers in this
closed hull. A retained base containing a crest probe
cannot leave r^(-1)(J). For otherwise, since it is a
connected oriented arc, in going out of the pulled hull
it enters the first (respectively last) end fine atom of
the immediately adjacent outside coarse block. It cannot
end inside that old-proper atom or at a fine cut; it
would therefore contain its probe, contradicting (2).
The same reasoning holds if the base travels toward
that outside block from the other side. If J reaches
a limiting dividing cut of the corridor, its fiber is
the singleton cut as checked in section 1; it is
excluded as an endpoint. This argument makes no claim
that a within-limb omitted-cut fiber is empty.

Consequently every retained base witnessing a crest
probe lies in the closed pulled noncritical corridor
(up to excluded endpoint cuts). There is at most one
such retained gap for the whole parent, since p is
injective on that corridor and two distinct lifts
would have the same nonempty target base. In particular
the primary found at the fixed adjacent-limb anchor
contains both end fine atoms of every old crest atom.
Its two endpoints are confined between the outside
probe gates and the corresponding first/last crest
probes. Thus they lie in the closed contour preimages
of the two ending atoms, respectively. This follows
by connectedness in the linear corridor: an initial
endpoint after the first fine atom of the first crest
block, or a terminal endpoint before the last fine
atom of the last crest block, would omit that probe.

We only need **limb** typing of these endpoints, not
membership in a prescribed open image of an individual
atom. A within-limb cut fiber belongs to the same
limb by saturated attachment locality, and a dividing
point is removed at width zero. Hence if the source
ends are in BL_k and BL_l, its actual simple primary
output has ends in BL_(k+1) and BL_(l+1), respectively,
with oriented base in the translated linear corridor.
This is a signed-gap proof of the endpoint shift;
it is not an inference from untagged itinerary labels.

## 3. A reciprocal-width comparison without choosing a rectangle

Let G be the surviving directional parent family and
g=W(G). Give the old ideal circle the real coordinate
(0,1) cut between BL_0 and BL_1, with BL_0 last.
Represent the old and translated corridor bases in
this coordinate, and lift each corresponding path to
the universal strip using its actual disk-side base.
This is possible because the endpoint order just proved
places both bases in these respective intervals (the
translated last limb BL_0 is represented at the right
of the line, not wrapped back to the left).

Width on disjoint Borel leaf subfamilies is a finite
measure: for countably disjoint Borel supports the
admissible densities restrict and combine, giving
countable additivity as in the finite parallel proof.
Each fiber of a fixed ideal remote endpoint has width
zero by a finite-energy logarithmic point singularity
in annular coordinates. Therefore the distribution of
that endpoint has no atoms. Choose a real median t
with two Borel subfamilies G_low, G_high of width
g/2 each, respectively remote endpoints below and
above t. If g=0 there is nothing to prove.

In the positive direction, E lies in BL_k and every
remote ending limb is >=k+2. For an old leaf of G_low,
its E endpoint lies to the left of BL_(k+1), and its
remote endpoint lies to the right of that limb but
below t. For a primary output of G_high, the image
of its E-side endpoint lies in BL_(k+1). Its other
endpoint is in the limb immediately after its old
remote endpoint's limb, hence strictly above t.
This remains true when that next limb is BL_0:
use its representation at the right end of (0,1).
There are four fixed, cyclically alternating ideal
electrodes on the extended real line of the upper
half-plane. Take the four dividing points to be
0, the two boundaries of BL_(k+1), and t. The old
G_low paths join electrodes 1 and 3, while the
G_high primary outputs join electrodes 2 and 4.
They are opposite pairs.

In the negative direction the remote endpoints of
the old paths lie in limbs <=k-2; the E endpoint is
now the right endpoint of the source cap. Choose
dividing points 0, t, the two boundaries of BL_k.
The old G_low connects the first and third electrodes.
The G_high primary output's remote endpoint is in
the following limb, strictly above t but before BL_k,
and its other endpoint is in BL_(k+1), strictly
after BL_k. It connects the second and fourth.
Again the boundary ordering is strict modulo the
discarded point endpoints. The median lies in the
remote range, so the four division points are
distinct in either case of positive width.

The universal strip is a subdomain of the upper
half-plane. If a density is admissible for one of
these full quadrilateral crossing families in the
half-plane, restrict it to the strip and push
through the universal cover by the all-sheet
square-sum rule. Energy does not increase and the
selected lifted path has its full length. Thus the
annular family widths are each bounded above by the
corresponding full quadrilateral width. The two
opposite-side quadrilateral widths are reciprocal
by rectangle uniformization (for a rectangle of
horizontal and vertical lengths a,b they are
b/a and a/b). We obtain

    W(G_low) * W(primary(G_high)) <= 1.

But coefficient-one common-chart transport gives
W(primary(G_high)) >= g/2 and W(G_low)=g/2.
Therefore g<=2. Add the 2V+C discard, giving
2V+C+2 for the directional class. Subadditivity
for the two possible directions proves (1).
For a known common full limb crest and localized E,
the direction is forced by the corridor order,
so only one bound is needed.

This is not an appeal to the assertion that any
families intersecting pairwise have reciprocal
widths: the four fixed boundary electrodes and
actual lift classes are specified above. No
assumption of a common conformal rectangle for
an arbitrary foliation is required.

## 4. Consequences and limits

In POSITIVE_CREST_CONTINUATION replace its additional
(Away) input with c_away=4V+2C_2+4. Its threshold is
still O_b(R+V+1): the number of localized-away
modules is bounded by K depending only on b.
No absolute V-independent Shift constant is
asserted for general incomplete parent lifts.

In addition, simplicity of the successive singleton
outputs in the positive-crest proof need not be
assumed on the discarded leaves. On the surviving
ones it follows inductively by the fixed-anchor
confinement at each selected step, because a good
raw gap passes both filters and gives an actual
simple output, which must be the unique singleton.
A simple marked parent with coincident ideal ends
is either contractible and inadmissible (away from
marking cuts), or essential with full-turn span
one. The latter family has width <=1/2 by the
long-base band metric of COLLISION_GAIN section 5:
density one on the band of height min(mod(X),1/2)
is admissible by horizontal variation of at least
one if the path stays in the band, or the two
vertical crossings otherwise. Add 1/2 once to
the initial discard when such inputs are allowed.
This does not discard arbitrary nonsimple parent
paths under a different definition of lamination.

The corrected geometric action, actual saturated
graph/end-atom and limb locality premises, and
Borel occurrence presentation remain essential.
The proof does not establish that the source's
unrestricted A.3.2 operation implements that
action. The associated discrete checks test
the end-probe and median ordering implications;
the geometry and modulus reasoning are written
proofs. AI-assisted research; independent
specialist review pending. No ledger promotion.
