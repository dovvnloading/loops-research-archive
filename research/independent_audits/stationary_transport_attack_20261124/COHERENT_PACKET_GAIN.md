# Coherent-packet confinement and a loss-controlled collision telescope

2026-11-25. Continuation of [COLLISION_GAIN.md](COLLISION_GAIN.md)
and [ANGULAR_CALIBRATION.md](ANGULAR_CALIBRATION.md).
The earlier all-sheet estimate pays the full covering degree at
every step. On an actual common-crest packet, that degree loss
can be removed by an explicit uniformly bounded metric discard.
The resulting response needs only a positive-width fraction with
one genuine duplicate stage, rather than a majority of double
stages. This is a self-contained annular pruning and response
inequality; the native occurrence and output-marking hypotheses
are kept separate.

## 1. Explicit confinement in a single covering chart

Let Y be an annulus of finite positive modulus M, normalized
as the flat cylinder (R/Z)×(0,M), and let p:Y→X be a proper
degree-d annular covering preserving the inner and outer ends.
In normalized coordinates p multiplies both strip coordinates
by d up to an angular translation. Let e be a fixed inner access
of Y. Let B be any family of simple proper inner-to-inner
crosscuts with distinct ideal ends, whose actual disk-side cap
bases all contain e in their interiors. No aggregate crest or
transverse measure is needed for the metric lemma.

Lift the cap and crosscut to the strip, with e represented by
the origin on the bottom line. The endpoints have coordinates
x_-<0<x_+ and x_+-x_-<1, so their absolute values are ≤1.
Set

\[
 s={1\over4d},\qquad
 C_d={\pi\over(\log 2)^2}\log(16d).
\]

Call a leaf bad if the supremum of |z| on this lifted crosscut
is at least s. Then

\[
 \boxed{W_Y(B_{\rm bad})\le C_d.} \tag{1}
\]

Indeed use density 1/|z| in the upper half-annulus
s/2≤|z|≤2, zero outside, restricted to the strip. Its
squared area is at most π log(4/s). Every bad lift has
length at least log 2:

* If it reaches (or approaches) radius s and also enters
  radius <s/2, its radial variation crosses [s/2,s].
* If it reaches radius >2, one of its two tails from a
  boundary endpoint of radius at most one crosses [1,2].
* In the remaining case it stays in the half-annulus,
  where its argument changes from π to 0. Its length
  is at least π.

These cases exhaust the bad family, including equality of
the supremum with s. The radial circles belong to the metric
support; the inequalities follow by compact exhaustion and
radial/angular variation, without monotonicity of the trace.
After division by log 2, push the metric through the strip
cover by the all-sheet square-sum rule. The area does not
increase, and every specified lift's length is dominated.
Nonrectifiable curves are handled by adding a positive
constant with area tending to zero in the finite-area
cylinder coordinate. This proves (1).

Every remaining crosscut is entirely contained in the
projection H_e of the upper half-disk |z|<s. The composite
strip-to-target covering is injective there: any two points
with the same image would differ by an integer multiple of
1/d horizontally, whereas their horizontal separation is
<2s=1/(2d). In particular p is injective on the *union*
of all good leaves. The d deck translates of H_e are pairwise
disjoint and each maps biholomorphically onto the same
target chart. These assertions hold even when the full
annular covering is not injective and when B is not a
lamination.

This gives a direct common-crest pruning proof with explicit
discard, rather than subtracting two widths using an unproved
measure convention. The bound C_d is O(log d) and independent
of the modulus, the number of marked atoms, or their angular
sizes. It only applies to actual directed cap paths around
one specified access; a union of unrelated crest packets
requires separate accounting.

## 2. One step: coefficient one, or a factor-two gain

Use the actual one-step annuli and maps of
[CANONICAL_LIFT_AND_DIRECTION.md](CANONICAL_LIFT_AND_DIRECTION.md):
i:X_1→X is the immersion and f:X_1→X the degree-two
covering. Work with a family A of simple proper inner-ended
parents which admit complete canonical unpunctured lifts
at this step, and whose actual retained output is a singleton
simple proper inner path δ(α).

Assume each parent has an actual retained maximal inner-ended
restriction with its disk-side cap base containing the same
fixed inner access e of X_1 in its interior. This is an
occurrence hypothesis, not a consequence of a symbolic crest
label. It follows, for example, from the signed-crossing
theorem for a common protected block in the corrected
geometric marking, or from an independently justified
directed restriction theorem on the same action.

At most one retained restriction of a given parent can have
this anchor in its cap base: any two would be distinct lifts
of the same simple δ(α), and their disk-side cap bases are
disjoint lifts of the same proper output base. Call this
unique restriction the primary one. The canonical-lift
exhaustion theorem makes every other inner-ended retained
restriction a disjoint parameter gap of the same parent lift.
There are at most two, because f has degree two.

Remove the parents whose primary restriction is bad in
Section 1. By the all-sheet pushforward through i, each such
parent contains a literal subarc witnessing the bad source
family. Hence their width is ≤C_2. On the good family the
primary lies in H_e. The source image of every other
retained restriction, if present, is the exact deck translate
of the primary, since they are the two lifts of δ(α). It lies
in the disjoint deck chart τH_e.

For a good subfamily S whose parents each have exactly r
inner retained restrictions, r=1 or 2, let D be their actual
output family. Pull a D-admissible metric back by f, keep it
on H_e if r=1 and on H_e union τH_e if r=2, and put zero
elsewhere. Each chart is injective, so the area is at most
r times its target area. Each parent has r disjoint literal
time subarcs of length ≥1 in the all-sheet pushed metric.
Divide by r and take the infimum. We obtain

\[
 \boxed{W_X(S)\le {1\over r}\,W_X(D).} \tag{2}
\]

For a subfamily with varying multiplicity, the primary
chart alone gives W(S)≤W(D). No area cost from the unused
covering sheet is charged. Equation (2) is valid without
a Borel selector or global immersion embedding.

If A is a lamination, all good primary restrictions form
a disjoint family of simple paths: two restrictions of
different parents cannot meet because their immersion
images belong to disjoint parent interiors. The covering
is injective on H_e. Therefore the good output paths of
distinct parents are also disjoint, in particular distinct.
This is an actual injective correspondence of good leaf
sets, not an assertion about the whole original singleton
action.

### Borel and additive refinement

Assume the parent is supplied in the standard-Borel path
atlas used in the canonical-lift note, and the actual
retained predicates are the geometric fine/coarse predicates
there. On complete parents the maximal gaps and their ideal
endpoints have Borel codes. The choice of the unique primary
is Borel by the countable gap enumeration, testing the
cap base for e. The lifted crosscut radius supremum is
Borel (rational-time evaluations, in the anchor-normalized
strip lift). The number of retained inner components and
the good/bad predicate are Borel. For output path coding
one can use the compact trace in the ideal annulus of the
embedded arc, together with its canonical orientation;
the ideal endpoint data distinguish the two orientations.
The resulting map is Borel and injective on the good
parent family, so its image is Borel by Lusin-Souslin.
Joint path evaluation can equivalently be transported by
the Borel inverse. These facts are confined to the simple
proper arcs of the stated atlas and do not assert an
unproved atlas for arbitrary retracing paths.

For a finite disjoint Borel sublamination partition, modulus
is additive: restrict admissible metrics to the disjoint
Borel supports for the lower inequality and combine them
for the upper inequality. The supports are Borel by
Lusin-Souslin applied to the injective leaf/interior-time
evaluation. No arbitrary union of intersecting families
is treated as additive. Thus for the single and double
subfamilies S_1,S_2 of the good parents, their output
families D_1,D_2 are disjoint Borel sublaminations, and
(2) gives

\[
 \boxed{W(D_1\cup D_2)
 \ge W(S_1)+2W(S_2)
 = W(S_1\cup S_2)+W(S_2).} \tag{3}
\]

This is the useful local response to a deck collision.
It is not the broad coefficient-one Wave theorem: it
relies on a fixed common directed anchor, actual complete
lifts, and the explicit metric discard.

## 3. A finite stationary telescope with uniform loss

Fix h≥1. Let A be a Borel lamination of simple proper
inner-ended parents admitting singleton simple inner-ended
outputs through h actual retained steps. For each stage
j=1,...,h assume a common source inner access e_j as in
Section 2 for every relevant parent output at that stage.
The access may depend on j and F, but not on the leaf.
Assume the repaired geometric retained predicates and
the Borel presentation above. If some path ends at a
finite omitted cut, it may be separately removed at zero
width as in the prior finite-energy arguments. No assertion
about unverified native markings is included.

First discard all parents whose canonical h-lift is
incomplete, at cost at most 2^h V(F) by the automatic
vertical charge. Remove the zero-width nonrectifiable
core exception. The remaining complete lift supplies
complete canonical lifts of every intermediate actual
output on its own occurrence window, as proved in
COLLISION_GAIN, §2. All inner-ended retained restrictions
at each step lie on that one complete lift.

Now apply the primary-packet discard of Section 2 at
each stage, removing original parents at their first
bad primary. Crucially, no factor 2^(j-1) is required
to descend the cost of the j-th discard. At every
previous good step the primary-only metric estimate
W(S)≤W(output(S)) is valid for *any* subfamily of the
survivors. Compose those coefficient-one estimates back
to the original family. The j-th first-bad family
therefore has original width at most C_2, not 2^(j-1)C_2.

Let A_good be the remaining original parents, and E the
union of all discarded families. By subadditivity,

\[
 \boxed{W(E)\le E_h:=2^h V(F)+h C_2.} \tag{4}
\]

Every good parent has an actual good primary at every
step, and the intermediate good output maps are
injective on the leaf sets. Define k(α) as the number
of stages where it has two distinct retained maximal
inner restrictions. Both actual witnesses lie on the
canonical lift and have disjoint time windows. Partition
A_good into the finitely many multiplicity patterns
(r_1,...,r_h) in {1,2}^h. Each pattern is Borel. On a
fixed pattern the estimate (2) composes without additional
discard, giving W(D_h(pattern))≥2^k W(A_good(pattern)).
All final images of the patterns are disjoint Borel
sublaminations by injectivity on primary supports.

Writing A_good,k for the union of patterns with k double
stages and D_good for all final good outputs, additivity
on their disjoint Borel supports gives

\[
 \boxed{ W(D_{\rm good})\ge
   \sum_{k=0}^h 2^k W(A_{{\rm good},k}). } \tag{5}
\]

In particular, with A_good,coll the union of classes k≥1,

\[
 W(D_{\rm good})\ge
 W(A_{\rm good})+W(A_{\rm good,coll}). \tag{6}
\]

Unlike the earlier all-sheet bound 2^(2k−h), this result
has no majority threshold. Each genuine duplicate stage
gives a factor two; a single stage already creates a
positive excess if the relevant family has positive width.

The injectivity of the final leaf map is important.
Without it one could not add the widths of the image
classes. The proof does not infer injectivity from the
singleton output: it establishes it on the actual primary
packet using (1).

## 4. Quantitative response to a collision-rich residual

Suppose the original family contains a subfamily A_coll
of width at least ηW(A), 0<η≤1, each parent with at least
one genuine duplicate stage in its specified stationary
chain. Assume the final good outputs are contained in
one actual controllable Wave C, with the control constant
bounded in the native parameters required for terminality.
This last requirement must be checked independently.

Subadditivity and (4) give

\[
 W(A_{\rm good})\ge W(A)-E_h,\qquad
 W(A_{\rm good,coll})\ge\eta W(A)-E_h.
\]

Consequently (6) yields

\[
 \boxed{W(C)\ge (1+\eta)W(A)-2E_h.} \tag{7}
\]

For finite positive W(A), if E_h≤ηW(A)/4 then
W(C)≥(1+η/2)W(A). For a strict source terminality
inequality use a gain parameter smaller than η/2.
Since E_h is a bounded-horizon multiple of V(F) plus
an explicit additive constant, this supplies the
vertical-or-wider-Wave response for such a collision
fraction at sufficiently large absolute width. It
does not require either a uniform free condenser bound
or the earlier majority-collision threshold.

Conversely, under the same output-controllability
hypotheses, if every allowed output Wave has width
≤(1+λ)W(A), then

\[
 W(A_{\rm good,coll})\le\lambda W(A)+E_h .
 \tag{8}
\]

The sharper pattern version (5) gives a weighted excess
bound sum_{k≥1}(2^k−1)W(A_good,k)≤λW(A)+E_h.
Thus failure of amplification forces most of the
stationary mass into chains with exactly one actual
retained inner component per step, rather than merely
chains with fewer than half their stages doubled.

## 5. Relative continuation without a covering-degree descent loss

There is also an independent improvement of the analytic
common-crest step of the archive's
[Gate N1 relative continuation](../../mlc_unified/kkl_stationary_relative_wave_continuation.md),
Lemmas 2.3 and 4.1–4.3 and Proposition 7.1.
Keep its actual geometric directed-restriction existence,
fine refinement, native output typing and away-Shift
bounds as explicit hypotheses. This is not a validation
of the literal disputed unrestricted marking action.

For this paragraph a simple proper singleton output and
one actual directed retained restriction above a common
fine-marked crest interval J suffice; the complete-lift
premise is not needed for primary-only width transfer.
Choose e in the interior of J and perform (1). Every
surviving primary maps homeomorphically onto the entire
simple output. Distinct good primaries map to disjoint
output paths because they belong to the single injective
covering chart. In particular for any subset D of the
good output leaves its full good parent saturation S_D
satisfies W(S_D)≤W(D).

Moreover, if p(J) is a proper connected target
multi-interval, it is contained in each surviving
singleton output crest. Indeed the full source cap
lifts the output disk cap homeomorphically. The entire
J lies in the source singleton crest, so its covering
image lies in the output base and avoids the output
ends. Since the fine marking is pulled back from the
target marking, a complete source fine atom of J maps
onto the complete corresponding target atom. If an
output endpoint were in that target atom, its inverse
within this fine atom and its actual source endpoint
would contradict the injectivity of the cap base.
The image of the entire J therefore lies between the
two marked ending intervals, including the indicated
interior junctions where applicable. No aggregate-crest
conclusion is inferred from merely one chosen endpoint.

When the source theorem supplies J over BL_0 with
p(J) the entire circle, no surviving proper disk-cap
output can have that base. Thus the over-critical
family has width at most C_2 in this directed simple
output scope. The two-step precritical family first
has discard at most C_2 and then has a good output
over BL_0. The primary-only transfer, rather than
a full degree-two pullback, bounds its remaining
width by C_2. Hence one may use

\[
 c_{\rm crit}=C_2,\qquad c_{\rm pre}=2C_2
 \tag{9}
\]

under these actual directed/simple-output hypotheses.
The source-independent metric argument proves the
pruning needed for this scoped use of the published
annular toolkit. It does not prove directed existence
when the source's ideal-subset operation is ill-typed.

For a positive directed packet with a noncritical
crest and the actual one-step central/noncentral
output decomposition of N1, let e_b bound the
discarded over-critical and away output width.
After primary pruning their complete good saturation
has width ≤e_b, so the one-step relative loss is
at most C_2+e_b. Iterating on the successively retained
good families, the coefficient-one primary transport
at every earlier stage descends each new loss without
a covering-degree factor. Thus after h such steps
the total loss in original-parent width is at most

\[
 h(C_2+e_b). \tag{10}
\]

If an initial opposite-direction packet is disposed
of by the precritical bound (9), add 2C_2 once.
This is an explicitly constructed surviving
subfamily, not an assertion about every arbitrary
choice of inclusion-maximal A_n. It gives a
conditional alternative relative continuation
telescope with a linear number-of-steps loss.
For the collision gain on this chain restore the
complete-horizon lift restriction; that adds at
most 2^h V(F) in original-parent width, once.
The fixed common crest, actual retained paths,
Borel marking predicates and controllable output
containment remain essential.

## 6. Quantitative residual audit

In the setting of §3 take h=b+2<P and assume the
output Wave containment required by §4. Let A be
the actual stationary family entering that
telescope and put

\[
 J_b=(7b+3)2^b R(F),\qquad
 E_h=2^h V(F)+hC_2.
\]

By the latest-stage census of STAGE_ENDPOINT_CENSUS,
the subfamily with at least b+1 Julia-critical
stages has width at most J_b. It may overlap the
collision class. Do not add their widths as if
they were a disjoint partition; use subadditivity
to remove their union.

Let S denote the good parents with exactly one
retained inner restriction at every stage and at
most b Julia-critical stages. If the allowed
output Wave has width at most (1+λ)W(A), with
0≤λ<1, then (8) bounds the good collision class.
Combining with the Julia-stage charge and the
exceptional cost yields

\[
 \boxed{
 W(S)\ge (1-\lambda)W(A)-2E_h-J_b .
 } \tag{11}
\]

If the preliminary relative continuation losses
of (10) are also included in A, they must be
charged separately (or included in an enlarged
E budget), not silently suppressed.

Equation (11) is a precise residual necessity
statement: a sufficiently wide stationary
family that neither triggers the vertical
alternative nor produces a gain must have
large modulus in a physically characterized
single-retained edge-end class. In particular
every such parent has at least three
non-Julia-critical stages. Conversely if one
establishes W(S)≤B_b(R+V+1), the displayed
inequality closes the corresponding conditional
short-or-wider-Wave numerical branch at an
explicit absolute scale. No such uniform
bound is proved here. The exact
[attachment-screening example](ATTACHMENT_SCREENING.md)
shows why it cannot be inferred from general
nested-carrier geometry and bounded vertical
modulus alone.

## 7. Relation to the native stationary frontier

The finite-horizon directed source packet is the
remaining geometric input of this theorem. On an
actual stationary chain where the directed restriction
theorem of the archive has been independently verified
for the corrected geometric marking, the common
crest intervals supply the e_j used above. At a
protected central-corridor step the signed-crossing
argument in CANONICAL_LIFT_AND_DIRECTION supplies
the same input directly. This does not establish it
at every exceptional critical step, or validate the
literal unrestricted maximal-subset restriction of
KKL A.3.2.

There are now two available quantitative classes in
the stationary problem (they may overlap):

1. Julia-critical endpoints: the census of
   STAGE_ENDPOINT_CENSUS charges parents with more
   than b such stages at h=b+2 by (7b+3)2^b R(F).
2. Genuine duplicate stages: under the directed
   packet and actual Wave containment assumptions,
   (7)–(8) supply a terminal response or a small
   residual-width estimate for any fixed positive
   collision fraction.

After also removing the bounded complete-lift and
primary-confinement defects, the uncharged,
nonresponding subclass must be sought among parents
with a single actual retained inner restriction
at every step and at least three non-Julia-critical
endpoint stages at h=b+2. No claim is made that
this subclass is empty or automatically has zero
width. Its edge-end geometry, the native directed
packet realization at all required stages, and the
remaining marking and telescope interfaces are the
specific open obligations. In particular the
quadratic separator theorem by itself does not
force a second retained restriction; a second
raw gap can still be discarded by a genuine
coarse filter.

The proof is written conformal analysis, with the
finite charge/excess telescope formalized separately
in StationaryPacketGain.lean. No global proof ledger,
stationary closure, H1–H4, UPTCR or MLC promotion
is asserted. Prepared with ChatGPT assistance;
independent mathematical review pending.
