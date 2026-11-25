# Precritical terminal response without an extra unbreakability step

Continuation of [SUFFIX_ANCHOR_RESPONSE](SUFFIX_ANCHOR_RESPONSE.md).
This removes its final-orientation width exception from the conditional
stationary estimate without requiring N=b+4 unbreakability.
The native horizon h=b+2, N=h+1 suffices for this part of the argument,
provided the last available singleton output is an actual simple proper
inner-ended path with distinct ideal ends, and the geometric assumptions
below hold. No unbreakability of that last output is assumed.

The crucial pair of old-proper accesses is taken on the actual critical
little Julia vertex, not on two arbitrary attached branches. The proof
uses raw gaps and metrics, not a symbolic doubling of an untagged leaf.

## 1. An actual deck pair on the old critical vertex

Use the saturated full-hull model and the exact access-complete
vertex/edge marking of SUFFIX_ANCHOR_RESPONSE section 8 and the
[native marked realization](../issue40_native_marked_realization_local_gates_20261124.md).
The primitive little Julia sets are nondegenerate model vertex
continua. The old carrier contains the entire original small cycle.
The full inverse graph has finitely many whole preimage vertex bodies
and unbranched open edges, with the complete fine marking cuts at
their accesses, obtained by the actual boundary covering.

In the one-step source the critical vertex J=Gamma_1(K_0) is an
entire degree-two preimage of K_1 (the whole-component theorem).
In particular P_1^(-1)(K_1)=J: the degree two on the critical
component exhausts the total degree. Also J lies in the old
carrier Gamma_1(T), not just in the enlarged carrier T_1.
Every branch of the enlarged model carrier leaving J attaches
through one of the finitely many incident preimage edges,
at a contact which maps to an original marked K_1 contact.

There exists an original marking atom A on the K_1 vertex side
whose interior avoids the contact landings: the vertex is a
nondegenerate subdendrite, and there are only finitely many
attachment hosts on its own prime-end circle. Between successive
hosts the open vertex-side arcs give complete marked atoms by
the graph-side argument. In the case of just one or no host,
use the corresponding nonempty vertex-side interval; the
marking must have an actual vertex-side atom. This is an
explicit exact-marking check, not a property of arbitrary
coarse labelling.

The two inverse fine atoms E^+, E^- of A under P_1 on C_1
are supported on J. Indeed their impressions map into K_1,
and the whole-inverse identity forces those impressions
into J. The model interior landings avoid the finite
contact roots: otherwise their images would be original
K_1 contacts, whose accesses are marked cuts. The physical
monotone impression comparison transfers this assertion.
Near each such compact physical impression, old and
enlarged carriers agree: they both contain the whole J;
all other model branch closures meet J only at the
finitely many excluded roots. Saturation and compactness
give the same neighborhood separation for their physical
lifts. Thus the ideal chart is the actual old one there.
For example transfer prime-end crosscut chains whose
closures eventually lie in this common neighborhood;
their small end domains are the same on both sides of the
inclusion, since there is no carrier difference nearby.
The embedded filled-graph collar then gives the proper
old-boundary limit under I_1. This applies to every
interior access of E^+ and E^-; its physical old image
is in the critical open limb. In particular both whole
fine atoms are old-proper over BL_0.

Choose a fixed actual access a in A. Its two inverse
accesses e^+,e^- lie in E^+,E^-, respectively. In the
normalized source cylinder their distance around the
inner circle is exactly one half, by the degree-two
annular covering. No lower bound on the angular size
of the old physical side or on an attached-branch
angle is needed. This pair is a source of two *different*
raw windows after confinement, even if both covering
images are the same path. Neither selected deep contact
nor an intermediate unbreakability assumption is
needed to produce it.

## 2. An over-critical width cap with no retention hypothesis

Let O be any actual Borel lamination of simple proper
inner-ended paths with distinct ideal ends, individually
crested over the whole BL_0. Suppose every relevant actual
controllable output Wave has width at most M<infinity,
where M is a common ambient threshold. Use the pair of
section 1. First charge the incomplete one-step canonical
lifts by 2V, modulo the zero-width finite-energy exceptions.
For each surviving complete parent the signed-crossing
argument of SUFFIX_ANCHOR_RESPONSE section 4 applies at
each of e^+,e^- because their whole atoms are old-proper
and the old image is a strict crest. It yields a positive
raw gap over each. Discard bad gaps at the two anchors
at total cost 2C_2, with C_2=pi log(32)/(log 2)^2;
equal-end essential loops are included in that discard.

Each remaining gap is contained in the fixed half-disk
chart of radius 1/8 about its anchor in the source
strip. The two projected charts are disjoint (the
anchors are half a circumference apart), hence the
gaps witnessing the two anchors have different
literal parent-time windows. The covering is injective
on each chart, so each packet's terminal outputs are
actual disjoint simple Borel paths. The entire A lies
in the crest of each. Its limb is BL_1; the generalized
near-critical packet lemma with the bank BL_0, BL_1
makes each packet at most (12b+1)-controllable.

Take admissible metrics on the two output packets,
pull each through its fixed injective chart, and push
through the immersion by the all-sheet square sum.
Their energies tend to the packet widths B^+, B^-,
respectively. On the surviving parent their two unit
lengths occur on disjoint intervals. The metric
one-half the square root of the sum of the squared
metrics therefore has length at least one and energy
at most (B^++B^-)/4. Since each packet has width <=M,

    W(O) <= M/2 + L,      L=2V+2C_2.               (1)

This is a relative terminal width cap, not the old
absolute bound on every unbreakable over-critical
Wave. In particular it holds with no retained action
at this step. Even if the two packets have identical
output support, the metric proof charges each once
and uses only the disjoint parent windows.

## 3. Precritical packet: a common primary and a mixed cap

Let Z be an actual source subfamily crested over the
whole precritical limb BL_(q-1), with actual simple
distinct-ended singleton outputs for one step. Its
source may be an earlier good primary prefix of the
original stationary parent family, and the width
threshold M is relative to that original input.
All source-to-original transfers below have coefficient
one along such a good prefix; alternatively the lemma
can be applied directly at the current stage.

The geometric pulled precritical block S has covering
image the proper block BL_0. Thus P_1 is injective
on S and its normalized angular length is <1/2
(the target BL_0 has a nonempty complementary open
limb). It is a connected run of fine atoms by the
corrected marking. Choose its first and last fine
atoms, both old-proper: they are the first fine
atom over the first old atom and the last fine
atom over the last old atom. This uses both end
atoms of the geometric Proposition 6.6 property.
If there is only one fine atom, use it once.

As in section 2, charge incomplete lifts by 2V
and all bad candidates at the two fixed anchors
by 2C_2, hence discard at most L. The signed
count supplies a positive gap for each anchor.
Each good gap passes the two retained filters by
the end-atom criterion. Its projection is the
unique actual simple output delta of its parent.
There can be only one gap over each of these
fixed anchors, by the disjoint base arcs of
distinct lifts of delta's cap.

Use the first-anchor gap as a common primary
for all remaining Z. Its fixed covering chart
gives an injective Borel output packet D, whose
members crest over its target atom in BL_0.
The near-critical bank argument, now using BL_0
alone, bounds its control by 6b+1. In particular
P=W(D)<=M. Split the good parents into two classes
and their disjoint output sublaminations into
D_double and D_over, with widths P_double and
P_over, so P=P_double+P_over.

* In the double class the first and last gaps
  are distinct. Both map to the same delta,
  so the two witnesses are its exact two deck
  lifts. Pull an admissible metric on D_double
  back to those two injective charts, with area
  at most twice its output area and length at
  least two on disjoint parent intervals.
  Therefore the double class has width at most
  P_double/2, also after good-prefix descent.

* In the other class a single good gap covers
  the two chosen anchors. Its base contains
  the whole first and last fine atoms (their
  interiors are old-proper, and cut endpoints
  are negligible). The short base of a
  confined gap has angular length <1/4; it
  cannot join the two anchors the other way
  around the circle, outside S, since S has
  length <1/2. It therefore contains the entire
  S between its endpoint atoms. If S is one
  fine atom the same conclusion is immediate.
  The simple covering image delta crests over
  all BL_0: the injective cap covering maps S
  onto BL_0 and its ends lie outside that
  image. Hence D_over is an actual leafwise
  over-critical packet. Coefficient-one
  transfer bounds this source class by P_over.

The important point is that the two cases share
one common injective primary output packet.
Their output widths add on disjoint Borel supports,
not by summing arbitrarily intersecting waves.
Apply the next-step bound (1) to D_over. There
is no need for delta to be unbreakable at this
next step, as (1) uses raw gaps alone. Thus

    P_over <= M/2+L.

By subadditivity for the source classes, additivity
for their disjoint output supports, and the initial
discard L, we get the uniform mixed estimate

    W(Z) <= L + P_double/2 + P_over
         = L + (P+P_over)/2
         <= 3M/4 + 3L/2
         = 3M/4 + 3V+3C_2.                       (2)

The same estimate holds for the original parents
which map into this precritical packet by the
already-good primary prefixes: every one-step
exception is descended by coefficient one, as
are both good class width bounds. No multiplicity
penalty in the prefix length occurs. In particular
(2) is valid for the final orientation-exception
class of SUFFIX_ANCHOR_RESPONSE with only one
additional singleton image, and not two additional
unbreakability steps. It does not claim an absolute
small-width estimate independent of M.

## 4. Integrated stationary width bound including the orientation exception

Use the h=b+2 setting of SUFFIX_ANCHOR_RESPONSE,
with q>=h+3 first. Assume all its hypotheses for
the actual directed simple stationary chain,
the saturated graph/host realization, and the
one-step property of section 3 on the exceptional
precritical class at stage h. The source class
still ends at BL_0 at stage h, so modulo the
physical gate exceptions every leaf either
has an initial physical critical end, or
crests over BL_(q-1). No orientation assumption
on the entire family is now imposed.

Let W>0 be the width of the stationary family A,
let G be its primary-good family through h,
and put, as before,

    E_p=2^h V+h C_2,
    N_b=12b*2^h,  N=h+N_b,
    E_a=sum_(r=1)^h C_(2^r)+N_b*C_(2^h).

Suppose every relevant actual controllable Wave
has width <=M=(1+lambda)W. The final primary and
all suffix, separator, precritical and over-critical
response packets have control bounded by
6b(h+2)+1 (or the smaller constants above).

By (2) the orientation-failing subfamily of G has
width <=3(1+lambda)W/4+3(V+C_2).
No bound on its width before the primary discard
is needed. On the other leaves, the suffix
dichotomy gives either an auxiliary already, or
the true depth-h selected carrier contact. The
two-bank hit charge or separator auxiliary then
applies as in the preceding note. Subadditivity
gives for the good auxiliary subfamily S of G,

    w=W(S) >= W - 3(1+lambda)W/4 - E_all,
    E_all=E_p+E_a+4R+3(V+C_2).                  (3)

The precritical and over-critical comparison
packets are not counted as auxiliaries of the
stage-h primary: their windows could lie inside
that primary. They are used only for (2).
The N actual suffix/ separator packets used
for the series response still have total width
B<=N(1+lambda)W. All their literal auxiliary
intervals are disjoint from their respective
final primary intervals. The previous series
proof therefore gives

    W(primary output) >= W-E_p+w^2/B.           (4)

Take lambda=1/(512N). If E_all<=W/16, then
(3) yields w>=W/8 (indeed a larger fraction).
If also E_p<=W/(512N), then B<=2NW and (4)
gives the strict response

    W(primary output) >= W+3W/(512N)
                         > (1+lambda)W.

The B=0 case would force w=0, inconsistent
with the positive fraction; an infinite
auxiliary or primary width is already a
response. Consequently, under the displayed
near-maximality hypothesis,

    W <= max(512N E_p, 16 E_all).               (5)

This is the conditional O_b(R+V+1) estimate
on the entire actual positively directed
stationary family, without the Z orientation
term of the preceding note.

For the small-q case q<=h+2, stop instead at
the first precritical positive crest, j=q-2
(including j=0 if q=2). It suffices to have
the actual directed singleton central-ending
chain through j and the one remaining actual
simple singleton at j+1; do not iterate the
positive crest through the wrap. With the
same primary-good construction up to j the
discard is E_j=2^j V+j C_2, and the entire
good family is the precritical packet.
Equation (2) then gives

    W <= E_j+3(1+lambda)W/4+3(V+C_2).

For lambda<=1/6 this implies
W<=8(E_j+3(V+C_2)), which is uniformly
O_b(V+1) since j<=h. In particular the
borderline q=h+2 does not require a nonexistent
positive nonprecritical terminal crest.
The available horizon N=h+1 is sufficient
for the singleton at j+1. No actual
singleton is required at j+2, only the
canonical one-step raw lifts of D_over in
the ordinary tower. The finite-horizon
stationary chain still must be constructed
up to the indicated stop.

## 5. Exact graph-side check for the end-atom property

Here is a sufficient independent geometric
certificate for the corrected end-atom premise,
under the same exact saturated graph realization.
This is not a proof of the literal A.3.2
maximal-subset operation.

In the model take the old minimal hull A of the
cycle vertices, B=G^(-1)(A). The original contact
set is finite and forward invariant (native
marked-realization section 2); the singleton
old graph vertices have their source-prescribed
forward invariance. Thus every old marked landing
is either on a whole original little vertex
(which is a whole preimage vertex in B), or is
a singleton preimage graph vertex. Its covering-
fine marking includes all accesses over its
marked landing, by the original exact marking
and its pullback. The inward extremes of the
collapsed host fiber at an old cut are fine
cuts, since they land at that old cut.
Consequently the inverse of an open old atom
under the geometric contour collapse is a
connected union of whole fine atoms with the
usual omitted-end convention.

Near an old marked landing only finitely many
preimage edges can leave its whole old vertex:
the other finitely many vertex bodies are compact
and disjoint. The local finite-host argument
of the native marked-realization note therefore
gives a regular old-side chart approaching the
inward extreme of the collapsed cut fiber.
The first fine atom of the open block contains
such an old-side subarc. It is either a side
of the preimage vertex containing that old
landing, or a side of an open preimage edge
incident there. In the vertex case the entire
vertex belongs to A. In the edge case the
whole open edge belongs to A as soon as a
nonempty part of it does: A is the union of
unique dendrite arcs joining original marked
little bodies, all of which are whole vertices
of the preimage graph. Such an arc cannot stop
in an unbranched open edge; it traverses that
entire edge or avoids it. This is the minimal
full-hull assumption, not an assumption that
all of B minus A has finitely many components.

In either case the interior of the fine atom
is away from the finite marked incident
edge-contact landings, so B and A locally
agree near each of its impressions, as in
section 1. On the saturated physical lift the
same is true by compactness and the monotone
impression formula. The embedded collar and
prime-end chart give actual continuous proper
old limits on the whole fine atom. By the
geometric collapse it maps within the
specified open old atom. Apply the same
argument at the other end to get the last
fine atom. No assertion about all interior
atoms of a coarse block is needed; such atoms
could be inside added vertex bodies with
many attachments.

This certificate presupposes the exact
vertex/edge access-complete marking and
its finite full-inverse graph incidence
(in particular the regular inward cut
charts). These are source-specific checks
on the saturated model, not consequences
of merely naming a little Julia cycle.
Under the corrected geometric action they
give both end atoms; the literal source
restriction is not reinstated.

## 6. Verification and exact remaining scope

The companion exact checker tests the short
precritical arc implication, opposite deck
chart geometry on finite circles, the mixed
cap algebra, and the integrated response
scale. It is not a test of the native
dynamics or prime-end marking. The finite
mixed-cap and strict-scale inequalities
are added to StationaryPacketGain.lean.

Together with SUFFIX_ANCHOR_RESPONSE the
deep-contact and final-orientation gates
are replaced by a bounded family of
actual response packets under the stated
geometric/chain hypotheses. This still
does not prove the actual corrected
relative continuation starting from an
arbitrary controllable ambient Wave,
the required relative width transfer
and terminality comparison, or the
source's literal marked action. In
particular (2) is not a substitute for
an absolute precritical discard in a
proof that needs that stronger statement;
the source-relative N1 induction and
initial positive/negative extraction
must be justified independently. The
upstream source small-breaking and
downstream native/global integrations
remain open. No canonical ledger status
is promoted. AI-assisted written proof,
specialist review pending.
