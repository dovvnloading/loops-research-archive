# Suffix-anchor response: deep contact or a second physical window

Continuation of [near-critical packet control](NEAR_CRITICAL_PACKET_CONTROL.md),
[canonical lifts](CANONICAL_LIFT_AND_DIRECTION.md), and
[auxiliary gap response](AUXILIARY_GAP_RESPONSE.md).

**Scope.** Under the corrected geometric contour marking and the actual
directed stationary singleton-chain hypotheses below, this proves a
replacement for the deep-contact premise: either a selected deep carrier
contact occurs, or an auxiliary raw gap already supplies the series
response. With the two-bank separator argument this yields a conditional
whole-family width bound O_b(R+V+1) for the positively oriented class.
No one-shot/sequential filtered-action equality, separate quantitative
attachment-angle calibration, or two retained output noncollision theorem
is used. This does not prove the native stationary theorem unconditionally.

## 1. Hypotheses and notation

Use the native rotation 1/q, h=b+2, h+1<q<=P, actual Kahn tower,
T_r=P_r^(-1)(T), X_r=U^r minus T_r, I_r and P_r as in
the filled-graph naturality note. Write C_r for the inner ideal circle
of X_r (in this note C_r is a circle, not a closed selected limb).
Write Omega_k for the rotational limbs, Omega^sel_n for the n-fold
selected inverse of the open critical limb within itself.
Assume the saturated monotone full-hull realization and canonical
vertex/edge access marking of the native marked-realization note;
in particular T is disjoint from Omega^sel_b, and physical limb
locality agrees with the cyclic order of BL_0,...,BL_(q-1).
The actual model/physical prime-end correspondence is required on the
finitely many full pulled carriers, and the corresponding boundary
covering squares commute. These are the finite extensions of the
nested-contour and monotone prime-end bridges, not the printed literal
unrestricted A.3.2 operation.

Assume the corrected one-step marking has these properties:

* its coarse block over each original atom A is a connected interval,
  refined by the fine covering marking; an end fine atom E in that
  block has continuous proper old-boundary image under I_1 in A
  (the geometric end-atom property used in NEAR_CRITICAL_PACKET_CONTROL,
  section 5, cf. KKL Proposition 6.6);
* the actual covering image of the geometric pullback of BL_k is
  BL_(k+1) for k noncritical, and that of the closed critical block
  is the entire old circle;
* the actual retained action tests the fine marked-path and
  one-coarse-atom exclusions, as in the corrected action.

Let A be a Borel lamination of finite positive width W of simple
proper parent paths with distinct ideal ends. For each parent suppose
there is the actual sequential untagged singleton chain alpha_j,
j=0,...,h, with alpha_0 the parent; every output is simple, has two
distinct inner ideal ends, ends at BL_0, and is individually crested
over the whole BL_(j+1). Require the same Borel path/occurrence atlas
as in COHERENT_PACKET_GAIN. In particular the positive initial
packet is selected before forming the family A, not obtained by
adding the negative packet through a saturation with other leaves.
The assumption is about actual paths, not only the union of
their combinatorial labels.

For the deep conclusion require that the initial end of alpha_h
in its positive cap orientation physically lands in Omega_0.
The exceptional width Z will measure parents for which this
is not established. This is automatic for the central-ending
positive-crest class if the final leaf does not crest over the
whole precritical block, by the circle-order argument of
CANONICAL_LIFT_AND_DIRECTION section 5 and physical landing
locality, modulo point gates. For a two-critical-end leaf or a
critical terminal end the base must traverse the precritical block.
If h+1=q-1, the entire final packet can be precritical; do not
pretend this case has been charged. An extra available singleton
step at the end, together with the verified two-step precritical
bound on the corrected action, is one sufficient way of removing
Z at bounded cost, as discussed in section 7.

All point-cut and infinite-length exceptions are removed at zero
width using the earlier finite-energy construction, with the
actual occurrence maps to descend the zero bound.

## 2. Lift a full atom coherently as an old-proper access

Here is an analytic lifting argument that does not require the
primary path to follow that atom through the entire tower.

Choose an original atom A_0 inside BL_1. Recursively choose an
old-proper end fine atom E_j in the coarse pullback of A_j,
and put A_(j+1)=P_1(E_j) on the inner ideal circle, for j<h.
It is a whole original atom inside BL_(j+2) by the noncritical
translation. We obtain a fixed finite chain of open atoms.

**Lemma 1.** For every j=0,...,h there is a whole fine atom B_j
on C_(h-j), with B_h=A_h, mapped homeomorphically onto A_h by
the boundary covering P_(h-j), on which I_(h-j) has a continuous
proper old-boundary limit in A_j. Moreover, the one-arrow
coverings between these suffix surfaces carry B_j
homeomorphically onto B_(j+1).

Proof. In the notation of the actual iterated fiber product let
f_(r-1):U^r→U^(r-1) be the last covering factor, and let
J_r:U^r→U^1 be the projection through the immersion factors
i_1,...,i_(r-1), with J_1=id. Then

    P_r=P_(r-1) f_(r-1),     I_r=I_1 J_r,
    P_1 J_r=I_(r-1) f_(r-1).                         (1)

These are the commuting tower identities. The restrictions
f_(r-1):X_r→X_(r-1) and P_1:X_1→X_0 are genuine double
covers. J_r maps X_r into X_1: a point mapping into T_1
would belong to K^r, with F of its filled-graph image in T,
hence F^r of that image in T by forward invariance.
Similarly I_(r-1) maps X_(r-1) into X_0. Both immersions
have degree one on the essential loop of these annuli.
Indeed a Jordan loop around the full filled set in its
embedded graph neighborhood maps to a Jordan loop around
the target filled set, containing its carrier. The
orientations agree by holomorphicity. No outer-end
properness of these immersions is required.

Assume B_(j+1) is constructed, and put r=h-j. The two
inverse intervals of B_(j+1) under f_(r-1) are whole fine
atoms of C_r. For every approach to a point of either
interval the right side of (1) tends to a point of A_(j+1)
on the target inner circle. On the universal strips
the two covering lifts are affine maps of angular
degree two, and the immersion lifts are periodic of
degree one. Equation (1) holds on the strips up to an
additive integral deck translation. It follows that
J_r extends to both open inverse intervals and its limits
lie in the two respective inverse arcs of A_(j+1) under
P_1. More explicitly, translating a lifted boundary
point of X_r by half a turn translates the lifted
f_(r-1) image by one full turn, hence its I_(r-1) image by
one full turn. Equation (1) then translates the lifted
J_r image by half a turn. The two inverse limits are
distinct and exhaust the two possibilities. The choice
of inverse arc is constant along the connected interval
by continuity. Choose the one whose limit is in E_j.
Composition with I_1 gives the asserted proper old
limit in A_j. Start at B_h=A_h. This proves the lemma,
including the fine-atom statement by the boundary
covering identity. QED.

In particular choose e_j in the interior of B_j for
each j<h. The entire atom B_j is old-proper, not
merely a label or a proper old-side germ. It follows
that no raw endpoint of a complete lift of alpha_j
in X_(h-j) can be in B_j: at an interior time its old
ideal limit would be on T, and at an original endpoint
it would be in a strict crest atom of alpha_j. The
endpoints at the finitely many cuts can be removed
at zero width as before. Crucially we have not asserted
that any prescribed sequential primary window
contains e_j in its final cap.

## 3. Full-tower critical saturation

**Lemma 2.** The entire pulled critical block on C_r, defined by
the nested geometric contour collapse of the full pulled model
carrier to the old carrier, has full boundary-covering image
under P_r. A raw end physically in the open precritical limb
is in the corresponding open pulled precritical block.

Proof in the saturated model. Write A for the old model hull,
A_s=G^(-s)(A), and use c_(s,t) for the monotone degree-one
contour collapse from A_s to A_t, s>=t. Use p_s for the
degree-two boundary covering from A_s to A_(s-1).
The ambient contour maps and their dynamical identity in
[ambient-angle exactness](../issue40_ambient_angle_exactness_20261124.md)
give

    c_(r-1,0) p_r = p_1 c_(r,1).                     (2)

Indeed compose both sides with the onto ambient-to-A_r contour
map, use nested collapse coherence, and apply the same ambient
dynamical identity to A_1 and to A_r. This uses the actual full
preimage A_r, not a selected sheet of the carrier.

A useful elementary fact about such a circle square is

    p_r(c_(r,1)^(-1)(S))
      = c_(r-1,0)^(-1)(p_1(S))                     (3)

for every subset S of the A_1 circle. To see the reverse
inclusion, the two preimages of any y under p_r are carried
bijectively by c_(r,1) onto the two preimages of c_(r-1,0)(y)
under p_1. Lift the square to real lines: for consecutive
preimages whose covering values differ by one, the degree-one
lower map changes by one, so the lifted upper map's values
are consecutive covering preimages, distinct modulo one.
This also proves (3) when S is closed, or is an arc with
specified omitted endpoints; no openness assumption is used.

Take S=c_(1,0)^(-1)(closure BL_0). By one-step critical
saturation p_1(S) is the full old circle. Nested coherence
and (3) imply p_r(c_(r,0)^(-1)(closure BL_0)) is the
whole A_(r-1) circle. Composing the remaining coverings
proves the claim for P_r. The degree-one physical-to-model
circle maps and the equal-degree covering squares transfer
the same surjectivity to the actual physical circles;
the proof of (3) applies with degree 2^r in place of two.
This is why merely knowing the image of the critical block
after collapsing the target would not suffice.

For locality, each model open rotational limb meets A
(it contains an original little Julia member). The
unique arc from any point of A_r in this limb to an old
point in the same limb avoids the dividing fixed point.
Consequently every added branch there attaches to A in
the same open limb, and all its contour accesses collapse
into that limb block. Old accesses there already have
this property. Monotone impression correspondence and
the singleton dividing-cut fiber give the asserted
physical locality. The same argument identifies the
old-proper atom of Lemma 1 with accesses collapsing
into its old positive limb: for old-proper limits
the contour map agrees with the old ideal limit.
QED.

## 4. Signed gaps on each suffix, including equal ideal ends

Work with alpha_j and its complete canonical (h-j)-lift.
The complete lift across its filled cap is supplied by
CANONICAL_LIFT_AND_DIRECTION section 3. The old-proper
atom B_j gives an actual end-tail on the disk-cap side
of that complete lifted parent: its I_(h-j) image tends
to a strict crest access. For a sufficiently late part
of the tail it avoids the completed parent. A path
from this tail to the outer collar inside X_(h-j)
can be chosen to make only finitely many transverse
crossings of the completed parent, by straightening
in the old annulus as in the earlier signed-crossing
proof.

For every raw inner gap orient its compactified curve
as a crosscut, and use its cap component not reaching
the outer end. The signed crossing sum along the
test path is one. Grouping crossings by raw gap
therefore gives

    sum_{gaps with e_j in open base} sign(gap) = 1.  (4)

Here sign=+1 if the cap side agrees locally with that
of the completed parent, and -1 otherwise. Finiteness
follows from the transverse test path; any gap with
e_j in its base separates that tail from the outer
collar, so it is met by the test path. Neither
retention nor uniqueness is required in (4).

For clarity about equal ideal ends, a simple proper
inner gap with coincident ideal endpoints closes to
a Jordan loop in the compactified annulus. If it is
contractible, its open base is empty; it contributes
zero to (4), since the tail is not its endpoint.
If it winds around the hole, its open base is the
circle minus the common endpoint. A strip lift of
that oriented base has length one. These essential
loops are included in the signed count and discarded
by the very same fixed-anchor metric: the proof
of the half-annulus estimate works with endpoints
x_-<0<x_+ and x_+-x_-<=1, including equality.
A span-one gap is necessarily bad. For distinct
ends a simple proper gap has a base of length <1;
in strip coordinates disjointness of deck translates
excludes interlacing endpoints. Good gaps over an
anchor thus have distinct ideal endpoints and simple
disk caps. The endpoint-cut and contractible-loop
cases do not create an uncounted positive crossing.

Apply this first at one step to the chosen end fine
atom E_j. Prune bad raw gaps over its fixed anchor
at cost C_2=pi log(32)/(log 2)^2. Every surviving
gap over that anchor contains E_j between its ends,
and passes both geometric filters by the end-atom
argument. Its covering projection is simple and,
by singleton output, is alpha_(j+1). Two different
lifts of the same proper disk cap cannot contain the
same anchor. Thus (4) gives the unique positive
primary after pruning, even if there were essential
raw loops before pruning. The resulting common-chart
primary transports and the full canonical lift cost
give a good original family G with

    W(G) >= W-E_p,     E_p=2^h V+h C_2.              (5)

This uses the coefficient-one descent in COHERENT_PACKET_GAIN.
The composed primary chain has literal nested time windows;
its final suffix gap is one of the actual maximal raw
gaps on each complete lifted alpha_j, by the segmented
occurrence and canonical exhaustion theorems.

Now perform (4) on the full suffix for each j<h.
For any parent in G, either that suffix's selected final
primary is a positive gap over e_j, or a different
positive raw gap over e_j exists. The latter is disjoint
in alpha_j time from the final primary, since both are
maximal raw gaps of the same contact set. On the original
parent this is a literal disjoint auxiliary subinterval
inside the stage-j primary window, not necessarily a
surviving sequential retained restriction. We may
also use such an auxiliary when the primary is positive.

Remove the original parents with any bad candidate at
suffix j at cost at most C_(2^(h-j)), by confinement,
immersion square-sum, and the coefficient-one good
prefix transport. It is immaterial whether the bad
gap is a primary or an auxiliary. Sum these costs
to get E_s=sum_(r=1)^h C_(2^r).
All remaining auxiliary suffix packets have actual
simple disjoint Borel terminal outputs: their gap
interiors are disjoint in the canonical source and
their common half-disk chart is injective under P_r.
Each contains the whole A_h strictly between its
endpoint atoms, since B_j was old-proper. For each
j there is one such packet; no q-dependent enumeration
of remote ends occurs.

The near-critical packet lemma generalizes directly
to the consecutive bank BL_0,...,BL_(h+1) of at most
6b(h+2) atoms: use the antipodal chart cut, allocate
its atom and the endpoint-bank atoms first; the
remaining proper common base traverses all of BL_0.
If the bank is the entire circle, the localized
classes already exhaust the packet. Thus every
suffix packet is (6b(h+2)+1)-controllable. We use
the corrected ordered-base definition and the full
circle convention of NEAR_CRITICAL_PACKET_CONTROL.
This includes the long same-atom case there.

## 5. Actual depth-h carrier contact for the no-auxiliary class

Assume the parent has no suffix auxiliary after the
above exclusions and satisfies the final orientation
condition of section 1. Let x be the physical value
on the original parent at the initial endpoint time
of its final primary window. It exists by the actual
endpoint formula of STAGE_ENDPOINT_CENSUS section 2.
Write x_j=F^j(x) in K. By the compatible fiber-product
chain, x_j is the initial physical graph end of the
full suffix primary at stage j, and x_h is the
initial end of alpha_h. The end may be interior in
earlier alpha_j; no claim that it is a retained
endpoint at every earlier stage is used.

By section 4 the full suffix primary has e_j in its
positive cap base. Suppose x_(j+1) is in Omega_0.
Its physical inverse origin is either the selected
inverse within Omega_0 or the precritical open limb.
If x_j is precritical, its initial ideal access
is in the pulled precritical block by Lemma 2,
whereas e_j collapses into BL_(j+1), with
1<=j+1<=h<=q-2. The positively oriented cap base
from that initial end to e_j must traverse the
entire pulled closed critical block. Its P_(h-j)
image is then the full circle, by Lemma 2. This
is impossible: a lift of the disk cap of the
simple proper alpha_h maps homeomorphically
onto that cap and has a proper base image.
Thus x_j belongs to the selected inverse of
Omega_0 inside Omega_0.

Starting at x_h in Omega_0 and descending j=h-1
to zero proves all h inverse steps are selected.
Hence x belongs to Omega^sel_h. It is in
F^(-h)(T), since x_h is an actual physical
landing in T. Because Omega^sel_h is disjoint
from T by the full-hull pruning, its parent
time is interior. Therefore the original
complete lift has the actual carrier contact

    theta_h(t_*) in Gamma_h(Omega^sel_h) intersect T_h,
    0<t_*<1.                                       (6)

This is the selected deep contact required in
AUXILIARY_GAP_RESPONSE, without assuming that
the same endpoint was retained throughout the
earlier chain, and without assuming that both
raw sides survive the coarse marking. More
precisely, the proof establishes the alternative
"actual contact OR actual auxiliary", not that
every original stationary parent has the contact.

## 6. Combine with the separator and series response

Set N_b=12b*2^h, N=h+N_b, and E_a=E_s+N_b*C_(2^h).
Assume the full separator host/fine-side realization
of AUXILIARY_GAP_RESPONSE; section 8 below gives
a sufficient graph-side certificate. On the no-suffix-
auxiliary class with (6), either both actual bank
components are hit, charged at <=4R by the two
degree-two end budget, or one is avoided and the
two raw separator gaps give a distinct auxiliary.
Their at most N_b confined packets and their
control constants are those of NEAR_CRITICAL_PACKET_CONTROL.
The union of suffix and separator packets has at
most N members, each with at most k=6b(h+2)+1
localized modules and one over-critical module.
The primary terminal output is a central-ending
Wave, hence at most 6b-localized, by its actual
disjoint good output realization.

Let S be the parents in G with a good auxiliary
from either route, and let w=W(S). No additive
measure on overlapping bad classes is assumed:
subadditivity gives

    w >= W-E_p-E_a-4R-Z.                            (7)

For a suffix auxiliary metric, pull through the
injective terminal suffix chart and push through
I_(h-j). This gives length at least one on its
literal auxiliary interval of alpha_j, at energy
at most the auxiliary packet width. Pull back
further along the j chosen good prefix charts,
with square-sum immersion pushforward, still
without increasing energy, on the corresponding
original-parent interval. This is disjoint from
the final primary window. Separator auxiliaries
are the same construction with j=0. Square-sum
the at most N metrics, whose total energy tends
to B=sum of auxiliary packet widths. Thus the
series proof of AUXILIARY_GAP_RESPONSE applies
on the original parent even when different
suffixes are used or auxiliary and primary
terminal outputs coincide. The good primary
images of S and G minus S have disjoint Borel
supports, and coefficient-one width transport
on the latter gives

    W(primary output) >= W-E_p+w^2/B.              (8)

If B=0, then w=0; an infinite-width relevant
packet already violates finite near-maximality.

Suppose all of these actual controllable outputs
have width <=(1+lambda)W. For finite W>0 and
lambda>=0, equations (7)-(8) imply

    w^2 <= N(1+lambda)W (lambda W+E_p).

In particular take lambda=1/(64N). If

    E_p <= W/(64N),    E_p+E_a+4R+Z <= W/2,         (9)

then w>=W/2 and B<=2NW. Equation (8) gives
W(primary output)>=W+7W/(64N)>(1+lambda)W,
a strict contradiction, unless an auxiliary
already violates the width cap. Consequently
near-maximality forces

    W <= max(64N E_p, 2(E_p+E_a+4R+Z)).            (10)

For Z=0, or Z bounded uniformly in b, this is an
explicit O_b(R+V+1) stationary width bound on the
actual directed family. It does not need a
uniform internal free-condenser calibration,
a positive angular lower bound on a protected
old side, distinct terminal outputs of both
portions, or a bound on the number of all
remote end atoms.

## 7. The horizon and the remaining native integration

The final orientation exception Z is real. In the
printed N=b+3 horizon h=N-1 there is just one
singleton step left; the two-step precritical bound
cannot silently be applied to alpha_h. For q<=h+1
a different small-q/critical-wrap estimate is
needed, rather than using nonexistent positive
limb indices. For q=h+2 the final crest is
precritical, not a positive nonprecritical crest.

A sufficient route for the full positive stationary
family is to carry out the relative continuation
and small-breaking reduction with one extra
unbreakability step N'=b+4, keeping the selected
contact horizon h=b+2. Under a verified geometric
two-step precritical bound c_pre, the exceptional
final precritical class then has width <=c_pre
at stage h, hence <=c_pre on the good original
family by the primary charts (or <=2^h*c_pre
without them). If the final prescribed crest is
itself precritical the same bound charges the
entire packet. If a critical crest occurs earlier,
the one-step critical bound charges that packet
on the corresponding valid horizon. The numerical
continuation proof has a fixed finite extra-step
cost, but the native upstream unbreakable extraction
and downstream small-breaking/terminality interface
must be rechecked at N'. This note does not assume
that the source's printed N already supplies it.

The width threshold and response here are relative
to W(A), and the terminal class must include the
stated control constants. If A is extracted from
an ambient Wave, its relative-width fraction and
all earlier continuation losses must be charged
in the ambient terminality comparison. No ledger
status or global MLC assertion follows automatically.

## 8. Graph-side certificate for the separator fine atoms

The fine-side premise can be checked on the
saturated finite graph of vertex continua rather
than by a conformal angle estimate. Here is a
sufficient exact marking condition and proof.

In the model assume the original marking cuts
are the access-complete cuts at vertex/edge
junctions and singleton graph vertices, as in
the native marked-realization note. The critical
values of G^h are in the original vertex bodies.
The full inverse graph has finitely many whole
inverse vertex bodies and singleton vertices,
and the remaining open edges are unbranched
inverse copies of the original open edges.
For a full inverse little-Julia vertex J, every
branch leaving J starts through one of the
finitely many incident edges. Its root lies in
J and is a preimage of an original contact;
these roots are preperiodic under the cited
finite original contact census. Every component
of the graph minus J has one root by the
dendrite property. Multiple branches at one
root are grouped by their distinct J-accesses,
not by their planar root alone.

For the model contour collapse to J, the fiber
of each such host comprises the complete
contour block of the corresponding branch
group, including its two extreme gates.
A positive arc between consecutive distinct
hosts lifts to an actual open J-side sector
between those extreme gates; all its model
landings lie in J. The extreme gates are
fine marking cuts: on their branch side a
one-sided edge germ is an unbranched inverse
of an original edge side, and on their J side
the covering sends the adjacent vertex germ
to the target little vertex. The change of
side occurs at the original marked junction
access. Finiteness of the incident edges
ensures such a one-sided germ at the extreme
of a host group, including when more than
one branch has the same host. This is the
exact access-complete marking assumption:
a coarser marking that fails to mark that
junction is not enough. Thus the nonempty
open sector is a union of whole fine atoms,
at least one. Every such atom maps into the
target little-Julia vertex marking.

Under the saturated physical monotone
prime-end correspondence each preimage cut
has a singleton boundary fiber by the
degree-matching covering argument. Its open
sector pulls to the corresponding physical
interval with the same fine cuts, and its
impressions lie in the physical J. The
finite branch group compactness and distinct
root/deep host certificate of SYMMETRIC_SEPARATOR
then supply the remaining hypotheses in
AUXILIARY_GAP_RESPONSE. This checks the
fine-side condition *if* that exact model
side/cut identification and its physical
lift hold for the actual source carrier.
It is not an independent validation of
the source's unrestricted maximal-subset
marking or of the entire non-LC realization.

## 9. Checks and disposition

The accompanying check_suffix_anchor_response.py
exhausts finite covering squares with monotone
degree-one lifts (including arbitrary subsets),
cyclic order, backward critical/auxiliary logic,
signed-gap patterns, and exact series scales.
It is not a test of prime-end or conformal
geometry. Two finite theorems are added to
StationaryPacketGain.lean for the backward
dichotomy and strict response scale, pending
kernel CI at this revision.

The principal new conclusion is that deep
contact is no longer an independent premise
of the width response on this oriented
stationary class. The remaining issues are
the corrected actual marking/relative
continuation, the final orientation or extra
horizon, the saturated exact graph/host-side
realization, and the terminality comparison.
No native or global ledger promotion.
AI-assisted written proof; specialist review
pending.
