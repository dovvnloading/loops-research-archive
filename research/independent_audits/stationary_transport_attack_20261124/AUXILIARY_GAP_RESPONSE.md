# Raw separator gaps and a series-or-terminal response

2026-11-25. This is the final response reduction of the
[coherent-packet telescope](COHERENT_PACKET_GAIN.md) together
with the [physical deck separator](SYMMETRIC_SEPARATOR.md).
It bypasses the need for both auxiliary paths to survive all
intermediate coarse filters, and bypasses a noncollision
assertion for their covering images. The remaining native
premises are an actual selected deep encounter and uniform
controllability of the auxiliary outputs. Neither is inferred
from the topological separator alone.

## 1. Two raw gaps from a deep carrier encounter

Use the actual finite Kahn tower at h=b+2<P with h<q,
I_h,P_h:U^h→U, full pulled carrier T_h=P_h^(-1)(T),
and X_h=U^h minus T_h. The proper annular covering has
degree d=2^h. Let α be a finite-length simple inner-ended
parent complete at h, and θ its canonical complete lift.
By the canonical-lift theorem all its raw inner-ended
restrictions are the gaps of the closed contact set
D_h=θ^(-1)(T_h). Their windows have the exact original
parent parameter. In particular θ(0),θ(1) belong to Γ_h(T).

Assume the actual parent has an interior deep *carrier*
contact:

\[
 \theta(t_*)\in\Gamma_h(C_h)\cap T_h,\qquad 0<t_*<1 .
 \tag{1}
\]

This is stronger than hitting an arbitrary part of C_h
outside the pulled carrier, and weaker than a retained
two-sided occurrence at that contact. It follows if an
actual proper raw restriction with an ideal endpoint
physically localized in the selected terminal limb has
been constructed, using the physical landing argument
in PREFIX_POTENTIAL_CHARGE. The source line-1600
assertion still needs this realization.

Consider Q_n, n=b or b+1, and J=Γ_h(Q_n). It is an
entire final deleted little-Julia component and is
contained in T_h; see VARIABLE_END_EXIT_TRANSFER,
Corollary 5.3. Suppose θ avoids J. The full-carrier
separator theorem puts Γ_h(T) and the deep contact
in different components of T_h minus J, since C_h
is contained in C_(n+1). Assume the saturated finite
graph-of-vertex-continua model and host-access
hypotheses of SYMMETRIC_SEPARATOR, §2. In the
model each connected branch leaving J has one root
on its vertex body. There are finitely many such
branches, with compact closures meeting each other
only within J; their physical inverse lifts have
the same property by saturation and monotonicity.
Group branches by their actual host access in the
annulus U^h minus J. The root and selected deep
branches have distinct hosts by the quadratic
separator and its selected univalent transport.
The two named branches already occur at horizon
n+1; increasing the full carrier to h cannot
change their old attachment to J in a dendrite.
The union of closures of branches of one host
is compact, and different such groups are
disjoint off J.

The closed lifted trace is compact and disjoint
from J, so its distance from J is positive in a
disk coordinate. Hence the contacts of θ with
the distinct host groups are disjoint closed
subsets of [0,1]. They cover D_h. The contacts
at times 0,1 have the root host and that at t_*
has the deep host. It follows that on each of
[0,t_*] and [t_*,1] there is a gap of D_h with
its two endpoints in different host groups.
For example, starting at time 0, take the first
contact outside the initial host group before
or at t_* (the first time exists by closedness);
take the last initial-group contact before it.
Between those two times there is no contact:
this is an actual maximal gap. Repeat from t_*
to 1, starting with the deep group. The two
open intervals are nonempty and disjoint.

They give two genuine maximal simple inner-to-inner
raw restrictions in X_h, with both endpoints
on T_h, but with endpoints on different branches
leaving J. The annular properness theorem supplies
their actual ideal limits. This argument avoids
any assumption that the two windows are precisely
(0,t_*) and (t_*,1), or that the parent intersects
only one added branch.

### The explicit fine-side condition

For the next step require the following native contour
realization condition: between two consecutive distinct
attachment hosts on J, the positive boundary-side sector
of J is a union of whole fine marking atoms of the
actual covering-pulled marking P_h^*I, with at least
one such atom in every nonempty sector. The host
blocks are the complete contour blocks of the
corresponding branches, as in the saturated model
geometric contour action. In particular no branch
is inserted across the side of a different host.
This condition holds in a finite embedded regular
vertex-continua realization when the fine marking
is exactly its access-complete induced marking.
For the general native non-LC case it is an
explicit acceptance test, not a consequence of
coarse branch labels.

Under this condition, the disk-side base of any
gap connecting different host groups contains at
least one whole fine atom supported on J. To see
this, collapse every complete branch contour
block to its host on the inner ideal circle of
U^h minus J. The two endpoints of the gap belong
to two distinct fibers. The oriented base
interval between them must traverse a positive
arc between those host points, and hence a
complete side sector between successive distinct
hosts. Its inverse on the actual J-side contains
one whole fine atom. This applies to whichever
of the two oriented arcs is the actual disk-side
base; it does not identify the two possible
relative homotopy classes.

Every such fine atom maps under P_h to one of
the original side atoms on the final cycle member
K_(h−n). Since at most 6b atoms occur in that
physical limb, there are at most 6b·2^h such
fine atoms. This is a conservative bound: it
uses the full covering degree, not a claimed
degree on a selected side. For the union of
the two possible separators n=b,b+1, use
N_b=12b·2^h candidate anchors. Choose one actual
inner access in the interior of each candidate
fine atom.

Of the two disjoint raw gaps just constructed,
at least one has time window disjoint from the
final retained primary window. Indeed that
primary is itself a gap of D_h, so it can
coincide with at most one of the two. The
other gap is a candidate auxiliary window.
We do not require it to survive any earlier
coarse filter.

## 2. Produce auxiliary output packets with a bounded discard

For each of the N_b possible anchors, collect all
candidate auxiliary raw gaps directed over its
whole fine atom. Apply the fixed-anchor confinement
lemma of COHERENT_PACKET_GAIN, §1, now to the
actual degree-d annular covering P_h. The family
of bad gaps for this anchor has width at most

\[
 C_d={\pi\log(16d)\over(\log 2)^2}.
\]

Push its metric through I_h. The union of parent
families having a bad candidate costs at most
N_b C_d by subadditivity. In particular one
may remove only parents with no good auxiliary
candidate, at no larger cost. Borel gap
enumeration and the actual fine-base predicate
make these tests measurable in the stated
path atlas. No preferred gap needs to be selected
for the metric estimate.

The remaining auxiliary gaps in each packet lie
in the same injective P_h chart, so their covering
images are simple proper inner-to-inner paths
with the indicated whole target fine-atom image
in their crest. The complete atom lies strictly
between their ends, since the raw endpoints are
on the two branch groups and the cap maps
homeomorphically. The image is therefore
fine-marked admissible: it is not subordinate to
at most two original atoms. Even when both
ends fall in one target atom, the disk-side
base containing the whole separate crest atom
runs the long way; the source path class is
retained in this assertion. The output is a
genuine simple path, not a formal WAD arc.

Within each packet, all auxiliary gap interiors
are disjoint on the canonical lift, since they
are distinct gaps of simple parents and different
parents have disjoint interiors. Covering
injectivity on the packet makes their outputs
a disjoint Borel lamination. A fixed crest and
the injective chart give an actual common-cap
output packet, with its full relative class
and endpoint atoms. If the native definition
requires a proper connected marked base rather
than permitting a full-circle base, that is a
separate typing check on this packet.

**Important remaining output condition.** A
whole K_j crest atom is not the same as one
localized ending atom, and is not automatically
the full critical-limb crest. The source notion
of controllability requires the corresponding
localized/over-critical decomposition. Nothing
above bounds the number of distinct output end
atoms independently of q. To use the following
response, establish actual uniformly controllable
Wave containers B_l for these auxiliary
packets (or split into a uniformly bounded
number of such containers). This is an explicit
native hypothesis. A sufficient special case is
an actual output endpoint in a fixed b-bounded
atom bank, using the native localized-wave
decomposition. The two-branch host certificate
alone does not imply that special case.

## 3. Series response without a second retained stage chain

Let A be a finite-positive-width stationary
lamination and A_good the complete, primary-
confined family of COHERENT_PACKET_GAIN, §3.
Thus every good parent has one canonical
primary final window and the output leaf map
is injective on A_good. Let S⊂A_good be a
Borel subfamily in which every parent has an
actual good auxiliary gap as in §2, disjoint
in time from its primary final window. Let
D_S be the primary final output of S, and let
B_1,...,B_N be actual controllable Wave
containers for all its auxiliary output
packets, with N uniformly bounded. Write

\[
 w=W(S),\quad P=W(D_S),\quad
 B=\sum_{l=1}^N W(B_l).
\]

**Theorem.** For finite positive P,B,

\[
 \boxed{w\le{PB\over P+B},
        \qquad P\ge w+w^2/B.} \tag{2}
\]

If P=0 or B=0 then w=0 by metric domination.
If an output has infinite width there is no
finite near-maximality claim; use the response
through that output when its typing is verified.

Proof. Given an admissible metric on D_S,
pull it through the sequence of good primary
charts only. At each step pull back by the
covering on the fixed injective primary chart
and push through the immersion by all-sheet
square-sum. Area does not increase. On the
literal final primary window of each original
parent its length is at least one: induct
backward along the nested time windows of
the actual primary occurrence, not on the
discarded shoulders. Thus there is a primary
metric of energy arbitrarily close to P.

For each auxiliary packet choose a metric
admissible on B_l, pull it back by P_h on the
fixed injective packet chart and push through
I_h. The resulting metric has energy at most
that of the output metric. Square-sum these
finitely many auxiliary metrics. Its energy
is at most B (up to the arbitrarily small
infimum errors), and every parent of S has
an auxiliary gap of length at least one in
this metric. No multiplicity penalty is
needed for multiple candidate gaps: the
packet metric already handles each.

If these primary and auxiliary metrics are
f_P,f_B, combine them as

\[
 f=(a^2 f_P^2+c^2 f_B^2)^{1/2},
 \qquad a,c\ge0,\quad a+c=1.
\]

The two literal time intervals of each parent
are disjoint, so its total f-length is ≥a+c.
The energy is ≤a²P+c²B. Minimize over the
two weights, taking a=B/(P+B), c=P/(P+B),
and let the admissible-metric errors tend
to zero. This proves the first inequality
of (2). It implies w≤P and
B(P−w)≥wP≥w², proving the second. QED.

This argument uses the additional literal
auxiliary arc even if its terminal covering
image coincides with the primary output or
with another auxiliary output. No
two-occurrence noncollision assertion is
needed. The auxiliary packets need not be
disjoint from the primary output support;
square-sum metrics handle their overlap.
Only the *parent time windows* must be
disjoint.

For the full good output D_good, disjoint
Borel support of the injective primary
images gives

\[
 W(D_{\rm good})\ge W(A_{\rm good})+w^2/B.
 \tag{3}
\]

Indeed apply (2) to S and coefficient-one
transport to its complement, and add their
disjoint primary output widths. All metric
bounds before that addition apply to
arbitrary curve families.

Let W=W(A)>0, assume the good-family loss is
≤E, and w≥ηW for η>0. If every auxiliary
container has width ≤(1+λ)W, then B≤N(1+λ)W.
Assuming the primary final good output lies
in an actual uniformly controllable Wave C,
(3) yields

\[
 \boxed{W(C)\ge W-E+
           {\eta^2\over N(1+\lambda)}W.} \tag{4}
\]

Alternatively a wider auxiliary container
is itself the native response. For example
take 0≤λ≤1 and E≤η²W/(4N). In the first case
the primary gain is at least η²W/(4N);
a strict terminal parameter smaller than
both this gain and the chosen auxiliary
threshold is admissible. All constants
depend only on the specified uniform N
and the input fraction, not on q.

## 4. Consequence for the intended two-pass-through route

Under the hypotheses of §§1–3, a complete
stationary parent with the actual selected
deep carrier encounter (1) is in one of two
classes. If it physically meets both Q_b
and Q_(b+1), the two-bank-hit estimate of
VARIABLE_END_EXIT_TRANSFER and the final
graph degree-two census give the earlier
uniform R(F)-charge. Otherwise it avoids
one of those separators, so §§1–2 give
the two raw gap records, of which at least
one is an auxiliary to the primary. Outside
the bounded angular confinement discard,
the series-or-response estimate applies
if the auxiliary outputs have the
specified uniformly controllable containers.

Thus there is no need to prove that both
raw gap routes survive every earlier
filter, nor that their terminal untagged
images are distinct. This is a conditional
repair of the *response logic*, not of
the source line-1600 encounter assertion.
The exact remaining native gates are
(1) for the actual stationary family,
the full fine-side/host realization used
in §1, and uniform control of the raw
auxiliary output containers. The latter
is essential; an arbitrary common crest
is not the source's controllability
condition. The corrected geometric
marking and primary-continuation input
also remain explicit. If (1) fails,
this argument does not create a selected
deep contact from a symbolic limb label.

Together with the attachment-screening
counterexample and the residual necessity
bound of COHERENT_PACKET_GAIN, this
locates the remaining gap in actual
native geometry and output typing,
not in degree accounting, metric
pruning, or collision algebra. No
native stationary theorem or global
MLC conclusion is claimed.

The real-number series and response
algebra is formalized in
StationaryPacketGain.lean. All actual
carrier, contour, path and conformal
arguments here are written mathematics.
Prepared with ChatGPT assistance;
specialist review pending.
