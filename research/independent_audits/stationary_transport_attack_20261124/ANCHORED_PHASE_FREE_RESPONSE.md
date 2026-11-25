# Phase-free anchored comparison: nonshort near-critical mass without singleton hypotheses

Continuation of [AMBIENT_SHARED_CREST_RESPONSE](AMBIENT_SHARED_CREST_RESPONSE.md),
[AWAY_ENDPOINT_SHIFT](AWAY_ENDPOINT_SHIFT.md),
[SUFFIX_ANCHOR_RESPONSE](SUFFIX_ANCHOR_RESPONSE.md), and
[CRITICAL_PHASE_LOCALIZATION](CRITICAL_PHASE_LOCALIZATION.md).

**Change of strategy.** Instead of assembling arbitrary crest packets
and estimating their competing covering phases, maximize width in a
class of actual common-atom packets. This is a different comparison
class from the source's fixed-controllability class. It avoids the
phase deficit on its own domain. In that class the near-critical
nonshort estimate can be proved without assuming any leaf is
unbreakable, even at one stage: a second raw gap with a different
image is already useful for the series law.

The new part of the proof is a bounded-probe, median-shift estimate
for localized-away leaves, without singleton outputs. This allows all
nonshort types of a common near-critical-atom input to be charged
against the *whole* primary packet, including its short background.
The proof retains the stated exact geometric marking and saturated
carrier/host hypotheses. It is not a complete replacement of the
native Wave-amplification theorem: the global anchored maximum may
have a remote crest, and the subsequent short-crest growth and
long fast-forward must still be implemented for this new class.

## 1. Comparison class and theorem

Fix a single native periodically repelling primitive block F, and
use the actual annuli X=U minus T and their canonical finite tower
X_j=U^j minus T_j. Use b, q, P, BL_k, C_d, V=W(X), R=W(RF)
and all the following standing hypotheses of the earlier notes:

* the actual saturated minimal-hull carrier identification, the
  corrected degree-one geometric contour-collapse marking and
  its cyclic limb locality, the covering squares in the finite
  tower and the actual first/last old-proper fine atoms;
* the whole noncritical corridor J mapped injectively by the
  one-step boundary covering onto the translated corridor,
  with singleton limiting dividing cuts, as in AWAY_ENDPOINT_SHIFT;
* the actual critical-vertex deck pair of PRECRITICAL_TERMINAL_RESPONSE,
  the near-critical image condition of CRITICAL_PHASE_LOCALIZATION,
  and the selected deep inverse hull exclusion and two-bank
  host/fine-side realization of SUFFIX_ANCHOR_RESPONSE and
  AUXILIARY_GAP_RESPONSE for the large-q branch;
* Borel proper embedded parent and raw path atlases, canonical
  completion, segmented occurrence compatibility, actual
  geometric simple-cap marking predicates, and the finite-energy
  zero-width cut exceptions used in those notes.

We do not assume that the printed unrestricted A.3.2 restriction
implements that corrected action. No singleton or unbreakability
hypothesis is imposed here.

Define the comparison class C_* to consist of all actual Borel
laminations of simple proper distinct-ideal-ended inner crosscuts
of X, marked-admissible in their actual oriented disk-cap class,
with **one whole original marking atom in the strict crest of
every leaf**. The atom may depend on the lamination and may be
anywhere on the circle. No aggregate minimal-base convention for
a disconnected Wave is needed. We use the literal path-family
modulus. The class contains every actual fixed-anchor confined
output used below, because its cap contains the whole image of
the anchor fine atom and both ends are outside that atom.
No bound on the number of localized modules of those outputs
is required by the definition of C_*.

For each fixed F the supremum M_* of the widths in C_* is finite:
there are finitely many original atoms of positive angular length;
a packet with common atom of length ell has every cap base of
span >=ell, and the band metric in COLLISION_GAIN section 5
bounds its width by 1/(2ell). This is only finiteness for the
given F, not a uniform angle calibration. If C_* is nonempty,
a near-maximal member of it exists by the definition of supremum.

If an actual simple proper k-controllable input has a decomposition
into k localized modules and one **leafwise** over-critical module,
a common-atom subfamily has width at least
(W(input)-1/2)/(2k+1), with the harmless zero-width exceptions
understood. Indeed remove the essential coincident-ideal-end
loops using the span-one band metric (cost <=1/2). Contractible
same-end loops in an atom are not marked paths. In a localized
module choose a fixed ending atom and the actual cap direction
of the leaf from it. Marked admissibility forces the next atom
in that direction to be strictly between the ending atoms,
including the long same-atom route. These give at most two
actual common-crest packets per localized module. The leafwise
over-critical module has a fixed crest atom in BL_0. Width
subadditivity gives the extraction. A purely aggregate
over-critical decomposition does not imply this leafwise
hypothesis. This observation relates the new maximum to initial
wide witnesses; it does not identify the two maximality classes.

Let A in C_* have width W>0 and a common atom in the consecutive
near-critical bank B_* = BL_(-b)..BL_b (take the entire circle
if the bank wraps over all q limbs). Suppose every member of
C_* has width <= M=(1+lambda)W. Put

    h=b+2, H=h+2, N=h+12b*2^h, C=C_2,
    K=6b(2b+h+1)+1, J=max(12K,N,2),
    E=1+2^H V+H C,
    E_a=sum_(r=1)^h C_(2^r)+12b*2^h*C_(2^h),
    B=E+8K+(48K+12+2h)C+E_a+4R.

The high-q branch uses q>=h+3 and h<q<=P, as in the previous
deep-contact argument. The small-q branch stops at the first
precritical crest and requires no such deep contact.
Let S be the nonshort subfamily of A, meaning its individual
leaf crests contain at least one whole limb. For any 0<sigma<=1
set

    delta = sigma^2/(32 J (h+11)^2),
    lambda=delta/2.

**Theorem.** Under the displayed hypotheses and comparison cap,
if W(S)>=sigma W, then

    W <= max(2E/delta, 4B/sigma).                (1)

Thus for a sufficiently wide near-maximal near-critical member
of the anchored class, the nonshort fraction is small, regardless
of breakability. In particular no phase-selection deficit, separate
away Shift premise, or singleton chain is present in (1).
The comparison is against C_*, NOT against an arbitrary larger
unrelated-crest input and NOT a wider-output claim with a fixed
source controllability bound.

## 2. Whole primary packet and signed-probe charging rule

Discard original cap spans >=1/2 at total width <=1 by the band
metric. Discard incomplete full canonical H-lifts at cost 2^H V.
Remove point-cut and infinite-length exceptions at width zero.
Let a_0 be the common atom. At each stage j<H select its first
old-proper fine atom in the pulled coarse block, choose a fixed
interior anchor, and set a_(j+1) to the covering image atom.
On a complete parent, the signed raw-gap sum at this anchor is
one. Prune all bad candidate gaps at cost C and choose one good
positive gap in the Borel occurrence enumeration. Its actual
simple covering image is marked, with the whole a_(j+1) in its
strict crest. All chosen gaps are confined in one injective
covering chart, giving disjoint Borel output paths and
coefficient-one metric transfer for every subfamily.
The proof is the signed end-atom argument and fixed-anchor
confinement of the preceding notes, not a singleton selection
from an untagged action.

Complete canonical H-lifts supply complete lifts of every
selected simple suffix by the actual segmented fiber-product
identities, as in AMBIENT_SHARED_CREST_RESPONSE section 2.
Earlier good charts descend every stage's discard cost to the
original parents without a degree multiplier. On restricting
all intermediate primary families to the final original good
family G we have

    W(G)>=W-E,   W(D_j)>=W(G) (0<=j<=H),

where D_0=G and D_j is its actual j-th selected primary image.
The disjoint supports at every height and their Borel
correspondence are those of one common covering chart.
Primary orientations agree along the nested windows.
Each D_j is in C_*. Set d=M-W+E and Q_n=sqrt(n M d).

If a subfamily T of G has an additional literal original-time
window disjoint from its stage-j primary window, realized in one
of n actual fixed-anchor auxiliary output packets in C_*,
then

    W(T)<=Q_n.                                   (2)

Indeed descend the primary and auxiliary metrics through the
chosen injective charts and square-sum immersions; the two
length tests are on disjoint parent windows. Their combined
auxiliary energy is <=n M. The series law gives
W(D_j)>=W(G)+W(T)^2/(n M), using disjoint primary support
addition on T and its complement. If the sum of actual
auxiliary widths is zero, the series test forces W(T)=0.
This is the earlier ambient comparison rule, with the cap
now on the anchored class, so even an auxiliary over a remote
atom is eligible.

### Signed-probe rule

At any stage consider a fixed first or last old-proper fine atom
E' of a coarse old atom I, with interior probe e. Consider only
parents for which I is entirely in the actual strict crest or
entirely outside the marked base. Neither original end is in I.
An inner endpoint of any raw gap cannot lie in E': its old limit
is in I, impossible at an interior original parent time, and the
original ends are outside I. Fine-cut endpoints have zero width.
Every raw gap whose base contains e therefore contains the whole
fine atom strictly between its ends. The signed crossing sum is
+1 for a strict crest atom, and zero for an outside atom.

For a chosen positive primary, a disagreement means it does not
contain e when I is in the strict crest, or it contains e when I
is outside the marked base. In the first case there is a
different positive raw gap over e. In the second case the
positive primary contributes +1 to a zero sum, hence there is
a distinct negative raw gap over e. These are literal different
maximal raw windows on the same complete lift. No identity of
their covering images is asserted. Prune all bad gaps at a
fixed finite list of n such probes at cost nC (on the originals).
For every remaining disagreement choose one additional good
gap at its first qualifying probe. It maps injectively in that
probe's fixed chart, to an actual marked path crested over
the whole target atom. The packets for each probe have disjoint
Borel supports by the literal source occurrences. Their union
need not have disjoint target images, but (2) uses their separate
energies and disjoint time windows, not their support sum.
Thus the width of parents lost for bad probes or for any
disagreement is bounded by

    n C + Q_n.                                   (3)

Probes and their required inside/outside status may be chosen
for different Borel subfamilies, so long as the total list is
finite and the endpoint exclusions hold on each tested
subfamily. The costs for simultaneous tests are incurred on
original parents by coefficient-one prefix transport.

## 3. A bounded-probe median shift with no singleton assumption

This is the replacement for the away-from-critical estimate.
At a stage j<H, let T be the subfamily of original G parents
whose actual stage-j path is nonshort and subordinate to the
noncritical corridor, and localized in at most K fixed original
ending atoms. (Use disjoint first-eligible module choices.)
No unbreakability is assumed. We prove

    W(T)<= A_away := 4K+24K C+2Q_(12K).           (4)

Partition into at most 2K directional modules: at a localized
end atom E_0 in BL_k, 1<=k<q, the actual cap extends either
positively or negatively in the linear noncritical corridor.
Nonshortness forces the whole adjacent limb in that direction
to be a strict crest, so in the positive direction the remote
endpoint is in BL_r, r>=k+2, and in the negative direction
it is in BL_r, r<=k-2. If the indicated neighboring limb is
critical, that direction does not occur in the away class.
The common ambient atom a_j is itself noncritical on this
class. The primary selected at a_j is positive relative to
the old cap, regardless of its other endpoints.

Fix one module of width g on the originals. Give the circle a
linear coordinate by cutting just before BL_1, so the order is
BL_1,...,BL_(q-1),BL_0. The remote endpoint distribution on
the original-parent measure is atomless: a fixed endpoint
fiber at stage j has zero width by the point singularity
metric, and earlier good charts descend the zero bound.
Countable disjoint Borel support modulus is additive, so
choose a median t, splitting original width into g/2 below
and g/2 above t. If g=0 omit the module.
Choose l with t in the closure of BL_l and all upper-half
remote endpoints in limbs with indices >=l. At a dividing
cut choose the preceding limb, or a median in the open
measure-zero interval between supports. In the positive case
l>=k+2, in the negative case l<=k-2. The endpoint support
bounds and the nonzero median masses allow these choices;
there is no use of a numerical angular lower bound.

Use the following at most six fixed probes on the upper half.
A limb's first/last fine probe means the first/last fine atom
of the pulled entire limb block, equivalently the first/last
fine atom of its corresponding end old atom. The actual
singleton dividing-cut fibers are those of the noncritical
corridor lemma. All these tests are on strict crest or
outside old atoms, never on either ending atom.

Common to both directions: the first and last fine probes of
the pulled critical block BL_0 must be **outside**. This is
true of the old cap, which is subordinate to the noncritical
corridor. If the positive primary has no disagreement, it
avoids both probes and has no endpoint in their fine atoms.
Because it contains its noncritical common anchor, its
connected base cannot cross either limiting dividing cut.
It lies wholly in the pulled noncritical corridor J.

For a positive module:
  - last fine probe of BL_(k-1) outside (use BL_0 if k=1);
  - first fine probe of BL_(k+1) inside;
  - last fine probe of BL_(l-1) inside.

For a negative module:
  - first and last fine probes of BL_(k-1) inside;
  - first fine probe of BL_(k+1) outside (BL_0 if k=q-1);
  - last fine probe of BL_(l-1) outside (BL_0 if l=1).

These status assignments follow from the source endpoint limbs:
the positive upper half runs from BL_k to a limb >=l; the
negative upper half runs from a limb between l and k-2 to
BL_k. They contain the stated entire intervening limbs and
avoid the stated outside limbs. Repeated probes may be
removed.

If the selected primary agrees with these tests, its source
base is an interval in J with no endpoints on the tested
fine atoms. In the positive case its initial endpoint is
after the last fine atom of BL_(k-1) and before the first
fine atom of BL_(k+1), hence inside the pulled BL_k.
Its terminal endpoint is after the last fine atom of
BL_(l-1), hence in a noncritical limb >=l.
In the negative case its terminal endpoint lies between
the last fine atom of BL_(k-1) and the first of BL_(k+1),
hence in the pulled BL_k. Its initial endpoint is before
the first fine atom of BL_(k-1) and after the last fine
atom of BL_(l-1), hence in a noncritical limb from l
through k-2. There is no angular margin requirement: the
whole fine atoms are tested, their endpoints cannot be raw
ends, and the boundary cuts delimiting limbs are single.
The injective corridor covering now translates the two
endpoint limbs. The output cap is in the corresponding
translated linear corridor; represent BL_0 last, not first.

Consequently the original lower-half stage-j paths and the
agreeing upper-half stage-(j+1) primary paths connect two
pairs of alternating fixed real-line electrodes in their
actual strip lifts. In the positive direction the four
division points are 0, the two boundaries of BL_(k+1),
and t. A lower-half old path has endpoints in BL_k and
after BL_(k+1) but below t; an agreeing upper-half output
has its initial endpoint in BL_(k+1) and terminal
endpoint strictly above t. In the negative direction
use 0, t, and the two boundaries of BL_k. A lower-half
old path has endpoints below t and in BL_k; an agreeing
upper-half output has initial endpoint above t but before
BL_k, and its terminal endpoint after BL_k. The strict
orders follow from whole-limb translation and the chosen
median l, including the output limb BL_0 at the right end.

Lift the actual paths to the strip and bound their widths
by the corresponding full quadrilateral families in the
upper half-plane. Restriction and square-sum descent
preserve admissibility; the two opposite widths are
reciprocal. If L is the original width removed from the
upper half for bad probes or disagreements, coefficient-one
transport gives

    (g/2) (g/2-L) <= 1    when g/2-L>=0.

When g/2-L<0 the bound g<=2L is already enough.
In all cases g<=2+2L: if g>2+2L both factors
would exceed 1. This is the median-loss inequality,
not a Shift rectangle asserted for arbitrary curves.

Now choose the medians before any test deletions for all
at most 2K modules. The total list has <=12K probes.
Apply (3) to the union of their upper-half losses against
the **same entire** primary D_(j+1). All these tested
module subfamilies are disjoint on original supports.
The sum of their loss widths is <=12K C+Q_(12K).
Summing the median-loss inequality gives (4).
In particular the potentially remote output atoms of
disagreement gaps do not require a new control bound;
they are in C_* by their actual whole crest atom.

## 4. Advance the nonshort residue without unbreakability

Use the same fixed whole primary sequence G,D_j throughout.
For any relevant stage j with j+1<=H, the whole BL_0
crest class costs

    U=2C+Q_2                                    (5)

on original parents: the actual two old-proper critical
vertex deck probes give two distinct positive good gaps,
one of them different from the primary; prune at both
probes and use (2). This is the earlier over-critical
raw-gap argument, with no retention requirement on the
extra gap.

For a whole precritical crest at stage j with j+2<=H,
test first/last old-proper fine atoms of its pullback.
If either chosen good positive gap differs from the
primary, use (2) at j+1, not a singleton double rule.
If both equal the primary, its cap contains the entire
pulled limb block: that connected block has angular
span <1/2 and the source primary cap span is <1/4.
It cannot connect its first and last anchors by the
opposite route of length >1/2. The whole end fine
atoms are inside, so the entire block between them
is inside. Its image crests the whole BL_0.
Use (5) at j+1. This gives the bound

    Z=4C+2Q_2.                                   (6)

The same first/last probe comparison for a noncritical
nonprecritical whole limb crest advances it to the
whole next limb except for a charge <=2C+Q_2. These
estimates require no unique untagged output: if an
alternative positive gap is distinct, the series
rule uses its own literal window.

To bound away modules at stages 0 and h, note that a_0
lies in B_* and a_j lies in the consecutive expanded
bank BL_(-b)..BL_(b+h) for j<=h. Noncritical anchors
translate one limb; at a critical old-proper anchor
its image lies in B_* by CRITICAL_PHASE_LOCALIZATION
section 1. The bank has <=6b(2b+h+1) original atoms
or is the whole circle. Every chosen path's cap span
is <1/2 and contains the ambient anchor (at stage 0
we made the band discard). Allocate endpoint bank atoms
and, if needed, the atom of the anchor's antipode as
in NEAR_CRITICAL_PACKET_CONTROL. Any other path has
both ends outside the bank and the actual cap containing
the anchor must traverse all of BL_0. Thus the
away-from-critical nonshort class belongs to at most
K localized modules at each of these two stages.
This is a leafwise statement on actual cap bases,
not a general assertion of aggregate Wave control.

Start with S intersect G, losing <=E. Partition its
actual stage-0 paths into over-critical (charge U),
away nonshort (charge A_away), and central-ending
nonshort. Each central nonshort leaf crests either
over BL_1 or over BL_(q-1) by the actual adjacent
limb order; assign the latter-only class to Z at 0.

For the positive residue, advance whole BL_1,
BL_2,... using the preceding first/last probes,
charging <=h(2C+Q_2) on originals.
Do not remove any charged class from G or D_j:
only the tracked nonshort subset is reduced.
For q<=h+2 stop at j=q-2 and use Z there. The
q=2 case starts already precritical.
For q>=h+3 reach stage h with whole BL_(h+1) crest.
Split the tracked image into over-critical, away and
central-ending; charge U and A_away for the first
two. If a remaining central-ending path does not
have its initial cap-oriented physical end in the
open critical limb, its terminal end is there and
its cap must traverse all BL_(q-1), since it also
crests BL_(h+1) with h+1<q-1. Charge Z again at h.
The dividing-point ends are zero-width exceptions.

## 5. Suffix response without a singleton chain

The remaining tracked originals have actual compatible
simple selected paths through h, crested at every stage
over BL_(j+1), with initial physical critical end at h.
The signed suffix-anchor proof applies to these
**particular selected positive primary windows**.
Its topological statement does not use singleton
uniqueness: for each j<h the coherent full-tower
fine atom B_j is old-proper over an atom in BL_(j+1).
The completed (h-j)-lift of the stage-j parent has
signed raw-gap sum one at the fixed probe in B_j.
Its selected final primary is an actual maximal
raw gap of that same suffix (segmented reconstruction,
proper final covering image and canonical exhaustion).

If that particular primary is not a positive gap
over the probe, some other positive raw gap is.
It is a different actual window, disjoint from
the stage-h primary on the original parent. Otherwise
the primary is positive over every such probe.
A precritical backward origin of its initial
critical endpoint would place that initial source
access in the pulled precritical block. The positively
oriented cap arc to the probe over BL_(j+1) would
traverse the entire pulled closed critical block.
By the full-tower critical saturation identity this
would map to the whole circle, contrary to the
proper simple final cap. Therefore each backward
origin lies in the selected inverse inside the
critical limb. Descending all h steps forces the
actual selected depth-h physical carrier contact,
not an arbitrary filled-limb hit. It is at an
interior parent time since the selected deep limb
is disjoint from the original full hull.

This is precisely the geometric proof of
SUFFIX_ANCHOR_RESPONSE sections 2--5. The singleton
hypothesis there ensured a chosen simple positive
chain; here that chain has already been constructed
directly. If a suffix probe yields the other raw
gap, no assertion about its earlier retention is
needed. If there is selected deep contact, the
two bank components charge <=4R for actual hits
of both; otherwise an avoided separator supplies
the other raw gap by AUXILIARY_GAP_RESPONSE. Use
its saturated host/fine-side hypotheses, not an
unproved coincidence of markings. Altogether
there are <=N actual suffix and separator anchors,
and all bad candidate gaps cost E_a.
Their good auxiliary outputs are members of C_*
because each contains its whole fine image atom.
Apply (2) against the same whole D_h. The remaining
tracked width costs Q_N.

## 6. Total estimate and remaining scope

Subadditivity on the original parents yields

    W(S) <= E+2A_away+2U+2Z+h(2C+Q_2)+E_a+4R+Q_N
         = B+4Q_(12K)+(h+6)Q_2+Q_N
         <= B+(h+11) sqrt(J M d).               (7)

The overcounts cover the small-q stop without using
the selected deep geometry in that case.
If W exceeds the right side of (1), then
E<delta W/2, B<sigma W/4 and
d=lambda W+E<delta W, M<=2W.
By the definition of delta,

    (h+11) sqrt(J M d) <= sigma W/4.

This would give W(S)<sigma W/2, contradicting the
nonshort fraction premise. This proves (1).

The result is an alternative to the pivotal-phase
problem, not a uniform native estimate of its
deficit. It shows that near-maximality in C_* plus
a near-critical common atom already excludes
wide nonshort mass, even if every relevant leaf
breaks. The short remainder and remote anchors
remain essential: to use this instead of the
source's full arbitrary-controllable ambient
comparison, one must move near-maximal remote
common-atom packets to the critical bank at
uniform cost, and handle the short-crest growth
and saturation in this class. A wider C_*
member with a remote anchor need not be uniformly
controllable in the source's original sense.
The finite-supremum observation alone does not
establish vertical amplification.

All native exact marking, saturated hull, canonical
tower, separator and Borel hypotheses remain as
stated. The companion regression checks the finite
probe order and exact width algebra; the analytic
proof is written mathematics, not a theorem checked
by those regressions. No ledger promotion, native
closure or MLC claim. AI-assisted research;
independent specialist review pending.
