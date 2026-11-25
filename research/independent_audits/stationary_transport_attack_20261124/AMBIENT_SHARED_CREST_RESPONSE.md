# Ambient stationary defect response with a shared near-critical crest

This note combines [AWAY_ENDPOINT_SHIFT](AWAY_ENDPOINT_SHIFT.md),
[POSITIVE_CREST_CONTINUATION](POSITIVE_CREST_CONTINUATION.md),
[SUFFIX_ANCHOR_RESPONSE](SUFFIX_ANCHOR_RESPONSE.md), and
[PRECRITICAL_TERMINAL_RESPONSE](PRECRITICAL_TERMINAL_RESPONSE.md).
It changes the comparison width from an isolated stationary
subpacket to the entire input lamination, including short
or breakable background leaves, provided the entire input
has a common actual crest atom in BL_1. This is a genuine
ambient fraction estimate in that class. It does not assert
an ambient theorem for arbitrary disconnected or unrelated
crest packets.

## 1. Exact scope and quantitative statement

Fix b>=1, h=b+2, m=h+2, N=h+12b*2^h,
C=C_2=pi log(32)/(log 2)^2, and K=6b(h+4)+1.
Use the exact corrected geometric action and all actual
saturated graph, carrier, finite tower, proper old-end
fine-atom, prime-end square, canonical lift and Borel
hypotheses of the preceding notes (including the actual
critical vertex deck pair and the two-bank host/fine-side
certificate). The high-q selected-depth argument is
used only if q>=h+3 and h<q<=P. All the needed finite
annular pullbacks through m exist, even if m exceeds
the source's unbreakability horizon. No singleton
condition is imposed beyond h+1=b+3.

Let A be a Borel lamination of simple proper marked
inner-ended paths of finite positive width W. Assume
one fixed original atom a_0 contained in BL_1 is in
the strict actual crest of every leaf. Other than this
common atom the leaves need not have the same crest,
end at BL_0, or be unbreakable. In particular a background
subfamily can be short or can break. Let S be the
subfamily of actual nonshort central-ending leaves
which are sequentially unbreakable through h+1 for the
corrected action. Suppose W(S)>=sigma W, 0<sigma<=1.

Put

    E=1/2+2^m V+m C,
    E_a=sum_(r=1)^h C_(2^r)+12b*2^h*C_(2^h),
    c_away=4V+2C+4,
    B0=E+(2h+10)C+K*c_away+E_a+4R,
    delta=sigma^2/(2048 N), lambda=delta/2.

Suppose every relevant actual Wave with at most K
localized modules and one over-critical module has
width <= M=(1+lambda)W (with the same ordered-base
and full-circle conventions as the earlier packet
control lemma). Then

    W <= max(2E/delta, 4B0/sigma).                (1)

Equivalently, above the displayed O_(b,sigma)(R+V+1)
threshold, a positive stationary fraction forces a
strict wider-Wave response **relative to W(A)**.
The response's control bound K is independent of
sigma, of the input controllability, and of q.
The extra two raw primary stages are used only for
comparison; they do not require the stationary
subfamily to be unbreakable past h+1.

## 2. A primary for the entire ambient family

First discard coincident-end essential inputs at
cost <=1/2 by the band estimate of AWAY_ENDPOINT_SHIFT
section 4, and the zero-width cut/finite-length
exceptions. Discard incomplete canonical lifts to
height m at cost <=2^m V. On each subsequent stage
choose a first old-proper end fine atom in the
coarse pullback of the common old atom a_j, and an
interior anchor e_j of that fine atom. The positive
signed gap sum is one for every ambient parent at
that stage. Prune all bad raw gaps over that anchor
at cost C. Select one good positive gap by the
first code in the countable Borel gap enumeration.
No uniqueness is needed for this ambient selection.

Each selected gap passes the two geometric marking
filters and maps homeomorphically to a simple
proper distinct-ended output, whose actual crest
contains the next common atom a_(j+1) (the whole
covering image of the selected fine atom). The
output chart is injective on the union of selected
gaps: before covering they have disjoint interiors
because their immersion images are literal disjoint
parent subpaths. Thus these are actual Borel
laminations. Their relative marking and orientation
are those of the gap caps. The same metric pullback
and all-sheet pushforward give coefficient-one
transport for *every* subfamily. Descend each
subsequent bad-anchor discard through the previously
chosen good charts at no increased energy.

The full-height canonical lift supplies complete
suffix lifts for every selected simple chain:
the segmented fiber-product reconstruction uses
the actual nested occurrence windows, not singleton
uniqueness; its terminal proper covering image
identifies the prefix lift with a canonical gap,
and the remaining coordinate projection of the
complete original lift is the canonical suffix
lift over that closed window. This is the
compatibility argument of COLLISION_GAIN section 2;
it applies to any particular selected retained
simple chain. No one-shot equality of all filtered
outputs is used.

Construct through m such choices, and denote the
original final good set by G and its primary
images at j by D_j, 1<=j<=m. Then W(G)>=W-E
and W(D_j)>=W(G) for all j. Restrict every
intermediate image to these same original G
parents; they remain disjoint Borel images
by injectivity. On the stationary leaves the
selected outputs through h+1 are necessarily
the actual singleton outputs, while for other
leaves one actual output is chosen.

All D_j are uniformly controllable. If q>=h+4
then a_j belongs to BL_(j+1) for j<=m (no
critical step before these outputs), so the
near-critical consecutive bank from BL_0 to
BL_(h+3) suffices. If q<=h+3 use the entire
circle, which has <=6b(h+3) atoms. At each
stage the common target chart is of radius
1/4, and the near-critical packet-control
lemma gives at most K localized modules and
one over-critical module, including the
cut-antipode exceptional atom. This applies
also to every restricted image D_j. No
addition of unrelated pushed packets has
occurred: each D_j is one actual lamination
from one common covering chart.

## 3. Two ambient comparison rules

Set d=M-W+E=lambda W+E. This is a nonnegative
width allowance, measured against the entire
original A, not the size of a subfamily.

**Double rule.** Suppose a subfamily T of G has
two distinct retained windows at some stage,
one the ambient primary and both projecting
onto its same simple singleton. The other
window is in the exact deck translate of
the primary chart. The two-chart metric
gives factor two for T; coefficient-one
holds on the rest of G. Addition is on
the disjoint primary Borel supports of the
same whole D_j. Hence

    W(T) <= d.                                  (2)

This remains valid if the competing retained
witness varies with the leaf.

**Auxiliary rule.** Suppose every parent in T
has a separate literal original-time window
disjoint from the primary window defining a
fixed D_j, and the auxiliaries have n actual
confined output packets of total width B<=n M.
Their metrics descend through the injective
auxiliary chart and the relevant good prefix
charts by all-sheet square-sum, with energy
at most B in total. The primary metric and
auxiliary length tests are on disjoint time
windows, even if the auxiliary output equals
a primary output. The series inequality of
AUXILIARY_GAP_RESPONSE gives

    W(D_j) >= W(G)+W(T)^2/B,

and consequently

    W(T) <= Q_n := sqrt(n M d).                 (3)

For B=0 the test forces W(T)=0. Infinite
output widths already violate the cap.
This proof does not compare D_j to the
width of T alone.

## 4. Two useful defect charges

At any stage j with j+1<=m, the subfamily
of G whose stage-j path crests over all
BL_0 has an ambient charge

    U=2C+Q_2.                                   (4)

Indeed take the actual old-proper deck pair
of PRECRITICAL_TERMINAL_RESPONSE section 1.
Their signed sums produce two positive raw
gaps. Charge all bad candidates at these
two anchors by 2C, descended through the
good ambient prefix. The good charts are
disjoint, so at least one gap is different
from the ambient chosen primary at j+1.
It supplies a separate window inside the
stage-j ambient path, hence on the
original parent. There are at most two
auxiliary packets, both controlled by the
near-critical bank BL_0,BL_1. Apply (3)
against the whole D_(j+1). No singleton
condition is required even on this subfamily.

At any stage j with j+2<=m, a precritical-
crested subfamily with a remaining actual
singleton step has an ambient charge

    Z=4C+d+Q_2.                                 (5)

Test the first and last fine atoms of the
geometric pulled precritical block. Charge
bad candidates at the two anchors by 2C.
If either good positive gap differs from
the ambient primary, use (2), since they
are retained witnesses of the same singleton.
Otherwise both are the ambient primary.
The pulled precritical block has angular
length <1/2, and the good base <1/4; with
both whole end atoms inside it, the base
must contain the whole intervening block
rather than go the other way around the
circle. Its output crests over BL_0.
Apply (4) at j+1 against D_(j+2).
This gives (5), including the one-atom
case. The final step uses only raw gaps
and the ambient primary, not unbreakability
of the precritical output.

## 5. Follow the stationary subset, keep the background

Remove A minus G from S at cost E. Split
the remaining S into the positively directed
class crested over BL_1, and the other
class crested over BL_(q-1). The adjacent
limb dichotomy follows by reading the
actual cap base from its central end
toward any full limb crest. If both
directions occur for a leaf, assign it
to the first class. For q=2 the first
class is already precritical. The
negative-only class costs at most Z
by (5) at j=0; we do not delete that
class from G or from the comparator
primary images.

For the positive class advance the
whole crest through each nonprecritical
stage j<h. On the surviving stationary
leaves test the first and last fine
atoms of the entire pulled BL_(j+1).
Bad candidates cost <=2C on the original
parents at that stage. If either positive
good retained gap differs from the
ambient primary, the singleton condition
and (2) bound that bad-to-continuation
class by d. Remove it only from the
tracked stationary class. If both are
the ambient primary, the good base
contains the entire pulled noncritical
limb block (length <1/2, as in the
precritical argument). The output
therefore crests over all BL_(j+2).
This constructs the required leafwise
whole crest sequence at a cumulative
cost <=h(2C+d) to the tracked subset,
without changing G or the primary
images D_j at any step.

For q<=h+2, stop the first time this
whole crest is precritical, j=q-2.
Charge that remaining positive packet
by (5). Since j+2<=m and j+1<=h+1,
the horizon suffices. No deeper selected
limb or backward critical argument is
used. The bound in section 6 below is
larger than the resulting E+h(2C+d)+2Z.

Suppose q>=h+3. At stage h the positive
residue has full crest BL_(h+1), with
one remaining singleton step. Its image
is a sublamination of the actual D_h.
Partition into central-ending, over-
critical with ends outside BL_0, and
away with ends outside and base
avoiding BL_0. This follows from the
connected cap base with whole ending
atoms. The away class is a subfamily
of the <=K localized modules of D_h:
the over-critical module of its control
decomposition cannot contain those
leaves. Each away module is nonshort
and one-step unbreakable, so the new
signed endpoint-shift bound gives
total <=K*c_away, descended at
coefficient one. Use (4) at h for
the over-critical class, charge U.

For the central-ending residue orient
each actual cap positively. If the
initial physical end is not in the
open critical limb, the final one is
there and the base traverses the
entire precritical block before it.
A dividing-point end is a zero-width
exception. Thus the unwanted
orientation class costs Z by (5)
at stage h. This is now an ambient
charge as small as desired relative
to W for small d/W, not the earlier
3M/4 packet-local bound.

The remaining positively oriented
central class satisfies the hypotheses
used in the suffix-anchor proof:
all actual prefix paths crest the
prescribed whole limbs, the primary
windows are compatible, and the final
initial end is physically critical.
Intermediate central-ending labels
are unnecessary. The coherent
old-proper suffix atoms and signed
gap tests yield either a different
raw suffix gap or an actual selected
depth-h carrier contact. If no
different suffix gap exists the
primary is positive over every such
anchor, so a precritical backward
origin would force full critical-block
saturation under the suffix covering,
contradicting the proper final cap.
Thus all inverse steps are selected,
giving the deep carrier contact.
The two-bank hit class costs <=4R;
otherwise the avoided separator
gives a distinct auxiliary raw gap.
These are exactly the metric and
geometric hypotheses and proofs of
SUFFIX_ANCHOR_RESPONSE sections
2--6 and AUXILIARY_GAP_RESPONSE.

Prune bad suffix/ separator gaps at
the total cost E_a. The remaining
auxiliaries form at most N actual
uniformly controllable packets (h
suffix anchors and 12b*2^h bank
anchors), each with the stipulated
near-critical chart. Their windows
are disjoint from the chosen stage-h
primary. Apply (3) against the whole
D_h to obtain charge Q_N for the
remaining stationary residue. The
over-critical and precritical charges
at later horizons use their own
ambient comparators, not the same
window as this final series response.

## 6. Collect the charges and choose the ambient scale

Subadditivity for the disjoint or
possibly overlapping tracked exclusions
gives the following explicit estimate:

    W(S) <= E+h(2C+d)+Z+K*c_away+U+Z+E_a+4R+Q_N
         = B0+(h+2)d+3Q_2+Q_N.                  (6)

The first Z is for the negative class,
the second for the final orientation.
Every term is measured on original
parents (a good prefix costs coefficient
one). The same upper bound covers the
small-q branch without a deep-contact
argument. No additive measure for
different overlapping output families
is used; all metric additivity with
primary widths is within a single D_j.

Assume W exceeds the right side of (1).
Then E<delta W/2 and B0<sigma W/4,
so d<delta W and M<=2W. Since N>=h+2
and 0<sigma<=1,

    (h+2)d/W <= (h+2)delta <= sigma/8,
    (3Q_2+Q_N)/W <= 4 sqrt(2N delta) = sigma/8.

In the last equality use delta=sigma^2/
(2048N). Thus (6) gives W(S)<sigma W/2,
contradicting W(S)>=sigma W. This proves
(1) with room in the constants. The
chosen gain parameter lambda is positive
and the control bound K is independent
of sigma. For example, this is a scoped
ambient QSDRA response with a fixed
positive fraction and the explicit
absolute width scale, not an assertion
that the full source QSDRA has been
proved.

## 7. The remaining genuine ambient problem

This comparison works even if arbitrary
background leaves break, because their
common old-proper anchor still yields an
actual simple primary. It also handles
both initial directions among the
stationary leaves of a shared-BL_1-atom
ambient lamination, without comparing
their separate widths to W(A).

For an arbitrary k-controllable Wave the
common atom hypothesis is not automatic.
A localized module may split into
opposite directions, and a union of
several modules need not share any
crest. Choosing a finite collection of
separate common-chart outputs does not
repair this: they may overlap or collide
after covering. Even if each disjoint
source packet transports at coefficient
one, two source deck copies of the
same target foliation have equal
overlapping images; there is no common
injective image of both with their
sum of widths. The fixed-degree
counterexample in the earlier QA audit
is precisely why this issue matters.

The next acceptance test is therefore
a source-valid ambient selection or
replacement theorem: either a sufficiently
wide near-maximal Wave can be chosen
with a shared near-critical crest in a
class stable under all required terminal
responses, or one can transport/replace
several disjoint crest packets without
losing their aggregate background width.
A finite anchor cover alone proves neither.
The old counterexample rules out a
general all-packet coefficient-one
covering assertion, not a more special
native selection theorem.

Exact corrected source marking and
saturated graph/host realization still
need source-specific verification;
the source's literal unrestricted
A.3.2 is not restored. The source
small-breaking and downstream mostly-
short/terminal integration need a
separate proof; no canonical ledger
promotion or MLC claim follows.
AI-assisted written mathematics,
specialist review pending.
