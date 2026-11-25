# Constructing positive crest continuation by a gain-or-discard argument

This is a continuation of [SUFFIX_ANCHOR_RESPONSE](SUFFIX_ANCHOR_RESPONSE.md)
and [PRECRITICAL_TERMINAL_RESPONSE](PRECRITICAL_TERMINAL_RESPONSE.md).
It removes the separate *central-ending, whole-limb-crested at every
stage* hypothesis from their positive-packet estimate. The price is
a small relative error in the width telescope, controlled by the
same terminality cap that the proof contradicts.

This remains conditional on the exact corrected geometric marking,
actual simple singleton paths, complete canonical occurrence
compatibility, the saturated graph and separator realization, and
a stated away-from-critical Shift estimate. It does not prove a
source-relative extraction from arbitrary mixed-direction Waves.

## 1. Setting and claim

Use the notation of the two preceding notes. Assume b>=1, q>=2,
h=b+2, and N_orig=h+1=b+3. For the large-q branch assume the
primitive hypotheses h+1<q<=P and the selected inverse hull
exclusions and exact host/fine-side realization used there.
All the finite contour squares and actual old-proper first and
last end atoms are required as in those notes. In particular a
noncritical pulled limb block is a connected interval of whole
fine atoms mapping onto the proper next limb block.

Let A be an actual Borel lamination of finite positive width W,
of simple proper paths with distinct ideal endpoints, each
individually crested over the whole BL_1. Each has an actual
sequential singleton chain of simple proper distinct-inner-ended
paths through N_orig. The corrected geometric fine-path and
one-coarse-atom exclusions are used; no unrestricted literal
maximal-subset definition or one-shot filtered-action equality
is invoked. The paths at intermediate stages are **not assumed
central-ending or whole-limb-crested**. They are also not assumed
to be the result of any independent N1 telescope.

Assume the disjoint Borel support width addition, canonical lift
completion, nested time-window reconstruction and zero-width gate
exceptions proved in the preceding geometric notes with their
stated hypotheses. In particular complete lifts to height h+1
give compatible complete lifts of the actual retained suffixes.

One additional input is explicitly isolated:

(Away) For a localized actual nonshort Wave subordinate to the
complement of BL_0, with one remaining actual unbreakable step
on the same corrected geometric action, its width is <= c_away.
The constant is uniform in q and the particular packet. This is
the away-Shift estimate required in N1 Lemma 6.3, rather than
the central-continuation conclusion of N1. We do not establish
its source validity for the corrected action here.

Write C=C_2=pi log(32)/(log 2)^2 and C_d for the previous
fixed-anchor confinement constant. Define

    N_b=12b*2^h, N=h+N_b, K=6b(h+3)+1,
    E_a=sum_(r=1)^h C_(2^r)+N_b*C_(2^h),
    A_b=2^(2h+1)*V+4*(2^h-1)*C,
    tau=1/(65536*N), lambda=tau/2^(h+2),
    H=E_a+4R+3(V+C)+K*c_away.

Suppose every actual K-controllable Wave (or one with a
smaller stated control bound) has width <= M=(1+lambda)W.
The claim is

    W <= max(2*(A_b+C)/tau, 32*H).                (1)

If the away constant is uniform, this is O_b(R+V+1);
the other constants are explicit and independent of q.
The comparator in (1) is the width of A itself, not the
width of an unspecified ambient Wave containing A.

## 2. One noncritical crest: advance or double gain

Suppose at stage j all surviving paths alpha_j are individually
crested over BL_(j+1), which is not precritical. Take the
first and last fine atoms of the geometric pulled BL_(j+1).
They are old-proper over the first/last old atoms by the
end-atom premise. Choose fixed interior anchors there
(one anchor if the atoms coincide).

A complete parent has a positive raw gap over each anchor
by the signed crossing identity of the suffix note, including
the coincident-end raw loop convention there. Prune all bad
gaps over these two anchors at total cost <=2C. Because the
whole atoms are old-proper and in the parent crest, the
remaining gap bases contain the whole anchor atoms strictly
between their endpoint atoms, and each gap passes both
geometric filters by the end-atom argument. The confined
covering image is the singleton alpha_(j+1).

Choose the gap over the first anchor as primary on all the
good parents. Its single chart makes the primary images an
injective Borel lamination. Two different gaps over that
same first anchor cannot have the same output: distinct
covering lifts of a simple disk cap have disjoint bases.
The same holds for the last anchor. If the first and last
gaps differ, they are the two deck lifts of the singleton
path. The two-chart metric estimate gives output width at
least twice the width of this double-gap source subfamily.

If they are the same gap, the base contains the whole pulled
limb block S. Indeed S has angular length <1/2 (degree-two
covering onto a proper connected block), and the good cap
base has length <1/4. It cannot travel between the two
anchors the other way around the circle. The entire first
and last fine atoms are already inside the base, so all of
S is inside. This includes the one-fine-atom case. Its
covering image crests over the whole BL_(j+2).

The common first-anchor output packet D, *including* the
double-gap class before it is removed, is controllable by
the fixed-chart near-critical bank lemma: its target
anchor atom lies in BL_(j+2). The bank from BL_0 through
that limb has at most 6b(j+3) atoms, with the extra chart-cut
atom as before. Its control bound is <=K at every step
used below. This is an actual output packet, not an
aggregation of two unrelated covering images. All its
subfamilies are Borel.

Now let G be the original-parent surviving class before
this step, with W(G)>=W-L_j, and use the already chosen
good prefix charts. The first/last anchor discard, on
the original parents, costs <=2C by coefficient-one
prefix transport. Denote the original good class after
pruning by G' and its double-gap subclass by B_j.
On disjoint Borel output supports, add the coefficient-one
and double-gap bounds (the latter descends through the
same good prefix). Thus

    W(D) >= W(G')+W(B_j)
         >= W-L_j-2C+W(B_j).

The common cap W(D)<=M gives W(B_j)<=lambda*W+L_j+2C.
Remove B_j as well. The surviving original family is
of width at least W-L_(j+1), where

    L_(j+1)=2*L_j+4C+lambda*W.                    (2)

Every resulting path individually crests the next
whole limb. Its actual primary output map remains
injective on the surviving originals and all good
prefixes have coefficient-one transport. This is a
relative telescope constructed by the gain-or-discard
argument itself, not an absolute small-discard N1
theorem.

Initially discard incomplete full canonical lifts at
height h+1 for cost <=2^(h+1)*V and the zero-width
exceptions. Set L_0=2^(h+1)*V. Equation (2) gives

    L_j=2^(j+h+1)*V+(2^j-1)*(4C+lambda*W),
    L_h=A_b+(2^h-1)*lambda*W.                    (3)

For all j<=h the numerical bound L_j<=L_h holds.
In the small-q case stop the construction at the
first precritical crest (section 5); the formula for
later j is only a numerical envelope, not an assertion
that those later crests exist.

## 3. Large q: control the terminal noncentral pieces

Suppose q>=h+3 and the construction reaches h.
Let G_h be the surviving original family, and D_h
its stage-h primary image (all crested BL_(h+1)).
Its width is >=W-L_h; it is K-controllable by the
last common first-anchor chart. Its members have
one remaining actual singleton step.

Partition leaves into those with an endpoint in BL_0,
those with both ends outside BL_0 and crest over BL_0,
and those with both ends outside and no such crest.
Use the actual connected-base trichotomy: a base with
both end atoms outside BL_0 is either disjoint from
that block or contains the whole block between the
ends. Remove the gate exceptions at zero width.
The last class lies in the localized modules of the
near-critical decomposition, subordinate to the
complement of BL_0. There are at most K such modules;
they are nonshort because of their full BL_(h+1)
crest. Input (Away), followed by coefficient-one
prefix transport, bounds their original parent
width by K*c_away.

For the over-critical class O a mere three-quarter
cap on the orientation exception and a separate
half cap on O would not suffice: their sum exceeds
W. Instead use the one remaining singleton step
to obtain a quadratic response against the primary
of the *whole* surviving packet.

All D_h leaves crest over the noncritical BL_(h+1).
Choose the first old-proper end fine atom of its
pullback and prune its bad gaps for cost <=C on
the original parents. The signed gap supplies an
actual retained primary, with all outputs in a
common injective chart. Its target anchor lies
in BL_(h+2); even if this is the precritical limb,
the bank size is bounded by K. Write D_(h+1)
for this whole good primary image.

For parents in O the two old-proper deck-related
critical-vertex anchors from PRECRITICAL_TERMINAL_RESPONSE
section 1 supply two distinct positive raw gaps.
Their bad-gap discard costs <=2C on the originals.
They are disjoint time windows, so at least one differs
from the chosen primary at stage h+1. This is an
auxiliary window in the stage-h path disjoint from
the final primary; it need not pass either filter.
There are at most two confined auxiliary packets
crested over their common target atom in BL_1.
Their control bounds are <=12b+1. No new completeness
cost is needed because the original lift was complete
through h+1.

Let o be the original-parent width of O and o' the
good auxiliary subfamily after these three anchor
discards. Then o' >= o-3C. Pull back the two auxiliary
metrics through their charts and along the good
prefix; they supply a unit auxiliary length on
a literal original-parent time window disjoint from
the new primary. The series law applied to the
subfamily and disjoint primary support addition on
its complement gives, with B_O<=2M the sum of
auxiliary output widths,

    W(D_(h+1)) >= W-L_h-C+(o')^2/B_O.

If B_O=0 then o'=0; otherwise the terminal cap
on D_(h+1) implies

    o <= 3C+sqrt(2(1+lambda)*W*(lambda*W+L_h+C)).
                                                      (4)

This step does not assert an absolute width bound
on arbitrary over-critical unbreakable Waves.
It uses the common positive primary of the whole
packet, and in particular does not compare the
width of O alone to a global terminality threshold.

The central-ending portion now splits by its
positive cap orientation. Those failing to have
an initial physical critical end have the full
precritical crest, as in the orientation argument
of the preceding notes. The mixed cap of
PRECRITICAL_TERMINAL_RESPONSE section 3 applies
to this actual subfamily (it still has one remaining
singleton), so its original width is <=3M/4+3(V+C).
No assumption on the orientation of the remaining
central-ending portion is made beyond the resulting
initial physical critical-end property.

## 4. Suffix response on the remaining portion, whole primary gain

For every remaining parent in G_h with that initial
critical end, all the actual stage-j paths crest
BL_(j+1) by section 2. These are the pathwise
hypotheses used in SUFFIX_ANCHOR_RESPONSE sections
2--5: its construction of coherent old-proper
suffix atoms uses those crests, not the intermediate
central endpoint labels. The complete suffix lifts
are available by the height h+1 completion.
Its signed-gap alternative therefore gives either
a different suffix raw window or an actual selected
depth-h carrier encounter. To see why the initial
critical endpoint suffices, in the absence of a
different suffix gap, the terminal primary is
positive at each old-proper suffix anchor. A
precritical origin of its backward critical
endpoint would force its full suffix base to cover
the pulled closed critical block. By full-tower
saturation that would map onto the whole circle,
contradicting the simple terminal cap. The
backward itinerary is thus selected critical
through h. The excluded selected limb is disjoint
from the original carrier but the endpoint is in
its h-th pullback: this is the actual interior
contact, not an arbitrary filled-limb hit.

Use the two-bank separator/fine-side realization
from the suffix note: two bank hits cost <=4R;
otherwise there is a different raw auxiliary
window for an avoided bank. There are <=N actual
confined suffix and separator packets with the
same total pruning bound E_a. The earlier
positive-packet control argument makes them
K-controllable. Good original prefix transport
descends all these metric costs at coefficient one.

Let w be the original-parent width of the
remaining good auxiliary class. Subadditivity,
without any subtraction of overlapping widths,
gives

    w >= W-L_h-o-K*c_away-3M/4-3(V+C)-E_a-4R
      =  W-L_h-o-3M/4-H.                        (5)

The final primary now used is D_h (NOT D_(h+1)).
All suffix/separator auxiliary windows are
disjoint from that primary's literal time
interval, whereas the extra-step O auxiliaries
need not be. They are not included in (5)'s
series budget. Crucially D_h includes the
over-critical, localized-away and orientation
exception pieces still present in G_h; only
the *auxiliary* subfamily is restricted to
the good central-ending oriented portion.
This is legitimate because the metric addition
takes place on the disjoint Borel primary
images of the auxiliary class and its complement
in G_h. The first-anchor construction already
gave the required control of the whole D_h.
Thus, with total auxiliary width B<=NM,

    W(D_h) >= W-L_h+w^2/B                       (6)

when w>0 (B=0 would force w=0).

If W exceeds the right side of (1), then
A_b+C<tau*W/2 and H<W/32. By (3),
L_h+C<=tau*W. Equation (4) yields

    o/W <= 3*tau+sqrt(8*tau) < 1/32.

Also L_h+3*lambda*W/4<W/32, since
tau<=1/65536. Hence (5) gives
w>=5W/32>=W/8. The sum B is <=2NW,
and (6) implies

    W(D_h) >= (1-tau+1/(128N))*W
             > (1+lambda)*W,

contradicting the cap. These numerical
implications use W>0, N>=1, and the explicit
lambda and tau of section 1. If any relevant
output has infinite width, the cap fails already.
This proves (1) in the large-q case.

## 5. Small q

For 2<=q<=h+2 stop at j=q-2, when the common
positive crest first becomes precritical.
The whole surviving packet has one remaining
actual singleton step. Its mixed cap yields

    W-L_j <= 3M/4+3(V+C).

This contradicts W exceeding (1), because
L_j<=L_h<=tau*W and 3(V+C)<=H<W/32.
This includes q=2 (no crest advance).
The mixed cap needs no singleton condition
at j+2: its last over-critical comparison
uses only raw gaps in the one-step tower.
Thus no extra unbreakability beyond h+1 is
silently required in either branch.

## 6. Scope and reproducibility

The construction replaces the assumed sequence
of central-ending, whole-limb-crested packets
by a relative gain-or-discard telescope from
one positive initial crest. It neither asserts
that the absolute N1 discards are bounded nor
uses those discards. The terminal width
comparison is relative to this packet A.
A mixed positive/negative initial ambient
Wave, or a positive packet that is only a
small fraction of a larger ambient width,
still needs a separate extraction/terminality
argument. One must not add unrelated pushed
packets as if their supports were disjoint.

The corrected geometric marking and exact
saturated graph/host identification are still
premises. The away-Shift input must be
validated on that corrected action (or replaced).
Actual simple proper distinct-ended singleton
paths through the native horizon must be
provided, and initial positive-crest selection
and the final source-relative downstream
integration remain open. No canonical proof
obligation or global theorem is promoted.

The accompanying checker exhausts rational
bookkeeping for (2), tests the closed recurrence
(3) and the strict constants in (4)--(6),
and the small-q contradiction. It does not
certify any of the geometric inputs. No new
Lean declaration is claimed in this note;
the earlier kernel-checked packet, series
and mixed-cap inequalities are the formal
algebra used here. AI-assisted written
mathematics; specialist review pending.
