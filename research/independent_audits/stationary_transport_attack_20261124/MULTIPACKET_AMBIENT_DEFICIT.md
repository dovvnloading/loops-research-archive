# Multi-packet ambient stationary response: an explicit phase-deficit alternative

Continuation of [SECTOR_PHASE_ASSEMBLY](SECTOR_PHASE_ASSEMBLY.md)
and [AMBIENT_SHARED_CREST_RESPONSE](AMBIENT_SHARED_CREST_RESPONSE.md).

The common initial crest in the earlier ambient argument is replaced
by a bounded finite packet cover at each primary stage. The resulting
ambient defect inequality is explicit: a wide near-maximal input with
a positive stationary fraction must have a large cumulative
same-directed-cell phase-selection deficit, unless a strict wider
controllable Wave is already obtained. Arbitrary crossings of output
traces and unrelated endpoint cells no longer have to be treated as
uncontrolled losses. Actual phase collisions, output control and
native corrected geometric marking still require resolution.

## 1. Standing assumptions and the assembly interface

Use h=b+2, H=h+2, N=h+12b*2^h,
C=C_2=pi log(32)/(log 2)^2 and L_*=4pi/log 2.
Retain the exact corrected geometric marking, saturated full-hull
graph, old-proper end atoms, actual critical vertex deck pair,
two-bank separator and fine-side realization, commuting contour
squares, canonical lift and Borel path hypotheses in the earlier
stationary notes. Use their small-q stop before the wrap when
necessary. For the deep-contact route require q>=h+3 and h<q<=P.

Let A be an actual Borel lamination of simple proper marked
inner-ended parent paths, finite positive width W. No common
initial crest is assumed. Let S be its actual nonshort central-
ending subfamily with sequential singleton outputs through
h+1 (not H). Suppose W(S)>=sigma W, 0<sigma<=1.

For each primary stage require a Borel partition of the current
surviving ambient paths into at most m fixed actual crest-atom
packets, with the old-proper end fine atom criterion. Such a
cover exists for a union of k localized modules and one
leafwise over-critical module with at most 2k+1 anchors:
choose the adjacent atom in the actual direction from the
fixed localized end, or one atom in the critical block.
The adjacent-atom statement uses marked admissibility
and the actual cap class, including the long same-atom
class. It does not hold for arbitrary disconnected
aggregate crests without a leafwise realization.

Each packet uses the signed positive-gap construction, then
the multi-packet assembly theorem of SECTOR_PHASE_ASSEMBLY.
Require that its individual good output packet has a control
certificate of at most k_* localized modules and one leafwise
over-critical module. Alternatively supply a direct uniform
control certificate for the assembled output. This assumption
is not automatic merely from a finite anchor cover; the
noncritical singleton special case in the assembly note,
and near-critical bank control in the preceding notes,
are verified sufficient cases.

The cap class must include the assembled primary outputs
and all actual auxiliary packets. For example the former
have control at most m k_*+1 after the optional band prune,
and the latter in the suffix/separator and critical response
have the control bounds of AMBIENT_SHARED_CREST_RESPONSE.
Write K for one bound covering all these outputs. If m or
k_* depend on the input control k, K may also depend on k.
This is a genuine remaining source-uniformity issue, not
erased by the algebra below.

Discard incomplete canonical lifts of the original parents
to height H at cost 2^H V; charge the essential coincident-
ideal-end inputs by <=1/2 and the point-cut exceptions at
zero width as in the previous notes. The complete lift
through H gives complete lifts of every selected actual
simple retained suffix on its own window. This follows
by segmented reconstruction and the unique filled-graph
endpoints; singleton identity is needed only on S up to
h+1, not on all background leaves.

At stage j, select one good positive retained gap in each
of the ambient crest packets. Form the directed target
cell partition and the actual source phase groups of
SECTOR_PHASE_ASSEMBLY, section 5. In choosing the largest
phase per pair we can use widths on the original surviving
parents, not just their stage-j images: the finite Borel
classes partition the originals, and the previously good
prefix has coefficient-one transfer. Denote that stage's
phase-selection deficit by Delta_j>=0. The other deletions
in the assembly proof are descended at coefficient one
through the good prefix and individual current charts.
They cost at most

    J_m = m C + 2 T_m L_* + 10*binomial(T_m,2)+1,
    T_m = 4 m^2.

Here m can be a bound on the packet count at that stage.
This is a safe overcount, not an actual atom enumeration.
Use the same m bound through H. For any stage where all
selected cap bases lie in one injective sector the deficit
vanishes (and the direct smaller sector bound is available).

Define

    E_base = 1/2+2^H V+H J_m,
    Delta = sum_(j=1)^H Delta_j,
    E = E_base+Delta.

After all stages the same original good family G has
W(G)>=W-E. At every height j<=H its actual assembled
primary image D_j is a Borel disjoint lamination and
W(D_j)>=W(G). Its path map is injective, and the covering
is injective on the union of chosen raw source supports
at each step. All these statements persist upon restricting
intermediate D_j to the final original good set G.
Thus an admissible metric on D_j descends with
coefficient-one area to the corresponding literal
nested windows of the original parents. The proof
does not add intersecting projected packets.

## 2. Ambient comparison without a shared crest

Suppose every relevant actual K-controllable output has
width <=M=(1+lambda)W, lambda>=0. If some output is
infinite the cap has already failed. Put d_0=M-W+E.
The comparison rules from AMBIENT_SHARED_CREST_RESPONSE
now apply unchanged to the assembled primary D_j:

* For a subfamily with another retained raw window at
  step j projecting to the same actual simple singleton
  as its selected primary, its original width is <=d_0.
  The two distinct windows are disjoint. On that subfamily
  pull the output metric through both degree-two lifts
  (area <=2 times output area), push through I_1, and
  divide by two; previous primary charts preserve the
  energy bound. This gives double gain, without requiring
  the extra gaps of different packets to be disjoint.
  Add on disjoint primary output supports of that
  subfamily and its complement in G.

* For a subfamily with a separate auxiliary original-time
  window disjoint from its selected primary at height j,
  and n actual auxiliary packets of total width <=n M,
  the series metric on the two windows gives

      W(subfamily)^2 <= n M d_0.

  The auxiliary may have the same terminal image as
  the primary. Pull the auxiliary metrics through their
  individual charts and the assembled good prefix,
  combine by square-sum, and use the disjoint time
  windows. Primary addition is on disjoint output
  supports in D_j only.

Write Q_n=sqrt(n M d_0). These are literal metric
conclusions, not a sum of widths of overlapping
alternative covering images. No common crest for
G was used in either comparison once the actual
assembled primary sequence had been constructed.

## 3. Track the stationary subset

The remaining part of the proof is the stationary
tracking argument of AMBIENT_SHARED_CREST_RESPONSE
sections 4--6. For clarity, the common-ambient-crest
hypothesis of that note was needed to construct the
primary sequence and control its whole output.
Once sections 1--2 above provide those facts, the
tracking uses only the following leafwise data.

* A family crested over the whole BL_0 at any stage
  j with j+1<=H costs U=2C+Q_2 on the originals:
  the actual old-proper critical deck pair gives
  two distinct raw windows, after its two anchor
  discards. At least one differs from the chosen
  primary of that parent, regardless of which
  primary anchor packet it belongs to. The two
  auxiliary packets have the actual near-critical
  control certificate.

* A precritical-crested family with one remaining
  singleton step at j and j+2<=H costs
  Z=4C+d_0+Q_2. Test its first/last old-proper fine
  atoms. Bad gaps cost 2C; if either positive
  retained gap differs from the chosen primary,
  it is another lift of the same simple singleton,
  so use the double rule. Otherwise both anchors
  lie in that primary. The full pulled precritical
  block has angular length <1/2 and the selected
  primary's cap base has span <1/2. It cannot go
  the other way around the circle between the
  anchors, whose intervening block lies inside
  an interval of length <1/2. Both whole end
  atoms, and hence the entire block, lie inside
  its actual base. The output crests BL_0; apply U
  at j+1. No extra singleton is used at j+2.

* From a nonshort central end the actual adjacent
  limb dichotomy gives a positive crest BL_1
  or a precritical crest BL_(q-1). Assign the
  negative-only class to Z at stage 0. Track
  the positive class by testing first/last fine
  atoms of each successive full noncritical
  crest. Charge 2C for their bad gaps and d_0
  for an additional retained singleton lift
  distinct from the selected primary. Otherwise
  the whole proper pulled crest lies in the
  primary by the same angular argument; its
  output crests the whole next limb. Up to h
  steps cost at most h(2C+d_0) on the tracked
  class. All selected primaries in this argument
  lie in the initial half-disk-confined charts
  of section 1, so their actual base spans
  are <1/2 (in the source, <1/4); subsequent
  assembly only prunes trajectories.

* For small q stop at the first precritical
  crest and use Z, with the native h+1
  singleton horizon. For large q, at h the
  remaining tracked positive paths crest
  BL_(h+1). Their images are sublaminations
  of the assembled actual controllable D_h.
  Partition into central-ending, over-critical,
  and away-localized. Over-critical costs U
  at h; the away class costs <=K c_away,
  c_away=4V+2C+4 by AWAY_ENDPOINT_SHIFT,
  descended through the good prefix.
  This uses the leafwise over-critical
  module and actual localized modules of
  the control certificate, not arbitrary
  aggregate bases. The central-ending
  paths whose initial physical end is
  not in the open critical limb crest
  over the precritical block, so cost Z.

* The rest has a terminal initial critical
  end and the actual whole positive crest
  chain. The coherent suffix anchors and
  signed gaps yield either a distinct
  raw suffix auxiliary or a selected
  depth-h physical carrier contact, as
  in SUFFIX_ANCHOR_RESPONSE. This proof
  uses the actual chosen retained singleton
  chain of the tracked leaves, not the
  ambient primary anchor sequence of
  other leaves. Two bank hits cost <=4R;
  otherwise the separator gives a distinct
  auxiliary raw gap. The total additional
  pruning is E_a=sum_(r=1)^h C_(2^r)
  +12b*2^h*C_(2^h). There are <=N actual
  confined auxiliary packets. Their windows
  are disjoint from the final primary at
  h, and the auxiliary rule bounds the
  remaining width by Q_N.

For the same reason as in the earlier
ambient proof, the over-critical and
precritical extra-step auxiliaries are
compared against their own later D_j;
they are not counted as disjoint windows
of the stage-h primary. The background
surviving G has not been removed when
charging any of these tracked stationary
defects.

Collecting all deletions by subadditivity
on original parents gives the precise
ambient inequality

    W(S) <= E+B_fixed+(h+2)d_0+3Q_2+Q_N,         (1)

where

    B_fixed = (2h+10)C+K c_away+E_a+4R.

This is the former shared-crest inequality
with E replaced by E_base+Delta. It holds
under the displayed actual assembly and
control hypotheses even if different
original crest packets are unrelated,
and the background leaves are breakable.

## 4. Quantitative phase-deficit alternative

Put

    delta=sigma^2/(2048N),   lambda=delta/2.

If W(S)>=sigma W and no relevant output
exceeds (1+lambda)W, then (1) implies
at least one of the two inequalities

    E > delta W/2,
    E+B_fixed > sigma W/4.                        (2)

Indeed if both fail, d_0<=delta W and M<=2W.
Then (h+2)d_0<=sigma W/8 and
3Q_2+Q_N<=4 sqrt(2N delta) W=sigma W/8.
The right side of (1) would be <=sigma W/2,
a contradiction. Consequently

    Delta > min(delta W/2-E_base,
                 sigma W/4-E_base-B_fixed).

A negative bound is vacuous. For example, in
the absolute-scale regime

    E_base+B_fixed <= delta W/4,

(2) forces the simpler strict estimate

    Delta > delta W/4.                           (3)

All quantities other than Delta are controlled
by b, the indicated finite packet and control
bounds, sigma, R,V, and universal constants;
there is no new dependence on the rotation
denominator or tiny boundary-sector angles.

The conclusion (3) locates a **positive-width
phase-selection conflict**. Some stage has
Delta_j>delta W/(4H). At that stage some
directed cell pair has total discarded-phase
width >delta W/(4H T_m). There are at most
m phases. If m=1 this is impossible; otherwise
one discarded phase has width
>delta W/(4H T_m(m-1)), and the selected
maximal phase has at least that width.
These are widths of disjoint original parent
subfamilies whose actual chosen raw gap bases
belong to distinct inverse covering intervals
of the **same directed target cell pair**.
The certificate does not infer equality
or even intersection of individual projected
paths from the common cell pair.

In particular if all selected primary cap
bases lie in a common injective sector at
each stage, Delta=0 and the full earlier
ambient conclusion follows with E_base in
place of E. More generally the phase loss
at one stage is bounded by the original
width of selected bases leaving any one
injective sector. In the exact native
noncritical corridor, the singleton
endpoint-trap theorem of SECTOR_PHASE_ASSEMBLY
gives this property without a common crest.

## 5. Remaining native target and limitations

This is an actual finite assembly and
quantitative reduction, not a proof
that a near-maximal arbitrary controllable
Wave meets the no-phase-loss condition.
The exact two-deck-copy example in
SECTOR_PHASE_ASSEMBLY shows that such a
claim would be false for abstract covers.
A native theorem must use the critical
limb and old carrier geometry to bound
the competing phase mass, or give an
alternative response even if this mass
is large. For example, if a phase lies
outside the injectively translated
noncritical corridor, the next test
is its actual old-side host/critical
origin and whether an additional
literal window can be extracted on
the *same* parent, rather than another
parent in the competing phase.

Also the output control bound K and
the finite anchor cover must be
available through the ambient
primary sequence. In particular
dependence of m or k_* on the input
control k does not prove the source's
uniform terminal controllability
constant. One cannot silently enlarge
the class in a near-maximal comparison.
These are separate acceptance gates
from the finite phase accounting.

No assertion about the literal
unrestricted A.3.2 marking is made.
The exact saturated graph/host and
old-proper source realization remains
a premise, as does the wider native
mostly-short/fast-forward/terminal
integration. The finite arithmetic
and Lean lemmas do not establish
these geometric hypotheses. No
canonical ledger status or MLC
conclusion is promoted. AI-assisted
written proof, specialist review
pending.
