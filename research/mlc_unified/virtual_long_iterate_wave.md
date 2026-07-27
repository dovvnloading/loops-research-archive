# Virtual long-iterate Wave branch

## 1. Status and verdict

This note audits Kahn--Kapiamba--Lyubich (KKL), Proposition 3.9, down to
the individual pullback, marking, degree, and stopping-time hypotheses needed
to transfer its proof to Dudko's partially invariant virtual Julia sets.

The conclusions are:

1. **KKL Proposition 3.9 is a source-stated theorem in the full
   parabolically \(B\)-bounded, prime primitively renormalizable
   \(\psi\)-quadratic-like category, but this project does not certify the
   v1 proof.**  Its bounded-visits argument lacks the required strict
   marked-interval growth step, while its stationary paragraph has an
   off-by-one occurrence, a false degree-one clause, and an unproved final
   proper-path/measurable-lamination extraction.  The first index error and
   the degree are repaired; the other two gates remain open.
2. **The proposed proof program is finite-horizon conditional on the
   bounded-visits repair.** For a fixed access/defect bound \(B\), a
   safe, non-optimized audit horizon is
   \[
     H_B(q)
     :=
     (216B^2+1)(q+B+4).
   \tag{1.1}
   \]
   Thus an all-horizon virtual object is unnecessary for this branch, but a
   single first return is generally insufficient.
3. **The long iterate is not paid for stage by stage.** KKL uses one
   fiber-product iterate with a selected degree profile. Replacing it by the
   global degree \(2^n\), or summing a positive buffer loss over \(n\asymp q\)
   stages, destroys period-independent constants.
4. **A single selected degree-two endpoint return is not the object used in
   the fast-forward proof.** KKL simultaneously retains a degree-one corridor
   and a bounded terminal fan whose pieces have degrees
   \(2,2^2,\ldots,2^L\), where \(L\) is fixed before \(q\). A virtual
   construction must retain this bounded fan or prove a different exhaustive
   wave decomposition.
5. **A conditional proof schema is proved below.** If the source-stated KKL
   theorem is supplied as a hypothesis and a virtual block realizes the
   corrected marked finite-horizon package in Definition 8.1, then the
   source terminal-wave proof can be transported using only data through
   (1.1), with constants independent of \(q\).  This is not an independent
   certification of Proposition 3.9.
6. **The realization theorem remains open.** Dudko's virtual-Julia-set
   proposal supplies a connected hull of Cantor small Julia sets and a finite
   critical-orbit segment. It does not construct the pulled ideal markings,
   selected fan, proper/end-proper interval action, critical-visit expansion,
   or marked-width comparison required below.

Nothing in this note proves the Virtual Long-Iterate Wave Lemma for arbitrary
virtual-Molecule blocks, the Master Transition Lemma, or MLC.

## 2. Source lock

Primary sources:

- J. Kahn, A. Kapiamba, and M. Lyubich,
  [*MLC for parabolically bounded primitive renormalization*](https://arxiv.org/html/2606.27272),
  arXiv:2606.27272v1, 25 June 2026;
- D. Dudko and M. Lyubich,
  [*MLC at Feigenbaum points*](https://arxiv.org/html/2309.02107),
  especially Lemmas 5.1--5.2;
- D. Dudko and M. Lyubich,
  [*Uniform a priori bounds for neutral renormalization*](https://arxiv.org/abs/2210.09280),
  especially the Shift Argument;
- D. Dudko,
  [*On the MLC Conjecture and the Renormalization Theory in Complex Dynamics*](https://arxiv.org/html/2512.24171),
  especially Interpolation Problem 4.4 and the virtual-Julia-set proposal.

The complete source archives, rather than the abstracts, were checked. The
relevant source-file hashes are:

| source file | SHA-256 |
|---|---|
| KKL `waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| DL23 `Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| DL24 `PseudoSiegelBounds.tex` | `4AE3253817EF8EEB76DF95FA411CB9C2B6CB0642C3C4AED4D8AE8305F2122172` |

The KKL source ranges used are:

| subject | `waves-with-Misha.tex` lines |
|---|---:|
| canonical renormalization and amplification | 476--492 |
| limbs, Hubbard tree, and core entropy | 495--535 |
| parabolically \(B\)-bounded definition | 661--667 |
| Proposition 3.9 | 736--739 |
| controllable-wave input from Section 4 | 750--769 |
| limb-side bound \(|\mathcal B L_j|\le 6B\) | 838--866 |
| terminal-wave architecture | 1142--1228 |
| interval action and bounded critical visits | 1232--1342 |
| breakable and mostly-short waves | 1346--1677 |
| long fast-forward | 1681--1797 |
| ideal markings and waves | 1839--1875 |
| covering/immersion width rules | 2060--2124 |
| induced marking action, Wave and Shift lemmas | 2126--2178 |

The DL23 source ranges used are `Feigen.tex`, lines 2797--2864. The
\(O(\log d)\) buffer-removal estimate is at lines 2821--2842. The DL24 Shift
Argument is `PseudoSiegelBounds.tex`, lines 8850--8880.

Throughout KKL Section 6, \(B\) is fixed. A constant called "universal" there
may depend on \(B\), but not on \(q\), the primitive period, or the particular
map. The controlling amplification convention is
\[
  \mathbb W(F)\ge M\,\mathbb W(\mathcal R F).
\tag{2.1}
\]
The reversed inequality printed at KKL line 698 is the already documented
orientation typo; it is not the convention used in the proof.

## 3. Exact source statement and certification status

Fix \(B\). Let \(F=(f,\iota)\) be a periodically repelling, prime
primitively renormalizable \(\psi\)-quadratic-like map whose renormalization
is parabolically \(B\)-bounded. In particular:

1. the limb rotation is \(1/q\);
2. each limb contains at most \(B\) components of the full small-Julia cycle
   \(\mathcal K\);
3. every component of \(\mathcal K\) in the critical limb maps into the
   \(B\)-neighborhood of the critical limb.

KKL Proposition 3.9 states:

> For every \(M\), there is \(N=N(B,M)\) such that, if
> \(\mathcal U\setminus\mathcal T\) has \(N\)-wide controllable waves and
> \(F\) is sufficiently high-type-near-degenerate relative to \(B,M\), then
> \(F\) has \(M\)-amplification.

This paragraph records the source statement, not a completed import.
In the project ledger `KKL_PARABOLIC_WAVE_AMPLIFICATION` is open until
both `KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR` and
`KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR` close.

Here \(\mathcal T\) is the complete Hubbard tree, its sides induce the complete
ideal marking \(\mathcal I\), and "controllable" means that a wave is a union
of one wave cresting over the critical limb and a bounded number of localized
waves.

The proof first establishes constants \(\delta_B>0\) and
\(\eta_B<\infty\) such that every sufficiently wide controllable wave \(A\)
is terminal:
\[
 \mathbb W(\mathcal U\setminus\mathcal T)
   >\delta_B\mathbb W(A)
 \quad\text{or}\quad
 \mathbb W(A')
   >(1+\delta_B)\mathbb W(A)
\tag{3.1}
\]
for an \(\eta_B\)-controllable wave \(A'\). Choosing a nearly widest
\(\eta_B\)-controllable wave rules out the second alternative. The first
then gives (2.1).

## 4. Dependency graph of the proof

The source proof is best read as the following directed graph.

```text
Proposition 3.9
  |
  +-- Terminal-wave lemma
       |
       +-- Mostly-short proposition
       |    |
       |    +-- Breakable => terminal
       |    |    +-- exact ideal-marking action
       |    |    +-- proper/end-proper restriction
       |    |    +-- itinerary proposition
       |    |    +-- Wave pushforward, loss O(1+log d)
       |    |
       |    +-- Long unbreakable => mostly short
       |         +-- critical crest: critical reset
       |         +-- translation crest: Shift Argument
       |         +-- entering critical limb:
       |              nested pullback trees through B+2
       |              + degree-one selected pushforward
       |              + comparison with W(RF)
       |
       +-- Critical-visit proposition
       |    |
       |    +-- bounded-time short pushforward
       |    +-- long fast-forward
       |         +-- all pulled markings through n <= q
       |         +-- proper middle corridor
       |         +-- bounded terminal degree fan
       |         +-- exhaustive itinerary decomposition
       |
       +-- Bounded-critical-visits lemma
            +-- exact limb shift and critical reset
            +-- strict growth of short critical crests
            +-- exclusion of a periodic short interval
```

Only the long fast-forward has length comparable with \(q\). The other
geometric wave estimates use bounded depth once \(B\) is fixed. However, the
terminal proof can concatenate a bounded number of long critical visits, so
the virtual horizon must cover the concatenation, not just one call to the
fast-forward proposition.

## 5. Detailed source audit

### 5.1 Complete ideal marking and induced action

KKL starts with the complete side marking \(\mathcal I\) of the finite
Hubbard tree. For the one-step correspondence, it proves:

\[
  f^*\mathcal I \text{ refines } \iota^*\mathcal I.
\tag{5.1}
\]

This gives the well-defined action
\[
  F_* = f_*\iota^*
\tag{5.2}
\]
on intervals, paths, laminations, and waves. The proof uses the actual
pullback tree \(f^{-1}(\mathcal T)\), not just a map of a selected crest.

For every long iterate used later, KKL forms
\[
  \mathcal U^n=f^{-n}(\mathcal U),\qquad
  \mathcal T^n=f^{-n}(\mathcal T),\qquad
  \mathcal I^n=(f^n)^*\mathcal I,
\tag{5.3}
\]
and the fiber-product immersion \(\iota_n\). It then uses the exact identity
\[
  f_*^n\iota_n^*I=F_*^nI.
\tag{5.4}
\]

For a virtual hull, (5.4) requires all of the following:

- every pullback interval exists;
- pulled intervals are pairwise disjoint;
- the refinement (5.1) holds at every stage;
- cyclic order and end intervals are preserved;
- stage maps compose to the same interval action as the long map;
- no omitted end permits a restriction path to escape.

Forward inclusion of the critical orbit does not imply any item on this list.

### 5.2 Local side count and controllability

KKL proves
\[
  |\mathcal B L_j|\le 6B
\tag{5.5}
\]
for the complete multi-interval of every limb. Consequently every short wave
is \(12B\)-controllable.

The proof of (5.5) uses the hull in the complete Hubbard tree of the fixed
point and all small Julia components in the limb. A bound on selected virtual
components is not enough: omitted Cantor components, added dams, fjords, and
multiple accesses can add sides without increasing the selected component
count.

### 5.3 General analytic transport lemmas

Three analytic rules are repeatedly used.

1. If a covering has degree at most \(d\) on the relevant end, a pushed
   lamination contains a lamination \(A\) satisfying
   \[
     \mathbb W(A')
       \le d\,\mathbb W(A)+2d.
   \tag{5.6}
   \]
2. For waves, DL23 buffer removal improves the loss to
   \[
     \mathbb W(A')
       \le \mathbb W(A)+O(1+\log d).
   \tag{5.7}
   \]
3. If a wave and a conformal shift have linked boundary order, the Shift
   Argument gives a universal upper bound for the unbreakable part.

The hypotheses "on the relevant end", "wave", "conformal shift", and "linked
boundary order" are essential. A topological correspondence of hulls does not
supply them.

### 5.4 Breakable waves

For a wave \(A\), the restriction by \(\iota\) is decomposed into:

- a vertical part;
- an inward-breaking part that produces two waves;
- an outward-breaking part meeting one of the finitely many intervals on
  which \(F_*\) is improper;
- an unbreakable remainder.

Properness on the crest, end-properness at its endpoints, and the itinerary
proposition show that this list is exhaustive. Harmonic-sum estimates then
turn a definite breaking fraction into either vertical width or a wider
controllable wave.

This is not a purely local drawing argument. If one proof-used restriction is
missing from a virtual partial cover, the asserted partition of \(A\) can
lose positive width and the conclusion no longer follows.

### 5.5 Constant-depth critical-limb alignment

The difficult bounded-depth case is a wave entering the critical limb. KKL
uses nested pullbacks
\[
  \mathcal L_0^0,\mathcal L_0^1,\ldots,
  \mathcal L_0^{B+2}
\tag{5.8}
\]
inside the full pullback trees. Since the critical limb contains at most
\(B\) components of \(\mathcal K\), the \(B\)-th nested limb is disjoint from
the original tree.  The corrected final level is \(m=B+2\).  Filled-set
graph naturality realizes the component over \(K_0^{B+1}\), but its local
and ideal-boundary degree under \(f^m\) is two, not the degree one printed
in KKL.  The source also does not prove that “passes through” yields one
retained proper path and measurable lamination after the final immersion
restriction filter.  Conditional on that extraction, domination and the
degree-two pushforward lemma give
\[
 \mathbb W(A_m)\leq\mathbb W(B)
 \leq2\mathbb W(C)+4
 \leq4\mathbb W(\mathcal R F)+4.
\tag{5.8a}
\]

The virtual analogue must therefore retain:

- the relevant components of every \(\mathcal K^s\), \(s\le B+2\);
- the canonical final graph component over \(K_0^{B+1}\);
- one proper occurrence-tagged measurable lamination surviving the complete
  restriction filter, with prime-end landing;
- the exact degree-two itinerary and \(+4\) pushforward charge;
- the marked-family comparison to the successor degeneration.

Containing the forward critical orbit does not construct these inverse
components.

### 5.6 Exact interval dynamics and bounded visits

Away from the critical limb, KKL has
\[
  F_*\mathcal B L_j=\mathcal B L_{j+1};
\qquad
  F_*\mathcal B L_0=\partial_{\mathrm C}\mathcal T.
\tag{5.9}
\]
It proves properness on the middle corridor
\[
  \mathcal B L_{[B,q-B-2]}.
\tag{5.10}
\]
This yields one stretching multi-interval of length at most two and uniformly
bounded images for all other intervals.

The source then proves that a short crest grows after at most a bounded number
of critical visits and takes
\[
  R_B=216B^2
\tag{5.11}
\]
as an impossible length for a critical-visit chain.

There is a transfer subtlety here. At KKL line 1331, periodic repetition of a
short multi-interval is excluded by invoking \(\lambda_F>1\). In the KKL
Hubbard-tree setting, this uses the coupling of the complete side marking to
the primitive expanding tree map. For a virtual quotient, positive entropy of
some retained core is not by itself enough: the periodic marking interval
might be invisible to the expanding branch. The virtual theorem must prove
one of the following explicitly:

1. every proof-used short critical interval is observed by the primitive core
   strongly enough to exclude periodic repetition; or
2. the strict critical-visit growth statement itself.

It may not replace this step by a bare assertion that a separate transition
matrix has spectral radius greater than one.

### 5.7 The genuinely long fast-forward

Let a short wave have crest near limb \(j\), with
\[
  B<j<q-B-L-1,
\]
where \(L\) is chosen from the desired width margin before \(q\). KKL sets
\[
  n=q-B-j-2.
\tag{5.12}
\]

The long pullback has two simultaneous features:

1. a degree-one translation region carrying the outgoing wave;
2. a bounded terminal fan on which the degrees are
   \[
     2^m,\qquad 1\le m\le L,
   \tag{5.13}
   \]
   and the total degree on the selected terminal union is at most
   \(2^{L+1}\).

The restricted wave is decomposed into four families:

- **vertical:** gives definite parent width through (5.6);
- **outgoing:** survives along the degree-one corridor and produces the
  critical visit;
- **lost:** maps over the whole boundary and has only bounded width by
  (5.7);
- **amplifying:** produces a wider controllable wave.

The itinerary proposition and proper/end-proper action prove that these four
families exhaust the original wave.

The important quantitative point is
\[
  \log(2^{L+1})=O(L),
\tag{5.14}
\]
with \(L\) independent of \(q\). KKL absorbs the resulting bounded losses
using the large successor width. If one instead uses the global degree
\(2^n\), then
\[
  \log(2^n)=n\log2=O(q),
\tag{5.15}
\]
while the vertical estimate loses a factor \(2^{-n}\). Neither loss is
uniform in \(q\).

### Proposition 5.1 (a degree-two endpoint return is insufficient)

Suppose a virtual model retains only one proper long-return component of total
degree two. If \(L\ge2\), that component cannot realize the KKL fast-forward
fan (5.13).

**Proof.** The degree of a proper restriction to any union of sheets over the
same regular target is at most the total degree of the retained proper map.
The KKL fan contains a proof-used region of degree \(2^L\ge4\), whereas the
retained map has total degree two. Thus that one component cannot contain the
required region. One must retain additional fiber-product components/sheets
or replace the source decomposition with a new argument. \(\square\)

This does not contradict the degree-two selected quadratic-like return used at
a checkpoint. It says that the wave proof needs a larger **auxiliary
multi-component fan** around that selected return.

### 5.8 Terminality and amplification

The mostly-short result, critical-visit result, and the bound (5.11) are
combined with a finite sequence of width-retention parameters. Since the
number of visits depends only on \(B\), the product loss remains a positive
\(B\)-dependent constant. This gives (3.1).

Finally, KKL chooses a nearly widest controllable wave. The wider-wave branch
of (3.1) is impossible by this choice, so the vertical branch yields
amplification.

## 6. Stopping-time and error ledgers

### 6.1 Time ledger

| proof segment | source time | virtual data required |
|---|---:|---|
| one-step marking/breaking | \(1\) | one covering/immersion stage and all restricted ends |
| critical-limb alignment | \(B+3\) | nested pullback trees and small-set components |
| one fast-forward | at most \(q+B+3\) | one long fiber product plus its entire stage marking |
| critical-visit chain | fewer than \(216B^2\) visits | concatenated pulled markings and fans |
| safe total audit horizon | \(H_B(q)\) in (1.1) | all proof-used stages before data are discarded |

The bound (1.1) is deliberately conservative. It is not asserted to be
optimal. Its role is to prevent the phrase "an appropriate number of first
returns" from hiding a missing factor \(216B^2\).

### Proposition 6.1 (finite-horizon sufficiency)

Assume the strict marked-interval growth implication isolated in
`KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR`.  Then every dynamical pullback
used in the KKL proof program for Proposition 3.9 has length at most
\(H_B(q)\), after concatenating the waves in one terminality argument.

**Proof.** The only unbounded call is the fast-forward (5.12), followed by at
most \(B+2\) further shifts to meet the critical limb. Thus one critical visit
uses at most \(q+B+3\) original iterates. KKL forbids a chain of
\(216B^2\) critical visits. The remaining pullbacks have depth at most
\(B+3\) and are covered by the added slack in (1.1). Multiplying the safe
per-visit budget by the safe visit count proves the claim. \(\square\)

### 6.2 Error ledger

| source of loss | KKL size | condition for virtual uniformity |
|---|---:|---|
| canonical buffers | \(O_B(1)\) | one-shot or telescoped, not once per corridor cell |
| wave pushforward | \(O(1+\log d)\) | \(d\le d_B\) on the selected end/fan |
| vertical pushforward | multiplicative \(d_B\) | selected degree bounded independently of \(q\) |
| bounded number of improper intervals | \(O(B^2)\) | complete access marking and defect localization |
| critical-limb connector | \(O_B(\mathbb W(\mathcal R F))\) | common marked-family comparison |
| chart/inflation change | absent in KKL | total \(o(\mathbb W(A))\), uniformly in \(q\) |

An estimate with error \(C\) at each of \(q\) stages gives \(Cq\), not the
source \(O_B(1)\). A virtual proof must construct the long map and estimate it
in one shot, telescope the errors, or charge them to a separately controlled
state coordinate.

## 7. Source-to-virtual object map

| KKL object | required virtual realization |
|---|---|
| full filled set \(K_F\) | full access-faithful virtual hull, with any filling additions charged |
| complete small-Julia cycle \(\mathcal K\) | every Cantor component and pullback component used by a proof leaf through \(H_B(q)\) |
| finite Hubbard tree \(\mathcal T\) | finite ribbon/tree carrier preserving every proof-used access and separation |
| side marking \(\mathcal I\) | complete prime-end marking, not a selected component count |
| limb multi-intervals \(\mathcal B L_j\) | cyclic corridor cells with \(O(B)\) complete sides per cell |
| \(F=(f,\iota)\) | analytic covering/immersion correspondence on the marked complement |
| \((f^n,\iota_n)\) | compatible selected fiber-product or mapping-telescope iterate through the declared horizon |
| \(F_*=f_*\iota^*\) | exact functorial action on intervals, paths, and wave laminations |
| proper middle corridor | no omitted pullback component or access in the translation region |
| terminal degree fan | retained auxiliary sheets with profile (5.13) |
| core entropy \(\lambda_F>1\) | marking-observable strict critical-visit growth |
| \(\mathbb W(\mathcal R F)\) | calibrated successor virtual degeneration \(D^+\) |
| \(\mathbb W(\mathcal U\setminus\mathcal T)\) | calibrated parent/vertical degeneration \(D^-\) |
| KKL wide wave | a genuine lamination in the realized marked surface, with the same crest and end classes |

Dudko's proposal supplies the first row only at a strategic level, together
with a finite segment of the critical orbit. The remaining rows are
construction theorems.

## 8. The minimal conditional theorem

### Definition 8.1 (wave-admissible virtual parabolic corridor)

Fix \(B,q\). A virtual block is **wave-admissible through \(H_B(q)\)** if it
provides the following data.

#### Marked carrier

`WA1.` A full connected virtual carrier and a finite access-faithful ribbon
core \(\mathcal T^v\), with complete ideal marking \(\mathcal I^v\).

`WA2.` A cyclic decomposition into limb multi-intervals
\(\mathcal B L_j^v\), \(j\in\mathbb Z/q\mathbb Z\), satisfying
\[
  |\mathcal B L_j^v|\le C_0B
\tag{8.1}
\]
and containing every access used below.

#### Finite-horizon analytic dynamics

`WA3.` Stage correspondences and selected fiber products through
\(H_B(q)\), all acting on hyperbolic finite-type marked surfaces.

`WA4.` For every proof-used \(n\le H_B(q)\), all pulled intervals exist and
are disjoint,
\[
 (g_n)^*\mathcal I^v\text{ refines }(\iota_n)^*\mathcal I^v,
\]
and the analogue of (5.4) holds with composition-compatible cyclic order.

`WA5.` The induced interval action has the KKL shift/reset rules (5.9), is
proper on the middle corridor, and is end-proper on every crest, end, and
limb crossed by the proof.

#### Combinatorial expansion

`WA6.` There is one stretching multi-interval of uniformly bounded length,
all other one-step interval images have \(O_B(1)\) length, and every short
critical crest strictly grows within \(O_B(1)\) critical visits. In
particular, no critical-visit chain of length \(R_B\) exists.

The last clause must be proved on the virtual marking. Positive entropy on an
unobserved quotient is not a substitute.

#### Analytic wave transport

`WA7.` Every restricted path has the exhaustive KKL itinerary on the
selected surfaces. The covering, immersion, domination, Wave, and Shift
lemmas apply to the retained families.

`WA8.` Each long fast-forward has a degree-one central corridor and a
bounded auxiliary fan with the KKL degree profile through the fixed terminal
depth \(L\). All degree and \(O(1+\log d)\) constants are independent of
\(q\).

`WA9.` At the stationary critical-limb stage, the canonical graph component
over \(K_0^{B+1}\) is retained.  The immersion restriction contains one
proper occurrence-tagged measurable lamination with the required prime-end
landing and
\[
 \mathbb W(A_m)\leq\mathbb W(B).
\]
The selected final restriction has degree two, and the proof charges
\[
 \mathbb W(B)\leq2\mathbb W(C)+4,
\]
not a degree-one estimate.

#### Width and error interface

`WA10.` There are parent and successor coordinates \(D^-,D^+\) comparable
to the exact KKL marked families used in the proof, with constants
independent of \(q\), rotation data before acceleration, and virtual depth.

`WA11.` The total error of each one-shot fast-forward, critical-limb
alignment, and chart change is at most \(E_B\), where
\[
  E_B\le \epsilon_B D^+
\tag{8.2}
\]
for a sufficiently small \(\epsilon_B\). No uncharged error is summed over
\(q\) stages.

`WA12.` If the original rotation is not \(1/q\), the block supplies an
accelerated order-preserving corridor for which `WA1`--`WA11` hold. A
formal relabeling by the inverse numerator is not accepted unless it
preserves the geometric cyclic intervals, defect region, and selected
degree profile.

### 8.1 Selector and threshold ledger

To compose with `virtual_branch_assembly.md`, fix a requested output factor
\(L\ge1\) and declare the following quantities before invoking the static
trichotomy:

\[
  P_w(B,L)\ge L,
\tag{8.3}
\]
the input width parameter for the wave branch;
\[
  Q_w(B,L)<\infty,
  \qquad
  A_w(B,L)<\infty,
\tag{8.4}
\]
the lower thresholds for the limb-corridor parameter \(q\) and successor
width \(D^+\), respectively;
\[
  R_w(B)=216B^2,
  \qquad
  H_w(B,L,q):=H_B(q)
   =(R_w(B)+1)(q+B+4),
\tag{8.5}
\]
the critical-visit and available-horizon requirements; and
\[
  m_w(B,L)<\infty,
  \qquad
  d_w(B,L):=2^{m_w(B,L)+1},
\tag{8.6}
\]
the terminal-fan depth and the resulting upper bound on the selected fan
degree.

In the literal KKL proof, the terminal-wave constants, visit bound, and fan
depth can be selected after \(B\) is fixed and before the requested output
factor is used in the final nearly-maximal-wave argument. Allowing
\(m_w\) to depend on \(L\) in (8.6) is a harmless conservative interface.
What matters for assembly is that none of (8.3)--(8.6) depends on \(q\),
the original rotation, or virtual depth, except for the explicitly displayed
linear occurrence of \(q\) in \(H_w\).

The predicates of `virtual_branch_assembly.md` are interpreted here as
\[
 \operatorname{Wave}_{P}(F)
 \iff
 \text{the realized tree complement has a \(P\)-wide controllable wave},
\tag{8.7}
\]
and
\[
 \operatorname{Amp}_{L}(F)
 \iff
 D^-\ge L D^+
\tag{8.8}
\]
after the declared `WA10` chart comparison. No monotonicity of
\(\operatorname{Wave}_P\) is used.

### Theorem 8.2 (selector-form finite-horizon KKL wave transfer; conditional)

Fix \(B\) and \(L\ge1\). The quantities
\[
 P_w(B,L),\ Q_w(B,L),\ A_w(B,L),\
 m_w(B,L),\ d_w(B,L),\ H_w(B,L,q)
\]
can be selected so that the following implication holds:
\[
\begin{split}
 &q\ge Q_w(B,L),\qquad
 D^+\ge A_w(B,L),\qquad
 h_{\rm avail}\ge H_w(B,L,q),\\
 &\deg_{\rm selected\ fan}\le d_w(B,L),\qquad
 \operatorname{Wave}_{P_w(B,L)}(F)
 \end{split}
 \quad\Longrightarrow\quad
\operatorname{Amp}_{L}(F).
\tag{8.9}
\]

The implication is conditional on the source-stated KKL Wave theorem and
on the block satisfying Definition 8.1 through the displayed available
horizon. Branch assembly must take the
maximum of the displayed lower \(q\)-, width-, and horizon requirements and
must separately verify the selected-fan degree/profile certificate.

Here the degree premise means that the full marked fan required by `WA8`
exists with its prescribed degree-one corridor and degree profile through
\(m_w(B,L)\); a smaller number attached only to one endpoint return does not
satisfy the premise.

The constants do not depend on \(q\), the original rotation number once
`WA12` has been realized, or the virtual transition depth. In particular,
Theorem 8.2 has exactly the branch-assembly form
\[
 \operatorname{Deg}_{Q_w(B,L),A_w(B,L)}(F)
 \wedge
 \operatorname{Wave}_{P_w(B,L)}(F)
 \Longrightarrow
 \operatorname{Amp}_{L}(F),
\tag{8.10}
\]
with the additional displayed horizon and selected-fan certificate.

**Proof.** By `WA1`--`WA5`, every ideal interval, wave, restriction, and
long action appearing in KKL Section 6 is defined with the same cyclic and
properness relations. `WA6` supplies the bounded-critical-visits lemma.
`WA7` supplies the source analytic transport inequalities. `WA8` supplies
the only unbounded iterate with degree and buffer losses independent of
\(q\). `WA9` supplies the remaining constant-depth geometric estimate.
Proposition 6.1 shows that no source step uses data past the declared
horizon.

Consequently the proof graph in Section 4 reproduces KKL's terminal-wave
lemma. Only finitely many width-retention parameters occur after \(B\) is
fixed. Choose them, record the largest required terminal depth as
\(m_w(B,L)\), and record its fan-degree bound as \(d_w(B,L)\). Choose the
source inequalities with slack and then choose \(\epsilon_B\) in (8.2)
small enough to preserve half of every strict margin. Let \(Q_w(B,L)\) be
the maximum of the source lower bounds on \(q\), including the requirement
that the translation corridor be longer than every fixed terminal window.
Let \(A_w(B,L)\) be the maximum of the source large-width and error-absorption
thresholds.

The nearly maximal controllable-wave argument then supplies a required
wave-input lower bound \(P'_w(B,L)\). For the concrete predicate (8.7), the
following downward monotonicity is immediate and is proved here rather than
assumed in branch assembly:
\[
 P\ge P',\quad \operatorname{Wave}_{P}(F)
 \Longrightarrow \operatorname{Wave}_{P'}(F).
\tag{8.11}
\]
Indeed, the same controllable wave satisfies
\(\mathbb W(A)\ge P D^+\ge P'D^+\). Set
\[
  P_w(B,L)=\max\{L,P'_w(B,L)\},
\]
which establishes (8.3); the static split and this theorem are both called at
this one declared value. Proposition 6.1 gives the horizon (8.5). The
terminal argument yields
\(\operatorname{Amp}_L(F)\), and `WA10` transfers it to \(D^-,D^+\).
\(\square\)

### Scope of Theorem 8.2

Theorem 8.2 is a proved **conditional reduction**, not a proof of the
source theorem and not the open realization. Its hypotheses deliberately
expose the exact analytic and combinatorial work. It must not be entered in
the ledger as a proof that either KKL's v1 stationary argument is complete
or arbitrary Dudko virtual hulls satisfy the Wave alternative.

## 9. Three irreducible construction targets

The open realization separates naturally into three lemmas.

### 9.1 Virtual Marked Interval-Action Lemma (`OPEN`)

Construct `WA1`--`WA6` from the virtual Cantor carrier:

- the complete pulled side markings;
- the shift/reset rule and middle properness;
- the unique bounded stretching region;
- marking-observable critical-visit growth.

This lemma must address the possibility that omitted Cantor components add
new sides or shield a periodic short interval from the expanding core.

### 9.2 Virtual Critical-Limb Alignment Lemma (`OPEN`)

Construct `WA9` and its width comparison:

- all nested critical-limb pullback components through depth \(B+2\);
- the canonical final graph component;
- one retained proper path/measurable lamination surviving the complete
  immersion restriction filter, with prime-end landing;
- the exact degree-two itinerary and \(+4\) pushforward charge;
- comparison of the pushed connector family with \(D^+\).

### 9.3 Selected Marked Fast-Forward Fan Lemma (`OPEN`)

For every proof-used short crest, construct in one shot:

1. the long selected pullback correspondence at time (5.12);
2. the degree-one central corridor;
3. the terminal fan (5.13);
4. properness and end-properness on every crossed interval;
5. the exhaustive vertical/outgoing/lost/amplifying decomposition;
6. a total error \(O_B(1)\), or an explicitly telescoping/relative error,
   independent of \(q\).

This is the genuinely long analytic bottleneck. It is more precise than the
phrase "controlled selected degree": the simultaneous fan and its marking
are required.

## 10. Adversarial tests

### Test A: only one critical first return is retained

An abstract interval system can agree with the KKL shift for one full limb
circuit, keep a short crest unchanged at the first return, and expand it
only after the second or later return. A virtual hull truncated after one
return cannot distinguish that system from one with a periodic short crest.

**Verdict:** one first return does not imply the bounded-visits conclusion.
Retain the full \(H_B(q)\) horizon or prove a uniform reanchoring theorem at
each visit.

### Test B: global polynomial iterate

For \(n\asymp q\), the global degree is \(2^n\). Equation (5.7) then loses
\(O(q)\), and (5.6) loses a factor \(2^q\).

**Verdict:** fails uniformity. A selected degree profile is mandatory.

### Test C: stage-by-stage buffer removal

Even if each one-step wave pushforward loses only \(C_B\), iterating the
estimate \(q\) times loses \(qC_B\).

**Verdict:** fails unless the error telescopes or is charged to a coordinate.
KKL avoids this by using one long selected map.

### Test D: bounded selected occupancy, unbounded accesses

Attach \(r\) full hairs or fjords to one selected continuum in a limb, with
each hair defining a dynamically distinct prime-end interval. The selected
component count remains one while the complete limb marking has \(r\) sides.

**Verdict:** selected occupancy does not imply (8.1), short-wave
controllability, or bounded constants.

### Test E: positive entropy hidden from the marking

Take an expanding primitive core with a retained deterministic side label
whose continuation never records the branching edge. The core spectral
radius is greater than one while the side label is periodic in the quotient.

**Verdict:** bare core entropy does not prove `WA6`. A marking-to-core
observability theorem is required.

This is a counterexample schema to the **inference**, not a claim that the
full KKL Hubbard tree has such a hidden side.

### Test F: only a degree-two selected telescope

For terminal depth \(L\ge2\), KKL needs a degree-\(2^L\) fan piece.
Proposition 5.1 rules this out inside a lone degree-two proper return.

**Verdict:** retain an auxiliary multi-component fiber-product fan or replace
the fast-forward decomposition.

### Test G: arbitrary numerator \(p/q\)

The KKL proof uses one long geometrically contiguous \(+1\) translation
corridor. Conjugating the orbit permutation \(j\mapsto j+p\) to
\(+1\) by multiplying labels by \(p^{-1}\) need not preserve geometric
contiguous intervals or the bounded defect neighborhood.

**Verdict:** KKL does not provide numerator-independent realization. A
continued-fraction/molecule block must construct the accelerated corridor
required by `WA12`.

### Test H: alternating wave and neutral blocks

A wave arriving at a pseudo-Siegel regularization can change its prime-end
base, split at a dam, or become serial rather than parallel in the new chart.

**Verdict:** terminality does not cross this interface without `WA10` and
`WA11`. The neutral chart cannot be treated as an identity.

### Test I: rapidly increasing \(q\)

If `WA1`--`WA12` hold with fixed \(B\), the source constants and the safe
horizon depend on \(q\) only through the length of the retained data, not
through the terminal margin.

**Verdict:** this adversary is passed by the conditional theorem, but no
virtual construction presently verifies the hypotheses.

### Test J: unbounded \(B\)

The visit bound \(216B^2\), limb-side bound \(6B\), controllability count,
and terminal constants all depend on \(B\).

**Verdict:** the KKL theorem is not uniform as \(B\to\infty\). A unified
application must prove a universal access/defect bound after block grouping,
or introduce a new calibrated coordinate that absorbs the \(B\)-dependence.

## 11. Partial-invariance audit certificate

Every proposed application should provide one row for each wave transition:

| field | required entry |
|---|---|
| source wave | support, crest, two ends, controllability decomposition |
| absolute time | start time and cumulative time from block entry |
| chosen iterate | one-step, bounded critical depth, or long fast-forward |
| stage hulls | every forward-closed excluded set through the iterate |
| pulled marking | all intervals and endpoints in cyclic order |
| proper locus | crest and every crossed middle interval |
| end-proper locus | every proof-used end interval |
| covering degree | degree on each selected family, not global degree |
| itinerary partition | vertical/outgoing/lost/amplifying families and proof of exhaustion |
| omitted objects | proof they add no access, sheet, separator, or escaping path |
| output wave | support, crest, ends, width loss, and new cumulative time |
| error charge | absolute, relative, telescoping, or state-coordinate charge |

The cumulative time in the last row must remain below \(H_B(q)\). A certificate
that lists only the endpoint return and its degree is incomplete.

## 12. Source-text repair notes

The KKL Section 6 source has several local notation slips with a unique
contextual repair:

- line 1168 has `sny` for `any`;
- line 1170 writes \(\mathcal R f\) where the ambient object is \(F\);
- line 1492 displays the pre-push width where the immediately preceding
  Wave estimate is meant to control the pushed wave after buffer absorption;
- line 1605 refers to \(A_N\) although the constructed terminal indexed wave
  is \(A_{N-1}\);
- lines 1788--1789 use \(A^{\mathrm{outbr}}\),
  \(B^{\mathrm{outbr}}\), and \(n\), while the locally defined objects are
  \(A^{\mathrm{out}}\), \(B^{\mathrm{out}}\), and the fast-forward time \(N\).

These are transcription defects, not virtual transfer theorems. The intended
objects are determined by the adjacent definitions. The entropy-to-no-periodic-
interval step at line 1331 is different: it is a real structural implication
of the complete Hubbard-tree setting and must be promoted to an explicit
virtual hypothesis or lemma as explained in Section 5.6.

## 13. Proposed ledger changes

No ledger file is modified by this note. The following changes are proposed.

### 13.1 Open source-stated node

Add:

`KKL_PARABOLIC_WAVE_AMPLIFICATION` (`open`)

> KKL state that, in the full parabolically \(B\)-bounded, prime
> primitively renormalizable \(\psi\)-ql category, sufficiently wide
> controllable waves and HTND imply arbitrary amplification.  Project
> certification requires both the bounded-visits interval-growth repair and
> the stationary proper-path/degree-two repair.

Evidence:
`virtual_long_iterate_wave.md#3-exact-source-theorem`.

### 13.2 Internal proved reduction

Add:

`FINITE_HORIZON_KKL_WAVE_REDUCTION` (`proved`)

> A wave-admissible virtual KKL realization through the safe horizon
> \(H_w(B,L,q)\), with the marked selected-fan certificate, admits a selector
> \(P_w(B,L)\ge L\) and explicit thresholds \(Q_w(B,L),A_w(B,L)\) satisfying
> the conditional implication
> \(\operatorname{Wave}_{P_w}\Rightarrow\operatorname{Amp}_L\) of
> Theorem 8.2.

The KKL Wave statement belongs in the reduction's explicit hypotheses, not
its proved dependencies.  Proved dependencies include finite-horizon
truncation, stage forward closure, relative-cover lifting, and the local
transport calculus.

Evidence:
`virtual_long_iterate_wave.md#8-the-minimal-conditional-theorem`.

### 13.3 Split the open realization

Refine `H2_VIRTUAL_LONG_ITERATE_WAVE` into, or make it depend on:

1. `H2_VIRTUAL_MARKED_INTERVAL_ACTION`;
2. `H2_VIRTUAL_CRITICAL_LIMB_ALIGNMENT`;
3. `H2_VIRTUAL_FAST_FORWARD_FAN`;
4. `H2_VIRTUAL_WAVE_CHART_TRANSFER`.

The existing node should also depend explicitly on
`H1_ANALYTIC_ACCESS_REALIZATION` and the conditional finite-horizon reduction.
The phrase "controlled selected degree" should be replaced by "degree-one
central corridor plus bounded marked auxiliary fan", because Proposition 5.1
shows that a lone degree-two return is not sufficient.

## 14. Next proof target

The sharp next analytic target is the **Selected Marked Fast-Forward Fan
Lemma** of Section 9.3. Its first deliverable should be one fully drawn
virtual block, with:

1. the complete stagewise prime-end marking;
2. the exact long pullback surface;
3. every auxiliary terminal sheet and its degree;
4. a leaf-by-leaf proof of the four-way itinerary partition;
5. one \(q\)-independent extremal-width loss estimate.

If this cannot be constructed, the replacement invariant must retain a
wave germ together with its full access itinerary and bounded terminal fan;
a scalar hull width and a single endpoint return do not contain enough
information.

## 15. Attachment-support refinement

The subsequent source audit
`kkl_translation_no_birth_source_audit.md` sharpens the first and second
deliverables above.

KKL Proposition 6.5 says that the pullback of an ideal interval consists
exactly of its ordinary inverse image plus the ideal boundaries of components
of \(\mathcal T'\setminus\mathcal T\) attached there. Proposition 6.7 proves
that this excess is absent on KKL's central corridor because
\[
 \mathcal T'\cap\mathcal L_{[B,q-B-2]}
 =
 \mathcal T\cap\mathcal L_{[B,q-B-2]}.
\]
Combined with the endpoint-birth ledger, this proves that a virtual
realization needs empty attachment support in the degree-one interior and a
uniformly bounded endpoint contribution in the defect windows. Component
saturation, translation labels, and component count alone do not imply that
condition.
