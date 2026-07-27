# KKL virtual-occupancy source audit

## 1. Scope and verdict

This note audits exactly what can be transferred from Kahn--Kapiamba--Lyubich
(KKL), *MLC for parabolically bounded primitive renormalization*, to a
partially invariant virtual hull.

The conclusions are:

1. **Remark 4.14 supports only the Section 4 trichotomy, Proposition 3.7.**
   Inside the full KKL \(\psi\)-quadratic-like setting, the parabolically bounded
   hypothesis in that one proposition can be replaced by a uniform bound on the
   number of small filled Julia sets in each limb.
2. **The same replacement is not licensed for Proposition 3.8 or Proposition
   3.9.** Their proofs use the rotation-\(1/q\) translation model, control of
   images of components in the critical limb, full fiber-product iterates,
   properness on long strings of ideal intervals, controlled degree, and exact
   Hubbard-tree dynamics.
3. **A bound on selected virtual components is not yet the KKL occupancy
   hypothesis.** KKL converts component occupancy into a bound on ideal intervals
   by using the finite Hubbard tree. A virtual hull can have additional prime-end
   accesses, fjords, dams, branch vertices, or omitted components. The usable
   virtual hypothesis is therefore an access-complete bound on the induced limb
   marking (or a proved finite-tree reduction that implies it).
4. **`virtual_block_quotient.md`, Proposition 9.1 is directionally correct but
   not theorem-complete.** It omits the large-renormalization-width premise and
   can be misread as importing the tame and wave amplification propositions.
   Its two proposed virtual subproblems are also insufficient as written:
   "virtual occupancy" must be upgraded to access-complete marking control, and
   the partial-cover problem must be split into a static Section 4 transfer, a
   full-return tame transfer, and a long-iterate wave transfer.
5. **The narrow next target should be the Virtual Section-4 Trichotomy
   Interface, not the whole KKL branch-closing argument.** The exact target is
   stated in Section 9 below.

Nothing in this audit proves a virtual tame theorem, a virtual Wave Lemma, the
Master Transition Lemma, or MLC.

## 2. Source lock

Primary source:

- J. Kahn, A. Kapiamba, and M. Lyubich,
  [*MLC for parabolically bounded primitive renormalization*](https://arxiv.org/html/2606.27272),
  arXiv:2606.27272v1, 25 June 2026;
- [v1 source archive](https://export.arxiv.org/src/2606.27272).

The source archive was read in full rather than through the abstract. The relevant
source-file hashes are:

| file | SHA-256 |
|---|---|
| `waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| `not-all-good2.tex` | `B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01` |

Source locations used below:

| subject | source location |
|---|---|
| canonical renormalization and amplification definition | `waves-with-Misha.tex`, lines 478--492 |
| parabolically \(b\)-bounded definition | `waves-with-Misha.tex`, lines 661--667 |
| fixed-\(b\) convention and HTND | lines 698--715 |
| Propositions 3.7--3.9 | lines 722--739 |
| Section 4 trichotomy proof | lines 750--910 |
| Remark 4.14 | lines 907--911 |
| tame setup and translation markings | lines 913--1140 |
| wave setup and terminal-wave reduction | lines 1142--1228 |
| interval action and bounded visits | lines 1232--1342 |
| breakable-wave analysis | lines 1346--1677 |
| long-iterate critical visits | lines 1681--1797 |
| ideal-marking dynamics and Wave Lemma | lines 2126--2178 |
| Translation Marking Theorem | lines 2182--2234 |
| tame full-return and Value argument | `not-all-good2.tex`, lines 1--251 |
| tame localization and subsurface cover | lines 254--351 |
| typical-interval and Wanderers argument | lines 358--502 |
| immersion transport | lines 509--604 |

All constants in KKL Sections 4--6 are considered after \(b\) has been fixed.
Thus a constant called "universal" inside the wave section is uniform in \(q\),
the period, the map, and the controllability parameter where stated, but the
section-wide convention still permits dependence on \(b\).

## 3. Exact KKL ambient data

KKL does not start with a connected continuum and a partially defined return. It
starts with a periodically repelling, prime primitively renormalizable
\(\psi\)-quadratic-like map
\[
  F=(f,\iota):
  (\mathcal U',K')\rightrightarrows(\mathcal U,K_F).
\]
The setup supplies:

- compact connected full filled sets satisfying the two full-preimage identities
  in the definition of a \(\psi\)-ql map;
- fiber-product surfaces \(\mathcal U^n\), maps \(f^n\), and immersions
  \(\iota_n\);
- a full cycle \(\mathcal K=\{K_i\}_{i\in\mathbb Z/p\mathbb Z}\) of all small
  filled Julia sets;
- the finite Hubbard tree \(\mathcal T\), whose distinguished vertices include
  the components of \(\mathcal K\);
- the canonical ideal marking \(\mathcal I\) of
  \(\mathcal U\setminus\mathcal T\), induced by the sides of the tree;
- the canonical WAD on \(\mathcal U\setminus\mathcal K\);
- a canonical \(\psi\)-ql renormalization \(\mathcal R F\);
- a well-defined amplification statement
  \[
    \mathbb W(F)\ge M\mathbb W(\mathcal R F).
  \]

These are not cosmetic. They are the objects on which "tame", "controllable
wave", pullback, domination, Value, and amplification are defined.

There is a printed orientation inconsistency in the source. The controlling
definition at lines 491--492, the super-optimism statement at line 611, and the
proofs in Sections 4--6 use
\[
  \mathbb W(F)\ge M\mathbb W(\mathcal R F).
\]
Line 698 reverses this inequality while saying it is recalling the definition.
That isolated reversal is incompatible with the actual definition and with,
for example, the deductions at lines 784 and 1174. It is not used here.

KKL calls the renormalization parabolically \(b\)-bounded when:

1. the rotation number is \(1/q\);
2. every limb contains at most \(b\) components of \(\mathcal K\);
3. every component of \(\mathcal K\) in the critical limb is mapped into one of
   the limbs with index \(|j|\le b\).

Only Item 2 is used in Proposition 3.7. Items 1 and 3 return essentially
throughout the proofs of Propositions 3.8 and 3.9.

## 4. Proposition 3.7 and Remark 4.14

### 4.1 Exact source theorem

After \(b\) is fixed, KKL Proposition 3.7 says:

> For every \(M\ge1\), if \(\mathbb W(\mathcal R F)\) is sufficiently large
> depending on \(b\) and \(M\), then either \(F\) has \(M\)-amplification,
> \(\mathcal U\setminus\mathcal K\) is \(M\)-tame, or
> \(\mathcal U\setminus\mathcal T\) has \(M\)-wide controllable waves.

Remark 4.14 then states that the only part of parabolic boundedness used in this
proof is the bound \(b\) on the number of small filled Julia sets in each limb.
Accordingly, the following is a source-licensed restatement.

### Theorem 4.1 (KKL occupancy trichotomy; imported)

For every \(B,M\ge1\), there is \(A(B,M)<\infty\) such that the following
holds. Let \(F\) already be a periodically repelling, prime primitively
renormalizable \(\psi\)-ql map in the KKL category, with its full cycle
\(\mathcal K\), Hubbard tree \(\mathcal T\), canonical WAD, and canonical
renormalization. If every limb of \(K_F\) contains at most \(B\) components of
\(\mathcal K\), and
\[
  \mathbb W(\mathcal R F)\ge A(B,M),
\]
then at least one of the following occurs:

1. \(F\) has \(M\)-amplification;
2. \(\mathcal U\setminus\mathcal K\) is \(M\)-tame in KKL's definition;
3. \(\mathcal U\setminus\mathcal T\) has an \(M\)-wide controllable wave in
   KKL's definition.

No rotation-\(1/q\) or critical-limb image condition is required for this
particular implication.

### 4.2 What occupancy does inside the proof

The proof has two static splits.

1. **Flux split.** If some horizontal Hubbard arc has large flux, restricting
   the associated lamination from
   \(\mathcal U\setminus\mathcal K\) to
   \(\mathcal U\setminus\mathcal T\) produces either vertical width or a wide
   localized wave.
2. **Alignment split.** If the canonical WAD is not aligned with the Hubbard
   tree, leaves with many Hubbard-tree intersections produce many restrictions
   in \(\mathcal U\setminus\mathcal T\). Pigeonholing over ideal intervals again
   produces a wide localized wave unless there is amplification.

The occupancy bound enters through the following finite-tree estimate:
\[
  |\mathcal L_j|\le 6B,
\]
where \(\mathcal L_j\) is the multi-interval in the ideal marking corresponding
to the \(j\)-th limb. KKL proves this by taking the hull in the Hubbard tree of
the fixed point and the at most \(B\) small Julia components in that limb.
Every other vertex is a branch vertex of valence at least three. The elementary
tree count then bounds edges and sides. Consequently,
\[
  |\mathcal I|\le 6Bq\le 6Bp.
\]

The other inputs in Section 4 are:

- the canonical-WAD/renormalization-width comparison
  \[
    p\,\mathbb W(\mathcal R F)
    \le 4\|X\|+O(p);
  \]
- comparison of the widths of all \(p\) small-Julia boundaries with the
  renormalization width;
- the fact that a path intersecting the horizontal Hubbard diagram at least
  \(n\) times restricts to at least \(n/2\) paths in
  \(\mathcal U\setminus\mathcal T\);
- the canonical lamination and its restriction to the tree complement.

Thus Remark 4.14 does **not** say that a bare component count proves the
trichotomy on an arbitrary marked surface. It says that, once all KKL objects
and these general estimates exist, component occupancy is the only special
part of parabolic boundedness used in Section 4.

### 4.3 Stopping-time content of Proposition 3.7

Section 4 does not push a wave through \(F_*^n\), construct a translation
marking, or invoke the long-iterate Wave Lemma. In that sense it is static.

There is nevertheless one important provenance requirement. The
width comparison among all components of the \(p\)-cycle is a dynamical fact.
A finite-horizon virtual proof must either:

- contain the orbit segments needed to prove that comparison for every cycle
  component used in the sum; or
- take the comparison as a separately proved virtual input.

Therefore "the Section 4 proof has no long wave stopping time" must not be
misread as "partial invariance is irrelevant."

## 5. Proposition 3.8: the tame branch

### 5.1 Exact source theorem

For fixed \(b\), KKL Proposition 3.8 says:

> For every \(M\), if \(\mathcal U\setminus\mathcal K\) is \(M\)-tame and
> \(F\) is sufficiently high-type-near-degenerate relative to \(b,M\), then
> \(F\) has \(M\)-amplification.

HTND requires both \(q\) and \(\mathbb W(\mathcal R F)\) to be sufficiently
large. This is not a conclusion of tameness or occupancy.

### 5.2 Additional hypotheses actually used

The tame proof needs substantially more than per-limb occupancy.

#### T1. Exact translation region

KKL uses
\[
  U_{(b,q-b)}
\]
as a translation region. In the middle limbs the pullback tree agrees with the
original tree, and \(f\) moves the relevant tree pieces homeomorphically by one
limb. This supplies:

- a unique lift \(F^*\alpha\) of an arc while it remains in the corridor;
- translation classes of arcs;
- inner and outer translation markings;
- exact cyclic order and a bounded shift parameter.

The proof of the inner marking explicitly uses
\[
  \mathcal T'_j=\mathcal T_j
  \quad\text{for }b\le j<q-b-1.
\]
That assertion depends on the parabolically \(b\)-bounded placement of the
critical defect, including the critical-limb image condition. Occupancy alone
does not imply it.

#### T2. Rotation-\(1/q\) indexing

The source uses the literal shift
\[
  \mathcal L_j\longmapsto\mathcal L_{j+1}
\]
and a single corridor of length comparable with \(q\). This is where the
rotation-\(1/q\) part of the source model enters. A virtual continued-fraction
block would have to prove its own accelerated bounded-shift model; it cannot
cite this indexing as automatic.

#### T3. Translation Marking Theorem with its topology term

For an \((n,r)\)-translation marking with
\[
  N=2(n+1)r,
\]
KKL proves
\[
  \|W^{\mathrm{long}}\|
  \le 2W_{\mathrm{std}}+6N.
\]
The cardinality \(N\) is allowed to grow with the corridor. Hence the source
gives a relative estimate after HTND absorption; it gives no
period-independent \(O(1)\) error.

#### T4. Full Hubbard return and Value

KKL sets
\[
  G=(g,\jmath)=(f^p,\iota_p)
\]
for the full small-Julia cycle period \(p\). The contradiction uses:

- the Hubbard transition \(T_F\);
- its left and right Perron weights;
- a Value functional expanded by \(F\);
- strict entropy over the full return;
- comparability of Perron coordinates throughout the translation region.

The per-limb occupancy bound gives \(p\le bq\), but does not itself construct
the full return or its eigenvectors.

#### T5. Bounded-return and literal-clone structure

In `not-all-good2.tex`, Lemma `get-around` uses both the at-most-\(b\)
critical-limb components and their bounded landing near the critical limb to
obtain a return depth \(N(b)\). The proof then identifies the long-\(q\)
Hubbard trees as literal clones of finitely many base trees.

There is a source-lock caveat. KKL Appendix C contains the printed clone
eigen-equation already refuted in this project. The corrected negative-weight
clone theorem in `corrected_clone_theorem_derivation.md` repairs the finite
graph algebra. It does **not** construct the literal virtual clone or discharge
any analytic hypothesis listed here.

#### T6. Full-return localization

Because the global full return \(g=f^p\) has uncontrolled degree, KKL:

1. selects an interval \(I\) in the translation region;
2. takes a particular component \(\widehat U_I\) of \(g^{-1}(U_I)\);
3. passes to subsurface covers and localizations \(V_I,\widehat V_I\);
4. proves the selected degree is bounded by \(2^m\), where \(m\) is the
   number of small Julia components in \(U_I\);
5. lifts the full-return immersion to the localized covers;
6. proves properness at the distinguished filled-set ends.

These are full-cover and full-return statements. Fullness of a virtual hull or
existence of a prime-end circle alone does not imply them.

#### T7. Canonical domination and Wanderers

On the localized covers, KKL uses canonical-WAD domination under \(g^*\).
The bad part of the domination witness is controlled first for bounded
concatenation length and then, for its tail, by the Wanderers Theorem:
\[
  \|\widehat X^{gb}_{\ge m}\|
  \le \frac4m\|X_I\|.
\]
Every arc in that witness and every ordered concatenation must exist on the
selected full-return cover. A quotient that retains only an endpoint label does
not provide this data.

#### T8. Immersion transport

KKL finally pushes the localized WAD through an immersion that is proper and
degree one at designated ends. This end-properness is what separates genuine
lifts from escaping arcs. A topological correspondence on a hull does not
automatically satisfy it.

### 5.3 Tame stopping-time audit

The decisive stopping time is the full period \(p\):

- \(g=f^p\) is used in Value;
- \(g^{-1}(U_I)\) is used to select \(\widehat U_I\);
- \(\iota_p\) is lifted to the localized covers;
- the degree proof factors through every intermediate stage
  \(0,\ldots,p\);
- Wanderers is applied to the pullback by this full return.

Since \(p\le bq\), this is finite for fixed \(b,q\), but it is not bounded
independently of the corridor length. A virtual partial cover must therefore
realize all relevant stage maps through the full return, or prove a different
accelerated return theorem with the same localization, degree, domination, and
Value properties.

Retaining only the critical orbit through a first return is not sufficient if
the selected cover omits:

- an intermediate small Julia component used to count critical degree;
- an end used in the WAD domination witness;
- an immersion branch needed for end-properness; or
- a Hubbard-tree edge used by Value.

## 6. Proposition 3.9: the wave branch

### 6.1 Exact source statement and certification boundary

For fixed \(b\), KKL Proposition 3.9 says:

> For every \(M\), there is \(N=N(b,M)\) such that if
> \(\mathcal U\setminus\mathcal T\) has \(N\)-wide controllable waves and
> \(F\) is sufficiently HTND relative to \(b,M\), then \(F\) has
> \(M\)-amplification.

The conclusion comes from a terminal-wave lemma: a sufficiently wide
controllable wave yields either definite vertical width or a definitely wider
controllable wave.

This records what KKL state; it does not certify the v1 proof.  The project
has since isolated an unproved strict interval-growth step in bounded visits
and an unproved stationary proper-path/measurable-lamination extraction,
along with a false printed degree-one clause corrected to degree two.
Accordingly `KKL_PARABOLIC_WAVE_AMPLIFICATION` remains open pending
`KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR` and
`KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR`.

### 6.2 Additional hypotheses actually used

#### W1. Exact action on ideal markings

KKL defines
\[
  F_*=f_*\iota^*
\]
only after proving that \(f^*\mathcal I\) refines
\(\iota^*\mathcal I\). The proof uses the exact description of pullbacks of
tree-side intervals and identifies the pullback Hubbard tree with a subset near
the filled Julia set.

A partially invariant hull must prove, not assume:

- that every pulled interval is defined;
- pairwise disjointness of pulled intervals;
- the refinement relation;
- correct cyclic order;
- compatibility under composition.

#### W2. Proper and end-proper middle dynamics

KKL proves that \(F_*\) is proper on
\[
  \mathcal L_{[b,q-b-2]}.
\]
The proof uses the fact that every component of \(F^{-1}(\mathcal K)\) in the
middle limbs is already a component of \(\mathcal K\). This is a
parabolically bounded defect-location statement, not a consequence of
occupancy.

The proper interval yields:

- a unique stretching multi-interval of length at most two;
- uniformly bounded images for all other intervals;
- control of breakable and unbreakable waves;
- a genuine shift region.

#### W3. Exact interval dynamics and entropy

The bounded-critical-visits lemma uses:

- \(F_*\mathcal L_j=\mathcal L_{j+1}\) away from the critical limb;
- \(F_*\mathcal L_0=\partial_{\mathrm C}\mathcal T\);
- exact growth of multi-intervals under returns to the critical limb;
- \(\lambda_F>1\) to rule out periodic repetition of an interval.

Counting active virtual components supplies none of these statements.

#### W4. Full pullback surfaces for large iterates

For every \(n\), KKL uses
\[
  \mathcal U^n=f^{-n}(\mathcal U),\qquad
  \mathcal T^n=f^{-n}(\mathcal T),\qquad
  (f^n,\iota_n),
\]
with
\[
  f_*^n\iota_n^*I=F_*^nI.
\]
The pair must act combinatorially on the marking. This is stronger than
knowing the image of the crest as a set.

#### W5. Controlled degree along fast forward

In the critical-visit proof, for a wave whose crest lies near limb \(j\), KKL
sets
\[
  n=q-b-j-2.
\]
On the selected pullback interval, \(f_*^n\) has a prescribed degree-one
region and degree \(2^m\) on the first \(m\) postcritical pieces. After fixing
a bounded \(m\), the wave pushforward error is controlled by
\[
  O(1+\log d).
\]

If a virtual construction uses the global degree-\(2^n\) polynomial iterate
instead of the selected component/fiber-product action, this error is
\(O(n)\) and the source argument does not transfer.

#### W6. Itinerary completeness

The fast-forward decomposition partitions every leaf into vertical,
outgoing, lost, or amplifying pieces. The assertion that these pieces exhaust
the wave uses KKL's itinerary proposition together with properness on the
crest and end-properness on every limb crossed. Every such restriction must
remain present in a virtual partial cover.

#### W7. Nested critical-limb pullbacks

The proof that a long unbreakable wave entering the critical limb has bounded
width uses nested pullbacks
\[
  \mathcal L_0^0,\mathcal L_0^1,\ldots,\mathcal L_0^{b+2}
\]
and the corresponding components of \(\mathcal K^n\). Occupancy shows that
after at most \(b\) nested critical-limb pulls the selected inner limb is
disjoint from \(\mathcal T\). The proof then needs a degree-one pushforward of
a lamination connecting one component of \(\mathcal K^n\) to the others.

This is occupancy plus a valid full pullback model, not occupancy alone.

### 6.3 Wave stopping-time audit

There are three different time scales.

1. **Bounded local breaking time.** Several arguments use a number of iterates
   depending only on \(b\); one explicit critical-limb depth is \(b+3\).
2. **One long fast-forward.** The critical-visit proof uses
   \(q-b-j-2\) iterates and then a bounded number of further iterates to return
   the crest to the critical limb. This is one limb circuit, hence
   \(O_b(q)\), not \(O(1)\).
3. **A bounded number of critical visits.** KKL takes
   \(216b^2\) as a bound on a chain of critical visits. Concatenating the
   constructed visits can therefore require \(O_b(q)\) total original
   iterates; a safe audit budget must retain the explicit \(216b^2\)
   visit-count factor.

The source does not state a generic "stop at the first return" rule. It
constructs the needed times from the exact interval dynamics and then uses all
fiber-product maps and markings through those times.

A valid virtual stopping certificate must list, for every wave used:

- its crest and ends;
- the chosen iterate \(n\);
- all stagewise pullback surfaces through \(n\);
- every proper or end-proper interval crossed;
- the degree on the selected component;
- the full itinerary decomposition of every retained leaf family;
- the components of \(\mathcal K^n\) used in the terminal estimate.

## 7. Assessment of `virtual_block_quotient.md`, Proposition 9.1

The present proposition says, in compressed form, that a full KKL object with
at most \(B\) small Julia sets in each limb receives the KKL
tame/amplification/wave trichotomy.

### 7.1 What is correct

- It correctly confines the statement to an object that already satisfies
  KKL's periodically repelling, primitively renormalizable \(\psi\)-ql
  definitions.
- It correctly identifies Remark 4.14 as allowing the Section 4 proof to use
  limb occupancy in place of the full parabolically bounded hypothesis.
- It correctly warns that a connected partially invariant virtual hull is not
  yet such an object.

### 7.2 What is overstated or underspecified

1. **Missing width premise.** Proposition 3.7 is conditional on
   \(\mathbb W(\mathcal R F)\) being sufficiently large depending on \(B,M\).
   It is not an unconditional trichotomy at every width.
2. **Ambiguous branch scope.** The phrase "tame/amplification/wave
   trichotomy applies" is accurate only for Proposition 3.7. It must not be
   read as saying that the tame branch amplifies by Proposition 3.8 or the
   wave branch amplifies by Proposition 3.9 under occupancy alone.
3. **Constants depend on two inputs.** For each requested factor \(M\), the
   threshold depends on both \(B\) and \(M\), not merely on \(B\).
4. **Virtual occupancy is too weakly phrased.** Bounding "active hull
   components" does not imply KKL's bound on ideal intervals unless an
   access-complete finite-tree carrier has first been constructed.
5. **The partial-cover gate is not one theorem.** Section 4, the tame
   full-return proof, and the wave long-iterate proof use different amounts of
   invariance and must be audited separately.

Accordingly, Proposition 9.1 should be treated as a correct informal pointer
to Theorem 4.1 above, not as a source-complete virtual transfer theorem.

## 8. Explicit no-go boundaries

The following inferences are not justified by KKL.

### No-go 8.1: selected occupancy implies bounded marking

A virtual hull may retain one selected continuum in each limb while its
boundary has many dynamically distinct prime-end accesses. It may also acquire
many accesses from pseudo-Siegel fjords and dams. The component count is then
bounded while the ideal marking is not.

KKL avoids this because its marking comes from the sides of a finite Hubbard
tree and its tree-counting lemma bounds those sides. The analogous virtual
tree/access theorem is an additional obligation.

### No-go 8.2: fullness implies KKL combinatorial action

A full hull gives a simply connected complement and a prime-end circle. It
does not imply
\[
  f^*\mathcal I\ \text{refines}\ \iota^*\mathcal I,
\]
nor properness or end-properness on the intervals used by a wave.

### No-go 8.3: a topological shift implies a translation marking

A topological circle homeomorphism on selected accesses does not provide the
holomorphic lifts, boundary homeomorphisms, standard-width estimate, or exact
defect region in KKL's Translation Marking Theorem.

### No-go 8.4: one proper return supplies all intermediate wave maps

A proper return between endpoint hulls does not automatically construct
\((f^n,\iota_n)\), pulled trees, pulled ideal markings, or the degree profile
at intermediate times. The wave proof uses all of them.

### No-go 8.5: global polynomial degree can replace selected degree

Using \(f^n\) globally gives degree \(2^n\). KKL's wave pushforward loss is
\(O(1+\log d)\); with global degree this becomes \(O(n)\). The selected
component and fiber-product degree control are essential.

### No-go 8.6: occupancy closes the tame branch

The tame branch additionally needs a literal bounded-defect translation
corridor, a full Hubbard return, localized WAD domination, Wanderers, Value,
and controlled Perron weights. Even the corrected clone theorem addresses only
the finite-matrix part of this list.

### No-go 8.7: occupancy closes the wave branch

The wave branch additionally needs exact interval dynamics through long
iterates, properness, end-properness, controlled degree, itinerary
completeness, and nested critical-limb pullbacks.

### No-go 8.8: KKL constants are uniform in occupancy

KKL fixes \(B\), and constants may depend on it. The source does not give
uniform constants as \(B\to\infty\). A unified virtual theorem must prove a
universal virtual occupancy/access bound or introduce a new calibration that
absorbs its growth.

## 9. Narrow replacement theorem target

The next target should isolate exactly the static content of Section 4.

### Virtual Section-4 Trichotomy Interface (`OPEN`)

For every \(B,M\ge1\), there is \(A(B,M)<\infty\) with the following
property.

Let a finite-horizon virtual block provide:

1. **Two marked complements.**
   Hyperbolic finite-type surfaces
   \[
     V_{\mathcal K}\supset V_{\mathcal T}
   \]
   playing the roles of
   \(\mathcal U\setminus\mathcal K\) and
   \(\mathcal U\setminus\mathcal T\), with a canonical or uniformly comparable
   lamination/WAD \(X\) on \(V_{\mathcal K}\).
2. **An access-complete tree carrier.**
   A finite tree or tree-like carrier \(\mathcal T^v\) whose sides induce the
   entire ideal marking used by restriction, flux, and waves. No omitted hull
   component or prime-end access may create an additional relevant interval.
3. **Virtual limb marking bound.**
   For every limb \(j\),
   \[
     |\mathcal L_j^v|\le C_0B,
   \]
   and consequently
   \[
     |\mathcal I^v|\le C_0Bq.
   \]
   If this is deduced from component occupancy, the virtual analogue of KKL's
   finite-tree side-counting lemma must be proved.
4. **Width/WAD comparison.**
   For the virtual successor width \(D_{\mathrm{ret}}\) and cycle length \(p\),
   \[
     pD_{\mathrm{ret}}\le C_1\|X\|+C_2p,
   \]
   together with uniform comparison of the boundary widths of every component
   included in that cycle.
5. **Restriction multiplicity.**
   A path with at least \(n\) intersections with the horizontal carrier
   restricts to at least \(c_0n\) paths in \(V_{\mathcal T}\), with universal
   \(c_0>0\).
6. **Faithful flux and wave decomposition.**
   Every restricted leaf used in the flux or alignment split is represented
   in the ideal marking, and the extremal-width inequalities used to extract a
   localized wave remain valid with uniform constants.
7. **Amplification interface.**
   The inequality defining absence of \(M\)-amplification controls
   \(\mathbb W(V_{\mathcal T})\) by \(M D_{\mathrm{ret}}\), in the same
   direction as in KKL.

If
\[
  D_{\mathrm{ret}}\ge A(B,M),
\]
then either:

1. the virtual block has \(M\)-amplification;
2. its WAD is \(M\)-tame relative to the carrier; or
3. its tree complement has an \(M\)-wide access-complete controllable wave.

### Why this is the correct narrow target

- It captures exactly the proof interface of KKL Section 4.
- It requires no translation corridor, full-return Value argument, or
  long-iterate Wave Lemma.
- It replaces the unsafe phrase "at most \(B\) active components" by the
  quantity actually used in the proof: bounded, access-complete limb marking.
- It makes the large-width threshold explicit.
- It leaves the tame and wave branch-closing theorems as separate obligations
  with their correct stopping horizons.

Once this interface is established, the subsequent targets should remain
separate:

1. **Virtual Tame Full-Return Lemma:** construct the selected full return,
   localization, literal/controlled corridor graph, WAD domination,
   Wanderers tail estimate, and corrected Value contraction through time
   \(p\).
2. **Virtual Long-Iterate Wave Lemma:** construct compatible marked
   fiber-product pullbacks, proper/end-proper interval action, controlled
   degree, and itinerary-complete wave transport through the \(O_B(q)\)
   stopping horizon.

Combining all three into one "partial-cover trichotomy" would hide the exact
place where invariance, degree, or stopping-time control can fail.

## 10. Adversarial validation checklist

Before any virtual invocation of KKL Proposition 3.7, answer:

1. Does the marking include every prime-end access that can receive a
   restricted canonical leaf?
2. Is the number of intervals per limb bounded, not merely the number of
   selected continua?
3. Is the virtual carrier a finite tree with the same valence accounting as
   KKL, or is a replacement side-count theorem proved?
4. Is the width/WAD comparison proved for all retained cycle components?
5. Are additive \(O(p)\) errors absorbed only after the large-width premise is
   checked?
6. Are "tame" and "controllable wave" defined on the actual virtual marked
   surfaces, rather than borrowed by analogy?

Before the tame branch, additionally answer:

1. What is the exact translation region and defect set?
2. Which theorem gives the bounded shift and the two translation markings?
3. Where is the full return \(G=(f^p,\iota_p)\) constructed?
4. Which selected component has bounded degree, and why?
5. Does every WAD domination concatenation survive the virtual quotient?
6. Is the Wanderers theorem applicable on the localized cover?
7. Is the corrected clone theorem applied to a literal or quantitatively
   controlled graph realization?
8. Are all errors relative/amortized rather than incorrectly declared \(O(1)\)?

Before the wave branch, additionally answer:

1. Does \(f^*\mathcal I\) refine \(\iota^*\mathcal I\) at every stage?
2. Which intervals are proper and end-proper?
3. Is there exactly one bounded stretching defect?
4. What is the selected degree of each fast-forward map?
5. Are all four fast-forward leaf classes exhaustive?
6. What is the cumulative stopping horizon for the critical-visit chain?
7. Does the marking retain every component of \(\mathcal K^n\) used in the
   nested critical-limb argument?
8. Is entropy invoked only after the virtual interval action has been shown to
   be the relevant Hubbard action?

Any unanswered item blocks the corresponding transfer. It is not a harmless
normalization choice.
