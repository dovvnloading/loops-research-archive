# Research Push VIII assessment: a finite label enumerator survives; the marked analytic interface does not

## 1. Decision

Research Push VIII does not prove
`FIXED_HORIZON_MARKED_BINARY_INTERFACE_COMPLETION`.
Its headline theorem depends on an immersion-pullback formula that is not
derived from the KKL definition, an incorrect implementation of
end-properness, an ill-typed welding composition law, and final-root
hypotheses that do not exclude new sheets or new pullback components.

The bundle nevertheless contains one useful finite diagnostic and one useful
design rule:

1. after the deletion-and-seed hull has been declared as part of an abstract
   finite label model, the interval-convex closure and exhaustive coarsening
   algorithm solve that finite model exactly; and
2. a response or access subdivision must not be used as a KKL action endpoint
   unless the actual covering/immersion marking criterion has been proved.

The first item is promoted only in the deliberately narrowed form
`FINITE_LINEAR_LABEL_MARKING_ENUMERATOR`.  The second is retained as a
no-laundering rule in the research documentation.  We also record the exact
pull-push composition obstruction as
`PULL_PUSH_WELDING_WORD_COMPOSITION_NO_GO`.

No proposed Push-VIII analytic node is promoted as written.  In particular,
the following remain open:

```text
DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE
DIRECT_DECORATION_TRACE_COLLAR_REALIZATION
DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS
END_PLUMBING_TRACE_RESPONSE_CONTROL
VIRTUAL_WAVE_MARKED_CORRESPONDENCE
VIRTUAL_WAVE_HORIZON_CERTIFICATE
H2_RESPONSE_REALIZATION
MBTT
UNIVERSAL_PROTECTED_TOWER_CLOSURE
MLC
```

VAAPC-I is likewise not established.

## 2. Chain of custody and reproduction

The audited bundle is

```text
research/mlc_research_push_8_bundle
```

and contains eighteen files, including the manifest itself.  The manifest
lists seventeen payload files.  Before executing any generator, all
seventeen SHA-256 values matched `SHA256SUMS_PUSH8.txt`.

The supplied computations reproduce:

```text
finite compiler trials                 1500
reported compiled systems              1221
reported obstructions                   279
reported oracle mismatches                0

matrix audit trials                    1000
reported exact assertion failures         0
```

Running the two scripts on Windows changes the two generated JSON reports
from LF to CRLF.  Their normalized-LF SHA-256 values still equal the
manifest values:

```text
marked_interface_test_report.json
  A677236B658053284318B0F64191F5CF70DF12374493DD9CC8A7BF31D18F97B0

welding_naturality_report.json
  F15EBCCB947ABDA329EC08F4090E43F22F0EB5837F43EBE65E0E66028C1AC5B8
```

The test file is an executable test driver, not a `unittest` test case:
`python -m unittest` discovers zero tests, while direct execution runs the
claimed randomized comparison.

An additional exhaustive audit of the finite predicate checked 4,150 small
systems:

```text
N=2, m=2       54 systems
N=3, m=3     4096 systems
total        4150 systems
```

There were no discrepancies between exhaustive endpoint enumeration and the
submitted finite predicate.  This validates the enumerator relative to its
own declared hull rule.  It does not validate that the hull rule equals a KKL
immersion pullback.

## 3. Source lock

### 3.1 Kahn-Lyubich direct-decoration and pseudo-piece sources

The source lock retained from the Push-VII audit is Kahn and Lyubich,
*A priori bounds for some infinitely renormalizable quadratics. II.
Decorations*, arXiv:math/0609046.

The audited `kingdom.tex` has SHA-256

```text
5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7
```

and supplies the two actual univalent \(f^q\) direct-decoration branches and
their finite binary iterates.  The audited `psiql.tex` supplies:

- the pseudo-piece path-space/universal-cover construction;
- the covering induced by a puzzle covering;
- the immersion induced by a puzzle inclusion;
- the finite ideal-boundary arc decomposition; and
- continuous extension of the immersion, with the explicit warning that the
  image of an ideal-boundary point need not lie in the target ideal boundary.

It does not supply an ideal-arc Sobolev trace theory or the Push-VIII finite
deletion-and-seed formula.

### 3.2 KKL ideal markings and immersion pullbacks

The relevant primary source is Kahn, Kapiamba, and Lyubich,
*MLC for parabolically bounded primitive renormalization*,
arXiv:2606.27272v1, Appendix A.

Its definitions have the following order:

1. an ideal marking is a dense tiling of the ideal boundary by pairwise
   disjoint connected open intervals;
2. subordination of a proper path is a homotopy-in-every-neighborhood
   condition in the ideal closure;
3. a covering pulls an ideal marking back by its boundary covering;
4. for an immersion \(\iota:V'\to V\), the pullback
   \(\iota^*X\) is the maximal source ideal set satisfying a condition
   quantified over proper target paths and their unique proper lifted
   components; and
5. \(F=(f,\iota)\) acts only if \(f^*\mathcal I\) refines the already-defined
   partial marking \(\iota^*\mathcal I\).

KKL define end-properness on the **end intervals of the multi-interval in
\(f^*\mathcal I\)**.  They do not define it by testing the first and last
micro-atoms of an auxiliary subdivision.

In KKL's native Hubbard-tree application, a component formula for
\(\iota^*I\) is proved using the actual inclusion, the components of
\(\mathcal T'\setminus\mathcal T\), and a component-exhaustion argument.
That proof is additional geometry.  It is not a consequence of a string of
proper/nonproper labels.

## 4. The submitted immersion-pullback formula is not proved

Push VIII records each source micro-atom by

\[
  r(j)\in\{0,\ldots,N-1\}\cup\{\bot\},
\]

where \(r(j)=\bot\) means only that the immersion is nonproper there.  It then
defines a deletion-and-seed hull \(H_\iota(B)\) and asserts

\[
  \iota^*B=H_\iota(B).
\tag{4.1}
\]

The table contains none of the following data used by the KKL definition:

- the proper target path;
- the components of its inverse image;
- uniqueness of the selected proper lift;
- the induced relative-cover or fundamental-group subgroup;
- the homotopy class used in subordination;
- ambient components attached to the source ideal interval; or
- a component-exhaustion theorem.

There is also a quantifier-direction error in the proof.  KKL asks whether
proper **target** paths with unique proper source lifts subordinate to a
candidate source set must themselves be subordinate to \(B\).  Push VIII
instead starts with a source path subordinate to a retained label component
and asserts that its immersed image is subordinate to \(B\).  The latter is
not the defining implication and does not establish maximality.

The label \(\bot\) is especially insufficient.  Two immersion collars can
have identical proper/nonproper boundary labels while their nonproper images
route through different target interior homotopy classes.  KKL pullback can
therefore differ while the submitted table is unchanged.

Consequently Theorem 5.1 is not a theorem about the actual KKL pullback.
It becomes true only if (4.1), or equivalent definition-level path-lift data,
is supplied as an additional hypothesis.

## 5. The finite theorem that survives

We now separate the finite combinatorics from the missing analytic
realization.

### Definition 5.1 (linear label-hull model)

Let the target consist of ordered micro-atoms
\(M_0,\ldots,M_{N-1}\), and let the source be the ordered string
\(A_0,\ldots,A_{m-1}\).  Give every source atom a label

\[
  r_j\in\{0,\ldots,N-1\}\cup\{\bot\}.
\]

For a contiguous target block \(B\), define \(H(B)\), by definition, as
follows:

1. delete every \(A_j\) with \(r_j\notin B\cup\{\bot\}\);
2. take the connected components of the remaining source string; and
3. retain precisely the components containing some \(A_j\) with
   \(r_j\in B\).

Separately give the source vertices a map

\[
  e:\{0,\ldots,m\}\longrightarrow\{0,\ldots,N\}.
\]

For this abstract model, call a target endpoint partition admissible when
the hulls of distinct target blocks are disjoint and the two endpoint
vertices of every retained hull component have \(e\)-images among the
target endpoints.

### Theorem 5.2 (finite linear-label marking enumerator)

In Definition 5.1:

1. a maximal \(\bot\)-run flanked by proper labels \(p,q\) belongs to two
   distinct hulls exactly when \(p,q\) lie in distinct target blocks;
2. the interval-convex transitive closure of all such pairs is the unique
   finest partition with pairwise disjoint label hulls;
3. every hull-disjoint target partition is a coarsening of that partition;
4. among its finitely many coarsenings, the endpoint condition is decided by
   checking \(e(v_-),e(v_+)\) for every hull component; and
5. exhaustive enumeration returns a maximum-cardinality admissible
   coarsening or a finite obstruction.

#### Proof

Let \(R\) be a maximal \(\bot\)-run with adjacent proper labels \(p,q\).
If \(p\) and \(q\) belong to different blocks, deleting labels outside the
first block leaves \(R\) joined to the \(p\)-seed, while deleting labels
outside the second leaves the same \(R\) joined to the \(q\)-seed.  Thus the
two hulls overlap on \(R\).

If \(p,q\) belong to one block, \(R\) is retained only by that block.  A run
with only one proper neighbor is likewise retained by at most the neighbor's
block.  Proper atoms assigned to other blocks separate all remaining source
components.  Hence merging the adjacent labels of every two-sided
\(\bot\)-run is necessary and sufficient for hull disjointness.

Target blocks are contiguous, so a block containing \(p\) and \(q\) contains
every micro-atom between them.  Taking the interval-convex transitive closure
therefore gives the unique finest hull-disjoint partition, and every other
one is its coarsening.

By the definition of the finite endpoint predicate, a finer source endpoint
partition refines a retained hull component exactly when both of its boundary
vertices map to target endpoints.  There are finitely many coarsenings, so
enumeration decides the predicate and a maximum-cardinality valid result
exists whenever the valid set is nonempty. \(\square\)

### Scope

Theorem 5.2 does not assert that \(H(B)=\iota^*B\), that \(e\) is the
boundary map of a covering, or that any label string is analytically
realizable.  It does not certify KKL properness, end-properness, collars,
trace maps, welding, word composition, or enlargement.

## 6. The submitted fixtures do not instantiate their stated model

Section 4 of Push VIII requires every source atom with covering label
\(c(j)=k\) to map homeomorphically to \(M_k\).  Its two covering endpoint
images must therefore be the two distinct endpoints \(k,k+1\), in one of
the two orientations.

The advertised successful fixture violates this at four atoms:

| source atom | covering label | supplied endpoint images | required set |
|---:|---:|---:|---:|
| 0 | 0 | \((0,0)\) | \(\{0,1\}\) |
| 3 | 2 | \((2,2)\) | \(\{2,3\}\) |
| 6 | 4 | \((4,4)\) | \(\{4,5\}\) |
| 9 | 6 | \((6,6)\) | \(\{6,7\}\) |

Such atoms are not homeomorphisms onto the declared open target atoms.
The fixture has twelve source atoms and eight target atoms with repeated
full-atom covering labels, which is also incompatible with the stated
degree-one boundary covering.

The randomized generator chooses covering atom labels and vertex images
independently.  Exact counts are:

```text
random systems                                 1500
systems satisfying atomwise endpoint consistency  1
systems violating it                          1499
accepted systems                              1221
accepted but atomwise inconsistent            1220
```

Requiring one coherent global orientation and the bijectivity expected from
a degree-one boundary homeomorphism leaves zero realized candidates in the
submitted population.

The compiler's `validate` method only range-checks the two representations.
It does not check their compatibility.  Indeed, arbitrarily changing every
`cov_micro` value in the success fixture leaves every decision field
unchanged; `cov_micro` is used only in the reported incidence vector.

The reported zero oracle mismatches therefore concern almost entirely
nonrealizable label tables.

## 7. The oracle does not validate the disputed geometry

`brute_force_valid_markings` independently enumerates endpoint subsets, but
it repeats:

- the same deletion-and-seed hull;
- the same boundary-vertex endpoint predicate;
- the same linear seam convention; and
- the same micro-atom interpretation.

It is independent of the optimized coarsening enumeration, not independent
of the mathematical model.  The test establishes:

> the optimized enumerator solves the declared finite label predicate.

It does not establish:

> the declared finite label predicate computes KKL immersion pullbacks on an
> actual direct-decoration pseudo-piece.

This distinction is the reason Theorem 5.2 is retained while the proposed
source-facing nodes are rejected.

## 8. The end-proper classifier is false

The compiler sets

```python
end_proper =
    first_micro_atom_is_proper and last_micro_atom_is_proper
```

for a retained hull component.  KKL instead require the immersion to be
proper on the whole end intervals of the corresponding multi-interval in
\(f^*\mathcal I\).

Consider the following covering-coherent finite table:

\[
\begin{aligned}
N&=5,\\
c&=(0,1,2,3,4),\\
c_\partial&=(0,1,2,3,4,5),\\
r&=(0,\bot,2,3,4),
\end{aligned}
\]

with mandatory target endpoints \(\{0,3,5\}\).  The compiler selects
\(\{0,3,4,5\}\).  The pullback over the target block \([0,3]\) is the source
string \([A_0,A_1,A_2]\).  It is one whole interval of the covering marking
\(f^*\mathcal I\), hence it is itself the relevant KKL end interval.  The
middle atom \(A_1\) is nonproper, so the immersion is not proper on that end
interval.

Nevertheless, the compiler reports

```text
proper       false
end_proper   true
```

because only \(A_0\) and \(A_2\) are inspected.  This is an exact
counterexample to the submitted end-proper classification.

The randomized run also demonstrates vacuity:

```text
accepted systems                                  1221
accepted with no immersion component                28
accepted with no proper or end-proper component     402
```

Compiler success therefore does not imply that any proof-used trace welding
is defined.

## 9. The fixed-horizon theorem fails even inside a coherent finite table

Take

\[
  r=(\bot,1,\bot),\qquad
  c=(0,1,2),\qquad
  c_\partial=(0,1,2,3),
\tag{9.1}
\]

and make all four target vertices mandatory.  This satisfies the stated
atomwise covering consistency.  The compiler returns `compiled`; its only
nonempty hull has source boundary images \(0,3\), so the endpoint criterion
passes.  But the output itself records

```text
proper       false
end_proper   false
```

for that component.

The submitted welding theorem is defined only for proper or end-proper
components.  Theorem 24.1 assumes only that every mandatory endpoint passes
the compiler or has a slit certificate, then concludes that the complete
horizon has actual welding operators.  Example (9.1) satisfies the explicit
compiler premise but has no welding on its sole nonempty component.

Thus Theorem 24.1 is false with its stated premises even before confronting
the actual KKL realization problem.  A correct assembly theorem must require
an independent certificate that every proof-used component is proper or
end-proper in the KKL sense and carries the required actual collar maps.

## 10. Collared traces: the correct conditional lemma and the missing realization

There is a standard local theorem behind the Push-VIII proposal.

Let \(C\) be an explicitly supplied bounded Lipschitz quadrilateral, let
\(J\) be one boundary side, and work in the homogeneous space

\[
  \dot H^1(C)=H^1(C)/\mathbb R
\]

with Dirichlet norm.  The trace image on \(J\), with its quotient norm, is a
Hilbert space.  A conformal isomorphism between two explicitly supplied
collars is an isometry of the homogeneous Dirichlet spaces and hence of
their quotient trace spaces.  For several sides of one connected collar
union, the compatible image must be given the quotient norm from one
\(\dot H^1\) space, retaining one diagonal constant and every cross-
\(H^{1/2}\) compatibility term.

Push VIII does not establish the hypotheses needed to apply that theorem to
the actual interface:

1. the cited KL pseudo-piece source does not select the claimed
   proof-compatible Lipschitz collars;
2. the actual immersion and covering are not proved to carry a coherent
   nested collar atlas;
3. the compact normalization term
   \(\left|\int_{K_J}u\right|^2\) is coordinate-dependent and its measure and
   positive-area hypothesis are not specified;
4. the image in the product trace space is not proved closed in the product
   norm; it is Hilbert only after the quotient norm is explicitly retained;
5. separate per-port groundings would erase relative constants, contrary to
   `MULTIPORT_TRACE_GAUGE_AND_STRICTNESS_NO_GO`; and
6. endpoint flags remain combinatorial data, not point evaluations of
   \(H^{1/2}\) traces.

Accordingly the local Lipschitz-collar lemma is valid, but the source-facing
node `COLLARED_IDEAL_ARC_TRACE_SPACE` is not promoted.

## 11. The one-step welding is still conditional

Formally, when actual compatible collars have been supplied, one may compose

\[
  \mathcal T_V(I)
  \xrightarrow{R_{\iota,E}}
  \mathcal T_{V'}(E)
  \xrightarrow{\operatorname{Sub}_{E_\ell}}
  \mathcal T_{V'}(E_\ell)
  \xrightarrow{P_{f,E_\ell}}
  \mathcal T_V(f(E_\ell)).
\tag{11.1}
\]

For (11.1) to be an actual bounded trace operator one must prove:

- \(E\) is a whole proper KKL end interval, not merely a proper micro-atom;
- the immersion maps an explicit source collar conformally into the chosen
  target collar;
- the covering transports a compatible source subcollar;
- in the fully proper case, every proper interval used by the physical
  interface is retained rather than only the two end arcs;
- all subarc traces are taken inside one closed compatible image with one
  global constant gauge;
- the output multiplicity counts actual covering subarcs and sheets; and
- the collar images and output tuple include every proof-used component.

None follows from the finite label table.  The proposed
\(\sqrt{\nu(I)}\) estimate is valid only for the homogeneous seminorm after
these collar inclusions and the multiplicity count are proved.  It does not
control the coordinate-dependent grounding term or provide a uniform bound
on \(\nu(I)\).

The operator is therefore a useful conditional pull-push template, not the
proved actual carrier welding claimed in the bundle.

The assertion that the compatible-image norm makes the map isometric also
needs correction: the quotient construction makes
\(\mathcal T_V(I)/\ker\mathcal W_{F,I}\) isometric to the range.  It makes
\(\mathcal W_{F,I}\) itself isometric only after injectivity is proved.

## 12. Exact failure of word functoriality

The proposed word theorem is ill-typed before it is false.

Let

\[
  F_1=(f_1,\iota_1):V_1\rightrightarrows V_0,\qquad
  F_2=(f_2,\iota_2):V_2\rightrightarrows V_1.
\]

Writing \(T_j\) for the relevant trace space, the factors have types

\[
\begin{aligned}
R_1 &:T_0\to T_1,& P_1 &:T_1\to T_0,\\
R_2 &:T_1\to T_2,& P_2 &:T_2\to T_1.
\end{aligned}
\]

Thus

\[
  W_1=P_1R_1:T_0\to T_0,\qquad
  W_2=P_2R_2:T_1\to T_1.
\]

The expression \(W_2\circ W_1\) has no type unless an additional
identification between \(T_0\) and \(T_1\) is supplied.  A generic
correspondence is a span; its composition requires a fiber product and a
new composite source, not componentwise notation alone.

Even if all spaces are artificially identified, componentwise composition
of the maps would give

\[
  W_{\rm comp}=P_1P_2R_2R_1,
\tag{12.1}
\]

while chronological multiplication gives

\[
  W_2W_1=P_2R_2P_1R_1.
\tag{12.2}
\]

There is no reason for (12.1) and (12.2) to agree.  Take

\[
R_1=P_2=I,\qquad
P_1=
\begin{pmatrix}1&1\\0&1\end{pmatrix},
\qquad
R_2=
\begin{pmatrix}1&0\\1&1\end{pmatrix}.
\]

Then

\[
W_{\rm comp}=P_1R_2=
\begin{pmatrix}2&1\\1&1\end{pmatrix},
\qquad
W_2W_1=R_2P_1=
\begin{pmatrix}1&1\\1&2\end{pmatrix}.
\tag{12.3}
\]

They differ.  Equality requires an additional Beck-Chevalley/interchange
square or a fiber-product correspondence theorem.  Ordinary associativity
of matrix multiplication cannot supply it.

This proves `PULL_PUSH_WELDING_WORD_COMPOSITION_NO_GO`.

## 13. What the matrix audit actually checks

The submitted matrix script:

1. constructs \(R^+\) so that \(R^+A_p=A_sR\);
2. constructs \(P^+\) so that \(P^+A_s=A_oP\);
3. verifies
   \[
     (P^+R^+)A_p=A_o(PR),
   \]
   which is the formal product of the two constructed identities; and
4. verifies \(W_3(W_2(W_1x))=(W_3W_2W_1)x\).

It does not construct or test:

- a composite covering/immersion span;
- the interchange square missing from Section 12;
- a pseudo-piece or relative cover;
- an ideal-boundary collar;
- a Sobolev trace;
- a compatible tuple image or its closedness;
- a proper/end-proper interval;
- a bridge word or endpoint flag;
- an actual enlargement; or
- the \(\sqrt{\nu}\) estimate.

The 1,000 exact checks are correct algebra, but they do not test the stated
word theorem or any analytic realization.

## 14. Slit repair, overlay refinement, and enlargement

### 14.1 Slit repair

A target crosscut graph produces a map on slit surfaces only after all of the
following are proved:

\[
  G'=f^{-1}(G)=\iota^{-1}(G)
\]

on every relevant sheet, with the correct side pairings.  One must also
exclude critical intersections, tangencies, cusps, omitted preimage
components, deck-phase conflicts, non-local finiteness, protected collisions,
and escape from the authorized localization.  After cutting, the entire
ideal-boundary and path-lift audit must be rerun.

The Push-VIII phrase "commuting selected source graph" does not establish
these properties.  Its slit theorem is therefore a conditional template.

### 14.2 Overlay refinement

Trace restriction is natural when all fine traces are the actual restrictions
of one common \(H^1\) function.  Exact response minimization also requires
that common physical domain, the closed compatible image, and the correct
transmission conditions.  The finite endpoint compiler supplies none of
these.  The proposed refinement theorem is conditional on the analytic
realization it claims to help construct.

### 14.3 Final-root enlargement

The project already proves `MARKED_PAIR_ENLARGEMENT_NATURALITY` under
analytic covering/immersion squares and exact protected endpoint inverse
images.  Push VIII does not construct those squares.

Moreover, the stated embeddings do not exclude new enlarged source
components or sheets outside the old embedded image.  Such a component may
join an old immersion pullback, add a proper lift, or insert a new nonproper
bridge while every old endpoint inverse-image equality remains true.  Exact
complete-interface naturality additionally requires:

- a bijection of all proof-used pullback components;
- no new sheet or lift over an old interval;
- no merge through a new nonproper bridge;
- equality of the full preimage graph;
- preservation of whole KKL end intervals and their properness; and
- coherent collar and relative-cover subgroup transport.

Without these conditions, only the old restricted subdiagram commutes.

## 15. Claim-by-claim disposition

| Proposed node | Disposition |
|---|---|
| `FINITE_BOUNDARY_IMMERSION_PULLBACK_FORMULA` | Rejected as an actual KKL theorem; path-lift and subordination data are missing. |
| `FINEST_IMMERSION_ADMISSIBLE_MARKING` | Retained only inside the abstract label-hull theorem. |
| `COVERING_IMMERSION_ACTION_CRITERION` | Conditional finite specialization; the actual endpoint criterion is already `PRIME_END_MARKING_ACTION_CRITERION`. |
| `BRANCH_ADAPTED_IDEAL_MARKING_COMPILER` | Rejected as an analytic compiler; narrowed to `FINITE_LINEAR_LABEL_MARKING_ENUMERATOR`. |
| `ACTION_TRACE_ENDPOINT_SEPARATION` | Retained as a no-laundering documentation rule. |
| `CERTIFIED_IDEAL_SLIT_REPAIR` | Conditional template; full preimage, side, sheet, and localization proof missing. |
| `COLLARED_IDEAL_ARC_TRACE_SPACE` | Standard after an explicit Lipschitz collar is supplied; actual pseudo-piece realization not proved. |
| `END_PROPER_END_GERM_TRACE_SPACE` | Application rejected because the end-proper classifier is false. |
| `ACTUAL_ONE_TO_MANY_IDEAL_WELDING` | Conditional pull-push template; actual collars, complete intervals, and gauges missing. |
| `MARKED_WELDING_WORD_FUNCTORIALITY` | Refuted/ill-typed by Section 12. |
| `NORMALIZED_MARKED_INTERFACE_NATURALITY` | Open; depends on the false word theorem and unconstructed immersion/collar squares. |
| `CERTIFIED_FINAL_ROOT_WELDING_NATURALITY` | Only a restricted formal implication; complete no-new-sheet naturality is missing. |
| `FIXED_HORIZON_MARKED_BINARY_INTERFACE_COMPLETION` | Refuted with its stated premises by Section 9 and depends on several failed nodes. |

The proposed `UNIVERSAL_MANDATORY_ENDPOINT_VISIBILITY_AND_REPAIR` node is not
added.  It bundles together existing independent open gates and uses
`VAAPC-I`, which is a clause label rather than an authoritative obligation
identifier.  Its contents remain distributed among the live virtual
correspondence, horizon, trace-collar, welding, response, Value, and H2
obligations.

## 16. Ledger-patch audit

The proposed patch is not in the authoritative ledger schema:

- the top-level object is a proposal wrapper, not the obligations array;
- the new open node lacks authoritative dependencies and evidence;
- `maps_to` is not a ledger field;
- `VAAPC-I` is not an obligation identifier;
- the evidence paths are not present under `research/mlc_unified`;
- the proposed analytic nodes bypass the existing open source-realization
  gates; and
- the principal node depends only on other proposed nodes, making the
  conditional package look unconditional.

Naively inserting the proposal would have changed the ledger from

```text
298 total = 23 imported + 212 proved + 63 open
```

to

```text
312 total = 23 imported + 225 proved + 64 open.
```

That insertion is rejected.  The integration adds only the two narrow proved
nodes described in Sections 5 and 12.  No pre-existing open status changes.
The resulting authoritative count is

```text
300 total = 23 imported + 214 proved + 63 open.
```

## 17. Correct replacement invariant

The next object must retain actual path-lifted correspondence data:

\[
\mathscr L_F(\mathcal I)=
\left(
  f^*\mathcal I,
  \{\iota^*I\}_{I\in\mathcal I},
  \{\pi_0(\iota^*I)\},
  \mathsf{Lift}_{\iota},
  \iota_*\pi_1,
  \mathsf{End}_{f^*\mathcal I},
  \mathsf{Prop},
  \mathsf{Collar},
  \mathsf{BC},
  \mathsf{Enl}
\right).
\tag{17.1}
\]

Here:

- \(\mathsf{Lift}_{\iota}\) contains definition-level unique-proper-lift
  witnesses, or a source-specific component-exhaustion theorem;
- \(\iota_*\pi_1\) records the relative-cover subgroup and monodromy data;
- \(\mathsf{End}_{f^*\mathcal I}\) is the complete covering interval and
  end-interval decomposition;
- \(\mathsf{Prop}\) proves properness on whole proof-used intervals;
- \(\mathsf{Collar}\) supplies the coherent Lipschitz collar embeddings and
  one-global-constant compatible trace spaces;
- \(\mathsf{BC}\) supplies the fiber-product/Beck-Chevalley interchange
  needed for chronological composition; and
- \(\mathsf{Enl}\) is a component-bijection and no-new-sheet certificate for
  every authorized enlargement.

The exact next theorem is:

### Path-lifted marked correspondence realization

For every proof-used fixed direct-decoration horizon, construct (17.1) from
the actual pseudo-piece covering and inclusion immersion, prove that every
required \(\iota^*I\) agrees with the source path-subordination definition,
prove whole-end-interval properness, construct coherent collars, and prove
the interchange and no-new-sheet enlargement squares.

Only after this theorem is established may the one-step pull-push template be
assembled into a word response or used in a transition theorem.

## 18. Global status

After the conservative integration, the global architecture is unchanged:

\[
\text{actual path-lifted marked interface}
\Longrightarrow
\text{finite/future-faithful response state}
\Longrightarrow
\text{strict backward transition}
\Longrightarrow
\text{coercive compactness}
\Longrightarrow
\text{rigidity}
\Longrightarrow
\mathrm{MLC}.
\]

Push VIII contributes a diagnostic enumerator, a clean action-versus-trace
separation rule, two useful finite obstruction formats, and an exact
composition no-go theorem.  It does not discharge the first arrow.
