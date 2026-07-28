# Referee issue resolution — 2026-07-24

## 1. Scope and source locks

This audit answers the report supplied as
`pasted-text.txt`, SHA-256
`58522C4C7DD59548A3F655D342F6369D645E9D230C72A86D41F9D62E4352D6CA`.
The report was treated as a list of hypotheses to verify, not as an
authority.

The primary source checks used:

- Kahn--Kapiamba--Lyubich, arXiv:2606.27272v1, extracted TeX
  `waves-with-Misha.tex`, SHA-256
  `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5`;
- Kahn--Lyubich, arXiv:math/0609046, extracted TeX `kingdom.tex`,
  SHA-256
  `5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7`;
- the current arXiv record for
  [Blokh--Levin--Oversteegen--Timorin](https://arxiv.org/abs/2205.03157).

No issue below changes the status of UPTCR or MLC: both remain open.

## 2. Resolution table

| Issue | Verification | Resolution |
|---|---|---|
| Attachment trace written as \(X\cap T\) | The current Markdown and TeX already used \(\overline X\cap T\); the reported formula appears to have lost the overline in extraction.  The ambiguity was real enough to harden. | The notation is now \(\tau_T(X)=\overline X^{\,T'}\cap T\), with the ambient of closure explicit and with a warning that \(X\cap T=\varnothing\).  Geometric trace and prime-end attachment records are separated. |
| Forward orbit union called closed | The current source already defined \(E_A=\overline{\bigcup_{n\ge0}\beta^n(A)}\).  One TeX sentence incorrectly attributed closedness to continuity. | Closedness is now attributed to the closure operation; continuity is used only for \(\beta(E_A)\subset E_A\).  The Markdown theorem already separates the marking criterion from minimal orbit closure. |
| KKL imported as global \(\mathcal T'=\mathcal T\) | Confirmed as a source-scope defect in narrative and ledger wording.  KKL prove only \(\mathcal T'\cap\mathcal L_{[B,q-B-2]}=\mathcal T\cap\mathcal L_{[B,q-B-2]}\). | Every import now states the restricted equality and its equivalent no-central-excess consequence.  Global equality is explicitly disclaimed. |
| Forward-coherent complement proof skipped connectedness of \(H'\) | Confirmed.  Full degree of the infinity component excludes other preimage-domain components, but does not alone prove the complementary pullback is connected. | The proof now passes to the connected unbranched degree-\(d\) cover of a punctured disk, classifies it by \(d\mathbb Z<\mathbb Z\), fills its unique puncture, and then deduces connectedness and fullness of \(H'\). |
| Direct-decoration component proof used only interior disjointness | Confirmed as under-explained. | The hypotheses now state closed Jordan pieces and proper degree-one boundary homeomorphisms.  Closed sibling disjointness is proved by uniqueness of the local inverse at a hypothetical common regular boundary point. |
| Shift treated as total at the root | Confirmed as a typing ambiguity. | The deletion map is now \(\sigma_{\rm pre}\), defined only on non-root finite addresses and infinite addresses.  The empty word has a separate terminal-cycle arrow \(\tau_{\rm root}\). |
| Safe-gap enlargement overclaimed as carrier stability | Confirmed as a scope ambiguity. | `PULLBACK_GAP_ENLARGEMENT_NATURALITY` is explicitly only a topological finite-fiber theorem.  Fullness, protected accesses, and analytic carrier admissibility are excluded from its conclusion. |
| Connector/free-component topology compressed | Confirmed. | The manuscript now has separate lemmas for finite one-ended slit removal, persistence of boundary endpoints and crosscuts, distinctness of prime ends, and cyclic-order preservation.  The main proofs invoke those lemmas. |
| Simultaneous pullback statement quantified over arbitrary \(B\subset O\) | Confirmed in the TeX statement; the detailed note already said “neighborhood.” | The statement now requires an open connected neighborhood \(K\subset B\subset O\), records that the selected component exists, and notes the admissible Jordan specialization used later. |
| Horizon selector depended semantically on its own final trace | Confirmed as a hidden semantic cycle, though the JSON graph did not expose it. | A new open `VIRTUAL_PREFIX_LOCAL_SCALE_SELECTOR` feeds the return atlas.  The frozen horizon then feeds `VIRTUAL_PROOF_USE_TRACE_SELECTOR`; the final proof-complete selector is downstream.  The machine graph is acyclic. |
| `VAAPC-P` mapped to a consequence that depended on full VAAPC | Confirmed as reversed dependency semantics. | New open obligation `VIRTUAL_UNPROTECTED_ATOM_EXPOSURE` records the independent exposure input.  `VAAPC-P` maps to it; completed packets plus exposure imply the common free component, not conversely. |
| Attachment-free anchor used where a disjunction suffices | Confirmed. | New open `VIRTUAL_ATTACHMENT_RESOLUTION` is the disjunction: actual attachment-free anchor, or collision-free analytically realized least attachment closure with empty central support.  Bounded attachment support depends on this disjunction. |
| BLOT bibliography title | Confirmed against the current arXiv record. | The bibliography now gives *Maps with no a priori bounds*, arXiv:2205.03157v4. |
| Immediate finite-cylinder lift absent | Confirmed as a tractable missing lemma. | `FINITE_CYLINDER_COMMUTING_ITERATE_LIFT` is proved.  The exact remaining gate is open `VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR`. |

## 3. Repaired complement-pullback derivation

Let \(R\) be degree \(d\), let \(H\) be a nondegenerate full continuum
containing every finite critical value, and put
\[
  \Omega=\widehat{\mathbb C}\setminus H.
\]
Then \(\Omega\) is simply connected and contains infinity.  The component
\(\Omega_\infty\) of \(R^{-1}(\Omega)\) containing infinity has degree
\(d\): a regular value near infinity has all \(d\) preimages there.  Any
other component would map properly and surjectively to \(\Omega\) with
positive degree, contradicting additivity of component degrees.  Hence
\[
  R^{-1}(\Omega)=\Omega_\infty.
\]

All finite critical points lie in \(R^{-1}(H)\).  Therefore
\[
  R:\Omega_\infty\setminus\{\infty\}
  \longrightarrow
  \Omega\setminus\{\infty\}
\]
is a connected unbranched degree-\(d\) cover.  A Riemann map identifies the
target with \(\mathbb D^*\).  Connected finite covers correspond to
subgroups \(d\mathbb Z<\pi_1(\mathbb D^*)\), so the source is again a
punctured disk.  Filling its single puncture makes \(\Omega_\infty\)
simply connected.  Thus its complement \(R^{-1}(H)\) is connected, while
its plane complement is connected by construction.  This proves the
claimed full continuum, without the omitted inference.

## 4. Repaired dependency order

\[
\begin{split}
&\text{direct-decoration component package}\\
&\longrightarrow
\text{finite-cylinder target-address selector}\\
&\longrightarrow
\text{disconnected marking transfer}\\
&\longrightarrow
\text{virtual Cantor-package realization}\\
&\longrightarrow
\text{prefix-local scale selector}\\
&\longrightarrow
\text{return atlas and branch language}\\
&\longrightarrow
\text{marked correspondence}\\
&\longrightarrow
\text{frozen Wave horizon}\\
&\longrightarrow
\text{proof-use trace and final selector}.
\end{split}
\]

The first, source-visible package and the commuting-iterate lift are proved.
Every later virtual arrow displayed above remains open.

## 5. Finite-cylinder result and exact residual gate

For equal-depth cylinder homeomorphisms
\[
  h_w=f^N|_{Q_w},
  \qquad
  h_v=f^N|_{Q_v},
\]
and \(F=f^r|_A\), actual containment
\[
  f^r(h_w^{-1}(A))\subset Q_v
\]
gives, pointwise,
\[
  h_v(f^r(x))
  =
  f^N(f^r(x))
  =
  f^r(f^N(x))
  =
  F(h_w(x)).
\]
Applying \(h_v^{-1}\) proves
\[
  f^r=h_v^{-1}\circ F\circ h_w.
\]
Surjectivity of \(F:A\to B\) gives exact image equality, and the
homeomorphic conjugacy preserves proper and local degree.

The formula does not choose \(v\).  The remaining theorem must construct a
unique target address for every source branch and prove prefix, partial
shift, root, marking, and enlargement compatibility.  Two closed cylinders
meeting the same image component are an actual uniqueness failure, not a
labeling inconvenience.

## 6. Status after repair

The machine ledger validates:

- 225 obligations total;
- 16 imported;
- 153 proved internally;
- 56 open.

The new proved obligation is
`FINITE_CYLINDER_COMMUTING_ITERATE_LIFT`.  The new and clarified open
obligations include:

- `VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR`;
- `VIRTUAL_PREFIX_LOCAL_SCALE_SELECTOR`;
- `VIRTUAL_UNPROTECTED_ATOM_EXPOSURE`;
- `VIRTUAL_ATTACHMENT_RESOLUTION`.

`VIRTUAL_DISCONNECTED_MARKING_TRANSFER`, VAAPC-I, UPTCR, and MLC remain
open.  No numerical regression discharges any analytic obligation.

## 7. Release validation

The post-repair release passed:

- the machine proof audit: 225 obligations, 16 imported, 153 proved, and
  56 open, with an acyclic dependency graph and `MLC` open;
- all 74 adversarial transfer regressions;
- a 73-page LaTeX build with no LaTeX, package, box, citation, reference,
  BibTeX, or fatal-error warnings;
- extracted-text checks for the ledger counts, unconditional-proof
  disclaimer, corrected BLOT title, proved finite-cylinder theorem, and
  all four new or clarified open gates;
- forbidden-text checks excluding the stale BLOT title and any proved
  classification of MLC;
- rendered inspection of every page on 13 contact sheets and
  full-resolution inspection of the title/status page, UPTCR statement,
  repaired complement proof, finite-cylinder theorem, selector ledger,
  final MLC status, and bibliography.

The released PDF SHA-256 is
`BE6FA8737D106313FDB949BC357301DB750BB065B846F3607BDD8813579D7EA2`.
