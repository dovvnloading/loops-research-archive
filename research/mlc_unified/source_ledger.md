# Source-locked theorem and notation ledger

Source lock date: 2026-07-26. “Imported” means the statement is used only with the
hypotheses shown here. “Open” means the source proposes the result or strategy but
does not prove the general statement needed by this project. A source claim whose
checked proof contains a material unresolved defect is also kept open, even if the
claim is stated as a theorem in the preprint.

## Primary sources

| ID | Locked source | Imported result | Hypotheses and limits | Role |
|---|---|---|---|---|
| D25 | Dzmitry Dudko, *On the MLC Conjecture and the Renormalization Theory in Complex Dynamics*, [arXiv:2512.24171](https://arxiv.org/abs/2512.24171) | Problem 4.3 asks for pseudo-Siegel bounds in the remaining unbounded satellite ql cases. Interpolation Problem 4.4 asks for a Virtual Molecule version of the Near-Degenerate Regime. The proposed virtual Julia sets are connected hulls of Cantor small Julia sets and contain the critical orbit only through a prescribed number of returns. | This is a survey and research proposal, not a proof of either problem. It says the two programs, together with existing positive/zero-entropy arguments, *should* imply full MLC. | Defines the two open gates and the virtual-hull idea. |
| KKL26 | Jeremy Kahn, Alex Kapiamba, Mikhail Lyubich, *MLC for parabolically bounded primitive renormalization*, [arXiv:2606.27272](https://arxiv.org/abs/2606.27272) | Theorem A: beau bounds for parabolically bounded prime primitive families. Theorem B: beau bounds plus bounded puzzle Teichmüller diameter imply rigidity. Theorem C: parabolically bounded prime primitive families are rigid. The paper recalls the native full-cycle Hubbard tree (and its rational-lamination lift when the filled carrier is not locally connected), the \(\psi\)-ql fiber-product iteration, canonical localization renormalization, and Kahn's theorem inducing a genuine ql map from bounded \(\psi\)-ql width. It also develops Thin--Thick, Value, Wanderers, Wave, amplification, and translation markings, with \(\|W^{\rm long}\|\le 2W_{\rm std}+6N\), and bounds WAD support by \(3|\chi(\mathcal V)|+|\mathcal I|\). | The Hubbard-tree import is native to a periodically repelling prime primitive \(\psi\)-ql map already carrying its complete small-Julia cycle. The geometric theorems require the paper's parabolic boundedness conditions. The paper explicitly treats a subcase of the near-parabolic regime, not all four regimes, and does not select a partial virtual package. Translation markings may have unbounded cardinality. | Positive-entropy/puzzle engine, terminal native carrier, categorical model for selected returns, corridor compression, and the rigidity endpoint. |
| DL25 | Dzmitry Dudko, Yusheng Luo, Mikhail Lyubich, *Uniform a priori bounds for neutral renormalization. Variation II: \(\psi^\bullet\)-ql Siegel maps*, [arXiv:2509.23031](https://arxiv.org/abs/2509.23031) | Equidistribution and regularized pseudo-Siegel estimates for \(\psi^\bullet\)-ql Siegel maps, including a transitional-level estimate. Definition `dfn:psi:Siegel:ql` requires core properness, homeomorphic iterated-core identifications, and covering-embedding properties for all fiber-product iterates. Proposition `prop:g:unwind` obtains them by inflation relative to a globally forward-invariant postcritical set and local saturation. The paper notes a multiple-component variant. | Eventually golden-mean Siegel setting and the paper's \(\psi^\bullet\)-ql hypotheses. The multiple-component remark is guidance, not a proved arbitrary finite-horizon virtual-inflation theorem. The explicit combinatorial-threshold construction excludes the transitional threshold, and applications require “global external input.” | Local neutral/sectorial engine and blueprint for the missing virtual correspondence. |
| DL22 | Dzmitry Dudko, Mikhail Lyubich, *Uniform a priori bounds for neutral renormalization*, [arXiv:2210.09280](https://arxiv.org/abs/2210.09280) | Uniform pseudo-Siegel bounds; construction of nested almost-invariant pseudo-Siegel disks with fjords and dams; uniform sectorial control for neutral quadratics. | Neutral quadratic setting developed in that paper. It does not prove the remaining unbounded-satellite cases. | Zero-entropy regularization model. |
| BLOT | Alexander Blokh, Genadi Levin, Lex Oversteegen, Vladlen Timorin, *Maps with no a priori bounds*, [arXiv:2205.03157v4](https://arxiv.org/abs/2205.03157) | For a degree-\(d\) polynomial with satellite relative period \(s\), every root annulus satisfies \(\operatorname{mod}(A)<2^{d-1}\pi/\log(4(s+1))\). With the base cycle added to the postcritical marking, an associated hyperbolic geodesic has a lower bound growing on the order of \(\log\log s\). | The root-annulus estimate is an upper bound, hence rules out classical uniform satellite modulus. The marked-geodesic result uses its stated infinite-renormalization and critical-set hypotheses. | Exact no-go theorem and evidence that the base cycle must be part of the state. |
| DL23 | Dzmitry Dudko, Mikhail Lyubich, *MLC at Feigenbaum points*, [arXiv:2309.02107](https://arxiv.org/abs/2309.02107) | Theorem A: every bounded-combinatorics Feigenbaum ql map has beau bounds. Theorem B: MLC at every Feigenbaum parameter. | Renormalization periods are uniformly bounded. | Recovery test and model backward-record argument. |
| CS15 | Davoud Cheraghi, Mitsuhiro Shishikura, *Satellite renormalization of quadratic polynomials*, [arXiv:1509.07843](https://arxiv.org/abs/1509.07843) | Exponential shrinking and rigidity for the paper's class \(\mathcal{QG}\) of high-type satellite sequences. | Strong arithmetic growth conditions; not arbitrary satellite combinatorics. | Recovery test showing satellite rigidity can be obtained without classical uniform root modulus. |
| L97 | Mikhail Lyubich, *Dynamics of quadratic polynomials, I--II*, [Acta Mathematica 178 (1997)](https://doi.org/10.1007/BF02392694), Part I [arXiv:math/9503215](https://arxiv.org/abs/math/9503215) | The Markov Yoccoz puzzle, principal-nest boundary avoidance, and native first-return decomposition into a degree-two central branch and univalent lateral branches; also the puzzle/rigidity machinery used by later papers. KKL26 isolates bounded puzzle Teichmüller diameter as the relevant additional input. | The return-map import is only for a specified native principal-nest puzzle level satisfying the source hypotheses. It does not select a virtual-Molecule scale and is not a blanket “bounds imply MLC” theorem. | Native analytic return-atlas positive control and rigidity endpoint. |
| KL06D | Jeremy Kahn, Mikhail Lyubich, *A priori bounds for some infinitely renormalizable quadratics. II. Decorations*, [arXiv:math/0609046](https://arxiv.org/abs/math/0609046) | For a fixed non-principal decoration outside a directly attached satellite copy, the paper constructs the ray puzzle, least \(q\)-return escape depth \(n\), escape route, critical piece \(Y^{nq+1}\), modified principal nest, terminal little-Julia cycle, and one pairwise-disjoint univalent pullback \(Q^v\) for each of the \(2^n\) separator vertices. | This is a direct-decoration construction in the original connected dynamical plane. It neither constructs Dudko's connected virtual carrier nor iterates through deeper disconnected virtual scales. Its raw separator count is not uniform in \(n\). | First virtual-scale puzzle selector and an explicit source of unbounded raw access incidence. |
| KL05P | Jeremy Kahn, Mikhail Lyubich, *Local connectivity of Julia sets for unicritical polynomials*, [arXiv:math/0505194](https://arxiv.org/abs/math/0505194), [Annals of Mathematics 170 (2009)](https://doi.org/10.4007/annals.2009.170.413) | Defines generalized polynomial-like first-return maps, the kingdom dynasty and modified principal nest, the first satellite escape kingdom, compact containment of its actual return domains, and analytic extensions of consecutive nest maps. | Imported only for the exact return-map construction and its stated connected-Julia/repelling-periodic category. It does not supply a virtual carrier or a uniform access compression. | Analytic foundation for the first decoration-scale escape atlas. |
| H92 | John H. Hubbard, *Local connectivity of Julia sets and bifurcation loci: three theorems of J.-C. Yoccoz*, [Topological Methods in Modern Mathematics, pp. 467--511 (1993)](https://pi.math.cornell.edu/~hubbard/Yoccoz.pdf) | Theorem III: if \(c\in{\cal M}\) is not infinitely renormalizable, then \(c\) has a basis of closed connected neighborhoods in \({\cal M}\). This is Hubbard's complete written proof/exposition of Yoccoz's theorem, based on Yoccoz's lectures and manuscript notes. | Exactly the non-infinitely-renormalizable quadratic parameter case; it is not an input for an infinitely renormalizable tower. | Removes the finite side of the global dichotomy and supplies the neighborhood-basis formulation needed for local connectivity. |
| Hat02 | Allen Hatcher, *Algebraic Topology*, [Chapter 3, pp. 255--257](https://pi.math.cornell.edu/~Hatcher/AT/ATch3.pdf) | Alexander duality for compacta: the arbitrary-compact-set extension replaces singular cohomology of the compact set by Čech cohomology. In dimension two it identifies \(\widetilde H_0(S^2\setminus K)\) with \(\check H^1(K)\). | The project uses the arbitrary-compacta form, not only Hatcher's locally contractible Corollary 3.45. It supplies qualitative connectedness and no metric separation. | Proves that a finite pairwise disjoint family of full augmented packets has connected common complement. |

The KKL26 row does not import the v1 Wave amplification proof.  That
theorem is source-stated but remains open in this project because its
bounded-visits interval-growth implication and stationary
proper-path/measurable-lamination extraction have not been repaired.
Theorems A--C and the other individually locked KKL clauses remain
imported only in the scopes stated above.

## Exact source locations

These locations refer to the TeX sources downloaded from arXiv on the lock date.

| ID | Location in source | Content checked |
|---|---|---|
| D25 | `main.tex`, Problem `prob:Satel:unbounded`, Interpolation Problem `prob:VirtMolec`, and the following paragraph | Exact statements of Problems 4.3/4.4 and the connected, partially invariant virtual Julia-set proposal. |
| KKL26 | `waves-with-Misha.tex`, Theorems A--C; “Future perspective”; Sections `sec:localization`, `sec:renorm`, `sec:hubbard trees`, and `Rigidity`; Appendix A.2.2 and Appendices `app:markings`, `app:dynamics`, and `app:transl-mark` | Scope of beau bounds, four-family classification, localization, the native full-cycle Hubbard tree and rational-lamination lift, the separate puzzle-Teichmüller requirement, WAD support bound \(3|\chi(\mathcal V)|+|\mathcal I|\), Thick–Thin, immersion itineraries/domination, and the exact long-arc estimate \(2W_{\rm std}+6N\). |
| DL25 | `main.tex`, Definition `dfn:psi:Siegel:ql`, Subsection `subsec:iter`, Definition `dfn:SiegelPreNorm`, Proposition `prop:g:unwind`, detailed inflation Subsection `sss:dfn:unwinding`, Remark `rem:prop:g:unwind`, Theorem `thm:main:ql maps`, and Section `Strategy to apply the main Theorem` | Exact \(\psi^\bullet\)-ql and iteration axioms; global forward-invariance and local-saturation hypotheses; relative-cover inflation; the multiple-component suggestion; transitional estimates; and the explicit statement that global input is required for applications. |
| DL22 | `PseudoSiegelBounds.tex`, Uniform Bounds Theorem and pseudo-Siegel disk definitions | Uniform neutral widths and almost-invariance. |
| BLOT | `no-bounds.tex`, Main Theorem and Corollary A | Root-modulus upper bound and base-cycle-marked hyperbolic-length result. |
| DL23 | `Feigen.tex`, `mainthm:A`, `mainthm:B` | Beau bounds and MLC for bounded-type Feigenbaum maps. |
| CS15 | `introduction.tex`, Theorem `T:rigidity` | Exponential diameter decay and MLC for \(\mathcal QG\). |
| L97 | Part I source `nest.tex`, lines 500--532, 577--619, 904--949, and 975--1005 | Markov puzzle pieces, principal-nest pullbacks, boundary avoidance, actual first-return components, and the central degree-two/noncentral univalent dichotomy. |
| KL06D | `kingdom.tex`, lines 21--155 and 181--233 | Satellite ray puzzle; least escape depth and route; \(Y^{nq+1}\); \(2^n\)-vertex separator and univalent pullbacks; modified principal nest and little-Julia cycle. |
| KL05P | `kingdom.tex`, lines 7--54, 102--223, 227--280, and 411--427 | GPL first returns; kingdom dynasty; compact first-return domains at the first escape kingdom; terminal primitive map; analytic extensions. |
| H92 | Theorem III, pp. 468--469 for the statement and Part III for the parameter-space proof | A non-infinitely-renormalizable \(c\in{\cal M}\) has a basis of closed connected relative neighborhoods. |
| Hat02 | Chapter 3, Corollary 3.45 and the arbitrary-compacta Čech extension on pp. 256--257 | The compacta form of Alexander duality used in `virtual_common_free_component.md`, Lemma 4.1. |

Clone-realization source check: KKL26 `waves-with-Misha.tex`, Appendix
`app:clones`, defines the abstract cross-section clone. Its concrete dynamical
licensing occurs in `not-all-good2.tex`: Lemma `lem:get-around`, lines 74--105;
Corollary `cor:cross-section`, lines 107--120; and Proposition
`prop:eigenweights`, lines 131--157. The argument uses a finite Hubbard tree and the
parabolic bound on small Julia sets per limb. The checked clone appendix has a
material finite-\(n\) exponent/orientation inconsistency; its exact reduced equation
and the limit proof depending on it are quarantined below rather than imported.

## Local source hashes

The hashes make the extraction reproducible even if an arXiv source is revised.

| arXiv ID | TeX file | SHA-256 |
|---|---|---|
| 2512.24171 | `main.tex` | `FD807D65C44852995182D23A4E96BB42717E8E7502F1D7B71636B16AF5D8A454` |
| 2606.27272 | `waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| 2606.27272 | `value1.tex` | `2767F71E57862DA5CF50FF7B96FC08917E24CA8F9BD2D4523C467B2E896AD83A` |
| 2606.27272 | `not-all-good2.tex` | `B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01` |
| 2509.23031 | `main.tex` | `ABFCC203BA7DC5F6A8F847AA8755FBCFA9091E8D6CAE520DFC5512FBDB1B8782` |
| 2309.02107 | `Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| 2210.09280 | `PseudoSiegelBounds.tex` | `4AE3253817EF8EEB76DF95FA411CB9C2B6CB0642C3C4AED4D8AE8305F2122172` |
| 1509.07843 | `Main.tex` | `F5A6080081D7000D44985369BEBF72CC1AE9A057182A11F52DEF9E1AF256FC8E` |
| 2205.03157 | `no-bounds.tex` | `ED8F55AE8ADE9667488AD91B4175AB40BFD2E3B7179D8141397F4A17B5B80DF6` |
| math/9503215 | `nest.tex` | `069C10711C36F5358134B418FDF6C5133A5AF16208D2B1C267EA7B4D3A5DF83A` |

### Native terminal Hubbard-tree anchor

The source-facing selector pass now distinguishes the actual KKL terminal
carrier from the still-undefined intermediate virtual package.

In `waves-with-Misha.tex`, lines 476--490 construct the native prime
primitive \(\psi\)-ql renormalization and its complete cycle
\(\mathcal K\) of small filled Julia sets. Lines 512--570 define the
smallest connected forward-invariant Hubbard tree \(\mathcal T\), its
finite vertex-edge tree and edge transition, and state that in the
non-locally-connected case the corresponding objects are obtained from the
locally connected rational-lamination model and its lift. Lines 602--650
construct the native tree arc/ideal data. This licenses
`KKL_NATIVE_TERMINAL_HUBBARD_TREE` only in that native category.

`terminal_hubbard_anchor.md` proves the finite-tree consequences separately.
For a finite selected vertex set \(S\), its convex hull is the union of the
unique paths between vertices. A tree map always satisfies
\[
  [\Phi(S)]\subset\Phi([S]),
\]
and equality holds when the selected restriction is injective. Enlarging
\(S\) adds a forest with one old-tree gate per component. Applied to the
complete terminal cycle, the hull is \(\mathcal T\), and the first edge on
the path from \(K_1\) to \(K_0\) selects a native ideal attachment side.

This does not import a Dudko virtual carrier. Dudko `main.tex`, lines
875--892, gives the satellite-copy chain and describes the proposed carrier
as the connected hull of corresponding **Cantor small Julia sets**. It does
not define the Cantor address space, actual embedded component family,
branch action, retained return number, protected side set, obstacle ledger,
or proof-use demands. A finite subset of the terminal primitive tree is
therefore not the first source-defined object.

The corrected interface is recorded in
`virtual_cantor_package_interface.md`. First construct
`VIRTUAL_CANTOR_PACKAGE_REALIZATION`, an actual compact component family and
its analytic return action. After the proof horizon is frozen, construct
`VIRTUAL_PROOF_USE_TRACE_SELECTOR`, a finite actual-component trace or a
future-faithful quotient. Only then may
`VIRTUAL_VERTEX_PACKAGE_SELECTOR` compare that trace with the terminal
Hubbard tree. These outputs are required before the recursive \(s=2\)
subtree can be formed.

The follow-up
`virtual_cantor_pullback_compactification.md` extracts the largest
component package already forced by the checked decoration source.
`kingdom.tex` lines 133--155 provide two actual univalent \(f^q\)-pullbacks
\(Q_0,Q_1\) of the separator \(P\). Their iterates, applied to the terminal
root \(K_0\), give a rooted family of actual preterminal Julia pullbacks.
The decreasing puzzle cylinders give connected end fibers indexed by the
binary Cantor space. Under the explicit hypothesis \(K(f)=J(f)\), the union
is a compact subset of \(J(f)\), and its components carry exact shift,
nesting-parent, sheet, time, and root-transition data. This licenses
`DIRECT_DECORATION_PULLBACK_COMPACTIFICATION`.

Root enlargements staying in
\(P\setminus(Q_0\cup Q_1)\) transport through all inverse words by commuting
squares, licensing `PULLBACK_GAP_ENLARGEMENT_NATURALITY`. Neither source
identifies the end fibers as the intended small Julia sets or transports
the satellite portrait of \(\mathcal M^{(2)}\) through the disconnected
intermediate map. The new first open analytic field is therefore
`VIRTUAL_DISCONNECTED_MARKING_TRANSFER`.

## Notation crosswalk

| This project | Meaning | Source analogue |
|---|---|---|
| \(F_n:U_n\to V_n\) | normalized ql or \(\psi^\bullet\)-ql return map at checkpoint \(n\) | ql/\(\psi\)-ql renormalizations in DL23 and KKL26 |
| \(\ell,h,d\) | molecule-chain length, largest continued-fraction entry, and continued-fraction depth | KKL26 “Future perspective” |
| \(W(F)\) | inverse ql modulus \(1/\operatorname{mod}(V\setminus U)\) when that annulus is valid | KKL26 width |
| \(\widehat Z^m\) | pseudo-Siegel regularization with dams/fjords | DL22/DL25 |
| \(H_n\) | proposed full connected virtual hull | D25 virtual Julia set, with added fullness requirement |
| \(B_n\) | base-cycle/neutral-access marking | forced by BLOT; compatible with DL sectorial markings |
| \(P_n^{\le r_n}\) | finite critical orbit through the last return used in the proof block | D25 “partial postcritical set” |
| \(\Sigma_n:=S_n,\ \nu_n:=r_n\) | collision-free manuscript aliases for the ambient surface and finite postcritical horizon | internal notation only; \(\nu_n\) is unrelated to the continued-fraction height \(h_n\) and to a block cell count \(r_B\) |
| \({\cal I}_n\) | ideal, translation, or sectorial boundary marking; its cardinality need not be bounded | KKL26/DL25 |
| \(\Gamma_n\) | declared marked family of essential closed curves and/or proper access arcs whose extremal width is transported | annular core curves, WAD proper arcs, and vertical/peripheral families in KKL26 and DL25 |
| \(D_n^\#\) | marked extremal length of \(\Gamma_n\) | proposed replacement invariant; not an imported theorem |
| \(E(B)\) | accumulated positive core entropy across a transition block | proposed entropy clock based on KKL26 Value contraction |
| \({\cal O}_B\) | WAD interaction types modulo the partial translation action | proved combinatorial compression in `virtual_block_quotient.md`; dynamical virtual realization open |
| \(\mathscr D_B\) | unnormalized active-width/corridor/Value vector before block-density and response normalization | local transition bookkeeping; virtual realization open |
| \(\mathscr R_B^{\rm val}=(Q_B/r_B,\Lambda_B/r_B,\mathbf V_B/r_B,S_B^{\rm std}/r_B)\) | provisional response-density/Value substate; \(\mathbf V_B\) can be omitted only after a Value-faithful port or coefficient-comparison theorem | finite response algebra proved; uniform surface realization and finite-feature compression open |
| \(\mathscr R_B^{\rm aug}=(\mathscr R_B^{\rm val},\mathbf\Xi_B/r_B)\) | augmented homogeneous state when reducible zero-entropy shear is retained; \(\mathbf\Xi_B=0\) if sectorial regularization removes the shear branch | finite-dimensional shear transport and regularization dichotomy open |
| \(\boldsymbol\nu_B\) | unbounded exact corridor-length, satellite-depth, and first-return counters; the number of counters must be universal | counter-follower realization open; KKL clone length is the model one-counter coordinate |
| \(\omega_B\in\mathcal T^*\) | optional explicit finite-alphabet word retaining ordered nested-molecule data; stack depth may be unbounded | D25/KKL give nested chains but no LIFO antirenormalization theorem; source-faithful push/pop realization open |
| \(\sigma_B=(r_B,\boldsymbol\nu_B,\omega_B,\rho_B,\kappa_B/r_B,\mathcal P_B,\mathcal F_B)\) | discrete and error-side data restricting valid charts, including exact counters, optional stack word, endpoint frame, and Frobenius flag/transfer type; not a homogeneous cone coordinate | internal congestion/topology/port/transfer audit state |
| \(L_B=L_{t_B}(\mathscr R_B^{\rm aug};\sigma_B)\) | potential homogeneous in the augmented geometric state, with constants uniform over admissible \(\sigma_B\) | forward contraction/backward expansion calibration remains open |
| \(\Psi_B(\,\cdot\,;\sigma_{\rm in},\sigma_{\rm out})\) | complete forward entropy-clock block map after identity localization/chart steps are grouped with the dynamical step | formal target in `block_contraction_program.md`; analytic realization remains open |
| \(F^{\le q}\) | depth-\(q\) truncation of the iterated-core and covering-embedding axioms | internal definition in `finite_horizon_inflation.md`; existence from arbitrary virtual hulls open |
| \(\Upsilon_j\) | stage-\(j\) finite excluded/marked set | must satisfy \(f(\Upsilon_j)\subset\Upsilon_{j+1}\) through the declared horizon |

## Import rules

1. KKL26's four cases classify **families** according to whether suprema of
   \(\ell,h,d\) are finite. They do not by themselves give a canonical finite block
   decomposition for each individual infinite tower.
2. DL22/DL25 may be used only after the map has been put into their neutral
   \(\psi^\bullet\)-ql setting. Compatibility across arbitrary ql/virtual changes is open.
3. BLOT forbids using ordinary satellite root modulus as a uniformly bounded checkpoint
   invariant when \(s\) is unbounded.
4. Beau bounds are not silently upgraded to MLC. The puzzle-Teichmüller/rigidity input
   remains a separate dependency.
5. “Expected,” “feasible,” “should imply,” and “to appear” are recorded as `OPEN`, never
   as imported lemmas.
6. If \(N_{\beta\gamma}\) is the raw source-to-target occurrence incidence, project
   source-column matrices satisfy \(B=N^{\mathsf T}\); KKL \(v,w\) become the
   project left and right eigenweights, respectively, and Value uses \(v^2w\).
   The checked source uses its symbol \(T_F\) with incompatible orientation cues,
   so no unconditional equation \(B=T_F\) or \(B=T_F^{\mathsf T}\) is imported.
7. The exact \(+\lambda^k\) finite-\(n\) clone equation in the checked KKL snapshot
   is not imported. The project uses only the independently proved literal-graph
   recurrence \(H(t)=\sum_k t^{-k}R_k\) from
   `corrected_clone_theorem_derivation.md`.

## Finite-horizon source-lock addendum

The finite-horizon pass checked the following additional locations in DL25 `main.tex`:

- Definition `dfn:psi:Siegel:ql` and Subsection `subsec:iter`: exact
  \(\psi^\bullet\)-ql core-properness, iterated-core, fiber-product, and
  covering-embedding axioms;
- Definition `dfn:SiegelPreNorm`, Proposition `prop:g:unwind`, and detailed inflation
  Subsection `sss:dfn:unwinding`: global forward-invariance, local saturation, and the
  relative universal-cover construction;
- Remark `rem:prop:g:unwind`: the suggested multiple-component framework and relaxed
  saturation at \(K_m\).

The remark is not imported as a general construction theorem. It may be used only as a
categorical blueprint after stage properness, core identities, local saturation, and
all needed covering-embedding iterates have been proved.

Topological equivalence of \(\psi\)-ql data is not a width comparison. The rescaling
family in `finite_horizon_inflation.md`, Theorem 7.1, varies width arbitrarily while
preserving the relevant topological data.

At the DL25 transition level \(m_F\), Theorem `thm:main:ql maps`, Case (B), gives
\[
W^{+,\mathrm{ver}}=O(\ell_{m_F}K_F),
\qquad
W^{+,\mathrm{per}}_3=O\!\left(\sqrt{\ell_{m_F}K_F}\right).
\]
This is imported only for eventually-golden-mean \(\psi^\bullet\)-ql Siegel maps with
the theorem's grounded-interval hypotheses. The paper's application section says that
global external input is still required for the vertical alternative.

## Localization and WAD source-lock addendum

KKL26 `waves-with-Misha.tex`, Section `sec:localization`, defines the subsurface cover
and localization by quotienting a universal cover by the stabilizer of a lifted
boundary curve, cutting, and gluing to the selected subsurface. Section `sec:renorm`
uses this to construct the canonical prime primitive \(\psi\)-ql renormalization.
Theorem `thm:induced quadratic-like map` produces a genuine ql restriction only after
the localized \(\psi\)-ql width is bounded. These statements do not provide the missing
virtual marked-width comparison.

The same source, Appendix `app:markings`, Theorem `main estimate`, gives
\[
W(\mathcal V,\mathcal I)-O(|\chi(\mathcal V)|+|\mathcal I|)
\le2\|X_{\rm can}\|\le W(\mathcal V,\mathcal I).
\]
Appendix A.2.2 (“Weighted arc diagrams”) states that the support of a WAD is a
nonintersecting arc diagram and has cardinality at most
\[
  3|\chi(\mathcal V)|+|\mathcal I|.
\]
Appendix `app:transl-mark`, Theorem `thm:bounded short`, gives the exact long-tail
estimate \(2W_{\rm std}+6N\). Appendix `app:dynamics`, Lemma `lem:domination` and
Proposition `prop:itineraries`, records harmonic-sum domination and path splitting
under immersions. None of these statements supplies a linear transition matrix for
unbalanced serial widths.

## Neutral/corridor normalization correction

The following source locations sharpen the DL25 entry and correct the project
normalization.

DL25 `main.tex`:

- lines 986--1010 define the closest-return lengths \(\ell_m\) and denominators
  \(\mathfrak q_m\);
- lines 1224--1226 define \(K_F=W^\bullet(F)\);
- line 2793 gives exactly \(\mathfrak q_{m+1}\) tiles at level \(m\);
- lines 3038--3042 define \(A_m=\ell_mK_F\);
- line 3077 records \(\ell_m\asymp1/\mathfrak q_{m+1}\);
- Proposition `prop:equidcombinbatorial`, lines 3253--3258, gives per-tile vertical
  width \(\asymp A_m\) at the transition level;
- Theorem `thm:main:psi-ql maps`, lines 3007--3016, gives peripheral
  \(O(\sqrt{A_m})\);
- lines 3281--3292 aggregate tile widths by the parallel law.

Writing \(r_m=\mathfrak q_{m+1}\), the source-compatible scales are
\[
  W_{\rm cell}\asymp A_m,
  \qquad
  W_{\rm total}\asymp r_mA_m\asymp K_F.
\]
Therefore the project's total retained WAD weight cannot be compared directly with
\(A_m\). The corrected target is
\[
  Q_{\rm cell}=Q_{\rm orb}/r_m\asymp A_m,
  \qquad
  Q_{\rm orb}\asymp K_F.
\]
For the proposed corridor coordinate this multiplicative target is asserted only in
the large-\(A_m\) branch after additive interface errors are absorbed. Below a
universal \(A_*\), the valid conclusion is a bounded normalized cell coordinate, to
be routed into the regularization threshold.

KKL26 `waves-with-Misha.tex`:

- lines 2185--2196 and 2228--2232 give
  \[
    N=2(n+1)p,
    \qquad
    \|X^{\rm long}\|\le2W_{\rm std}+6N;
  \]
- lines 1004--1015 bound \(p\) in the inner parabolically bounded application;
- lines 936--958, 1004--1007, 1040--1048, and 1082--1085 contain the HTND,
  arc-length, tameness, and parabolic-boundedness hypotheses used there;
- lines 174--175 state that transfer to the \(\psi^\bullet\) category is outside the
  paper's scope.

KKL's \(p\) is a translation-marking shift, not a DL25 continued-fraction entry. No
imported result identifies \(n+1\) with \(\mathfrak q_{m+1}\).

The response-algebra state records
\[
  \mathscr R_B=
  \left(
    Q_{\rm tot}/r_B,\,
    \Lambda_B/r_B,\,
    S/r_B
  \right),
\]
while
\[
  \sigma_B=
  \left(
    r_B,\,
    \boldsymbol\nu_B,\,
    \omega_B,\,
    \rho_B=r_{\rm mark}/r_\parallel,\,
    \kappa/r_B,\,
    \mathcal P_B,\,
    \mathcal F_B
  \right)
\]
is side/error data. Here \(\rho_B\) measures marking-to-parallel-replica congestion,
\(\boldsymbol\nu_B\) holds declared exact clocks, and \(\omega_B\) is an optional
explicit nesting word rather than a cone coordinate. Neither bounded incidence nor
bounded \(\rho_B\) follows from connectedness of the virtual hull, and raw \(r_B\),
counter values, and stack depth are not coercive cone coordinates. The BC1 addendum
below proves that positive-entropy use requires the additional Value moment
\(\mathbf V_B/r_B\), unless the port quotient is proved Value faithful.

## KKL typed-incidence and clone-source audit

The complete relevant ranges of KKL26 `value1.tex`,
`waves-with-Misha.tex`, and `not-all-good2.tex` were re-audited in
`kkl_transfer_orientation_audit.md`.

For a source Hubbard edge \(\beta\) and target edge \(\gamma\), define
\[
  N_{\beta\gamma}
  =
  \#\{\alpha\in\iota^*\beta:f_*\alpha=\gamma\}.
\]
The project's forward count transport uses source columns, hence
\[
  B_{\gamma\beta}=N_{\beta\gamma},
  \qquad B=N^{\mathsf T}.
\]
The Value coordinate sums, independently of the paper's ambiguous \(T_F\) label,
give
\[
  Nv=\lambda_Fv,
  \qquad
  N^{\mathsf T}w=\lambda_Fw.
\]
Therefore KKL \(v\) is the project left eigenweight, KKL \(w\) is the project right
eigenvector, and the base Hubbard-edge Value coefficient is
\[
  v_\beta^2w_\beta
  =
  (\ell_{\rm left})_\beta^2(r_{\rm right})_\beta.
\]
Chronological project products obey
\[
  B_m\cdots B_1=(N_1\cdots N_m)^{\mathsf T}.
\]

The audit also checks the entire clone appendix. Its literal chain recurrence,
reduced \(+\lambda^k\) weights, and displayed finite-\(n\) eigenvalue equation are
mutually inconsistent. On the explicit primitive base graph
\[
  e\to a,\quad a\to e,\quad a\to b,\quad b\to e
\]
with cross section \(\{e\}\), the clone Perron root satisfies
\(\lambda_n^{n+3}=\lambda_n+1\), whereas the displayed reduced equation would force
the impossible identity \(\lambda_n^n=\lambda_n^{n+5}\). The advertised asymptotic
\(\lambda_n^n\to2\) still holds in this example, so the counterexample invalidates
the printed finite-\(n\) proof bridge, not automatically the limiting claim.
`corrected_clone_theorem_derivation.md` now independently derives the negative-weight
equation for every literal fixed cross-section clone under its declared hypotheses
and proves the clone limit and both typed gate-eigenvector limits. This closes the
mathematical repair internally while leaving the printed source bridge rejected.

## BC1 finite-port and Value-observability addendum

The BC1 pass rechecked the following exact KKL26 locations in
`waves-with-Misha.tex`:

- lines 1881--1894: a canonical support class is represented by a rectangular
  lamination whose conformal width is the width of its connecting path family, after
  the declared square-buffer removal;
- lines 1901--1914: WADs, their norm, the finite support bound, and validity via an
  inducing lamination;
- lines 1937--1943: the canonical lamination and canonical WAD;
- lines 2086--2090: harmonic-sum domination for restrictions of a lamination;
- lines 2099--2108: ordered interval itineraries under an immersion;
- lines 2113--2124: coefficientwise WAD domination with harmonic-sum weights.

The companion source file `value1.tex`, lines 6--20 and 103--111, defines an expanding
valuation and proves
\[
  \operatorname{val}(X)
  =
  \sum_\alpha X(\alpha)\ell(\alpha)^2,
  \qquad
  X\dominates Y\Longrightarrow
  \operatorname{val}(X)\ge\operatorname{val}(Y),
\]
together with pullback contraction by the core eigenvalue in the primitively
renormalizable periodically repelling \(\psi\)-ql setting.
At the base Hubbard level, its length is
\(\ell(\beta)=v(\beta)\sqrt{w(\beta)}\). In project source-column coordinates this
means \(\ell(\beta)^2=(\ell_{\rm left})_\beta^2(r_{\rm right})_\beta\), as locked in
the preceding typed-incidence audit.

These source statements justify the discrete WAD and harmonic-itinerary inputs to
`bc1_finite_port_response.md`. They do not identify the WAD with a uniformly
bounded-terminal surface response. In particular, KKL Value weights support
coordinates by \(\ell(\alpha)^2\), while an electrical response weights their endpoint
incidence vectors. The exact non-observability theorem in that note shows that the
response state must either use Value-faithful ports or retain the relevant Value
moments.

`bc2_value_feature.md` uses the same KKL `value1.tex` statements to close one
source-licensed primitive block algebraically:
\[
  V_F((f^n)^*X)\le\lambda_F^{-n}V_F(X).
\]
The timing variables in KKL's concrete tame application must not be conflated.
In `not-all-good2.tex`, lines 7 and 131--149, the complete WAD step is
\(g=f^{\mathrm{per}}\), while the cloned cross-section length is
\(q-(2B+2)\), where \(B\) is the fixed limb-occupancy bound. The clone
calculation there is used to control \(\lambda_F^{q-(2B+2)}\) and eigenweight ratios;
the strict Value loss is applied separately with exponent \(\mathrm{per}\).
Thus KKL does not source-license an automatic equality between graph delay and
pullback exponent.

Internally, the exact sufficient timing condition is the inequality \(r\ge n\):
if a literal clone has delay \(n\) and the realized outgoing WAD satisfies
\[
  Y\le(f^r)^*X+E,
  \qquad r\ge n,
\]
then KKL monotonicity and pullback contraction give
\[
  V_F(Y)
  \le \lambda_F^{-r}V_F(X)+V_F(E)
  \le \lambda_F^{-n}V_F(X)+V_F(E).
\]
This timing-domination step is proved in `virtual_clone_entropy.md`, Theorem 4.1.
For a virtual corridor, the relation \(r\ge n\) remains part of the analytic
realization theorem.

KKL `waves-with-Misha.tex`, lines 2236--2318, states for a fixed primitive graph
with a cloned cross section that
\(\lambda_n\to1\), \(\lambda_n^n\to h(1)>1\), and a normalized eigenvector
converges on the fixed cross section. The checked proof uses the inconsistent
finite-\(n\) bridge documented above. Consequently it is not imported. The same
limit, with both typed gate-eigenvector limits, is instead a proved internal theorem
of `corrected_clone_theorem_derivation.md`.

Its affine-error corollary is internal. The source does not provide a common
finite-feature state when the Hubbard tree, valuation, or chart changes. Also, the
row-space rank test in that note applies to the lifted, uneliminated port Laplacian;
a terminal response after Schur elimination is nonlinear in its edge weights and must
pass the direct fiber-observability test instead.

## Variable clone-entropy addendum

KKL26 `waves-with-Misha.tex`, lines 2236--2318, assumes a fixed primitive directed
graph \(A\), a cross section \(E\), and a crossing bound \(N\). It states a reduced
labeled equation and the limits
\(\lambda_n\to1\), \(\lambda_n^n\to h(1)>1\), plus eigenvector convergence. The
literal \(+\lambda^k\) equation is false for the source definitions on the
three-vertex test above. The project therefore does not source-license the printed
proof. It independently derives the exact literal-clone operator
\[
  H(t)=\sum_{k=2}^{K}t^{-k}R_k
  =t^{-1}D(tI-Q)^{-1}C,
  \qquad
  \rho(H(\lambda_n))=\lambda_n^n,
\]
in `corrected_clone_theorem_derivation.md`.

`virtual_clone_entropy.md` then proves internally that every irreducible
non-permutation integer return matrix of dimension at most \(d\) satisfies
\[
  \rho(R)\ge2^{1/d}.
\]
If the actual maximum first-return length is \(K\le N<n\), the corrected clone
multiplier \(q_n=\lambda_n^n\) obeys
\[
  q_n\ge\rho(R)^{n/(n+K)}>2^{1/(2d)},
\]
and a source-licensed KKL complete block therefore has homogeneous Value factor
\(\le2^{-1/(2d)}\), provided its actual WAD pullback exponent \(r\) is at least
the graph delay \(n\). Application to a virtual corridor remains open because no source
proves that the corridor has:

- a complete literal clone edge graph, including every multiplicity;
- universally bounded gate dimension and actual first-return depth with \(n>K\);
- a source-licensed primitive \(\psi\)-ql WAD realization with
  \(Y\le(f^r)^*X+E\) and \(r\ge n\);
- future-closed ports and outgoing Value-error control.

The same note proves exact bounded-entropy reduced Perron-eigencone compactness and
shows by a directed cycle with one self-loop that primitive spectral radii can tend
to \(1\) when reduced dimension is unbounded. For a weighted retained operator that
satisfies its own corrected equation at its own root, it proves the strict expansion
tolerance
\[
  \epsilon<1-2^{-1/d},
\]
with multiplier at least
\(((1-\epsilon)2^{1/d})^{n/(n+K)}\). One-sided lower domination alone does not imply
eigencone compactness. These stability statements are internal and are not
attributed to KKL.

## Exact corridor-to-clone addendum

KKL26 `waves-with-Misha.tex`, lines 2240--2268, defines a cross section \(E\), the
length-\(n\) clone obtained by replacing \(E\) by
\[
  E_0,\ldots,E_n,
\]
and the associated reduced labeled matrix once the clone length exceeds the crossing
bound. KKL separately assumes the relevant original and cloned transition matrices
are primitive. This finite graph construction is usable as a definition; its printed
weighted eigenvalue equation is not imported. Once this literal graph is realized,
the internal corrected theorem supplies its negative-weight spectral equation.

`corridor_clone_criterion.md` proves internally that a directed transition
multigraph is this clone exactly when:

- its only corridor-to-corridor edges are the declared label-preserving chain edges;
- every other corridor edge enters at \(E_0\) or exits at \(E_n\);
- deleting the distinguished chain edges and identifying their labels gives a
  reduced quotient in which \(E\) is a cross section; and
- edge multiplicities agree with the reduced quotient.

It also proves that endpoint defects confined to universally bounded entry and exit
windows can be absorbed into the active graph without increasing \(|E|\). A finite
union of equal-length disjoint corridors gives one clone only under the separately
stated hypothesis that the union of their cross sections is a cross section of the
combined reduced quotient.

These are finite-graph statements, not imported dynamical theorems. No cited source
proves that Dudko's virtual hull produces the required core/Hubbard transition
multigraph, that hidden critical edges are absent, that the WAD pullbacks carry a
complete compatible itinerary-incidence map to that core graph, or that cross-section
dimension, endpoint-window size, parallel-corridor count, and label depth are
universal. KKL's cloned graph is the Hubbard-tree/core transition defining the
Perron eigenweights; it is not the terminal WAD response network.

## Transfer/shear addendum

Neither D25 nor KKL26 states that every virtual corridor has a pure cloned interior.
D25 allows a nested virtual bounded-type satellite chain but does not construct its
finite core transition. KKL's exact cloning assertion uses the special
parabolically bounded Hubbard-tree translation region.

`corridor_entropy_shear_dichotomy.md` therefore treats pure cloning as one branch of
an internal finite-state trichotomy. It proves:

- a cocycle of permutation layer transfers has an identity **interior** gauge after
  label transport; exact cloning still requires side-edge, gate, source, and WAD
  hypotheses;
- a nonzero irreducible non-permutation integer framed return of dimension \(d\) has
  \(\rho\ge2^{1/d}\);
- every reducible integer framed return of spectral radius at most \(1\) has a
  cycle/zero Frobenius diagonal and polynomial feed-forward transport; the purely
  transient case is nilpotent.

The unipotent example
\[
  \begin{pmatrix}1&1\\0&1\end{pmatrix}^{m}
  =
  \begin{pmatrix}1&m\\0&1\end{pmatrix}
\]
proves internally that bounded local type and zero exponential entropy do not imply
exact cloning or bounded transport. No source is credited with the resulting Virtual
Corridor Transfer Trichotomy. In particular, its nonstationary common-flag theorem
and its pseudo-Siegel or retained-state control of shear are open.

`corridor_support_automaton.md` adds an internal nonstationary reduction. For an
\(s\)-state automaton with \(d\)-dimensional nonnegative transfers, the pair of
automaton state and prefix Boolean support takes at most \(s2^{d^2}\) values. Exact
loop pumping therefore leaves a support skeleton of length at most
\(s2^{d^2}-1\), while retaining every numerical loop in its nested, contextual
position. A cyclic non-simple strongly connected support component has a witness
within the same bound and hence the algebraic graph gap \(2^{1/d}\). That gap is a
dynamical entropy certificate only for a closed repeatable return with a
source-licensed endpoint frame. No cited source constructs the required
source-faithful finite automaton for a virtual hull or proves that its
support-neutral loops share a regularizable Frobenius flag.

`virtual_language_memory.md` proves that this finite-automaton request itself needs a
counter qualification. The minimal exact deterministic state count is the index of
right future equivalence. A fixed three-letter alphabet with horizon \(2m+1\) can
have index at least \(2^m\), and a unique exit after \(m\) translation steps requires
at least \(m+1\) states unless the exit time is stored as a counter. Hence no cited
finite-horizon theorem implies a uniform automaton.

The corrected internal target retains a universal number of unbounded counters
\(\boldsymbol\nu_B\). For a loop increment \(\Delta\), a continuation increment
\(\eta\), and endpoint predicate \(\Phi\), deletion is endpoint-safe exactly on the
counter fiber where
\[
  \Phi(\nu+\eta)=\Phi(\nu+\Delta+\eta).
\]
Zero increment or reachable-fiber invariance is a convenient sufficient condition,
not a pathwise necessity. KKL's explicit clone length is a model for retaining,
rather than deleting, such a counter; its printed weighted equation remains under
the clone-source quarantine above.

D25 `main.tex`, lines 875--892, supplies a finite canonical inclusion chain of
satellite copies and proposes the virtual hull. KKL26 `waves-with-Misha.tex`, lines
299--303, supplies a unique infinite nested satellite-copy sequence, while lines
478--491 describe forward prime-primitive \(\psi\)-ql renormalization. None of these
passages defines matched push/pop maps, no-skipping reverse order, or recovery of the
predecessor hull together with its WAD/access state. D25's satellite
antirenormalization extension is stated as a strategy, not a theorem. Therefore a
LIFO model is an explicit open alternative, not an imported fact, and the labeled
word \(\omega_B\) cannot be replaced by its depth without proof.

## KKL occupancy-trichotomy scope addendum

### Live DKL availability check

As of the source-lock date, the public KKL reference list still labels
Dudko--Kahn--Lyubich, *Virtual renormalization: interpolating between primitive
and satelite regimes*, as **in preparation**. Targeted arXiv and author/title
searches on 2026-07-23 located no public manuscript. Consequently no theorem
from DKL is imported here; the brief virtual-hull descriptions in Dudko's note
and KKL's perspective section remain strategy statements rather than a
checkable source proof.

KKL26 Proposition 3.7 and Remark 4.14 license one additional import, and only
one. For every fixed limb-occupancy bound \(B\) and amplification parameter
\(M\), there is a threshold \(A(B,M)\) such that a periodically repelling,
prime primitively renormalizable \(\psi\)-ql map already carrying KKL's full
cycle \(\mathcal K\), Hubbard tree \(\mathcal T\), canonical ideal marking,
canonical WAD, and canonical renormalization satisfies
\[
  \mathbb W(\mathcal R F)\ge A(B,M)
  \quad\Longrightarrow\quad
  \begin{cases}
  F\text{ is }M\text{-amplifying},\ \text{or}\\
  \mathcal U\setminus\mathcal K\text{ is }M\text{-tame},\ \text{or}\\
  \mathcal U\setminus\mathcal T\text{ has }M\text{-wide controllable waves}.
  \end{cases}
\]
Remark 4.14 removes the rotation-\(1/q\) and critical-limb image hypotheses
only from this static Proposition 3.7 split. It does not transfer Proposition
3.8's tame amplification proof or Proposition 3.9's wave amplification proof.

The occupancy used in Section 4 is not merely a count of selected continua.
KKL turns at most \(B\) small filled Julia sets per limb into an access-complete
ideal multi-interval bound \(|\mathcal L_j|\le 6B\) using the finite Hubbard
tree. A virtual hull must construct the analogous complete limb marking, prove
the canonical-WAD/renormalization-width and cycle-component comparisons, and
faithfully restrict the flux and alignment laminations before this import can
be applied. Those requirements form the open Virtual Section-4 Interface.

The finite-tree conversion itself is now proved internally in
`virtual_limb_marking_bound.md`. A reduced anchored tree spanning \(m\)
non-anchor marked atoms has at most \(4m-2\) oriented tree sides; charging up
to two local ideal decorations at every prescribed vertex, including the
anchor, gives at most \(6m\) intervals. This
closes only the combinatorial count after access completeness and a uniform
atom bound are supplied. A star-tree family shows that the selected-component
count cannot substitute for the marked-atom count.

The two branch closures remain distinct open obligations. The tame branch
requires the full selected return, localization, bounded selected degree,
complete WAD domination, Wanderers control, and the actual Value pullback
timing. The wave branch requires stagewise pulled markings and the entire
\(O_B(q)\) fast-forward/critical-visit horizon. The exact source map and
line-level proof audit are recorded in
`kkl_virtual_occupancy_source_audit.md`.

Their quantifier composition is proved internally in
`virtual_branch_assembly.md`. Following KKL's proof of Theorem 3.6, the static
split is invoked at the wave theorem's input parameter
\(P=P_w(B,L)\); the tame theorem must accept that same \(P\), while
amplification monotonicity descends from \(P\) to the requested \(L\).
This is a logical assembly theorem only and imports no missing analytic
branch estimate.

### Tame and Wave branch source lock

The tame statement is imported only in its native category:

- Proposition 3.8 closes the \(P\)-tame branch for parabolically
  \(B\)-bounded, prime primitively renormalizable KKL \(\psi\)-ql maps once
  the declared high-type and successor-width thresholds are met.
- Proposition 3.9 **states** the controllable-Wave conclusion in the same
  category, with constants depending on \(B\) and the requested
  amplification but not on the satellite period.  Its v1 proof is not
  imported: bounded-visits interval growth and the stationary
  proper-path/measurable-lamination extraction remain open.

The tame import and the source-stated Wave theorem do not assert that a
Dudko virtual hull supplies KKL's full
cycle, localized return, canonical WAD, Hubbard-tree side action, or marked
wave laminations. The complete hypothesis extractions are in
`virtual_tame_full_return.md` and `virtual_long_iterate_wave.md`.

The tame audit proves internally, rather than imports:

- total selected degree \(2^{m_I}\) for \(m_I\) quadratic encounters;
- absorption of a marking error linear in the full-return period;
- the algebraic Value contradiction behind near-self-domination; and
- the conditional transfer from `VR0`--`VR5` and `VR7` in a realized KKL
  coordinate.

Its geometric realization and unified-chart clause `VR6` remain open.
Moreover, multiplication by \(a^{-1}\bmod q\) does not preserve cyclic order
for a general rotation \(a/q\); a virtual block needs a geometric accelerated
corridor, not a formal change of labels.

Conditional on the missing bounded-visits interval-growth implication,
the Wave audit proves internally that the theorem-call program fits inside
the conservative horizon
\[
 H_B(q)=(216B^2+1)(q+B+4),
\]
and proves a conditional `WA1`--`WA12` finite-horizon transfer. It also proves
that a single degree-two endpoint return cannot contain the terminal
degree-\(2^L\) fan for \(L\ge2\). The open virtual theorem must therefore
construct a degree-one central corridor together with the bounded auxiliary
marked fan, plus the interval action and critical-limb alignment. None of
these internal reductions is attributed to KKL or to the unavailable DKL
manuscript.

`selected_marked_fast_forward_fan.md` closes one further internal topological
step. A finite full inverse-component tree with separated compact obstacles
admits one simultaneous system of proper Jordan pullback sheets. The degree of
each branch is \(2^m\), where \(m\) is its number of quadratic encounters, and
one branch for each \(m=0,\ldots,M\) has total degree
\(2^{M+1}-1\). This is a new internal theorem, not an imported KKL statement.
It assumes the inverse tree and obstacles; it does not construct the complete
prime-end marking, the \(\psi\)-ql immersion, the wave itinerary partition, or
the extremal-width comparison.

The same note proves internally that pullback-component saturation is not a
formal consequence of fullness or partial invariance. Under \(z\mapsto z^2\),
the closed right half-disk maps surjectively onto the closed unit disk and both
contain the critical orbit, but the half-disk is not the unique component of
the unit disk's pullback. No source theorem is credited with repairing this
gap; a virtual construction must prove the actual component relation.

`saturated_virtual_seed_forest.md` uses Dudko's public virtual-hull description
only as motivation. It proves internally that forward-coherent connected seeds
have a canonical component saturation, that finite separated forward-closed
obstacles give the exact complement inclusions, and that a finite root endpoint
marking pulls back with exact degree-weighted cardinality and cyclic order.
None of these statements is attributed to the in-preparation DKL work.
The remaining source gap is precisely the construction of forward-coherent
connectors and a bounded root marking that captures every proof-used future end.

`marked_endpoint_birth_ledger.md` is also internal. It proves the exact
degree-weighted recurrence for endpoints first exposed at intermediate stages.
In particular, bounded births at each degree-one translation step can still
accumulate linearly in the period; period independence follows when genuine
births vanish in the central corridor and remain confined to a bounded
terminal window. No such no-birth theorem is imported for a virtual hull.
The same note proves internally that local carrier equality on a degree-one
corridor interval, together with absence of attached pullback components and
conformal endpoint lifts, implies zero endpoint births. KKL's proper
translation region realizes this mechanism in its native Hubbard-tree setting;
the corresponding virtual carrier equality is still open.

### KKL translation-corridor no-birth source lock

KKL26 Proposition 6.5 (`waves-with-Misha.tex`, lines 1254--1261) gives the
exact pullback description for a marked ideal interval \(I\):
\[
 \iota^*I
 =
 \iota^{-1}(I)
 \cup
 \{\text{ideal boundaries of components of }
 \mathcal T'\setminus\mathcal T\text{ attached at }I\}.
\]
KKL Proposition 6.7 (source lines 1279--1286) proves properness on
\(\mathcal L_{[B,q-B-2]}\) from the actual equality
\[
 \mathcal T'\cap\mathcal L_{[B,q-B-2]}
 =
 \mathcal T\cap\mathcal L_{[B,q-B-2]}.
\]
The source proof obtains this equality from parabolic boundedness of the full
cycle of small filled Julia sets. The import is therefore confined to KKL's
native Hubbard-tree category.

`kkl_translation_no_birth_source_audit.md` proves the abstract internal
consequence: endpoint births are supported on attached pulled-carrier excess,
and a bounded terminal attachment window has the exact geometric-sum charge
from the endpoint ledger. It does not import the corresponding theorem for
Dudko's virtual hull. The live virtual obligation is to prove empty attachment
support throughout the degree-one central corridor, bounded access-complete
attachment contribution in the defect windows, and proper/end-proper
relative-cover lifts through every Wave stopping time.

### Canonical interface carrier source boundary

D25, Interpolation Problem 4.4 and the following paragraph, specifies
partially invariant virtual Julia sets only as connected hulls of the
corresponding Cantor small Julia sets containing a finite critical-orbit
segment. It does not specify an inclusion-minimal carrier, a regulated
connector system, attachment traces, protected-access survival maps, or a
component-exhaustion theorem.

The internal pass
`canonical_virtual_interface_carrier.md` proves that these omissions cannot
be filled by formal minimality. Two prescribed points have no least connected
full planar carrier. It further gives a critical-value-free branch of
\(z^2\) whose first pulled excess is an upper half-disk over the immersed
interval; monotone absorption of that excess erases a declared upper
prime-end access. This is an internal analytic counterexample to the proposed
inference, not an imported theorem and not a counterexample to a future
virtual-renormalization construction.

The exact replacement datum is the least finite attachment closure together
with every full attachment trace and the partial survival map on protected
accesses. KKL's native central carrier equality remains the positive control.
No checked public source proves the corresponding connector, survival, or
component-exhaustion theorem for every virtual-Molecule block.

### Root-pullback carrier reduction

D25 supplies no canonical stagewise connector rule. The internal note
`root_pullback_virtual_carrier.md` removes the need for one: for a finite
horizon, one full root continuum and the routed components of all its
iterated pullbacks determine the entire saturated forest. This is an
elementary polynomial pullback theorem and is not attributed to D25, DKL, or
KKL.

The reduction creates three exact checks:

1. each complete required package, not only each atom separately, lies in
   one iterated-pullback component;
2. those components have the prescribed parent map and selected-sheet
   separation; and
3. a target is degree one exactly when it avoids the quadratic critical
   value.

Root enlargement can only merge component classes. Hence adding future data
after selecting fan sheets is invalid without a stability theorem. The
existence of one root satisfying all packages, all routing, the declared
critical word, and admissible virtual localization remains open. This
root-component theorem still does not imply the KKL immersion-carrier
equality or empty attachment support.

### UPTCR source-hypothesis boundary

The formal closure package is recorded in
`mlc_closure_proposition.md`. Its source boundary was rechecked on
2026-07-23 against the complete public HTML versions of D25 and KKL26.

D25, lines 423--429 of the public HTML, labels the target as
“Interpolation Problem 4.4,” describes the virtual Julia sets as connected
hulls of Cantor small Julia sets containing only a finite critical-orbit
segment, and calls the construction a strategy to be developed a priori.
Those lines do not prove any of UPTCR-1--UPTCR-6.

KKL26 Theorem B, both in the introduction and at the proof in Section 7,
states rigidity for sets of **prime primitive** types having both beau
bounds and bounded puzzle Teichmüller diameter. The same introduction
explicitly says that transfer to broader mixed quadratic-like and
\(\psi\)-quadratic-like settings is beyond the article's scope. Thus KKL
Theorem B is a native positive control for UPTCR-6, not a proof of the mixed
tower clause. In particular, neither beau bounds alone nor the UPTCR
backward inequality alone is entered as a rigidity theorem.

The only new proved global statement in this pass is the logical implication
`UPTCR_IMPLIES_MLC`. It uses the internal backward-record lemma, Yoccoz's
complementary theorem, and the parameter-neighborhood conclusion expressly
included in UPTCR-6. `UNIVERSAL_PROTECTED_TOWER_CLOSURE` remains open.

### UPTCR cross-validation addendum

The complementary premise was rechecked directly in Hubbard's 1993 text.
Theorem III states that a parameter in \(\mathcal M\) which is not
infinitely renormalizable has a basis of closed connected neighborhoods in
\(\mathcal M\). Thus the Yoccoz side of `UPTCR_IMPLIES_MLC` has exactly the
relative-neighborhood strength used in the proof.

The UPTCR source and availability check was repeated on 2026-07-23. Targeted
arXiv searches located KKL26 as the newest directly relevant public result,
not a full MLC theorem. No later public proof of Dudko's Interpolation Problem
4.4, unbounded satellite MLC in full generality, or arbitrary mixed-tower
rigidity was located.

The cross-validation corrected three internal overstatements:

1. KKL's Wave mechanism requires the selected degree-two quadratic return
   **and** an auxiliary fan with branches of degrees \(2^m\); “exactly one
   degree-two stage” applies only to the selected return spine.
2. A nonzero sheet, critical, obstacle, access, or localization collision is
   fatal for the current protected core. Bounded defect-window depth controls
   cost only after a replacement local model resolves the collision.
3. The entropy, pseudo-Siegel, and transient/shear routes need only cover the
   blocks. No checked theorem makes them mutually exclusive.

These corrections are internal consequences of
`DEGREE_TWO_FAST_FORWARD_NO_GO`,
`CONNECTED_CARRIER_NO_MINIMUM`, and
`QUADRATIC_PROTECTED_ACCESS_COLLISION`. They do not import or prove an open
UPTCR clause. The exact proof attempt and corrected conditional implication
are in `uptcr_cross_validation.md`.

### Protected regulated connector source pass

The connector pass rechecked Dudko Section 4.5 and KKL Sections 2.5--2.6 on
2026-07-23.

- Dudko defines the virtual objects only as connected hulls of the relevant
  Cantor small Julia sets carrying a finite part of the critical orbit. No
  regulated connector, crosscut-chain survival map, or component-routing
  theorem is stated.
- KKL's native primitive carrier has a canonical Hubbard tree. When the full
  carrier is not locally connected, KKL pass to the locally connected
  rational-lamination model and lift its Hubbard tree. Their Wave marking is
  induced by the sides of this actual tree.

The KKL construction motivates the lamination-lifted candidate
\[
  H_{\rm lam}
  =
  \operatorname{Fill}\bigl(\pi^{-1}(T_{\rm com})\bigr),
\]
but the checked source does not apply that formula to Dudko's partial
virtual-Molecule packages or prove that its fibers and filled components
avoid their protected prime-end collars.

Targeted exact-title, author, “Virtual Molecule,” and “virtual
renormalization” searches found no public Dudko--Kahn--Lyubich construction
paper beyond the cited strategy. Therefore
`VIRTUAL_PROTECTED_ROUTING_CERTIFICATE` is not source-imported.

The new theorem `PROTECTED_REGULATED_CONNECTOR_REALIZATION` is internal: it
proves actual carrier realization, access survival, and univalent naturality
from an explicit protected ribbon-routing certificate. It does not assert
that the virtual dynamics supplies the certificate.

### Protected free-component source pass

The source-availability check was repeated on 2026-07-24. KKL's public
reference list still records Dudko--Kahn--Lyubich, *Virtual renormalization:
interpolating between primitive and satelite regimes*, as “in preparation,”
and targeted arXiv searches located no public replacement. Dudko's
Interpolation Problem 4.4 still supplies only the connected-hull strategy.

The internal note `virtual_protected_routing_domain.md` proves the exact
topological criterion omitted by that strategy. Once the complete finite
root-shadow, protected-collar, obstacle, critical-exclusion, and localization
inventory is frozen, a protected connector exists exactly when one component
of their complement has simultaneous singleton ports to all required atoms.
The proof uses only planar path connectivity, a finite spanning-tree
reduction, and `PROTECTED_REGULATED_CONNECTOR_REALIZATION`.

No public source proves that the actual virtual-Molecule data have this
common component. KKL's native Hubbard tree remains a positive control only
in its published primitive category. Accordingly
`PROTECTED_FREE_COMPONENT_CRITERION` is internal and proved, while
`VIRTUAL_COMMON_FREE_COMPONENT` and
`VIRTUAL_PROTECTED_ROUTING_CERTIFICATE` remain open.

### Augmented-atom common-domain source pass

The source-availability check was repeated on 2026-07-24 after the
free-component reduction.  Dudko Section 4.5 still does not define a typed
collar/obstacle assignment, disjoint fullifications, or explicit surviving
ports.  KKL Sections 2.5--2.6 supply those kinds of data only through their
native complete Hubbard-tree carrier.  KKL's bibliography still lists the
Dudko--Kahn--Lyubich virtual-renormalization work as in preparation, and no
public arXiv version was found.

The only new source import is the arbitrary-compacta form of Alexander
duality recorded as `ALEXANDER_DUALITY_COMPACTA`.  Hatcher's Corollary 3.45
states the locally contractible form; the following discussion on
pp. 256--257 explicitly records the extension to arbitrary compact sets by
using Čech cohomology.  That extension is required because the virtual
root-shadow atoms need not be locally connected.

The internal theorem `AUGMENTED_ATOM_COMMON_DOMAIN` applies this duality
twice.  Each full packet has vanishing first Čech cohomology; finite
additivity over pairwise disjoint packets gives the same vanishing for their
union, so the common complement is connected.  Explicit port arcs then put
all root-shadow atoms in one component of the original free domain.

The dynamical construction of the packet is not imported.  It is recorded
as the open `VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`.  The annular model in
`virtual_common_free_component.md` proves underdetermination of the public
connected-hull data; it is not an actual quadratic virtual-Molecule
counterexample.

### Augmented-packet closure audit addendum

The public-source check was repeated on 2026-07-24 with the locked Dudko
and KKL TeX files.  Dudko's virtual-Molecule paragraph still ends with the
connected-hull strategy.  KKL's native Hubbard-tree construction still
applies to its complete primitive small-Julia cycle, and the cited
Dudko--Kahn--Lyubich virtual-renormalization manuscript remains listed as in
preparation.  An exact-title and author search found no public arXiv
replacement.

The new result `AUGMENTED_PACKET_CLOSURE_AUDIT` is therefore internal and
source-independent.  It proves the closure-operator identities
\[
  \operatorname{Fill}(\operatorname{Fill}(K)\cup L)
  =
  \operatorname{Fill}(K\cup L)
\]
and their finite order-independence consequence.  For a fixed typed
assignment, the final completed packets are unique.  Their actual
seed/bounded-chamber intersections record every post-fill merger, and
monotonicity makes merger and localization defects persistent under
same-label enlargement.

The same audit isolates the exact port condition: the original atom must
contain an unprotected point admitting an actual Jordan access arc from the
complement of its completed packet.  Once each individual access exists,
finite compact separation lets the arcs be truncated in pairwise disjoint
packet neighborhoods.  Thus global port-arc crossing is not an additional
obstruction.  No local connectivity or numerical width estimate is used.

What remains source-open is not a choice of completion order.  It is the
actual virtual dynamical input `VAAPC-I`, zero unique-closure collision
`VAAPC-C`, unprotected exposure `VAAPC-P`, complete-horizon transport
`VAAPC-H`, and uniform incidence/compression `VAAPC-U`.

### VAAPC-I horizon and source-adequacy addendum

The source-availability check was repeated on 2026-07-24 against the same
hash-locked TeX files and the current arXiv submission records.  Dudko
arXiv:2512.24171 and KKL arXiv:2606.27272 still have only version 1.  Fresh
exact-title, author, and phrase searches located no public
Dudko--Kahn--Lyubich virtual-renormalization manuscript.

Dudko TeX lines 875--881 define the combinatorial virtual-Molecule copy
chain and its two subcases.  Lines 885--892 explicitly present the Virtual
Molecule regime as an interpolation problem and propose connected hulls of
Cantor small Julia sets containing the critical orbit for an “appropriate
number” of first returns.  The source does not define that number, a
stopping rule, or a stopping interface.

This is the first failed `VAAPC-I` source field.  Without a final stage,
“through last proof use” has no endpoint and the stagewise component,
collar, obstacle, access, and transport records cannot be enumerated.
The source also does not provide the later typed fields: stage
localizations, selected branches, a virtual Wave proof ledger, dependency
edges, packet labels, or final-root-enlargement stability.

KKL TeX lines 514--557 and 750--765 provide these kinds of objects in their
native primitive category through the complete Hubbard tree and its induced
ideal marking.  Transport to the partial virtual carrier would require a
typed component/access bridge commuting with every selected branch and
preserving proof-use dependencies.  The checked source does not construct
that bridge; KKL line 381 instead points to the virtual-renormalization work
as forthcoming.

The internal
`HORIZON_FIRST_INVENTORY_AUDIT` proves the finite dependency-closure theorem
and the exact horizon-extension stability criterion.  It does not supply
the actual horizon.  That first replacement input is recorded as the open
`VIRTUAL_WAVE_HORIZON_CERTIFICATE`; `VAAPC-I` and all later virtual clauses
remain open.

### Virtual Wave stopping and marked-correspondence addendum

The KKL Wave section and its ideal-marking appendices were audited
line-by-line against the hash-locked v1 TeX on 2026-07-24.  The complete
direct citation universe of TeX lines 1142--1797 contains 53 internal
`\ref`/`\eqref` labels and one bibliography key.  The list and definition
lines are recorded in `virtual_wave_horizon_certificate.md`, Section 6.

KKL's native stopping logic is explicit at theorem-call level after its
interval-growth premise is supplied.  A wide controllable wave is first
replaced by a short wave unless it is terminal.  Each later nonterminal
alternative is a critical visit.  KKL lines 1334--1342 set the proposed
forbidden chain length to
\[
  N_b=216b^2.
\]
Conditional on `KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR`, the recursion
stops before it forms a chain of \(N_b\) waves.  The arithmetic after that
growth implication is valid; the implication itself is not yet proved.
This constant is not uniform in \(b\): KKL line 1149 explicitly allows
every constant in the Wave section to depend on the fixed parabolic bound.

KKL lines 1707--1709 provide the actual native marked stage pair
\[
 (f^r,\iota_r):
 f^{-r}(U)\setminus f^{-r}(T)\rightrightarrows U\setminus T,
 \qquad
 (f^r)_*\iota_r^*I=F_*^rI .
\]
The interior fast-forward branch contains both a degree-one translation
part and degree-\(2^m\) auxiliary ends (lines 1740--1743); it is not a
globally univalent corridor.  The source proof also contains an undefined
exponent \(n\) at line 1789 where the local iterate is denoted \(N\), and
line 1260 contains malformed self-referential wording.  The audit records
these v1 defects and does not silently repair them.

The internal `RESOLVED_FINITE_WAVE_HORIZON_COMPILER` proves finite stopping,
least proof-use closure, and order-independent simultaneous final-root
closure after actual marked branches and a finite dependency universe have
been supplied.  The checked virtual sources do not supply the corresponding
marked carrier complement, ideal marking, covering/immersion pairs, or
proper/end-proper interval action.  The first replacement theorem is
therefore the open `VIRTUAL_WAVE_MARKED_CORRESPONDENCE`.  It is formulated
as a horizon-independent schema over a prefix-closed admissible word
language and finite provisional root packages; formulating it only for
“proof-used words” would be circular.

This addendum promotes no virtual analytic statement.

### Virtual marked-correspondence boundary-action addendum

The public source boundary was rechecked for the next gate.  Dudko TeX
lines 875--892 do not define a typed return graph, actual branch
localizations, or a marked complement.  KKL TeX lines 2062--2141 define
covering/immersion pairs and require
\[
  g^*I\ \text{to refine}\ \iota^*I
\]
before the pair acts on a marking.  KKL lines 1707--1709 prove this in the
native Hubbard-tree pullback model, not for a virtual-Molecule carrier.

The new internal proof
`virtual_wave_marked_correspondence.md` does not import a missing source
theorem.  It proves:

1. prefix closure for the paths of any actual typed return graph;
2. an unmarked polynomial complement pair from a full carrier containing
   all critical values and invariant under the return;
3. the exact endpoint criterion
   \(E^\iota\subset E^g\) for marking refinement; and
4. naturality under analytic commuting squares and exact protected-endpoint
   inverse images.

The exterior-disk phase example proves that the previously listed generic
inputs do not determine the marked action.  Accordingly the source-facing
gap is split into `VIRTUAL_RETURN_BRANCH_LANGUAGE`,
`VIRTUAL_PROVISIONAL_COMPLEMENT_PAIR`, and
`VIRTUAL_ACCESS_ACTION_CERTIFICATE`.  No checked source discharges any of
these three statements.

### Virtual return-base and demand-schema addendum

The first marked-correspondence subgate was audited further in
`virtual_return_branch_language.md`.

Dudko TeX lines 264--268 define return time relative to a selected
eta-neighborhood, and lines 290--291 globalize an iterate only after such a
return has been selected.  The later virtual paragraph, lines 875--892,
provides no corresponding open return localization.  Thus its phrase about
first returns does not determine a return-time function or a connected
analytic branch component.

KKL TeX line 381 refers the virtual construction to `DKL:virtual`.
The locked bibliography file
`macros/everything.bib`, SHA-256
`1C4224148A52F81A9BD3DAE08B11E10564E6ADD79360E15532F4F03E527B8FD7`,
records that item as unpublished and "In preparation."  Exact-title and
author searches on the source-lock date located no public primary
manuscript.  No result from it is imported.

The mathematical underdetermination is independently checked by
\(f(z)=z^2-1\): the seed \(-1\) returns in two iterates to
\(D(-1,1/4)\) and in one iterate to \(D(-1/2,3/4)\).  Consequently the
first new source-facing datum is `VIRTUAL_RETURN_BASE_ATLAS`, followed by
the horizon-independent `VIRTUAL_WAVE_DEMAND_SCHEMA`.

The internal atlas compiler and enlargement-naturality theorem are proved.
They do not construct either source-facing input.  In particular, an
injective enlargement morphism proves persistence of old words but not the
absence of newly demanded words; complete stability requires a bijection on
demanded branch-component pairs.

### Native principal-nest return atlas and virtual-selector addendum

Lyubich's arXiv source `math/9503215` was locked on 2026-07-24:

```text
source-lock/Lyu97/source.tar
SHA256 F799BDC011BEE5F89A467F7C24AFB3C53D0AE556FE7822952A0DE8ADD141FF16
```

The precise imported ranges are `nest.tex` lines 500--532, 577--619,
904--949, and 975--1005.  They construct the native Markov puzzle,
principal-nest pullbacks, nice first-return components, and the
degree-two-central/degree-one-lateral dichotomy.

The derived theorem in `virtual_return_base_atlas.md` uses the open
interior \(B_n=\operatorname{int}V^{n-1}\), proves niceness from the
source's stronger boundary avoidance, and records actual branch
components, integer iterates, chronological degree words, component
itineraries, Jordan prime-end markings, and external-angle phase.  Its
scope is a specified native principal-nest level.

The virtual source audit remains negative at the next bridge.  KKL lines
299--315 give the parameter-copy chain and virtually-satellite
classification; KKL lines 1803--1809 give the terminal Yoccoz
renormalization level.  Dudko lines 875--892 describe the intermediate
virtual-Molecule scales.  None of these ranges supplies a map from an
intermediate chain index to an embedded nice puzzle/principal-nest base or
proves placement of the virtual carrier and proof-used access package in
that base.

KKL line 504 is also insufficient for this purpose: its neighborhood
\(U_I\) is chosen only up to isotopy relative to the small Julia cycle.
The explicit concentric-disk calculation for \(z^2-1\) shows that a
relative-isotopy class need not determine first-return time.

The exact next source-facing datum is therefore
`VIRTUAL_SCALE_TO_PUZZLE_SELECTOR`.  The native atlas is a positive control,
not a promotion of `VIRTUAL_RETURN_BASE_ATLAS`.

### First decoration-scale selector addendum

The next pass source-locked the two Kahn--Lyubich inputs needed to test the
first satellite scale in the original connected dynamical plane:

```text
Kahn--Lyubich Decorations, arXiv:math/0609046
source.tar  SHA256 DA8FCF924793267421F80BE3E17CD7EB2B72CD4F5B08E3F5A38E2161EC608234
kingdom.tex SHA256 5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7

Kahn--Lyubich Modified Principal Nest, arXiv:math/0505194
source.tar  SHA256 03221A00D020656BA3470E7F4C985CF613C4F26B1C766BFA87BA7A6D1A7B0C7F
kingdom.tex SHA256 2DF0B51CB7DC8BB421AD72684F187D3502A7CA8599F10CDF9DAC9A7E844253BA
```

For a parameter in a fixed non-principal decoration outside a directly
attached satellite copy \(M_{p/q}\), the source defines the least integer
\(n\) for which \(f^{nq}(0)\) enters an off-critical \(Z^1\)-piece and
constructs

\[
V_{\rm esc}=f^{-nq}(Z^1_\kappa)|_0=Y^{nq+1}.
\]

The first direct-decoration scale therefore has the actual selector
\(\nu_{\rm dec}(1)=nq+1\).  The GPL source supplies its actual compactly
contained first-return components and exact iterate restrictions.  The
derived proof in `virtual_scale_to_puzzle_selector.md` establishes the
chronological degree words and native branch prime-end markings.

Two obstructions prevent promotion of the universal selector.

1. At the terminal primitive first-return map
   \(f^P:A_0\to B\), every intermediate little Julia set
   \(K_i=f^i(K_0)\), \(1\le i<P\), lies outside the open critical base
   \(B\).  The first excluded component is \(K_1\).  Thus a complete cycle
   requires the actual multi-base chain of intermediate domains, not one
   critical puzzle piece.
2. The raw decoration separator \(Y^{(n-1)q+1}\) has exactly \(2^n\)
   vertices and one pairwise-disjoint pullback \(Q^v\) per vertex.  A
   complete raw fan marking is therefore not uniformly bounded in \(n\).

The checked sources still do not choose a connected continuum in \(J(f)\)
joining the primitive little Julia sets.  Consequently the first
attachment access of \(K_1\) remains an undefined analytic witness, not a
zero collision coordinate.  Nor do the sources prove a future-faithful
compression of the \(2^n\) raw records or that a universally bounded
subset is complete for every later proof use.  The first-scale escape atlas is
therefore a proved skeleton, not `VIRTUAL_SCALE_TO_PUZZLE_SELECTOR`.

### Direct-decoration compactification and referee-repair addendum

The source relates its two advertised branch granularities: after defining
\(g=f^q|_{Q_L\cup Q_R}\), it identifies the \(2^n\) pieces \(Q^v\) as the
components of \(\operatorname{dom}(g^n)\).  Thus a \(Q^v\) is a
length-\(n\) binary cylinder, not an unrelated branch family.  This
relation does not license silent switching between the binary alphabet
with step \(f^q\) and the macrobranch alphabet with step \(f^{nq}\);
contact, phase, protected-marking, and state-dimension claims must be
proved at the chosen granularity.

The direct-decoration pullback package is derived only from the source's
actual closed Jordan pullbacks and proper degree-one restrictions.  The
closed sibling sets are disjoint: a common regular boundary point would
admit a unique local inverse of \(f^q\), contradicting the selection of two
different inverse branches.  Proper degree one between the closed Jordan
pieces supplies the boundary homeomorphisms used in the component proof.
These are explicit hypotheses and deductions, not consequences of
interior disjointness alone.

For finite non-root and infinite addresses, the analytic action is the
partial first-symbol deletion map \(\sigma_{\rm pre}\).  The empty address
has a separate terminal-cycle arrow \(\tau_{\rm root}\).  The safe-gap
enlargement theorem is only a topological finite-fiber result; it does not
assert fullness, protected-access survival, or analytic carrier
admissibility.

The internal theorem
`FINITE_CYLINDER_COMMUTING_ITERATE_LIFT` uses no additional external
source.  If \(h_w=f^N|_{Q_w}\) and \(h_v=f^N|_{Q_v}\) are equal-depth
homeomorphisms, \(F=f^r|_A\), and the actual containment
\(f^r(h_w^{-1}(A))\subset Q_v\) is known, commutation of polynomial
iterates proves

\[
 f^r|_{h_w^{-1}(A)}=h_v^{-1}\circ F\circ h_w.
\]

The theorem does not select \(v\).  No checked source supplies the required
component-level target existence, uniqueness, prefix compatibility,
partial-shift compatibility, root rule, or marked enlargement
naturality.  These fields are the open
`VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR`, upstream of
`VIRTUAL_DISCONNECTED_MARKING_TRANSFER`.

The complete post-referee dispositions and source hashes are recorded in
`referee_issue_resolution_20260724.md`.  In particular, KKL carrier
naturality is imported only in the restricted form

\[
 \mathcal T'\cap\mathcal L_{[B,q-B-2]}
 =
 \mathcal T\cap\mathcal L_{[B,q-B-2]},
\]

never as global equality of the two carriers.

## Research Push II source-boundary addendum

The Push II packet was audited on 2026-07-24 against the live public arXiv
records and the locked local TeX sources.  The complete artifact inventory
and disposition are in
`research_push_2_assessment_and_integration.md`.

### Public-source status

- Dudko, arXiv:2512.24171, Section 4.5 states Interpolation Problem 4.4
  and describes partially invariant virtual Julia sets as a proposed
  strategy.  It does not construct a scale-two root branch
  \(F=f^r:A\to B\), its protected marking, a relative-cover telescope, or
  an end attachment.
- KKL, arXiv:2606.27272, Section 1.3 classifies the virtually-satellite
  case and lists virtual renormalization in its future perspective.  Its
  proved \(\psi\)-ql results are used only in their native categories.
  The v1 Wave amplification theorem is source-stated but not
  project-certified for the two proof gaps recorded below.
- Kahn--Lyubich Decorations, arXiv:math/0609046, supplies the already
  imported direct-decoration ray/equipotential puzzle and the two actual
  univalent pullbacks.  It does not prove that every nested direct-
  decoration fiber equals one prime-end impression.
- Kahn--Lyubich, arXiv:math/0505194, supplies the already imported native
  generalized polynomial-like return construction.  It does not select
  the next virtual portrait.

### Retimed-pair type correction

For a KKL-style pair
\[
 (g_w,\iota_w):(U_w,K_w)\rightrightarrows(B,K),
\]
the target \(K\), rather than the pulled source \(K_w\), is the filled
Julia set in the \(\psi\)-ql terminology.  The retimed theorem proves
\[
 g_w^{-1}(K)=\iota_w^{-1}(K)=K_w.
\]
It does not turn \(K_w\) into the target of a word-indexed self-return.

### Prime-end source limit

The checked decoration source uses multiple rays and a separator with
many vertices.  It does not supply either:

1. a single compatible affine angular inverse lift across every exterior
   component used by a word; or
2. a cofinal fundamental-chain theorem identifying a nested puzzle fiber
   with the impression of the limiting angle.

Consequently `DIRECT_DECORATION_END_PRIME_END_COFINALITY` remains open.
Even its future proof would not establish protected access survival
through collars, obstacles, and final-root enlargement.

### Corrected local hash

The checked principal-nest file is

```text
source-lock/KL09/
  kingdom.tex
SHA-256
2DF0B51CB7DC8BB421AD72684F187D3502A7CA8599F10CDF9DAC9A7E844253BA
```

An earlier occurrence in
`virtual_cantor_pullback_compactification.md` omitted the substring
`E844253BA`; that documentation typo is corrected.  The file itself was
unchanged.

## Research Push III source boundary

The external Push III archive is locked at
`external_inputs/push_3_20260725`; its archive SHA-256 is
`D6A2B5074CF55AB7983AE0E835A4F38B5388DFB4043B3A57E254C9A6EED2DD62`.
The complete theorem-by-theorem audit is
`research_push_3_assessment_and_integration.md`.

The direct-decoration sources license the already recorded inverse branches.
They do not import:

1. the packet's intrinsic scale-two pseudo-puzzle atlas;
2. its protected serial-neck certificate;
3. marked finite-horizon assembly;
4. scalar collapse of analytic cut cross-sections; or
5. a strict transition for every mixed block.

The normalized direct limit is therefore proved only as a coordinate limit
of an independently supplied root portrait.  Its conformal observable
identity is exact in that scope.  The series estimate is conditional on
explicit intact walls and no bypass.  The scalar nodal-response step is not
source-imported and is obstructed by nonconstant cylinder trace modes.

## Research Push IV source boundary

The external Push IV directory is locked at
`external_inputs/push_4_20260725`.  Its complete file-hash manifest and
theorem-by-theorem disposition are in
`research_push_4_assessment_and_integration.md`.

The elementary full-trace rectangle formula, exact variational semigroup,
sharp trace-renormalized comparison, compact half-cylinder limit, and
Hilbert-trace elimination lemma are proved internally.  They are not
imported from Kahn--Lyubich.

Kahn--Lyubich Decorations, arXiv:math/0609046, supplies the actual
direct-decoration puzzle pieces and univalent branches already used by
`DIRECT_DECORATION_PULLBACK_COMPACTIFICATION`.  It does not state that the
physical region between a parent equipotential arc and its dynamically
pulled child is a rectangle with those full arcs as matching trace
interfaces.

The exact Böttcher model shows why this cannot be inferred.  Under
\(z\mapsto z^{2^q}\), inverse pullback divides angular width by \(2^q\).
Thus a nondegenerate full parent arc and its full pulled child cannot be the
two equipotential sides bounded by the same two rays.  The missing angular
footprint produces additional boundary or trace-port data.

Consequently no source licenses the proposed
`BOTTCHER_TRACE_COLLAR_ATLAS` or the promotion of
`END_PLUMBING_TRACE_RESPONSE_CONTROL`.  The explicit replacement source-
facing gate is `DIRECT_DECORATION_TRACE_COLLAR_REALIZATION`.

## Side-research source addendum

The 2026-07-25 side-library intake adds the following locked source
boundaries.  Full disposition and the rejected claims are recorded in
`side_research_library_assessment_and_integration.md`.

### Fatou basin critical-cycle theorem

Lukas Geyer's *Complex Dynamics* course notes, Corollaries 11.6 and 11.8,
record the standard facts used in the primitive-root local calculation:
the attracting petals of a parabolic germ correspond to immediate
parabolic basin data, and every cycle of immediate attracting or parabolic
basin components contains a singular value.  For a polynomial there are no
finite asymptotic values, so a finite parabolic basin cycle contains a finite
critical point.

Source:
<https://www.math.montana.edu/geyer/2016-fall-m597/materials/s2016-complex-dynamics-notes.pdf>.

This import is used only to prove that the quadratic germ
\(g(w)=\lambda w+w^2\), for primitive \(\lambda^q=1\), has one cycle of
\(q\) petals.  It supplies no global satellite or parameter theorem.

### BLOT Theorem B annulus distinction

Under the exact hypotheses of BLOT Theorem B---fixed-degree rational maps
converging to a limit, polynomial-like renormalizations
\(f_n^{q_n}:U_n\to V_n\) with connected \(K_n\), Hausdorff convergence to a
nondegenerate compact \(K\), \(q_n\to\infty\), and no parabolic periodic
domain of the limit containing \(K\)---the conclusion is

\[
\operatorname{mod}(U_n\setminus K_n)\longrightarrow0.
\]

The Lavaurs example later in the same paper instead retains a lower bound on
the different outer annulus
\(\operatorname{mod}(V_n\setminus U_n)\).  These quantities are not
interchangeable.  The exact source anchors and local hash are in
`unbounded_satellite_modulus_source_reaudit_20260726.md`.

### Satellite subclass theorems

The following imports narrow the unbounded-satellite complement but do not
exhaust it.

1. **Cheraghi--Shishikura.**  Theorem D of
   [arXiv:1509.07843](https://arxiv.org/abs/1509.07843) applies to
   \(\mathcal QG_N\), with
   \[
   b_{1,1}\ge N,\qquad
   b_{i,j+1}\ge b_{i,j}^2,\qquad
   b_{i+1,1}\ge q_i^2.
   \]
   There are \(C<\infty\) and \(0<\lambda<1\) for which the depth-\(n\)
   parameter prefix set has diameter at most \(C\lambda^n\).  The source
   concludes combinatorial rigidity and MLC at an infinitely
   satellite-renormalizable parameter with that combinatorics.  The objects
   are prefix parameter sets, not "finite fibers."  Printed source location:
   pp. 5--6, Theorem D.

2. **Levin, Theorem 1.**  In
   [arXiv:0710.4406v4](https://arxiv.org/abs/0710.4406), for simply
   renormalizable selected periods \(n_m\) and separating-fixed-point
   rotations \(p_m/q_m\),
   \[
   \limsup_m\frac{\log|p_m|}{n_m}>0
   \]
   implies MLC at the parameter.  If all selected renormalizations are
   satellite, the weaker condition
   \[
   \limsup_m\frac{\log q_m}{n_m}>0
   \]
   suffices.  Printed source location: pp. 1--2.

3. **Levin, Theorem 2.**  For the all-satellite cascade,
   \[
   q_m\to\infty,\qquad
   \limsup_m |t_m|^{1/q_{m-1}}<1,
   \]
   equivalently
   \(\limsup_m|t_{m+1}|^{1/q_m}<1\), imply convergence, MLC at the
   infinitely renormalizable limit, and non-local connectivity of its Julia
   set.  Printed source location: pp. 3--4.

4. **Levin, Theorem 7.**  With \(t_m=p_m/q_m\), the exact conditions are
   \[
   \sup_{m\ge1}|t_m|q_0\cdots q_{m-1}<\infty \tag{Y0a}
   \]
   and
   \[
   \inf_{m\ge2}
   \frac{\log\!\left(|p_{m-1}q_{m-1}|/|t_m|\right)}
        {q_0\cdots q_{m-2}}>0. \tag{Y0b}
   \]
   These imply convergence.  If, for some \(\beta>0\),
   \[
   \limsup_m
   \frac{q_m}
        {\max\{(q_0\cdots q_{m-1})^2,
        \exp(\beta q_0\cdots q_{m-2})\}}>0, \tag{Y1}
   \]
   MLC holds at the limit.  The separate condition `(S)` concerns the Julia
   set, not the MLC conclusion.  Printed source location: pp. 10--11.

5. **Kahn--Lyubich, Elephant Eyes.**  The a-priori-bound theorem in
   [arXiv:2601.21905](https://arxiv.org/abs/2601.21905) is imported only
   for the exact E1--E3 class: an even quadratic-like map with connected
   Julia set and repelling fixed points, rotation \(1/q\), the stated central
   little-Julia uniqueness, and \(p=q+b\) with bounded \(b\).  Section 8's
   parameter argument invokes little Mandelbrot copies on
   Ecalle--Voronin cylinders and cites `[DLP]` as in preparation.  That
   cylinder-copy input and the resulting parameter conclusion are not
   independently imported here.

Lim's public sector-renormalization note,
[arXiv:2607.11408v1](https://arxiv.org/abs/2607.11408), reports a neutral
attractor rigidity theorem as `[DLL26]`, *Rigidity of the attractor of
neutral quadratic polynomials*, "2026. Manuscript."  The full DLL26 proof
was not publicly available in the audited sources.  The result remains
reported context, not a ledger import.

## Research Push VI source boundary

The Push-VI audit rechecked the exact binary direct-decoration input in
Kahn--Lyubich, *A priori bounds for some infinitely renormalizable
quadratics. II. Decorations*,
[arXiv:math/0609046](https://arxiv.org/abs/math/0609046).

The source supports:

- closed topological puzzle disks (`kingdom.tex`, lines 28 and 32);
- finite external-ray/equipotential boundary arcs (lines 45--48);
- \(P=Y^{(n-1)q+1}\) with two univalent \(f^q\)-pullbacks
  \(Q_L,Q_R\subset P\) (lines 116--118 and 133--137); and
- the binary restriction \(g=f^q|_{Q_L\cup Q_R}\) and its iterated
  pullback components (lines 150--154).

These facts authorize the finite nested chains used in
`BINARY_DIRECT_DECORATION_NESTED_SEPARATOR_CALCULUS`.  They do not supply a
finite branch-invariant boundary atomization, a protected overlay, a common
trace topology, or a compact response cocycle.

In particular, the claimed Push-VI atom maps are not a source theorem.
On a shared external ray, Böttcher height is multiplied by \(2^q\) under
\(f^q\).  A finite partition atom adjacent to the fixed landing point maps
across its first positive cut, so it cannot map to a single atom of the same
partition.  The source-compatible survivor is an exact set image, pending a
separately constructed one-to-many incidence/restriction atlas.

The standard planar Sobolev trace theorem is used only after an interface is
proved Lipschitz or otherwise admissible.  A survey reference for the
Lipschitz \(H^1\) trace setting is Lamberti--Provenzano,
[arXiv:1910.03971](https://arxiv.org/abs/1910.03971).  It does not turn an
arbitrary Jordan or prime-end boundary into an admissible trace interface,
nor does it construct the dynamical overlay.

## Research Push VII source refinement

The same Kahn--Lyubich source closes the fixed-block **structural** binary
contact calculation more strongly than Push VI used it.

- The \(2^n\) vertices of \(P\) contain all specified \(f^{qm}\)-preimages
  of \(\alpha\) (`kingdom.tex`, lines 116--118).
- The binary branches \(Q_L,Q_R\) are the two univalent \(f^q\)-pullbacks
  inside \(P\) (lines 133--137).
- Every vertex \(v\) has one pairwise-disjoint depth-\(n\) binary pullback
  \(Q^v\) attached to the two \(P\)-boundary rays landing at \(v\)
  (lines 140--155).

Together with the already audited closed-disjoint Jordan branch
compactification, these facts imply the exact contact recursion, pairwise
cylinder-contact formula, prefix endpoint itinerary, and post-depth-\(n\)
two-state structural skeleton recorded in
`FIXED_BLOCK_BINARY_CONTACT_AUTOMATON`.

The submitted alternating ray/equipotential boundary word is not a source
encoding.  Kahn--Lyubich's combinatorial boundary model explicitly
distinguishes consecutive rays meeting at one vertex from rays joined by an
equipotential (`kingdom.tex`, lines 293--301).  Any source compiler must
retain this connector type and landing equivalence.

For pseudo-pieces, `psiql.tex` constructs the Riemann surface by paths or
universal-cover gluing (lines 95--123), proves covering and immersion
naturality (lines 169--207), describes the finite ideal-boundary arcs
(lines 231--244), and gives continuous boundary extension (lines 248--253).
The same passage warns that an inclusion immersion need not send source
boundary into target boundary.

These source results do not define \(H^1_{\rm fin}\) on a pseudo-piece,
prove bounded trace or extension operators on its ideal arcs, establish
closed compatible trace quotients, construct a Dirichlet-to-Neumann form,
or identify the dynamical covering boundary with the inclusion-immersed
boundary.  Those remain analytic proof obligations.

The fixed-tree Value factorization in
`FIXED_KKL_PAIR_STATE_MOMENT_FACTORIZATION` is an algebraic regrouping of
the checked KKL formula in `.tmp_wave_audit/value1.tex`, especially lines
67--90 and 103--111.  It does not import a binary-to-Hubbard incidence map,
a universal terminal-tree bound, or a strict transition.

## Research Push VIII source refinement

The Push-VIII audit rechecked the proposed pulled/immersed interface against
the same Kahn--Lyubich decoration source and against the ideal-marking
appendix of Kahn--Kapiamba--Lyubich.

The locked Kahn--Lyubich files are:

```text
kingdom.tex
  SHA256 5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7
psiql.tex
  SHA256 6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF
```

`kingdom.tex` lines 133--155 supply the two actual univalent
\(f^q\)-pullbacks and their finite binary iterates.  `psiql.tex` lines
95--123 construct the pseudo-pieces, lines 169--207 induce a covering from
a puzzle covering and an immersion from a puzzle inclusion, and lines
231--253 describe the finite pseudo-boundary arcs and continuous immersion
extension.  The last passage explicitly warns that the immersed source
boundary need not lie in the target boundary.

These facts do not prove the submitted finite label-hull formula for an
immersion pullback.  KKL define an ideal marking and its end-intervals at
`waves-with-Misha.tex` lines 1844--1865, path subordination at lines
1867--1869, and \(\iota^*X\) at lines 2081--2097 by quantifying over proper
target paths, unique proper lift components, and subordination homotopies.
A table that records only a proper target atom or a nonproper symbol does
not record that lift relation, the relative-cover subgroup, monodromy, or
the required homotopy data.  The Push-VIII proof instead reasons from a
source path to its image, reversing the defining KKL implication.

KKL's native component description at lines 1240--1271 does reduce the
path definition to an explicit union, but only after using the actual
Hubbard-tree inclusion, injectivity near the filled carrier, and the
Caratheodory boundaries of every component of
\(\mathcal T'\setminus\mathcal T\).  No corresponding component-exhaustion
theorem is present in the checked pseudo-piece source.  Thus the submitted
boundary labels do not realize \(\iota^*\mathcal I\).

The end-proper test has a separate source-level error.  KKL lines
2157--2159 require properness on the complete end-intervals of the
multi-interval in \(f^*\mathcal I\).  Testing only the first and last
micro-atoms is weaker: a single covering interval can have proper outer
micro-atoms and a nonproper middle.  The supplied successful fixture is
also not an analytic covering atlas: for example, its first atom is said
to map homeomorphically to \(M_0\), while both of its recorded covering
endpoint images are \(0\).  The randomized compiler audit therefore
validates its declared finite predicate, not realizability by the
degree-one direct-decoration cover.

The proposed generic word law is likewise not source-imported.  A
covering/immersion pair is a span, and consecutive pull--push
correspondences compose through a fiber product with an interchange
condition.  KKL lines 1707--1709 identify \(F_*^n\) with
\((f^n,\iota_n)\) only in their native iterated-inclusion model.  They do
not license componentwise multiplication of independently typed
pull--push trace operators.  Analytic enlargement squares also do not by
themselves exclude new sheets, new pullback components, or a new
nonproper bridge.

Two narrow results are retained:

1. `FINITE_LINEAR_LABEL_MARKING_ENUMERATOR` proves the interval-convex
   closure and exhaustive coarsening theorem after the deletion-and-seed
   hull is declared as part of an abstract finite label model.  It makes
   no KKL or analytic-realization claim.
2. `PULL_PUSH_WELDING_WORD_COMPOSITION_NO_GO` records the exact typing and
   noncommutation obstruction and the need for a fiber-product or
   Beck--Chevalley interchange certificate.

The action-versus-trace endpoint separation is retained as a no-laundering
documentation rule, not as an analytic construction theorem.  No proposed
Push-VIII trace, welding, slit, normalized-word, final-root, or
fixed-horizon completion theorem is imported from the checked sources.

After this split the authoritative ledger has 300 obligations:
23 imported, 214 proved, and 63 open.  The complete marked contact,
trace-collar, welding, end-plumbing, virtual marked correspondence, Wave
horizon, H2, MBTT, VAAPC-I, UPTCR, rigidity, and MLC gates all remain open.

## Fixed direct-decoration path-lift and collar refinement

The source-specific analytic pass is documented in
[`direct_decoration_path_lifted_collar_certificate.md`](direct_decoration_path_lifted_collar_certificate.md).
Its chain of custody is locked to the official arXiv sources as follows:

```text
Kahn--Lyubich, arXiv:math/0609046, official source archive
  .tmp_kl08_source.tar
  SHA256 DA8FCF924793267421F80BE3E17CD7EB2B72CD4F5B08E3F5A38E2161EC608234
  kingdom.tex
  SHA256 5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7
  psiql.tex
  SHA256 6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF
  moduli.tex
  SHA256 CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E

Kahn--Kapiamba--Lyubich, arXiv:2606.27272v1
  waves-with-Misha.tex
  SHA256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

**Superseded historical claim; not a theorem.**  An earlier version of
Theorem 4.1 claimed that, for either fixed direct-decoration branch
\(g=f^q|_{Q_a}:Q_a\to P\), the inclusion-induced pseudo-piece immersion
\(\boldsymbol\iota_a:\mathbf Q_a\to\mathbf P\) was an interior holomorphic
embedding.  The proposed proof identified complementary components and
then asserted that the degree-one map on each annular tile had an
injective universal-cover lift.  That assertion silently replaced the
bold ambient annulus immersion by a physical nested-annulus inclusion.
For a degree-one annulus immersion, lift injectivity is equivalent to
base-annulus injectivity; winding degree one alone proves neither.
Consequently the four-case quotient check never acquired its required
same-tile injectivity hypothesis.  The claim was retracted and
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING` remains open.  The corrected
source audit and exact abstract no-go certificate are recorded below.

The pass also locates the first remaining source-specific obstruction.  Put
\(\Omega=\boldsymbol\iota_a(\mathbf Q_a)\).  For each nonproper source
ideal side \(E\), let \(C_E\) be the adjacent component of
\(\mathbf P\setminus\Omega\), and define

\[
 \Phi_{\rm acc}(E)=
 \{x\in\partial_i\mathbf P:
   \text{a proper arc in }C_E\text{ joins the }\Omega\text{-side }E
   \text{ to }x\}.
\]

The first unresolved \(C_E\) is adjacent to an immersed
deeper-equipotential outer side.  The checked KL construction does not
exclude that this component passes through a target-tile overlap and
reaches more than one target port.  If \(\Phi_{\rm acc}(E)\) meets two
distinct target marking intervals and the required extensions can be made
with no further intersection with \(\Omega\), a small source crosscut
subordinate to \(E\) has target proper extensions through \(C_E\) to both
intervals while remaining their unique proper source intersection.  KKL's
universal proper-path definition then forbids assigning \(E\) separately
to either pullback.  Conversely, absorbing \(E\) into one pullback requires
proof that every such extension has its entire footprint in that one
target multi-interval.  Neither `kingdom.tex` nor `psiql.tex` computes
these footprints, proves the no-further-intersection clause, or supplies
the required exclusion crosscuts; the one
special port in `moduli.tex` is not an all-port exhaustion theorem.
Therefore single-footprint complement exhaustion, based-sheet and
subgroup data, and whole-end properness remain an actual analytic gate,
not a finite-label inference.

The original pass proposed three promotions:

- `DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING` (subsequently retracted);
- `KL_TILE_INTERIOR_HOMOGENEOUS_TRACE`; and
- `NONPROPER_LABEL_HULL_PULLBACK_NO_GO`.

Its path-lift node remains open:

- `DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`.

A subsequent same-tile audit found that the embedding proof treated the
bold ambient immersion as a physical annulus inclusion.  The corrected
status is recorded below; these historical counts are not authoritative.

## Outer-port footprint and conformal ideal-boundary resolution

The follow-up proof is documented in:

```text
embedded_disk_accessible_footprint_theorem.md
direct_decoration_outer_port_footprint.md
```

It adds Kahn I to the fixed-branch source lock:

```text
Kahn, arXiv:math/0609045, official source archive
  .tmp_kl06_source.tar
  SHA256 3A63FC9773DB8B60ED4A0EB9A1C551E6F66C08E66AB92C36F4E2B482570AB817
  wad.tex
  SHA256 B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580
```

The exact source chain is now closed:

1. `wad.tex`, lines 169--175, defines the ideal boundary from the disk
   universalization and deck limit set.
2. `psiql.tex`, lines 95--161, gives the finite-star pseudo-piece
   gluing.  The physical puzzle piece is a closed Jordan domain, so the
   open van Kampen cover uses \(\operatorname{int}Y\) and the open tile
   images.  `kingdom.tex`, lines 56--62, and `psiql.tex`, lines 139--160,
   show that the omitted vertices are the only missing central-boundary
   points and every other such point belongs to a tile.  A Schoenflies
   collar pushes paths in each \(Y_i\) off the remaining Jordan-boundary
   arcs, making every nonempty central--tile intersection
   path-connected.  Repeated van Kampen makes the surface simply
   connected.  If its bold target disk uniformizes as \(\mathbb D\),
   Liouville excludes a plane
   source; if the target uniformizes as \(\mathbb C\), the path-space
   projection omits at least two vertices in \(S_Y\), so Little Picard
   excludes a plane source.  Hence the pseudo-piece is a conformal disk.
3. In the trivial deck-group case Kahn's ideal closure is the closed
   disk.
4. `psiql.tex`, lines 231--253, names
   \(\lambda,\xi,\eta\) as a tiling of that ideal boundary and extends the
   inclusion immersion continuously to it.

This supplies the continuous conformal ideal extension needed by the new
embedded-disk theorem.  For any holomorphic disk embedding with such an
extension, boundary fibers are light by a Jensen--Fatou uniqueness
argument.  Every parameter component of a target proper path restricted
to the embedded image is topologically proper; its connected endpoint
cluster set lies in one light boundary fiber and is therefore a
singleton.  Thus every component is KKL proper.  First/last traversal and
repeated-access hairpin arguments then give the exact formula

\[
 \iota^*I
 =
 \{p:\Phi_\iota(p)\subset I\}
\]

for every connected target ideal set \(I\).

For the direct-decoration pair, the earlier claim that common logarithmic
coordinates put each source tile into the complete lower strip was
overstrong.  KL supply a degree-one annulus immersion, not a simultaneous
common-coordinate inclusion.  The map
\(z+\varepsilon\sin(2\pi z)\) is a globally embedded degree-one strip map
with a wavy upper boundary, so translation and exact cap geometry do not
follow.  The lower-strip, closed-\(O\)-port, and tile-star conclusions are
retained only under an explicit common-coordinate inclusion hypothesis
that also includes tile--central overlap reflection.

The unconditional and conditional-control nodes are:

- `KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY`;
- `EMBEDDED_DISK_ACCESSIBLE_FOOTPRINT_THEOREM`;
- `GENERAL_ANNULUS_IMMERSION_LOWER_STRIP_NO_GO`;
- `COMMON_COORDINATE_NESTED_ANNULUS_OUTER_CAP`.

The same hostile audit also supplies the explicit noninjective
degree-one strip immersion and the conditional tile-injectivity gluing
criterion.  The later source-locked reduction
`KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION` proves that a degree-one
universal-cover tile lift is injective exactly when its bold base-annulus
immersion is injective, and that full properness would suffice.  The exact
finite-Blaschke construction
`KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO` further proves that Kahn's complete
abstract annulus-lemma hypotheses do not imply global injectivity.  Thus
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING` and
`DIRECT_DECORATION_OUTER_CAP_FOOTPRINT` are open in this historical pass.
The later canonical-localization audit supersedes the proposed universal
embedding route: it proves an actual canonical-seed collision and turns the
former embedding node into a non-gating restricted-class question.  The
corrected relation-reflection proof below remains a valid conditional
theorem on any separately proved injective pair:

\[
 Q\cap P_{j(i)}=Q_i,
 \qquad
 L_i^{-1}\!\left(\widetilde e_{j(i)}(Q_i)\right)=e_i(Q_i).
\]

The first equality follows from component bijectivity; the second follows
from overlap commutation and tile injectivity.  Reflection over the whole
of \(P_{j(i)}\) remains a stronger non-gating saturation question,
potentially relevant to collars or footprints.  On canonical seeds the
next universal task is instead a sheet-sensitive \(O\)- and
\(\xi/\eta\)-footprint theorem retaining localization cosets, followed by
family-level pullback disjointness, covering refinement, and complete
end-properness.  VAAPC-I, UPTCR, rigidity, and MLC remain open.

The decisive source distinction is:

- KL II `kingdom.tex`, lines 3--18 and 45--53, gives physically nested
  \(U^m\) only in the initial ordinary quadratic-like presentation;
- KL II `psiql.tex`, lines 8--15 and 198--206, gives only immersions
  between bold ambient domains and between their universal-cover tiles at
  a general \(\psi\)-ql stage;
- Kahn I `psiql2.tex`, lines 87--98, proves embedding of such an annulus
  immersion only on a sufficiently thin inner collar; and
- KL II `moduli.tex`, lines 361--394 and 420--443, separately normalizes
  annuli and calls the deeper-to-shallower map a natural immersion, without
  simultaneously straightening it to a translation.

The exact covering-space calculation is internal and uses no additional
import.  If \(I:A_s\to A_t\) has annular degree one and
\(L:\widetilde A_s\to\widetilde A_t\) is a compatible lift, then
\(L T_s=T_tL\).  A base collision \(I(u)=I(v)\), \(u\ne v\), lifts to
\(L(y)=T_t^kL(x)\), hence
\[
 L(T_s^{-k}y)=L(x)
\]
at two distinct source points.  Conversely, base injectivity, deck
equivariance, and freeness exclude every lift collision.  A proper
degree-one holomorphic immersion is a one-sheeted annular covering and
hence a biholomorphism.  Kahn I `conclusions.tex`, lines 39--49, supplies
only the end-properness used there, while KL II `psiql.tex`, lines 248--253,
explicitly allows source ideal boundary to map into target interior.

The no-go theorem uses no additional imported theorem beyond standard
Sturm, Rouche, and harmonic-minimum principles.  With
\(r'=1287/1000\), \(r=(r')^{16}\), and
\[
 R(z)=
 \frac{
 B_{(1+6i)/10}(z)B_{(-3-i)/10}(z)B_{(-7+2i)/10}(z)}
 {B_{(-6+2i)/10}(z)B_{4i/10}(z)},
\]
exact Gaussian-integer expansions prove:

- no zero or pole on \(1\le |z|\le r'\);
- an orientation-preserving degree-one inner-circle homeomorphism;
- \(1<|R(z)|<r\) throughout the source annulus;
- absence of critical points by eight exhaustive rational Rouche disks;
  and
- an exact self-collision obtained from a second Rouche-isolated root of
  \(N-R(z_1)D_0\), \(z_1=-1+4i/5\).

The exact arithmetic is independently regenerated by
`validate_kahn_annulus_no_go.py`.  This counterexample has the complete
abstract annulus data in Kahn's collar lemma but is not asserted to arise
from the additional KL dynamical path-space structure.

The subsequent source-complete pass adds three narrowly scoped proved
nodes.

First, `PSI_QL_GLOBAL_INJECTIVITY_NO_GO` uses
\[
 f(z)=z^2,\qquad
 i(z)=\frac{e^{\pi(z+1)/50}-1}{e^{\pi/25}-1},
 \qquad K=[0,1],\quad K'=[-1,1]
\]
on \(\mathbb D_{75}\to\mathbb D_{5625}\).  It verifies every abstract
degree-two \(\psi\)-quadratic-like axiom, including
\(i^{-1}(K)=f^{-1}(K)=K'\) and complementary annular degree \(+1\), while
\(i(50i)=i(-50i)\).  This is not an actual KL localization collision.

Second, `KL_LOCALIZATION_SUBGROUP_REFLECTION_CRITERION` proves that for a
lift of an independently supplied physical embedding \(a\), the lift is
injective exactly when
\[
 a_*^{-1}(H_t)=H_s.
\]
This cover theorem is conditional in the KL application.  At a general
bold \(\psi\)-ql stage the source supplies only an immersion, so base
univalence or realization as a physical-embedding lift remains a separate
prerequisite.

Third, `FINITE_HORIZON_KAHN_COLLAR_EMBEDDING` proves a conditional
finite-chain theorem.  Full Kahn round-annulus data, embedded central
maps, tile-component bijections, exact declared gluing, and the additional
overlap-reflection equality on the retained collars yield coherent Kahn
collars and holomorphic embeddings of the collar-truncated pseudo-pieces.
The exact collar-relative fiber-product condition is necessary for the
quotient argument; the theorem assumes the stronger full collar equality,
which is sufficient and is not supplied by the checked Kahn/KL source.
Unlike the full-tile theorem, collar injectivity alone cannot compare
against a canonical overlap representative that may lie outside the
retained collar.  The theorem does not embed full pseudo-pieces, exhaust
omitted sheets, prove width comparison, or prove final-root no-birth.  All
global closure gates remain open.

## Forced collision in the actual canonical localization

The superseding proof is
[`kl_canonical_localization_forced_collision.md`](kl_canonical_localization_forced_collision.md).
It uses the following checked source files:

```text
Kahn, arXiv:math/0609045, official source archive
  .tmp_kl06_source.tar
  SHA256 3A63FC9773DB8B60ED4A0EB9A1C551E6F66C08E66AB92C36F4E2B482570AB817
  pullback.tex
  SHA256 7E0B43D74F2C6E4A4375F4A4F40271ABC6A289247B40FD5D0D8CB88ED6928E5C
  intro.tex
  SHA256 E7DD61396FEA927903D4DE4FD386E7AAEFD0BD3E2CEE1CE6F011680AD58144E0
  psiql2.tex
  SHA256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228

Kahn--Lyubich, arXiv:math/0609046, official source archive
  kingdom.tex
  SHA256 5DC04FEFF6B6A1D73040FFD50519C35D62EFF03C1049686DA71D595758E38FA7
  psiql.tex
  SHA256 6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF
```

The exact source uses are:

1. Kahn I `pullback.tex`, lines 2--7, gives
   \(U^{r+1}\subset U^r\) and quadratic-like degree two at every ordinary
   pullback stage, hence global degree \(2^p\) for \(F=f^p\).
2. `intro.tex`, lines 22--44, defines \(K_p(j)\), the union
   \(\mathcal K_p\), and primitive pairwise disjointness.
3. `psiql2.tex`, lines 434--505, defines localization by the cover subgroup
   carried by a local neighborhood and proves functoriality and preservation
   of immersion, not embedding.
4. `psiql2.tex`, lines 510--558, defines the actual source and target
   deletion packets and the canonical localization at
   \(A=K_p\), \(B=\mathcal K_p\).
5. `psiql2.tex`, lines 350--416, gives the exact equalizer pullback
   \[
   \mathbf U^{r+2}=\{(x,y):i_r(x)=f_r(y)\},\qquad
   i_{r+1}(x,y)=y.
   \]
6. KL II `kingdom.tex`, lines 116--155, gives the direct-decoration depths
   \(m=\nu q+1\) and \(n=(\nu-1)q+1\); `psiql.tex`, lines 169--207,
   distinguishes the dynamical covering arrow from the inclusion-induced
   immersion.

The internally proved finite full-pullback lemma shows that the inverse
image of a full continuum under one quadratic stage is either one
degree-two full continuum or two degree-one full continua.  Consequently
\((f^p)^{-1}\mathcal K_p\) is a finite family of pairwise-disjoint full
continua.  Global degree \(2^p\) versus central degree two produces an
excess component \(X\ne K_p\) of \((f^p)^{-1}K_p\).  Invariance and
primitivity give \(X\cap\mathcal K_p=\varnothing\), so a Jordan disk
isolates \(X\) from both removal packets.  Its peripheral loop is excluded
from the source local subgroup by winding number and is nullhomotopic in
the target complement.  This proves
\[
 a_*^{-1}(H_t)\supsetneq H_s
\]
for the physical inclusion used by the actual canonical localization, and
hence proves a point collision of the localized inclusion.  The exact
equalizer recursion propagates it to every later \(i_r\); when the same seed
has KL direct-decoration data, it reaches the exact full tile and glued
pseudo-piece maps.

This promotes only `KL_CANONICAL_LOCALIZATION_FORCED_COLLISION`.  The
same-seed direct-decoration alignment remains an explicit implication, not
an inferred parameter-existence statement.  The universal footprint and
contact chain is rerouted through a sheet-sensitive state retaining
\[
 a_*^{-1}(H_t)/H_s.
\]

## Canonical sheet-resolution factorization

The follow-up proof is
[`kl_localization_sheet_resolution_factorization.md`](kl_localization_sheet_resolution_factorization.md).
It imports no new dynamical theorem.  It applies standard covering
classification to the already source-locked physical inclusion and
localization covers, and proves every needed factorization statement
internally.

For
\[
 K=a_*^{-1}(H_t),
\]
the selected pullback component
\[
 P_K=\operatorname{Comp}
 \bigl(X_s\times_{X_t}\widehat X_t\bigr)
\]
is the \(K\)-cover of \(X_s\).  The physical localization lift factors
uniquely as
\[
 \widehat X_s\xrightarrow qP_K\xrightarrow e\widehat X_t,
 \qquad A=e\circ q,
\]
where \(q\) is a covering and \(e\) is embedded.  The kernel pair of
\(A\) is exactly the kernel pair of \(q\), and the category of elements of
the \(q\)-monodromy functor is the canonical sheet groupoid.  Uniqueness is
within the connected, based, commuting intermediate-cover comparison class
stated in the proof.

The already proved winding certificate gives the stronger conclusion
\[
 [K:H_s]=\infty:
\]
the powers \(\gamma^nH_s\) have distinct winding and hence are pairwise
distinct cosets.  Raw finite sheet enumeration is therefore impossible.
The factorization base-changes through Kahn's full, unselected exact
equalizers on the complementary-cover locus.  By itself this gives no
filled or prime-end extension and no boundary realization.

The proof also gives exact injectivity and surjectivity criteria for an
induced **based coset** map under enlargement.  It explicitly rejects
their use as a complete geometric no-birth theorem: trivial groups do not
detect a newly attached simply connected component or prime-end access.

The conditional safe-set reduction additionally assumes the explicit
endpoint-subordination rules on an authorized ideal-boundary model; those
rules are not supplied by the covering factorization.

This promotes only
`KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION`.  It proves no actual
\(O,\xi,\eta\) footprint, singleton KKL-proper-lift isolation,
future-faithful compactification, whole-end properness, width estimate, or
global gate.

## Kahn-iterate complementary and tilewise interior alignment

The follow-up proof is
[`kahn_iterate_complementary_component_alignment.md`](kahn_iterate_complementary_component_alignment.md).
It uses only the locked Kahn I and KL II sources:

```text
Kahn I, arXiv:math/0609045
  intro.tex
  SHA256 E7DD61396FEA927903D4DE4FD386E7AAEFD0BD3E2CEE1CE6F011680AD58144E0
  psiql2.tex
  SHA256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228

Kahn--Lyubich II, arXiv:math/0609046
  psiql.tex
  SHA256 6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF
```

Kahn's special pullback lemma, `psiql2.tex` lines 259--265, says that
because one leg is an immersion, the complex-manifold pullback has the
ordinary topological fiber product as its underlying space.  For the
finite iterates, lines 350--399 give
\[
 x\in K^{r+1}
 \Longleftrightarrow i_r(x)\in K^r
 \Longleftrightarrow f_r(y)\in K^r
 \Longleftrightarrow y\in K^{r+1}
\]
and prove that the entire pullback is again a disk/FJ pair.  Hence
\[
 \mathbf U^{r+2}\setminus K^{r+2}
 =
 (\mathbf U^{r+1}\setminus K^{r+1})
 \times_{\mathbf U^r\setminus K^r}
 (\mathbf U^{r+1}\setminus K^{r+1})
\]
is the one connected ambient complementary equalizer.  Surjective
base change of \(q\) then makes the resolved intermediate connected.

There is also a tilewise interior conclusion.  Kahn's lines 155--174 show
that the inclusion immersion of the complementary annuli has oriented
degree \(+1\).  For every source tile \(a\), the pullback of its target
tile \(j_\iota(a)\) is therefore connected and is the source universal
cover.  KL's chosen source and target component embeddings in
`psiql.tex` lines 95--160 fix compatible lifted basepoints and hence the
deck phase.  Distinct source indices mapping to one target index remain
separately labelled copies.  Pulling \(q/e\) through each labelled tile
gives a surjective cover onto one connected resolved intermediate followed
by an embedding into the target tile **when the annular KL base immersion
has that whole \(q/e\) factorization**.  This is a conditional
covering-space theorem.  It does not identify the canonical infinite
sheet-resolution cover with the whole actual KL tile map.

For one fixed seed, KL use Kahn's same \(\mathbf U^m\)-tower.  This is a
conditional fixed-seed alignment theorem, not a parameter-existence
theorem.  The result is family-valued over all source tile indices:
\(\mathbf Y\setminus K_Y\) is the disjoint family of the glued
universal-cover copies.  The dynamical covering component map and the
inclusion component map remain distinct and are not proved equal.

The source gives a boundary extension only for the composite KL
immersion, and explicitly warns that its boundary need not map into the
target boundary.  The subsequent relative-boundary theorem proves that
this distinction is structural: any whole actual KL tile
covering/embedding factorization must be one-sheeted.  The canonical
infinite resolved cover therefore needs a separately constructed
comparison map to the KL tile before any boundary or footprint
identification.

This promotes only
`KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT`.  No filled completion,
prime-end theorem, final-root no-birth, width estimate, global virtual
carrier, UPTCR clause, rigidity statement, or MLC claim follows.

## Resolved intermediate relative ideal boundary and KL incompatibility

The proof is
[`resolved_intermediate_relative_ideal_boundary.md`](resolved_intermediate_relative_ideal_boundary.md).
It uses the following locked source files:

```text
Kahn I, arXiv:math/0609045
  wad.tex
  SHA256 B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580
  psiql2.tex
  SHA256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228

Kahn--Lyubich II, arXiv:math/0609046
  psiql.tex
  SHA256 6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF
  moduli.tex
  SHA256 CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E

KKL source lock
  waves-with-Misha.tex
  SHA256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

For an annular holomorphic factorization
\[
A_s\xrightarrow qP\xrightarrow eA_t,\qquad e q=\iota,\qquad\deg\iota=1,
\]
put
\[
G=\pi_1(P),\quad H=q_*\pi_1(A_s),\quad N=\ker e_*.
\]
Then \(G=N\rtimes H\).  In one based universal-cover action,
\[
\mathcal E_a/H=A_s,\qquad
\mathcal E_a/N=\mathcal R_a,\qquad
\mathcal E_a/G=P.
\]
Thus \(q_a:\mathcal E_a\to\mathcal R_a\) is the universal cover with deck
group \(N\), and exact base change preserves every \(q\)-fiber.

If \(\zeta\) lies in the deck limit set, choose
\(\gamma_n z_0\to\zeta\).  Bounded hyperbolic distance gives
\(\gamma_n z\to\zeta\) for every \(z\), while
\(q_a(\gamma_n z)=q_a(z)\).  No continuous point-valued extension at
\(\zeta\) into a Hausdorff target can exist.  The same proof applies to
every nonconstant deck-invariant composite.

Kahn and KKL therefore use the relative ideal boundary obtained after
removing the deck limit set.  On an invariant subset of the domain of
discontinuity, the quotient is Hausdorff, and any continuous extension of
the invariant composite descends uniquely.

There is also a backward correction.  KL's strip uniformization and
named boundary paragraph identify actual-tile fixed points
\(\omega_\pm\) with the two infinitely wrapping vertices and extend the
actual tile composite \(L_a\) there.  The based source-cover
biholomorphism extends with
\(\overline\Phi_a(\omega_\pm)=\zeta_\pm\); hence the transported
resolved-source composite is \(K_a=L_a\Phi_a^{-1}=e_aq_a\).
Normality puts \(\zeta_\pm\) in
\(\Lambda(N)\) whenever \(N\ne1\).  Hence a whole actual KL tile
covering/embedding factorization must have \(N=1\).  The canonical
infinite sheet-resolution cover is not that whole tile factorization.
At this point in the dependency chain the next audit is the
canonical-resolution/actual-KL correspondence; the following no-go theorem
closes its whole-tile branch and leaves only restricted or revised
interfaces before relative-boundary and footprint transport.

This promotes only
`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY`.  The full footprint,
proper-path and whole-end-interval map classification, Wave certificate, VAAPC-I, UPTCR,
rigidity, and MLC remain open.

## Canonical resolution/whole-KL-tile correspondence no-go

The proof is
[`canonical_resolution_kl_tile_correspondence_no_go.md`](canonical_resolution_kl_tile_correspondence_no_go.md).
It imports no new source statement.  It reuses the locked Kahn
ideal-boundary convention and the locked KL universal-tile, strip,
infinite-wrapping, and continuous-composite statements listed in the
preceding entry.

A whole-tile comparison is typed by a based source universal-cover
biholomorphism \(\Phi\), conjugacy of the annular deck generators, a
target comparison \(B\) injective on the canonical composite image, the
complete identity
\[
 L_{\rm KL}\Phi=B e q,
\]
and transport of the two wrapping fixed points to KL's named vertices.
For a nontrivial canonical kernel \(N=\operatorname{Deck}(q)\), a deck
sequence converges to either wrapping point while \(eq\) is constant on
the sequence.  KL continuity at the transported vertex would make
\(Beq\) constant on the entire source disk, contradicting nonconstancy
and target separation.

Thus the canonical infinite resolved cover cannot be the whole actual KL
tile factorization.  This is not an injectivity theorem for an arbitrary
KL immersion: the proof records the exact locally univalent,
noninjective, boundary-continuous disk map
\[
 z\longmapsto e^{4(z-1)}
\]
as a positive control showing that non-covering immersion collisions can
survive.  Proper collar/interior, relation-valued, retimed one-sheet, and
relocalized comparisons remain open.

This promotes only
`CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO`.  The immediate positive
gate at this point in the dependency order is the restricted-interface
construction; the next entry records the relation-valued interior branch
and its remaining proper-end/response gate.

## Canonical/KL restricted-interface classification

The proof is
[`canonical_kl_restricted_interface_classification.md`](canonical_kl_restricted_interface_classification.md).
It imports no new external theorem.  It reuses the locked Kahn annulus
lemma and KL pseudo-piece/tile/boundary/width definitions, with these
source limits kept explicit:

- Kahn supplies an existential embedded inner collar, uniform only when
  the target annulus stays away from modulus zero;
- KL's inclusion-induced tile maps are immersions, not asserted
  embeddings;
- KL extends the glued pseudo-piece immersion at its pseudo-piece ideal
  boundary, not a single tile map on the whole standalone prime-end
  circle; and
- the two wrapping vertices are the only standalone source-tile points
  used for the promoted partial boundary extension.

For every **supplied fixed labeled same-source datum**, based universal
covering uniqueness constructs the span
\[
 \mathcal R\mathop{\longleftarrow}^{q}\mathcal E
 \mathop{\longrightarrow}^{K}\widehat A_t^{\rm KL}.
\]
The fiber product of a target path with each \(K_i\) is an étale space
over the parameter interval.  Its path components are exactly the
maximal parameter-compatible interior lifts; the tagged disjoint union
over source labels preserves repeated component labels, resolved traces,
sheets, and deck phases.

If \(N=\operatorname{Deck}(q)\ne1\), any descent \(K=\kappa q\) would make
\(K\) a nonconstant \(N\)-invariant map.  The source-locked values at the
two transported wrapping points
\(\zeta_\pm\in\Lambda(N)\) contradict the deck-limit theorem.  The same
deck sequences prove that these two values lie in the closure of every
resolved fiber orbit.  No value on the rest of \(\Lambda(N)\) is asserted.

Two exact negative controls accompany the span:

1. For
   \[
    \mathbb A(1,e^{\varepsilon/2})
    \hookrightarrow
    \mathbb A(1,e^\varepsilon),
   \]
   every source inner collar has crossing width at least
   \(4\pi/\varepsilon\), while the target has width
   \(2\pi/\varepsilon\).  Thus Kahn's hypotheses alone cannot bound the
   **unscaled** additive difference.  Calibrated and source-specific
   responses remain open.
2. Exact Kahn base change preserves every \(q\)-fiber, so selecting a
   later finite stage in the unchanged equalizer tower cannot turn an
   infinite factor into a one-sheet factor.

For revised covers, the algebraic reflection criterion
\(a_*^{-1}(H_t)=H_s\) is necessary and sufficient for one-sheetedness
only after the lift condition \(a_*(H_s)\le H_t\) is supplied.  It gives
no dynamical authorization.

This promotes only
`CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION`.  The subsequent
geometric-trace audit below corrects the proposed next gate: parametrized
lifts are not the whole KKL restriction, and final-root no-birth is
independent of the response estimate.

## Full-pseudo-piece proper lifts and geometric-trace no-go

The proof is
[`canonical_kl_geometric_trace_proper_end_response.md`](canonical_kl_geometric_trace_proper_end_response.md).
It source-locks:

- KKL `waves-with-Misha.tex`, SHA-256
  `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5`;
  line 406 defines proper paths, lines 2081--2097 define geometric
  immersion restriction and pulled intervals, and lines 2157--2159 define
  end-properness on complete end-intervals;
- KL `psiql.tex`, SHA-256
  `6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF`;
  lines 169--207 separate covering and inclusion-immersion maps, while
  lines 231--253 give the named full pseudo-piece boundary and its
  continuous, not necessarily boundary-valued, extension.

For one supplied full KL pseudo-piece inclusion immersion between conformal
disks, every maximal parametrized lift of a KKL proper target path has
unique source ideal endpoints.  Interior source clusters would extend the
lift and contradict maximality; connected boundary clusters lie in a
single boundary fiber, and bounded-holomorphic boundary uniqueness makes
that connected fiber subset a point.  Exact endpoint naturality holds.
This proves `FULL_KL_PSEUDOPIECE_MAXIMAL_LIFT_PROPERNESS`, but not map
properness on an ideal interval.

KKL restriction is larger: it contains every proper source path in the
geometric inverse trace.  The identity lollipop has a loop-omitting proper
restriction absent from its parametrized graph.  Moreover,
\[
K(z)=\exp\!\left(-\frac{1+z}{1-z}\right)
\]
gives one target diameter infinitely many proper source restrictions
indexed by logarithmic deck phase.  Translated logarithmic rectangles
have aggregate raw **interior-crossing** width
\((2m+1)w_0\); they are not asserted to be complete KKL-marked
laminations.  This proves
`PARAMETRIZED_PULLBACK_KKL_EXHAUSTION_NO_GO` in that exact scope.

The corrected open order is:

1. `DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER`;
2. `DIRECT_DECORATION_CANONICAL_KL_STAGE_ALIGNMENT`;
3. `DIRECT_DECORATION_RELATION_PROPER_PATH_END_INTERVAL_CLASSIFICATION`;
4. `DIRECT_DECORATION_CANONICAL_KL_RELATION_PROPER_END_RESPONSE`; and,
   independently after step 3,
5. `DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH`.

Path properness, immersion properness on an ideal subset, and
end-properness on a pulled multi-interval are never conflated.

At this earlier source-audit checkpoint, the authoritative ledger had
407 obligations: 25 imported, 283 proved, and 99 open.  VAAPC-I, Wave
certificates, UPTCR, rigidity, and
MLC remain open.

### Rejected double-airplane alignment promotion

The separate audit
[`kl_aligned_double_airplane_source_lock_20260725.md`](kl_aligned_double_airplane_source_lock_20260725.md)
tests whether primitive tuning by the real period-three airplane supplies
a named same-seed KL direct-decoration witness.  The checked inputs are
Shen--Wang arXiv:2010.05199v1 (source archive SHA-256
`8F38A8F23999AA59FEE3A1C4F927835D0B7560C2D16C00FE8C1BE21BB66F60A2`)
and Inou--Kiwi arXiv:0809.1262v2 (source archive SHA-256
`F47BE43D92D843DAD8F20C45FC5EDF459EEEF2F02173B59BF9964A3CF3C858EC`),
with Milnor's period-three portrait used only to identify the intended
primitive hyperbolic component.

The sources construct an actual marked physical return germ hybrid
equivalent to the chosen target once their primitive-base hypothesis is
supplied.  They do not state, in the exact form required here:

1. pairwise disjointness of the three physical outer little Julia sets;
2. both repelling fixed points and KL's finite non-satellite escape for
   that same physical germ; or
3. preservation by Kahn localization of the complete KL puzzle marking on
   every direct-decoration domain.

No aligned-witness theorem is therefore promoted.  This negative source
verdict does not weaken the unconditional canonical-localization collision
or its conditional same-seed propagation.

## Terminal dense-obstacle theorem and ordered-multicurve replacement

The complete proof is
[`terminal_dense_obstacle_and_submulticurve_replacement.md`](terminal_dense_obstacle_and_submulticurve_replacement.md).
It uses the following locked statements and no local-connectivity
assumption in the prime-end argument itself.

1. Douady--Hubbard, *On the dynamics of polynomial-like mappings*,
   Chapter I, Sections 1--2: straightening and the connected
   polynomial-like external map.  In prime-end coordinates the latter is
   conjugate to \(t\mapsto dt\pmod 1\).  This is a special dynamical
   exactness statement; it is not inferred from the degree of an arbitrary
   circle covering.
2. KKL `waves-with-Misha.tex`, SHA-256
   `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5`,
   lines 497--501 and 514--520: the nondividing fixed point
   \(\beta_F\), connectedness of \(K\setminus\{\beta_F\}\), and the
   locally connected native Hubbard carrier as the least connected
   forward-invariant carrier containing the primitive small-Julia cycle.
3. KL `psiql.tex`, SHA-256
   `6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF`,
   lines 231--275: the tile-tagged \(J\)-boundary, ordered
   multicurves, and Lemma `lifts`.
4. KL `appendix.tex`, SHA-256
   `05A13ED2D46CB9E2D188E6D96F4A2B639626F99657723118B4DE3479CD980916`,
   lines 10--45: extremal length/width and the lifting-overflow
   comparison.

The native locally connected primitive carrier is proper: the fixed
point \(\beta_F\) belongs to no member of the pairwise-disjoint primitive
cycle, so leastness puts the carrier in
\(K\setminus\{\beta_F\}\).  For any proper compact connected
forward-invariant carrier \(T\subsetneq K\) with
\(\operatorname{int}K=\varnothing\), impression covariance and exactness
of the external map imply that no open external prime-end arc can have all
impressions in \(T\).  Combining this with the proved local
access-survival equivalence shows that the prime-end closure of
\(K\setminus T\) fills every finite inner ideal point of the carrier
complement and both deck-limit corners.  Thus the proposed universal
obstacle-free terminal collar is false already in KKL's locally connected
native subcategory.

The valid width replacement is relation-valued.  If a physical curve
connects \(S_Y^v\) to \(S_Y^w\), KL's Lemma `lifts` extracts an ordered
submulticurve lifting to a horizontal multicurve from
\(\partial^v\Psi(Y)\) to \(\partial^w\Psi(Y)\).  With multicurve length
defined as the sum of component lengths, the pushforward-metric proof gives
\[
 \mathcal W(\mathcal H_Y(v,w))
 \le
 \mathcal W(\Gamma_Y(v,w))
 =
 \operatorname{Bd}_Y(v,w)^{-1}.
\]
This comparison has coefficient one and preserves the complete
\((\gamma,\gamma',\gamma^*)\) provenance relation.  It does not identify
an original KKL Wave endpoint with a KL prime end.

The non-locally-connected physical properness of the lifted KKL carrier
remains open: KKL lines 542--543 say that the rational-lamination Hubbard
objects lift, but the locked sentence does not identify the physical
carrier with a particular full inverse image or exclude the
\(\beta_F\)-fiber.

### Crest-versus-end source boundary

KKL lines 1874--1875 define a Wave's crest as the part of its base between
its two ends.  Consequently, a Wave *over* the terminal side has that side
in its crest; it does not thereby end there.  KL `psiql.tex` lines
231--244 place the two half-accesses at a vertex \(v_i\) in adjacent
tiles, \(\eta_i\) and \(\xi_{i+1}\), whereas KL `moduli.tex`, SHA-256
`CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E`,
lines 351--358 defines the one-tile family \(\mathcal C_{A_i}\) between
\(\xi_i\) and \(\eta_i\).  These are different endpoint types.  The
`moduli.tex` skipping-over estimate at lines 479--505 additionally
requires distinct endpoint vertices, a fixed separating puzzle piece, and
a componentwise skip witness.  None of those data follows from the crest
label alone, and an appended connector would destroy the required
subcurve relation.

KKL's stationary alignment paragraph has two logically separate defects.
With \(N=b+3\), the subwaves are defined only through \(A_{N-1}\); the
occurrence \(A_N\) at KKL line 1605 is an off-by-one error.  The project
proves the conditional indexing repair: if line 1603 is first validated,
then applying it at \(n=b\) and \(n=b+1\) gives both source predicates on
the actually defined \(A_{N-1}=A_{b+2}\).
The conditional reduction is
[`kkl_stationary_wave_component_incidence.md`](kkl_stationary_wave_component_incidence.md).

Line 1603 itself is not yet validated.  Its two separator-side portions
must first survive every immersion filter as actual terminal Waves, carry
complete marked prime-end access records, remain in one selected collar
without re-entry or sheet change, and avoid collision under the
nontrivial deck involution of the unique quadratic collar.  KKL's coarse
component labels cannot prove the last clause: the root and deep parents
route to the same component of \(T\setminus K_1\).  The complete
source-specific reduction is
[`kkl_stationary_tsnc_source_reduction.md`](kkl_stationary_tsnc_source_reduction.md).

The analytic model in
[`stationary_occurrence_collision_obstruction.md`](stationary_occurrence_collision_obstruction.md)
proves that two raw proper immersion-restriction components can have one
identical untagged degree-two image.  Its common image is not a KKL Wave
and the complete acting outer marking is not asserted, so it is a
multiplicity no-go rather than a counterexample to line 1603's exact
antecedent.

The retained-realization source audit proves the maximal positive
statement currently available from KKL's definitions:
`KKL_STATIONARY_ONE_RETAINED_CHAIN`.  Every selected unbreakable leaf has
at least one retained one-step component at every stage, and every
retained component at that stage has the same singleton untagged image.
This does not bind the two topological line-1603 portions to two full
segmented extension towers.  KKL lines 2083 and 2141 define the next
restriction by containment in the preceding output, so the next proper
path may occupy a strict parameter window.  Exact common-parameter
equality of all full paths reconstructs one complete fiber-product path
and is proved as
`PQL_STRICT_SYNCHRONIZED_CHAIN_RECONSTRUCTION`, but it is only a special
case and is not the general KKL invariant.

The correct finite invariant is proved in
[`kkl_stationary_segmented_occurrence_binder.md`](kkl_stationary_segmented_occurrence_binder.md).
`PQL_SEGMENTED_OCCURRENCE_RECONSTRUCTION` retains every full stage path,
every occurrence map, and the compatible relation path at every finite
tower prefix.  Earlier prefix coordinates may be nonproper strict
segments, while the last coordinate at each prefix is the full proper
stage path.  Conversely, the complete prefix flag reconstructs the
segmented record.  One deepest path cannot recover the discarded
shoulders, endpoint accesses, attachment provenance, or filter behavior
of the earlier full paths.

This finite theorem does not construct either actual line-1603 route.
Proposition 2099 allows adjacency and same-pulled-interval transitions
instead of actual paths, while the native attachment formula can absorb
an extra-tree boundary into one coarse interval and subject subordinate
candidates to the filter.  The missing source theorem is
`KKL_STATIONARY_TWO_OCCURRENCE_BINDER`, documented in
[`kkl_stationary_segmented_occurrence_binder.md`](kkl_stationary_segmented_occurrence_binder.md).

The subsequent graph proof
[`pql_iterate_filled_graph_naturality.md`](pql_iterate_filled_graph_naturality.md)
constructs their actual final fiber-product lifts and proves that the
lifts themselves are whole, distinct components of
\(\mathcal K^{N-1}\).  Final occurrence refinement, order,
a proper restriction, and one KL puzzle pair remain open.

## Kahn filled-set graph theorem and the KKL stationary degree defect

The locked Kahn source is
`.tmp_kl06_source/psiql2.tex`, SHA-256
`E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228`.
Lines 350--399 construct each fiber-product pullback and prove that its
immersion restricts to a homeomorphism on the filled set; lines 410--416
iterate the construction and record the commuting pullback squares.  If
\[
 I_m=i_0\circ\cdots\circ i_{m-1},
 \qquad
 P_m=f_0\circ\cdots\circ f_{m-1},
\]
then
\[
 I_m|_{K^m}:K^m\to K^0
\]
is a homeomorphism and
\[
 P_m=F^m\circ I_m
\quad\text{on }K^m.
\]
This proves `PQL_ITERATE_FILLED_GRAPH_NATURALITY`.

At KKL's stationary depth \(m=b+2\), the graph lifts of
\(K_0^b,K_0^{b+1}\) therefore exist, have images
\(F^2(K_0)\) and \(F(K_0)\), and are whole, distinct components of
\(\mathcal K^m\).  This proves
`KKL_STATIONARY_FINAL_COMPONENT_REALIZATION`.

The same typed formula exposes a second error in the v1 KKL proof.  The
selected inverse chain inside \(\mathfrak L_0\) is univalent because the
critical value lies in the disjoint limb \(\mathfrak L_p\), but the
remaining itinerary crosses the unique critical point in the central
small Julia set exactly once.  Thus
\[
 \deg(P_m|\widehat K_b)
 =
 \deg(P_m|\widehat K_{b+1})
 =
 2,
\]
not one as printed at KKL lines 1592--1593.  The exact repair to the
pushforward inequality is
\[
 \mathcal W(B)\le2\mathcal W(C)+4,
\]
which, with KKL's
\(\mathcal W(C)\le2\mathcal W(\mathcal RF)\), would give
\[
 \mathcal W(A_m)\le4\mathcal W(\mathcal RF)+4.
\]
This proves `KKL_STATIONARY_DEGREE_TWO_CORRECTION`.

## Finite stationary collars and the quantitative-defect route

Kahn's embedded polynomial-like restriction, iterated over one fixed
finite horizon, gives an open neighborhood of the pulled filled set on
which the complete immersion is an embedding.  On the complement of the
pulled tree inside that neighborhood it is a conformal isomorphism.  With
the induced ideal accesses, it preserves access side and cyclic order.
This proves `KKL_STATIONARY_FINITE_EMBEDDED_COLLAR_NATURALITY`.
It does not show that a Wave-subordinate route has a representative wholly
inside the collar.

Choose nested Jordan neighborhoods in that embedding domain.  Their image
annulus has a block-dependent positive modulus \(\mu_h\).  If selected
route germs have a measurable source-lift segment crossing from the inner
to the outer collar, those subarcs overflow the annular crossing family,
and hence
\[
 \mathcal W(E_h)\le\mu_h^{-1}.
\]
This is the proved `KKL_STATIONARY_COLLAR_EXIT_OVERFLOW` for that
explicitly selected crossing class.  It does not cover every `D1` exit:
a target trace may merely touch and reenter or continue on another global
immersion sheet without the required source annular crosscut.

The source-derivability obstruction is sharp.  For
\[
 U_R=\mathbb D_R,\quad U'_R=\mathbb D_{\sqrt R},\quad
 K=\overline{\mathbb D},\quad T=[-a,a],\quad
 f_R(z)=z^2,\quad i_R(z)=z,
\]
with \(0<a<1\) and \(R\downarrow1\), the pseudo-polynomial-like axioms,
degree two, global immersion embedding, connected filled set, and every
finite Kahn horizon hold.  Moreover
\[
 \mathcal W(U_R\setminus T)\le M_a,
 \qquad
 \mu_h^{-1}\ge\frac{2\pi\,2^h}{\log R}\to\infty
\]
for every horizon-\(h\) filled-set collar.  This proves
`KAHN_QUALITATIVE_COLLAR_VERTICAL_CHARGE_NO_GO`: the qualitative Kahn
data and a bounded vertical width cannot imply a vertical-linear collar
charge.  The family is not asserted to be a native periodically repelling
primitive KKL block and \(T\) is not asserted to be its native primitive
Hubbard tree.  Thus the model refutes the derivation from the larger
qualitative class, not the intended native theorem.

Kahn's qualitative embedding theorem gives only \(\mu_h>0\) for the
fixed block.
The period- and degeneration-uniform estimate
\[
 \mu_h^{-1}
 \le C_b\bigl(\mathcal W(U\setminus T)+1\bigr),
\]
together with a measurable source-crossing selector or an intrinsic
route-local conductance bound covering all proof-used exits, is the open
`KKL_STATIONARY_UNIFORM_COLLAR_EXIT_CHARGE`.

The proposed Quantitative Stationary Defect Bound (QSDB) is
`KKL_STATIONARY_QUANTITATIVE_DEFECT_BOUND` and remains open.  It asks for
a partition in KKL's native transverse width measure, with its
restrictions agreeing with the proof-used lamination widths, into a good
segmented-incidence family and a defect family uniformly charged to
vertical and renormalization widths.  Its use in the source-wide induction
also requires the native HTND scale or the explicit absolute hypothesis
\[
 \mathcal W(A)\ge C_{b,k,\lambda}\bigl(R(F)+1\bigr).
\]
The proved implication first establishes the disjoint estimate with
\(B=A^{N\text{-br}}\cup A^{\rm sh}\), then applies KKL's small-breaking
theorem.  With
\(\theta>\max\{\lambda/\lambda_3,1/(1+\delta_3)\}\), terminality of
\(B\) transfers quantitatively to \(A\), while the unbreakable branch is
contained in \(A^{\rm sh}\) and is strictly short.  This is
`KKL_STATIONARY_QSDB_SUFFICIENCY`; it is not a proof of QSDB, the
stationary repair, VAAPC-I, UPTCR, or MLC.

The quantitative repair is not yet unconditional.  KKL do not define
their phrase “passes through \(K_0^{m-1}\)” as a theorem producing one
retained proper path in
\(U^m\setminus\mathcal K^m\).  Their general immersion-restriction
definition permits splitting and discards subordinate or non-marked
paths.  Connected occurrence transport, prime-end landing, the
non-locally-connected model, measurable lamination assembly, and
\(\mathcal W(A_m)\le\mathcal W(B)\) remain the open node
`KKL_STATIONARY_FINAL_PASS_THROUGH_PATH_EXTRACTION`.  Consequently
`KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR` is open.

There is an independent defect in the bounded-visits argument.  For
length-\(k\) multi-intervals meeting the critical limb, the corrected
finite count is at most \(6b+k-1\), so a repetition requires a strict
pigeonhole excess.  Even after a repetition is obtained, the global
Perron--Frobenius inequality \(\lambda_F>1\) does not by itself exclude
a periodic marked interval.  The missing interval-level strict-growth
or no-periodicity statement is
`KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR`.

Consequently `KKL_PARABOLIC_WAVE_AMPLIFICATION` is open and
source-stated, not imported as a project-certified proof.  Its two
independent predecessors are the bounded-visits repair and
`KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR`.

The stronger fixed-pair route has additional independent gates:
`KKL_STATIONARY_FINAL_INCIDENCE_REFINEMENT`,
`KKL_STATIONARY_NESTED_INCIDENCE_ORDER`,
`KKL_STATIONARY_FIXED_PAIR_PROPER_RESTRICTION`, and
`TERMINAL_STATIONARY_RESTRICTION_KL_PUZZLE_SELECTOR`.

## 2026-07-26 source ledger: fixed-end WAD and survivor routes

### Locked corpus

The present reduction was checked against the following byte-locked
files:

| source | SHA-256 | controlling clauses |
|---|---|---|
| `.tmp_wave_audit/waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` | 1355--1392, 1423--1494, 1513--1532, 1547--1622, 2065--2178 |
| `.tmp_wave_audit/not-all-good2.tex` | `B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01` | 514--545, `thm:immer-decomp` |
| `.tmp_kl06_source/wad.tex` | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` | finite topology and valid-WAD definitions |
| `.tmp_kl06_source/psiql2.tex` | `E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228` | pseudo-quadratic-like covering/immersion framework |
| `.tmp_kl06_source/appendix.tex` | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` | 12--68, extremal length/width, overflow, series, and parallel laws |

The exact horizon convention is

\[
 H=N=b+3,\qquad m=N-1=b+2.
\]

The first quantity controls ambient KKL breakability; only the route
levels \(1\le h\le m\) enter the route-packet degree sum.  The safe
covering bound is \(D_h\le2^h\), with the ending-locus degree certified
where the KKL pushforward-lamination lemma requires it.

### Source-safe consequences

1. For a supplied single-valued, native-width-typed route selector,
   selected exits split exactly into
   \[
   E_A\cap A^{N\text{-br}},\quad
   E_A\cap A^{N\text{-nbr}}\cap A^{\rm sh},\quad
   E_A\cap A^{N\text{-nbr}}\setminus A^{\rm sh}.
   \]
   The first two are already contained in
   \(B_A=A^{N\text{-br}}\cup A^{\rm sh}\).  KKL's one-step breaking
   theorem cannot be reapplied to the third, ambient-unbreakable
   family.

2. From the native identity \(F_*=f_*\iota^*\), a singleton nonempty
   next ambient path has a nonempty retained-predecessor fiber.  Thus
   every selected survivor has, pointwise, either a strict-path
   replacement or a retained-path state mismatch at its first named
   failure.  Iterating this witness gives a finite segmented
   alternative flag, subject to the simple-path occurrence-window
   lemma.  No Borel selection, uniform fiber bound, deepest-path
   realization, or width estimate follows.

3. `thm:immer-decomp` applies to a finite-topology immersion only
   after a valid target WAD and proper degree-one source starting ends
   are supplied.  Its paired realizing foliations give valid full and
   other-end sub-WADs with
   \[
   \|Y_{\rm full}\|=\|Z'_{\rm full}\|,
   \qquad
   \|Y_{\rm exit}\|=\|Z'_{\rm exit}\|.
   \]
   These are paired coefficient-norm equalities, not equality of
   arbitrary marked extremal-width families and not
   \(\|Y'\|=\|Y\|\).

4. If the actual candidate-end relation is Borel, nonempty on every
   target-leaf fiber, and takes values in a supplied finite set of
   eligible ends, a fixed ordering gives a Borel least-end selector.
   This elementary finite selection does not construct the candidate
   relation, the exit occurrence, or a period-independent bound on
   marked accesses, sheets, windows, or retained paths.

5. A target survivor family dominated by a genuine proper vertical
   source packet, with native marking survival, injective leaf
   accounting, and the required ideal-end degree, obeys
   \[
   \mathcal W(\mathscr S_h^{\rm ver})
   \le D_h(V(F)+2)\le2^h(V(F)+2),
   \]
   and hence
   \[
   \sum_{h=1}^{b+2}\mathcal W(\mathscr S_h^{\rm ver})
   \le(2^{b+4}-4)(V(F)+1).
   \]
   This is a proved implication from the packet hypotheses, not a
   source construction of those packets.

### Exact non-imports

Master line 1600 supplies only an existential restriction ending at
the marked \(L_0^h\)-continuum.  It does not construct a Freudenthal
end representing that access.  Under the separately stated
\(\mathrm{TWO}_h\wedge\mathrm{INC}_h\) hypotheses, the physical inner
Freudenthal end is nonproper because an approaching sequence maps to
a compact subset of the target surface.  Unconditionally, however,
the first failure is the access/Freudenthal type mismatch.  The
original \(BL_0\) and remote accesses remain only candidates.  Two
fixed-end applications therefore require:

\[
 C_h^-,\ X_h^-,\ C_h^+,\ X_h^+,\ P_h,\ M_h,
\]

where \(C_h^\pm\) certify the eligible proper-degree-one ends,
\(X_h^\pm\) certify exit of the two maximal lifts at the same
\(L_0^h\) occurrence, \(P_h\) supplies common leaf/window/sheet/access
coupling, and \(M_h\) supplies native filter survival and the asserted
covering-Wave images.  None is imported from line 1600 or from
`thm:immer-decomp`.

After granting measurable route selection, the first uncharged output
is a retained survivor Wave ending at \(BL_0\).  It has no certified
vertical crossing or exact final small-Julia incidence.  KKL's
critical-limb estimate cannot charge it without circularly invoking
the disputed line-1603 alignment.  A source-native measurable
fixed-end partition, a Borel retained-predecessor packet with uniform
or summable multiplicity, and a noncircular response for this
critical-end residual remain open.

Accordingly no unconditional stationary repair or global closure gate
is promoted by this source pass.  The 414/26/287/101 count was the
historical checkpoint before the access-seeded and paired-response
integration.

## 2026-07-26 source ledger: access-seeded and paired-Wave response

The additional checked proof files are:

| proof document | SHA-256 | certified scope |
|---|---|---|
| `kkl_stationary_fixed_end_topological_obstruction.md` | `9284C52BC7E954DF0B1E211B5CFF1124B1F3878CAA103E5CB1F47A612479A6E2` | unconditional access/Freudenthal type obstruction; two-end/nonproper/vertical refinement only under its displayed hypotheses |
| `kkl_access_seeded_maximal_lift_measurability.md` | `2460ABCB137BC04987932731E0B40F26BBFC28CEBE8A403A7AED9472D66C65FF` | continuous-product maximal lift, lower-semicontinuous exit, and Borel landing/finite-horizon code |
| `kkl_stationary_bl0_survivor_analysis.md` | `5F94E965B612B710DF24B643ACDFB79FC3FC216BE0127FFA4D9C4176CB544C48` | exact occurrence Series inequality and paired-Wave response algebra, conditional on actual source Waves and the uniform Wave constant |

The KL06 Series and holomorphic transformation rules are imported from
the locked `appendix.tex`.  At this pre-QA checkpoint, KKL master lines
2149--2152 were recorded as the stated Wave pushforward estimate.  The
post-freeze correction below narrows this to a documentary source record:
the local file does not contain the proof or document the full dependence
of the hidden \(O(1+\log d)\) constant, and
`KKL_WAVE_PUSHFORWARD_UNIFORM_PACKET_CONSTANT` remains open.

The strongest newly proved conditional inequality is

\[
\max_{1\le i\le r}\mathcal W(C^i)
\ge r\mathcal W(S)-C_b.
\]

It follows from the exact source-family relation

\[
\mathcal W(S)\le\bigoplus_{i=1}^r\mathcal W(B^i)
\]

and the coefficient-one Wave estimates
\(\mathcal W(B^i)\le\mathcal W(C^i)+C_b\).  For \(r=2\) it gives a
factor-two packet response up to \(C_b\), including certified
common-output collisions.  No source line constructs the required
full-width paired source Waves.

At the pre-QA freeze the authoritative status was 423 obligations: 28 imported,
291 proved, and 104 open.  VAAPC-I, UPTCR, MBTT, rigidity, and MLC
remain open.

## Post-freeze source correction — 2026-07-26

The immutable source/version and dependency audit is
`qa_dependency_status_2026-07-26.md`.  The native stationary
line-by-line audit is `qa_native_kkl_stationary_2026-07-26.md`; the
extremal-width/Wave audit is `qa_extremal_wave_2026-07-26.md`.

Two source-scope corrections are now mandatory:

1. KKL master lines 2149--2152 remain a documentary record of a printed
   coefficient-one Wave assertion, but the literal broad formulation is
   not imported as valid mathematics.  The cyclic-cover counterexample
   in the QA-3 report satisfies the printed pulled-marking, Wave,
   ending-multi-interval, and finite-degree predicates and contradicts
   the logarithmic-loss conclusion.
2. Dudko--Lyubich's native annular buffer-extraction lemma remains
   imported only for one Wave above one fixed boundary interval under a
   degree-\(m\) closed-annulus covering.  The counterexample consists of
   several independent lifted coordinates and lies outside that native
   hypothesis.

The candidate `kkl_wave_local_end_collision_reduction.md` is retracted:
full-base degree does not control inter-component conductance collapse.
A valid replacement must impose and verify coherent single-coordinate
Wave geometry or retain a multiplicity-aware linear charge.

The KKL stationary source at locked master lines 1534--1623 is also
classified as incomplete as printed.  In particular, line 1576 does
not prove its relative complement estimate, line 1605 invokes undefined
\(A_N\), and the final canonical graph component has continuum degree
\(2\), not \(1\).  See the native QA report for the complete
clause-by-clause classification.

Post-QA ledger state:

```text
430 total / 30 imported / 292 proved / 108 open
MLC, UPTCR, VAAPC-I, and the native stationary repair: open
```

## Gate N1 source promotion — 2026-07-26

The first native stationary gate is now proved in
`kkl_stationary_relative_wave_continuation.md`, frozen at SHA-256
`ADFC7BCD5A73CE7E7ABE12C11C3E2C4D778826B995BF9114C6F8B431EF38094F`.
The final dependency and source-semantic decision is recorded in
`kkl_stationary_n1_integration_audit_20260726.md`.

The source-critical import uses only the rectifiable sub-scope and is
narrower than the displayed retained width in the Dudko--Lyubich Wave lemma.  The
pre-pruning Borel leaf atlas first splits every KKL packet, in a
finite-area round-annulus model, into a Borel rectifiable core and a
zero-width nonrectifiable family.  The proof at frozen Feigen lines
2830--2841 is applied only to that core and deletes
\(T=O(\log m)\) deck-span packets, each of
width \(O(1)\), followed by one \(O(1)\) outer buffer.  The Parallel
Law therefore gives a direct upper bound

\[
 \mathcal W(\mathscr S\setminus\mathscr S^{\rm new})
 =O(1+\log m).
\]

At \(m=2\) this is absolute.  The interpretation of deleted
\(O(1)\)-curves as a width buffer is source-locked by Feigen
1791--1792 and 2601 and by the explicit unit-buffer calculation in
the locked DL2 source at 2348--2355.

Two independent audits agree on the following mandatory split:

1. exact extremal-width additivity on disjoint measurable supports is
   mathematically proved;
2. the frozen Feigen phrase “genuine subwave” does not explicitly
   import the separate DL2 measurable-support convention, so that
   additivity rederivation remains conditional; and
3. the native proof-internal deleted-packet estimate is independent of
   that semantic issue and is the only route imported by Gate N1.

The remaining project-original proof components are the Borel
width-envelope pruning theorem and the standard-Borel ordered-Wave
realization.  Their frozen hashes and two independent backward-audit
hashes are listed in the final integration audit.  The pre-pruning
Borel dependency includes Sections 2--5 and the filtered occurrence
construction in BOWR Section 7.2; later Borel pruning introduces no
dependency cycle.

The post-promotion ledger state is:

```text
437 total / 31 imported / 299 proved / 107 open
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION: proved
Gates N2--N4 and the complete native stationary repair: open
MLC, UPTCR, and VAAPC-I: open
```

## Gate N2 quotient-level correction — 2026-07-27

The source-complete audit is
`kkl_stationary_n2_kiwi_model_identification_audit_20260727.md`.
Its primary external source is Jan Kiwi, *Real laminations and the
topological dynamics of complex polynomials*, Advances in Mathematics
184 (2004), 207--267, DOI
`10.1016/S0001-8708(03)00144-0`, specifically Theorem 2
(pp. 209--210), Proposition 4.2 (pp. 233--234), and Theorem 5.12
(pp. 243--244).

For a polynomial with connected Julia set and no irrationally
indifferent cycle, the imported theorem supplies a continuous monotone
semiconjugacy to the locally connected real-lamination model.  Theorem
2, the fiber quotient of Proposition 4.2, and the factorization in the
proof of Theorem 5.12 give singleton complete fibers at periodic and
preperiodic points.  After KKL's same-filled quadratic-like
restriction and straightening, this gives an existential monotone model
for the periodically repelling KKL filled continuum.  It does not
construct a marked dynamical homeomorphism of target models
intertwining that projection with the one named at KKL lines 542--543.

The previous point-valued clause
`\(\pi(K_i)=\{\bar v_i\}\)` is retracted.  It conflated two quotient
levels.  Every nondegenerate primitive small-Julia continuum \(K_i\)
contains two distinct finite-orbit points obtained from the two fixed
points of the quadratic-like return; Kiwi's map separates them.
Consequently the geometric image \(\pi_{\rm Kw}(K_i)\) is
nondegenerate.  Only a later carrier-tree quotient may send that image
to the abstract vertex \(\bar v_i\).

The corrected non-locally-connected lift requires all of the following:

1. a marked dynamical homeomorphism of target models intertwining the
   transported Kiwi and KKL projections;
2. \(T=\pi^{-1}(T_{\rm com})\);
3. selected inverse-sheet correspondence;
4. \(\pi(K_i)\subset\bar K_i\) for the actual geometric model
   continuum; and
5. complete limb, sheet, parent, and access-label compatibility.

These clauses remain open.  Therefore Gate N2, VAAPC-I, UPTCR, and MLC
remain open.  The corrected ledger checkpoint is
`465 total / 34 imported / 316 proved / 115 open`.
