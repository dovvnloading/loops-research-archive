# Issue #40 — missing bridge atlas: **end lifting / Shift Lemma / electrical pull-off / prime-end covers / return-spectrum**

**Date:** 2026-11-06. **Method:** direct web audit of Kahn–Kapiamba–Lyubich, *MLC for parabolically bounded primitive renormalization* [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1); Kahn–Lyubich, *A priori bounds for some infinitely renormalizable quadratics: IV. Elephant Eyes* [arXiv:2601.21905v1](https://arxiv.org/html/2601.21905v1); Ferreira–Jové, *Boundary behaviour of universal covering maps* [arXiv:2409.01070v1](https://arxiv.org/html/2409.01070v1); Bartholdi–Dudko–Pilgrim, *Correspondences on Riemann surfaces and non-uniform hyperbolicity* [arXiv:2407.15548](https://arxiv.org/abs/2407.15548). Existing native issue: [Issue #40](https://github.com/dovvnloading/loops-research-archive/issues/40).

**Status:** source-dependent **new synthesis, a proved elementary mass-dichotomy corollary of a published lifting theorem, and explicitly typed proof obligations**. Neither the end-promotion needed to apply Theorem 5.42 at a KKL marked cut, the Shift Lemma inclusion at recurrent critical gates, nor an electrical circuit comparison in the general KKL category has been established. This is a research roadmap with real acceptance/failure tests, not an MLC proof or independent specialist verification.

## Executive finding — there are TWO separate proof routes, neither requiring a global pointwise non-LC boundary quotient

**Route A (topological WAD witness-or-escape).** KKL already has **Theorem 5.42**: proper degree-1 ends of a finite-topology immersion carry a complete WAD lifting, with an exact dichotomy between arcs whose **both** ends stay in the prescribed source end set and arcs whose other end is **new**. Combine it with the paper's **WAD valuation contraction** (§2.7) and the **root-exposure terminality** of the preceding [native source proof](./kkl_native_root_exposure_absorption_20261106.md). The missing bridge is an actual *cut-open finite-topology end promotion*: produce a localized surface where the source-selected **marked prime-end cut** is a **whole proper degree-one end** in the precise sense of Theorem 5.42, and show that *new ends* from lifting are either charged as vertical width or meet the distinguished root-exposed critical block. Those two claims are **not** consequences of the theorem as printed.

**Route B (width-first, circumvent a no-periodic-interval theorem).** KKL already has an **Appendix A.15 Shift Lemma**: under a shifting base and one specific end/crest containment, the **unbreakable Wave width is at most 2**. §6.2 treats the complementary **breakable** part with a quantified terminality mechanism. It may suffice for *Wave amplification* to show that any actual critical-cut return either (i) gets root-exposed and terminates, (ii) satisfies the Shift Lemma hypotheses and has \(\mathcal W(S^{ubr})\le2\), or (iii) has significant breakable/escaped mass and enters the existing §6.2 terminality mechanism. That would bypass proving that *all* proper periodic marked intervals are forbidden. The missing step is an actual **critical-cut return -> shift/escape/breakable trichotomy**. It is NOT proved by KKL Proposition 6.9's PF eigenvalue alone.

## 1. KKL Theorem 5.42: a **survive-or-new-end** lift in the source itself

Exact source: [KKL §5.9, Theorem 5.42 and its application](https://arxiv.org/html/2606.27272v1#S5.SS9), HTML paragraphs following eq. (5.42)/(5.43), plus Appendix A.3.2.

Hypotheses **as printed**:
- \(i:V'\to V\) is a **holomorphic immersion of finite-topology open Riemann surfaces**;
- \(E'\) is a set of **whole ends of \(V'\)**, and \(i\) is **proper of degree one at every such end**;
- \(Y=\sum_jv_j\beta_j\) is a **valid WAD on \(V\)** with each represented arc having at least one endpoint on an end \(E=i(E')\).

Then a valid \(Y'\) exists with
\[
Y'\ge\sum_jv_j\beta'_j,
\]
and **for every original weighted arc occurrence \(j\)** either
- (survive) both ends of \(\beta'_j\) lie in \(E'\), with \(i_*\beta'_j=\beta_j\), or
- (escape) one end of \(\beta'_j\) is in \(E'\) but the other is **not**.

The proof actually lifts leaves of the partial proper foliation and splits the resulting WAD by relative endpoint type. **KKL applies this theorem to a localized immersion** \(\hat V_I\setminus\hat{\mathcal K}_I \to V_I\setminus\mathcal K_I\) in its own §5.9; thus it is not an unused abstract lemma.

### Proposition 1.1 — precise quantitative mass dichotomy (no extra analytic assertions)

For this **actual** source situation write \(W=\sum_jv_j=\|Y\|\ge0\). Let \(W_{\rm sur}=\sum_{j\in\mathrm{survive}}v_j\) and \(W_{\rm esc}=\sum_{j\in\mathrm{escape}}v_j\), **preserving all separate original occurrence labels** even if the lifted isotopy classes merge. Then
\[
\boxed{W_{\rm sur}+W_{\rm esc}=W.}
\tag{1.1}
\]
For every \(0<\eta<1\), one has the exact alternative
\[
\boxed{W_{\rm sur}\ge(1-\eta)W
\quad\text{or}\quad W_{\rm esc}>\eta W.}
\tag{1.2}
\]
The total prescribed lifted weight is at least \(W\) as a subdiagram of \(Y'\). This is a numerical consequence of Theorem 5.42, **not** the desired KKL interval non-return theorem.

**Proof.** Partition the original finite/indexed arc occurrences by the theorem's two exclusive endpoint alternatives; nonnegative weights add to \(W\). If \(W_{\rm sur}<(1-\eta)W\), then \(W_{\rm esc}=W-W_{\rm sur}>\eta W\). The source WAD dominance inequality gives the lifted lower bound. \(\square\)

**Two missing identifications, neither optional:** (i) a *proper end at a cut* must be **constructed**, not replaced by a single prime end merely by relabeling; (ii) an escape endpoint *outside \(E'\)* need **not** be the one planar root \(x\), so cannot be declared root-exposed/terminal without a **source-defined access-to-attachment charge**. New ends can belong to other punctures, non-LC Julia continua, or outer boundaries. Their WAD mass must be classified using actual proper paths/Carathéodory attachment, or converted to genuine vertical width via the source's canonical decomposition.

**Concrete source-native test:** For each remaining **root-avoiding internal critical-cut state** of the [finite gate graph](./kkl_native_finite_critical_cut_first_return_graph_20261106.md), choose its genuine rectifiable arc family in a neighborhood of the critical gate, construct a **cut-open finite-topology pair** and verify end degree one. If this fails, identify exactly which crosscut accumulates at the added continuum or which end has degree greater than one; that is a sharp geometric first-failure certificate. If it passes, apply (1.2) to a native nonzero WAD and trace the surviving versus escaped endpoints through \(f_*\).

## 2. A source-level **Shift Lemma** may make some residual cycles irrelevant to *wide* Waves

Exact source: [KKL Appendix A.3.4, Lemma A.15](https://arxiv.org/html/2606.27272v1#A3.SS4), and §6.2 (Propositions 6.10–6.11, particularly the estimates around eqs. (6.15)–(6.19)).

A connected multi-interval \(B\) is **shifting** when \(F_*\) acts combinatorially on \(B\), and for **every constituent original marking atom \(\mathbf I\subset B\)**,
\[
\mathbf I\cap F_*\overline{\mathbf I}=\varnothing.
\tag{2.1}
\]

For an admissible Wave \(S\) subordinate to such a \(B\), with crest \(C\) and appropriate end \(E\Subset I\), **either** additional containment
\[
F_*\overline E\subset C
\quad\text{or}\quad E\subset F_*C
\tag{2.2}
\]
forces
\[
\boxed{\mathcal W(S^{ubr})\le 2.}
\tag{2.3}
\]

Thus a **wide** recurrent Wave satisfying (2.1)–(2.2) cannot have most of its width carried by its unbreakable part. The source's §6.2 already splits the remaining breakable part into \(A^{ver},A^{in},A^{out}\) and controls it via vertical width or wider waves. In particular §6.2 directly counts the number \(N\) of **improper** original marking atoms by
\[
\boxed{N\le 4\mathbf b(2\mathbf b+2),}
\tag{2.4}
\]
independent of \(q\) (source paragraph leading to eq. (6.17)). This is another **existing native uniform bad-site count** that should be combined with our \(r-1\le6\mathbf b-1\) internal critical-cut candidates—rather than independently enumerating all non-LC prime ends.

### New targeted *weaker* objective

Instead of the still-open absolute claim
\[
\text{“Every proper periodic critical-cut interval is impossible”},
\]
try to prove **for proof-used wide Waves only**:
> Every true native return around a root-avoiding internal critical cut either is source-root exposed; or has a **shifting marked segment with (2.2)**; or creates a **source-valid breakable/escaped WAD portion** carrying a definite fraction of width.

The first branch is terminal by [root-exposure absorption](./kkl_native_root_exposure_absorption_20261106.md). The second has its unbreakable width bounded by 2 by (2.3). The third can potentially use KKL's **already proved** breakable-wave terminality (Prop. 6.10); it is **not yet known** that the third has the required lower bound or source end markings. This program might close Wave amplification **without** repairing the literal universal Proposition 6.9 for intervals that are irrelevant to wide Waves.

**Non-implications:** Proposition 6.7 (proper on a good *limb corridor*) does **not** by itself imply shifting on an arbitrary crest that straddles adjacent limbs or contains a closed-only attachment. Likewise, repeating an interval alone does **not** guarantee either containment (2.2). The open/closed \(\iota^*\) audit remains essential.

## 3. **Elephant Eyes**: alternate proof by flux and pull-off, not marked-length monotonicity

Source: Kahn–Lyubich [arXiv:2601.21905v1](https://arxiv.org/html/2601.21905v1), §3.1.6 Lemma 3.8, §3.4, §6 Lemma 6.3 and Corollary 6.4, §7 Translation Property and Theorem 7.1.

This 2026 release treats **elephant-eye combinatorics**, a specific low-cluster regime with \(p=q+O(1)\). It supplies:
- **local width / flux inequalities** for holomorphic maps between partially marked disks (Lemma 3.8), and local crossing/boundary transformation estimates with additive errors (Lemmas 3.12–3.13);
- a **pull-off horizontal-weight loss** result: a last-legitimate-pullback map is **at most two-to-one**, giving definite loss and *new vertical* weight in the bounded/periodic regime (§6);
- **arbitrarily many disjoint translation domains** for sufficiently long periods (§7), allowing local width losses to be summed into a global amplification estimate (Theorem 7.1), independent of a prime-end marked-interval no-return claim.

### A plausible b-bounded “electrical aggregation” lemma to test (NOT proved)

If one can localize each of the at most \(\mathbf b\) small Julia continua per limb into a **bounded-topology bordered cluster** and control a **conformally natural effective Dirichlet-to-Neumann (conductance/flux) form** at its marked gates, then summing over many distant translated clusters could detect either:
1. **uniform loss of horizontal effective conductance**, converting to vertical width; or
2. sufficient horizontal WAD alignment with the original Hubbard tree to use KKL's native valuation contraction.

This strategy **does not require** a globally injective point-to-prime-end landing map, but the effective electrical form and source-legitimate arc decomposition **must be constructed from actual holomorphic surfaces**. A Schur complement of an *invented* finite resistor network is not an acceptable substitute. Also, KL26 is **not** a theorem for arbitrary \(\mathbf b\)-bounded prime primitive types; “one small Julia set per limb” and elephant-eye geometry must not be identified with *every* \(b=1\) case without source checks.

**Concrete falsification:** If a cluster's effective flux depends on arbitrarily many non-LC contact accesses in a way that cannot be bounded uniformly by \(\mathbf b\), the desired bounded-topology reduction fails. Alternatively if the additive loss in the source's transformation rules accumulates at order \(q\), it may swamp any local gain. Test those exact two points before claiming a global voltage/amplification theorem.

## 4. Ferreira–Jové: **prime ends as deck-equivalence classes** in multiply connected domains

Source: Ferreira–Jové, [arXiv:2409.01070v1](https://arxiv.org/html/2409.01070v1), especially Theorem 5.9 (accessible boundary points modulo the deck group) and Theorem 5.11 (regular, singular, parabolic prime ends using projected *admissible null chains*).

Theorem 5.11 says a **regular** universal-cover prime end is recognized by eventually **simply connected** projected crosscut neighborhoods, while singular ends have **infinitely connected** neighborhoods; impressions can be non-singleton. Theorem 5.9 identifies accesses to a fixed **accessible point** with radial preimages modulo the **deck group**, subject to its stated hypotheses. Do not conflate these two theorems: access to a singleton accessible **point** and a general **prime end with nontrivial impression** are different types.

**Proposed application:** work first on \(U\setminus\mathcal K\) (many holes), not on an assumed globally quotiented \(U\setminus\mathcal T\). For each actual proof-used critical-cut and each candidate WAD dual arc, choose a source/target universal-cover null-chain; verify **regularity and uniqueness modulo the true deck group**; construct a cut-open **finite-topology local sector** where KKL's Theorem 5.42 can be used. If a chain is singular or projected neighborhoods have infinite connectivity, record that as an explicit analytic obstruction and switch to the flux/pull-off branch, rather than fabricating a unique access.

**Missing theorem:** Ferreira–Jové does **not** prove that KKL's particular immersion \(\iota\) extends continuously over those ends or respects complete attached-component boundaries. Deck-equivalence **for one universal cover** also does not automatically identify ends of different source/target surfaces.

## 5. Bartholdi–Dudko–Pilgrim: a biset/“X-ray” language for the two arrows \(f,\iota\)

Source: [arXiv:2407.15548](https://arxiv.org/abs/2407.15548) (also author-hosted PDF). It studies a pair (covering, analytic map) \(T\rightrightarrows S\) via **bisets of path lifts**, and proves under *finite-area hyperbolic / admissibility* hypotheses a non-uniform contraction property and a finite attractor for lifted curve isotopy classes. A highlighted application concerns non-exceptional rational maps with four postcritical points.

KKL \(F=(f,\iota)\) has **the same two-arrow shape**, so a **biset of actual proper-path lift choices with end/side tags** could replace a guessed circle transition automaton. A genuine cycle of the internal critical-cut first-return graph would correspond to a **periodic admissible path-lifting word with monodromy**, not merely an equality of planar root points. Encoding the *monodromy tag* makes loss of the two covering sheets detectable.

**Essential caveat:** The published contraction theorem is **not directly applicable** to the unmodified KKL carrier annulus, whose hyperbolic ends do not automatically satisfy the finite-area assumptions; nor does a native prime-primitive stage necessarily have four postcritical points. The biset encoding is a promising **representation/interface**, and any contraction property must be proved anew on an actual localized KKL surface with appropriate hyperbolic geometry. No direct finite-attractor conclusion is claimed.

## 6. KKL Appendix C: **first-return** spectral growth survives one-step \(\lambda_q\to1\)

Source: KKL [Appendix C Theorem C.1](https://arxiv.org/html/2606.27272v1#A3), for its **specified cloned graph family** and its return cross-section matrix \(\hat T_\lambda\):
\[
\boxed{\lambda_n\to1,\qquad\lambda_n^n\to h(1).}
\tag{6.1}
\]
Thus using only one-step \(\lambda_n>1\) is potentially a **poor uniform invariant** for long parabolic tails. A return-normalized **positive dual WAD pairing** might retain a definite expansion across a whole inserted translation run, just as the source already does in its clone theorem. This complements the [physical limb-insertion time-change](./kkl_parabolic_tail_timechange_gate_holonomy_20261106.md) and our **finite critical-cut first-return graph**.

**Important source-proof audit:** In the proof of C.1, equation (C.5) asserts \(h(1)>1\) and gives as its explanation that \(\hat T_1\) is **primitive and integer-valued**. Those two properties **alone do not imply \(h(1)>1\)**: the \(1\times1\) matrix \([1]\) is primitive and integral with Perron root exactly 1. The *actual constructed* \(\hat T_1\) may well have extra branching that makes (C.5) valid; this is a **missing explanatory hypothesis/check**, NOT a counterexample to the cloned graph theorem or to KKL. Verify a genuine source-defined **branching/strict PF** certificate for \(\hat T_1\) before using uniform return growth.

Also (6.1) is a theorem for the paper's **specific clone construction**, not automatic for the nonlinear \(\iota^*\) dynamics of *all* prime primitive parabolic tails. A real transfer must identify the actual first-return WAD operator with an appropriate \(\hat T_\lambda\) or bound it via a proved domination inequality.

## 7. A deliberately narrow one-gate experiment that could settle the missing positive witness

Do not start by enumerating every non-LC prime end or writing a longer Markov simulation. Fix one actual KKL stage and choose one **root-avoiding internal critical marked cut** from the finite family of at most \(2(r-2)(12\mathbf b-1)\) continuing short crest candidates (under the selected-root placement of the companion root-exposure theorem).

**Input:** its exact \(\mathcal I\)-marked open atom/cut data, source \(\mathcal T'=f^{-1}\mathcal T\), selected root access and true KKL proper-path \(\iota^*\), and one actual bivertical arc crossing the critical gate.

**Try the following yes/no tests in order:**

1. **Null-chain regularity:** Can the cut's original source/target proper crosscuts be represented by a Ferreira–Jové regular end chart and a **finite-topology cut-open source/target immersion**?
2. **Degree-one proper end:** Is the localized \(\iota\) *proper and degree 1 at the entire promoted end*? If no, record the exact first crosscut that hits an attached branch and pass to the **escaped-end / root-terminal** analysis; never silently apply KKL 5.42.
3. **WAD mass dichotomy:** If yes, apply 5.42 to an actual nonzero horizontal WAD \(Y\). Charge **each** lift either to a matched horizontal dual arc or to a **genuine new source end**. Its total prescribed mass is not lost; a fixed fraction survives or escapes by (1.2).
4. **Root/vertical charge:** Prove any escape mass meets the *source-selected root-exposure* access (so the corresponding closed crest terminates) **or** contributes a controlled positive amount to canonical vertical WAD width. This is the **main unproved analytic bridge**; absence of it is a precise first-failure certificate.
5. **Recurrent width fallback:** If a true critical-cut return persists, test the actual \(\iota^*\)-based shifting criterion and both A.15 end/crest inclusions. If these hold, its unbreakable Wave width is **at most 2**; the source's §6.2 then handles substantial breakable width, subject to its source conditions.
6. **One-tail transport:** Only after a native stage works, test whether a balanced Branner–Douady limb insertion carries the entire cut-open end/WAD packet through the extra one-step/two-step clock phase. A physical point embedding alone is insufficient.

**Acceptance outcome:** a source-certified proper-end diagram with either (i) a nonzero dual WAD that genuinely dominates an inverse-return in the forbidden direction, or (ii) a quantified escape/terminal or Shift-Lemma outcome, and no false cut-stalk cancellations. **Failure outcome:** the first actual cut whose null chains, degree-one end, WAD escape charge, or shifting-end inclusion cannot be verified. Both are more informative than another finite synthetic circle regression.

**Ledger:** Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, and MLC remain **OPEN**. This new cross-paper atlas is **not** a complete native prime-end realization, and no independent expert review is claimed.
