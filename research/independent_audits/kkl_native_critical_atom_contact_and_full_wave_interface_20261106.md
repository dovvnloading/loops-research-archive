# Issue #40 — closed-crest contact automatically gives a **full-atom critical encounter**

**Date:** 2026-11-06.  
**Scope:** source-defined **endpoint/interval bridge** for the actual KKL Wave-crest marking. Under the previously proved high-rotation active short-Wave theorem, this eliminates the *last independent endpoint-only critical-encounter hypothesis* from the corrected bounded-visits argument. It does **not** prove that every proper periodic critical-return interval has a positive bivertical/WAD witness and does **not** close Wave amplification or MLC.

**Primary KKL v1 source:** [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §4 preceding Lemma 4.8: \(\mathbf L_j=\partial_C\mathcal L_j\) is an **open connected \(\mathcal I\)-multi-interval**; §6 definition of critical visit: the *closed crest image* \(F_*^{m}C_A\) meets \(\mathbf L_0\) and lies in the succeeding Wave's crest \(C_B\); §6.1 Props. 6.5–6.6: open/closed native immersion pullbacks separately defined; Appendix A.1: marking atoms are pairwise disjoint **open** prime-end intervals and a multi-interval is an open connected union of whole atoms and marked endpoint cuts. The actual dynamical surface is the KKL annular carrier complement; no pointwise planar ray landing or monotone boundary quotient is assumed.

Companions: [large-\(q\) short-Wave proper-base theorem](./kkl_short_wave_proper_base_large_rotation_20261106.md); [proper-base noncrossing crest theorem](./kkl_wave_nonempty_crest_noncrossing_20261106.md); [canonical active Wave](./kkl_active_wave_canonical_base_20261106.md); [dual-WAD and corrected visit count](./kkl_dual_arc_wave_core_reduction_20261106.md).

## 1. Finite original marking geometry

Let \(C=\partial_C^{\mathrm{in}}(\mathcal U\setminus\mathcal T)\) be the **actual** inner prime-end circle with its finite original vertex-side ideal marking \(\mathcal I\). Its atoms are open arcs separated by finite marked cuts. Let \(L\subset C\) be any **open** multi-interval consisting of a positive number of consecutive full marked atoms and the internal cuts between them (in particular \(L=\mathbf L_0\) is allowed).

Let \(J\subsetneq C\) be a positive-length **open connected** marked multi-interval, with \(C_J=\overline J\) its usual regular closed marked arc. Its endpoints are original marking cuts and \(J=\operatorname{Int}_C(C_J)\).

### Lemma 1.1 (the marked-cut contact lemma)

If
\[
\boxed{C_J\cap L\ne\varnothing,}
\tag{1.1}
\]
then there exists an **entire original marking atom** \(\mathbf I_a\in\mathcal I\) such that
\[
\boxed{\mathbf I_a\subset J\cap L.}
\tag{1.2}
\]

In particular a *regular positive closed crest* can **never** meet an **open limb** only at one of its own marked boundary cuts.

**Proof.** If the intersection contains any point in the **interior of one marking atom** \(\mathbf I_a\), the marked-block property of \(C_J\) and \(L\) means the whole atom belongs to both. We are done. Suppose the intersection contains only marked cuts. Choose a cut \(e\in C_J\cap L\). Since \(L\) is open, this cut is an **internal** cut of the limb's full-atom block, and the two original atoms adjacent to \(e\) both belong to \(L\). Since \(C_J=\overline J\) is a **closed positive connected marked block** with its cut endpoints in the marking, at least one of the two adjacent atoms to \(e\) belongs to its open interior \(J\): if \(e\) is internal to \(J\), both do; if \(e\) is an endpoint of \(C_J\), its inward neighboring atom does. Thus one adjacent full atom is in \(J\cap L\), contradicting the supposition that only cut points meet. This establishes (1.2).

Equivalently, lift the relevant circular blocks to the ordered **integer** marking cuts of \(\mathbb R\), writing \(C_J=[s,t]\), \(J=(s,t)\), \(L=(a,b)\), all endpoints integer with \(s<t\), \(a<b\). If the closed and open intervals intersect, then \(s<b\) and \(a<t\). Consequently \(j=\max(s,a)\) satisfies \(j\ge s,a\) and \(j+1\le t,b\); the open unit atom \((j,j+1)\) lies in both intervals. This integer implication is formalized in the companion Lean file. \(\square\)

**Crucial specificity:** This lemma requires **\(L\) open**, as the real KKL limb \(\mathbf L_0\) is. For a *closed* comparison set meeting \(C_J\) at an outer cut, full-atom contact need not follow. The statement does not equate \(F_*C_J\) with \(\overline{F_*J}\) and cannot be used without the regular closed-block hypothesis.

## 2. Theorem — genuine short critical successors automatically have full-atom visits

Let \(F=(f,\iota)\) be an actual KKL parabolically \(\mathbf b\)-bounded prime primitive stage of rotation \(1/q\), with the original full vertex-side limb marking, and assume

\[
q\ge24\mathbf b.
\tag{2.1}
\]

### Theorem 2.1 (native critical-visit atom realization)

Suppose \(B\) is a genuine **short** Wave and is a critical visit of \(A\) in the source's §6 sense: for some \(m\ge1\), the actual closed-input action \(F_*^mC_A\) is defined, nonempty, meets the **open critical limb** \(\mathbf L_0\), and
\[
F_*^mC_A\subset C_B.
\tag{2.2}
\]

Then \(B\) has a uniquely determined **active proper minimal base and positive regular crest** in the category of the companion canonical-Wave theorem, and its open marked crest core

\[
J_B=\operatorname{Int}C_B,\qquad C_B=\overline{J_B}
\]

satisfies
\[
\boxed{\exists\ \mathbf I_a\in\mathcal I,\quad
\mathbf I_a\subset J_B\cap\mathbf L_0.}
\tag{2.3}
\]

**Proof.** Since the actual image \(F_*^mC_A\) meets \(\mathbf L_0\), it is nonempty. Its inclusion into \(C_B\) therefore implies \(C_B\ne\varnothing\) and \(C_B\cap\mathbf L_0\ne\varnothing\). By the [short-Wave proper-base theorem](./kkl_short_wave_proper_base_large_rotation_20261106.md), \(B\) has a **proper** minimal base under (2.1). By the [noncrossing no-point-crest theorem](./kkl_wave_nonempty_crest_noncrossing_20261106.md), its nonempty crest is a **regular closed marked interval** \(C_B=\overline{J_B}\) with \(J_B\) positive and connected. The [active canonicality theorem](./kkl_active_wave_canonical_base_20261106.md) makes this base and the nonempty-crest end pair intrinsic. Apply Lemma 1.1 to \(C_J=C_B\) and \(L=\mathbf L_0\). This gives the full-atom conclusion (2.3). \(\square\)

**Important source distinction:** The theorem proves \(\mathbf I_a\subset J_B\cap\mathbf L_0\), **NOT** that \(F_*^mJ_A\cap\mathbf L_0\) contains an atom. That stronger statement may fail because closed-only attached-component boundaries can birth atoms at the source-defined \(\iota^*\) endpoint. The corrected **constant-length plateau** argument only needs \(J_B\) to meet the critical limb in a full atom: when successive cores have the same length and are nested through \(F_*^{m_i}\), the inclusion becomes equality, producing a genuine forward-orbit critical encounter. Without plateau equality, no critical encounter for the image of the *previous open core* is asserted.

## 3. A truly source-compatible Wave-to-interval reduction

Suppose a chain of actual **short critical successor** Waves \(A_1,\ldots,A_N\) satisfies the source's closed crest inclusions, with \(q\ge24\mathbf b\). By Theorem 2.1 every \(J_i=\operatorname{Int}C_{A_i}\) is a connected **positive** open marked multi-interval meeting \(\mathbf L_0\) through a full atom. The monotone native proper-path pullback (KKL Appendix A.3.2) and Proposition 6.6 give
\[
\boxed{\Phi^{m_i}J_i\subset J_{i+1},\qquad\Phi=F_*.}
\tag{3.1}
\]

There is no need to replace \(F_*^m\overline J\) with \(\overline{F_*^mJ}\). If a proper open image saturates the entire boundary it cannot be contained in a proper succeeding crest, so such a chain terminates.

**Proposition 3.1 (growth reduced to a single critical-return nonperiodicity lemma).** Add just the following independently formulated source-domain assumptions:

- \(\Phi\) preserves nondecreasing original marked length along proper marked iterates (as required by the corrected interval-growth repair);
- every **proper positive-length periodic marked interval whose orbit contains a full-atom encounter with \(\mathbf L_0\)** is impossible (the remaining **native dual-WAD witness/nonreturn** gate);
- all relevant closed and open iterates are well defined with the source's actual endpoint/attachment data.

Then the corrected strict \(r+k-1\) counting argument of the companion dual-WAD note applies to the actual short critical chain, with \(r\le6\mathbf b\) from KKL Lemma 4.8 and all core lengths \(1\le k_i<12\mathbf b\) when short crest length bound holds. In particular the conditional \(N<216\mathbf b^2\) critical-transition bound follows **without separate assumptions of positive crests, canonical bases, full-atom critical visits, or a disconnected full-base action**.

**Proof.** Canonical positive cores and inclusions are above. Along a constant-length block, inclusions of same-length connected marked intervals are equal; the selected visit times hence form a single deterministic \(\Phi\)-orbit and each visiting state contains a full critical atom by (2.3). There are at most \(r+k-1\) such length-\(k\) states. The strict pigeonhole lemma forces a repeated **critical-return** state, excluded by the stated nonperiodicity assumption. Therefore every block of \(18\mathbf b\) visits increases length, and \(\ell<12\mathbf b\) bounds the number of blocks as in the corrected theorem. \(\square\)

The **last line is conditional**, not a proof of the previously missing interval nonreturn or its native dual witness. The geometric crest/subordination assumptions have been discharged **within the large-\(q\) short critical-visit category**, but the analytic return obstruction remains.

## 4. Lean kernel scope and remaining gates

The Lean module \`formalization/weighted/NativeWaveGate.lean\` certifies the integer cut-overlap lemma
\[
[s,t]\cap(a,b)\ne\varnothing
\ \Longrightarrow\
\exists j\in\mathbb Z:\quad s,a\le j,\quad j+1\le t,b,
\]
expressed using the strict integer conditions \(s<b\), \(a<t\), as well as the strict critical-state pigeonhole and positive Perron/WAD algebraic return contradiction. It does **not** check that KKL's actual \(\Phi\) maps are admissible or supplies the missing dual witness, and it does **not** formalize annular Jordan crossing or non-LC prime-end impressions.

**Narrowest next research gate:** Prove that a hypothetical **proper positive-length periodic critical-return marked interval** produces a nonzero native bivertical WAD witness with the forbidden inverse-return domination direction, using the genuine source carrier crosscuts and KKL §§2.6–2.7. Equivalently find a direct native no-return theorem. Alternatively exhibit the first source-defined counterexample. At high \(q\), no independent Wave crest positivity, base-choice, full-base, or endpoint-only critical encounter gate remains under the stated source hypotheses.

**Do NOT promote** KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, or MLC. **Issue #40 remains OPEN.** All topological/analytic lemmas are research proofs pending independent specialist review.


## Postscript — the residual positive return gate is **only an internal critical cut**

The [native critical-cut gate theorem](./kkl_native_critical_cut_gate_reduction_20261106.md) sharpens Proposition 3.1 here. KKL §6.1 says \(\Phi(\mathbf L_0)=C\), so **no continuing proper orbit state can contain the entire critical limb**. If it intersects the critical limb in a full marked atom but remains proper under another iterate, then one endpoint of that interval must be an **internal original marking cut of \(\mathbf L_0\)**. There are only \(r-1\) such cuts, with two possible interval-side orientations per fixed marked length, \(r\le6\mathbf b\). Thus the remaining critical-periodic-state witness/acyclicity problem is **finite-gate localized independently of \(q\)**. If \(r=1\), the proper periodic critical-return obstruction is already excluded using only saturation; no dual-WAD theorem is required in this special case.

The improved conditional visit bound is \(N<(2r-1)(12\mathbf b-1)\le(12\mathbf b-1)^2\). The only unproved part is excluding actual periodic internal-cut gate cycles for \(r\ge2\), together with source-defined closed/action well-typedness and proper length monotonicity; **not** crest positivity, base choice or endpoint-only critical intersection at \(q\ge24\mathbf b\).
