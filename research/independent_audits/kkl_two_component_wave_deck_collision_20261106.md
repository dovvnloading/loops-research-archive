# Issue #40 — two-component closed-Wave crests and an **exact native deck-collision formula**

**Date:** 2026-11-06.  
**Status:** a source-typed **finite-component extension** of the KKL open/closed carrier interval action and an exact intrinsic two-sheet collision formula, valid on the actual degree-two annular prime-end covering, **without assuming local connectivity or a global immersion boundary quotient**. This closes the *classification* of the possible full-base Wave crest topology; it does **not** yet establish all original critical-Wave inclusions, positive dual-WAD visibility, or the repaired interval-growth theorem.

**Primary source:** Kahn–Kapiamba–Lyubich [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), Appendix A.1 (ends, crest), A.3.1/A.3.2/A.3.4 (actual covering \(f_*\), immersion proper-path pullback \(\iota^*\) and separately defined closed-input action), §6.1 Proposition 6.5 (full attached-component boundary formula and connected pullbacks), Proposition 6.6 (combinatorial action). The companion [noncrossing crest theorem](./kkl_wave_nonempty_crest_noncrossing_20261106.md) proves all nonempty proper-base crests are regular positive and eliminates a completely zero-atom full-base short crest for large marked rotation.

## 1. The full-base crest has at most **two** components

The actual inner Carathéodory boundary \(C=\partial_C\mathcal T\) is a topological circle in the annular carrier setting, without assuming singleton impressions. An original KKL Wave \(A\) with full base \(B_A=C\) has two *minimal connected open marked* end multi-intervals \(E_-,E_+\subset C\) and crest

\[
C_A=C\setminus(E_-\cup E_+).
\tag{1.1}
\]

### Lemma 1.1 (two-component topology and one possible isolated gate)

The set \(C_A\) is a union of **at most two** compact connected arcs/points. Its components are canonical, disjoint, and in the finite original marking each is either:
- a **positive closed marked interval** \(D=\overline J\) with \(J\) a connected open marked multi-interval of positive length; or
- a **single marked endpoint** \(\{e\}\).

If \(A\) is short and \(M=|\mathcal I|\ge24\mathbf b\), at least one component contains a full original marking atom. Consequently **at most one component can be endpoint-only**.

**Proof.** The union of two connected open subsets of a circle has either one or two connected components (including the entire circle as a special case). Its closed complement consists of at most two closed arcs or singleton points, with boundaries at original marking cuts. Because the ends and their union are unions of full open atoms and marked cuts, each nondegenerate complementary component contains complete atoms, and its interior is a connected open marked multi-interval whose closure is the component. For a short full-base Wave the source gives \(\ell(E_\pm)<12\mathbf b\). If the crest contained no full atom then every one of the \(M\) atoms would be covered by \(E_-\cup E_+\), contradicting \(M\ge24\mathbf b\) by the strict integer bound \(M\le\ell(E_-)+\ell(E_+)\le24\mathbf b-2\) established in the companion theorem. With at most two components, if one has a positive atom, there can be at most one remaining singleton component. \(\square\)

This proves a **native, LC-free topology reduction**, not a claim that an isolated endpoint component is necessarily a valid input for all \(\iota^*\)-iterations.

## 2. A **typed** componentwise closed action—what it does and does not solve

For a compact set \(D\subset C\) whose connected components \(D_1,\dots,D_s\) are **all positive closed original marked multi-intervals** (so \(D_i=\overline{J_i}\), \(\ell(J_i)>0\)), define the *componentwise extension* of the true KKL action by

\[
\boxed{
\widehat F_*(D):=\bigcup_{i=1}^s f_*(\iota^*D_i).
}
\tag{2.1}
\]

Each \(\iota^*D_i\) is **the actual source-defined proper-path restriction**, with **all** attached-component boundaries eligible at its closed endpoints (Proposition 6.5), not a closure of an open pullback. This is therefore a canonical extension of the already defined **connected** action to **finite unions** of connected positive closed pieces; no synthetic circle quotient is supplied.

### Theorem 2.1 (canonical component count and inclusion)

Under the actual annular source/target covering hypotheses, the operation in (2.1):

1. agrees **exactly** with the native \(F_*D\) for one positive connected closed marked interval \(D\);
2. is independent of the order of the canonical components and is **finite-component monotone** on pairs \(D\subset E\) for which all positive components remain in the stated domain;
3. has an image with **at most \(s\)** connected components, each a compact connected interval or the whole boundary circle.

**Proof.** Proposition 6.5 makes every \(\iota^*D_i\) a connected source prime-end interval. The actual covering \(f_*\) is continuous on the inner circles of genuine annular complements, hence its image of such a compact interval is compact and connected. A union of \(s\) connected sets has at most \(s\) connected components, proving item 3. Item 1 is the definition of the native closed input. If \(D\subset E\), every connected component \(D_i\) lies in some connected component \(E_j\); the native proper-path restriction is monotone under inclusion by its universal definition, and a continuous image preserves inclusion. Therefore \(\widehat F_*(D)\subset\widehat F_*(E)\), proving item 2. \(\square\)

**Strict limitation:** \(\widehat F_*\) is an explicitly **defined extension**, not an assertion that KKL Appendix A.3.4 already defined \(F_*\) on **disconnected** crests. If one component is an isolated endpoint \(\{e\}\), the source's closed-multi-interval definition does not automatically give the entire required action; such components must be separately certified by proper-path endpoint data. Likewise, iteration is defined only when successive outputs have the required finite closed marked decomposition. This is the exact type work needed before treating a full-base crest as one connected input.

## 3. The **exact** two-sheet collision identity

Let \(p:C'\to C\) be the genuine oriented degree-two covering on inner prime-end circles induced by \(f\), under the actual annular hypothesis. Its nontrivial deck involution

\[
\tau:C'\longrightarrow C'
\]

is intrinsic: \(p\circ\tau=p\), \(\tau^2=\operatorname{id}\), and every fiber is precisely \(\{x,\tau(x)\}\). In conformal angular charts, \(p(t)=2t\pmod1\) and \(\tau(t)=t+\frac12\pmod1\), but **the theorem below is coordinate-free**.

### Theorem 3.1 (two-component fiber-intersection formula)

For **arbitrary subsets** \(J_1,J_2\subset C'\), without any LC or impression restriction,

\[
\boxed{
p(J_1)\cap p(J_2)
=
p(J_1\cap J_2)\ \cup\
p(J_1\cap\tau(J_2)).
}
\tag{3.1}
\]

In particular, if the actual immersion pullback pieces \(J_1=\iota^*D_1\) and \(J_2=\iota^*D_2\) are **disjoint**, then

\[
\boxed{
p(J_1)\cap p(J_2)
=
p(J_1\cap\tau(J_2)).
}
\tag{3.2}
\]

Thus **every collision between distinct components** comes from the *single actual deck-pair relation*. No other cancellation mechanism exists for the covering on these two packets.

**Proof.** If \(y\in p(J_1)\cap p(J_2)\), choose \(x_1\in J_1,x_2\in J_2\) with \(p(x_1)=p(x_2)=y\). The actual degree-two fiber has precisely the points \(x_1,\tau(x_1)\), so either \(x_2=x_1\) (the first set of (3.1)) or \(x_2=\tau(x_1)\) (the second). Conversely, if \(x\in J_1\cap J_2\) or \(x\in J_1\cap\tau(J_2)\), then \(p(x)\in p(J_1)\cap p(J_2)\), using \(p\circ\tau=p\). This proves (3.1). If the source sets are disjoint the first term vanishes, giving (3.2). \(\square\)

**Native status:** The formula depends only on the **actual holomorphic degree-two cover**. The immersion \(\iota^*\) determines the two source sets, including attached trees, and is not approximated or replaced by a monotone circle map. The theorem remains valid for arbitrary non-singleton impressions because prime ends, not planar points, are its inputs.

### Corollary 3.2 (exact proper-image angular multiplicity deficit)

Assume \(J_1,J_2\subset C'\) are disjoint measurable **connected** intervals and **both** images \(p(J_i)\) are proper. Let \(\mu'\) and \(\mu\) denote normalized angular Lebesgue measure on the actual annular prime-end coordinates of \(C'\) and \(C\). Then

\[
\boxed{
\mu\bigl(p(J_1)\cup p(J_2)\bigr)
=2\mu'(J_1)+2\mu'(J_2)
-2\mu'\bigl(J_1\cap\tau(J_2)\bigr).
}
\tag{3.3}
\]

**Proof.** By the proper connected-image injectivity theorem from the preceding [two-sheet access note](./kkl_native_two_sheet_access_20261106.md), \(p\) is injective on each \(J_i\), and the conformal angular coordinate has slope two. Thus \(\mu(p(J_i))=2\mu'(J_i)\). Equation (3.2) and injectivity on the subset \(J_1\cap\tau(J_2)\) give \(\mu(p(J_1)\cap p(J_2))=2\mu'(J_1\cap\tau(J_2))\). Apply measure inclusion-exclusion to the target image union to obtain (3.3). \(\square\)

**Interpretation:** The **only** missing multiplicity term is an actual \(\tau\)-overlap of the two source packets. This is an **angular-access** mass statement, *not* a Perron–Frobenius Hubbard-edge weight identity and not the original marked length \(\ell_{\mathcal I}\). It is nonetheless an exact analytic checksum that a proposed native two-component Wave transport must satisfy.

## 4. What remains of the Wave interface

By the previous [noncrossing theorem](./kkl_wave_nonempty_crest_noncrossing_20261106.md), a proper-base admissible Wave with nonempty crest has a **single regular positive** closed component, so the ordinary native action and positive-core transport apply directly. For a full-base short Wave with \(M\ge24\mathbf b\), the crest has at least one positive component and *at most one possible isolated endpoint component*. Its **positive part** has at most two connected components and can be propagated by \(\widehat F_*\) (subject to marking-aligned iterates); its isolated endpoint part, if present, remains an explicit source-defined \(\iota^*\) gate obligation.

The new theorem says the *two-positive-component* difficulty is **precisely**:

1. **Source merging:** if the full attached-boundary pullbacks \(J_1,J_2\) meet, treat their union as one source connected packet (check marked endpoints carefully).
2. **Covering deck collision:** if they remain disjoint, compute \(J_1\cap\tau(J_2)\). If empty, the target positive components remain disjoint; if nonempty, their overlap is **exactly** (3.2), with angular multiplicity loss (3.3) for proper images.

This leaves a narrow source-specific question: can a critical-visit packet with a **full-base two-component crest** have nontrivial deck overlap while remaining **proper, nonterminal and short**? If not, all positive-crest interval-growth bookkeeping can be done componentwise, without classifying every prime end at the critical root. If so, the overlap creates an explicit **two-sheet collision certificate**; it must be charged as multiplicity, not silently canceled in a union.

This is **not** the final Wave theorem. The original proposition's \(F_*\) on disconnected crests, the possible isolated endpoint component, and the critical-return positive dual-WAD witness remain unproved for every native KKL stage.

## 5. Adversarial checks / bounded scope

- A **single** proper connected pullback interval cannot fold under the covering. Only **different components** can overlap via the deck involution (or first merge in the immersion restriction).
- A planar **one-root** attachment point may represent multiple prime-end accesses; do not substitute a planar-root equality for the intrinsic deck relation \(\tau\).
- A full-base crest can have a **singleton component** even when its **total** crest length is positive. Its closed-only proper-path access transport is **not** automatically defined by (2.1).
- Formula (3.3) is about **conformal angular measure of access sets**. It cannot be used as KKL's Perron edge mass or as \(\ell_{\mathcal I}\) without a separate transfer theorem.
- If either \(p(J_i)=C\), enter the **saturated** case and do not invoke single-sheet angular formula (3.3).
- The componentwise extension is **a new typed definition**, not a license to treat every union of intervals as a connected multi-interval in the source's A.3.4.
- The theorem is unconditional for **actual degree-two annular coverings**, but the annularity/closed-block realization of a wild lifted carrier is an independently stated stage hypothesis.

**Status:** real finite-component crest reduction and genuine double-cover multiplicity formula; **Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, and MLC remain OPEN**. No independent specialist proof review or new priority claim.
