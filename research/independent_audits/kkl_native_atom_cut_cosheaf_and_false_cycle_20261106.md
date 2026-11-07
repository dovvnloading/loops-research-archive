# Issue #40 — a **cut-augmented prime-end cosheaf** and a holomorphic *false return-cycle* certificate

**Date:** 2026-11-06. **Status:** a new source-defined **attachment-locality criterion** for an exact finite *atom-plus-cut* presentation of the actual KKL immersion interval action, and an **explicit holomorphic Misiurewicz example** in which the usual atom-word action predicts a periodic proper two-cycle that the genuine full \(\iota^*\) **destroys by saturation**. This is *not* a synthetic countermodel: every arc, cut, covering map and attached component is obtained from the **same real quadratic polynomial**. The polynomial is *outside* the required prime primitive renormalization category, and the general attachment-locality criterion is an explicit missing native access theorem rather than an assumed global monotone quotient.

**Primary source:** Kahn–Kapiamba–Lyubich [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), Appendix A.1 (finite ideal marking, open atoms and marked endpoint cuts), Appendix A.3.2 (immersion pullback on **connected** subsets, including single marked cuts), §6.1 Proposition 6.5 (full attached-component Carathéodory boundaries for open/closed multi-intervals), Proposition 6.6 (combinatorial action) and Proposition 6.8 (source-selected root \(\iota^*x\)). Companion [exact Misiurewicz analytic atlas](./kkl_misiurewicz_actual_expanding_attachment_atlas_20261106.md) supplies the complete holomorphic coordinates used in §3.

## 1. The missing geometry is **zero-cells**, not just edge transitions

Let \(C=\partial_C^{\rm in}(\mathcal U\setminus\mathcal T)\) be the actual KKL annular prime-end circle with a **finite** original vertex-side marking

\[
C=\bigcup_{i=0}^{M-1}\mathbf I_i\ \cup\ \{e_0,\ldots,e_{M-1}\},
\tag{1.1}
\]

where \(\mathbf I_i\) are disjoint open **atom arcs** and \(e_i\) the marked **cut prime ends** (the latter are not necessarily unique planar landing points). For a connected **open** marked multi-interval \(J\) the source allows **internal marked cuts** to belong to \(J\), although its two outer boundary cuts are excluded. Thus

\[
J=\Bigl(\bigcup_{\mathbf I_i\subset J}\mathbf I_i\Bigr)
\ \cup\ \Bigl(\bigcup_{e_j\in J}\{e_j\}\Bigr).
\tag{1.2}
\]

In KKL §6.1, the immersion pullback \(R(J)=\iota^*J\) has the **actual** Proposition 6.5 form

\[
R(J)=H(J)\cup\bigcup_{X\in\mathscr A(J)}B_X,
\qquad
B_X=\text{the COMPLETE native Carathéodory boundary of }X,
\tag{1.3}
\]

where \(H(J)=\iota^{-1}(J)\) is the old-side portion and \(\mathscr A(J)\) is the set of added-tree components that the real proper-path relation declares eligible **over \(J\)**.

The old-side part is set-theoretic and respects unions. **But the full component family \(\mathscr A(J)\) need not be inferred from a finite atom-word transition list**: its eligibility may be triggered by an internal cut even when neither neighboring *open atom* pulls back that branch.

Define the **cellwise attachment-locality condition** \((\mathrm{CELL})_J\) as

\[
\boxed{
\mathscr A(J)=
\bigcup_{\mathbf I_i\subset J}\mathscr A(\mathbf I_i)
\ \cup\
\bigcup_{e_j\in J}\mathscr A(\{e_j\}).
}
\tag{1.4}
\]

This condition is a statement about the source-defined **proper-path attachment eligibility**, not about a globally continuous prime-end quotient. Its right-hand side uses only actual **atom and singleton cut** inputs, which Appendix A.3.2 defines as connected subsets. If an individual marked cut has more than one planar-access occurrence, \(\mathscr A(\{e_j\})\) must be computed using that **particular prime end**, not the common planar root label.

### Theorem 1.1 (exact atomic-cut cosheaf formula, under the smallest possible access-locality test)

For every proof-used connected marked multi-interval \(J\) satisfying \((\mathrm{CELL})_J\), the real KKL immersion pullback satisfies

\[
\boxed{
\iota^*J=
\bigcup_{\mathbf I_i\subset J}\iota^*\mathbf I_i
\ \cup\
\bigcup_{e_j\in J}\iota^*\{e_j\}.
}
\tag{1.5}
\]

Consequently, with the actual covering \(p=f_*\), its exact native interval action is

\[
\boxed{
\Phi(J)=p\Bigl(
  \bigcup_{\mathbf I_i\subset J}R(\mathbf I_i)
  \cup
  \bigcup_{e_j\in J}R(\{e_j\})
\Bigr).
}
\tag{1.6}
\]

The formula preserves **all source boundary components** \(B_X\) rather than replacing an attached branch by one planar point. It is an exact **cellular cosheaf-type gluing identity for this finite family of inputs**, not a claim that arbitrary subspaces of \(C\) have a globally defined boundary map \(q\).

**Proof.** Expand the right side of (1.5) by the actual union formula (1.3) for each marked atom and the connected singleton pullback of Appendix A.3.2; for this theorem we require the same attached-component description to be verified for those singleton inputs, as part of \((\mathrm{CELL})_J\). The old-side pieces unite to \(H(J)\), because the old near-carrier pullback is a set preimage and (1.2) covers all old atom and cut points in \(J\). The attached-component pieces unite to \(\bigcup_{X\in\mathscr A(J)}B_X\) **exactly** by (1.4). This is (1.3), proving (1.5). The covering \(p\) sends unions to unions as a set function, yielding (1.6). No pointwise map for \(\iota\) at interior points of attached source branches is used. \(\square\)

**What remains genuinely analytic:** In the full non-LC native KKL category the source does not explicitly prove (1.4) for *all* selected singleton access cuts, and its Proposition 6.5 is stated for **marked multi-intervals and their closures**, not arbitrary singleton inputs. Appendix A.3.2 defines \(\iota^*\{e\}\), but whether its full component census is precisely the one-root \(B_X\) family at that cut is **a theorem to establish**, not a notation change. If (1.4) fails, exhibit one actual component eligible for \(J\) but not for any of its constituent atom/cut accesses: that is the **first-failure witness**. The theorem is *not* an unproved unconditional distributivity claim.

## 2. Why the finite **marked cuts** are a more natural object than all prime ends

KKL Proposition 6.8 says every added component of \(\mathcal T'\setminus\mathcal T\) meets the old tree at one planar \(x\). The source either places \(x\) **inside one old marked atom** or treats \(x\) as an old **marked endpoint**, using \(\operatorname{Int}\iota^*x\). Thus a source-verified \((\mathrm{CELL})_J\) needs a **complete access block** only at the atom or cut containing the actual selected \(x\)-occurrence, plus the guarded trivial cut records away from the root. This is a **finite-support** proposal, not an assertion that every non-LC access impression containing the same planar \(x\) has been counted or collapsed.

In a genuine finite marked category, (1.5) means **the complete interval action is determined by the actual boundary-access stalks on 0- and 1-cells**. A finite image word listing only the \(\Phi(\mathbf I_i)\) does *not* give the \(\Phi(\{e_j\})\). The latter can carry full positive angular access intervals and can change properness to saturation.

This gives a different first-priority geometry theorem from a global prime-end atlas: **prove \((\mathrm{CELL})_J\) only for the at most \(2(r-1)(12\mathbf b-1)\) source-defined internal critical-cut states** of the companion [finite return graph](./kkl_native_finite_critical_cut_first_return_graph_20261106.md). Any stage for which those actual finite stalks are known supports exact return-gate computation; no image is invented by the model.

## 3. A full holomorphic **false two-cycle** destroyed by one internal cut

Use the actual periodically repelling quadratic from the companion Misiurewicz certificate:

\[
P_c(z)=z^2+c,\quad
c^3+2c^2+2c+2=0,\quad
T=[c,b],\ b=c^2+c,\quad T'=[c,-c],
\tag{3.1}
\]

with one genuine added branch \(X=(b,-c]\) at the old tip \(x=b\). The exact Joukowski conformal uniformizations satisfy

\[
P_c\Psi_{T'}(w)=\Psi_T(w^2);
\]

hence the **actual source-to-target covering** on prime ends is \(p(s)=2s\pmod1\). Let

\[
\theta=\frac{\arccos(-c-1)}{2\pi}\in(0,\tfrac14).
\tag{3.2}
\]

The exact source immersion contour has **one** entire attached root block

\[
R(\{0\})=B_X=[1-\theta,1]\cup[0,\theta]
\subset C',
\quad
p(B_X)=[1-2\theta,1]\cup[0,2\theta].
\tag{3.3}
\]

Importantly \(0\) is an **internal marked cut** of some open multi-intervals, not always an excluded endpoint.

Refine the target prime-end circle using **genuine actual vertex accesses** at

\[
0,\quad2\theta,\quad\tfrac12,\quad1-2\theta.
\tag{3.4}
\]

Denote its four open atom arcs by

\[
\begin{array}{ll}
A_0=(0,2\theta),&
A_1=(2\theta,\tfrac12),\\
A_2=(\tfrac12,1-2\theta),&
A_3=(1-2\theta,1).
\end{array}
\tag{3.5}
\]

From **the same analytic polynomial**, the open atom images are exactly

\[
\boxed{
\begin{aligned}
\Phi(A_0)&=(2\theta,1-2\theta)=A_1\cup\{\tfrac12\}\cup A_2,\\
\Phi(A_1)&=A_3,\qquad
\Phi(A_2)=A_0,\qquad
\Phi(A_3)=(2\theta,1-2\theta).
\end{aligned}}
\tag{3.6}
\]

These formulas follow by applying the source-defined old-side slit correspondence (no attached component is eligible for the **open** atom input) and then angular doubling. All four are genuine real holomorphic source diagrams, not an independently chosen word list.

Define two genuine **open connected marked intervals**

\[
J_{\rm mid}=(2\theta,1-2\theta)=A_1\cup\{\tfrac12\}\cup A_2,
\qquad
J_{\rm out}=(1-2\theta,1+2\theta)
=A_3\cup\{0\}\cup A_0
\quad\bmod1.
\tag{3.7}
\]

**The tempting atom-only rule is WRONG.** If one simply takes the union of the four atom images and fills the intervening cut to make a connected word, then (3.6) appears to give

\[
\boxed{
J_{\rm mid}\ \longrightarrow_{\text{atom-only}}\ J_{\rm out}\
\longrightarrow_{\text{atom-only}}\ J_{\rm mid}.
}
\tag{3.8}
\]

It is a perfectly coherent apparent **proper length-two cycle** in the atom-word language, even though the graph incidence matrix is derived from this same real polynomial.

### Theorem 3.1 (exact analytic *cut-defect* kills the apparent return)

For the **real** \(F_* = f_*\iota^*\) of this polynomial,

\[
\boxed{
\Phi(J_{\rm mid})=J_{\rm out},
\qquad
\Phi(J_{\rm out})=C.
}
\tag{3.9}
\]

In particular there is **no** actual proper two-cycle; it is destroyed by the whole attached boundary \(B_X\) born at the **internal marked cut** \(0\in J_{\rm out}\).

**Proof.** The source proper-path restriction of the middle interval is the old connected source arc
\[
R(J_{\rm mid})=(\tfrac12-\theta,\tfrac12+\theta),
\]
whose covering image is the proper arc \((1-2\theta,1+2\theta)\), i.e. \(J_{\rm out}\). On the next step the input \(J_{\rm out}\) contains the *marked cut* \(0\) **as an interior point**. Proposition 6.5's complete added-component rule inserts the whole \(B_X\) in the source, so
\[
R(J_{\rm out})=(\tfrac12+\theta,\tfrac32-\theta),
\]
a source circular interval of lifted span \(1-2\theta>\frac12\). Its image under the **actual degree-two covering** \(p\) is all of \(C\). Equivalently, applying the cellwise decomposition of this *explicit* slit geometry,
\[
\Phi(J_{\rm out})
=\Phi(A_3)\cup\Phi(\{0\})\cup\Phi(A_0)
=J_{\rm mid}\cup\overline{J_{\rm out}}=C.
\]
This proves (3.9). Note that \(\Phi(\{0\})\) is **not a point**: it is the entire closed positive-length arc \(p(B_X)\). \(\square\)

**An even sharper warning:** The missing block is already born for an **OPEN connected multi-interval**, because its internal **cut** is included. This is NOT only the previously known failure of \(F_*\overline I=\overline{F_*I}\) when an *outer endpoint* is added by closure. Both defects must be tracked independently.

## 4. Mathematical consequences for real KKL critical-return gates

The example provides an actual holomorphic falsification of the inference

> “An expanding/edge-faithful atom substitution plus correct images of each open atom is enough to determine the native interval first-return graph.”

It is **false even for a locally connected, strictly preperiodic-to-repelling real quadratic**. The omitted zero-cell stalk changes a putative **periodic orbit into immediate saturation**. The example is not a prime primitive renormalization and is **not** an Issue #40 all-native-category counterexample, but it is a direct analytic **adversarial test** for every proposed KKL gate certificate.

At a genuine KKL stage the correct finite return proof now has a clean possible interface:

1. **1-cell data**: retain every actual marked atom pullback and its edge traversals, already related to KKL's native bivertical \(T_F\) operator in §§2.6–2.7.
2. **0-cell data**: for each proof-used actual **internal critical cut**, compute its source-defined \(\iota^*\{e\}\) as a full **access block**, including every attached component eligible at that precise prime end.
3. **Locality check**: prove \((\mathrm{CELL})_J\) for the finitely many native critical return input intervals and every intermediate proof-used open/closed input. If locality fails, report that *exact* source access as the first-failure certificate; do not replace it with planar root labels.
4. **Cover and saturation**: apply the true degree-two \(f_*\) to the *union of all atom and cut stalks*. If the connected source pullback has angular span at least half a circle with the appropriate endpoint convention, it saturates. For proper images the covering restriction is injective, so no full source access block can silently disappear.
5. **Acyclicity**: on nonterminal length-preserving outputs, use KKL's actual critical-cut first-return graph and search for a strictly decreasing **root-block charge / dual-WAD weight / insertion holonomy rank**. A genuine cycle would be a real source-defined counterexample to the desired nonreturn, not a finite-word artifact.

**This is the new lens:** the entire problem can be formulated as a **cellular incidence/attachment gluing problem on the *original marked prime-end circle***, with *nontrivial geometric stalks over marked zero-cells*. It does not require a global continuous pointwise quotient at every unmarked prime end. The source's proper-path relation remains the only authority for the non-LC stalk geometry.

**Status:** exact analytic one-root cut-defect cycle elimination plus a conditional **native cellular cosheaf theorem** and a finite source-defined proof target. Not an all-native interval-growth repair, full Wave amplification or MLC proof. No new proof priority or specialist referee claim. **Issue #40 and all named ledger gates remain OPEN.**
