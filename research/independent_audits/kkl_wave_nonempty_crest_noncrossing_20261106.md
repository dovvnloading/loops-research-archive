# Issue #40 — an admissible-Wave **no-point-crest theorem** from planar noncrossing

**Date:** 2026-11-06.  
**Status:** a **new geometric theorem in the actual native marked-annulus category**, not a synthetic transition model. For a proper Wave base the nonempty crest is **automatically a regular positive marked interval**, even with composite minimal ends and non-locally-connected carrier impressions. A short Wave with full-circle base cannot have a nonempty zero-atom crest once the original marking has at least \(24\mathbf b\) atoms. The full-circle case with positive but possibly disconnected crest, and the missing native critical-return dual witness, are still open.

**Source lock:** Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), Appendix A.1 (actual ideal marking; every leaf of a Wave is a marked path *not subordinate to any multi-interval of length at most two*; smallest connected base and minimal ends; crest \(C=B\setminus(E_-\cup E_+)\)); §4 (original marking from sides of \(\widehat{\mathcal K}\)); §6, immediately before Proposition 6.2 (a short Wave has **each end length \(<12\mathbf b\)**). This note relies on **topology of actual proper arcs in the annular carrier complement**, not on graph valence, a rational-lamination point quotient or an invented expanding matrix.

## 1. A standard geometric lemma, stated with the correct homotopy type

Let \(V=\mathcal U\setminus\mathcal T\) be the actual annular carrier complement in a KKL stage, and \(C=\partial_C^{\rm in}V\) its inner prime-end boundary circle. Let \(\mathcal I\) be the finite original vertex-side marking. Each atom is an **open prime-end arc**, not a planar landing point. The planar continuum may be non-locally-connected.

Let \(B\subsetneq C\) be a **proper** connected open marked multi-interval and choose the linear cyclic cut at a point of \(C\setminus B\). Its atoms are consecutively \(\mathbf I_0,\dots,\mathbf I_{k-1}\). The lift \(\widetilde B\) to the universal covering of the annulus is a genuine real interval, possibly of nearly one full circumference; it is not an entire line.

### Lemma 1.1 (two-atom shortcut and alternating-end crossing)

Let \(\gamma,\delta\) be simple proper paths in \(V\), each **subordinate to the same proper base \(B\)** in KKL Appendix A.1's sense.

1. If the endpoints of \(\gamma\) lie in the same marked atom \(\mathbf I_j\), or in two **adjacent** atoms \(\mathbf I_j,\mathbf I_{j+1}\), then \(\gamma\) is subordinate to a multi-interval of combinatorial length at most two. **Thus it is not an admissible KKL marked path.**
2. If the four endpoints of \(\gamma,\delta\) occur in alternating order along \(B\), then their homotopy classes **have positive geometric intersection number**. Hence they cannot both be disjoint leaves of a KKL lamination.

**Proof.** The source's subordination condition says each path has a representative in **every** collar neighborhood of \(B\), rel its marked ideal endpoints. For (1), within a simply connected thin collar of the **proper** base arc, the class of a path joining these endpoints is that of the unique boundary subarc between them. If their atoms are the same or adjacent, this subarc lies in the corresponding one- or two-atom multi-interval, proving subordination to it.

For (2), lift both homotopy classes to the actual universal cover of the annulus, choosing the lift whose endpoints lie on the *same* real interval \(\widetilde B\). The chosen classes are boundary-parallel within the simply connected collar of \(\widetilde B\). Alternating ideal endpoints force any two proper crosscuts representing the classes to intersect, by the Jordan separation theorem in that collar. A different representative of the same rel-endpoint homotopy class cannot remove this essential intersection. Projecting to \(V\) proves positive geometric intersection. This uses *actual prime ends* and the source's subordination homotopy; it assumes no landing of impressions. \(\square\)

The **proper-base** hypothesis is essential: if \(B=C\), different winding/deck classes of paths in an annulus can be subordinate to the whole circle and the unique-short-boundary-subarc conclusion need not apply.

## 2. Theorem — no nonempty point-only crest for a proper base

Let \((A,B_A,E_-,E_+)\) be a **nonempty admissible base-tagged KKL Wave datum** in the actual marked annulus: \(B_A\subsetneq C\) is a **specified proper inclusion-minimal** base, and \(E_-,E_+\subset B_A\) are **specified minimal connected** end multi-intervals (each leaf has one endpoint in each). We do not assume that this base/end pair is *uniquely* determined by the underlying lamination. Set

\[
C_A=B_A\setminus(E_-\cup E_+).
\tag{2.1}
\]

### Theorem 2.1 (specified proper-base crest dichotomy)

\[
\boxed{
C_A=\varnothing\quad\text{or}\quad
\ell_{\mathcal I}(C_A)\ge1,\quad
C_A=\overline{\operatorname{Int}C_A},
\quad \operatorname{Int}C_A
\text{ is a connected open }\mathcal I\text{-multi-interval}.
}
\tag{2.2}
\]

In particular **a genuine admissible Wave with a **specified proper minimal base/end tag** cannot have a nonempty crest consisting only of one or more marked endpoints.** Every nonempty proper-base crest is a *regular positive marked crest* in the exact sense of the earlier dual-arc Wave-core reduction, even if the two minimal ends are **composite** and even if \(\mathcal T\) has non-singleton prime-end impressions.

**Proof.** Work in the linear order of the marked proper base \(B=B_A\), with atoms \(\mathbf I_0,\ldots,\mathbf I_{k-1}\). Minimality of the base ensures there is at least one *leaf endpoint* in each of the two **outermost base atoms**. Indeed, if an outermost atom had no endpoint, then by Lemma 1.1(1)'s **unique boundary-subarc property** every leaf would still be subordinate to the proper base obtained by removing that atom and its outer cut; this would contradict minimality of \(B\). (The argument is about the unique homotopy class in a proper boundary collar, not merely about the set of occupied endpoints.)

Because every leaf has one endpoint in each of \(E_-,E_+\), the union of these two connected end multi-intervals contains all leaf endpoints. Their minimality ensures each of their outermost occupied end atoms contains at least one leaf endpoint. If one end contained both outermost base atoms, it would contain all of \(B\), leaving \(C_A=\varnothing\). Thus for a **nonempty** crest the two ends occupy, up to exchanging labels, a **left prefix** and a **right suffix** of the linear base. They may either overlap, touch at one marked cut \(e\), or be separated by one or more full marked atoms.

If the two ends overlap, their union covers the base and \(C_A=\varnothing\). If they are separated by one or more entire marked atoms, their complement in \(B\) is a **single closed consecutive block** containing at least one full marked atom. It equals the closure of its connected open marked interior, giving (2.2).

It remains to exclude the **touching** case. Suppose that \(E_-\) ends immediately before \(E_+\) at a single marked endpoint cut \(e\), with \(\mathbf I_{j-1}\) the last atom of \(E_-\) and \(\mathbf I_j\) the first of \(E_+\). By **minimality of the two ends**, there is a leaf \(\gamma\) whose \(E_-\)-endpoint belongs to \(\mathbf I_{j-1}\), and a leaf \(\delta\) whose \(E_+\)-endpoint belongs to \(\mathbf I_j\).

If \(\gamma=\delta\), that leaf joins **adjacent** atoms and violates the marked-path admissibility of Lemma 1.1(1). Otherwise, write the other endpoint of \(\gamma\) in \(\mathbf I_r\subset E_+\), and the other endpoint of \(\delta\) in \(\mathbf I_\ell\subset E_-\). By Lemma 1.1(1), admissibility forces \(r\ge j+1\) and \(\ell\le j-2\): an opposite endpoint in \(\mathbf I_j\) or \(\mathbf I_{j-1}\) would give a two-atom shortcut. Consequently the four endpoints occur in the **alternating order**
\[
\ell\quad(\delta),\qquad j-1\quad(\gamma),\qquad
j\quad(\delta),\qquad r\quad(\gamma).
\tag{2.3}
\]
By Lemma 1.1(2), these distinct leaves must intersect, contradicting the lamination condition. Thus the touching case is impossible. The only nonempty crest is the separated **positive closed block**, completing the proof. \(\square\)

**Scope and review-critical assumption:** The theorem uses the **actual** source definition of the ends as *minimal connected multi-intervals* and the fact that each leaf has one endpoint assigned to each end. It uses no assumption that the ends are single atoms or that the lamination is connected as a subset. If a user-defined “Wave” allows a different, nonminimal/nonconnected end packet, the theorem need not hold for that different object. The full-circle base is deliberately treated separately below.

## 3. Full-circle bases: a quantitative *short-Wave* exclusion

Write \(M=|\mathcal I|\) for the finite number of original marked atoms on \(C\). Source §6 (paragraph before Proposition 6.2) explicitly shows that if a KKL Wave \(A\) is **short**, then

\[
\ell(E_-)<12\mathbf b,\qquad
\ell(E_+)<12\mathbf b.
\tag{3.1}
\]

### Theorem 3.1 (short full-base, zero-core exclusion for long markings)

Suppose \(A\) is a **short** admissible Wave with full base \(B_A=C\). If its crest contains **no complete marked atom**, then

\[
\boxed{
M\le \ell(E_-)+\ell(E_+)\le24\mathbf b-2.
}
\tag{3.2}
\]

Hence whenever \(M\ge24\mathbf b\), **every nonempty short Wave crest (including those with full-circle base) contains at least one full marked atom**.

**Proof.** If the crest contains no complete atom, every original marked atom lies in \(E_-\cup E_+\); otherwise its full open atom would survive in \(C_A=C\setminus(E_-\cup E_+)\). Counting the finite atoms gives \(M\le\ell(E_-)+\ell(E_+)\). The source's strict shortness bounds (3.1), with all counts integer, give \(\ell(E_\pm)\le12\mathbf b-1\), proving (3.2). \(\square\)

In a genuine rotation-\(1/q\) KKL cycle, §2.4 says the small Julia cycle visits the noncritical limbs successively and the critical value lies in \(\mathfrak L_1\). Consequently the cycle supplies a distinguished small filled Julia vertex in **each** of the \(q\) limbs. As §4 defines \(\mathcal I\) from sides of this vertex package, each such nonempty limb contributes at least one original marking atom. Thus **for the standard full vertex-side KKL marking**, \(M\ge q\), and \(q\ge24\mathbf b\) is a sufficient large-rotation criterion. To apply this to a nonstandard, truncated or partially induced marking, the inequality \(M\ge q\) must be checked independently; Theorem 3.1 itself requires only \(M\ge24\mathbf b\).

**Important remaining distinction:** A full-circle-base crest may be the union of **two separated positive closed intervals**, rather than one connected closed multi-interval. Its positive full-atom content is established by Theorem 3.1, but the original source's \(F_*\) action is defined on connected multi-intervals and their closures. The **componentwise closed crest action and selection** still need to be justified for a full-base Wave. Theorem 2.1 supplies both **positive mass and connected regularity** automatically for all proper-base critical crests.

## 4. Consequence for the existing critical-visit growth repair

KKL §6 defines a critical visit \(B\) of \(A\) by requiring a **short** Wave over the actual image \(F_*^m C_A\), and that this image meet \(\mathbf L_0\). An empty crest cannot meet the critical limb under an image operation that sends empty set to empty set.

Therefore:

- **Proper-base critical visits:** Their starting Wave has a nonempty crest. By Theorem 2.1, the crest is **automatically regular positive**. The exact open-core transport theorem from the companion [dual-WAD/crest note](./kkl_dual_arc_wave_core_reduction_20261106.md), Theorem 4.2, applies to **every pair of such proper-base crests** without assuming atomic ends and without any false equation \(F_*\overline J=\overline{F_*J}\).
- **Short full-base Waves with \(M\ge24\mathbf b\):** Their nonempty crests have **positive** full-atom content by Theorem 3.1, but can have **two components**; an extra componentwise closed-transport step is still required.
- **Small-marking or non-short full-base exception:** If \(M<24\mathbf b\), or the Wave is not short, a nonempty zero-atom crest cannot yet be eliminated by this argument. The finite endpoint-gate framework remains relevant only in that exceptional category, not as an assumed generic obstruction.

**This is a substantive native geometric advance:** for the **large-\(q\) short-Wave regime** central to KKL's near-parabolic strategy, the former “zero-core Wave” obstruction is eliminated as a *nonemptiness/positive-atom* issue. The central remaining obstacle is a **native positive dual-arc witness for a hypothetical proper critical-return interval**, plus full-base multi-component crest transport and endpoint-only critical encounters.

The argument is on the **actual Carathéodory ideal boundary**, and its noncrossing input works in the universal cover of the real annulus even when the *planar* Julia continuum is non-LC. No model landing quotient or finite transition simulation is assumed.

## 5. Suggested referee adversarial checks

1. **Proper versus full base:** Lemma 1.1's unique boundary subarc and alternating-end intersection genuinely require \(B\subsetneq C\). An essential annular winding leaf subordinate only to the *whole* circle cannot be substituted into that lemma.
2. **Source minimal ends:** Check the Appendix A.1 end definition provides the minimal **connected** pair as used above. If there are multiple incomparable choices of end orientation for a disconnected lamination, work with each verified source-assigned minimal pair; do not silently choose the most favorable one.
3. **Two-atom filter:** The “short path” excluded here is a path subordinate to an interval of **length at most two**, not merely one with endpoints in adjacent atoms *regardless of homotopy class*. Subordination to a *proper B* fixes the homotopy class, which is why the shortcut argument is valid.
4. **End-packet overlap:** If E_- and E_+ overlap, they cover the whole proper base and the crest is **empty**; that does not produce a counterexample to positive **nonempty** crests.
5. **Full-base crest disconnectedness:** Positivity of an atom is not automatically connectedness or regularity for a full-circle base, and \(F_*\) on a disconnected set must not be assumed defined without separate extension.
6. **“Universal” constants:** The bound \(24\mathbf b\) follows from the source's short-end bound; it is a **combinatorial threshold**, not a new analytic Wave width-amplification estimate.

**Status:** Theorems 2.1 and 3.1 are new topological/combinatorial deductions from the *actual* KKL Wave definitions and annular ideal-boundary geometry. They do **not** prove KKL Lemma 6.4, full Wave amplification or MLC. **Issue #40 and all named ledger gates remain OPEN.** No independent specialist review or priority claim.


## Postscript — base ambiguity correction and scope of Theorem 2.1

The companion [genuine native Wave-base nonuniqueness certificate](./kkl_native_wave_base_nonuniqueness_20261106.md) constructs two **disjoint positive-width**, individually admissible three-atom leaf packets in an actual KKL annular carrier collar. Their union has **two different incomparable inclusion-minimal connected marked bases**, and for an even number of original atoms the bases can have equal minimum length. Therefore the unqualified phrase **"the smallest base" in Appendix A.1 need not determine a unique base for arbitrary disconnected laminations**, unless a separate connected/indecomposable-support convention is intended.

Accordingly **Theorem 2.1 must be read as a theorem about a Wave with a fixed specified proper minimal base and specified minimal end pair contained in it**, rather than a proof of global uniqueness of such a base. Its no-point-crest argument applies **to each such tag separately** and is unaffected by this correction. The full-circle theorem analogously applies **to a selected full-base tag** and does not imply that a full base is forced/canonical for all underlying laminations. Any application to the actual source's “critical visit” definition must either specify consistent Wave tags through transport, prove a canonical base in the intended subclass, or establish that the desired conclusion is independent of base choice.

This is **a mathematical source-domain type issue**, not proof that the analytic Wave amplification theorem is false. It strengthens the need to make the actual closed Wave crest a precisely typed input before applying \(F_*\) to it.
