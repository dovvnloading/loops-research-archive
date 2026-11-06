# Issue #40 — native two-sheet edge-access census and proper-image noncancellation

**Date:** 2026-11-06  
**Input:** [PR #41, native critical-gate theorem](./kkl_native_critical_gate_prime_end_20261106.md).  
**Status:** **partial native theorem**, with a proved proper-image covering dichotomy, actual two-sheet edge census, and a **hypothesis-explicit** edge-trace implication (not original-marking interval growth). **No global \(\iota\) boundary quotient, no synthetic transition matrix, and no closure of interval growth/Wave/MLC**.

**Primary source version:** Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §2.1 (pseudo-ql maps), §2.5 (complete Hubbard tree and *two preimage edges per edge*), §4 and §6 (original vertex-side Wave marking), §6.1 (Propositions 6.5–6.8), Appendix A.1 (connected open multi-intervals, including a whole component), Appendix A.3.1–A.3.4 (covering pushforward and proper-path immersion restriction).

This note uses **actual** \(F=(f,\iota)\) and \(\mathcal T\), not the finite circles of merged PRs #38–39. The new claims are topology/geometry consequences of source statements plus explicitly stated regular-edge hypotheses; they are **not** an independent proof of the paper's whole §6.1.

## 1. Native types and an essential domain qualification

For a source-admissible primitively renormalizable, periodically repelling KKL stage let

\[
\mathcal T'=f^{-1}(\mathcal T),\quad V=\mathcal U\setminus\mathcal T,\quad
V'=\mathcal U'\setminus\mathcal T',\quad
C=\partial_C^{\rm in}V,\quad C'=\partial_C^{\rm in}V'.
\tag{1.1}
\]

The restriction \(f:V'\to V\) is an **unbranched covering**; \(\iota:V'\to V\) is the *different* holomorphic immersion. We work at stages where \(V,V'\) are connected annuli and the inner ideal boundaries are circles. The initial note's Lemma 2.1 explains this when the **actual** carrier \(\mathcal T\) is compact, connected, full and contains the unique critical value. For a non-locally-connected lifted carrier, verifying the actual annulus/fullness hypothesis is a separate required native check; replacing \(\mathcal T\) by the rational-lamination tree does not prove it.

In this annular case the actual covering induces a degree-two map

\[
p=f_*:C'\longrightarrow C
\tag{1.2}
\]

on **accesses** (not on planar landing points); annular uniformization makes it conjugate to angular doubling. The immersion pullback \(R(J)=\iota^*J\) is the Appendix A.3.2 **maximal proper-path restriction relation**, not the preimage under an assumed global monotone \(q:C'\to C\). For a source-marked open multi-interval \(I\) and separately its closure, Proposition 6.5 provides

\[
R(J)=H(J)\cup\bigcup_{X\in\mathscr A(J)}B_X,\qquad
J\in\{I,\overline I\},
\tag{1.3}
\]

where \(\mathscr A(J)\) indexes the **actual** attached components of \(\mathcal T'\setminus\mathcal T\) meeting the old carrier over \(J\), and \(B_X\) is the **complete** Carathéodory boundary contribution. Proposition 6.5 says the resulting \(R(I)\) is an interval, and Appendix A.3.4 defines \(F_*I=p(R(I))\). None of (1.1)–(1.3) identifies individual endpoint impressions in the non-LC case.

## 2. Theorem A — exact no-folding dichotomy for *actual* proper images

### Lemma 2.1 (general circle covering)

Let \(p:C'\to C\) be any finite-degree covering of **connected circles**. If \(J\subset C'\) is connected and \(p(J)\ne C\), then \(p|_J\) is injective. Moreover, after deleting any \(y\notin p(J)\), \(J\) lies in **one** connected component of \(C'\setminus p^{-1}(y)\), and \(p\) maps that component homeomorphically to \(C\setminus\{y\}\). Thus the restriction preserves local cyclic order after choosing these oriented charts.

**Proof.** Choose \(y\in C\setminus p(J)\). Because \(p\) is a finite circle covering, the complement of the finite fiber \(p^{-1}(y)\) consists of \(\deg p\) open arcs, each mapped *homeomorphically* onto the punctured circle \(C\setminus\{y\}\). Connected \(J\) avoids the fiber, so it lies in exactly one such arc. The claimed injectivity and order follow. \(\square\)

### Theorem 2.2 (native proper-or-saturated access transport)

Let \(F\) be as in §1 and \(I\) an *open connected marked multi-interval*. Put \(J=R(I)\).

\[
\boxed{F_*I\ne C\ \Longrightarrow\
p|_{R(I)}\text{ is injective and preserves access order.}}
\tag{2.1}
\]

Consequently two **distinct accesses inside the same actual \(R(I)\)** cannot collide under \(f_*\) while the image remains proper. If a collision occurs between distinct points of \(R(I)\), necessarily \(F_*I=C\). This includes every accessible old or added edge-side atom that actually belongs to \(R(I)\).

**Proof.** Proposition 6.5 supplies connected \(R(I)\); apply Lemma 2.1 to the actual annular covering \(p\). No pointwise \(\iota\)-boundary extension is needed. \(\square\)

**Critical limitation.** This is **not** a proof that a missing edge-side or endpoint belongs to \(R(I)\) in the first place. Also, different pulled-back intervals \(R(I_1),R(I_2)\) may have overlapping *images* even when each image separately is proper. The theorem concerns the single connected interval used in each proper-output comparison.

### Corollary 2.3 (closed-endpoint transport, with the necessary hypothesis)

Let \(J_o=R(I)\), \(J_c=R(\overline I)\), and assume, as must be checked for the actual closed pullback, that

\[
\overline{J_o}\subset J_c,\qquad J_c\text{ is connected}.
\tag{2.2}
\]

If \(p(J_c)\ne C\), then \(p\) is injective on \(J_c\) and

\[
\boxed{
F_*(\overline I)\setminus\overline{F_*I}
=p\bigl(J_c\setminus\overline{J_o}\bigr).
}
\tag{2.3}
\]

In this proper-closed case, closure-only accesses **remain distinct** after covering pushforward. Their source is localized by PR #41, Theorem 3.1, to old lifted endpoints or to complete boundaries of components in \(\mathscr A(\overline I)\setminus\mathscr A(I)\).

**Proof.** Lemma 2.1 applies to connected \(J_c\) with proper image. By (2.2), \(\overline{J_o}\subset J_c\), so the image of \(J_c\setminus\overline{J_o}\) is the image of \(J_c\) minus \(p(\overline{J_o})\). For a continuous map on compact circles, \(p(\overline{J_o})=\overline{p(J_o)}\). Substitution gives (2.3). \(\square\)

There are thus three distinct endpoint outcomes:

1. **Open saturation:** \(p(J_o)=C\), so also \(p(J_c)=C\).
2. **Proper closed image:** \(p(J_c)\ne C\), and (2.3) records each newly born access injectively.
3. **Closure-triggered saturation:** \(p(J_o)\ne C\) but \(p(J_c)=C\). In this case **do not** apply (2.3); recording only \(\overline{F_*I}\) would lose the closed-crest behavior.

This trichotomy is exact where (2.2) is verified. A claim that (2.2) holds for every non-locally-connected native closed pullback is **not** being smuggled in.

### Notational warning: two meanings of “proper”

Throughout Theorem 2.2, **proper output** means \(F_*I\ne C\), a *set-theoretic nonsaturation condition*. KKL Appendix A.3.4 defines “\(F_*\) is **proper on an interval**” to mean that **the immersion \(\iota\) is proper on \(\iota^*I\)** (and “end-proper” only on its end intervals). This is a different property. In particular, KKL Proposition 6.7's properness on the good corridor does **not** by itself invoke the nonsaturation hypothesis of Theorem 2.2.

### Native one-step Wave endpoint interface (source A.14, plus Corollary 2.3)

KKL Proposition A.14 provides a true source-defined Wave statement: if \(F_*\) acts combinatorially on \(I\), \(A\) is a Wave over \(I\), and \(B\subset F_*A^{\rm ubr}\) is the appropriate unbreakable descendant, then \(B\) is a Wave over \(F_*I\). For a source end \(E\Subset I\), the proposition separately places a target end of \(B\) inside **\(F_*\overline I\)**, *not* automatically inside \(\overline{F_*I}\).

When the closed source pullback satisfies (2.2) and the closed target image is proper, Corollary 2.3 therefore gives an **exact two-location classification** for **at least one** such target end \(E_B\) (as guaranteed by A.14):

\[
E_B\subset
\overline{F_*I}\ \cup\ 
p\bigl(R(\overline I)\setminus\overline{R(I)}\bigr).
\tag{2.4}
\]

The second set consists of the closure-only access births localized by the native attachment formula, which may matter even if the first set has no such access. If the closed target image saturates, this classification cannot be upgraded using covering injectivity and must be treated separately.

This is **not** the missing assertion \(F_*^m(C_A)\subset C_B\) for the genuine **closed** Wave crests: A.14 controls the Wave-over-interval and an end, not every crest point. It does identify exactly why open/closed propagation needs distinct records.

## 3. Theorem B — two-sheet census for actual Hubbard **edges**

Let \(E=E(\mathcal T)\) and \(E'=E(\mathcal T')\) be the genuine abstract edge sets of KKL §2.5. The critical point and critical value are in the distinguished vertex package; the restriction over the interior of any target edge \(b\in E\) is unbranched.

KKL §2.5 explicitly states that

\[
f:E'\longrightarrow E
\quad\text{is two-to-one on edge sets.}
\tag{3.1}
\]

For a target edge \(b\), set

\[
\mathcal E_b=\{\tilde b\in E':f(\tilde b)=b\},
\quad
\mathcal E_b^{\rm old}=\{\tilde b\in\mathcal E_b:\tilde b\subset\iota^{-1}(\mathcal T)\},
\quad
\mathcal E_b^{\rm add}=\mathcal E_b\setminus\mathcal E_b^{\rm old}.
\tag{3.2}
\]

Membership here is in the **actual old subtree** identified inside \(\mathcal T'\) by \(\iota\) near \(\mathfrak K\), not in a conjectural circular quotient.

### Theorem 3.1 (complete *edge-lift* census)

For every genuine target edge \(b\),

\[
\boxed{
|\mathcal E_b^{\rm old}|+|\mathcal E_b^{\rm add}|=2.
}
\tag{3.3}
\]

After subdividing source old edges at the actual preimages of target vertices, let \(M_{ab}\) denote the number of components of the embedded old edge \(a\) that \(f\) carries homeomorphically over the target edge \(b\). With **row = source old edge**, **column = target edge**, we have

\[
\boxed{
M_{ab}=(T_F)_{ab},\qquad
\sum_{a\in E}(T_F)_{ab}=|\mathcal E_b^{\rm old}|\le2.
}
\tag{3.4}
\]

In particular, all target-edge preimage **strips** are exhausted by two actual holomorphic sheets; the unused sheets in \(\mathcal E_b^{\rm add}\) are exactly those lying in the added-tree portion. There is no arbitrary third edge lift or numerical transition model.

**Proof.** Equation (3.3) is KKL's degree-two statement (3.1) with its actual source edge set partitioned by the old subtree. The map \(f\circ\iota^{-1}\) on the old Hubbard tree is the graph map used in §2.5 to define \(T_F\). An occurrence of \(b\) in the graph image of source edge \(a\) corresponds to precisely one lifted preimage edge \(\tilde b\) in the old subtree contained in \(a\) (after subdivision); conversely each old lifted preimage edge lies within exactly one old edge of the unsubdivided Hubbard tree. Thus each old lift contributes exactly once to the sum of the relevant graph row, proving (3.4). \(\square\)

**Clarification for non-LC maps:** §2.5 explicitly transfers the *combinatorial* tree through the rational-lamination model. Equations (3.1)–(3.4) are native **abstract-edge counts**, but, without the additional regular-edge/access realization below, do **not** assert that every abstract lift supplies two distinct prime-end side atoms of the *actual* non-LC carrier.

### Lemma 3.2 (actual regular-edge four-side-germ census)

Assume each relevant open edge of \(\mathcal T'\) is locally isolated as an embedded planar open arc: around each of its interior points, there is a disk meeting \(\mathcal T'\) in one subarc that separates the disk into two sides. This holds for a finite locally connected embedded ribbon tree with compact vertex bodies, and must be **verified** for a non-LC lifted carrier.

Then over any regular interior point \(y\in b\) there are exactly

\[
2\text{ preimage points}\times2\text{ local sides}
=\boxed{4\text{ distinct source side germs}},
\tag{3.5}
\]

and each of the two target side germs has exactly two source preimages. The old and added counts per target *side* are respectively \(|\mathcal E_b^{\rm old}|\) and \(|\mathcal E_b^{\rm add}|\).

**Proof.** Choose a small disk \(D\) at \(y\) meeting \(\mathcal T\) in a single embedded arc, with no critical value and no vertex. Since \(f\) is an unbranched degree-two covering over \(D\), its preimage is the disjoint union of two conformal disks, each mapped biholomorphically to \(D\). The source tree intersects each disk in one lifted arc, with two complementary local sides. A biholomorphism permutes these two sides bijectively. Thus the source supplies exactly four distinct *local Carathéodory side germs* and sends exactly two to each target side. Partitioning the two lifted arcs by old/new membership proves the last assertion. These are access germs, not claims of singleton impressions. \(\square\)

**What (3.3)–(3.5) do *not* provide:** They do not enumerate the components \(X\in\pi_0(\mathcal T'\setminus\mathcal T)\) at exceptional *vertices*, how their many edge lifts concatenate into the **complete** \(B_X\), which cyclic sector holds \(B_X\), whether two different components share a planar landing point but have distinct prime ends, or the endpoint-only records of (2.3). Those are exactly the remaining attachment-census obligations.

## 4. Edge-side incidence is **not** automatically the native Wave marking

**Source-type correction (material).** KKL §4 and §6 (opening paragraph of the Wave case, arXiv HTML lines 571 and 1122) say explicitly that the source marking \(\mathcal I\) is induced by **the sides of the vertex package** \(\widehat{\mathcal K}\). Section 2.5, meanwhile, defines \(T_F\) on the **edges** of the Hubbard tree. The two kinds of sides must not be identified without a proof. In particular, the full open side of an edge may be subdivided by vertex-side marking endpoints or may not be an atom of \(\mathcal I\) at all.

Thus the following edge-side calculation is initially an **auxiliary access-trace theorem**. It must not be advertised as a numerical expansion estimate for the original \(\mathcal I\)-length \(\ell\).

### Definition 4.1 (edge-trace access atlas)

On an actual *regular* locally connected ribbon carrier, let \(\mathcal S\) be the two oriented open Carathéodory side arcs \(s_a^+,s_a^-\) belonging to each genuine old edge \(a\in E(\mathcal T)\). These are **actual side traces**, not asserted to be the native \(\mathcal I\)-atoms. A common refinement of \(\mathcal I\) with the cuts of \(\mathcal S\) can be used where one is actually constructed; do not assume a canonical finite common refinement of a non-LC carrier.

For a proof-used source \(\mathcal I\)-multi-interval \(I\), the **edge-trace realization condition** \(\operatorname{ETR}(I)\) consists of three statements requiring actual \(f,\iota\) witnesses:

1. **Full-side detection.** For each old side trace that the comparison proposes to charge to \(I\), the *entire* \(s_a^\sigma\) is contained in \(I\), with no uncharged source subsegments. The charged sides are disjoint actual access subsets. Their inclusion is certified in the **original** marking, not chosen by relabeling.
2. **Complete immersion restriction.** The old lift of every charged full side survives as a complete side trace in \(R(I)\), with all intervening actual attached-component Carathéodory blocks included in source cyclic order by Proposition 6.5.
3. **Graph-to-access compatibility.** For every source edge \(a\) and each traversed target edge \(b\), the corresponding regular \(f\)-lift sends a complete source subtrace to one complete target \(b\)-side; all occurrences in the original source-defined graph word are included, and the target traces stay distinguished as access subsets. This is a **global side/access assertion**, not merely an equality of graph labels.

Local versions of Item 3 follow from the holomorphic side-germ census of Lemma 3.2. Extending them over every vertex endpoint and exceptional attached block is the unresolved analytic step.

### Proposition 4.2 (conditional positive edge-trace estimate)

Write \(T_Fw=\lambda_Fw\), with positive Perron vector \(w=(w_a)_{a\in E}\) and \(\lambda_F>1\). Fix a native \(\mathcal I\)-multi-interval \(I\) for which \(\operatorname{ETR}(I)\) has been verified. Let \(\mathcal S(I)\) be its **verified list of complete old side traces** and set

\[
m_{\mathcal S}(I)=\sum_{s_a^\sigma\in\mathcal S(I)}w_a.
\tag{4.1}
\]

If \(F_*I\ne C\), then the **target** contains the disjoint full target edge-side traces coming from these charges, of total weight

\[
\boxed{
m_{\mathcal S}^{\rm output}(F_*I)
\ \ge\ \sum_{s_a^\sigma\in\mathcal S(I)}
\sum_b(T_F)_{ab}w_b
=\lambda_Fm_{\mathcal S}(I).
}
\tag{4.2}
\]

If the target saturates \(C\), it belongs to the separate saturated alternative. This proves **edge-trace** expansion, not \(\ell(F_*I)>\ell(I)\) for the original Wave marking.

**Proof.** For each complete charged source side, ETR Items 2–3 give its full old graph-image trace in \(R(I)\) and through \(f_*\); the weight of that trace is \(\sum_b(T_F)_{ab}w_b=\lambda_Fw_a\). Proposition 6.5 includes the attached pieces; none subtract from the old traces. For proper output Theorem 2.2 makes \(p\) injective on the **single connected** \(R(I)\), so independently tagged source occurrences cannot collapse to the same target access. Summing the disjoint complete target side traces gives (4.2). \(\square\)

**Do not infer** (i) that \(\operatorname{ETR}(I)\) holds for all original \(\mathcal I\)-multi-intervals, (ii) that all full edge sides form atoms of \(\mathcal I\), (iii) that the vertex-side length \(\ell_{\mathcal I}\) grows from the edge weight, or (iv) that any vertex-only/zero-edge sector escapes. These are **three separate native bridges**, not implications of the Perron eigenvalue.

### Corollary 4.3 (one distinguished critical access gains a genuine long limb image)

Let \(x\) and \(\mathbf J'\) be the **actual** attachment access and source preimage package in the proof of KKL Proposition 6.8, under its nonempty-corridor hypothesis. The source gives

\[
\mathbf J'\subset\operatorname{Int}\iota^*\{x\},
\qquad
p(\mathbf J')=\mathbf L_{(\mathbf b,q-\mathbf b)}.
\tag{4.3}
\]

Therefore

\[
p\bigl(\iota^*\{x\}\bigr)\supset \mathbf L_{(\mathbf b,q-\mathbf b)}.
\tag{4.4}
\]

If that corridor contains a genuine positive edge-side trace, this **particular** zero-dimensional marked input access \(x\) creates a positive-edge-side image after its source-defined restriction and covering. It is an actual critical-gate escape witness (not a finite model).

**Proof.** Apply \(p\) to the two source inclusions stated in KKL's proof of Proposition 6.8. If a positive edge-side lies in the resulting corridor, it belongs to the image. No assumption about a globally continuous quotient, and no uniqueness of the planar impression at \(x\), is used. \(\square\)

**Domain warning:** Appendix A.3.4 defines \(F_*\) on **multi-intervals**, while \(x\) above can be a marked **endpoint**. Equation (4.4) is therefore intentionally written as the set \(p(\iota^*\{x\})\), **not** as \(F_*x\) in the original multi-interval dynamical system. The proof of KKL Proposition 6.8 extends it to a short actual stretching multi-interval \(I_{\rm str}\); this does not establish escape for *every* zero-weight vertex sector.

## 5. Native local zero-sector nontrapping **before** global access identification

There is a second genuinely holomorphic input which does not require the synthetic automaton. Let \(K_0\) be a connected small filled Julia set of an actual KKL renormalization. Fix an **actual quadratic-like restriction** \(g:W'\to W\) of the renormalization in a neighborhood of \(K_0\), as supplied by KKL Theorem 2.1 for each fixed finite-width stage. Denote its inner prime-end access circle by \(C_{K_0}\).

The Douady–Hubbard straightening theorem for connected polynomial-like maps gives a quasiconformal conjugacy near \(K_0\) with a degree-two polynomial \(P\) with connected filled Julia set. This homeomorphism of complementary collars induces a homeomorphism of their **prime-end circles**. Böttcher's map for \(P\) identifies the circle covering of accesses with angle doubling. Thus the actual *local* return map on accesses,

\[
g_\partial:C_{K_0}\to C_{K_0},
\tag{5.1}
\]

is **topologically conjugate** to \(\theta\mapsto 2\theta\bmod 1\). This does not require any pointwise landing of external rays or local connectivity of \(K_0\). Source references: KKL §2.1 Theorem 2.1, §2.3 renormalization, and Douady–Hubbard *On the dynamics of polynomial-like mappings* (1985), Straightening Theorem.

### Theorem 5.1 (native local degree-two return cannot trap an open access interval)

For every nonempty connected open interval \(J\subset C_{K_0}\) there exists \(n\ge1\) such that

\[
\boxed{g_\partial^n(J)=C_{K_0}.}
\tag{5.2}
\]

More precisely, in a straightened angular chart of length \(L\in(0,1]\), any \(n\) with \(2^nL>1\) suffices. In particular **no nonempty open local prime-end interval can remain forever disjoint from any fixed nonempty gate set \(G\subset C_{K_0}\)**.

**Proof.** Under the prime-end conjugacy, \(g_\partial^n(J)\) is the image of a real open interval of length \(2^nL\) modulo \(\mathbb Z\). Once this length exceeds one, its projection is the entire circle. Every fixed nonempty gate set is then met. The proof is on the actual quadratic-like access circle, not on the combinatorial rational lamination. \(\square\)

**Do not conflate** \(C_{K_0}\), the local prime-end circle of one *small filled Julia set*, with \(C=\partial_C\mathcal T\), the carrier-relative circle used by KKL's Wave marking. They are different complements, and an individual external access of \(K_0\) can be split or concealed by incident carrier edges. Theorem 5.1 **does not yet prove** zero-sector escape under the global \(F_*\).

### Corollary 5.2 (conditional global vertex-gate escape criterion)

Suppose an actual proof-used global zero-edge sector \(S\subset C\) has a **faithful return-access identification** with a nonempty open \(J\subset C_{K_0}\) satisfying:

1. every successive proper zero-edge image of \(S\) under one full small-Julia return is represented by the corresponding \(g_\partial^m(J)\);
2. there is a **nonempty** set \(G\subset C_{K_0}\) of source-defined actual carrier edge-attachment *accesses*, with the property that meeting \(G\) forces the global return image either to acquire a complete edge-side or to saturate \(C\);
3. this implication is verified for distinct **prime ends** and both open and closed endpoints, not deduced from a planar point or graph valence.

Then \(S\) cannot remain a proper zero-edge sector indefinitely.

**Proof.** Theorem 5.1 gives \(n\) for which \(g_\partial^n(J)=C_{K_0}\), hence meets \(G\). Item 1 transfers the meeting to the actual global return, and Item 2 forces positive edge-side acquisition or saturation, contradicting permanent proper zero-edge evolution. \(\square\)

This shows precisely where local degree two enters: it provides **real nontrapping on the small-Julia access circle**, but global zero-weight escape remains conditional on an *analytic gate correspondence* between the **two different prime-end circles**. The necessary faithful identification is part of Issue #40's still-open attachment census, especially in the non-LC case.

## 6. Which parts of Issue #40 have actually advanced?

| Item | Source-defined progress | Still open |
| --- | --- | --- |
| Actual cover and immersion | \(p=f_*\) annular covering separated from proper-path \(R=\iota^*\) | Annular carrier identification for each non-LC lift |
| Attachment completeness | Proposition 6.5 entire \(B_X\) inserted for marked open/closed inputs; PR #41 endpoint origin localization | Full native \(X\)-by-\(X\) census at the exceptional \(x\) and neighboring limbs |
| Edge incidence | Exactly two **actual** preimage edges over each target edge; old/new partition (3.3); source-defined \(T_F\) count (3.4); local four-germ census (3.5) | Global source-side endpoint matching and non-LC (ESR) |
| Proper-output multiplicity | **Proved unconditionally in the annular prime-end setting** by Theorem 2.2 | Saturated output can identify covering sheets; record it as saturation, not a numerical edge-row identity |
| Local zero-sector nontrapping | **Proved on the actual small-Julia quadratic-like access circle** (Theorem 5.1) | Faithful return selector between \(C_{K_0}\) and carrier \(C\) (Corollary 5.2) |\n| Edge-trace weight | **Conditional only** on native ETR and original-marking side detection: (4.2), not a theorem for \(\ell_{\mathcal I}\) | Original vertex-side marking ↔ edge-side trace comparison, all zero-mass sectors |
| Closed Wave crests | Proper-closed endpoint defect transported by (2.3), when (2.2) is checked | Actual crest inclusions, proper/positive/short hypotheses, closure-triggered saturation |

### First remaining native verification target

At the distinguished point/access \(x\) of the proof of KKL Proposition 6.8, construct the **actual** finite or nonfinite list

\[
\bigl\{(X,\partial_C X,\gamma_X^-,\gamma_X^+,j_X,
\text{source old/new edge sheets},\text{closed-only membership})\bigr\},
\tag{5.1}
\]

where the \(\gamma_X^\pm\) are **distinct prime-end gate accesses** determined by genuine proper-path/crosscut charts, \(j_X\) is the cyclic insertion sector, and the edge sheets are the actual \(f^{-1}(E(\mathcal T))\) from (3.2). In the non-LC setting, **do not** infer gates from point impressions or from \(\pi:\mathfrak K\to\mathfrak K_{\rm com}\). Verify that this grouping exhausts \(\mathcal E_b^{\rm add}\) for every edge \(b\), then use its records to discharge (ETR), the original vertex-side-marking comparison, and zero-sector escape. Finally test the **closed** Wave crest as a separate input \(J_c\), using the trichotomy of §2 and the source's warning that \(F_*\overline I\) can differ from \(\overline{F_*I}\).

### Failure controls (analytical, not a new finite simulation)

- **Covering fold claimed while target proper:** impossible for **one connected** pullback interval (Theorem 2.2). If observed, either an interval was disconnected, boundary types were mixed, or the asserted covering/access chart was wrong.
- **A third preimage edge strip:** impossible under the actual degree-two source edge map (3.3). It is either a duplicate label or an incorrect \(\mathcal T\)-/\(\mathcal T'\)-identification.
- **A missing added edge sheet:** detectable by failing (3.3), even before classifying complete attached components.
- **Duplicate target trace in a proper output:** violates Theorem 2.2 when both source traces are genuinely in the *same* \(R(I)\); a separate abstract matrix can conceal this.
- **Endpoint-only large attachment dropped:** violates the source-separated \(R(\overline I)\) audit. If it saturates the target, classify as closure-triggered saturation, **not** a proper image.
- **Original Wave-marked atom assumed to be an edge-side atom:** invalid; the source marking is induced by sides of \(\widehat{\mathcal K}\), and ETR needs an original-marking comparison.\n- **Zero-sector claimed expanding from \(\lambda_F>1\):** invalid without an actual gate-escape proof.

**Ledger decision:** retain \(KKL\_BOUNDED\_VISITS\_INTERVAL\_GROWTH\_REPAIR\), \(KKL\_PARABOLIC\_WAVE\_AMPLIFICATION\), and MLC as **OPEN**. The native gate realization over the whole non-LC category, not a more elaborate synthetic regression, is next. No independent specialist review has been obtained.
