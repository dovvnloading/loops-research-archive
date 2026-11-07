# Issue #40 — changing lens: native Hubbard dual arcs, PF non-return, and open-core Wave transport

**Date:** 2026-11-06.  
**Target:** Issue #40 / KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR.  
**Status:** new, rigorous **dual-WAD non-return criterion**, proved positive-core Wave interface, and source-locked repair of a literal exponent typo in the v1 expanding-valuation definition. These results **do not** prove that all proof-used native intervals have positive dual witnesses, nor that zero-core crests escape. No native interval-growth/Wave/MLC gate is promoted.

**Source lock:** Kahn–Kapiamba–Lyubich (KKL), [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §2.5 (finite Hubbard edges, primitive \(T_F\), non-LC combinatorial lift), §§2.6–2.7 (bivertical Hubbard arc diagrams, native dual operator, positive expanding valuation), §6.1 (Propositions 6.5–6.9, proof of Lemma 6.4), Appendix A.1 (wave ends, crest), Appendix A.3.2 and A.3.4 (proper paths, monotone pullback, separately computed closed inputs). This note deliberately uses **existing actual arc operators** rather than selecting an independent finite transition matrix.

## 1. A source-locked finding: the edge/arc bridge already exists

A critical part of the previous draft PR #41's missing-step list was formulated as “derive \(T_F\) from the same actual prime-end side diagram.” The native source itself supplies a **different geometric realization that is already proved**, and it is stronger for spectral purposes:

- KKL §2.6 associates to **each genuine Hubbard edge** \(e\in E(\mathcal T)\) one **bivertical arc class** \(\beta_e\in\mathcal H^{\mathrm{biv}}\) in \(\mathcal U\setminus\mathcal K\). This is a class of actual proper arcs, not an individual prime-end side of \(\partial_C\mathcal T\).
- §2.6 gives actual \(f^*,\iota^*\) pullback collections and \(f_*,\iota_*\) on these dual arc classes.
- §2.7, proof of Theorem 2.4, **explicitly identifies the matrix** of
  \[
  \boxed{\mathfrak T(\beta)
    :=\sum_{\alpha\in\iota^*\beta} f_*\alpha}
  \tag{1.1}
  \]
  with \(T_F\), and the reversed pullback/pushforward operation with \(T_F^\top\), including the identities for their iterates.
- §2.5 states \(T_F\) is primitive, \(\lambda_F>1\) for the prime primitive type, and lifts the corresponding combinatorial data from \(\mathfrak K_{\mathrm{com}}\) when \(\mathfrak K\) is non-LC.

**Consequence:** The correct remaining bridge is **not** “realize every matrix row holomorphically again.” For non-return of marked intervals, it is enough to produce a **native dual-WAD or edge-witness carried by that interval** and prove that its recurrence induces the appropriate native **domination** or transition inequality. This still requires geometry, but may avoid enumeration of every prime-end impression and every exceptional component gate.

**Nonconflation:** \(\mathcal H^{\mathrm{biv}}\) lives in \(\mathcal U\setminus\mathcal K\); KKL's Wave marking \(\mathcal I\) lives on \(\partial_C(\mathcal U\setminus\mathcal T)\) and is induced by the **vertex sides** of \(\widehat{\mathcal K}\). A bivertical arc is not a marking atom. The source's existing matrix identity does **not** automatically assign positive dual edge mass to every open marked interval.

## 2. A literal source inconsistency, with the proof-licensed correction

In v1 §2.7, in the definition immediately before Theorem 2.4, property (3) of a “\(\lambda\)-expanding valuation” is printed as

\[
\operatorname{val}((f^*)^nX)
\le\lambda^{-1}\operatorname{val}(X)
\quad \text{for every }n\ge0.
\tag{2.1, printed}
\]

Taken **literally at \(n=0\)**, this implies \(\operatorname{val}(X)\le\lambda^{-1}\operatorname{val}(X)\), so \(\operatorname{val}(X)=0\) for every \(X\) if \(\lambda>1\). That contradicts property (1), which requires \(\operatorname{val}(X)>0\) for a nonzero horizontal WAD. It is an unambiguous **exponent/domain typo in the printed definition**, not a native quadratic counterexample or a refutation of the intended spectral theorem.

Two fixes are consistent with the intended results: change \(n\ge0\) to \(n\ge1\) while retaining a uniform \(\lambda^{-1}\), **or**, better, use the stronger equation actually **derived in the proof** of Theorem 2.4:

\[
\boxed{
\operatorname{val}((f^n)^*X)
\le\lambda_F^{-n}\operatorname{val}(X)
\qquad(n\ge0).
}
\tag{2.2, proof}
\]

The proof's calculations (2.12), (2.14) and final paragraph make the \(n\)-dependent exponent explicit. The remainder of this note uses **(2.2)**, not literal (2.1). This is a source-audit repair, not an assertion about the correctness of all downstream Wave estimates.

## 3. Theorem A — native dual-WAD recurrence obstruction

Let \(F\) be any **actual** KKL prime primitive, periodically repelling stage covered by the hypotheses of §2.7, including its non-LC combinatorial lift as employed there. Let \(\mathcal W_n\) denote the native cone of WADs on \(\mathcal U^n\setminus\mathcal K^n\), and let \(\operatorname{val}\) be the **source-defined** valuation in the proof of Theorem 2.4, normalized so (2.2) holds. Write \(\multimap\) for KKL Appendix A.3.3's actual **domination** relation.

### Theorem 3.1 (no positive horizontal WAD dominates itself through an inverse return)

For any \(p\ge1\) and any **nonzero horizontal** WAD \(X\in\mathcal W_0\) with \(\operatorname{val}(X)>0\), one cannot have

\[
\boxed{ (f^p)^*X\multimap X. }
\tag{3.1}
\]

More generally, if \(Z\subset(f^p)^*X\) is a WAD with \(\operatorname{val}(Z)\le\operatorname{val}((f^p)^*X)\), then **\(Z\multimap X\) is impossible**.

**Proof.** By KKL's domination monotonicity (property (2) of §2.7), the hypothesized \((f^p)^*X\multimap X\) would give
\[
\operatorname{val}((f^p)^*X)\ge\operatorname{val}(X)>0.
\]
But the actual proof estimate (2.2) gives
\[
\operatorname{val}((f^p)^*X)\le\lambda_F^{-p}\operatorname{val}(X)
<\operatorname{val}(X),
\]
a contradiction. If \(Z\multimap X\), then \(\operatorname{val}(Z)\ge\operatorname{val}(X)\), while the assumed subdiagram inequality and (2.2) yield \(\operatorname{val}(Z)<\operatorname{val}(X)\). \(\square\)

**This is already a theorem in the native KKL analytic category:** its hypotheses and inequalities are all from the source's actual WAD theory; **no** pointwise \(\pi\)-lift of non-LC prime ends, global immersion quotient, finite contour simulation, or invented signed edge matrix enters.

**But it is not the old Proposition 6.9.** A proper periodic *boundary interval* \(I\) does not automatically yield a **nonzero horizontal WAD \(X\)** whose n-fold inverse pullback **dominates X in the direction (3.1)**. Establishing **that single direction of domination** (or an equivalent dual-arc witness) is precisely the missing boundary-to-arc lemma. Reversing the domination arrow gives **no** contradiction and is not a valid shortcut.

### Theorem 3.2 (equivalent PF witness criterion for interval nonperiodicity)

Let \(\Phi=F_*\) be the native open marked interval action from KKL §6.1. Suppose a proper periodic interval \(I\) of period \(p\ge1\) has an actual **nonnegative dual edge-witness vector** \(d(I)\in\mathbb R_{\ge0}^{E(\mathcal T)}\), nonzero, with the following precisely specified **native compatibility** on its orbit:

\[
\boxed{
d(\Phi^p I)\ \ge\ T_F^p d(I)
}
\tag{3.2}
\]

coordinatewise, using the same **column-source** convention for both \(d\) and \(T_F\) as in §2.5. Then such a proper periodic \(I\) cannot exist.

**Proof.** Since \(\Phi^p I=I\), (3.2) implies \(d(I)\ge T_F^p d(I)\). Take a strictly positive **left** Perron eigenvector \(\omega^\top T_F=\lambda_F\omega^\top\), with \(\lambda_F>1\). Then
\[
0<\omega^\top d(I)\ge\omega^\top T_F^p d(I)
=\lambda_F^p\omega^\top d(I)>\omega^\top d(I),
\]
impossible. \(\square\)

The **actual source** already provides \(T_F\) through (1.1); the **new** task is a boundary-to-dual **observable** \(d\) satisfying (3.2). It need only be constructed on a hypothetical proper periodic orbit (or on proof-used recurrent intervals), **not on every prime end**. This is a strictly narrower geometric requirement than full exceptional \(X\)-by-\(X\) access classification.

**Zero-witness obstruction:** A periodic interval with \(d(I)=0\), or one for which the domination direction cannot be established, is **not** excluded. Such intervals are exactly the “zero-edge sector” obstruction isolated in the earlier contour repair. Perron growth itself is not a zero-sector escape argument.

## 4. Theorem B — open-core transport fixes the positive closed-Wave interface

**Source facts:** KKL Appendix A.1 defines the crest of a Wave \(A\) to be \(C_A=B_A\setminus(E_{A,-}\cup E_{A,+})\). The crest is generally **closed**, not an admissible open marked multi-interval. In §6, a critical visit \(B\) of \(A\) is a short Wave **over \(F_*^mC_A\)**; that phrase means the **entire image set** is contained in the new crest \(C_B\). Appendix A.3.4 extends the action separately to closures of multi-intervals and warns that closing the open output need not give the closed output.

Define a **regular positive marked crest** to be a proper, closed, connected \(C\subset\partial_C\mathcal T\) for which

\[
J(C)=\operatorname{Int}_{\partial_C\mathcal T}(C)
\tag{4.1}
\]

is a nonempty *connected open* \(\mathcal I\)-multi-interval and

\[
C=\overline{J(C)},\qquad
\ell(C)=\ell(J(C))>0.
\tag{4.2}
\]

Every ordinary crest that is a closed consecutive string of at least one complete original marking atom with only its two marked endpoint cuts adjoined has this property. We **do not** assert that every Wave, especially a crest consisting of just a marked endpoint, is regular positive.

### Lemma 4.1 (monotonicity of the native proper-path pullback)

For any two connected subsets \(X\subset Y\subset\partial^i V\) for which KKL's immersion pullback is defined, one has

\[
\iota^*X\subset\iota^*Y,\qquad f_*\iota^*X\subset f_*\iota^*Y.
\tag{4.3}
\]

The same holds for iterates of the separately defined closed/open action whenever their iterates are defined.

**Proof.** In Appendix A.3.2 the pullback is the **maximal** source subset satisfying: every uniquely restricted proper path subordinate to that subset has its target path subordinate to \(X\). When \(X\subset Y\), every source subset admissible for \(X\) is admissible for \(Y\), because subordination to \(X\) implies subordination to \(Y\). Maximality thus yields the first inclusion; \(f_*\) is set-theoretic image of the actual covering, hence preserves inclusions. Iteration preserves inclusions as long as each typed action exists. Alternatively, Proposition 6.5's complete-component union formula is visibly monotone on its marked open/closed domain. \(\square\)

### Theorem 4.2 (positive-crest core functoriality, no endpoint equality required)

Let \(A,B\) be **genuine native** Waves whose crests \(C_A,C_B\) are regular positive in the sense of (4.1)–(4.2). Assume \(B\) is a critical visit of \(A\) at some \(m\ge1\), with the *source-defined* closed transport

\[
F_*^m C_A\subset C_B.
\tag{4.4}
\]

Then their **genuine open marked cores** satisfy the exact inclusion

\[
\boxed{
F_*^m J(C_A)\subset J(C_B)
}
\tag{4.5}
\]

and **no loss of combinatorial length** occurs on passing to the cores:

\[
\ell(J(C_A))=\ell(C_A),\qquad
\ell(J(C_B))=\ell(C_B).
\tag{4.6}
\]

**Proof.** Since \(J(C_A)\subset C_A\), Lemma 4.1 gives
\[
F_*^mJ(C_A)\subset F_*^m C_A\subset C_B.
\]
KKL Proposition 6.6 says the left-hand side is a **connected open marked multi-interval** whenever the native action is defined. An open subset of a closed \(C_B\) lies in its topological interior \(J(C_B)\), giving (4.5). Length equalities are (4.2), which holds by the regular positive crest hypothesis. At no point did the proof replace \(F_*^m\overline J\) with \(\overline{F_*^mJ}\). Complete attached-boundary contributions may remain strictly larger on the closed input; the **inclusion direction** suffices. \(\square\)

**Important advance:** For **regular positive crests**, the formerly assumed missing “closed crest equals closure of open image” condition is **unnecessary** for the bounded-visit proof. The original closed critical-visit inclusion (4.4), a **definition-level condition**, plus monotonicity automatically transports the open cores in precisely the needed direction.

**Not yet solved:** A crest of **zero marked length** can consist of one or several endpoints; then \(J(C)=\varnothing\). Such a Wave is a genuine possibility under the source definitions (e.g. an annular Wave between adjacent marking atoms with crest their separating endpoint). The core theorem gives **no** growth mechanism for that case. Nor does it prove a source Wave has positive length merely because it has positive conformal width. The **zero-core case** must be settled by a separate local gate/terminality theorem, not ignored.

### Theorem 4.3 (an actual short positive-width Wave with **zero** marked crest)

Suppose a **genuine KKL annular carrier complement** \(V=\mathcal U\setminus\mathcal T\) has two consecutive **distinct** original marking intervals \(\mathbf I_0,\mathbf I_1\subset C=\partial_C^{\rm in}V\), separated by the marked endpoint \(e\). Assume both are nondegenerate open arcs of the actual inner prime-end circle. Then there exists a **genuine positive-extremal-width** lamination \(A\) of proper paths in \(V\) with

\[
B_A=\mathbf I_0\cup\{e\}\cup\mathbf I_1,\quad
E_{A,-}=\mathbf I_0,\quad E_{A,+}=\mathbf I_1,
\quad\boxed{C_A=\{e\},\ \ell(C_A)=0.}
\tag{4.7}
\]

Every leaf of this Wave is short in the sense of KKL §6: its singleton crest cannot contain a whole limb of the original marking. Thus **positive conformal width + actual shortness does not imply positive marked crest length** even before any non-LC complications.

**Proof.** Uniformize a genuine collar of the actual annulus \(V\) by a round annular collar; the inner prime-end boundary is then an honest circle of accesses, without assuming that any planar impression is a singleton. Pick compact nondegenerate disjoint subarcs \(J_0\Subset\mathbf I_0\), \(J_1\Subset\mathbf I_1\) close to \(e\). There is an embedded topological quadrilateral \(Q\) in the collar with these two opposite boundary sides and the other two sides in \(V\), following the *short* boundary arc through \(e\), not the long way round the annulus. By conformal uniformization of a Jordan quadrilateral, \(Q\) has finite strictly positive extremal modulus and supports a positive-width foliation by pairwise disjoint simple arcs connecting \(J_0\) to \(J_1\). These curves are proper paths in \(V\) with endpoints in the corresponding **prime-end** arcs and are subordinate to the short marked base \(B_A=\mathbf I_0\cup\{e\}\cup\mathbf I_1\).

No connected open marked multi-interval smaller than \(B_A\) can contain **both** distinct endpoint atoms, so \(B_A\) is the minimal base. As all leaves begin in \(\mathbf I_0\) and end in \(\mathbf I_1\), the minimal end multi-intervals are exactly those two atoms. By Appendix A.1's *definition* of crest, \(C_A=B_A\setminus(\mathbf I_0\cup\mathbf I_1)=\{e\}\). Since a single marking endpoint contains no complete limb, the Wave is short. \(\square\)

**Bounded-visits consequence:** The zero-core obstruction in Theorem 4.2 is not merely a technical corner case that one could erase by assuming every Wave of positive width has a positive crest. This genuine native Wave does **not** itself supply a chain of repeated critical visits or refute KKL Lemma 6.4. It proves that a repair must either prove that **proof-used** critical-visit crests belong to the regular-positive subclass, or supply a distinct endpoint/zero-core escape or terminality argument.

### Theorem 4.4 (zero-core critical visits reduce to an **actual endpoint gate graph**)

Assume the original KKL vertex-side ideal marking \(\mathcal I\) is **finite**, as in its finite combinatorial Hubbard-tree presentation. Let \(\mathsf E(\mathcal I)\) be its **actual marked endpoint accesses**, not the planar vertex points. Define a partial **native endpoint map** on \(\mathsf E(\mathcal I)\):

\[
g(e)=e'
\quad\Longleftrightarrow\quad
R_\iota(\{e\})\text{ is one source endpoint and }
f_*(R_\iota(\{e\}))=\{e'\},\quad e'\in\mathsf E(\mathcal I).
\tag{4.8}
\]

A marked endpoint \(e\) is **stretching** if the actual set \(f_*\iota^*\{e\}\) contains a nonempty *open original marked multi-interval*; such an \(e\) has **no** arrow in \(g\). The map is **partial**: we do not assert that a source singleton necessarily maps to a marked endpoint, nor that \(F_*\) is defined on all singletons outside the source's closed-input extension.

**Lemma (zero-core classification).** If \(C\) is a **connected** crest assembled from original full marking atoms and endpoints, has \(\ell(C)=0\), and is nonempty, then \(C=\{e\}\) for some \(e\in\mathsf E(\mathcal I)\).

**Proof.** Such a crest contains no full open marking atom, so is a connected subset of the **finite discrete set** of marked endpoints. A connected finite subset of a circle is a singleton. \(\square\)

**Theorem.** Suppose \(A_0,\dots,A_N\) is a genuine sequence of critical visits with **zero-core** nonempty connected crests \(C_{A_j}=\{e_j\}\), and the extended native actions on these closed inputs and their intermediate outputs are **marking-aligned** (each image is either a union of complete marking atoms and endpoints, or a singleton marked endpoint). Then the concatenated dynamics between successive crests must follow the **actual** partial endpoint graph \(g\):

\[
\boxed{
e_{j+1}=g^{m_j}(e_j)
\quad\text{for the critical-visit iterate }m_j\ge1.
}
\tag{4.9}
\]

If any intermediate access is stretching, the next crest **cannot** remain zero-core. Consequently an arbitrarily long zero-core chain must contain an eventually periodic directed **endpoint cycle** of \(g\). To rule out all such chains, it suffices to exclude directed cycles of **guarded/nonstretching endpoints** whose orbits make the required critical-limb visits.

**Proof.** The crest being zero-core forces it to be a marked endpoint by the preceding lemma. By the critical-visit definition and the Wave-over relation, the nonempty image \(F_*^{m_j}\{e_j\}\) is contained in the singleton \(\{e_{j+1}\}\), hence is that singleton. If any intermediate closed image contained a nonempty open marked multi-interval \(J\), native monotonicity (Lemma 4.1) and combinatorial action (KKL Proposition 6.6) would force every subsequent image to contain the **nonempty open** marked multi-interval \(F_*^r J\). It could not become a singleton. Thus, under the stated marking-alignment hypothesis, **every** intermediate image is a singleton marked endpoint, and each one-step transition is an arrow of \(g\). This yields (4.9). A directed path of length at least \(|\mathsf E(\mathcal I)|\) in a finite partial functional graph either terminates or repeats an endpoint, and repetition produces a directed cycle. \(\square\)

**Source-specific critical-root exclusion.** In the proof of KKL Proposition 6.8, the selected old access \(x\) has a source interval \(\mathbf J'\subset\operatorname{Int}\iota^*x\) whose cover image includes the long corridor \(\mathbf L_{(\mathbf b,q-\mathbf b)}\). When that corridor contains a nonempty open marked atom, the corresponding **selected** endpoint access at \(x\) is **stretching**, so it cannot belong to a zero-core endpoint cycle. This is a **genuine native gate statement** already present in the source, not an assigned edge in a synthetic graph. Other distinct prime-end occurrences at the **same planar x** remain separately typed; do not assume they share the selected stretching property without checking their actual proper-path restrictions.

**Remaining finite problem:** The source does not here supply the full **actual endpoint map \(g\)** at the finitely many exceptional endpoint accesses. Nor does the paper establish from §2.7 alone that every guarded endpoint cycle misses the critical limb. The theorem is a **rigorous conditional reduction to a native finite gate graph**, not an assertion that the graph has been computed or is acyclic. In particular a positive-width zero-core Wave exists by Theorem 4.3; positive conformal width cannot be used to remove these states.

## 5. Root-contact endpoint localization without a global prime-end quotient

Let \(A=\overline{\mathcal T'\setminus\mathcal T}\) be the actual excess carrier and let

\[
R=A\cap\mathcal T
\tag{5.1}
\]

be its *physical contact set*. A target Carathéodory access \(a\) is called **guarded** if its prime-end impression is disjoint from \(A\), equivalently from \(R\), and it has a defining crosscut tail in \(V\) disjoint from \(A\). The compact nested-shadow argument in the previous [non-LC protected-access note](./kkl_nonlc_protected_prime_end_access_20261106.md) proves the latter tail automatically when impressions avoid the compact \(A\). The same real crosscuts give the local old-to-source access identification, regardless of LC.

### Proposition 5.1 (no new closed-only attachment at a guarded endpoint)

Let \(I\) be a source-marked open interval and \(a\in\partial I\) one **guarded** endpoint. Under the actual KKL Proposition 6.5 attachment formula, no **complete new-component boundary \(B_X\)** can enter \(R_\iota(\overline I)\) *solely* by admitting the endpoint \(a\). Moreover the old-side access has a locally unique proper source continuation near \(a\), so it cannot spawn an additional nondegenerate source boundary interval at that endpoint.

**Proof.** A closed-only component \(X\) with the endpoint \(a\) as its **only** newly admitted attachment would have \(\overline X\cap\mathcal T\) represented by \(a\); its planar root would belong to \(\operatorname{Imp}(a)\cap R\), contradicting guardedness. For old-side continuation, take a sufficiently deep defining shadow disjoint from \(A\). Inside that shadow the actual old carrier and full carrier coincide, and the near-carrier immersion is an embedding. The same crosscuts are proper in both complements and give a unique source access chart. Thus there is no interval of new source prime ends over \(a\). \(\square\)

**Scope:** This is a **local endpoint result**, not a claim that all endpoints of the native marking are guarded. If **both** endpoints of \(I\) are guarded and the usual connected open/closed interval conventions hold, the local conclusion together with Proposition 6.5 gives

\[
\iota^*\overline I=\overline{\iota^*I},
\tag{5.2}
\]

provided the actual closed pullback is closed and contains \(\overline{\iota^*I}\). These closure assumptions are explicitly stated instead of being deduced from a global monotone circle quotient. If one endpoint is **unguarded**, (5.2) can fail *dramatically*, as the exact periodic-repelling Misiurewicz and basilica quadratic analytic controls already show.

KKL Proposition 6.8 states that **all added components of \(\mathcal T'\setminus\mathcal T\) meet the old tree at the same planar point \(x\)**. If the excess components form a finite contact family, then \(R=\{x\}\); in general a countable family can have additional accumulation contacts without a separate compactness argument, so **do not equate** all impression/contact pathology with \(\{x\}\) by notation alone. Under the finite-contact hypothesis, the **only potentially unguarded endpoint accesses** are those whose impressions contain the actual critical attachment root \(x\). This sharply narrows the closed-only Wave gate problem without enumerating all non-LC prime ends.

## 6. Revised proof architecture / falsification targets

There are now **two independently typed native bridges**, not one giant access census.

**Bridge A — nonperiodicity in the actual dual-arc category.** KKL §2.6–2.7 *already proves* the \(T_F\) ↔ \(\mathcal H^{\mathrm{biv}}\) identity and the strict pullback value estimate. To eliminate a hypothetical proper periodic **open** marked interval, it suffices to extract **one nonzero source horizontal WAD** with \((f^p)^*X\multimap X\), or a nonzero real edge-witness \(d(I)\) satisfying (3.2) on that periodic orbit. No full global prime-end quotient is needed. The first failure is a proper periodic interval **invisible** to all usable dual witnesses (zero dual mass), or a failure of the required domination **direction**. Neither can be ruled out by \(\lambda_F>1\) alone.

**Bridge B — original closed Wave crests.** When a proof-used crest has a **regular positive marked core**, Theorem 4.2 already gives the exact open-core inclusion with unchanged length, without any forbidden closure commutation. The remaining cases are zero-core crests and those whose closed transport or original-marking regularity is not verified. The source's critical-visit *definition* supplies closed inclusion only after \(F_*^m C\) is well typed; the closed-input end effects must remain in its computation, not be silently replaced by \(\overline{F_*^mJ}\).

**Native root geometry is now a support problem:** identify **which original marked endpoints are guarded** by actual contact-free crosscut chains; for unguarded cuts establish the **complete source proper-path attachment block**, using Proposition 6.5. Only these exceptional cuts need contact-impression surgery, not every interior non-LC access.

### Strict status

**Established in this note:** native WAD non-return (Theorem 3.1); Perron witness contradiction (Theorem 3.2); type-safe positive-crest open-core transport (Theorem 4.2); **a genuine short positive-width native Wave with zero marked crest** (Theorem 4.3); no newly born attached block at a guarded endpoint (Proposition 5.1); precise identification and proof-licensed repair of the **\(n=0\)** exponent typo in KKL §2.7's definition.

**Open:** construct a dual witness/domination for every proper recurrent *native* interval; classify the actual **finite marked endpoint gate graph** and exclude guarded critical-limb cycles under the source's typed closed-input action; verify contact/guard status for actual non-LC exceptional marked endpoints and the full source-specific closed-crest admissibility. Theorems 3.1 and 4.2 do **not** jointly imply KKL Proposition 6.9, Lemma 6.4, the corrected bounded-visit growth repair, full Wave amplification, or MLC.

No synthetic simulation was run or relied upon; no independent specialist referee review is claimed. **Leave Issue #40 and all ledger gates OPEN.**
