# Issue #40 — ROOT-EXPOSURE ABSORPTION: native closed critical-gate terminality without Perron growth

**Date:** 2026-11-06. **Status:** a new **source-defined finite-time terminality theorem** for actual KKL \(\Phi=F_*=f_*\iota^*\), obtained by coupling the *genuine* critical-root access expansion of Proposition 6.8 to the exact limb translations and critical saturation of Proposition 6.6. **No Perron eigenvalue, global monotonicity of combinatorial marked length, synthetic interval substitution or LC assumption is used.** Its exceptional source-selected \(x\)-access domain is explicit. An \(r=2\) distinguished-root placement yields a much stronger short-Wave no-continuation theorem, conditional only on the earlier native Wave crest/type hypotheses.

Primary source: Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §6.1, Proposition 6.6 and text immediately after (exact \(\Phi\mathbf L_j=\mathbf L_{j+1}\) for \(j\ne0\), \(\Phi\mathbf L_0=C\)), proof of Proposition 6.8 (all added components meet one planar \(x\); its **designated ideal-boundary occurrence** has \(\mathbf J'\subset\operatorname{Int}\iota^*\{x\}\), \(f_*\mathbf J'=\mathbf L_{(\mathbf b,q-\mathbf b)}\)). The actual old and added boundary pieces are those of Proposition 6.5, and **open and closed** inputs remain distinct as in Appendix A.3.4.

## 1. The only dynamical inputs, correctly typed

Fix a genuine parabolically \(\mathbf b\)-bounded prime-primitive KKL stage of rotation \(1/q\), with \(q\ge2\mathbf b+3\) and original vertex-side marking. Write \(C=\partial_C\mathcal T\) for the **actual** inner Carathéodory circle and \(\Phi=f_*\iota^*\). Its actual open limb multi-intervals \(\mathbf L_j\) are indexed by \(\mathbb Z/q\mathbb Z\).

Source §6.1 provides

\[
\Phi(\mathbf L_j)=\mathbf L_{j+1}\quad(j\ne0),
\qquad
\Phi(\mathbf L_0)=C,\qquad \Phi(C)=C.
\tag{1.1}
\]

As usual, \(\Phi\) is inclusion-monotone on its source-defined admissible connected inputs: \(X\subset Y\Rightarrow\Phi X\subset\Phi Y\). For the arguments below, all required connected open/closed iterates are assumed **well typed** under KKL A.3.4; this is a separate endpoint/action requirement, not a pointwise quotient axiom.

Let \(a_x\) be the **distinguished ideal access occurrence selected by the source** in its proof of Proposition 6.8. Here \(x\) is initially a *planar tree point*; the individual prime ends at it are NOT automatically identified. Source proof supplies a specific source restriction interval \(J_x'\) and a long corridor

\[
J_x'\subset\operatorname{Int}\iota^*\{a_x\},
\qquad
f_*J_x'=\mathbf Q:=\mathbf L_{(\mathbf b,q-\mathbf b)}.
\tag{1.2}
\]

By definition \(\mathbf Q\) contains the \(q-2\mathbf b-1\) consecutive **complete limbs**

\[
\mathbf L_{\mathbf b+1},\mathbf L_{\mathbf b+2},
\dots,\mathbf L_{q-\mathbf b-1}.
\tag{1.3}
\]

Each limb has at least one actual original marking atom, and distinct limb atoms are disjoint; hence

\[
\ell(\mathbf Q)\ge q-2\mathbf b-1.
\tag{1.4}
\]

We write a **root-exposed input** for a connected original marked open or closed multi-interval \(D\) for which the **actual** source-defined pullback satisfies

\[
\boxed{\mathbf Q\subset\Phi(D).}
\tag{1.5}
\]

Every input containing the *source-designated access* \(a_x\) in the precise Appendix A.3.2 subordination sense is root exposed by (1.2) and monotonicity. **A different prime end with the same planar impression as \(x\) is not thereby root exposed**; that is a separate geometric claim.

## 2. Native long-corridor propagation needs no marked-length monotonicity

### Lemma 2.1 (exact limb packet propagation)

For \(0\le t\le\mathbf b+1\),

\[
\boxed{
\Phi^{t}\mathbf Q\supset
\bigcup_{j=\mathbf b+1}^{q-\mathbf b-1}\mathbf L_{j+t\bmod q}.
}
\tag{2.1}
\]

All these \(q-2\mathbf b-1\) limb blocks remain **distinct**, so for \(0\le t\le\mathbf b+1\),

\[
\ell(\Phi^t\mathbf Q)\ge q-2\mathbf b-1
\quad\text{unless the image is already the full circle.}
\tag{2.2}
\]

Moreover,

\[
\boxed{
\Phi^{\mathbf b+2}\mathbf Q=C.
}
\tag{2.3}
\]

**Proof.** For \(t=0\) the inclusion follows from (1.3). Assume it holds for \(t<\mathbf b+1\). For each initial \(j\in[\mathbf b+1,q-\mathbf b-1]\), the current index \(j+t\) is not \(0\bmod q\): the *largest* index is \(q-\mathbf b-1+t\le q-1\), and the *smallest* is positive. Thus the genuine source rule \(\Phi\mathbf L_{j+t}=\mathbf L_{j+t+1}\) from (1.1), combined with inclusion monotonicity, yields the packet inclusion for \(t+1\). At \(t=\mathbf b+1\), the initial final limb \(j=q-\mathbf b-1\) reaches index \(q\equiv0\), so the image includes **the complete critical limb** \(\mathbf L_0\). Applying \(\Phi\) once more, the exact source saturation rule \(\Phi\mathbf L_0=C\) forces \(\Phi^{\mathbf b+2}\mathbf Q=C\), proving (2.3). Distinctness of shifted indices mod \(q\) gives the cardinal-length bound independently of any PF expansion or monotonicity of \(\ell\). \(\square\)

This is a **special geometric invariant packet**, not an assertion that the marked length of *every* proper interval is nondecreasing. It uses an **existing source-defined corridor** and its true limb-by-limb dynamics.

## 3. Theorem — root-exposed closed crests cannot have any short successor

### Theorem 3.1 (root-exposure finite-time absorption)

Let \(D\) be any source-admissible root-exposed **connected** marked open or closed multi-interval of the actual KKL stage. Then for **every** positive iterate \(m\ge1\) for which the source action is well defined,

\[
\boxed{
m\le\mathbf b+2
\quad\Longrightarrow\quad
\ell(\Phi^{m}D)\ge q-2\mathbf b-1
\ \text{or }\Phi^{m}D=C,
}
\tag{3.1}
\]
and
\[
\boxed{\Phi^{\mathbf b+3}D=C.}
\tag{3.2}
\]

More generally any iterate \(m\ge\mathbf b+3\) equals \(C\), since the whole circle is absorbing. Both statements are **independent of \(\lambda_F>1\)** and of any general nondecreasing length hypothesis.

**Proof.** By root exposure \(\Phi D\supset\mathbf Q\). For \(1\le m\le\mathbf b+2\), inclusion monotonicity gives \(\Phi^mD\supset\Phi^{m-1}\mathbf Q\); apply Lemma 2.1 with \(t=m-1\). For \(m=\mathbf b+3\), the same monotonicity and (2.3) give \(\Phi^{\mathbf b+3}D\supset\Phi^{\mathbf b+2}\mathbf Q=C\), hence equality. Subsequent images remain \(C\). \(\square\)

### Corollary 3.2 (no short critical Wave successor after a root-exposed crest)

Assume
\[
\boxed{q\ge14\mathbf b+1}
\tag{3.3}
\]
(which follows from the large-rotation regime \(q\ge24\mathbf b\)). Let a **genuine closed Wave crest** \(D=C_A\) be one connected marked closed interval, and suppose it is root exposed at the source-selected access \(a_x\).

Then **no** genuine short Wave \(B\) can crest over \(\Phi^mD\) for **any** \(m\ge1\), provided the source's closed iterates are well typed and the successor short-crest length bound is \(\ell(C_B)<12\mathbf b\).

**Proof.** By Theorem 3.1, if \(m\le\mathbf b+2\), the image \(\Phi^mD\) contains at least \(q-2\mathbf b-1\ge12\mathbf b\) complete original marking atoms, possibly already the entire circle. An inclusion \(\Phi^mD\subset C_B\) would force \(\ell(C_B)\ge12\mathbf b\), contradicting shortness. If \(m\ge\mathbf b+3\), the image is \(C\), impossible to fit in a short proper crest. \(\square\)

This is a **uniform-in-\(m\) terminality theorem for one actual source-selected exceptional contact**. It bypasses the Perron matrix, critical-return WAD witness, and global proper-length growth entirely. It also handles **closed-only birth** at a marked endpoint: if \(a_x\) belongs to \(C_A=\overline{J_A}\) but not to the open core \(J_A\), the *closed* pullback still exposes the whole root block and forces terminality.

## 4. The exact \(r=2\) special case and new gate pruning

Let \(r=\ell(\mathbf L_0)\).

### Corollary 4.1 (two-atom critical limb with selected root at its internal cut)

Assume \(r=2\), with its **one internal marked cut equal to the actual source-selected \(a_x\)** in the sense of (1.2). Suppose \(q\ge24\mathbf b\), and a genuine short Wave \(A\) is an **active critical successor**, so by the prior [native Wave interface](./kkl_native_critical_atom_contact_and_full_wave_interface_20261106.md) its nonempty crest \(D=\overline J\) is regular positive, \(J=\operatorname{Int}D\) meets \(\mathbf L_0\) in a whole marking atom, and its base is proper.

Then **\(A\) cannot have any further short critical successor at any positive iterate time**.

**Proof.** If \(J\) contains the whole \(\mathbf L_0\), then \(\Phi J=C\) from KKL §6.1; since \(J\subset D\) and \(\Phi\) is monotone, \(\Phi D=C\), so there is no later short successor. Otherwise \(J\cap\mathbf L_0\ne\varnothing\) but \(\mathbf L_0\not\subset J\). By the actual [native internal critical-cut theorem](./kkl_native_critical_cut_gate_reduction_20261106.md), one endpoint of \(J\) is the **only internal critical cut**, namely \(a_x\). Therefore \(a_x\in D=\overline J\). By source root exposure of that selected access and Corollary 3.2, no future short successor can crest over \(\Phi^mD\). \(\square\)

**Exact scope:** The placement of the source-selected root *at the unique internal critical cut* is a **stage-specific hypothesis**; KKL Proposition 6.8 distinguishes both an atom-interior and an endpoint case and does **not** assert the root has this location for every stage. This proves a sharply restricted **actual KKL native theorem**, not the universal \(r=2\) case if its root lies elsewhere. Under the stated placement, a continuing short critical-visit chain stops after the root-exposed crest—without the unproved positive dual-WAD nonreturn theorem.

### Corollary 4.2 (remove root-exposed states from the critical-cut return search)

At arbitrary \(r\), and \(q\ge14\mathbf b+1\), any proof-used *closed regular* critical crest \(D=\overline J\) with a continuing short critical successor must satisfy

\[
\boxed{\mathbf Q\not\subset\Phi D.}
\tag{4.1}
\]

In particular its original marked access set cannot contain the **source-selected** \(a_x\) whose immersion pullback contains the critical root corridor. Therefore a finite critical-cut graph constructed for **continuing short Wave crests** may discard all states \(J\) whose *closed* crest \(\overline J\) contains \(a_x\), provided the actual source interval is already known to be a canonical regular positive crest. This is a strictly stronger test than examining the **open core J** alone: endpoint-only exposure is fatal even when \(J\) excludes \(a_x\).

**Proof.** Contrapositive of Corollary 3.2 and the source monotonicity of the actual closed pullback. \(\square\)

### Corollary 4.3 (root-pruned gate capacity, independent of \(q\))

Retain the hypotheses that the source-selected \(a_x\) is one of the \(r-1\) **internal marked cuts of \(\mathbf L_0\)**, where \(r\ge2\), and \(q\ge14\mathbf b+1\). For each fixed positive short interval length \(k\), the **native open critical-cut candidate family** from [the return-graph reduction](./kkl_native_finite_critical_cut_first_return_graph_20261106.md) has at most \(2(r-1)\) states. But any state \(J\) with \(a_x\in\overline J\) has a **closed** root-exposed crest and is therefore **terminal** for continuing short critical Waves by Corollary 3.2.

A continuing short critical-Wave core \(J\) must, therefore, have its critical-intersecting **boundary cut at one of the remaining \(r-2\) internal cuts**. For each fixed \(k\), at most two genuine intervals begin/end at each such cut, giving

\[
\boxed{
|\mathcal G_{k,\mathrm{short\ continuable}}|
\le 2(r-2)\le12\mathbf b-4.
}
\tag{4.2}
\]

In particular **when \(r=2\), the continuable closed-crest gate set is empty**, in agreement with Corollary 4.1. Summing over the \(12\mathbf b-1\) allowable positive short lengths gives a **root-pruned total candidate capacity**

\[
\boxed{
|\mathcal G_{\mathrm{short\ continuable}}|
\le 2(r-2)(12\mathbf b-1).
}
\tag{4.3}
\]

**Proof.** Any proper continuing interval meeting the critical limb but not containing it has at least one boundary cut among its \(r-1\) internal cuts, by the actual cut-gate theorem. If that cut is the distinguished \(a_x\), then \(a_x\in\overline J\), contradicting Corollary 3.2 for a continuing **closed** short Wave crest. Thus at least one boundary cut lies among the remaining \(r-2\) cuts. At fixed \(k\), specifying which of those cuts is the start or end determines at most one marked interval. Count them; other root-exposed states are *also* excluded and can only reduce the family further. \(\square\)

**Why this is stronger than a graph subtraction:** The source-selected \(a_x\) is a **closed-input** obstruction, so a candidate gate with *open* interval endpoint \(a_x\) is rejected even though \(a_x\notin J\). The true complete \(\iota^*\) attached-root block in \(\overline J\), not a synthetic transition word, enforces this exclusion. The finite gate count uses real marked cuts and is uniform in the rotation denominator \(q\).

### Corollary 4.4 (improved conditional bound for root-avoiding critical visits)

Assume \(r\ge3\), \(a_x\) is an internal critical cut, \(q\ge24\mathbf b\), and the source's actual short critical Wave crests have the regular positive/core and full-atom intersection properties proved in the companion high-rotation Wave notes. Suppose furthermore that **proper marked length is nondecreasing** and there are **no periodic proper critical-return orbits among the root-avoiding cut-side states** (the remaining native nonreturn/dual-WAD gate). Then a continuing short critical-visit chain satisfies the sharper strict bound

\[
\boxed{
N < \bigl(2(r-2)+1\bigr)(12\mathbf b-1)
=(2r-3)(12\mathbf b-1).
}
\tag{4.4}
\]

**Proof.** The corrected plateau argument is identical to the [native critical-cut theorem](./kkl_native_critical_cut_gate_reduction_20261106.md), except that a constant-length block of continuing critical visits can only use the at most \(2(r-2)\) genuine **root-avoiding** states counted in Corollary 4.3. Therefore \(2(r-2)+1\) visit states in one constant-length orbit force a periodic root-avoiding critical return by strict pigeonhole; this is excluded by the stated nonreturn assumption. The core length is between \(1\) and \(12\mathbf b-1\), giving the bound. \(\square\)

This conditional estimate improves the already sharpened \((2r-1)(12\mathbf b-1)\) bound while preserving the exact root-guard and other analytic hypotheses. It is **not** an unconditional repair for \(r\ge3\).

## 5. What this does NOT assert

- The theorem is *not* a new global pointwise continuous map for the immersion \(\iota\); only the source-selected \(a_x\) of KKL's proof of Proposition 6.8 is charged.
- A **different** prime end whose impression contains the same planar root \(x\) is **not** automatically root exposed. This is exactly the non-LC selection issue isolated in Issue #40.
- The root-exposure short-Wave terminality does **not** prove that the full original marked interval action has nondecreasing length or no periodic proper states at cuts **different** from \(a_x\).
- The theorem uses actual source-defined closed iterate operations. It does not claim that \(F_*^m\overline J=\overline{F_*^mJ}\), which Appendix A.3.4 explicitly warns may fail.
- For small \(q\), the initial corridor may contain fewer than \(12\mathbf b\) atoms and the immediate long-image shortness contradiction needs its explicit numerical condition.

**Next exact native gate problem:** for each \(\mathsf{Cut}_{\rm crit}\) identify whether its *closed* crest includes the selected root \(a_x\). Those that do are now **unconditionally terminal** (given typed closed iterates), with no dual witness. Only the remaining *root-avoiding* critical-cut-side states can belong to a continuing short critical chain. Compute their actual \(\iota^*\) cutoff/attachment eligibility; if any survive, use a direct source-cut rank or the bivertical WAD. The new **parabolic-tail insertion** theorem can then compare the reduced, root-avoiding gate family across q.

**Status:** source-derived exceptional-root finite-time absorption, long-q root-guard terminality, and native r=2 special case under precise root placement. No full KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, or MLC proof; Issue #40 OPEN. Independent specialist review remains required.
