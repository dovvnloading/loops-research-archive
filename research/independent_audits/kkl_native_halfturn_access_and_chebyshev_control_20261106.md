# Issue #40: Native half-turn access threshold and quadratic witness

**Date:** 2026-11-06. **Status:** proved native annular-cover theorem and real quadratic control, not full KKL category closure. No synthetic transition matrix.

Primary source: Kahn–Kapiamba–Lyubich, arXiv:2606.27272v1, §2.1, §2.5, Proposition 6.5, proof of Proposition 6.8, and Appendix A.3.1–A.3.4.

## 1. Scope and native maps

For a genuine KKL stage \(F=(f,\iota)\), set \(\mathcal T'=f^{-1}(\mathcal T)\), \(V=\mathcal U\setminus\mathcal T\), \(V'=\mathcal U'\setminus\mathcal T'\). Assume the actual carrier complements are connected annuli with actual inner Carathéodory circles \(C,C'\). The holomorphic degree-two covering \(f:V'\to V\) induces a covering \(p:C'\to C\) in annular conformal coordinates conjugate to

\[
p(t)=2t\pmod 1.
\tag{1.1}
\]

This is the actual holomorphic covering, **not** a chosen finite interval substitution. The immersion is a different map. For an admissible marked open multi-interval \(I\), its native proper-path restriction is \(R(I)=\iota^*I\), and the closed input \(R(\overline I)\) must be computed separately. KKL Proposition 6.5 says both are intervals obtained by including every eligible complete attached-component Carathéodory boundary. By definition \(F_*I=p(R(I))\).

The annularity hypothesis requires separate verification for every actual non-locally-connected carrier lift; the combinatorial model alone is not a proof of it. For general surfaces KKL Appendix A.3.1 only states extension of the covering to an open dense portion of the ideal boundary. The complete circle chart (1.1) here depends on the connected annular covering.

## 2. Theorem: exact half-turn saturation criterion

**Theorem 2.1.** Let \(J\subset C'\) be a nonempty proper connected arc whose real angular lift has endpoints \(a<b\) and span \(L=b-a<1\). Endpoints may independently be present or absent.

- If \(L<1/2\), the image is proper and the covering is injective on \(J\).
- If \(L>1/2\), the image is the entire target circle \(C\).
- If \(L=1/2\), the image is proper **if and only if** both endpoints are absent. Precisely,
  \[
  p((a,a+1/2))=C\setminus\{p(a)\},\qquad
  p([a,a+1/2])=C.
  \tag{2.1}
  \]
  Including either endpoint at exact half-turn span saturates the image.

**Proof.** The lift of \(p\) is \(P(t)=2t\). Its image has angular span \(2L\). A real interval projects modulo one to a proper circle interval when its span is below one, to the full circle when its span is above one, and at span exactly one it omits the common endpoint residue only if both endpoints are omitted. If two distinct source points have the same image, their lifts differ by \(1/2\). Consequently they cannot coexist in a connected nonsaturated interval. \(\square\)

The punctured source circle (a lift of span one with both endpoints omitted) has saturated covering image. Theorem 2.1 is about connected source access intervals; it does not assert anything about the pointwise extension of \(\iota\).

**Corollary 2.2 (native open/closed distinction).** Suppose a marked open input \(I\) has actual pullback \(R(I)=(a,a+1/2)\) and its separate closed pullback satisfies \(R(\overline I)=[a,a+1/2]\). Then

\[
F_*I=C\setminus\{p(a)\},\qquad F_*\overline I=C,
\tag{2.2}
\]

although \(R(\overline I)\setminus\overline{R(I)}=\varnothing\). In particular, **endpoint-completed saturation is not the same as an immersion-born access outside the closure of the open pullback**.

This conditional diagnostic must not be mistaken for a claim that some actual KKL critical visit realizes this half-turn position. Theorem 2.1 is an exact necessary constraint for any stage-level access census. Nor does this example witness the source's independent warning that \(F_*\overline I\) can differ from \(\overline{F_*I}\): in (2.2) these two closed sets are both \(C\).

### Corollary 2.3 (positive angular access mass cannot disappear in a proper image)

Let \(\sigma_{C'}\) and \(\sigma_C\) denote normalized angular Lebesgue measure in the **actual** conformal annulus charts of §1. The measures are intrinsic to the distinguished inner boundary circles up to rotation of those charts.

For a connected native source interval \(J=R(I)\) with **nonsaturated** covering image, and any Borel set \(S\subset J\),

\[
\boxed{\sigma_C(p(S))=2\,\sigma_{C'}(S).}
\tag{2.4}
\]

In particular, if an eligible actual attached-component boundary \(B_X\) is a **nondegenerate interval** contained in \(R(I)\), its full image is still a nondegenerate interval with positive angular access mass. Disjoint source access blocks inside the *same* proper-output pullback have disjoint images, so their positive angular masses add without overlap. **Nothing of positive angular access length can be erased by the covering in the nonsaturated case.**

**Proof.** By Theorem 2.1 the covering is injective on the connected \(J\) and is represented by \(t\mapsto 2t\pmod1\) within one sheet. On that sheet the normalized circular arclength Jacobian is exactly two. The Borel change-of-variables formula gives (2.4). \(\square\)

**This is not Hubbard edge weight expansion.** The conformal angular access mass of a Carathéodory side is not automatically the Perron weight of the combinatorial Hubbard edge, and it does not measure KKL's original vertex-side marking length \(\ell_{\mathcal I}\). Points and closed-only endpoints have angular measure zero, even though they can alter **set-level saturation** at the exact half-turn threshold (Corollary 2.2). Thus positive access mass preservation does not itself solve the missing endpoint/gate census or the Wave interface.

## 3. A real quadratic-dynamics counterexample to unique access from one planar point

Consider the genuine quadratic polynomial

\[
P(z)=z^2-2,\qquad K_P=[-2,2].
\tag{3.1}
\]

The Joukowski uniformization of its actual complementary domain is

\[
\Psi(w)=w+w^{-1},\quad |w|>1,
\quad P(\Psi(w))=\Psi(w^2).
\tag{3.2}
\]

The continuous landing map on the exterior prime-end circle is

\[
L(t)=\Psi(e^{2\pi it})=2\cos(2\pi t).
\tag{3.3}
\]

Consequently

\[
L(1/4)=L(3/4)=0,
\qquad
p(1/4)=p(3/4)=1/2,
\qquad
L(1/2)=-2=P(0).
\tag{3.4}
\]

The upper and lower slit accesses of the **same planar critical point** \(0\) are distinct prime ends. Their images are the same target prime end. The actual prime-end arc \(J_o=(1/4,3/4)\) and closed arc \(J_c=[1/4,3/4]\) give

\[
p(J_o)=C\setminus\{1/2\},\qquad p(J_c)=C.
\tag{3.5}
\]

**Proof.** Formula (3.2) is an identity since \((w+w^{-1})^2-2=w^2+w^{-2}\), and \(\Psi\) maps the exterior disk conformally to the complement of the real segment. Equations (3.3)–(3.5) follow directly. All accesses here are genuine prime ends of a real polynomial, not synthetic circle labels. \(\square\)

**Exact limitation.** This is a **genuine analytic counterexample to the inference** that one planar landing point determines one prime-end access, even with a locally connected Julia set. It is **not** a counterexample in the required parabolically bounded, prime primitive KKL renormalization category. For the whole invariant segment there is no added preimage-tree branch, so the example does **not** refute Proposition 6.5 or 6.8 and does not settle Issue #40 by its native-counterexample alternative.

## 4. Consequences for the distinguished KKL attachment point

KKL's proof of Proposition 6.8 states that every component of \(\mathcal T'\setminus\mathcal T\) meets the old tree at a common **planar point** \(x\). It also constructs a real critical gate whose source interval is contained in \(\operatorname{Int}\iota^*x\), and distinguishes whether \(x\) is in an old marking atom or is its endpoint. The one-point assertion does **not** identify all the distinct prime-end occurrences of \(x\), as the real polynomial witness demonstrates.

The next native census therefore requires, for every actual \(X\subset\mathcal T'\setminus\mathcal T\):

1. A specific crosscut-access atlas for every source **prime end** with impression containing \(x\), without assuming these are unique or mutually identified.
2. The complete \(B_X=\partial_C X\subset C'\), its individual gate accesses, original cyclic order, and **separate** membership in \(R(I)\) and \(R(\overline I)\), via the actual proper-path universal definition.
3. The source and target annular charts of the **same** \(f,\iota\), giving a check of the sharp half-turn condition of Theorem 2.1 for each actual pullback interval; proper images cannot fold two distinct accesses.
4. The two genuine preimage edge strips over each target Hubbard edge from KKL §2.5, assigned to their actual old or attached source pieces. Edge strips and prime-end side atoms are different types until the global access correspondence is proved, especially when the actual carrier is non-locally-connected.
5. An independent **closed** Wave crest transport statement on original vertex-side marking atoms. The local covering calculation is not a proof of positive original marked-interval growth, zero-edge escape, or the crests' required inclusions.

A proposed stage certificate claiming a connected **nonsaturated** \(R(I)\) includes two source accesses with equal \(p\)-image contradicts Theorem 2.1. A proposed certificate equating the planar point \(x\) with one prime end contradicts the implication failure shown by (3.4), unless independent geometric access information is provided. The former is a source-annular necessary theorem, while the latter is an adversarial polynomial control **outside** the full KKL category.

**Ledger:** Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, and global MLC remain OPEN. No synthetic transition simulation, full non-LC access proof, or independent specialist verification is claimed.
