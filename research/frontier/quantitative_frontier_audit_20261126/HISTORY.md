# Exact backward-history rigidity at the physical 3/9 tip

**Target:** VIRTUAL_END_BLOWUP_REALIZATION (open), specifically the unresolved shape quotient in [analytic histories and ordered accesses](../../independent_audits/decoration_analytic_history_end_blowup_20261126/NOTE.md), §§3–6, 8. Also consumes the actual physical inverse branches and isolator in that note §4. **Status:** proposed written theorem on that fixed source-realized decoration; no ledger promotion.

## 1. Statement and source inputs

Let \(c_*\) be the real, actual nonattracting 3/9 tip from the archive, and write \(a=-c_*\), \(f(z)=z^2-a\), \(g=f^2\). In particular
\[
  1.786510<a<1.786511.
\]
Use the actual first ambient direct-decoration separator \(P\), its two closed univalent pullbacks, and the two inverse branches
\[
 \phi_L(x)=-\sqrt{a-\sqrt{x+a}},\qquad
 \phi_R(x)=+\sqrt{a-\sqrt{x+a}}
\]
on the real root interval \([\alpha,-\alpha]\), with the positive real square roots. The branches extend analytically near that interval. These identifications, the parameter isolator, and the existence of all normalized suffix limits on a common complex neighborhood of \(P\) are inherited exactly from the cited note, §§1–4; no new parameter isolation or ray landing is claimed.

For a finite word \(w\), let \(\phi_w=\phi_{w_1}\circ\cdots\circ\phi_{w_m}\) and \(S_w(z)=(\phi_w(z)-\phi_w(0))/\phi'_w(0)\). For a left-infinite history \(\eta=(\ldots,\eta_2,\eta_1)\), let \(H_\eta=\lim_{k\to\infty} S_{\eta_k\cdots\eta_1}\) be the existing normalized analytic limit; the history map is continuous by the uniform suffix estimate in that note. The last letter is the rightmost letter.

**Theorem.** At this physical parameter, the map \(\eta\mapsto H_\eta\) is injective, hence a homeomorphism from the left-infinite binary history space onto the compact space of normalized affine shapes. In particular the affine-shape quotient left undecided in the preceding audit is exactly the full backward history, not a smaller quotient. The ordered-sector graph boundary is therefore homeomorphic to \(\{L,R\}^{\mathbb N}\times\{L,R\}^{-\mathbb N}\times\mathbb Z/2\); this is a topological identification with the existing graph compactification, not a construction of new protected relative-cover data.

The key invariant is not a periodic multiplier approximation. Every limiting chart has a nonremovable square-root singularity at the same positive real critical value \(s=a^2-a=g(0)\), while it is holomorphic across its reflection \(-s\). Thus no two limiting charts can be reflections of one another in their normalized coordinates.

## 2. A common enlarged real analytic domain

Set \(I=[-29/20,5/4]\). The two algebraic branches above extend holomorphically on a complex neighborhood of \(I\) and satisfy \(g\circ\phi_j=\mathrm{id}\). Indeed both successive radicands are positive there, since \(x+a>0\) and \(x<s\). They agree with the physical inverse branches where the original real interval meets \(I\), by local inverse uniqueness. In fact the original real interval is contained in \(I\): \(\alpha=(1-\sqrt{1+4a})/2\) satisfies \(-1<\alpha<0\).

For \(x\in I\), put \(t=\sqrt{x+a}\). The rational estimates
\[
  29/50<t<1743/1000,\qquad a-t>0,\qquad
  |\phi_j(x)|<11/10
\]
follow by squaring and the displayed parameter interval. The derivative is
\[
  |\phi'_j(x)|=\frac{1}{4t\sqrt{a-t}} .
\]
On the enlarged interval of \(t\)'s, \(t^2(a-t)\) has only the positive critical point \(2a/3\), a maximum; its minimum is at one of the two endpoints. Replacing \(a\) by \(178651/100000\) decreases this expression. At both rational endpoints \(t=29/50,1743/1000\), direct rational arithmetic gives \(t^2(178651/100000-t)>1/9\). Therefore \(|\phi_j'|<3/4\) on \(I\).

Choose a sufficiently small \(\delta>0\) and the open stadium \(U=\{z:\operatorname{dist}(z,I)<\delta\}\). The branches are defined there by holomorphic square roots agreeing with the real choices; continuity on the compact interval gives \(\sup_U|\phi_j'|\le 4/5\). For \(z\in U\), integrate the derivative along the line segment from a nearest \(x\in I\) to \(z\) to obtain \(|\phi_j(z)-\phi_j(x)|\le(4/5)|z-x|\). Because \(\phi_j(I)\subset[-11/10,11/10]\subset I\), both branches map \(U\) into \(U\) (indeed their images are compactly contained there). They are univalent since \(g\circ\phi_j=\mathrm{id}\), and all word compositions are univalent on \(U\).

All \(S_w\) are normalized univalent maps on the same bounded simply connected \(U\), with \(S_w(0)=0, S'_w(0)=1\). The Koebe growth theorem after uniformizing \(U\) at 0 gives local boundedness; Montel and the univalent-limit theorem (or Hurwitz applied to difference quotients) give subsequential limits that are holomorphic univalent, because the derivative at 0 is still 1. For a fixed history, the prior suffix convergence near 0 identifies every such subsequential limit there with the existing \(H_\eta\). The identity theorem identifies them on all of \(U\). Normality then gives convergence on compact subsets of \(U\), and the existing chart has a unique continuation to \(U\), again denoted \(H_\eta\). In particular \(H_\eta'\ne0\) throughout \(U\).

The elementary bounds \(5/4<s<29/20\) follow from \(s=a^2-a\) and the rational parameter endpoints. Thus \(-s\) belongs to the interior of \(I\) and every \(H_\eta\) is holomorphic there. No analogous holomorphy at \(+s\) follows from \(U\), and below we prove it is impossible.

## 3. One-sided singularity for every limiting chart

For any history \(\xi\) and last letter \(j\), the exact chain rule for normalized word compositions and local convergence of derivatives give
\[
 H_{\xi j}(z)=
 \frac{H_\xi(\phi_j(z))-H_\xi(\phi_j(0))}
 {H_\xi'(\phi_j(0))\phi_j'(0)}
 \tag{1}
\]
on \(U\). The denominator \(D_{\xi,j}\) is nonzero. This is the same normalized append map as in the preceding analytic-history audit.

For real \(0\le x<s\), the branches continue by the real formulas and \(\phi_j(x)\in[-11/10,11/10]\). Thus (1) analytically continues \(H_{\xi j}\) along the entire half-open real segment to \(s\); local square-root charts agree on overlaps. At \(x=s-h\), \(h>0\) small,
\[
 \sqrt{x+a}=\sqrt{a^2-h}=a-\frac{h}{2a}+O(h^2),
 \qquad
 \phi_j(s-h)=\epsilon_j\sqrt{\frac{h}{2a}}+O(h^{3/2})
\]
with \(\epsilon_L=-1,\epsilon_R=+1\). Since \(H_\xi(0)=0\), \(H_\xi'(0)=1\), (1) yields a finite one-sided limit \(A_{\xi,j}=-H_\xi(\phi_j(0))/D_{\xi,j}\) and
\[
 H_{\xi j}(s-h)=A_{\xi,j}
 +\frac{\epsilon_j}{D_{\xi,j}\sqrt{2a}}\sqrt{h}+O(h).
 \tag{2}
\]
The coefficient is nonzero. A function holomorphic near \(s\) agreeing with this branch would have value \(A_{\xi,j}\) at \(s\) and difference from that value \(O(h)\), contrary to (2). This proves the nonremovable square-root singularity along the specified analytic continuation. It holds for every history because each has a last letter.

In particular for any two histories \(\xi,\zeta\),
\[
 H_\xi(z)\ne -H_\zeta(-z)
 \quad\text{as germs at }0.                         \tag{3}
\]
If the germs were equal, the right-hand side would continue holomorphically along \([0,s]\), since \([-s,0]\subset U\). By the identity theorem on successive overlapping neighborhoods the two branches would agree for \(0\le x<s\), contradicting (2). This argument does not require a maximal global continuation or a statement about all singularities.

## 4. Exact symbolic injectivity

Suppose \(H_{\xi j}=H_{\zeta k}\). By (1), equality implies an affine relation between \(H_\xi(\phi_j(z))\) and \(H_\zeta(\phi_k(z))\), with nonzero slope.

If \(j=k\), local univalence of \(\phi_j\) implies \(H_\xi(t)=A H_\zeta(t)+B\) near \(t=\phi_j(0)\). Analytic continuation in \(U\), followed by evaluation and differentiation at 0, gives \(B=0,A=1\). Thus \(H_\xi=H_\zeta\) on \(U\), and on the original chart neighborhood by germ uniqueness.

If \(j\ne k\), the exact reflection identity \(\phi_k=-\phi_j\) gives \(H_\xi(t)=A H_\zeta(-t)+B\) near \(t=\phi_j(0)\). Both sides are holomorphic on the connected component of \(U\cap(-U)\) containing the real segment from \(\phi_j(0)\) to 0 (the whole intersection is convex). Evaluating the continued relation and its derivative at 0 now gives \(B=0,A=-1\), contrary to (3).

Consequently equal shapes must have the same last letter and equal predecessor shapes. Repeating this implication inductively identifies every finite suffix of the histories; the histories are equal. Compactness of the history space, continuity of the history map (prior uniform suffix estimate), and the Hausdorff property of the chart space give the homeomorphism asserted in §1. QED.

The proof uses actual inverse branches; no generic nonlinearity assumption, numerical separation of finitely many histories, or claim that two distinct periodic multipliers suffice for global injectivity is needed. It also does not claim all nonlinear analytic IFS have an injective history map: the asymmetric critical value is essential here.

## 5. Consequences and boundary

The graph boundary of the preceding audit was shown to be the product of the forward address, the shape space, and the independent sector parity. Substituting the proven homeomorphism identifies it with the full backward address as claimed. In particular a compact Hausdorff realization retaining the normalized affine chart must distinguish every backward history, even after the physical endpoint and ordered sector phase have been fixed. Any finite truncation of the history fails to determine the exact chart. This is stronger than a mere continuum-cardinality result: it recovers the entire past as a continuous function of the chart.

The result concerns affine geometry on the actual normalized chart. It is not an obstruction to forgetting affine geometry when a proof-used observable is invariant under conformal reparametrization. It does not authorize additional root portraits, relative-cover classes, proper/end-proper intervals, Wave protection, a uniform-in-parameter estimate, or H1–H4/UPTCR/MLC. No canonical claim status is changed. The proof has not undergone independent human specialist review or Lean verification.

**Attribution.** The physical branch identifications, root parameter isolator, suffix compactness and independent angular phase are from the cited archive notes; the present singularity argument is a proposed internal strengthening. Classical tools: holomorphic inverse branches, Koebe growth, Montel, Hurwitz and the identity theorem. AI-assisted proof development and drafting: OpenAI GPT-6.2. No worldwide priority claim.
