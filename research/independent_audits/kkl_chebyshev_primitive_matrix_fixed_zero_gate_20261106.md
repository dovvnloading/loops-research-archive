# Issue #40 — a real quadratic with primitive expanding Markov incidence and a fixed prime-end access

**Date:** 2026-11-06.  
**Status:** exact holomorphic **negative control** for the shortcut “primitive \(T_F\)-like edge growth rules out periodic zero-mass marked sectors,” and a formal admissibility audit showing why the tempting adjacent-atom zero-core Wave construction **fails**. It does **not** disprove KKL's prime primitive **renormalization** theorem because this quadratic has no such renormalization; its matrix is a *real Markov-refined postcritical* incidence matrix, not the KKL small-Julia-cycle \(T_F\).

**Source issue:** Kahn–Kapiamba–Lyubich [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §2.5 for the true primitive Hubbard-edge operator and §2.6–2.7 for its native dual-arc realization, §6.1 Proposition 6.9's invocation of \(\lambda_F>1\), Appendix A.1 for marked intervals and Wave crests. The test is motivated by the exact dual-WAD/endpoint reduction in [the companion note](./kkl_dual_arc_wave_core_reduction_20261106.md).

## 1. An actual periodically repelling quadratic with a primitive growing graph

Take the **genuine holomorphic quadratic polynomial**

\[
\boxed{P(z)=4z(1-z).}
\tag{1.1}
\]

The affine change \(w=2-4z\) gives

\[
(2-4P(z))=(2-4z)^2-2.
\tag{1.2}
\]

Thus \(P\) is conjugate to the Chebyshev quadratic \(w\mapsto w^2-2\). Its filled Julia set is exactly the real interval

\[
K_P=[0,1],
\tag{1.3}
\]

and all of its finite periodic cycles are repelling. The critical orbit is strictly preperiodic:

\[
\frac12\longmapsto 1\longmapsto 0\longmapsto 0,
\qquad P'(0)=4.
\tag{1.4}
\]

Choose an actual quadratic-like restriction \(P:U'\to U\) with
\[
U=D(\tfrac12,2),\qquad U'=P^{-1}(U).
\tag{1.5}
\]
The domain \(U'\) is a connected Jordan disk containing \(K_P\) and is compactly contained in \(U\), since
\[
4|z-\tfrac12|^2=|1-P(z)|\le|P(z)-\tfrac12|+\tfrac12<\tfrac52
\quad(z\in U'),
\]
so \(|z-\frac12|<\sqrt{5/8}<2\). Thus the pair \((f,\iota)=(P,\mathrm{inclusion})\) is a genuine quadratic-like/\(\psi\)-ql stage.

Set \(T=[0,1]\); it is the postcritical Hubbard hull. **There is no excess preimage hair**:

\[
\boxed{T'=P^{-1}(T)=T.}
\tag{1.6}
\]

Indeed, for \(y\in[0,1]\), the two solutions of \(4z(1-z)=y\) are \((1\pm\sqrt{1-y})/2\in[0,1]\), and there are no others.

Subdivide at the **actual critical point** \(1/2\) to form two monotone Markov edges

\[
L=[0,\tfrac12],\qquad R=[\tfrac12,1].
\tag{1.7}
\]

The **same polynomial** maps each edge onto the full old tree:

\[
P(L)=P(R)=[0,1],
\quad L\mapsto LR,\quad R\mapsto R^{-1}L^{-1}
\tag{1.8}
\]

where edge orientations are taken left-to-right. Therefore the **honest holomorphic Markov incidence matrix** is

\[
\boxed{
M=
\begin{pmatrix}1&1\\1&1\end{pmatrix},
\quad M>0,\quad \rho(M)=2.
}
\tag{1.9}
\]

This matrix is **primitive** (all entries are already positive), not merely irreducible. Each target subedge has exactly two actual inverse strips, each inside \(T\). There is no arbitrarily chosen automaton.

**Scope:** The “edges” in (1.7) are a Markov refinement including the critical point as a vertex. They are **not** KKL's E(\(\mathcal T\)) for a prime primitive small-Julia renormalization, because this map has no such renormalization. Formula (1.9) is therefore a genuine **analytic structural counterexample to a bare matrix-to-gate inference**, not a counterexample to any KKL statement whose additional native hypotheses are essential.

## 2. The actual prime-end covering fixes one terminal access

The complements \(V=U\setminus T\) and \(V'=U'\setminus T'\) are genuine annuli. The inclusion immersion \(\iota:V'\hookrightarrow V\) is **proper on the inner prime-end boundary** because the carriers are identical; it introduces no additional component Carathéodory boundaries.

The exact Joukowski uniformization of the slit complement is

\[
\Psi(w)=\frac12+\frac14(w+w^{-1}),\quad |w|>1.
\tag{2.1}
\]

Direct substitution gives

\[
\boxed{
P(\Psi(w))=\Psi(-w^2).
}
\tag{2.2}
\]

Consequently the **actual** degree-two prime-end covering is, in the same source/target angular chart \(w=e^{2\pi is}\),

\[
\boxed{p(s)=2s+\tfrac12\pmod1.}
\tag{2.3}
\]

The planar terminal point \(x=0\) corresponds to the **unique** slit-tip prime end

\[
e=\tfrac12\in\mathbb R/\mathbb Z,
\quad \Psi(-1)=0.
\tag{2.4}
\]

That prime end is genuinely fixed:

\[
\boxed{p(e)=e,\qquad \iota^*\{e\}=\{e\}.}
\tag{2.5}
\]

The full analytic degree-two circle map **has a fixed zero-dimensional gate**, even though the Markov edge matrix (1.9) is strictly positive and expanding. It is the actual polynomial dynamics, not a finite circle simulation.

## 3. A fixed access **does not** automatically give a KKL Wave

The *genuine* polynomial fixed-access conclusion (2.5) remains correct. However **the original proposed positive-width Wave between the two adjacent marking atoms was invalid**, and is **withdrawn**. Here is the exact source-defined obstruction:

KKL Appendix A.1 says that a proper path in \((\mathcal V,\mathcal I)\) is **not subordinate to any multi-interval of combinatorial length at most two**. The proposed collar paths have endpoints in the adjacent slit-side atoms \(\mathbf I_0=(0,1/2)\), \(\mathbf I_1=(1/2,1)\), and are subordinate to their connected two-atom short base

\[
B=\mathbf I_0\cup\{e\}\cup\mathbf I_1,\qquad \ell(B)=2.
\tag{3.1}
\]

Consequently **none of those collar paths is a valid marked path**, so their positive-modulus quadrilateral is **not a KKL Wave**. In particular, there is no established positive-width zero-crest Wave \(A\) with \(C_A=\{e\}\) in this example.

The **correct** surviving analytic statement is

\[
\boxed{
M=\begin{pmatrix}1&1\\1&1\end{pmatrix}
\text{ is primitive with }\rho(M)=2,
\quad p(e)=e,\quad \iota^*\{e\}=\{e\}.
}
\tag{3.2}
\]

This shows primitive Markov expansion alone does not prevent a fixed **marked endpoint access**. It does **not** show that the endpoint is the crest of an admissible KKL Wave or that it belongs to a genuine critical-visit chain. These extra assertions require additional native geometric proof.

## 4. Precise implication and no overclaim

This analytic calculation tests the following **unqualified** inference, but only its endpoint part:

> A genuine holomorphic degree-two tree map with a primitive expanding positive edge matrix cannot have periodic proper zero-core prime-end sectors or that they can be valid KKL Wave crests.

The weaker claim that primitive expansion forces every **marked endpoint** to be nonperiodic is **false** by (1.9) and (2.5). The stronger claimed implication about **genuine Wave crests is not tested** by this example, because the proposed Wave is inadmissible as shown in §3. Primitive edge expansion constrains the positive edge cone; it does not alone control fixed endpoint accesses.

This is **not** a counterexample to KKL Proposition 6.9 or Lemma 6.4 in their required class. The polynomial is not primitively renormalizable, has no KKL small-Julia cycle, and no native limb \(\mathbf L_0\) or KKL critical-visit chain was constructed. In particular one cannot infer the hypothesis “intersects \(\mathbf L_0\)” from this fixed tip.

**Use in Issue #40:** A zero-core proof must rule out (or declare terminal) cycles of the **actual endpoint/turn gate dynamics** meeting the specific critical-limb condition, and separately handle the non-LC impression/attachment locus **if those endpoints actually occur as admissible critical crests**. The dual-bivertical-arc spectral machinery of KKL §2.6–2.7 is valid in its typed domain and does not alone exclude cycles outside that positive cone. This precisely justifies the **finite marked endpoint gate graph** proposed in the companion note.

**Keep OPEN:** Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, and MLC. No synthetic simulator, full native-category proof, or independent referee validation is claimed.
