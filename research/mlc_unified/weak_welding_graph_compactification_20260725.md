# Weak welding graph compactification: rejection and exact no-go

Date: 2026-07-25  
Status: **original claim rejected; weak-operator welding algebra no-go proved**  
Global status: `DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS`, `UPTCR`, and
`MLC` remain open

## 1. False projection formula

The previous note asserted that, for a bounded welding \(J:H\to H\),

\[
 P(J)=\frac12
 \begin{pmatrix}I&J^*\\J&I\end{pmatrix}
\tag{1.1}
\]

is the graph projection.  Formula (1.1) is a graph projection only in the
unitary case.

For scalar \(J=2\), (1.1) has eigenvalues \(3/2\) and \(-1/2\), so it is not
positive.  For scalar \(J=1/2\), it is not idempotent.

The correct orthogonal projection onto \(\operatorname{graph}J\) is

\[
 \Pi_J=
 \begin{pmatrix}
 A&AJ^*\\
 JA&JAJ^*
 \end{pmatrix},
 \qquad A=(I+J^*J)^{-1}.
\tag{1.2}
\]

Indeed, for \(Rx=(x,Jx)\), one has \(R^*R=I+J^*J\) and
\(\Pi_J=R(R^*R)^{-1}R^*\).

## 2. Weak operator topology does not preserve graph constraints

Let \(H=\ell^2(\mathbb Z)\), let \(Ue_k=e_{k+1}\), and put \(J_n=U^n\).
Then

\[
 J_n\rightharpoonup0
\]

in the weak operator topology, while

\[
 J_n^*J_n=I.
\]

Thus operator multiplication is not weakly continuous.

There is a direct graph failure.  With \(u_n=e_{-n}\),

\[
 u_n\rightharpoonup0,\qquad J_nu_n=e_0.
\]

The pairs \((u_n,J_nu_n)\in\operatorname{graph}J_n\) converge weakly to
\((0,e_0)\), which is not in \(\operatorname{graph}0\).

Because the \(J_n\) are unitary, their true graph projections are (1.1), and

\[
 \Pi_{J_n}\rightharpoonup\frac12I_{H\oplus H}.
\]

The limit is not idempotent and is not a graph projection.  Calling it a
"relaxed welding relation" supplies no composition, inverse, or gluing law.

## 3. What remains true

On a separable Hilbert space, every uniformly bounded sequence of operators
has a weak-operator convergent subsequence.  Positivity and a fixed upper
Loewner bound pass to the weak limit for a separately retained response
operator.

That elementary compactness statement does **not** preserve:

- \(J^*J\), composition, or inverse bounds;
- graph membership;
- phase-preserving welding;
- Dirichlet fiber-product constraints;
- protected prime-end markings; or
- a strict response transition.

Therefore weak-operator subsequence extraction is not a replacement for
`DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS`.

## 4. Required replacement

A usable compact state must have a topology or additional invariant in
which the actual trace relation, composition, inverse control, response
gluing, phase, protected accesses, and Value observables are jointly closed.
Alternatively, one must prove a strong/norm compactness or a uniform
quasisymmetric welding theorem for the source-defined physical ends.

Neither alternative is currently proved.  The detailed proof is in
`side_research_retained_lemmas.md`, Section 6.

