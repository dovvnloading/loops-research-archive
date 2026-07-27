# Retained lemmas from the side-research library

Date: 2026-07-25  
Status: narrow proved statements and exact no-go results  
Global status: `MLC`, `UPTCR`, and `VAAPC-I` remain open

This note contains the proofs that survived the side-library audit.  Every
statement is deliberately narrower than the unresolved dynamical
realization and parameter-rigidity problems.

## 1. Primitive-root parabolic nondegeneracy

### Theorem 1.1

Let \(\lambda\) be a primitive \(q\)-th root of unity, \(q\ge2\), and set

\[
 g(w)=\lambda w+w^2.
\]

Then

\[
 g^q(w)=w+C_{\lambda,q}w^{q+1}+O(w^{q+2})
 \quad\text{with}\quad C_{\lambda,q}\ne0.
\tag{1.1}
\]

In particular, every coefficient of degrees \(2,\ldots,q\) vanishes.

### Proof: resonance cancellation

Put \(F=g^q\).  Since \(F'(0)=\lambda^q=1\), write

\[
 F(w)=w+a_mw^m+O(w^{m+1})
\]

at the first nonzero nonlinear term.  Such a term exists because \(F\) is a
polynomial of degree \(2^q\), hence is not the identity polynomial.

Both \(F\) and \(g\) are iterates of \(g\), so \(F\circ g=g\circ F\).
At degree \(m\), after cancelling the common contribution from \(g(w)\),

\[
 a_m\lambda^m=a_m\lambda.
\]

Because \(a_m\ne0\),

\[
 \lambda^{m-1}=1.
\]

Primitivity of \(\lambda\) gives \(q\mid(m-1)\).  Therefore

\[
 m=1+kq
\tag{1.2}
\]

for an integer \(k\ge1\), proving the cancellation through degree \(q\).

### Proof: quadratic nondegeneracy

For a parabolic germ whose first nonlinear degree is \(1+kq\), the iterate
\(F=g^q\) has \(kq\) attracting petals.  Multiplication by the primitive
root \(\lambda\) permutes their tangent directions in cycles of length
exactly \(q\).  Thus the petals form \(k\) cycles for the original map
\(g\).

We use the classical Fatou theorem that every cycle of immediate attracting
or parabolic basin components of a rational map contains a critical point.
For a polynomial there is no finite asymptotic value.  The polynomial \(g\)
has exactly one finite critical point,

\[
 c_g=-\frac{\lambda}{2}.
\]

The critical point at infinity belongs to the basin of infinity and cannot
lie in a finite parabolic basin cycle at \(0\).  Distinct cycles of
immediate parabolic basins are disjoint, so they require distinct finite
critical points.  Hence \(k\le1\).  Since \(k\ge1\), we have \(k=1\).
Equation (1.2) therefore gives \(m=q+1\), and the coefficient in (1.1) is
nonzero.

The standard basin-critical-point input is recorded, for example, in
L. Geyer's complex-dynamics notes, Corollaries 11.6 and 11.8:
<https://www.math.montana.edu/geyer/2016-fall-m597/materials/s2016-complex-dynamics-notes.pdf>.

### Formal coefficient cross-check

Let

\[
 \phi(z)=z+\sum_{n\ge2}b_nz^n,\qquad
 h(z)=\lambda z+Az^{q+1}+O(z^{q+2}),
\]

and solve \(g\circ\phi=\phi\circ h\) through degree \(q+1\).  With
\(b_1=1\) and

\[
 S_n=\sum_{i=1}^{n-1}b_i b_{n-i},
\]

coefficient comparison gives

\[
 b_n=\frac{S_n}{\lambda^n-\lambda},
 \qquad 2\le n\le q,
\tag{1.3}
\]

whose denominators are nonzero by primitivity, and

\[
 A=S_{q+1}.
\tag{1.4}
\]

Iterating the resonant normal form yields

\[
 [z^{q+1}]\,h^q=q\lambda^{q-1}A.
\tag{1.5}
\]

A tangent-to-identity conjugacy preserves the first nonlinear coefficient,
so (1.5) equals \(C_{\lambda,q}\).  Equations (1.3)--(1.5) are an exact
algebraic audit, not the source of the all-order nonvanishing proof.

### Scope

The theorem constructs a local parabolic normal-form anchor.  It supplies no
uniform Ecalle cylinder, Lavaurs phase transport, protected carrier,
satellite-to-neutral comparison, or parameter estimate.

## 2. Fixed modulus does not force ambient end shrinking

### Theorem 2.1

There are nested univalent images \(D_m\) of the unit disk and conformally
conjugate degree-two quadratic-like maps on them such that every
quadratic-like modulus is the same, while

\[
 \bigcap_{m\ge0}\overline{D_m}
\]

contains a nondegenerate continuum.

### Proof

Fix \(0<r<1\) and let

\[
 E_r=\left\{x+iy:x^2+\frac{y^2}{r^2}<1\right\}.
\]

This symmetric ellipse is contained in the unit disk \(\mathbb D\) and its
boundary meets \(\partial\mathbb D\) at \(\pm1\).

Let \(\phi:\mathbb D\to E_r\) be the unique Riemann map normalized by

\[
 \phi(0)=0,\qquad \phi'(0)>0.
\]

Uniqueness and the symmetries of \(E_r\) imply

\[
 \phi(\overline z)=\overline{\phi(z)},\qquad
 \phi(-z)=-\phi(z).
\]

Carathéodory's theorem extends \(\phi\) homeomorphically to the boundary.
The positive and negative real boundary points must therefore satisfy
\(\phi(1)=1\) and \(\phi(-1)=-1\), and

\[
 \phi([-1,1])=[-1,1].
\tag{2.1}
\]

Because \(E_r\subset\mathbb D\), the iterates of \(\phi\) are defined and

\[
 \overline{\mathbb D}\supset\phi(\overline{\mathbb D})
\supset\phi^2(\overline{\mathbb D})\supset\cdots.
\]

By (2.1), every member contains \([-1,1]\).  Hence their intersection is
nondegenerate.

Now choose a quadratic-like map \(F:A\to B\) with
\(\overline B\subset\mathbb D\).  Define

\[
 F_m=\phi^m\circ F\circ\phi^{-m}:
 \phi^m(A)\longrightarrow\phi^m(B).
\]

Each \(F_m\) is proper of degree two, and conformal invariance gives

\[
 \operatorname{mod}\bigl(\phi^m(B)\setminus
 \overline{\phi^m(A)}\bigr)
 =\operatorname{mod}(B\setminus\overline A).
\]

Thus fixed finite moduli of conjugated returns do not force the ambient
nested images to shrink.

### Scope

This is an interface countermodel, not a quadratic-polynomial
counterexample and not a counterexample to MLC.  It identifies the missing
serial-separation or equivalent ambient-control hypothesis.

## 3. Serial annuli force a singleton end

### Theorem 3.1

Let \(K_0\supset K_1\supset\cdots\) be compact full planar continua in one
bounded localization, and put \(K=\bigcap_nK_n\).  Suppose there are
pairwise disjoint annuli \(A_n\) such that:

1. \(A_n\subset\widehat{\mathbb C}\setminus K\);
2. \(A_n\) separates \(K_n\), hence \(K\), from one fixed nondegenerate
   full outer continuum \(L\); and
3. the annuli occur in the same nesting order, with no side bypass.

If

\[
 \sum_{n=0}^{\infty}\operatorname{mod}(A_n)=\infty,
\tag{3.1}
\]

then \(K\) is a singleton.

### Proof

Assume that \(K\) contains two distinct points.  Since \(K\) and the fixed
outer continuum \(L\) are disjoint nondegenerate continua, the doubly
connected domain separating them has finite conformal modulus.  Every
\(A_n\) is an essential, pairwise disjoint subannulus of that domain.
Grötzsch superadditivity therefore gives

\[
 \sum_{n=0}^N\operatorname{mod}(A_n)
 \le \operatorname{mod}(\widehat{\mathbb C}\setminus(K\cup L))
 <\infty
\]

for every \(N\), contradicting (3.1).  Thus \(K\) has at most one point.
Nested compactness makes \(K\) nonempty, so it is a singleton.

### Scope

The conclusion requires actual pairwise-disjoint serial annuli around the
same end and one fixed outer side.  The current direct/virtual construction
does not yet realize these hypotheses or rule out side bypasses.

## 4. Sectorwise dyadic Bottcher trace isometry

### Theorem 4.1

Let \(T:I\to J\) be an affine bijection between intervals, with either
orientation.  For \(u:J\to\mathbb C\),

\[
 [u]_{\dot H^{1/2}(J)}^2
 =\int_J\int_J\frac{|u(x)-u(y)|^2}{|x-y|^2}\,dx\,dy.
\]

Then

\[
 [u\circ T]_{\dot H^{1/2}(I)}
 =[u]_{\dot H^{1/2}(J)}.
\tag{4.1}
\]

### Proof

Write \(T(\xi)=a+s\xi\) with \(s\ne0\).  Under
\(x=T(\xi)\), \(y=T(\eta)\), the two-dimensional Jacobian contributes
\(|s|^2\), while

\[
 |x-y|^2=|s|^2|\xi-\eta|^2.
\]

The factors cancel exactly, proving (4.1).

For one declared inverse Böttcher angular lift

\[
 T_{k,q}(\theta)=\frac{\theta+k}{2^q}
\]

on one compatible sector, normalized intrinsic pullback therefore has norm
one, independently of \(q\).

### Scope

This is a homogeneous, one-sector statement.  It supplies neither a
multisector identification nor a bounded physical-to-core welding,
all-depth contact closure, endpoint protection, or coercive response.

## 5. Correct multi-port gauge and strictness obstruction

### Proposition 5.1

For a connected Dirichlet cell with ports
\(\Gamma_1,\ldots,\Gamma_N\), the energy is invariant under adding one
common constant to all boundary traces.  It is not invariant under adding
independent constants to the individual ports.

### Proof

Adding one constant to a harmonic extension does not change its gradient.
For the second statement, take the rectangle
\((0,R)\times(0,1)\) with constant endpoint traces \(a\) and \(b\).
The affine minimizer has energy

\[
 \frac{(a-b)^2}{R},
\]

which changes under independent shifts of \(a\) or \(b\).  Thus the correct
connected-cell trace state is

\[
 \left(\bigoplus_{i=1}^N H^{1/2}(\Gamma_i)\right)
 \Big/\operatorname{span}\{(1,\ldots,1)\},
\tag{5.1}
\]

or an equivalent mean-zero state augmented by \(N-1\) relative port
potentials.

### Proposition 5.2

A strict response factor is not stable under addition of arbitrary common
nonnegative energy.

### Proof

Let \(q_{\rm out}=\mu q_{\rm in}\) with \(0<\mu<1\), and add
\(c=tq_{\rm in}\), \(t\ge0\), to both sides.  Then

\[
 \frac{q_{\rm out}+c}{q_{\rm in}+c}
 =\frac{\mu+t}{1+t},
\]

which is larger than \(\mu\) for \(t>0\) and tends to one.  A strict
post-gluing estimate therefore requires a relative bound on the added
energy, a separately coercive transition for the full state, or an explicit
additive-error budget.

## 6. Weak operator compactness does not compactify welding algebra

### Proposition 6.1

For bounded \(J:H\to H\), the orthogonal projection onto its graph is

\[
 \Pi_J=
 \begin{pmatrix}
 A&AJ^*\\
 JA&JAJ^*
 \end{pmatrix},
 \qquad A=(I+J^*J)^{-1}.
\tag{6.1}
\]

The formula

\[
 \frac12\begin{pmatrix}I&J^*\\J&I\end{pmatrix}
\tag{6.2}
\]

is not a graph projection for general bounded \(J\).

### Proof

Let \(R:H\to H\oplus H\) be \(Rx=(x,Jx)\).  Then
\(R^*R=I+J^*J\), so the orthogonal projection onto
\(\operatorname{ran}R=\operatorname{graph}J\) is

\[
 R(R^*R)^{-1}R^*,
\]

which is (6.1).  For scalar \(J=2\), (6.2) has eigenvalues
\(3/2\) and \(-1/2\), so it is not positive.  This disproves the general
claim.

### Theorem 6.2

Uniform boundedness and weak operator subsequence convergence do not
preserve welding composition, inverse relations, or graph constraints.

### Proof

On \(H=\ell^2(\mathbb Z)\), let \(Ue_k=e_{k+1}\) and \(J_n=U^n\).  For
fixed \(x,y\in H\),

\[
 \langle U^nx,y\rangle\longrightarrow0,
\]

first for finitely supported vectors and then for all vectors by density and
uniform boundedness.  Thus \(J_n\to0\) in the weak operator topology.
Nevertheless,

\[
 J_n^*J_n=I
\]

for every \(n\), so multiplication is not weakly continuous.

Set \(u_n=e_{-n}\).  Then \(u_n\rightharpoonup0\), but

\[
 J_nu_n=e_0.
\]

Therefore pairs in the varying graphs can converge weakly to a pair not in
the graph of the weak limit.

Because every \(J_n\) is unitary, (6.1) reduces to (6.2), and
\[
 \Pi_{J_n}\rightharpoonup\frac12I_{H\oplus H}.
\]
The limit is not idempotent and is not a graph projection.  Weak operator
compactness alone is therefore not a welding compactification compatible
with gluing.

### Scope

The open welding gate needs a topology or invariant that preserves the
actual trace relation, composition, inverse control, phase, protected
markings, response forms, and transition inequalities.  Weak operator
boundedness by itself supplies none of these.

## 7. Correct finite quadratic-like conjugacy statement

Let \(F:A\to B\) be quadratic-like, \(A\Subset B\), and let \(\phi\) be
univalent on \(B\).  Then

\[
 F_\phi=\phi\circ F\circ\phi^{-1}:\phi(A)\to\phi(B)
\]

is quadratic-like of the same degree and modulus, and

\[
 K(F_\phi)=\phi(K(F)),
\qquad
 K(F)=\{z\in A:F^n(z)\in A\text{ for every }n\ge0\}.
\tag{7.1}
\]

Indeed \(F_\phi^n=\phi\circ F^n\circ\phi^{-1}\) wherever the iterates are
defined, so survival in the source domain is equivalent under \(\phi\).
This finite conjugacy does not make \(F_\phi\) an iterate of the original
quadratic polynomial and does not construct a limiting virtual return.
