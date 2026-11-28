# Candidate statements and rejection record

**Status: no candidate retained; no Lean theorem claimed.**
This file records statements considered before any formalization. It is an
unsuccessful research checkpoint, not a new mathematical contribution or a
survey offered in place of the requested theorem.

Throughout, \(f_c(z)=z^2+c\) and \(P_n(c)=f_c^{\circ n}(0)\).

## A. A two-parameter critical-orbit cancellation criterion

### Candidate statement

Let \(c,d\in\mathbb C\) have bounded critical orbits. For \(j\ge1\), put
\(s_j=P_j(c)+P_j(d)\), and for \(n\ge1\) put
\(A_n=\prod_{j=1}^n s_j\). Assume every \(s_j\ne0\),
\(|A_n|\longrightarrow\infty\), and that the complex series
\(\sum_{n\ge1}A_n^{-1}\) converges. Then

\[
(c-d)\left(1+\sum_{n\ge1}A_n^{-1}\right)=0.
\]

In particular, nonvanishing of the parenthesized quantity forces \(c=d\).

### Check and rejection

Write \(h_n=P_n(c)-P_n(d)\) and \(\delta=c-d\). Subtraction gives

\[
h_{n+1}=s_n h_n+\delta,\qquad h_1=\delta.
\]

Division by \(A_n\) and telescoping gives the exact finite identity

\[
\frac{h_{n+1}}{A_n}
=\delta\left(1+\sum_{k=1}^n A_k^{-1}\right).
\]

The left side tends to zero by boundedness. This proves the displayed
candidate in ordinary mathematics, but it is precisely variation of constants
for a first-order scalar recurrence. Its proof needs no new idea.
No relation between its cancellation condition and equal combinatorics has
been established. Introducing a matrix or calling the expression a nonlinear
Thurston obstruction does not change this fact.

**Decision: discarded before Lean formalization.** This written calculation
does not count as a result under the user's required Lean-and-novelty gate.

The archive's existing phase-variable secants are in
[QuadraticParameterUnivalence.lean](../../formalization/weighted/QuadraticParameterUnivalence.lean);
the cross-parameter calculation above differs in variables, but that alone
does not establish mathematical novelty.

## B. Center derivative versus Thurston determinant

### Candidate statement

For a quadratic center \(c\) of exact critical period \(p\ge3\), let
\(\chi_c\) be the characteristic polynomial of the actual Thurston pushforward
on integrable meromorphic quadratic differentials with poles in the
postcritical set. Then
\[
P_p'(c)=-\frac{\chi_c(1)}{\chi_c(0)}\ne0.
\]

### Closest result and decision

This is the degree-two specialization of Buff–Epstein–Koch,
*Eigenvalues of the Thurston operator*, Proposition 13; the needed exclusion
of eigenvalues zero and one follows from their Theorem 3. Proposition 12
already gives the critical-cycle characteristic polynomial. Theorem 4
already puts the unit circle in the closure of the union of center spectra.

**Decision: discarded as classical.** Mere spectral degeneration, determinant
repackaging, and center transversality cannot be counted as new results.
No fiber-specific estimate was proved.

Primary source, with this numbering:
[author PDF](https://www.math.univ-toulouse.fr/~buff/Preprints/Eigenvalues/eigenvalues.pdf)
([published DOI](https://doi.org/10.1112/topo.12145)).

## C. Angled internal addresses separate nonhyperbolic combinatorial classes

### Candidate statement

For any \(c,d\in M\) whose combinatorial classes are nonhyperbolic,
equality of their angled internal addresses implies \(c=d\).
Here a nonhyperbolic class means a class containing no hyperbolic parameter;
this is not interchangeable with merely requiring that \(c\) and \(d\)
themselves be nonhyperbolic.

### Closest result and decision

Schleicher's *Internal Addresses of the Mandelbrot Set and Galois Groups of
Polynomials*, Theorem 3.9 and the discussion of combinatorial classes, already
identify the combinatorial information carried by those addresses.
Singleton nonhyperbolic classes are exactly the unresolved strengthening
relevant here.

**Decision: not retained.** This statement has not been proved in this
investigation; recoding the same class does not add a separating invariant.

Primary source:
[published article](https://armj.math.stonybrook.edu/html-articles/Files-2015-2024/16-42/).
For the separate fiber terminology, see Schleicher,
[On Fibers and Local Connectivity of Mandelbrot and Multibrot Sets](https://arxiv.org/abs/math/9902155).
Combinatorial classes and all versions of fibers must not be identified
without their definitions and the relevant theorem.

## D. Infinite intersection of two critical orbits

### Candidate statement

If
\[
\{P_n(c):n\ge0\}\cap\{P_n(d):n\ge0\}
\]
is infinite, then \(c=d\).

### Closest result and decision

Ghioca–Tucker–Zieve, *Intersections of polynomial orbits, and a dynamical
Mordell–Lang conjecture*, Theorem 1.1, gives a common iterate for nonlinear
complex polynomials of the same degree whose orbits intersect infinitely.
For monic centered quadratics the coefficient of \(z^{2^k-2}\) in
\(f_c^{\circ k}\) is \(2^{k-1}c\), so a common iterate gives \(c=d\).

**Decision: discarded as a direct classical consequence.** Equal combinatorics
does not supply the orbit-intersection hypothesis.

Primary source:
[author PDF](https://websites.umich.edu/~zieve/papers/mordell-lang.pdf).

## E. Six projectively matching critical-orbit points

### Candidate statement

Suppose \(P_0(c),\ldots,P_4(c)\) are pairwise distinct and a Möbius map \(T\)
satisfies \(T(P_j(c))=P_j(d)\) for \(0\le j\le5\). Then \(c=d\).

### Check and rejection

The degree-two rational maps \(T\circ f_c\) and \(f_d\circ T\) agree at
five distinct points. After clearing denominators their difference has
numerator degree at most four, hence vanishes identically. The conjugacy
preserves the marked critical point zero, so it also preserves the other
critical point infinity. Thus \(T(z)=az\). Comparing the quadratic and
constant coefficients gives \(a=a^2\), hence \(a=1\) and \(c=d\).

**Decision: discarded.** The mechanism is the polynomial root bound and
normalization of a rational conjugacy. It has no proved connection to two
points of a common combinatorial fiber. Classifying exceptional shorter
configurations would not repair that missing connection.

## What has not been obtained

No statement with both a genuinely new proof mechanism and a proved
connection to the actual quadratic-family fiber problem survived.
In particular, no uniform comparison of Thurston operators on increasing
postcritical marked sets, no separating enrichment of kneading data,
and no new injectivity theorem for the pinched-disk model were proved.

These rejections are scoped to the candidates above. They are not a theorem
that such an approach is impossible, and they make no exhaustive claim about
the literature. No excluded archive machinery was used to manufacture a
replacement result.
