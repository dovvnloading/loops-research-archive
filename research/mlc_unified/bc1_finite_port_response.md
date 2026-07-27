# BC1: finite-port response realization and the Value-observability obstruction

## 1. Status

This note proves the finite-dimensional analytic and electrical core of `BC1` and
isolates the remaining uniform dynamical theorem.

It proves:

1. every fixed finite-electrode surface has an exact response matrix;
2. a future-closed port quotient has an exact compressed response;
3. every finite WAD with an incidence-faithful port assignment has an exact graph
   Laplacian;
4. KKL WAD domination implies a Loewner-order response inequality when its
   itineraries are represented faithfully;
5. the surface and WAD forms are comparable on each fixed nondegenerate block;
6. response plus total WAD weight does **not** determine KKL Value after a port
   quotient merges support classes with different Value coefficients.

It does not prove uniform comparison constants, a universal number of future-closed
ports, or the virtual analytic realization. Those remain the global content of
`H2_RESPONSE_REALIZATION`.

## 2. Finite electrode surfaces

Let \(S\) be a finite disjoint union of compact smooth bordered Riemann surfaces.
Choose pairwise disjoint compact electrode arcs
\[
  P_1,\ldots,P_d\subset\partial S
\]
whose closures are mutually separated in \(\partial S\). Every component of \(S\)
must meet at least one electrode. The rest of the boundary is insulating.

For \(x=(x_1,\ldots,x_d)\in\mathbb R^d\), let \(\mathcal A_x\) be the affine Sobolev
class of real \(H^1(S)\) functions whose trace is \(x_i\) on \(P_i\). Define
\[
  \mathcal E_S(x)
  =
  \inf_{u\in\mathcal A_x}
  \int_S |\nabla u|^2\,dA.
\tag{2.1}
\]
The integral is conformally invariant in real dimension two. The separation
hypothesis makes every \(\mathcal A_x\) nonempty; it also avoids forcing
infinite-energy jumps at adjacent electrode endpoints.

### Theorem 2.1 (exact surface response)

There is a unique symmetric positive semidefinite matrix
\(\Lambda_S\in\operatorname{Sym}_d^+\) such that
\[
  \mathcal E_S(x)=x^{\mathsf T}\Lambda_Sx
\tag{2.2}
\]
for every \(x\in\mathbb R^d\). Moreover:

1. \(\Lambda_S\mathbf 1_C=0\) for the indicator of the electrodes on every connected
   component \(C\) of \(S\);
2. its kernel consists exactly of vectors constant on the electrodes belonging to
   each component;
3. its off-diagonal entries are nonpositive and its row sums are zero;
4. consequently it is the Laplacian of the complete conductance graph on the
   electrodes, with conductances
   \[
     c_{ij}=-(\Lambda_S)_{ij}\ge0,\qquad i\ne j.
   \tag{2.3}
   \]

**Proof.** For each \(i\), let \(h_i\) be the weak harmonic function equal to \(1\) on
\(P_i\), equal to \(0\) on the other electrodes, and satisfying the natural Neumann
condition on the insulating boundary. Direct minimization gives existence and
uniqueness. Linearity of the mixed Dirichlet--Neumann problem shows that the minimizer
for \(x\) is
\[
  h_x=\sum_i x_i h_i.
\]
Thus (2.2) holds with
\[
  (\Lambda_S)_{ij}
  =
  \int_S\langle\nabla h_i,\nabla h_j\rangle\,dA.
\tag{2.4}
\]
This proves symmetry and nonnegativity.

The energy is zero exactly when \(h_x\) is constant on each component, which proves
the kernel statement. Constant boundary data have constant harmonic extension, so
the componentwise row sums vanish.

For \(i\ne j\), the maximum principle gives \(0\le h_i\le1\). Green's identity writes
\((\Lambda_S)_{ji}\) as the outward flux of \(h_i\) through \(P_j\). Since \(h_i=0\)
there and is nonnegative inside, that flux is nonpositive. Hence
\((\Lambda_S)_{ij}\le0\). The zero row sums now give the graph-Laplacian
representation (2.3). \(\square\)

The theorem is exact but block-dependent. It does not say that the number of
electrodes or the spectrum of \(\Lambda_S\) is uniform along a renormalization tower.

## 3. Port compression

Let
\[
  \pi:\{1,\ldots,d\}\longrightarrow\{1,\ldots,\bar d\}
\]
be a port quotient and let \(J_\pi:\mathbb R^{\bar d}\to\mathbb R^d\) repeat a
quotient potential on every member of its fiber.

### Proposition 3.1 (exact compressed form)

On potentials constant on the fibers of \(\pi\), the exact response is
\[
  \Lambda_{S,\pi}=J_\pi^{\mathsf T}\Lambda_SJ_\pi,
\qquad
  \mathcal E_S(J_\pi y)=y^{\mathsf T}\Lambda_{S,\pi}y.
\tag{3.1}
\]

**Proof.** Substitute \(x=J_\pi y\) into (2.2). \(\square\)

### Definition 3.2 (future-closed quotient)

A port quotient is **future closed through a declared block horizon** if no later
pullback, restriction, Wave/Wanderers use, or chart transition permits two electrodes
in one present fiber to carry different potentials or different oriented access
labels.

Future-closedness is not cosmetic. It is the exact information condition under which
(3.1) remains a sufficient state.

### Proposition 3.3 (non-future-closed compression loses response data)

If a quotient identifies two ports that may later separate, its compressed response
does not determine the later response.

**Proof.** Take two ports joined by conductance \(g>0\):
\[
  \Lambda_g
  =
  g
  \begin{pmatrix}
    1&-1\\
    -1&1
  \end{pmatrix}.
\]
Identifying the two ports restricts to potentials \((t,t)\) and gives the zero
\(1\times1\) response for every \(g\). After the ports separate, the energy of
\((0,1)\) is \(g\), which cannot be recovered from the compressed state. \(\square\)

Thus a quotient based only on present translation equivalence is invalid unless the
equivalence persists for every later use inside the complete block.

## 4. Exact WAD response

Let
\[
  X=\sum_{a\in A}w_a a,\qquad w_a>0,
\tag{4.1}
\]
be a finite WAD. An **incidence-faithful port assignment** gives each oriented end of
every \(a\) a port vertex \(s(a)\) or \(t(a)\). The two ends of a positive
self-access must remain distinct unless a proved future-closed equivalence identifies
them.

Let \(B_X\) be the signed port--arc incidence matrix, with column
\(e_{s(a)}-e_{t(a)}\) for \(a\). Define
\[
  L_X=B_X\operatorname{diag}(w_a)B_X^{\mathsf T}.
\tag{4.2}
\]

### Proposition 4.1 (exact WAD quadratic form)

For every port potential \(x\),
\[
  x^{\mathsf T}L_Xx
  =
  \sum_{a\in A}w_a\bigl(x_{s(a)}-x_{t(a)}\bigr)^2.
\tag{4.3}
\]
If a subset \(I\) of ports is declared internal and every network component meets the
retained terminal set \(T\), minimizing over \(x_I\) gives the Schur-complement
response
\[
  \Lambda_X^T
  =
  (L_X)_{TT}
  -(L_X)_{TI}(L_X)_{II}^{\dagger}(L_X)_{IT}.
\tag{4.4}
\]

**Proof.** Equation (4.3) follows by expanding (4.2). Equation (4.4) is the response
calculus proved in `network_response_state.md`. \(\square\)

For the KKL canonical WAD, every support coordinate is induced by a rectangular
lamination of the same extremal width. Therefore (4.3) is the exact Dirichlet energy
of the disjoint rectangular carrier when its port sides are equipotentials. Promoting
those ideal sides to separated electrodes in the actual virtual surface, and
controlling the energy of the complementary thick pieces, is an additional analytic
step.

## 5. KKL domination is electrical domination

Suppose \(X\) dominates \(Y\) in the source sense:
\[
  X\ge\sum_i\sum_{j=1}^{m_i}w_{ij}\alpha_{ij},
  \qquad
  Y=\sum_i v_i\beta_i,
  \qquad
  \bigoplus_jw_{ij}\ge v_i.
\tag{5.1}
\]
Assume the port assignment is **itinerary faithful**: the ordered arcs
\((\alpha_{ij})_j\) form a port path from the initial port of \(\beta_i\) to its final
port, including every intermediate ideal interval appearing in the restriction
itinerary.

### Theorem 5.1 (domination-to-Loewner theorem)

Let \(T\) be the target ports and eliminate every intermediate itinerary port. Then
\[
  \Lambda_X^T\succeq L_Y
\tag{5.2}
\]
as quadratic forms on \(\mathbb R^T\).

**Proof.** Allocate to the \(i\)-th itinerary a path network with successive
conductances \(w_{i1},\ldots,w_{im_i}\). Its effective endpoint conductance is
\[
  c_i=\bigoplus_jw_{ij}\ge v_i.
\tag{5.3}
\]
The coefficientwise inequality in (5.1) says that the sum of all allocated edge
conductances is a subnetwork of \(X\). Rayleigh monotonicity therefore gives
\[
  \Lambda_X^T\succeq\Lambda_{\mathrm{alloc}}^T.
\]
For a fixed terminal potential \(x\), shared internal vertices in the allocated union
can only increase the minimum relative to minimizing the internal vertices of every
path independently:
\[
  \min_z\sum_i\mathcal E_i(x,z)
  \ge
  \sum_i\min_{z_i}\mathcal E_i(x,z_i).
\tag{5.4}
\]
The right side equals
\[
  \sum_i c_i(x_{s(\beta_i)}-x_{t(\beta_i)})^2
  \ge
  \sum_i v_i(x_{s(\beta_i)}-x_{t(\beta_i)})^2
  =
  x^{\mathsf T}L_Yx.
\]
This proves (5.2). \(\square\)

This theorem is the exact response-form analogue of KKL's harmonic-sum domination.
It is conditional only on an itinerary-faithful incidence graph; it does not require
a balance assumption.

## 6. Fixed-block comparison and the uniformity gap

Let \(\Lambda_S\) be the exact surface response and let \(\Lambda_X\) be a WAD
response on the same terminal space.

### Proposition 6.1 (fixed-block spectral comparison)

If
\[
  \ker\Lambda_S=\ker\Lambda_X=K,
\tag{6.1}
\]
then there are block-dependent constants \(0<\alpha_B\le\beta_B<\infty\) such that
\[
  \alpha_B\Lambda_X
  \preceq
  \Lambda_S
  \preceq
  \beta_B\Lambda_X.
\tag{6.2}
\]
The optimal constants are the minimum and maximum generalized Rayleigh quotients
\[
  \alpha_B
  =
  \min_{x\in K^\perp\setminus\{0\}}
  \frac{x^{\mathsf T}\Lambda_Sx}{x^{\mathsf T}\Lambda_Xx},
  \qquad
  \beta_B
  =
  \max_{x\in K^\perp\setminus\{0\}}
  \frac{x^{\mathsf T}\Lambda_Sx}{x^{\mathsf T}\Lambda_Xx}.
\tag{6.3}
\]

**Proof.** On the finite-dimensional space \(K^\perp\), both forms are positive
definite. The quotient in (6.3) is continuous on the
\(\Lambda_X\)-unit sphere, which is compact, and is everywhere positive. Its extrema
give (6.2). \(\square\)

Kernel equality is necessary for a two-sided comparison. If
\(x\in\ker\Lambda_X\setminus\ker\Lambda_S\), the upper inequality fails for every
finite \(\beta_B\); the reverse kernel defect destroys the lower inequality.

The uniform BC1 comparison is therefore exactly the additional assertion
\[
  \inf_B\alpha_B>0,
  \qquad
  \sup_B\beta_B<\infty
\tag{6.4}
\]
over all allowed periods, shifts, transition depths, and side records. Finite
dimensionality on each block does not imply (6.4).

## 7. Value is not observable from response alone

KKL Value has the form
\[
  \operatorname{val}(X)
  =
  \sum_a X(a)\,\ell(a)^2,
\tag{7.1}
\]
where \(\ell(a)\) is determined from the Hubbard-tree eigenweights. A terminal
response instead records the endpoint incidence moment
\[
  L_X
  =
  \sum_a X(a)\,b(a)b(a)^{\mathsf T},
  \qquad
  b(a)=e_{s(a)}-e_{t(a)}.
\tag{7.2}
\]

### Theorem 7.1 (Value-response non-observability)

Suppose two distinct global WAD coordinates \(a,b\) are assigned to the same ordered
port pair after compression and
\[
  \ell(a)^2\ne\ell(b)^2.
\tag{7.3}
\]
Then total WAD weight, terminal response, and the fixed unweighted port/ribbon pattern
do not determine KKL Value. The same is true after adjoining any recorded coordinate
that is fixed by the redistribution below; this includes \(S_B^{\rm std}\) when the
two classes are outside its long-corridor support or enter it only through their total
weight.

**Proof.** Fix \(t>0\) and, for \(0<s<t\), set
\[
  X_s=s\,a+(t-s)b.
\]
Every \(X_s\) has the same total weight \(Q=t\), the same support labels and port
pattern, and the same response
\[
  L_{X_s}
  =
  t\,
  (e_A-e_B)(e_A-e_B)^{\mathsf T}.
\tag{7.4}
\]
But
\[
  \operatorname{val}(X_s)
  =
  s\ell(a)^2+(t-s)\ell(b)^2
\tag{7.5}
\]
is nonconstant in \(s\) by (7.3). \(\square\)

This obstruction can occur whenever translation compression merges distinct global
support classes. Merely retaining their unweighted labels in
\(\mathcal P_B\) does not retain how much weight lies on each label. Nor may the
aggregate standard-width coordinate be assumed to recover that distribution without
a separate injectivity or comparison theorem.

### Corollary 7.2 (necessary augmentation)

Before `BC2` can transfer KKL Value contraction, at least one of the following must be
proved:

1. **Value-faithful ports:** no merged response coordinate contains support classes
   with inequivalent Value coefficients;
2. **bounded coefficient distortion:** the coefficients inside each merged class are
   uniformly comparable in the precise inequality needed by the block gauge;
3. **Value moments:** the homogeneous state retains
   \[
     \mathbf V_B
     =
     \left(
       \sum_a X_B(a)\ell_{B,k}(a)^2
     \right)_{k=1}^{m_B}
   \tag{7.6}
   \]
   for every valuation used by an outgoing chart, with \(m_B\) uniformly bounded or
   itself compressed by a proved finite-feature theorem.

The response-only candidate
\[
  \mathscr R_B
  =
  (Q_B/r_B,\Lambda_B/r_B,S_B^{\rm std}/r_B)
\]
is therefore insufficient for the stated BC2 deduction without one of Items 1--3.
A provisional augmented state is
\[
  \mathscr R_B^{\rm val}
  =
  \left(
    Q_B/r_B,\,
    \Lambda_B/r_B,\,
    \mathbf V_B/r_B,\,
    S_B^{\rm std}/r_B
  \right).
\tag{7.7}
\]

## 8. Exact remaining uniform theorem

The surviving analytic form of BC1 is:

### Uniform Future-Closed Port Realization (`OPEN`)

For every complete virtual, neutral, or primitive block, construct electrode surfaces
and incidence ports such that:

1. the port quotient is future closed through every later use in the block;
2. every positive self-access and every pair of Value-inequivalent support classes
   remains observable;
3. KKL restriction itineraries are port paths, so Theorem 5.1 applies;
4. the exact surface and WAD responses have the same componentwise kernel;
5. the generalized eigenvalues in (6.3) satisfy the universal bounds (6.4), with
   declared relative or topology-charged errors;
6. either the number of ports and Value moments is universal, or an additional
   compression theorem controls their normalized complexity;
7. all constructions are compatible with neutral and virtual chart transitions.

This statement, not the existence of a response matrix for one surface, is the real
BC1 bottleneck.

## 9. Adversarial audit

Any proposed realization must survive:

1. **later separation:** two presently merged ports separate after a pullback;
2. **positive self-access:** both ends of a positive horizontal WAD class lie in one
   coarse ideal interval;
3. **kernel mismatch:** a dangling or invisible class gives an extra graph kernel;
4. **spectral degeneration:** fixed port topology but
   \(\alpha_B\to0\) or \(\beta_B\to\infty\);
5. **floating-electrode error:** an intermediate surface gate is allowed arbitrary
   trace data although Schur elimination treated it as an equipotential conductor;
6. **Value redistribution:** weights move between two response-equivalent support
   classes with different \(\ell(a)^2\);
7. **itinerary collapse:** two consecutive restriction segments are identified
   without retaining their intermediate port;
8. **unbounded feature dimension:** translation compression leaves an unbounded
   family of inequivalent outgoing valuations.

Failures 1--3 invalidate the state. Failure 4 invalidates uniform BC1. Failure 6
forces Value-faithful refinement or the moment coordinate (7.6). None is repaired by
increasing a universal additive constant.

## 10. Source lock

The source statements used to motivate the WAD part are in KKL26
`waves-with-Misha.tex`:

- lines 1881--1894: rectangular laminations and their conformal widths;
- lines 1901--1914: WAD definition, norm, finite support, and validity;
- lines 1937--1943: canonical lamination/WAD and its maximality;
- lines 2086--2090: harmonic domination of restricted laminations;
- lines 2099--2108: ordered restriction itineraries;
- lines 2113--2124: WAD domination with harmonic-sum weights.

The KKL Value formula and contraction are in `value1.tex`, lines 6--20 and
103--111. These results apply in KKL's primitively renormalizable, periodically
repelling \(\psi\)-ql setting. They do not prove future-closed port compression or
the uniform spectral bounds (6.4).
