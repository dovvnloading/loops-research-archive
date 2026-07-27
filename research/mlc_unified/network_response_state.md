# Bounded-terminal response state

## 1. Purpose and status

The corridor state must represent two incompatible-looking laws:

- parallel families add;
- serial restrictions combine by the harmonic sum.

A fixed positive linear vector cannot do both on unrestricted widths. A
Dirichlet-to-Neumann response matrix does so exactly: parallel gluing is matrix
addition, while elimination of an intermediate terminal is a Schur complement.

This note proves the finite-network algebra and states the analytic surface comparison
that would be needed to use it in the MLC project.

## 2. Finite conductance networks

Let \(G=(V,E)\) be a finite graph with conductances \(c_e>0\). Split the vertices into
a nonempty terminal set \(T\) and interior set \(I\). For a potential
\(u\in\mathbb R^V\), define
\[
  \mathcal E_G(u)
  =
  \sum_{\{v,w\}\in E}c_{\{v,w\}}(u_v-u_w)^2.
\tag{2.1}
\]
Assume every connected component of \(G\) meets \(T\), so the interior Dirichlet
problem is nondegenerate.

Write the graph Laplacian in blocks:
\[
  L=
  \begin{pmatrix}
    L_{TT}&L_{TI}\\
    L_{IT}&L_{II}
  \end{pmatrix}.
\tag{2.2}
\]

### Proposition 2.1 (response matrix)

For prescribed terminal values \(x\in\mathbb R^T\),
\[
  \min_{u|_T=x}\mathcal E_G(u)
  =
  x^{\mathsf T}\Lambda_Gx,
\tag{2.3}
\]
where
\[
  \Lambda_G
  =
  L_{TT}-L_{TI}L_{II}^{-1}L_{IT}.
\tag{2.4}
\]
The matrix \(\Lambda_G\) is symmetric positive semidefinite and annihilates the
constant vector.

**Proof.** For fixed \(x\), the energy is the quadratic form of \(L\). Its derivative
with respect to the interior values \(y\) vanishes exactly when
\[
  L_{II}y=-L_{IT}x.
\]
The hypothesis makes \(L_{II}\) positive definite, so
\(y=-L_{II}^{-1}L_{IT}x\). Substitution gives (2.4). Nonnegativity follows from the
minimized energy, and constant potentials have zero energy. \(\square\)

More precisely,
\[
  \ker\Lambda_G
  =
  \left\{
    x:
    x\text{ is constant on }T\cap C
    \text{ for every connected component }C\text{ of }G
  \right\}.
\tag{2.5}
\]
Indeed, zero minimized energy means that the harmonic extension is constant on each
component. The kernel may therefore be larger than the span of the global constant
vector.

## 3. Exact gluing laws

### Proposition 3.1 (parallel law)

If two networks have the same terminal set and disjoint interiors, and are glued only
along those terminals, then
\[
  \Lambda_{G_1\parallel G_2}
  =
  \Lambda_{G_1}+\Lambda_{G_2}.
\tag{3.1}
\]

**Proof.** For any fixed terminal potential, the two interior minimizations are
independent and their energies add. Equality of the quadratic forms gives (3.1).
\(\square\)

### Proposition 3.2 (terminal elimination)

Partition a response matrix according to retained terminals \(R\) and terminals
\(J\) that become interior:
\[
  \Lambda=
  \begin{pmatrix}
    \Lambda_{RR}&\Lambda_{RJ}\\
    \Lambda_{JR}&\Lambda_{JJ}
  \end{pmatrix}.
\]
If every connected component represented by the response form contains a retained
terminal, then \(\Lambda_{JJ}\) is positive definite and eliminating \(J\) produces
\[
  \Lambda_{\rm eff}
  =
  \Lambda_{RR}
  -
  \Lambda_{RJ}\Lambda_{JJ}^{-1}\Lambda_{JR}.
\tag{3.2}
\]
In general the quotient-safe formula is
\[
  \Lambda_{\rm eff}
  =
  \Lambda_{RR}
  -
  \Lambda_{RJ}\Lambda_{JJ}^{\dagger}\Lambda_{JR},
\tag{3.3}
\]
where \({}^\dagger\) denotes the Moore--Penrose inverse.

**Proof.** This is Proposition 2.1 applied a second time, with the former \(J\)
terminals treated as interior variables. For a positive semidefinite block matrix,
\(\ker\Lambda_{JJ}\subseteq\ker\Lambda_{RJ}\), so the minimized quadratic form is
independent of the representative modulo the kernel and is given by (3.3). In the
positive-definite case the pseudoinverse is the ordinary inverse. \(\square\)

### Corollary 3.3 (harmonic series law)

Two scalar conductances \(x,y>0\) joined in series have effective conductance
\[
  \frac{xy}{x+y}
  =
  \left(x^{-1}+y^{-1}\right)^{-1}.
\tag{3.4}
\]

**Proof.** For endpoint potentials \(0,1\) and intermediate value \(t\), minimize
\[
  xt^2+y(1-t)^2.
\]
The minimizer is \(t=y/(x+y)\), and the minimum is \(xy/(x+y)\). \(\square\)

These network operations obey the same elementary parallel and harmonic formulas that
appear in KKL's WAD calculus. This is not an identification of WAD restriction with
electrical elimination: the source supplies harmonic domination, while response
realization remains an additional theorem.

## 4. What terminal response retains and forgets

If the number \(d=|T|\) of active terminal/access types is universally bounded, then
\(\Lambda_G\) lies in a fixed finite-dimensional cone of symmetric
\(d\times d\) matrices, independent of corridor length. It retains exactly the
minimized quadratic energy seen from those terminals, including cross-couplings and
electrical degeneracies.

It does not recover the internal network, which gates were eliminated, the original
parallel decomposition, or cyclic order. Electrically equivalent networks have the
same response matrix. More seriously, an arc whose two ends are assigned to one
terminal becomes an invisible zero-energy loop, and a dangling positive-weight branch
attached through one terminal is invisible until a later pullback reopens it.

Therefore a safe state must either construct separate incidence ports for every
future-relevant oriented access, prove terminal observability and future-closedness, or
retain scalar WAD density and finite port/ribbon data alongside the response form.

The response matrix does not remove the replication obstruction. Serial chains make
their effective conductance small. An aligned family of \(r\) identical parallel
replicas has response \(r\Lambda\), but eigenvalues of arbitrary response-matrix sums
do not add componentwise. This is precisely the behavior that the congestion
coordinate in `virtual_hull_realization.md` must detect.

## 5. Candidate normalized block state

For a block with \(r_B=r_{\rm mark}\ge1\) marking cells and
\(r_\parallel\ge1\), let \(Q_B\) denote the total retained scalar
canonical-WAD/corridor weight \(Q\) of `corridor_network_calibration.md`, and let
\(S_B^{\rm std}\) denote its aggregate standard corridor width. The scalar \(Q_B\)
is retained as an independent observable: no identity \(Q_B=G(\Lambda_B)\) is assumed.

The homogeneous geometric coordinate is
\[
  \mathscr R_B=
  \left(
    \frac{Q_B}{r_B},\;
    \frac{\Lambda_B}{r_B},\;
    \frac{S_B^{\rm std}}{r_B}
  \right)\in{\cal C}_{t_B}.
\tag{5.1}
\]
The chart side/error data are
\[
  \sigma_B=
  \left(
    r_B,\;
    \rho_B,\;
    \frac{\kappa_B}{r_B},\;
    \mathcal P_B
  \right),
  \qquad
  \rho_B=\frac{r_{\rm mark}}{r_\parallel},
\tag{5.2}
\]
where \(\mathcal P_B\) is finite labeled port/ribbon-order data. If no parallel
replica exists, record \(\rho_B=\infty\) and route the block away from the
replication branch.

Only \(\mathscr R_B\) is scaled by a positively homogeneous chart gauge. The raw cell
count, congestion, normalized topology charge, and discrete port order are parameters
constraining which chart estimates are valid; all comparison constants must be
uniform over the declared admissible class of \(\sigma_B\). In particular, coercivity
must not bound \(r_B\), which is allowed to tend to infinity.

This normalization would match the corrected neutral scale only after proving
\[
  r_B\asymp r_m
  \quad\text{and}\quad
  G(\Lambda_B)\asymp Q_{\rm orb}
\tag{5.3}
\]
for a specified quotient-safe gauge \(G\). Under those open comparisons, the desired
neutral normalization is
\[
  Q_{\rm cell}\asymp A_m,
  \qquad
  Q_{\rm orb}\asymp r_mA_m\asymp K_F.
\]

The independent scalar \(Q_B/r_B\) and port data remain because invisible self-access
mass and cyclic order cannot be recovered from \(\Lambda_B/r_B\) alone. Raw \(r_B\)
remains audit/multiplicity metadata, not a coercive cone coordinate.

### Value-observability correction

`bc1_finite_port_response.md`, Theorem 7.1, proves that
\[
  (Q_B,\Lambda_B,\mathcal P_B)
\]
does not determine KKL Value if two distinct global WAD coordinates with different
Hubbard-tree coefficients are compressed to the same port pair. Redistributing weight
between those coordinates leaves \(Q_B\), \(\Lambda_B\), and the unweighted port
pattern fixed while changing Value. The same counterexample keeps
\(S_B^{\rm std}\) fixed when the two classes are outside its long-corridor support or
enter it only through their total. No source theorem says that aggregate standard
width otherwise recovers the lost distribution.

Accordingly, either the port quotient must be proved **Value faithful**, or the
homogeneous state must be provisionally enlarged to
\[
  \mathscr R_B^{\rm val}
  =
  \left(
    \frac{Q_B}{r_B},\;
    \frac{\Lambda_B}{r_B},\;
    \frac{\mathbf V_B}{r_B},\;
    \frac{S_B^{\rm std}}{r_B}
  \right),
\tag{5.4}
\]
where \(\mathbf V_B\) contains every inequivalent outgoing Value moment. A uniform
bound on the dimension of \(\mathbf V_B\), or a finite-feature compression theorem,
is an additional open obligation. The three-coordinate state (5.1) remains valid for
response algebra but is not by itself a complete positive-entropy state.

The later transfer audit adds one more conditional augmentation. If reducible
unit-spectral-radius corridor transport is not removed by sectorial regularization,
let \(\mathbf\Xi_B\) be its retained nilpotent shear moments and set
\[
  \mathscr R_B^{\rm aug}
  =
  \left(\mathscr R_B^{\rm val},\frac{\mathbf\Xi_B}{r_B}\right).
\tag{5.5}
\]
The discrete side state then also records its Frobenius flag \(\mathcal F_B\). Neither
the dimension nor the transport law of \(\mathbf\Xi_B\) is proved here.

## 6. Analytic response-realization theorem

### Surface/network comparison (`OPEN`)

For every realized virtual or neutral marked surface, construct a labeled,
future-closed port set and response matrix \(\Lambda_B\) such that:

1. the number of ports is universal after translation compression, no positive
   future-relevant WAD class is collapsed to a same-port loop, and eliminated ports
   never reappear without their data being retained;
2. for every terminal potential modulo the componentwise kernel, surface extremal
   energy and terminal quadratic energy have a quantified comparison, with the
   multiplicative, additive \(O(\kappa)\), or relative error stated explicitly;
3. KKL itinerary domination is represented by the same terminal eliminations as the
   Schur complements in (3.2)--(3.3), up to the declared amortized error;
4. the geometric hypotheses implying that distinct parallel WAD support produces
   independent parallel subnetworks are proved; WAD support disjointness alone is not
   assumed to imply surface-energy additivity;
5. access projection between KKL and DL25 charts has bounded quasiconformal
   distortion, lift multiplicity, and terminal congestion;
6. cyclic order, orientation, and finite port data used by every later restriction are
   preserved;
7. every outgoing KKL valuation is observable either from a Value-faithful port
   refinement or from the retained moment vector \(\mathbf V_B\);
8. the topology/marking and standard-width charges are controlled by the geometric
   density coordinates \(\mathscr R_B^{\rm aug}\) and the admissible side data
   \(\sigma_B\) of (5.2);
9. a quotient-safe scalar gauge of the full state, or a family passing the chart-cycle
   audit, either strictly contracts every complete forward upper entropy-clock block
   (after identity chart/localization steps are grouped with its dynamical step) with
   uniform error margin, or expands an independently proved backward lower transition,
   as required by Lemma 5.4 or Lemmas 5.1--5.3 of `master_transition.md`.
10. every analytic neck eliminated as a scalar node is either proved to have a
    constant admissible trace class or has its complete possibly multi-port
    boundary-trace response controlled in the declared norm.  The constant-mode
    two-terminal conductance is not sufficient:
    `SCALAR_NECK_TRACE_MODE_NO_GO` gives an exact cylinder counterexample.
    `FULL_TRACE_RECTANGLE_DTN` and
    `TRACE_RENORMALIZED_NECK_ESTIMATE` solve the operator problem for a genuine
    rectangle, but `PULLED_EQUIPOTENTIAL_SERIAL_RECTANGLE_NO_GO` proves that a
    full parent equipotential arc and its dynamically pulled child do not form
    such a serial rectangle.  The actual unequal-footprint interface remains
    open in `DIRECT_DECORATION_TRACE_COLLAR_REALIZATION`.

No cited source proves this comparison for arbitrary virtual blocks. It is a candidate
replacement invariant, not a completed transition theorem.

## 7. Falsification tests

The bounded-terminal response state fails if:

- the number of dynamically essential access types is unbounded after translation
  compression;
- surface extremal energy cannot be compared uniformly with any bounded-terminal
  network because of uncontrolled thick pieces;
- chart projection has unbounded degree or changes a parallel family into a serial
  one;
- positive self-access or dangling WAD mass is invisible at the chosen ports;
- an eliminated port becomes active under a later pullback;
- response-equivalent support classes have different KKL Value coefficients and their
  weights are not separately retained;
- a cut cross-section is treated as one floating scalar although its nonconstant
  \(H^{1/2}\) traces carry unsummed Dirichlet energy;
- a parent and child trace are identified as one complete interface even though
  inverse pullback changes their angular footprints;
- a strict trace margin is invoked without proving that accumulated physical
  resistance crosses the required threshold;
- electrically equivalent states with different cyclic order have different later
  restrictions;
- the response comparison gives only a forward upper map with no strictly contracting
  gauge;
- every natural scalar gauge is neutral on an admissible chart cycle.

Such a failure would identify the additional coordinate required: terminal growth,
thick-piece conformal data, scalar hidden mass, a cross-section trace-response
operator, Value moments, future port history, ribbon order, projection
congestion/orientation, or a genuinely non-scalar cycle state.
