# Response-calibrated block contraction program

## 1. Status and purpose

This note isolates the next analytic theorem needed by the unified MLC program.
It does **not** prove that theorem. It proves only the abstract implication from a
source-realized forward block contraction to the backward recurrence used by MBTT.

The distinction is essential:

- the collar and corridor constructions naturally give **forward upper** estimates;
- the record argument needs **backward lower** amplification;
- individual localization and chart-change maps may be identities;
- therefore contraction can be required only for a complete entropy-clock block after
  those identity steps are grouped with its dynamical step.

## 2. Complete block datum

A complete block \(B:t\to u\) consists of:

1. a predecessor chart \(t\) and successor chart \(u\);
2. homogeneous geometric states
   \[
     x=\mathscr R_{\rm in}\in{\cal C}_t,
     \qquad
     y=\mathscr R_{\rm out}\in{\cal C}_u;
   \]
   after the BC1 observability audit, \(\mathscr R\) includes the normalized outgoing
   Value-moment vector unless the chosen ports are proved Value faithful, and after
   the transfer audit it also includes normalized shear moments unless that branch is
   sectorially regularized;
3. side/error records
   \[
     \sigma_{\rm in}
     =
     (r_{\rm in},\boldsymbol\nu_{\rm in},\omega_{\rm in},\rho_{\rm in},
      \kappa_{\rm in}/r_{\rm in},\mathcal P_{\rm in},
      \mathcal F_{\rm in}),
     \qquad
     \sigma_{\rm out}
     =
     (r_{\rm out},\boldsymbol\nu_{\rm out},\omega_{\rm out},\rho_{\rm out},
      \kappa_{\rm out}/r_{\rm out},\mathcal P_{\rm out},
      \mathcal F_{\rm out}),
   \]
   which are not scaled by the cone action. Here \(\omega\in\mathcal T^*\) is an
   optional explicit nesting word; its finite-alphabet LIFO update is available only
   after a source theorem proves the antirenormalization order;
4. all localization, access projection, response elimination, and chart changes from
   the first regularized checkpoint through the stopping checkpoint;
5. either a closed source-framed return with accumulated positive entropy
   \(E_B\ge E_*>0\), a transient/extinction transition, a certified nonexpanding
   regularization that leaves no residual large family, or a retained finite shear
   state with a proved homogeneous block map;
6. a source-realized forward comparison
   \[
     y\preceq
     \Psi_B(x;\sigma_{\rm in},\sigma_{\rm out})+e_B.
   \tag{2.1}
   \]

The word **complete** forbids deleting a noncontracting chart edge from the error
budget or requiring a pure coordinate change to contract separately. In particular,
\(r_{\rm in}\) and \(r_{\rm out}\) need not agree; their normalization ratio is part of
the side-pair dependence of \(\Psi_B\), and uniformity over all allowed ratios must be
proved rather than assumed.

## 3. Open analytic theorem

### Response-Calibrated Block Contraction Theorem (`OPEN`)

There are universal finite chart types, nontrivial monotone positively homogeneous
gauges
\[
  L_t(\,\cdot\,;\sigma):{\cal C}_t\to[0,\infty),
\]
error gauges \(G_t\), and constants
\[
  E_*>0,\qquad
  0<\mu_*<1,\qquad
  0\le\delta<1-\mu_*,
  \qquad
  C<\infty,\qquad
  D_*<\infty
\]
such that every complete block satisfies one of the following alternatives.
The gauge may depend on the admissible side record \(\sigma\), but is positively
homogeneous only in its geometric argument; all contraction, error, and coercivity
constants are uniform over the allowed side records.

#### Entropy and nonexpansion routing

Every entropy contribution used to establish the strict factor is carried by a
closed repeatable source-framed return, with typed core/WAD incidence and exact
memory-safe compilation. No spectral radius of an unframed open layer is charged.
Every nonexpanding framed residual is routed exhaustively to:

1. transient/nilpotent extinction;
2. pseudo-Siegel or sectorial regularization; or
3. a calibrated finite shear/flag state that participates in a proved strict
   contraction of an augmented complete block.

This clause is the exact open `H2_ENTROPY_DICHOTOMY`; the arithmetic translation
density identity is only one input to its routing and is not evidence for the whole
theorem.

#### Strict-contraction branch

For every admissible pair
\((\sigma_{\rm in},\sigma_{\rm out})\), the realized map in (2.1) obeys
\[
  L_u(
    \Psi_B(z;\sigma_{\rm in},\sigma_{\rm out});
    \sigma_{\rm out}
  )
  \le\mu_*L_t(z;\sigma_{\rm in})
\tag{3.1}
\]
for every admissible state \(z\) and every allowed pair of side records. Its error
obeys the ordered-cone stability implication
\[
  y'\preceq z'+e
  \quad\Longrightarrow\quad
  L_u(y';\sigma_{\rm out})
  \le L_u(z';\sigma_{\rm out})+G_u(e;\sigma_{\rm out}),
\tag{3.2}
\]
and the block error budget
\[
  G_u(e_B;\sigma_{\rm out})
  \le\delta L_u(y;\sigma_{\rm out})+C.
\tag{3.3}
\]

All constants are independent of satellite period, continued-fraction entries,
translation length, raw cell count, transition depth, and the number of elementary
chart changes inside the block.

#### Nonexpanding branch

Transient extinction or pseudo-Siegel/virtual regularization absorbs every residual
family and gives
\[
  L_u(y;\sigma_{\rm out})\le D_*.
\tag{3.4}
\]

A merely finite-dimensional retained shear state does not imply (3.4). It must
instead satisfy the positive-branch contraction in the augmented gauge, or remain
grouped until a later block regularizes it.

The theorem also requires every dynamically admissible cycle of complete block maps to
pass the forward-contraction cycle test of
`entropy_and_cycle_bookkeeping.md`. A cycle test is necessary, not sufficient to
construct the gauges.

## 4. Closed abstract reduction

### Theorem 4.1 (block contraction implies backward amplification)

Assume a complete strict-contraction block satisfies (2.1) and (3.1)--(3.3). Then
\[
  L_t(x;\sigma_{\rm in})
  \ge
  \lambda L_u(y;\sigma_{\rm out})-C',
\qquad
  \lambda=\frac{1-\delta}{\mu_*}>1,
  \qquad
  C'=\frac C{\mu_*}.
\tag{4.1}
\]

**Proof.** Equations (2.1) and (3.2) give
\[
  L_u(y;\sigma_{\rm out})
  \le
  L_u(
    \Psi_B(x;\sigma_{\rm in},\sigma_{\rm out});
    \sigma_{\rm out}
  )
  +G_u(e_B;\sigma_{\rm out}).
\]
Apply (3.1) and (3.3):
\[
  L_u(y;\sigma_{\rm out})
  \le
  \mu_*L_t(x;\sigma_{\rm in})
  +\delta L_u(y;\sigma_{\rm out})+C.
\]
Move the relative-error term to the left and divide by \(\mu_*\). The strict
inequality \(\delta<1-\mu_*\) gives \(\lambda>1\). \(\square\)

### Corollary 4.2 (abstract MBTT closure)

If every complete block satisfies the open theorem, then every endpoint with
\(L_u(y;\sigma_{\rm out})>D_*\) lies in the strict-contraction branch and has a
preceding checkpoint satisfying (4.1). Hence the scalar tower satisfies MBTT, and the
backward record lemma bounds all calibrated potentials.

This corollary is conditional on existence and exhaustion of the complete blocks. It
does not prove the virtual construction, surface/response comparison, entropy charge,
coercivity, or parameter rigidity.

## 5. Analytic proof modules

The open theorem separates into five independently auditable modules.

### `BC1` Surface-to-response realization

Construct future-closed oriented ports and prove a quadratic-form comparison between
surface extremal energy and \(\Lambda_B\) for every terminal potential modulo the
componentwise kernel. No positive WAD self-access may collapse to a same-port loop.
The fixed-finite-port response theorem and the exact conversion of
itinerary-faithful WAD domination to Loewner order are proved in
`bc1_finite_port_response.md`. The remaining content is uniform future-closed port
construction and uniform spectral comparison over all blocks.

### `BC2` Entropy contraction in the same gauge

Transfer KKL Value contraction to the normalized response-density state. Theorem 7.1
of `bc1_finite_port_response.md` proves that
\((Q_B,\Lambda_B,S_B^{\rm std},\mathcal P_B)\) does not determine Value when port
compression merges support classes with different Hubbard-tree coefficients. Thus
BC2 must first prove Value-faithful ports, uniformly comparable coefficients inside
each merged class, or retain the normalized Value-moment vector
\(\mathbf V_B/r_B\). `bc2_value_feature.md` proves the exact row-space criterion and
minimal augmentation rank for a lifted port-Laplacian state. It also proves that one
fixed source-licensed KKL primitive valuation needs at most one new scalar and obeys
the exact affine pullback contraction. What remains is uniform feature transport
across different primitive, neutral, and virtual charts.
`virtual_clone_entropy.md` further proves that exact clone realization with reduced
cross-section dimension at most \(d\), actual first-return depth at most \(N\), and
common delay \(n>N\) gives the universal complete-block factor
\(2^{-1/(2d)}<1\), without a finite template list. This applies to the
translation-clone branch. `corridor_clone_criterion.md` closes its purely
finite-graph part: exact
chain interiors plus a cross-sectional reduced quotient are equivalent to a KKL
clone, and universally bounded endpoint windows can be absorbed into the active
graph. What remains is to derive those edge-by-edge hypotheses, including
multiplicity and absence of hidden critical/WAD branches, from the virtual
finite-horizon dynamics.

`corridor_entropy_shear_dichotomy.md` proves why a clone-only target is not
exhaustive: a nonzero irreducible non-permutation **closed or canonically framed
return endomorphism** of bounded dimension has a uniform graph entropy gap. The
nonexpanding branch includes both transient/nilpotent extinction and recurrent
common-flag shear; it is not exhausted by spectral-radius-one matrices. The
remaining dynamical task is the Virtual Corridor Transfer Trichotomy, including
return closure, nonstationary flag changes, and a pseudo-Siegel or retained-state
treatment of shear. The entropy recurrence must then use the exact
future-discounted error formula. Positive total entropy without that realization,
observability, and charge is insufficient.

### `BC3` Neutral interface and large-shift routing

At a DL25 transition, compare per-cell and orbit-total coordinates only after proving
\[
  r_B\asymp r_m,
  \qquad
  G(\Lambda_B)\asymp Q_{\rm orb}.
\]
The multiplicative comparison \(Q_{\rm cell}\asymp A_m\) is required only for
\(A_m\ge A_*\), after additive interface constants are absorbed; \(A_m<A_*\) belongs
to the bounded normalized regularization branch.
For KKL shift \(p\), either prove density/congestion control uniform in \(p\), route
large \(p\) into a valid neutral/sectorial chart, or introduce a different
acceleration. Longer translation length alone does not dilute the density \(2p\).

### `BC4` Error conversion

Convert
\[
  4S+C_{\rm net}\kappa
\]
and neutral peripheral losses into \(G_u(e_B)\) units. Prove (3.3) using replication,
discounting, telescoping, or a stated combination. A coordinate label match is not a
width comparison.

### `BC5` Block and cycle completeness

List every elementary edge in the block, compose its map in the correct order, and
verify every intermediate state belongs to the next domain. Audit every admissible
block cycle. Pure chart changes are grouped with the dynamical step and are never
credited with entropy.

## 6. Falsification suite

Any proposed proof must survive:

1. an identity localization map followed by a weak positive-entropy step;
2. reciprocal chart changes whose ungrouped two-cycle is the identity;
3. \(r_B\to\infty\) with fixed response densities;
4. \(r_{\rm mark}\to\infty\) but \(r_\parallel=1\);
5. a long serial chain with large branch weights but small effective response;
6. positive WAD mass whose two ends collapse to one terminal;
7. an eliminated terminal that becomes active after a later pullback;
8. fixed total entropy divided among arbitrarily many elementary steps with unit
   errors;
9. alternating primitive, neutral, and virtual blocks with no bound on the number of
   chart changes;
10. locally distinct translated arcs that become one global marked isotopy class.

A failure identifies the missing coordinate or invalid grouping; it is not repaired by
enlarging a universal constant.

## 7. Source boundary

- [KKL26](https://arxiv.org/abs/2606.27272) supplies the WAD/Value engine and
  translation estimates only in its parabolically bounded prime primitive setting.
- [DL25](https://arxiv.org/abs/2509.23031) supplies the neutral transition estimates
  only under its eventually-golden-mean \(\psi^\bullet\)-ql hypotheses and still calls
  for global external input.
- [Dudko 2025](https://arxiv.org/abs/2512.24171) poses the unbounded-satellite and
  virtual-molecule interpolation problems; it does not prove the response realization
  or block contraction above.

Accordingly, `BC1`--`BC5` are proof obligations, not imported consequences.

## 8. Immediate research order

1. Prove `H2_VIRTUAL_CORE_COCYCLE_REALIZATION` for one virtual block: construct the
   exact raw finite-horizon carrier, typed incidence \(B=N^{\mathsf T}\), KKL
   left/right Value roles, endpoint frame, and complete raw WAD incidence. Uniform
   state or module dimension is not part of this first step.
2. Prove the restricted Uniform Counter/Stack-Follower theorem for that raw cocycle.
   Retain every future-relevant labeled nesting word; treat it as LIFO only after an
   exact push/pop and predecessor-recovery theorem. Do not infer a stack from set
   inclusion or encode the word opaquely in one counter.
3. Prove `H2_UNIFORM_CORE_WAD_DIMENSION` independently of the signature count, and
   verify every WAD transport-quotient commuting square as well as fixed-family
   future observability.
4. Prove `H2_MEMORY_SAFE_PUMPING_COMPILATION`: use exact typed checkpoint macros or a
   finite memory congruence before constructing the Markov-complete finite
   automaton. Apply support pumping only at that fixed trace resolution, retaining
   every contextual loop emission in nested order.
5. Prove the Virtual Corridor Transfer Trichotomy: route permutation interiors to
   `FC1`--`FC6` only after the purity/gate clauses hold, cyclic branching to the
   positive-entropy contraction only on a closed source-framed repeatable return, and
   nonexpanding contextual loops to extinction, a pseudo-Siegel block, or a
   calibrated shear state with a proved complete-block contraction. The finite graph
   implications are already proved.
   Any clone branch must realize the hypotheses of the independently proved
   \(t^{-k}\) recurrence; the false printed KKL \(+\lambda^k\) equation remains
   quarantined as a source claim.
6. Extend the fixed-port BC1 core to that block by constructing separated
   future-closed electrodes and bounding the generalized response eigenvalues.
7. Decide the cross-chart Value-observability branch: prove a Value-faithful port
   refinement or retain and transport the minimal Value-moment vector.
8. Compute the exact grouped response/Value map \(\Psi_B\), convert its error to
   outgoing Value units, and test the cycle obstruction.
9. Prove the DL25 common-family bridge and `BC3` at one neutral transition.
10. Only then attempt a uniform mixed-block theorem.

Steps 1--5 are specified in `virtual_core_cocycle_program.md`.

The first decisive deliverable is therefore not a global MLC claim. It is a fully
source-realized block for which (2.1), (3.1), and (3.3) are all proved in one
normalization, or an explicit counterexample identifying the additional state needed.
