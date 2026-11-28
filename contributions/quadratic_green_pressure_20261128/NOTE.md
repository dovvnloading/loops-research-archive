---
ledger: MLC
result: partial
ai: ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-green-pressure-20261128"></a>

# Quadratic Jacobian partitions, Green flatness, and a density obstruction

Ledger statement being addressed:

> The Mandelbrot set is locally connected.

## Claim

This packet studies the actual quadratic family
`f_c(z)=z^2+c`, its critical-value orbit
`P_n(c)=f_c^n(c)`, and the existing parameter Green potential
`G(c)=lim_n 2^(-n) log(max(1,|P_n(c)|))`.
Write `M={c:G(c)=0}`; the imported Lean theorem identifies this set
with the bounded critical-orbit locus.

**Validation status at this working revision:** the first CI build checked the
initial source and found two tactic/elaboration errors in the partition and
shadowing proofs. This revision repairs both and adds the consequences below.
The full build and transitive audit are pending. Mathematical statements in
this note are not claimed as kernel-validated until those checks pass.

### A. A finite partition certificate for actual Green sublevel disks

For a regularizer `epsilon>=0`, define

    S_0(c,epsilon)=1,
    S_(n+1)(c,epsilon)=(2|P_n(c)|+epsilon) S_n(c,epsilon)+1.

The factor `2|P_n(c)|` is the actual one-step complex derivative norm.
The exact expansion is

    S_n(c,epsilon)
      = sum_(j=0)^n product_(k=j)^(n-1) (2|P_k(c)|+epsilon).

Thus this is a finite renewal partition for the regularized geometric
Jacobian. It is not an asserted identification with stationary topological
pressure or an equilibrium measure.

For every `c in M`, every complex parameter `d`, every `epsilon>=0`,
and every horizon `n`, put `delta=|d-c|`. The criterion is

    delta S_j(c,epsilon) <= epsilon for every 0<=j<=n
      implies
    G(d) <= 2^(-n) [log(2+epsilon)+log(3+epsilon)].

All hypotheses concern the actual polynomial orbit. There is no fiber metric,
sampling rule, selected branch geometry, critical-encounter counting, or
geometric-limit assumption. A Green value larger than the displayed threshold
forces failure of at least one of the explicitly stated partition inequalities.

### B. Interior and boundary consequences; a genuine threshold distinction

If `epsilon>0` and `S_n(c,epsilon)<=B` for every `n`, then the entire
parameter disk

    |d-c| B <= epsilon

lies in `M`. Hence `c` is interior to `M`. At every `c in M` that is
not interior, the partitions are unbounded for every fixed positive
regularizer. This is an actual-family boundary obstruction.

Bounded response cannot be replaced by arbitrarily slow exponential growth.
Define `SlowRegularizedGrowth c` by the exact quantifier order

    for every A>1, there exist epsilon>0 and K>=1 such that
    S_n(c,epsilon)<=K A^n for every n.

The regularizer and prefactor may depend on `A`. The actual parameter
`c=1/4` satisfies this property and belongs to the frontier of `M`.
The module proves both assertions directly. Therefore slow regularized
growth does not force interiority.

### C. Conditional Green flatness from partition growth

Suppose `G(c)=0`, `epsilon>0`, `K>=1`, `A>1`, and
`S_n(c,epsilon)<=K A^n` for all `n`. For every positive integer `m`
such that `A^m<=2`, and every `d` with `|d-c|K<=epsilon`,

    G(d) <= 2[log(2+epsilon)+log(3+epsilon)]
               (|d-c|K/epsilon)^m.

The number two here is the actual quadratic degree. The competition is
between the growth of the orbit-dependent partition and the degree
normalization of the Green potential.

In particular, `SlowRegularizedGrowth c` at a zero-potential parameter
implies: for every natural `k`, there are positive `C,r` such that

    |d-c|<=r  implies  G(d)<=C |d-c|^(k+1).

This is a pointwise all-orders upper estimate, not a smoothness assertion.
At `c=-2`, the actual orbit gives `S_n(-2,epsilon)>=4^n`, so slow
regularized growth fails.

The actual cusp supplies a stronger concrete calibration:

    |d-1/4| <= 1/[4(n+1)^2]
      implies
    G(d) <= 2^(-n) log(3/2)

for every complex `d` and every `n>=0`. Cusp flatness and its general
scaling are prior mathematics; this all-horizon Lean certificate is a test
of the new partition framework, not the main originality claim.

### D. A separate obstruction to uniform normalized-density coercivity

Let `V_n(c)=P_n'(c)`, proved from the actual parameter derivative, and set

    rho_n(c)=2^(-n)|V_n(c)|^2/(1+|P_n(c)|^2)^2.

For every `c in M` and every `n`,

    rho_n(c)+rho_(n+1)(c) >= 2^(-n)/450.

The exponential rate is optimal uniformly on `M`: at the actual parameter
zero the sum equals `(3/2)2^(-n)`. Hence there is no positive
level-independent floor, and no floor `C r^n` with `C>0`, `r>1/2`
uniform in `c,n`. The constant 450 is not claimed optimal.

This is explicitly a statement about squared spherical parameter derivatives.
The module does not assume or formalize their Laplacian interpretation.
The classical Euclidean identity for
`U_n=2^(-n-1)log(1+|P_n|^2)` is `Delta U_n=2 rho_n`; it is context,
not an additional counted Lean theorem.

## Evidence

### Exact archive gap

The base is main at `6a10209b3cc51878bc45de7668894757b2575e08`.

The proved ledger row `CONDITIONAL_REDUCTION` says:

    YOCCOZ + H1_MARKED_CONSTRUCTION + MBTT + H3_COERCIVITY + H4_RIGIDITY
      imply MLC.

All four displayed program hypotheses remain open. Their combined global
form is `UNIVERSAL_PROTECTED_TOWER_CLOSURE`, the six-clause Universal
Protected-Tower Compactness and Rigidity package, required for every
infinitely renormalizable quadratic polynomial:

1. canonical protected carriers;
2. exact analytic realization;
3. a uniformly finite Value-observable response state;
4. a universal backward transition;
5. coercive marked compactness;
6. tower rigidity with singleton parameter fiber and connected relative
   parameter neighborhoods.

The precise sources are `ledger.json`,
`research/mlc_unified/master_transition.md` sections 6--8, and
`research/mlc_unified/mlc_closure_proposition.md` section 5. H4 alone
is not the missing hypothesis. This packet does not try to complete those
constructions.

### Proof of the finite certificate

1. The recurrence for the partition unfolds by induction to the suffix
   product formula, with the empty suffix contributing one.
2. Write `e_j=|P_j(d)-P_j(c)|`. The exact quadratic identity and the
   triangle inequality give

       e_(j+1) <= (2|P_j(c)|+e_j)e_j+delta.

   Induction using `e_j<=delta S_j<=epsilon` gives
   `e_(j+1)<=(2|P_j(c)|+epsilon)delta S_j+delta
   =delta S_(j+1)`. No linearization error is discarded.
3. The archive's proved radius-two bound on actual bounded orbits gives
   `|c|<=2`, `|P_n(c)|<=2`. The j=0 condition gives
   `delta<=epsilon`, so `|d|,|P_n(d)|<=2+epsilon`.
4. The previously constructed escape potential satisfies

       |2^(-n)log(max(1,|P_n(d)|))-G(d)|
         <=2^(-n)log(1+|d|).

   Substitute the two preceding bounds. This proves A.
5. If the partition bound holds for every time, the same shadowing estimate
   bounds every actual `P_n(d)` by `2+epsilon`. The proved
   bounded-orbit equivalence gives `G(d)=0`. A positive radius then proves
   the interior statement and its boundary contrapositive.

### Proof of the power and cusp statements

For C, let `t=delta K/epsilon`. When `0<t<=1`, choose the last integer
scale with

    A^n t<=1<A^(n+1)t.

Every earlier partition satisfies the finite criterion. Raising the right
inequality to `m` and using `A^m<=2` gives
`1<2^(n+1)t^m`, hence `2^(-n)<2t^m`. This proves the displayed
constant without relaxing the growth base. The case `d=c` is separate.

For all orders, take `A=exp(log(2)/(k+1))`. The hypotheses supply
`epsilon,K`; use radius `epsilon/K` and constant
`2[log(2+epsilon)+log(3+epsilon)](K/epsilon)^(k+1)`.

At the cusp, a real induction proves `0<=P_j(1/4)<=1/2`. For fixed
`n`, choose `epsilon=1/[2(n+1)]`. Then
`S_j<=2(j+1)` for every `j<=n`. The stated parameter disk therefore
satisfies all the finite inequalities, and `|P_n(d)|<=1`. Its finite
escape approximant is exactly zero; also `|d|<=1/2`. The escape error
gives the constant `log(3/2)`.

For each `A>1`, choosing `epsilon=(A-1)/2` and
`K=max(1,1/epsilon)` proves the cusp's slow-growth property. To verify
that this is an actual boundary witness, the proof shows that for every
real `h>0` the critical-value orbit at `1/4+h` grows at least by `h`
per step, since

    x^2+1/4+h-x=(x-1/2)^2+h.

It crosses the proved escape radius. Such parameters occur in every
neighborhood of `1/4`, while the cusp itself has zero escape.

### Proof of the density obstruction

Differentiating the actual recurrence gives `V_(n+1)=2P_n V_n+1`.
In particular two successive tangents cannot both vanish. Also
`P_(n+1)-P_n^2=c`, so the pair of consecutive orbit observations
recovers the actual parameter.

Put `q=P_n(c)`, `v=V_n(c)`, `u=2qv+1`. For `c in M`,
`|q|<=2`, and `1<=|u|+4|v|`. Squaring and using
`2(|v|-2|u|)^2>=0` yields

    1<=18|v|^2+9|u|^2.

Both spherical denominators are at most 25. The adjacent normalization is
`2^(-n-1)=2^(-n)/2`; multiplication yields the constant 450.
At zero, `P_n=0` and `V_n=1` for all `n`, proving the exact decay
and both impossibility results. This counterexample is on `M), not a
claim of the same optimality restricted to its boundary.

### Lean modules and validation

| Module | Main declarations |
|---|---|
| `QuadraticGreenPressure.lean` | `regularizedResponse_partition`, `regularizedResponse_shadowing`, `regularizedResponse_green`, `bounded_regularizedResponse_zero_disk`, `bounded_regularizedResponse_interior`, `boundary_regularizedResponse_unbounded` |
| `QuadraticGreenPower.lean` | `regularizedResponse_natural_power`, `slowRegularizedGrowth_power_bound`, `chebyshev_not_slowRegularizedGrowth` |
| `QuadraticGreenCusp.lean` | `cusp_green_disk`, `cusp_slowRegularizedGrowth`, `cusp_green_all_orders`, `cusp_mem_frontier_zero`, `slow_growth_does_not_force_interior` |
| `QuadraticGreenDensity.lean` | `criticalValue_hasDerivAt`, `sphericalDensity_pair_lower`, `sphericalDensity_pair_zero`, `no_uniform_positive_density_floor`, `no_slower_geometric_density_floor` |

All are in `formalization/weighted/`, registered as default targets, with
every public theorem listed in the existing theorem index. No existing
mathematical source or workflow is changed.

Reproduce with the pinned Lean 4.32.0 and locked mathlib revision:

    python code/contribute.py check
    python code/verify_lean_coverage.py
    cd formalization/weighted
    lake exe cache get
    lake build
    cd ../..
    python code/verify_lean_coverage.py --audit weighted

The local command runner is unavailable, so no local build is claimed.
The unchanged weighted workflow compiles the full project and audits
every transitive dependency against its existing foundational allowlist:
`propext`, `Classical.choice`, and `Quot.sound`.

## Dependencies

The formal proofs use only the actual-family modules `QuadraticEscape`
and `QuadraticExtremalMultiplier`, the new modules in this packet, and
mathlib algebra, calculus, finite products, real logarithms, topology and
geometric limits. None of H1--H4, MBTT, or UPTCR is a premise of these
theorems.

The prior-work audit is material:

- `contributions/sharp_escape_exponents_20261126/NOTE.md` already
  establishes stronger-than-half one-sided boundary exponents away from
  minus two and the sharp square-root endpoint. This packet changes the
  observable to a nonstationary regularized partition; it does not claim
  that Green regularity itself is new.
- `research/independent_audits/adversarial_proof_frontier_20261126/`
  already has written cusp asymptotics and disk estimates, especially
  `CUSP_KERNEL.md`, `CUSP_RATE.md`, and `CUSP_HARMONIC_RATE.md`.
  The new cusp Lean statements are a formal calibration, not a priority claim.
- S. Zakeri, *External rays and the real slice of the Mandelbrot set*
  ([primary preprint](https://arxiv.org/pdf/math/0210382)), Theorems 1.1--1.2,
  proves harmonic nullity of the real slice together with Hausdorff dimension
  one of its landing-angle set. Pages 1--2 also record harmonic nullity of
  hyperbolic-component boundary arcs and Beurling's capacity-zero exceptional
  set for nonlanding rays. Thus harmonic nullity and positive continuum
  capacity alone do not furnish the requested fiber contradiction.
- S. Smirnov, *Symbolic Dynamics and Collet-Eckmann Conditions*, IMRN 2000,
  no. 7, 333--351, especially Theorem 4
  ([primary text](https://www.unige.ch/~smirnov/papers/symbolic-j.pdf)),
  supplies the stronger dimension-zero exceptional-angle context.
- Classical spherical-derivative and bifurcation-current technology is
  background, not a new claim of this packet. None of the external
  complex-dynamical theorems is imported as an assumption into the proofs.

## Boundary

These results provide a potential-theoretic criterion and explicit
thermodynamic obstructions on the actual quadratic family. They do not
prove MLC, triviality of a parameter fiber, landing of external rays,
shrinking of prime-end impressions, or a new infinitely renormalizable
MLC case. No ledger status change is requested.

The remaining research issue is substantive: obtain useful partition-growth
bounds for the unresolved infinitely renormalizable parameters and relate
such bounds to a lower or angular-access estimate that can distinguish a
nontrivial common fiber. Upper Green flatness alone cannot do this. This
packet has not constructed that missing connection. The density floor
also tends to zero, and its optimality witness is an interior parameter;
no boundary-only density theorem is inferred.

The proposed new statements in this archive are the precise regularized
partition certificate, its actual-family interior/boundary and flatness
consequences, and the calibrated two-observation density estimate.
Targeted archive and primary-literature searches found no exact statement
of this combined criterion. They do not establish worldwide novelty or
that no one has previously considered related majorant or thermodynamic
arguments. Classical ingredients and the known cusp behavior are credited
explicitly. This limitation must not be concealed by the Lean validation:
the kernel checks proofs, not originality.

## Attribution

Builds on the archive's actual escape-potential and radius-two formalization.
The finite nonlinear comparison is a direct quadratic majorant argument;
the geometric partition interpretation and the precise consequences are
developed here. Independent AI review checked the proof architecture and
identified tactic errors before the second CI attempt. No human specialist
has reviewed the mathematics. All work is released under the repository's
CC0 terms.
