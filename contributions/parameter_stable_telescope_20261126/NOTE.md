---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="parameter-stable-telescope-20261126"></a>

# Parameter-stable quadratic collars, analytic inverse families, and exact component transport

## Claim

**Verified: 20 named public Lean theorems in four modules.** All 23 workflows
passed at the proof checkpoint below, including the full Lean build and
transitive axiom audit.

This contribution extends the archive's fixed-parameter compact-core construction
to a neighborhood of the actual quadratic parameter. All mathematical results
listed below are stated as Lean theorems in the existing Mathlib project.
The final validation section records the checked proof checkpoint.

Write `F_c^n(z)` for the n-fold iterate of `z ↦ z²+c`, using
`QuadraticEscape.orbit`. Fix a finite time n, a compact set C in the complex
plane, and an open ambient set W containing C. Assume only:

1. F_c^n is injective on C.
2. F_c^j(z) is nonzero for every z in C and every j < n.

The terminal time is deliberately excluded. The compact set may be disconnected
or empty, and n may be zero.

The new theorems construct a common open parameter neighborhood P containing c
and a common open phase collar U containing C, with compact closure inside W.
Every nearby actual iterate F_d^n is injective and critical-free on the entire
closure of U, and one positive constant δ gives

```text
δ ‖z-w‖ ≤ ‖F_d^n(z)-F_d^n(w)‖
```

for every d in P and z,w in closure U. Thus parameter stability and a uniform
inverse-distance bound are conclusions, not input assumptions.

A second construction gives an open target collar V containing F_c^n(C) and a
single inverse g(d,y), jointly complex analytic on P×V. It maps V into U,
inverts the actual F_d^n, has spatial derivative
`1 / deriv(F_d^n)(g(d,y))`, and is conformal in y. At the base parameter,
`g(c,F_c^n(C)) = C` exactly.

For every compact connected K contained in that common V, and every y in K,

```text
g(d,K) = connectedComponentIn ((F_d^n)⁻¹(K)) (g(d,y)).
```

This is the whole physical pullback component through the moving anchor,
not merely an injective subset. No local connectivity, path connectivity,
Jordan boundary, or simple connectivity is assumed.

Finally, after restricting the parameter neighborhood to a disk, the actual lift

```text
h(d,z) = g(d,F_c^n(z))
```

is a normalized finite-time holomorphic motion of C: h(c,z)=z, every h(d,·)
is injective on C, and F_d^n(h(d,z))=F_c^n(z). Each h(d,z) is the unique
solution in U. When C is connected and nonempty, h(d,C) is exactly the full
component over the fixed terminal compact F_c^n(C).

## Evidence

### 1. Parameter-stable compact univalence

[QuadraticParameterUnivalence.lean](../../formalization/weighted/QuadraticParameterUnivalence.lean)
defines the polynomial divided difference recursively:

```text
D_0(c,x,y) = 1
D_(j+1)(c,x,y) = (F_c^j(x)+F_c^j(y)) D_j(c,x,y).
```

The six public theorems are:

- `orbit_sub_eq_mul_dividedDifference`: exact identity
  F_c^n(x)-F_c^n(y)=(x-y)D_n(c,x,y).
- `orbitDividedDifference_diagonal_ne_zero`: no preterminal critical
  encounter implies D_n(c,x,x) is nonzero.
- `orbitDividedDifference_ne_zero`: compact-core injectivity handles
  distinct x,y; the preceding diagonal theorem handles x=y.
- `orbitDividedDifference_continuous`: joint continuity in c,x,y.
- `quadratic_parameter_univalent_neighborhood`: compactness gives a
  positive lower bound on C×C, and two tube-lemma applications extend it
  to a common parameter neighborhood and a common phase neighborhood.
- `quadratic_parameter_univalent_neighborhood_within`: shrink the phase
  neighborhood to have compact closure in W. Uniform injectivity,
  critical avoidance, and the lower difference estimate hold on this
  entire closure.

This uses the exact actual orbit. No abstract itinerary is substituted for it.

### 2. Jointly analytic inverses and exact moving components

[QuadraticParameterInverse.lean](../../formalization/weighted/QuadraticParameterInverse.lean)
uses the skew map `(d,z) ↦ (d,F_d^n(z))`.

- `quadratic_skew_analytic` proves joint complex analyticity.
- `quadratic_skew_locally_invertible` constructs an invertible joint
  derivative from preterminal critical avoidance. For one step the
  derivative is the triangular map (u,v) ↦ (u,u+2zv). Only the spatial
  factor needs to be nonzero.
- `quadratic_skew_univalent_inverse` proves that an open injective
  restriction has an open image and a jointly analytic selected inverse.
  The global selection agrees locally with the analytic inverse-function
  theorem by uniqueness.
- `quadratic_compact_parameter_inverse_family` uses compactness of
  F_c^n(C) and the tube lemma to obtain a product P×V inside that open
  skew image. The resulting inverse retains the actual parameter,
  recovers the original compact core exactly, and has the stated
  reciprocal spatial derivative and conformality.
- `quadratic_inverse_compact_component` proves exact global component
  recognition for any continuous inverse over a compact connected target.
  The image g(K) is compact and therefore closed. The left and right
  inverse identities make it relatively open in the full preimage,
  because it is exactly the part lying in U. Connectedness prevents the
  component through g(y) from escaping it.
- `quadratic_inverse_family_compact_component` applies this recognition
  to every compact connected subtarget of the common analytic collar.
  The anchor is g(d,y), and therefore moves with d.

### 3. Quantitative inverse perturbation

[QuadraticParameterDistortion.lean](../../formalization/weighted/QuadraticParameterDistortion.lean)
adds explicit finite recurrences. If parameters have norm at most A and
the starting phase has norm at most R, set

```text
R_0 = R,       R_(j+1) = R_j²+A,
S_0 = 0,       S_(j+1) = 2 R_j S_j+1.
```

Theorems `orbitRadius_nonneg`, `parameterSensitivity_nonneg`,
`orbit_norm_le_radius`, and `orbit_parameter_distortion` prove

```text
‖F_d^n(z)‖ ≤ R_n,
‖F_d^n(z)-F_e^n(z)‖ ≤ S_n ‖d-e‖.
```

Theorem `orbit_inverse_joint_bound` combines this with the spatial
lower difference estimate. For the selected inverses on one common U,

```text
δ ‖g_d(y)-g_e(v)‖ ≤ ‖y-v‖+S_n ‖d-e‖.
```

Here each target may lie in its own actual image F_d^n(U) or F_e^n(U).
The theorem does not presume those images are identical.
`quadratic_compact_inverse_uniform_bound` constructs one common local
δ>0 and S≥0 from the compact-core assumptions, while retaining compact
source closure and the prescribed ambient containment. This quantitative
existence theorem and the joint analytic collar theorem are separate
formal statements; no unproved identification of independently chosen
collars is used.

### 4. Finite-time holomorphic motion

[QuadraticParameterMotion.lean](../../formalization/weighted/QuadraticParameterMotion.lean)
contains:

- `quadratic_compact_finite_time_motion`: restrict to an actual parameter
  disk, lift the fixed terminal image through g, and prove joint
  analyticity, normalization, injectivity, the finite-time identity,
  unique lifting inside U, and analytic parameter slices.
- `quadratic_compact_motion_component`: for a connected nonempty C,
  identify every transported core with the complete global pullback
  component of F_c^n(C) through the transported anchor.

The second theorem uses the compact-component recognition theorem above.
Connectedness is an explicit additional hypothesis for that conclusion.

### Validation

Validation is performed by the repository's existing CI, using the pinned
Lean 4.32.0 and pinned Mathlib revision. Local compilation was unavailable
after workspace disk exhaustion during toolchain installation; no local
compilation result is claimed. The development and every repair are
committed to [PR #219](https://github.com/dovvnloading/loops-research-archive/pull/219).

All four modules are default Lake targets and all public theorem names are
registered in the existing source and theorem indexes under the CONSTRUCT
route. The CI runs the complete weighted build and transitive declaration
audit, plus the root/standalone and repository consistency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted
foundational dependencies. No proof placeholders, new axioms, native
evaluation, unsafe declarations, or implementation overrides are introduced.
No workflow, toolchain, dependency pin, validator, or status ledger is changed.

#### Verified CI evidence

At proof checkpoint [`bf7cde4`](https://github.com/dovvnloading/loops-research-archive/commit/bf7cde4ea601dec9be28eaefb242bb02916dbaad):

- [Weighted full build and transitive axiom audit](https://github.com/dovvnloading/loops-research-archive/actions/runs/45902899455/job/140192691309): all 8,884 build jobs completed; 107 weighted modules and 2,714 declarations passed.
- [Root build and root/standalone audits](https://github.com/dovvnloading/loops-research-archive/actions/runs/45902899474/job/140192691891): 38 root modules and 1,625 declarations passed, together with all five standalone modules.
- [Repository research audit](https://github.com/dovvnloading/loops-research-archive/actions/runs/45902899474/job/140192691505), [contribution intake](https://github.com/dovvnloading/loops-research-archive/actions/runs/45902899603), and [model-to-geometry coverage](https://github.com/dovvnloading/loops-research-archive/actions/runs/45902899325) passed.
- All 23 workflow runs associated with this proof checkpoint concluded successfully.

The weighted log records:

```text
Build completed successfully (8884 jobs).
AXIOM_AUDIT weighted QuadraticParameterDistortion: 23 declarations, 13 theorems; allowed axioms only
AXIOM_AUDIT weighted QuadraticParameterInverse: 30 declarations, 27 theorems; allowed axioms only
AXIOM_AUDIT weighted QuadraticParameterMotion: 2 declarations, 2 theorems; allowed axioms only
AXIOM_AUDIT weighted QuadraticParameterUnivalence: 16 declarations, 11 theorems; allowed axioms only
AXIOM_AUDIT_PASS weighted: 107 modules, 2714 declarations
```

The audit counts include private and compiler-generated declarations; the
source/theorem registry lists all 20 explicitly named public theorems.
The inverse module uses an elaboration-only transparency setting to reconcile
product-space instance paths. It does not alter kernel checking or the
allowed axiom set. The final documentation changes affect no Lean source
or registration from the verified proof checkpoint.

Reproduction in a workspace with the pinned dependencies:

```sh
cd formalization/weighted
lake exe cache get
lake build QuadraticParameterUnivalence QuadraticParameterInverse QuadraticParameterDistortion QuadraticParameterMotion
lake build
cd ../..
python code/verify_lean_coverage.py --audit weighted
python code/contribute.py check
```

## Dependencies

Research target: MAPPING_TELESCOPE. Its ledger prerequisites
PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER, RELATIVE_COVER_LIFT, and
STAGE_FORWARD_CLOSURE describe the research program; their documentary
statuses are not used as Lean proof premises.

Formal inputs are QuadraticEscape's actual complex orbit and joint
continuity; SaturatedTelescope's actual orbit facts; TelescopeRamification's
critical-encounter and analytic-orbit theorems; the earlier compact
univalent-neighborhood and collar results; and TelescopeConformalInverse's
derivative criterion. The pinned Mathlib supplies compactness, the tube
lemma, complex analytic calculus, the inverse-function theorem, and
connected-component topology. All mathematical dependencies are traversed
by the existing kernel audit.

## Boundary

This is finite-time, parameter-local progress for actual quadratic maps,
conditional on the explicitly supplied compact injective critical-free
core. P, U, V, δ, and S depend on c, n, the compact core, and the chosen
ambient neighborhood. No uniform radius over all periods, all native
blocks, or an infinite tower is claimed.

The exact moving component theorem concerns compact connected subtargets
inside the constructed common V. It does not identify every native
marked/deck-phase choice, preserve a global source-defined route, or prove
compatible cyclic Jordan cores. It does not construct or stabilize the
complete one-critical degree-two return: that additionally requires
retaining the moving critical value and trapping the whole critical
pullback inside the prefix target.

The motion preserves the specified terminal image. It is not asserted to
conjugate the one-step dynamics, preserve Julia-set membership, or be
compatible over all iterate lengths.

Therefore MAPPING_TELESCOPE, H1–H4, UPTCR, and MLC retain their existing
open statuses. No ledger status change is requested. This advances the
repository's formal construction; no priority claim over classical
complex analysis or existing literature is made.

## Attribution

Extends the [univalent telescope collars contribution](../univalent_telescope_collars_20261126/NOTE.md),
whose boundary explicitly left parameter-uniform collar radii and analytic
bounds open. It also builds on the
[saturated telescope contribution](../saturated_telescope_20261126/NOTE.md),
[ramification and proper-collar contribution](../telescope_ramification_order_20261126/NOTE.md),
and [written cyclic pullback audit](../../research/independent_audits/h1_mapping_telescope_20261126/NOTE.md).
The source-facing residual is
[critical chronology, section 15.3](../../research/mlc_unified/critical_chronology_and_retimed_telescope.md#153-relative-cover-and-marked-telescope).

Classical compact separation and analytic inverse-function arguments are
formalized through Mathlib rather than introduced as assumptions.
Proof development, integration, and independent source-level mathematical
review are AI-assisted. No independent human review has occurred.
