---
ledger: H4_RIGIDITY
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

<a id="center-multiplier-coordinate-20261126"></a>

# Actual multiplier disks, exact ramification, and zero-escape neighborhoods

Ledger statement being addressed:

> Controlled marked towers yield connected relative parameter neighborhoods forming a basis at the parameter with diameters tending to zero, either directly or through a precisely applicable trivial-fiber theorem.

## Claim

This contribution adds **28 public Lean theorems in seven registered modules**.
It constructs a local analytic multiplier coordinate at every exact-period
center of the actual quadratic family, proves the exact ramification of every
repeated-return multiplier, and realizes a nonempty multiplier disk by distinct
parameters in the actual bounded-critical-orbit locus.

Write
\[
f_c(z)=z^2+c,\qquad P_j(c)=f_c^j(0).
\]
Fix a natural number \(n\), put \(p=n+1\), and assume precisely
\[
P_p(c_0)=0,\qquad P_j(c_0)\ne0\quad(0<j<p).
\]
There is no assumed analytic motion, multiplier derivative, inverse chart,
trapping disk, or parameter-locus identification in these center hypotheses.

### A. Constructed coordinate and exact repeated-return order

`center_multiplier_parameter_coordinate` constructs one analytic
periodic motion \(\zeta(c)\) through zero and an analytic local inverse
\(\psi(t)\) of its actual first-return multiplier
\[
\mu(c)=(f_c^p)'(\zeta(c)).
\]
The coordinate and companion motion theorem prove
\[
\zeta(c_0)=0,\qquad
\zeta'(c_0)=P_p'(c_0),\qquad
D:=\mu'(c_0)=2P_p'(c_0)(f_{c_0}^{p-1})'(c_0)\ne0,
\]
\[
\psi(0)=c_0,\qquad \psi'(0)=D^{-1},
\qquad \psi(\mu(c))=c,\qquad \mu(\psi(t))=t
\]
on the respective parameter and multiplier neighborhoods. The same moving
cycle retains minimal period \(p\) and is attracting near \(c_0\). Locally,
\(\mu(c)=0\) holds exactly at \(c=c_0\).

For every natural \(k\), including zero, the actual \(kp\)-return multiplier has
**analytic vanishing order exactly \(k\) in the original parameter \(c\)**:
\[
\operatorname{ord}_{c_0}\bigl(c\mapsto
(f_c^{pk})'(\zeta(c))\bigr)=k.
\]
On one common multiplier neighborhood, simultaneously for every \(k\),
\[
(f_{\psi(t)}^{pk})'(\zeta(\psi(t)))=t^k.
\]
This is a normal form for the multipliers of repeated returns, not a conjugacy
normal form for the entire dynamical map.

For \(k\ge2\), the repeated-return multiplier has zero parameter derivative and
admits **no differentiable local left inverse**. Thus the exact-period
hypothesis in the unramified multiplier coordinate has a proved obstruction
when a return is repeated.

### B. An actual open multiplier disk

`center_multiplier_disk` constructs \(r>0\), an analytic parameter
map \(\psi\), and an analytic periodic-point map \(\xi\), both analytic
throughout \(\{t\in\mathbb C:|t|<r\}\), such that:

1. \(\psi(0)=c_0\), \(\xi(0)=0\), and \(\psi'(0)=D^{-1}\).
2. \(\psi\) is injective on that disk.
3. Every parameter \(\psi(t)\) has zero actual parameter escape. By the existing
   `QuadraticEscape.parameterEscape_zero_iff`, its actual critical
   orbit is bounded.
4. \(\xi(t)\) is a periodic point of \(f_{\psi(t)}\) of minimal period \(p\),
   with actual multiplier \(t\) and \(|t|<1\).
5. The derivative of every \(pk\)-fold iterate at \(\xi(t)\) equals
   \(t^k\), simultaneously for all natural \(k\).

Both maps and their common domain are constructed; they are not hypotheses.

### C. Uniform dynamical trapping and actual parameter interior

The trapping and escape results require only a positive critical return
\(P_{n+1}(c_0)=0\); that return need not be minimal.

`center_uniform_return_trapping` constructs a single positive
dynamical radius \(s\) such that, for every sufficiently nearby complex
parameter \(d\),
\[
|z|\le s\ \Longrightarrow\ |f_d^{n+1}(z)|<s.
\]
`center_uniform_zero_escape_disk` proves that every point of the
same closed disk has zero actual escape for every nearby \(d\).
`center_mem_interior_zero_escape` then proves
\[
c_0\in\operatorname{int}\{d\in\mathbb C:
\operatorname{parameterEscape}(d)=0\}.
\]
The parameter-locus conclusion is proved directly from the return and escape
identities, without assuming an attracting-basin theorem.

## Evidence

### 1. Isolate the critical derivative factor

[QuadraticCenterMultiplier.lean](../../formalization/weighted/QuadraticCenterMultiplier.lean)
proves from the actual recurrences that
\[
M_{n+1}(c,z)=2z\,M_n(c,z^2+c),
\qquad M_j(c,z)=(f_c^j)'(z).
\]
For any differentiable motion through zero, differentiating this identity kills
the derivative of the tail factor:
\[
\frac{d}{dw}M_{n+1}(w,\zeta(w))\big|_{w=c_0}
=2\zeta'(c_0)M_n(c_0,c_0).
\]
The existing exact moving-point tangent identity gives
\(\zeta'(c_0)=P_{n+1}'(c_0)\). Existing all-period center transversality makes this
factor nonzero. Exact critical period excludes zero among every tail factor.
This proves nonvanishing for all positive periods, including period one.

### 2. Construct the coordinate on the same periodic branch

[QuadraticMultiplierCoordinate.lean](../../formalization/weighted/QuadraticMultiplierCoordinate.lean)
starts with the existing analytic exact-period motion. It recovers that
motion's actual return equation from its `Function.minimalPeriod`
identity, derives its tangent, and applies Mathlib's analytic inverse-function
theorem to its multiplier.

The return equation, attraction, inverse identities, and zero isolation all
refer to this one motion. No separately constructed branch is silently
identified with it.

### 3. Compute every repeated-return multiplier and its order

[QuadraticMultiplierIteration.lean](../../formalization/weighted/QuadraticMultiplierIteration.lean)
proves the actual multiplier cocycle and deduces, on any \(p\)-periodic point,
\[
M_{pk}(c,z)=M_p(c,z)^k.
\]
For the constructed center motion, the first multiplier has analytic order
one. Mathlib's `analyticOrderAt_pow` and germ-congruence theorem
give order \(k\) in the original parameter. The chain rule shows that a
differentiable left inverse of a repeated-return multiplier with \(k\ge2\)
would have derivative both zero and one.

The order-zero case \(k=0\) is included: the zero-fold spatial derivative is
the constant one. No positive-repetition premise is silently imposed.

### 4. Construct a uniform trapping disk

[QuadraticCenterTrapping.lean](../../formalization/weighted/QuadraticCenterTrapping.lean)
uses the existing polynomial secant product to prove
\[
f_d^p(z)=P_p(d)+zS_p(d,z,0).
\]
At the center, \(S_p(c_0,0,0)=M_p(c_0,0)=0\). Joint continuity supplies a
parameter-state neighborhood with \(|S_p|<1/2\). Choose one closed dynamical
disk inside the state neighborhood, then restrict the parameter until
\(|P_p(d)|<s/2\). The triangle inequality proves strict return trapping
uniformly over all points of the disk and all parameters in that neighborhood.

### 5. Link trapping to the actual escape potential

[QuadraticTrappingEscape.lean](../../formalization/weighted/QuadraticTrappingEscape.lean)
first identifies the two existing orbit conventions exactly. It proves that
a bounded subsequence at times \(pk\), with \(p>0\), forces the actual escape
potential to vanish.

The existing escape-approximation error at time zero gives a uniform escape
bound on bounded sets. The exact functional equation multiplies the initial
escape by \(2^{pk}\) at return time \(pk\). Since \(2^{pk}\ge pk+1\), positive
initial escape contradicts a bounded return subsequence. Intermediate
iterates need not be estimated separately.

[QuadraticCenterParameterLocus.lean](../../formalization/weighted/QuadraticCenterParameterLocus.lean)
combines this with the constructed trapping disk. It proves a uniform
dynamical disk of zero-escape points, a neighborhood of zero-escape parameters,
and actual ambient interior membership.

### 6. Realize a common analytic disk

[QuadraticMultiplierDisk.lean](../../formalization/weighted/QuadraticMultiplierDisk.lean)
combines the inverse identities, eventual analyticity of both maps, exact
period and attraction, and the zero-escape parameter neighborhood.
A metric-neighborhood theorem extracts one positive-radius multiplier disk
on which all conclusions hold. The identity \(\mu(\psi(t))=t\) proves
injectivity of \(\psi\).

### Validation and development record

At proof checkpoint
[`73a227a107bfe874e0fb62e23c7097ea2b8a1465`](https://github.com/dovvnloading/loops-research-archive/commit/73a227a107bfe874e0fb62e23c7097ea2b8a1465),
**all 23 CI workflows passed**. The unchanged
[weighted Lean job](https://github.com/dovvnloading/loops-research-archive/actions/runs/45914420973/job/140230112792)
reported:

```text
Build completed successfully (8944 jobs).
AXIOM_AUDIT_PASS weighted: 137 modules, 3123 declarations
```

Its per-module transitive dependency audit also passed for all new modules:

| Module | Public theorem declarations | Audited compiled declarations |
|---|---:|---:|
| `QuadraticCenterMultiplier` | 8 | 10 |
| `QuadraticMultiplierIteration` | 8 | 10 |
| `QuadraticMultiplierCoordinate` | 2 | 7 |
| `QuadraticMultiplierDisk` | 1 | 1 |
| `QuadraticCenterTrapping` | 2 | 2 |
| `QuadraticTrappingEscape` | 4 | 8 |
| `QuadraticCenterParameterLocus` | 3 | 4 |
| **Total** | **28** | **42** |

The compiled count includes private and generated declarations. Every
declaration passed the existing permitted-axiom audit; no new axioms or
proof placeholders were introduced. Source coverage and forbidden-token
checks passed as well. The proof text in the final documentation revision is
unchanged from this passing checkpoint; its source edits update comments,
and the revision runs the existing CI again.

One unrelated provenance check initially timed out while downloading its
locked KL2 reference PDF. The
[unchanged failed-job retry](https://github.com/dovvnloading/loops-research-archive/actions/runs/45914420940/job/140231206678)
passed. No source lock, verifier, or workflow was changed.

The PR was opened at the initial target-selection checkpoint. The derivative
calculation, repeated-return laws, constructed coordinate, exact analytic
order, disk realization, trapping, and escape bridge are all preserved as
successive commits in the same PR. Concurrent mechanical synchronizations
with main were retained, including the other contributions' proof files and
registry entries. No force push was used.

CI initially caught a reserved-token name, scalar-module elaboration
mismatches in derivative rules, an addition-order mismatch in the
trapping estimate, and a natural-number normalization in the escape bound. These were corrected in the proofs. No hypothesis,
toolchain, workflow, validator, or proof-trust rule was weakened.

All seven modules are default Lake targets, and every public theorem is
registered in the source/theorem index. The existing compiled-declaration
audit permits only `propext`, `Classical.choice`, and
`Quot.sound`. It also audits private and generated declarations.

No local compilation is claimed. The official pinned-toolchain download
exceeded the available workspace storage, and the sandbox policy rejected
the bounded cleanup escalation after sandbox startup failed. The unchanged
GitHub Actions Lean workflows are the compilation and dependency-audit
authority for this contribution.

Reproduce with the pinned Lean 4.32.0 and locked Mathlib revision:

```sh
cd formalization/weighted
lake exe cache get
lake build QuadraticCenterMultiplier QuadraticMultiplierIteration QuadraticMultiplierCoordinate QuadraticCenterTrapping QuadraticTrappingEscape QuadraticCenterParameterLocus QuadraticMultiplierDisk
lake build
cd ../..
python code/verify_lean_coverage.py --audit weighted
python code/contribute.py check
```

## Dependencies

- Research target: `H4_RIGIDITY`. Its `H3_COERCIVITY`
  prerequisite remains open. Neither ledger gate is assumed by these Lean
  theorems.
- [QuadraticCriticalTransversality.lean](../../formalization/weighted/QuadraticCriticalTransversality.lean):
  actual critical/return recurrences, actual parameter and spatial derivatives,
  center transversality, and the moving-point tangent identity.
- [QuadraticPeriodicMotion.lean](../../formalization/weighted/QuadraticPeriodicMotion.lean)
  and [QuadraticPeriodicStability.lean](../../formalization/weighted/QuadraticPeriodicStability.lean):
  constructed analytic periodic motion, exact-period persistence, and
  analyticity/continuity of its multiplier.
- [QuadraticCollisionFactorization.lean](../../formalization/weighted/QuadraticCollisionFactorization.lean):
  the explicit jointly analytic secant product and its exact difference and
  diagonal identities.
- [QuadraticEscape.lean](../../formalization/weighted/QuadraticEscape.lean):
  the actual limiting escape potential, uniform error bound, iterate
  functional equation, and zero-escape/bounded-orbit equivalence.
- Pinned Mathlib:
  [analytic inverse-function theorem](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Calculus/InverseFunctionTheorem/Analytic.lean),
  [analytic vanishing order](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Analysis/Analytic/Order.lean),
  complex calculus, metric neighborhoods, and neighborhood filters.

## Boundary

This is an all-period local theorem at **superattracting quadratic centers**.
It proves actual zero-escape neighborhoods there. It does not establish
connected relative neighborhoods at arbitrary boundary parameters or the
infinite marked-tower rigidity required by H4. H1-H4, UPTCR, and MLC retain
their existing statuses; no ledger status change is requested.

The parameter neighborhoods and both disk radii depend on the center and
return time. There is no universal radius over periods, no entire unit
multiplier disk, no global hyperbolic-component uniformization, and no
cross-scale or infinite-tower estimate.

The results establish an attracting exact-period cycle and bounded critical
orbits for the constructed nearby parameters. They do not separately prove
convergence of the critical orbit to that particular marked cycle.
The disk theorem states analyticity and injectivity on its domain; it does
not identify its full image with a hyperbolic component.

The coordinate and motion are represented by total Lean functions whose
inverse and dynamical identities have explicitly local scope.
The repeated-return obstruction concerns differentiable local left inverses.
No claim about arbitrary continuous inverses is substituted for that theorem.

Source registration uses the existing METADATA route. It records the actual
formal results without promoting an unresolved native model-to-geometry
identification. This contribution advances the archive's verified
formalization; no worldwide mathematical-priority claim is made.

## Attribution

Builds on the archive's
[constructed periodic motion and critical coordinates](../quadratic_periodic_motion_20261126/NOTE.md),
[arithmetic multiplier contribution](../h4_arithmetic_multiplier_rigidity_20261126/NOTE.md),
critical-transversality development, and actual escape-potential development.
Mathlib supplies the analytic inverse-function and vanishing-order machinery.
No unformalized dynamical theorem is inserted as an assumption.

OpenAI GPT-6 Astra Pro performed proof construction, integration, and separate
AI source reviews. The reviews checked exact-period edge cases, common-branch
and common-neighborhood quantifiers, actual escape identification, and the
limits listed above. No independent human specialist review has occurred.
