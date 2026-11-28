---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical development, Lean implementation and adversarial review
human_review: none
---

<a id="signed-crest-endpoint-20261128"></a>

# Signed displacement of the actual maximal crest endpoint

## Claim

**Validated:** the complete Lean proof chain, physical assembly and
transitive axiom audit passed at commit
[`c54e3b2057d8fd8f670333b630dc6a6b3ed4a54b`](https://github.com/dovvnloading/loops-research-archive/commit/c54e3b2057d8fd8f670333b630dc6a6b3ed4a54b).
All 23 workflows passed. The new modules contain no proof placeholders
or new axioms; their transitive dependencies use only the repository's
permitted foundations. The exact validation record is below.

Write `q_p = (1/4)^p`. Let `c` satisfy the existing `ActualTip p c`, let
`F` be the existing actual crossing family, and let `r_p` be the unique
maximal endpoint of the complete actual terminal gate. Here `r_p` is the
normalized radius; the corresponding original-plane radius is `d*r_p`,
where `d = f_c^p(0) > 0`. Let `k_0` be the unique limiting parameter and
`r_0` its unique limiting endpoint.

`ActualCrestEndpointDrift` proves

\[
\frac{3}{50}q_p < r_p-r_0 < \frac{21}{100}q_p
\qquad (p\ge100).
\]

Consequently the actual maximal endpoints approach the limit from above
at precisely the first exponential order, and

\[
r_{p+1}<r_p \qquad (p\ge100).
\]

The same mechanism proves a direct inequality for the obligation's
transport quantity: the all-density physical descendant/parent modulus
ratio is strictly above its existing limiting coefficient for `p >= 100`.
This is a one-sided limit theorem; it does not assert monotonicity of the
width ratios across periods.

The consecutive-period theorem permits independent choices of actual
parameters and crossing families satisfying the archive's predicates.
The final existence theorem constructs one sequence of these endpoints,
proves it strictly decreasing and convergent, and retains the complete
physical collar realization for the very same radii.

These statements concern the selected maximal circular collars in F17,
which is the subject of `NOV26_OPEN_CREST_LIMIT`. The radius is selected
by the literal return's terminal collision and the complete gate set,
not by an auxiliary extremal problem.

## Evidence

### 1. The new mathematical mechanism

Put `d = f_c^p(0)` and `H(z) = f_c^p(d*z)/d`, exactly as in the archive.
Let `A_n` be the actual quadratic coefficient of `f_c^(n+1)` and define
its quartic coefficient by the exact recurrence

\[
B_0=0,\qquad B_{n+1}=2x_{n+1}B_n+A_n^2,
\qquad x_j=f_c^j(0).
\]

The normalized quartic coefficient is `beta = B_(p-1)*d^3`.
`ActualCrestQuartic` proves, for every `ActualTip p c`, `p >= 17`, and
`|z| <= 3/2`,

\[
H(z)=1-\kappa z^2+\beta z^4+E(z),\qquad
|E(z)|\le400q_p^2.
\]

The estimate bounds the complete polynomial remainder. Its proof
retains every term of degree six and above in the squaring recurrence;
it does not discard an unbounded Taylor tail.

`ActualCrestQuarticScale` proves

\[
\frac7{50}A_{p-1}^2\le B_{p-1}\le\frac{17}{100}A_{p-1}^2,
\qquad 3q_p<\beta<7q_p.
\]

The upper bound uses the whole early critical prefix, followed by the
last two positive orbit points. The lower bound retains the squared
quadratic contributions of the final two steps. The exact normalized
return scale then transfers these coefficient bounds to `beta`.

### 2. The correlated parameter correction

Let `u_n = Q_k^n(0)` for `Q_k(x)=1-k*x^2`. The first quartic response
along this orbit is defined by

\[
b_0=0,\qquad b_{n+1}=-2ku_n b_n+u_n^4.
\]

`ActualCrestQuarticRelation` controls the complete actual orbit by
`u_n + beta*b_n` through the sixth return. Using the actual signed
relation `H^6(0)+H^3(0)=0`, it obtains, for `p >= 100`,

\[
|R(\kappa)+\beta(b_6+b_3)|\le10^{27}q_p^2,
\quad R(k)=Q_k^6(0)+Q_k^3(0).
\]

On the archived parameter isolator, exact rational interval proofs give

\[
-6.264834\le b_6+b_3\le-6.211794,
\qquad 6.599964\le R'(k)\le6.656502.
\]

For `p >= 100`, the remainder is small enough to prove

\[
\frac{93}{100}\beta<\kappa-k_0<\frac{95}{100}\beta.
\]

The reference parameter in the finite orbit expansion is the actual
`kappa`. Thus the parameter shift is subsequently obtained from the
critical relation, rather than assumed as an independent perturbation.

### 3. The endpoint response and its sign

Write the actual selected endpoint as `z=-x+i*v`, its first image as
`i*Y`, and its second image as `T`. The actual third image is exactly
`-1`. The complete quartic remainder gives four scalar equations with
errors at most `400*q_p^2`:

\[
\begin{aligned}
2-\kappa T^2+\beta T^4&\simeq0,\\
1+\kappa Y^2+\beta Y^4-T&\simeq0,\\
1-\kappa(x^2-v^2)+\beta(x^4-6x^2v^2+v^4)&\simeq0,\\
2\kappa xv-4\beta xv(x^2-v^2)-Y&\simeq0.
\end{aligned}
\]

The fifth equation is the exact normalized circle equation
`(x-3/4)^2+v^2-r_p^2=0`.

`CrestEndpointQuantitative` first gives explicit coarse proximity of the
actual radius, point and first two images to the limiting endpoint.
`CrestModelCoordinateBounds` independently isolates the existing
limiting parameter by exact signs and strict monotonicity, then isolates
the positive solution of the backward endpoint equations. Every model
coordinate is proved within `10^-22` of its declared rational center.
The centers are not assumed values of the model.

`CrestResponseLinearization` certifies finite differences under addition
and multiplication, keeping an explicit linear part and a bound on all
remaining products. The exact model equations cancel before numerical
center bounds are used: the certificate concerns differences of the
actual and model expressions. Thus a center enclosure of size `10^-22`
contributes only after multiplication by an already proved `O(q_p)`
displacement. It introduces no absolute `10^-22` residue, which would
swamp `q_p` at large periods.

`CrestResponseArithmetic` applies this algebra to
the five equations and forms an exact rational combination eliminating
`Delta T`, `Delta Y`, `Delta x`, and `Delta v`. It yields

\[
|\Delta r+P\Delta\kappa+B\beta|\le q_p/20000,
\]

with

\[
0.2087\le P\le0.2088,\qquad -0.222\le B\le-0.2219.
\]

Combining this with the correlated parameter bounds gives the genuinely
signed endpoint response

\[
\beta/50<r_p-r_0<3\beta/100.
\]

The two effects have opposite signs, so neither the old unsigned map
error nor the prior sign of `kappa-k_0` determines this conclusion.
The quartic scale bounds then prove the claimed first-order bounds.
Finally `q_(p+1)=q_p/4` and `21/400 < 3/50` give strict decrease.

### 4. Identification with the actual maximal physical collars

`ActualCrestEndpointResponse.actual_endpoint_quartic_response` supplies
every arithmetic hypothesis directly from the existing `ActualTip`,
`Family`, `terminal`, `radialPoint`, and `crestTerminal` objects.

`ActualCrestEndpointDrift.exists_strictly_decreasing_physical_endpoints`
retains the exact complete set equality

```
Icc (1/16) (parentOuter p) ∩
  {s | ActualEndpointGates c p s alpha ∧
       terminalGate F s ∧ fourthTerminalGate F s}
= Ico (1/16) r_p.
```

For the same `r_p` it supplies the existing `RealizedCollar`, including
proper actual parent and descendant paths, their all-density modulus
identities, the exact width ratio and full dynamical ancestry. It also
supplies a point in the physical and archived parent source with

\[
|z+3d/4|=d r_p,\qquad
\operatorname{Re} f_c^p(z)=0,\qquad
\operatorname{Im} f_c^p(z)>0,\qquad f_c^{3p}(z)=-d.
\]

Thus the normalized radius and the original-plane maximal collar are
linked by an exact Lean theorem within the final assembly.

### 5. Signed transport for the same physical families

At any limiting crossing `z`, write `t=Re(z^2)`. Its defining equation
implies `k_0*t=1`, and hence `1/2 <= t <= 3/5`. Also
`Re(z^4) <= t^2`. The proved correlated parameter shift therefore gives

\[
\operatorname{Re}H(z)<-\beta/10<0.
\]

The actual crossing function is strictly increasing in the circle cosine.
Thus its selected cosine is strictly larger than the limiting cosine,
and its positive arccosine angle is strictly smaller, at every radius in
the full parent interval. This is proved for the actual branch by
`ActualCrestQuarticCrossing` and `ActualCrestAngularDrift`.

Consequently the actual radial modulus density is larger throughout the
common retained interval. On the additional interval `(r_0,r_p)` it is
at least one. Together with the new endpoint lower bound this gives

\[
\operatorname{Mod}(\Gamma_p)-
\int_{1/16}^{r_0}\frac{ds}{s\arccos u_0(s)}
>\frac3{50}q_p,
\]

where `Gamma_p` is the existing literal four-return physical descendant
family, and `Mod` is its independently defined modulus over all measurable
planar densities, expressed as a real number by `modulus.toReal` in Lean.
Finiteness follows from the archived integral identity. The identity
transferring the integral to this modulus
is the archived `descendants_width_eq_integral`, applied to the same
actual family and maximal endpoint.

The finite-period physical parent modulus is
`log(2-2/p)/(2*pi)`, strictly smaller than `log(2)/(2*pi)`.
`ActualCrestWidthDrift.actual_physical_ratio_gt_limit` then states

\[
\frac{\operatorname{Mod}(\Gamma_p)}
     {\operatorname{Mod}(\text{parent}_p)}
>\operatorname{fullModelCoefficient}(k_0,r_0).
\]

This final inequality is about the obligation's own complete selected
physical transport ratio. Neither a surrogate path family nor an assumed
modulus identification occurs in its hypotheses.

### 6. Validation record

The branch started from main `637266b909d5e7566d8e39141f3b135e3405f38f`
and has integrated subsequent main changes. The previous closed
geometric-child attempt #272 is not the base and contributes no results
or proof dependencies to this packet.

Lean is not installed in the local execution environment. Validation was
performed by the unchanged repository CI build and transitive proof audit.
The [weighted Lean run](https://github.com/dovvnloading/loops-research-archive/actions/runs/46136726569)
at source commit `c54e3b2057d8fd8f670333b630dc6a6b3ed4a54b` reports:

```
Build completed successfully (9292 jobs).
AXIOM_AUDIT_PASS weighted: 308 modules, 8104 declarations
```

All 13 new modules compiled. Their 366 declarations, including private
and generated declarations, individually passed the transitive audit.
The unchanged allowlist is `propext`, `Classical.choice`, and `Quot.sound`.
The source-coverage check also rejects `sorry`, `admit`, new `axiom`
declarations, `native_decide`, `unsafe`, and `implemented_by`. All 43
public theorem names are registered in the existing theorem index;
the helper count is not a count of separate research discoveries.

All 23 workflows at that source commit passed. The non-draft local command
`python3 code/contribute.py check --pr-title '[NOV26_OPEN_CREST_LIMIT] Signed drift of the actual maximal crest endpoint'`
also returned `RESULT: PASS`, and `git diff --check` passed. Every proof
checkpoint and repair was committed in PR #275. The final documentation
checkpoint changes no Lean source. Numerical exploration is not used as
proof evidence.

## Dependencies

The proof builds on the existing actual parameter existence, literal
return recurrence, signed-tip recognition, complete angular and radial
classification, proper physical paths, and all-density modulus results.
It uses the following archived modules directly or transitively:

- `LimitingCrestParameter`, `LimitingCrestQuadraticReturn`,
  `NearTwoShooting`, and `NearTwoTip` for the literal maps and parameter.
- `ActualCrestRemainderScale` and `TwoLevelPerturbation` for earlier
  full-polynomial estimates and the actual critical-return scale.
- `GlobalCrestClassification`, `GlobalCrestFinalCut`, and
  `GlobalCrestPhysical` for the exact complete gate and physical collision.
- `ActualCrestTransportLimit` and `UniformCrestTransport` for the same
  actual collar's proper paths, complete moduli, and ancestry.

Generic finite-difference algebra and final assembly corollaries are
supporting steps. The new claim is the signed, matching-order law and
strict period ordering for the already-defined maximal actual endpoint.

## Boundary

This is a quantitative refinement within the selected full-circle
collar obligation. The already archived endpoint convergence,
all-period physical persistence, positive transport limit and signed
auxiliary coefficient drift are prior results, not claims of this packet.
The ledger's open entry is retained unchanged.

The theorem does not identify selected circular collars with an
unrestricted KKL Wave optimum. It neither closes general native marking
or all-Wave comparison gaps nor proves MLC or any H1–H4 assertion.
The explicit threshold is deliberately conservative. No claim of strict
endpoint ordering below `p=100`, an optimal displacement constant, a
first-order limit for `(r_p-r_0)/q_p`, or monotonicity of the physical
modulus ratios across periods is made. The physical parent normalization
has its own slower period dependence, so the endpoint exponential law
is not asserted as the convergence rate of the normalized width ratio.

## Attribution

The canonical objects and prior convergence/realization results are due
to the existing packets
[actual maximal crest](../actual_maximal_crest_20261127/NOTE.md),
[global crest classification](../global_crest_classification_20261127/NOTE.md),
[actual crest path width](../actual_crest_path_width_20261127/NOTE.md), and
[uniform crest transport](../uniform_crest_transport_20261128/NOTE.md).
The original finite-period and numerical asymptotic work is
[crest transport asymptotics](../../research/independent_audits/crest_transport_asymptotics_20261116/NOTE.md).

The earlier actual-maximal-crest packet explicitly allows oscillating
endpoints. Global classification does not claim a new asymptotic error
rate. Uniform transport proves a sign for the auxiliary quadratic
coefficient but does not prove the endpoint's first-order sign or period
monotonicity. The new quartic/critical-relation/endpoint calculation is
what removes those remaining possibilities for the actual maximal collar.

Repository and primary-literature searches found no prior version of
this exact signed endpoint theorem. This records the checked comparison
with prior work; it is not a claim of an exhaustive worldwide priority
search. All proof code and exposition are released under the repository's
CC0 terms; human review is recorded above.
