---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="actual-maximal-crest-20261127"></a>

# Actual initial crest endpoints and full radial-integral limits

## Claim

For every integer return index p at least 17, constructed literal quadratic
parameters have a coherent actual crossing curve on the enlarged
radius window S=[1/16,133/2000]. For all sufficiently large return indices, its
complete two-sided terminal gate has a maximal initial connected component
[1/16,r_p). The endpoint is an actual third-return collision, is not an
assumed parameter, and converges to the unique limiting-model endpoint
r_infinity in (663/10000,133/2000).

The complete selected radial coefficients, with the source's
period-dependent normalization, converge to the full model coefficient,
which is strictly greater than 1/3. Consequently the actual selected
radial coefficients are eventually greater than 1/3. These are integrals
of actual polynomial crossing data; they are not asserted to be physical
KKL extremal widths.

## Evidence

Research baseline: main commit `7b179434fdbf12070485ba4a91c6dc3c9f55fa24`.
The branch also incorporates main commit
`77e136b56347d7517d62dbaee5ffca3a8d9628ea`; its independent three-return
results and registrations are preserved.

### Objects and precise new result

Write f_c(z)=z^2+c, d_p=f_c^p(0)>0, and

    H_p(z)=f_c^p(d_p z)/d_p.

The earlier `NearTwoTip.exists_actual_tip` constructs the parameters
satisfying `ActualTip`: the near-minus-two interval, positive return
scale, sharp normalized quadratic coefficient, signed six-versus-three
return relation, and critical-orbit bounds. Parameter existence is
therefore discharged in the new final existence theorem.

For every s in S the new extended-window theorem constructs a unique
upper-semicircle root

    z_p(s)=-3/4+s*(u_p(s)+i*sqrt(1-u_p(s)^2)),
    Re H_p(z_p(s))=0,  Im H_p(z_p(s))>0.

The angle is 100-Lipschitz, the point curve is injective and 15-Lipschitz,
and every upper-semicircle root lies in -1/100<u<1/100. Both second and
third images are exactly real. The point error against the same limiting
radical curve is at most 33000*4^(-p), uniformly over S.

Define the literal actual terminal coordinate

    T_p(s)=Re H_p^3(z_p(s)).

`ActualCrestEndpoint.actual_terminal_tendsto` proves uniform convergence
on all of S to `crestTerminal k_infinity`. The finite-composition proof
first obtains actual intermediate-domain containment from compactness
and the strict reference-domain bounds; it never assumes that containment.
The first-exit theorem then constructs r_p with

    T_p(r_p)=-1,
    T_p(s)>-1 for every 1/16<=s<r_p,
    connectedComponentIn(S intersect {s : T_p(s)>-1},1/16)=[1/16,r_p).

It proves r_p tends to r_infinity. No monotonicity or uniqueness of later
roots of T_p is a premise. The separate original-plane theorem gives an
actual point w_p on |w+3*d_p/4|=d_p*r_p with

    f_c^(3*p)(w_p)=-d_p,

and a positive-imaginary p-th image. This is an exact complex polynomial
equality, not merely a real-part test.

### Actual radial order and the opposite terminal cut

`ActualCrestRadialOrder` proves that the actual terminal coordinate is
strictly decreasing on all of S for sufficiently large return indices. Equal
third images can be pulled back through the actual injective second
support; the positive imaginary first images exclude the antipodal
collision alternative. Initial-disk injectivity then forces equal radii.
Continuity and injectivity on an interval give strict order, and the
independently proved first exit determines its decreasing orientation.
Thus the endpoint is the only terminal root anywhere in S, and the exact
strict-gate classification is T_p(s)>-1 if and only if s<r_p.

`ActualCrestUpperGate` also proves the opposite source cut on the entire
window, with one uniform positive margin for all sufficiently large
return indices:

    T_p(s)+delta < -Re H_p^4(0),  delta>0.

Its actual fourth-cut error is at most 3688776*4^(-p). The strict model
upper-cut gap and the already proved uniform actual terminal convergence
supply the margin. Consequently the complete source terminal condition
-1<T_p(s)<-Re H_p^4(0) holds exactly before the unique endpoint in S.

### Full moving-endpoint integral

The coefficient is defined from the complete selected initial component:

    C_p = 2*pi/log(2-2/p)
          * integral_[1/16,r_p] 1/(s*arccos(u_p(s))) ds.

This is the source normalization: the original parent radii have ratio
2(p-1)/p. Uniform angle convergence, uniform positivity of the denominator,
and convergence of the moving endpoint prove

    C_p -> fullModelCoefficient(k_infinity,r_infinity) > 1/3.

The integral argument allows oscillating endpoints. It does not replace
the moving integral by a fixed interior subintegral. The theorem
`ActualCrestIntegral.exists_actual_initial_collars_and_positive_limit`
constructs the model parameter, actual parameter sequence, curve families,
and endpoints without any parameter-existence or approximation premise.

### One simultaneous constructed realization

`ActualCrestTheorem.exists_actual_complete_collars_and_limit` assembles
all conclusions for the same constructed model parameter, actual parameter
sequence, crossing families, and endpoint sequence. A single positive
upper-cut margin and a common eventual threshold give strict radial order,
the unique endpoint, the exact complete two-sided gate and its connected
component, entire-support signs and bounds, fourth-iterate injectivity,
the exact original-plane collision, and an actual coefficient above 1/3.
The endpoint and coefficient limits refer to those very same endpoints.
This final theorem has no input hypotheses. Its connected-component claim
uses the complete two-sided source terminal condition explicitly.

### Entire-support control

`ActualCrestSupport` transfers the archived model estimates to the full
closed disk |z+3/4|<=133/2000, not just selected crossing points. Eventually
all four actual images stay in |z|<=23/20, the entire second image has
positive real part, and the entire third image has negative real part.
The exact actual collision classification excludes antipodal collisions
on those supports. In particular H_p^4 is injective on the whole part of
the input disk where Re H_p(z)>0. One threshold works simultaneously for
every parameter satisfying `ActualTip`, independently of parameter choice.

### Lean files and verification

All files are in `formalization/weighted/`:

| Module | Role |
|---|---|
| CrestFirstExit | First exit, exact component, uniform root stability |
| CrestIterateLimit | Finite-composition limits with proved domain checks |
| ActualCrestCrossingWindow | Extended actual crossing family and full semicircle uniqueness |
| CrestIntegralLimit | Moving-endpoint integral and source normalization |
| ActualCrestEndpoint | Literal actual terminal endpoint and original-plane collision |
| ActualCrestIntegral | Constructed parameters, endpoint and full integral limit |
| ActualCrestSupport | Entire actual support, signs and fourfold injectivity |
| ActualCrestRadialOrder | Actual strict radial order and unique terminal root |
| ActualCrestUpperGate | Opposite terminal cut with a uniform positive margin |
| ActualCrestTheorem | One constructed realization satisfying all conclusions simultaneously |

Every module has compiled locally with pinned Lean 4.32.0 and Mathlib.
The repository's original compiled-declaration audit passed for all 169
declarations across the ten new modules, including private and generated
declarations. Their transitive dependencies use only `propext`,
`Classical.choice`, and `Quot.sound`. The full contribution intake also
passes against the updated main branch. The PR records
head-specific CI builds; the existing weighted workflow builds the full
project and audits every declaration. No workflow or trusted baseline is
changed. Reproduce with:

    cd formalization/weighted
    lake build
    cd ../..
    python3 -B code/verify_lean_coverage.py --audit weighted
    python3 -B code/contribute.py check

All public theorems are registered with `code/contribute.py lean-add`.

## Dependencies

`NOV26_CREST_16` and the still-open `NOV26_OPEN_CREST_LIMIT`; the source
`research/independent_audits/crest_transport_asymptotics_20261116/NOTE.md`;
`LimitingCrestEndpoint`, `LimitingCrestSharpCoefficient`,
`LimitingCrestArcGates`, `ActualCrestLimit`, `NearTwoTip`, and
`QuadraticCrestDividedDifference`; pinned Mathlib topology, interval
integration, complex arithmetic, and real analysis. The source note
motivates the objects; its unformalized dynamical claims are not premises
of the new actual-polynomial existence theorem.

## Boundary

`NOV26_OPEN_CREST_LIMIT` remains open; no ledger status change is requested.

- The endpoint and exact two-sided terminal-gate classification are
  proved on S=[1/16,133/2000]. They do not exclude another admissible
  component elsewhere in the larger original parent interval. The
  selected open radial interval is (1/16,r_p); the closed inner endpoint is used
  only to anchor the relative connected-component statement.
- The formal `ActualTip` parameters are constructed and satisfy the stated
  polynomial relations, but their identification with the source's
  distinguished primitive-component branch, least critical preperiod,
  and primitive renormalization period is not supplied here.
- The source real q/w gates, central properness, full physical KKL
  access marking, marked proper-path admissibility, prime-end transport,
  and conformal-width identification remain to be proved. The selected radial coefficient is not an unrestricted Wave
  optimum or an already identified extremal width.
- All endpoint and coefficient conclusions are eventual in the return index;
  this packet does not assert an explicit first index for them or prove
  the displayed numerical conjecture near 0.347005.
- No H1-H4, UPTCR, MLC, or worldwide priority claim is made.

## Attribution

The model endpoint and its >1/3 coefficient were already proved in the
`limiting_crest_gate_20261126` packet. The
`actual_crest_foliation_20261126` packet proved actual curves and uniform
limits only on [0.063,0.066], and explicitly left the maximal actual
endpoint and full integral open. Those results are used, not resubmitted
as new progress. The advance here is the actual moving endpoint, exact
initial component, full moving integral, and entire-support transport.
AI-assisted proof development and independent AI scope review; no
independent human review. Released under CC0.
