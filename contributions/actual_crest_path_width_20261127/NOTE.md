---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical development, Lean proofs and adversarial review
human_review: none
---

<a id="actual-crest-path-width-20261127"></a>

# Actual proper circular crest transport and its physical modulus limit

## Claim

For the constructed parameters satisfying the archive's `ActualTip`
predicate, uniformly for all sufficiently large return indices, the
selected upper q-side circular arcs undergo the specified **literal
real-slit restrictions and four polynomial pushes**. Their complete
physical image family consists of simple proper slit arcs. Its
independently defined all-density modulus equals the archived radial
integral. Dividing by the modulus of the full chosen physical circular
parent gives a ratio converging to the archived positive coefficient,
strictly above one third.

The new content is the **whole-path and physical-metric identification**.
The scalar coefficient, its endpoint, its positivity and its analytic
limit were already proved in the archive and are used as inputs. This
packet does not claim a new scalar asymptotic calculation or complete
native KKL realization.

The main unconditional existence theorem is
`ActualCrestTransportLimit.exists_proper_physical_transport_limit`.
`eventually_every_actual_tip_realizes_collar` gives uniform realization
for every admissible actual parameter and crossing family. Neither
requires a path-survival, univalence, width-comparison or strict-support
hypothesis as input.

## Evidence

### Precise objects and theorem

Write `f_c(z) = z^2 + c`, `d = f_c^{p}(0) > 0`, and
`H(z) = f_c^{p}(d*z)/d`. These are the literal polynomial and normalized
return from `LimitingCrestQuadraticReturn`, not a limiting quadratic
surrogate. Let `u_p(s) = GlobalCrestCrossing.realAngle F s` be the unique
selected actual upper-circle crossing, and let `r_p` be its globally
classified terminal root. The existing construction gives

- `663/10000 < r_p < 133/2000` and `terminal F r_p = -1`;
- an actual fixed point `518/1000 < α_p < 519/1000`;
- the original chosen parent outer radius
  `parentOuter p = (p-1)/(8*p)`.

The physical **parent family** is the full chosen circular foliation

\[
 P_{p,\rho}(t)=-\frac{3d}{4}+\rho e^{it},\qquad
 0\le t\le2\pi,\qquad
 \frac d{16}<\rho<d\frac{p-1}{8p}.
\]

Both parameter ends are at q on the target slit. Its open interior lies
in the actual target slit complement; the left real contact w is outside
that target slit. Each open loop is simple.

The selected **descendant family** contains exactly the full images

\[
 D_{p,s}(t)=f_c^{4p}\!\left(d\left(-\frac34+s e^{it}\right)\right),\qquad
 0\le t\le\arccos u_p(s),\qquad
 \frac1{16}<s<r_p.
\]

`every_radius_occurs` proves every retained radius contributes its complete
path. `descendant_radius` proves conversely that every curve counted by
the modulus has precisely such a radius and literal polynomial formula.
No desired properness condition is built into this formula as an assumed
witness: universal properness is subsequently proved.

For these smooth parametrized families the modulus is defined by

\[
 M(\Gamma)=\inf_{\substack{\rho:\mathbb C\to[0,\infty]\text{ measurable}\\
 \forall\gamma\in\Gamma,\ \int_0^{T_\gamma}
 \rho(\gamma(t))|\gamma'(t)|\,dt\ge1}}
 \int_{\mathbb C}\rho(z)^2\,dA(z).
\]

The Lean definitions use extended nonnegative densities, ordinary
parametrized arclength and planar Lebesgue area. They do not restrict
the competitors to radial, continuous, bounded or finite-energy densities.
The exact results are

\[
 M(\mathcal D_p)=\int_{1/16}^{r_p}
     \frac{ds}{s\arccos u_p(s)},\qquad
 M(\mathcal P_p)=\frac{\log(2-2/p)}{2\pi},
\]

and, for all sufficiently large indices,

\[
 \frac{M(\mathcal D_p)}{M(\mathcal P_p)}>
 \frac13,\qquad
 \frac{M(\mathcal D_p)}{M(\mathcal P_p)}\longrightarrow
 C_\infty>\frac13.
\]

Here `C∞ = LimitingCrest.fullModelCoefficient κ₀ r∞`, with the parameter
root, terminal root and endpoint convergence specified in the theorem.
No new decimal enclosure for the previously proposed numerical value
is asserted.

`RealizedCollar` combines properness of both exact metric families,
the two modulus identities, the exact ratio, the strict lower bound,
the maximal q-side **parameter** component, and the complete physical
restriction ancestry of every counted descendant. The final existence
theorem constructs all parameter, crossing-family, fixed-cut and
terminal-endpoint data and proves these realizations eventually alongside
the limit for the same families.

## The new whole-path argument

### Different source and target slits

In normalized coordinates the source slit is `[-1,1]` and the target slit
is `[H^2(0),1]`. In original coordinates these are `[-d,d]` and
`[f_c^{2*p}(0),d]`. The new modules prove these identities and inclusion
of the scaled domains in the archive's original physical source and
target domains.

For every full parent radius, the parent circle intersects the target
slit **only at q**, and intersects the source slit **exactly at q and w**.
Consequently the complete parent is a proper loop in the target, and
the first source restriction cuts it into the upper and lower semicircles.
`CircularParentModulus` proves that using the proper parameter interval
`[0,2π]` gives the same complete-density metric as the polar integration
chart `(-π,π)`. This equality holds even for unbounded and nonintegrable
extended densities.

### Complete ancestors, not endpoint tables

The exact divided difference of the complete high-degree return gives

\[
 \operatorname{Im}H(z)=2\operatorname{Re}z\operatorname{Im}z\,
   \operatorname{Re}S(z,\bar z),
 \qquad \operatorname{Re}S(z,\bar z)<0
\]

on the certified disk. This proves the real-contact census and signs
at every point of the actual full semicircle.

The first three source restrictions retain its entire open interior.
At the designated crossing, the second image is strictly greater than
`1`, outside both slits. The third image is to the left of `H^2(0)`, hence
outside the target slit, but is inside the longer source slit. Therefore
the fourth restriction deletes exactly this one point. No additional
hidden real contact is allowed.

Each complete closed ancestor remains simple. In the first-image case,
where the two real ends do not lie in one strict half-plane, the proof
separately excludes an antipodal collision by the strict actual inequality
`Re H(q) + Re H(w) < 0`.

`ActualCrestComponents.fourth_q_component` proves that the whole surviving
q-side parameter interval `(u_p(s),1)` is the connected component for
every basepoint on that side. Thus the selected arc is not an arbitrarily
shorter proper subarc. The module also identifies its literal third-image
set and proves injectivity of that parametrization. The component theorem
is stated in the real parameter survivor set; no separate ambient-complex
connected-component theorem is claimed.

### Closed-family conformal realization

The concrete open chart for `H^4` is defined by

\[
 |H^j(z)|<23/20\ (0\le j\le3),\quad
 \Re z<0,\quad \Re H(z)+\Im H(z)>0,\quad
 \Re H^2(z)>0,\quad \Re H^3(z)<0.
\]

It contains all the selected **closed** q-side leaves, including their
crossing endpoints. The tilted first-image condition includes the endpoint
where `Re H = 0`. The exact signed fibers and diagonal divided difference
construct joint injectivity, the nonzero derivative and the inverse
chart on this actual open set. Scaling its image gives exactly
`d*H^4(z) = f_c^{4*p}(d*z)`.

Every counted descendant is proved simple on its entire closed interval,
with open interior in the physical target slit complement and strictly
positive imaginary part. Its two real endpoints lie respectively in
`(f_c^{6*p}(0), d*α_p)` and `(f_c^{2*p}(0), f_c^{5*p}(0))`.
`descendant_full_ancestry` supplies the whole physical semicircle and
all intermediate source/target memberships for that same counted curve.

### Metric identification

The generic analytic tools are classical. Cauchy--Schwarz and polar
change of variables give a lower energy bound for every admissible
density. The explicit leafwise reciprocal-speed density attains it on
every leaf, not just almost every radius. A separate conformal transport
proof derives both density transports from the chain rule and the real
Jacobian `|h′|^2`.

Applying those tools to the proved actual chart and whole surviving
family removes the conformal-realization premise from this concrete
path-family calculation. Only after this identification does the proof
reuse the archived coefficient bound and convergence theorem.

## Dependencies

### Earlier work and novelty boundary

The inspected earlier packets are inputs, not results re-claimed here:

- `contributions/global_crest_classification_20261127/NOTE.md` and its
  `GlobalCrest*` modules already prove the complete algebraic radial
  classification, actual endpoint gates, scalar coefficient above one
  third and its analytic limit. Its Boundary explicitly leaves proper
  path survival and conformal-width identification open.
- `contributions/actual_crest_foliation_20261126/NOTE.md` and
  `ActualCrestSupport` supply uniform actual-map convergence and phase
  bounds. In particular, `actual_selected_side_fourfold_injective`
  already proves joint injectivity on the open selected side. This
  packet extends the realization to closed leaves and the complete
  restriction history; it does not claim first discovery of that open
  injectivity statement. The strict-support upgrade is a compactness
  consequence of those archived estimates, not a new distortion theorem.
- `research/independent_audits/crest_transport_asymptotics_20261116/NOTE.md`
  gives finite certificates through period 16 and makes its conformal
  interpretation conditional on the missing path and analytic realization.
- The November 23 marked-slit path work proves independent A.1 width
  classes, not the present common-parent fourfold surviving foliation.
- The merged `marked_wave_supremum_limit_20261127` contribution studies
  an unrestricted parent-Wave supremum using Hausdorff trace length.
  That is a different extremal problem from this fixed circular parent
  and its selected descendants.

The source distinction between covering pushforward and the complete
native immersion pullback remains relevant: Kahn, Kapiamba and Lyubich,
*MLC for parabolically bounded primitive renormalization*,
[arXiv:2606.27272v1, Appendix A.3.2](https://arxiv.org/html/2606.27272v1).
The present literal path and metric theorems do not identify that entire
ideal-marking operation. No worldwide priority claim is made on the basis
of an archive search or a limited literature search.

## Lean validation and reproduction

The twelve new modules are registered in the unchanged weighted build,
the theorem index and the physical-source registry. Their canonical
sources compile in the pinned Lean 4.32.0 / Mathlib project. The repository's
transitive `Lean.collectAxioms` audit permits only `propext`,
`Classical.choice` and `Quot.sound`. No proof gaps, new axioms, native
computation trust escape, workflow modification or status-ledger edit
is introduced.

The completed local audit checks all 483 declarations across the twelve
new modules, including private and generated declarations, and reports
`AXIOM_AUDIT_PASS`. The complete contribution intake check reports
`RESULT: PASS` with one contribution packet and sixteen changed files.

The full build and audit are the existing CI gates at the PR's exact
head. Local reproduction, with the repository toolchain installed:

```sh
python code/contribute.py check
cd formalization/weighted
lake exe cache get
lake build ActualCrestTransportLimit
cd ../..
python code/verify_lean_coverage.py --audit weighted
```

The separate generic metric modules are supporting infrastructure. The
actual-object theorems are concentrated in `ActualCrestPaths`,
`ActualCrestParentPaths`, `ActualCrestComponents`,
`ActualCrestConformalChart`, `ActualCrestProperFamilies`,
`ActualCrestWidth` and `ActualCrestTransportLimit`.

## Boundary

`result: partial` is intentional; **leave NOV26_OPEN_CREST_LIMIT open**.
The proved advance removes the concrete whole-path survival and
conformal-metric identification premises for the selected smooth real-slit
families. It does not establish:

- Native KKL ideal markings, the complete immersion-pulled marking,
  identification of the actual Hubbard tree or its prime ends, or the
  claimed old-edge/crest interpretation.
- Identification of every `ActualTip` parameter with the distinguished
  primitive-component branch, its named kneading chart, or a least-period
  assertion not already present in that predicate.
- Physical survival for every finite index `p >= 17`. The new complete
  realization is uniform and **eventual**, with an unspecified threshold.
- An unrestricted Wave optimum, an arbitrary family of paths between
  boundary rails, or equality with the other packet's Hausdorff trace
  modulus API. The proved metric here is the standard derivative-arclength
  modulus of these explicit smooth curves.
- A new scalar limiting coefficient, a new certified decimal enclosure,
  H1-H4, UPTCR or MLC.

Only the upper q-side descendant family is counted; no extra factor from
a reflected family is inserted. The denominator uses the entire original
chosen circular parent, not the retained collar. The one rejected slit-QC
route is recorded in closed PR #256 and contributes no claimed result.

## Attribution

Earlier archive results and classical analytic tools are credited above.
AI assistance is disclosed in the frontmatter. Three parallel mathematical
and Lean reviews were performed within the same AI session; these are not
independent human review. Human review remains `none`. The contribution is
released under the repository's CC0 terms.
