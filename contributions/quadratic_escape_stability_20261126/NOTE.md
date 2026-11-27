---
ledger: H3_COERCIVITY
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-escape-stability-20261126"></a>

# Actual quadratic Böttcher coordinates and quantitative filled-set stability

## Claim

This packet adds 57 public Lean theorems about the actual monic centered
quadratic family, its escape potential, and its filled sets. The principal
results are a constructed normalized analytic coordinate at infinity,
harmonicity along escaping analytic families, and explicit Hausdorff and
conjugacy bounds for large parameters. Validation status and reproducible
commands appear under **Evidence**. All 57 public theorems compile in CI,
and the full transitive dependency audit passes. There are no new axioms
or proof placeholders.

Write `f_c(z) = z²+c`, with `f_c^n` its actual forward iterate. The existing
objects used throughout are

```text
G_c(z) = lim_{n→∞} 2^(-n) log(max(1, |f_c^n(z)|)),
K_c = {z : G_c(z)=0} = {z : the forward f_c-orbit of z is bounded},
P(c) = G_c(c) = 2 G_c(0).
```

The limit, the characterization of `K_c`, and the critical-value
normalization of `P` are existing proved facts, not hypotheses added here.
Their Lean names are `QuadraticEscape.orbit`, `escape`, `parameterEscape`,
and `QuadraticCantor.filled` / `filledMap`.

### 1. A normalized analytic coordinate at infinity

The complex correction and exterior function are constructed explicitly:

```text
S_c(z) = Σ_{n≥0} 2^(-(n+1)) Log(1+c/(f_c^n(z))²),
B_c(z) = z exp(S_c(z)).
```

For `C≥0`, `|c|≤C`, and `|z|≥2(1+C)`, the theorems establish convergence
of this series and

```text
2 S_c(z) = Log(1+c/z²) + S_c(f_c(z)),
B_c(f_c(z)) = B_c(z)²,
log |B_c(z)| = G_c(z),
|S_c(z)| ≤ (3/2)|c|/|z|²,
|B_c(z)/z − 1| ≤ 3|c|/|z|².
```

`B_c` is analytic on the open explicit exterior `|z|>2(1+|c|)`, and
`B_c(z)/z → 1` as `|z|→∞`, with no restriction on the direction of
approach. Its reciprocal expression

```text
g_c(w) = w exp(−S_c(1/w)) = 1/B_c(1/w)
```

extends analytically through `w=0`, with `g_c(0)=0` and `g'_c(0)=1`.
The proof produces an analytic local inverse with derivative one and
proves, in a neighborhood of zero,

```text
g_c(w²/(1+c w²)) = g_c(w)².
```

For every `c` there is finally an `R≥2(1+|c|)`, `R>0`, such that `B_c` is
analytic and injective on `{z : R<|z|}`. The injectivity radius is
existential; the functional equation and error estimates have the
explicit domain stated above. This is a local Böttcher coordinate at
infinity constructed from actual iterates.

### 2. Harmonicity of the actual escape potential

If `a,b : ℂ → ℂ` are analytic at `x` and `G_{a(x)}(b(x))>0`, then
`w ↦ G_{a(w)}(b(w))` is harmonic at `x`. In particular, `z ↦ G_c(z)` and
the critical-value potential `c ↦ P(c)` are harmonic and real analytic on
their respective positive loci. Each satisfies the circle mean-value
identity on every closed disk contained in that positive locus.

The proof derives a finite iterate entering a common exterior region
from positive escape. An entry time is not an additional assumption,
and the harmonicity theorem does not assume a Green or Böttcher coordinate.

### 3. Whole-orbit shadowing and quantitative structural stability

If `z∈K_c` and `|f_c^n(z)|≥s>1` for every `n`, then for **every** complex
parameter `d` there is `w∈K_d` with

```text
|f_d^n(w) − f_c^n(z)| ≤ |d−c|/(s−1)   for every n≥0.
```

For `|c|,|d|≥8`, set

```text
δ = |d−c|,
s = min(sqrt(|c|/2), sqrt(|d|/2)).
```

Existing orbit geometry proves the required separation by this `s`. The
new theorems then give

```text
HausdorffDist(K_c,K_d) ≤ δ/(s−1) ≤ δ.
```

There is no smallness condition on `δ` in the Hausdorff estimate. If also
`δ≤(s−1)²`, there is a homeomorphism `h : K_c ≃ₜ K_d` with

```text
h(f_c(x)) = f_d(h(x)),
|f_d^n(h(x)) − f_c^n(x)| ≤ δ/(s−1)   for every x∈K_c and n≥0.
```

The general theorem requires separation by the same `s>1` on both entire
filled sets and an error budget `0≤r≤s−1`, `δ≤(s−1)r`; its conclusion
has error `r`. The norm-two specializations remain available: if both
parameter norms are at least eight and `δ≤1`, the conjugacy moves every
point and every forward iterate by at most `δ`.

For every `ε>0` there is also an `R≥8` such that both parameter norms
being at least `R` implies

```text
HausdorffDist(K_c,K_d) ≤ ε |d−c|.
```

The proof chooses `R = max(8, 2(1+ε⁻¹)²)`. No threshold or coefficient is
asserted optimal.

## Argument

**Analytic construction.** On the stated exterior, norms of actual
iterates never decrease and `|c/(f_c^n(z))²|≤1/2`. The principal logarithm
therefore stays away from its branch cut. A geometric majorant gives
normal convergence, including for analytic parameter/point data on a
common exterior. The finite sum telescopes exactly to the repository's
orbit approximant. Passing to its already proved limit identifies the
real part of the correction with `G_c(z)−log|z|`.

Reindexing the convergent series proves its functional equation; taking
exponentials gives the Böttcher equation. The stronger logarithm estimate
gives the inverse-square error and normalization at infinity. In reciprocal
coordinates this normalization yields derivative one at zero. Analyticity
on a punctured neighborhood and continuity at zero give a removable
singularity. The analytic inverse function theorem then gives both inverse
identities and injectivity on a far exterior. No coordinate or inverse was
supplied as an input.

For an arbitrary escaping analytic family, boundedness would contradict
positive escape, so an actual iterate enters a common exterior. The
identity `G_c(f_c^N(z)) = 2^N G_c(z)` transports exterior harmonicity back
to the original family. Real analyticity and mean value follow from
Mathlib's harmonic-function theorems.

**Shadowing construction.** For any `x,u∈ℂ`, a suitable sign of a square
root gives `v²=u` and

```text
|x| |v−x| ≤ |u−x²|.
```

Choose the sign for which `|v−x|≤|v+x|`; the triangle inequality gives
`|v+x|≥|x|`, and factorization gives the estimate. Applying it backwards
preserves the error budget `r` because `(r+δ)/s≤r`. Induction produces
finite shadows. Their initial points form nested nonempty compact sets
inside the closed ball of radius `r` around the reference point. Their
intersection produces one shadow at every time. Its boundedness follows
from the bounded reference orbit and fixed error, proving actual membership
in `K_d`.

**Uniqueness and topology.** If two `d`-orbits remain within `r` of a
reference orbit separated from zero by at least `1+r`, the sum of their
positions has norm at least two. Exact quadratic difference factorization
then doubles their distance at each step. That distance is also bounded by
`2r`, so the initial points agree. The all-time shadow relation is closed
in `K_c×K_d`. Its two projections are continuous bijections from a compact
space, hence homeomorphisms. Their composition supplies `h`; uniqueness
after shifting time proves conjugacy. The Hausdorff estimate uses shadows
in both directions and requires no uniqueness assumption.

## Evidence

All five modules are registered in the weighted Lean project and in the
public theorem index. The registry lists all 57 public statements; the
compiled declaration audit also covers private and generated declarations.

| Module | Public theorems | Principal declarations |
| --- | ---: | --- |
| `QuadraticShadowRadius.lean` | 10 | `large_parameter_orbit_shadow_radius`, `filled_hausdorff_radius`, `filled_hausdorff_small_lipschitz_at_infinity` |
| `QuadraticOrbitShadowing.lean` | 5 | `infinite_orbit_shadow`, `filled_orbit_shadow`, `large_parameter_orbit_shadow` |
| `QuadraticJuliaStability.lean` | 8 | `orbit_shadow_unique_of_separation`, `filled_structural_conjugacy_of_separation`, `filled_structural_conjugacy_radius` |
| `QuadraticEscapeHarmonic.lean` | 16 | `exterior_escape_log_correction`, `escape_pair_harmonicAt`, `parameter_escape_harmonicAt`, `escape_circle_average` |
| `QuadraticBottcherExterior.lean` | 18 | `bottcher_semiconjugacy`, `bottcher_log_norm`, `bottcher_normalization`, `reciprocal_local_coordinate`, `bottcher_exterior_coordinate` |

The shadowing and stability declarations use namespace `QuadraticCantor`.
The analytic modules use namespaces `QuadraticEscapeHarmonic` and
`QuadraticBottcherExterior`, respectively.

**Verified proof revision:**
[`05a748aecf686cd2689e786df9850f690c73f944`](https://github.com/dovvnloading/loops-research-archive/commit/05a748aecf686cd2689e786df9850f690c73f944).
The full weighted build succeeded (8,974 build jobs), and its transitive
dependency audit passed in
[run 45920174296](https://github.com/dovvnloading/loops-research-archive/actions/runs/45920174296).
The audit's exact module summaries are:

```text
AXIOM_AUDIT weighted QuadraticBottcherExterior: 54 declarations, 52 theorems; allowed axioms only
AXIOM_AUDIT weighted QuadraticEscapeHarmonic: 32 declarations, 30 theorems; allowed axioms only
AXIOM_AUDIT weighted QuadraticJuliaStability: 9 declarations, 9 theorems; allowed axioms only
AXIOM_AUDIT weighted QuadraticOrbitShadowing: 5 declarations, 5 theorems; allowed axioms only
AXIOM_AUDIT weighted QuadraticShadowRadius: 16 declarations, 16 theorems; allowed axioms only
AXIOM_AUDIT_PASS weighted: 152 modules, 3314 declarations
```

The 116 audited declarations in these five modules include private helpers
and generated declarations; the public theorem count is 57. The only
permitted axioms are Lean's existing `propext`, `Classical.choice`, and
`Quot.sound`. The source scan registered all 195 Lean files and found no
prohibited proof tokens. The root and standalone Lean builds and audits,
as well as the research checks, passed in
[run 45920174230](https://github.com/dovvnloading/loops-research-archive/actions/runs/45920174230).
Contribution intake also passed, and all reported workflow runs on the
verified proof revision were green. The final packet update changes only
documentation; the Lean sources and proof registration are unchanged.

The draft PR was opened before the proofs were developed. Successive
proof checkpoints, including compiler repairs, were committed into it.
The first five-theorem checkpoint already passed the full build and audit
at `6c082ded253ba72425bcc5784e4882b7a5e1bf1d`
([run 45917813979](https://github.com/dovvnloading/loops-research-archive/actions/runs/45917813979)).

Reproduction from the repository root:

```sh
python code/contribute.py check --base origin/main
python -B code/verify_lean_coverage.py
```

With the pinned Lean 4.32.0 toolchain installed:

```sh
cd formalization/weighted
lake exe cache get
lake build
cd ../..
python -B code/verify_lean_coverage.py --audit weighted
```

Local Lean compilation was unavailable: the pinned compiler artifacts
and Mathlib cache exceeded this workspace's available disk capacity.
GitHub Actions is the compilation authority. No workflow, toolchain,
dependency version, audit policy, or protected status record was modified.

## Dependencies

- [QuadraticEscape.lean](../../formalization/weighted/QuadraticEscape.lean):
  actual iterates, orbit approximants, convergence, functional equation,
  continuity, and `escape_zero_iff_bounded`.
- [QuadraticCantorGeometry.lean](../../formalization/weighted/QuadraticCantorGeometry.lean),
  [QuadraticCantorSplitting.lean](../../formalization/weighted/QuadraticCantorSplitting.lean),
  and [QuadraticCantorExpansion.lean](../../formalization/weighted/QuadraticCantorExpansion.lean):
  the actual `filled` set and self-map, compactness, square roots, invariant
  filled sets, and proved lower norm bounds for `|c|≥8`.
- Pinned Mathlib v4.32.0 at
  `81a5d257c8e410db227a6665ed08f64fea08e997`: normal convergence of analytic
  series (`Complex.differentiableOn_tsum_of_summable_norm`), complex
  logarithm and exponential estimates, harmonic real parts and logarithms,
  removable singularities, analytic local inverses, compact intersections,
  compact-to-Hausdorff homeomorphisms, and Hausdorff distance estimates.
  The exact transitive dependencies are checked by the existing CI audit.

The target obligation is H3_COERCIVITY, stated at M6 in
[`master_transition.md`](../../research/mlc_unified/master_transition.md).
The earlier [planar fill limit packet](../h3_planar_fill_limit_20261126/NOTE.md)
provides background on one-sided planar filling stability; its conclusions
are not used as substitutes for the actual-orbit proofs here. This packet
adds analytic and stability inputs for actual polynomial objects. It does
not supply the compactness theorem for marked renormalizations demanded
by the full obligation.

## Boundary

**H3_COERCIVITY remains open. No ledger status change is requested.**
Its full statement concerns nondegeneration of analytic carriers, branch
graphs, relative covers, protected prime ends, response forms, and Value
features under the calibrated-potential, incidence, and congestion
hypotheses. These theorems do not derive that admissibility from those
hypotheses. They also do not prove MLC or any of H1 through H4.

The Böttcher chart is local at infinity; no extension throughout the
entire escaping basin, external-ray landing theorem, boundary extension,
or uniform marked-family chart is asserted. Structural conjugacies are
for fixed parameter pairs in the stated separated regime. Joint parameter
dependence, holomorphic motion, external markings, and renormalization-carrier
compactness remain unproved here. The large parameter estimates do not
cover the Mandelbrot boundary.

The contribution is a formal extension of the archive's actual quadratic
dynamics development. These are classical kinds of complex-dynamical
results with explicit estimates; no worldwide mathematical priority or
claim of a previously unknown general theorem is made.

## Attribution

Matthew Robert Wesney's research archive and its existing quadratic
escape, Cantor geometry, and planar compactness developments; the Lean
and Mathlib contributors. OpenAI GPT-6 Astra Pro developed these proofs
and documentation with parallel proof and infrastructure review. No human
mathematical review has been performed in this session.
