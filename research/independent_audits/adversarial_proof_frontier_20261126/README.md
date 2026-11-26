# Adversarial proof frontier — 2026-11-26

Base main: 59fff186a31bf7def8d7c7e2d60519190585c3bd. PR #176. AI assistance: OpenAI GPT-6.2 (research selection, proof search, proof drafting, adversarial self-review and checker implementation). No independent human specialist review or formal kernel verification yet. No ledger or global gate promotion.

## Scope and findings

Target: H4_RIGIDITY, specifically the changing-ground interface of [parameter ground transfer](../parameter_ground_transfer_20261126/NOTE.md) and [sharp boundary frontier, §4](../../frontier/sharp_boundary_frontier_20261126/NOTE.md). That source gave order estimates at the main cusp with a large multiplicative gap. We focus on the actual quadratic parameter plane, not an abstract marked-width model. H4 and MLC remain OPEN.

Let c₀=1/4, G the parameter Green function normalized by log|c| at infinity, D_u={G<u}, L=log(1/u), a=π log(2)/L. The submitted written results are:

| Result | Proof | Scope |
|---|---|---|
| Ω_(u,α)=(D_(u^α)−c₀)/a² converges to C∖[α⁻²,+∞) for α>0 | [CUSP_KERNEL](CUSP_KERNEL.md) | Actual positive-level kernel, locally uniform with varying α in compact intervals |
| r_(u^α)(c₀)=4π²(log 2)²/(α² L²)·(1+O(L⁻²/³)) | [CUSP_RATE](CUSP_RATE.md) | Explicit subdomain proof; superseded by stronger error below |
| r_(u^α)(c₀)=4π²(log 2)²/(α² L²)·(1+O(log L/L)) | [CUSP_HARMONIC_RATE](CUSP_HARMONIC_RATE.md) | Localized half-plane harmonic barrier; no matching error lower bound |
| Full scaled Green-transfer kernel, regular part and nonpolar compact energy difference limit | [CUSP_GROUND](CUSP_GROUND.md), Theorems A–B | Uniform over compact windows separated from the smaller limiting slit |
| Physical closed disks entirely in the main cardioid, diameter comparable to L⁻³, distance O(L⁻²) from c₀, with transfer loss log L+O(1) | [CUSP_GROUND](CUSP_GROUND.md), Theorem C | Actual counterexample to uniform extension of pointwise cusp control; not a nested tower |
| Real first escape iteration J=π/h+O(1); explicit bound 124, log(1/G(c₀+h²))=π log(2)/h+O(1) | [TRANSIT_CANCELLATION](TRANSIT_CANCELLATION.md) | Signed discretization-error cancellation, sharper radial bracket O(1/L) |

The cusp-centered loss for s=u^β, t=u^α (0<α<β) tends to 2 log(β/α), whereas actual nearby nonpolar continua have loss log L+O(1). Thus a scalar cusp estimate alone does not control moving compacts in the H4 criterion.

## Adversarial checks

- Escape normalization: G=2g_c(0); the shift by the first escaping iteration is exactly 2^(1−J), so π log 2 is the exponent, and the dilation scale is its square.
- Uniform complex inclusion does not follow from a real path alone. The radial majorant includes the entire subthreshold disk; the exact fixed-point multiplier inequality includes every fixed compact off the positive ray.
- Kernel convergence is not Hausdorff convergence of the entire boundary. Compact inclusion and exclusion at every point of the limiting slit are established for every subsequence.
- The slit conformal radius is 4b, not b, from the explicit normalized map.
- The harmonic barrier compares Green functions on the actual intersection component. Boundary limsup and positivity suffice even at nonregular boundary points; the singularity cancels at the pole; infinity is controlled by the half-plane Green kernel. No local connectivity assumption enters.
- The full Green difference includes the diagonal; divided differences converge there by derivative convergence. Uniform comparison of infima does not presume the same equilibrium measure for distinct grounds.
- The near-cusp witness lies in the actual attracting cardioid (strict multiplier inequality on the entire disk). Its threshold is the actual real G-level, not a numerical surrogate. It approaches the excluded smaller slit endpoint, so is not a counterexample to the compact-window theorem.
- The real transit signed correction telescopes through log(d_(j+1)/d_j), including the last overshooting step. The bounded error does not imply an unrestricted limit of the integer-clock correction.

## Exact finite regression

From repository root:

    python -B research/independent_audits/adversarial_proof_frontier_20261126/check_arithmetic.py

The checked file has Git blob SHA 60b06b2fb24b0850792b0d81e733b45d0cebf4b5 and SHA256 54b9462db5ff02007b2702f481000fe3ff6cadc8f2a1096a4ce052339a05a333. Python 3.13.5 locally; no external dependencies, floats, random seeds or numerical tolerances. The executed output certified first crossings N and J for h=2^(-k), k=4,…,12, by outward dyadic interval iteration at resolution 2^-192, aborting on ambiguous crossing; rational Machin arctangent brackets for π check both explicit error bounds. J values: 48, 99, 199, 400, 802, 1607, 3215, 6432, 12866. The exact rational conformal-inclusion test checked 6,336 samples (2,628 outside the disk, all satisfying the cardioid test) and 396 model witness samples. The latter are algebraic coordinate tests, not computed native Green crossings. The checker tests arithmetic, not the continuum kernel, Poisson, or energy proofs. CI workflow: [adversarial cusp frontier arithmetic](../../../.github/workflows/adversarial-cusp-frontier-20261126.yml). No full archive test or Lean run is claimed. Source registration is METADATA only.

## Attribution and unresolved frontier

The leading real parabolic passage limit π/h is classical; the proof notes give attribution to established literature and an elementary proof rather than claim priority. The attracting-basin theorem and quadratic parameter uniformization are classical Fatou/Douady–Hubbard inputs; Carathéodory kernel convergence and the Green/Poisson formulas are standard complex analysis. The earlier archive work and its source locators are cited where used; this pass has not reopened every primary-source proof or audited all transitive H4 dependencies. No literature-priority claim.

The next genuine geometric task is to identify a positive-level kernel or uniform compact-window separation for actual moving protected parameter nests, especially the unbounded satellite regime. An exact theorem at the single main cardioid cusp is not a substitute for that result. The physical counterexample demonstrates why a proof based merely on conformal radius at a marked central parameter is insufficient. The proof target was selected by the assistant from the archive's live obligations; other active fronts were not comprehensively audited. Main has not been modified or merged by this investigation. H1–H4, UPTCR and MLC remain open.
