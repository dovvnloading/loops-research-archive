---
ledger: NOV26_OPEN_OPTIMAL_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="parent-wave-exhaustion-20261128"></a>

# Research claim: quantitative exhaustion of the actual parent Wave optimum

## Claim

Draft investigation; no new result about the optimum is claimed yet. The target is a genuinely
stronger result about the complete physical parent supremum in
ActualParentSupremum.physicalParentWidth, beyond the archived convergence
theorem and its O(1/p) error estimate.

## Evidence

The existing archive already proves convergence for every sequence of actual
signed tips, exact dilation to the physical slit disks, full Borel Wave
transport, and a 3*pi/N bound for escaping families. Those results are inputs,
not claimed progress here.

The attack is to determine whether the geometry of the selected left relative
class yields a sharper finite-domain exhaustion estimate, or an exact
variational obstruction to such an estimate. A valid endpoint must use the
existing complete supremum of all admissible parent Waves, with no optimizer,
foliation, or native geometric identification assumed as the conclusion.

Local Lean 4.32.0 is available. Every proposed final theorem will be compiled
in the unchanged weighted project and audited by the existing CI.

### Compiled development checkpoint

Eighteen auxiliary modules have compiled locally and are registered for CI:

- ParentWaveLeftCrossing derives an actual interior intersection with the
  left real ray from the existing ParentLeaf relative-homotopy definition.
  The crossing is proved, not supplied as an additional assumption.
- ParentWaveHalfPlane proves an unconditional bound for the entire canonical
  parent supremum by one half of the finite, all-path upper-half-plane
  condenser modulus. Its metrics include all measurable extended densities
  and its paths include nonrectifiable traces.
- ParentWaveReflection constructs complete simple parent leaves by reflecting
  upper crossing arcs, and proves that a Borel family with disjoint complete
  traces produces a genuine Borel ParentWave with disjoint interiors.
- ParentWaveElliptic constructs an injective primitive of the literal
  transformed elliptic differential on the first quadrant. The strict
  derivative-sign argument proves injectivity there.

- ParentWaveReflectionModulus proves the exact modulus identity for those
  reflected Borel families: the reflected modulus is one half of the original
  upper-family modulus, for all measurable densities and Hausdorff trace lengths.
- ParentWaveEllipticBoundary proves continuous extension to the full finite
  closed quadrant, including both square-root vertices.
- ParentWaveEllipticInfinity proves a uniform limit at infinity of the actual
  primitive by analytic regularization in the reciprocal coordinate.
- ParentWaveEllipticChart links the quadrant coordinate to the literal upper
  half-plane differential and proves that its squared norm is exactly the
  absolute value of the physical cubic differential.
- ParentWaveRectangle proves the image criterion using the actual finite
  boundary and uniform infinity limit; its hypotheses have not all yet been
  verified for the elliptic chart.

- ParentWaveEllipticSides identifies all four actual boundary derivatives,
  their signs, the constant coordinates, and the positive finite side lengths.
- ParentWaveBoundaryInverse derives continuous inverse extensions from finite
  boundary continuity, injectivity, and the proved uniform limit at infinity.
- ParentWaveTraceLength connects canonical simple traces to the actual arclength
  parameter; finite Hausdorff length implies rectifiability, rather than being
  replaced by a rectifiability assumption.
- ParentWaveLocalLength derives weighted Hausdorff-length change inequalities
  from arbitrarily sharp local Lipschitz bounds. This covers all measurable
  densities and arbitrary, possibly nonrectifiable and noninjective traces,
  with a relative-domain form for boundary contacts.
- ParentWaveRectangleModulus computes both the exact literal rectangle
  foliation modulus and the modulus of all continuous rectangle crossings.
- ParentWaveRectangleFoliation proves that an inverse chart with the stated
  endpoint data produces an actual disjoint Borel upper family.

- ParentWaveEllipticImage proves that the literal primitive maps onto the
  complete open rectangle, with all finite and infinite boundary hypotheses
  discharged from the differential.
- ParentWaveUpperBoundary constructs the actual holomorphic continuation
  across each regular real boundary point, with exact cubic derivative norm.
- ParentWaveTraceEndpoints proves exact invariance of the canonical modulus
  when the two endpoint atoms of every trace are removed.

The second checkpoint's full weighted project build passed in GitHub Actions;
its subsequent transitive axiom audit was canceled. A complete
successful audit is still required before the research result can be delivered.

These are intermediate proof steps toward the candidate in ATTACK.md. They
do not establish the optimum, its value, or a sharper rate, and are not
presented as satisfying the requested research result on their own.

## Dependencies

- NOV26_OPEN_OPTIMAL_LIMIT, an open research-update obligation in ledger.json.
- The marked_wave_supremum_limit_20261127 packet and its eleven Lean modules.
- research/independent_audits/maximal_native_wave_20261123/H3_WIDTH.md,
  to distinguish archived written results from new results.

## Boundary

No improved rate, optimizer, exact width, or status change is claimed
by this draft. The physical parameter selection and native ideal
marking boundaries of the imported work remain explicit. A theorem about a
substitute quantity will not count without a proved link to physicalParentWidth.
MLC and H1-H4 remain open.

## Attribution

The archive's existing full-supremum convergence, geometric compression,
modulus transport, and physical orbit estimates are prior work. This draft
records the next research claim before proof development.
