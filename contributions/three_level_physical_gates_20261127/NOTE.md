---
ledger: NOV26_OPEN_DEPTH_GATES
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="three-level-physical-gates-20261127"></a>

# Three-level physical quadratic return gates — research in progress

## Claim

This draft attacks the unbounded three-level subcase of NOV26_OPEN_DEPTH_GATES.
The intended theorem constructs a parameter of the literal quadratic polynomial
with three nested proper degree-two returns and a complete terminal gate under
explicit separation of the three return periods. No new theorem is claimed
until its Lean declaration compiles and the repository CI audits its dependencies.

## Evidence

Baseline: e8d82717b184b5f4e46c34a46b1445fc75f33a1c.

The latest two-level theorem in TwoLevelPhysicalGates constructs actual nested
returns for q >= 17 and p >= 10*q + 30. Its boundary explicitly leaves arbitrary
finite depth open. The proposed next step prepends a further large outer period
to the entire signed two-level parameter bracket, retaining complete complex
orbit estimates between intermediate returns and paying for the changing
normalization scales. The planned three-level shooting argument must control
the original polynomial through the full 6*p*q*r horizon.

This initial commit records the target before proof development. Subsequent
commits will contain the proof, failures that change the route, and CI evidence.
The local environment has no Lean executable and insufficient disk for a Lean
and Mathlib installation; the unchanged repository Lean CI will judge compilation.

## Dependencies

Existing compiled infrastructure: NearTwoShooting, TwoLevelOuterChart,
TwoLevelReference, TwoLevelPerturbation, TwoLevelSelection, and
TwoLevelPhysicalGates. These are inherited results, not claimed as new work.
Ledger context: NOV26_DEPTH3 and the open NOV26_OPEN_DEPTH_GATES.

## Boundary

The obligation remains open. This draft does not claim arbitrary-depth tuning,
canonical kneading identification, KKL prime ends, optimal widths, H1–H4, MLC,
or literature-wide novelty. A plan and a green intake check are not a result.
The substantive increment, if proved, must be an unconditional theorem about
the actual three-level polynomial family, beyond the archived two-level case.

## Attribution

Builds on the archive's all-period shooting, two-level physical-domain
construction, and Mathlib. Proof development and adversarial scope review:
OpenAI ChatGPT GPT-6 Astra Pro. Human review: none.
