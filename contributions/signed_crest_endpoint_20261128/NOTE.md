---
ledger: NOV26_OPEN_CREST_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical development, Lean implementation and adversarial review
human_review: none
---

<a id="signed-crest-endpoint-20261128"></a>

# Signed displacement of the actual maximal crest endpoint

## Claim

Draft claim; no new theorem is certified at this initial checkpoint.

The target is the literal maximal endpoint `r_p` already selected by
`GlobalCrestClassification.actual_complete_parent_classification`,
with its existing complete physical realization in
`ActualCrestTransportLimit.RealizedCollar`. The proposed new theorem
determines a strictly positive displacement from the limiting endpoint
at order `4^(-p)`, with sufficiently tight constants to prove eventual
strict decrease of the actual endpoints across consecutive periods.

The intended final inequalities have no supplied perturbation or
unidentified surrogate endpoint: they quantify the existing actual
polynomial return, the unique root of its terminal gate, the complete
admissible radius interval, and the realized physical collar.

## Evidence

Started from main `637266b909d5e7566d8e39141f3b135e3405f38f`.
The previous closed geometric-child attempt #272 is not the base of this
branch and is not counted as progress here.

The promising mechanism retains the quartic coefficient of the complete
physical return. It requires a bound of order `q^2` on every remaining
term, where `q=4^(-p)`. The actual signed critical relation then controls
the correlated shift of the quadratic coefficient. Combining both
effects in the actual terminal collision gives a signed radial response.
An unsigned map error or the previously proved sign of the quadratic
coefficient alone does not determine that response.

High-precision exploratory calculations indicate a positive radial
response, but they are not proof evidence. All final inequalities and
quantified constants must be proved in the repository's Lean 4 project
and pass the unchanged CI build and transitive proof audit.

## Dependencies

- Existing actual parameter existence and the physical signed-tip
  recognition and uniqueness theorems on main.
- `GlobalCrestClassification` for the unique actual endpoint and exact
  full-parent admissible set; `GlobalCrestPhysical` for its original-plane
  collision and proper-return component membership.
- `UniformCrestTransport` and `ActualCrestTransportLimit` for the complete
  physical collar and all-density width identities.
- `ActualCrestSignedDrift` for the prior auxiliary coefficient sign;
  `LimitingCrestQuadraticReturn` for the complete nonlinear recurrence.

## Boundary

The target is the archive's selected maximal circular collar, not an
unrestricted KKL Wave optimum. The already proved endpoint convergence,
every-index persistence, and signed auxiliary coefficient drift are
prior work, not new claims of this packet. No result is certified at
this checkpoint. The ledger status remains open.

## Attribution

The previous actual endpoint, full-parent classification, physical
modulus realization, and signed return-coefficient results are credited
to the existing actual-maximal-crest, global-crest-classification,
actual-crest-path-width and uniform-crest-transport contributions.
The proposed new content is the correlated quartic-to-physical-endpoint
response and a signed sharp-order theorem for those same actual endpoints.
