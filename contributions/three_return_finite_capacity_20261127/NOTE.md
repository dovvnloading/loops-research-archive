---
ledger: NOV26_OPEN_3P_MODULUS
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

# Finite two-sided capacity for actual three-return collars

## Claim

Work in progress. The target is a new quantitative nondegeneration theorem for the actual canonical physical three-return domains at every selected integer period p >= 3. The intended advance is an explicit inner-disk inclusion and a strictly positive lower bound for the existing Lipschitz Dirichlet capacity, complementing the archived upper bound.

No new theorem is claimed verified at this initial draft checkpoint.

## Evidence

The merged uniform_three_return_collar_20261127 packet already constructs the actual canonical proper degree-two return and proves that its reciprocal variational capacity exceeds 1/60. It explicitly leaves capacity positivity and finiteness of that reciprocal unproved. This contribution will build on that construction rather than repeat it.

The new Lean source will be registered in the existing weighted project, public-theorem index and source table. Validation will use pinned Lean 4.32.0 and the existing CI transitive axiom audit.

## Dependencies

NOV26_OPEN_3P_MODULUS; NOV26_TIP_THEOREM. Existing ThreeReturnAnnulus, ThreeReturnDomain, UniformThreeReturn and UniformThreeReturnRenormalization modules, together with the actual finite and analytic-tail parameter estimates they consume.

## Boundary

This draft claims no closure of the ledger obligation. Positive capacity for the chosen actual collar is distinct from an identification with classical annulus modulus, and no uniform statement about arbitrary further domain shrinking is assumed. The exact remaining modulus comparison and physical marking hypotheses will be recorded after the proof. No MLC, H1-H4, arbitrary-depth or canonical KKL Wave conclusion is claimed. Status records and workflows remain unchanged.

## Attribution

The actual all-period domain construction and the trial-energy upper bound belong to the preceding archived contribution. This work targets the explicit nondegeneration gap identified in its Boundary section. OpenAI ChatGPT, GPT-6 Astra Pro performs proof search, Lean development and validation. Human review: none. Original contributions are released under the repository's CC0 terms.
