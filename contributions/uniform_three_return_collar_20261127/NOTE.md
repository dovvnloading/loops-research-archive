---
ledger: NOV26_OPEN_3P_MODULUS
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; Lean proof development and independent AI scope review
human_review: none
---

# Uniform selected three-return collars

Ledger statement being addressed:

> Uniform physical three-return modulus: Two strict Rouche margins do not bound all arbitrarily shrunk 3p collars by one universal physical modulus (F04).

## Claim

This draft investigates a canonical collar for the actual normalized three-return, with a fixed outer disk of radius 3/10 and a source containment radius of 13/50. The intended new step is simultaneous control of the full intermediate phase domains, so that no unquantified shrinking is needed. No completed theorem is claimed in this initial commit.

## Evidence

Preliminary exact interval evaluation at the smaller source circle gives a strictly positive boundary margin for each finite period p=3,...,12. The existing all-period coefficient and remainder estimates also give a positive margin there. The mathematical and Lean work will verify these bounds, the selected connected component, the intermediate phase containment, and the resulting annular separation.

All accepted results will be stated as Lean theorems in the pinned repository project and checked by the existing CI and transitive-axiom audit. Progress and proof revisions will be committed to this pull request.

## Dependencies

- NOV26_TIP_THEOREM and the actual finite and all-period primitive-tip estimates cited by research/tip_family_theorem/AUDIT.md, finding F04.
- Existing exact real interval and complex remainder infrastructure in the repository.
- PR #238 contains independent all-period actual-parameter construction. Any use of that work will be explicitly declared as a dependency; its crossing-curve result is not this contribution's claim.

## Boundary

The ledger row remains open while this is a draft. A uniformly chosen collar does not give a bound for every arbitrarily shrunk collar. The exact relation between the intended canonical result and the row will be recorded after the proof. No canonical KKL marking, Wave width, MLC, or H1-H4 conclusion is claimed. No status-record or workflow change is proposed.

## Attribution

The existing archive supplies the tip normalization, coefficient enclosures, and strict outer Rouché margins. This work targets the additional uniform inner containment and simultaneous phase control, not a repetition of those estimates. The contribution uses the repository's CC0 terms.
