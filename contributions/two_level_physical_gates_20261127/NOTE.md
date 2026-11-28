---
ledger: NOV26_OPEN_DEPTH_GATES
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="two-level-physical-gates-20261127"></a>

# Two-level physical gates: research in progress

## Claim

This draft claims the open obligation for investigation. No new mathematical result is claimed at this checkpoint. The proposed target is a uniform physical gate theorem for an infinite two-level class of actual quadratic returns with both return periods sufficiently large.

## Evidence

Baseline: main commit 665e5f942d6b39902272fe6d8ca2dee6fbca8a6f.

The hard step is to control the second normalized return of a nonquadratic analytic first return, including the actual parameter selection and complete intermediate complex domains. A second application of a theorem whose input is the literal map z^2+c is invalid.

The existing single-level Lean development (NearTwoShooting, NearTwoTip, LimitingCrestQuadraticReturn, ThreeReturnEstimates, and UniformThreeReturnRenormalization) will be inspected for a perturbatively invariant class. Finite deeper grids, classical straightening, an assumed uniform error, and generic implication lemmas are not accepted as the desired new result.

All resulting accepted mathematics must be Lean theorems in the existing project, registered with the contribution tooling, built by the unchanged CI, and passing the transitive dependency audit. Work and failed routes will be committed here as they develop.

### Research checkpoint: a separated-period two-level construction

Write A_p(c) for the exact quadratic coefficient of f_c^p at zero and
G_c(u)=A_p(c) f_c^p(u/A_p(c)). Its constant term is
a(c)=A_p(c) f_c^p(0). The first chart must reach a=-2; the archived
return-value endpoint 12*4^(-p) only guarantees -a>1.8. We instead
use 14*4^(-p), which gives -a>2.1 using the existing inverse-product
bound. This supplies a real first-return chart crossing any required
second-level parameter interval near -2.

The complete (untruncated) polynomial remainder suggests the uniform
estimate |G_c(u)-(u^2+a(c))| <=128*4^(-p) on |u|<=12/5.
On the reference q-return chart, the critical scale lies between
7*4^(-q) and 12*4^(-q). A finite-iterate bound with expansion factor 5
then permits a conservative separated-period condition, currently
being checked in Lean, of p>=10*q+30. This is intended to
control every intermediate complex point and the six-return shooting
relation, not merely endpoint arithmetic.

The second scale has opposite sign in physical coordinates:
D=G_c^q(0)>0 but f_c^(pq)(0)=D/A_p(c)<0. The new coordinate identities
retain that sign, and all physical radii must use its absolute value.
The target is a whole physical central return disk with exact two-sheet
fibers and a crest crossing on every radius in the fixed interval,
after selecting a zero of the actual signed 6pq-versus-3pq relation.

These estimates and existence claims are work in progress at this
checkpoint. No theorem is promoted by this derivation alone.

### Source checkpoint: unvalidated proof development

The TwoLevelOuterChart, TwoLevelReference, TwoLevelPerturbation,
TwoLevelConjugacy, TwoLevelSelection, TwoLevelCollisions, and
TwoLevelGateDomain modules now contain the proposed Lean proofs.
These sources are committed for review and compiler feedback. They
have not yet compiled, so their declarations are not certified results.
Local Lean 4.32.0 and the pinned Mathlib cache are installed; sequential
compilation of the archived dependencies is in progress.

The first CI build (commit e85df79) compiled TwoLevelReference and
reported explicit elaboration errors in the remaining upstream modules.
The next source checkpoint fixes those errors and adds the literal outer
pullback component, its half-target boundary barrier, and its exact
fiber census. The proposed final family is still unvalidated.

## Dependencies

NOV26_DEPTH3. Existing depth-three packet, the literal all-period first-return estimates, and the source distinction between physical prescribed collars and optimal polynomial-like moduli.

## Boundary

The ledger obligation remains open. This checkpoint is an investigation, not a proved partial result. No physical depth-two or arbitrary-depth gate, parameter uniqueness, tuning identification, KKL marking, Wave-width theorem, H1–H4 conclusion, or novelty priority is asserted.

## Attribution

The baseline archive and its cited work provide the starting point. AI mathematical development and independent adversarial review; no human review.
