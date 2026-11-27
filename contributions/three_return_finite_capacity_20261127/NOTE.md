---
ledger: NOV26_OPEN_3P_MODULUS
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="three-return-finite-capacity-20261127"></a>

# Finite two-sided extremal length for actual three-return collars

## Claim

Work in progress. The target is a new quantitative nondegeneration theorem for the actual canonical physical three-return domains at every selected integer period p >= 3. The intended advance is an explicit inner-disk inclusion and a strictly positive lower bound for the existing Lipschitz Dirichlet capacity, complementing the archived upper bound.

The general analytic lemmas below have compiled locally. The all-period inradius and final physical assembly are still undergoing validation; no ledger closure is claimed at this proof-development checkpoint.

## Evidence

The merged uniform_three_return_collar_20261127 packet already constructs the actual canonical proper degree-two return and proves that its reciprocal variational capacity exceeds 1/60. It explicitly leaves capacity positivity and finiteness of that reciprocal unproved. This contribution will build on that construction rather than repeat it.

The new Lean source will be registered in the existing weighted project, public-theorem index and source table. Validation will use pinned Lean 4.32.0 and the existing CI transitive axiom audit.

### Proof-development checkpoint

ThreeReturnInradius.lean now contains the proposed all-period theorem that the closed normalized disk of radius 1/40 lies in the literal central three-return source. Its stronger analytic estimate is |F^3(z)| < 4/25 on that whole disk, leaving target margin 1/150. The finite p=3,...,16 integer certificate has been independently evaluated and kernel-checked locally with decide +kernel. The real/complex soundness proof, analytic tail and physical scaling are present in the source and are undergoing compilation; they are not yet claimed verified. The lower-capacity and full rectifiable-curve extremal-length arguments are being developed separately.

A reusable pinned Lean 4.32.0 installation and Mathlib cache were located after the initial draft. Local proof checking is available; the existing CI remains the final authority.

### Compiled analytic checkpoint

CollarCapacityLower.lean has compiled locally with no warnings. For every compact or noncompact inner plate containing B(0,r), every r,R > 0, and the unchanged all-Lipschitz plate-potential class, it proves capacity(K,B(0,R)) >= r/R and reciprocal capacity <= R/r < infinity. The argument uses almost-everywhere horizontal slices, the Lipschitz fundamental theorem of calculus, the actual planar derivative, and the measure-preserving real product coordinates. No uniform bound on the competitors' Lipschitz constants is assumed.

CollarExtremalLength.lean has also compiled locally. It defines the standard two-modulus using every measurable nonnegative conformal density and every continuous rectifiable joining curve, with metric length integrated in Mathlib's unit-speed arclength parameter. The explicit whole-disk metric proves joining-curve extremal length >= 1/(100*pi) whenever the inner plate lies inside the existing physical radius 3*d/20 and the target is D(0,d/6). This is a separate curve-family theorem, not a renamed Dirichlet capacity. A full horizontal joining-family argument is now being developed to give its upper bound as well.

### Compiled full-family checkpoint

CollarMetricEnergy.lean, CollarStraightLength.lean and CollarHorizontalFamily.lean have now compiled locally. For a compact plate K with B(0,r) subset K subset B(0,R), 0<r<R, the new theorem bounds the standard two-modulus below by r/R and joining-curve extremal length above by R/r. It extracts each straight joining curve after the last contact with K, computes its exact natural arclength integral, and applies Holder and Fubini to every admissible Borel-measurable extended nonnegative density, including densities of infinite area. No regularity of the inner boundary is assumed. At physical radii r=d/40 and R=d/6 this gives the intended upper bound 20/3.

CI exposed three elaboration/parser issues in the all-period inradius proof. Those source errors have been repaired in this checkpoint; the inradius and final actual-domain assembly remain under validation. All new claims continue to be distinguished from proposed statements until their Lean checks finish.

## Dependencies

NOV26_OPEN_3P_MODULUS; NOV26_TIP_THEOREM. Existing ThreeReturnAnnulus, ThreeReturnDomain, UniformThreeReturn and UniformThreeReturnRenormalization modules, together with the actual finite and analytic-tail parameter estimates they consume.

## Boundary

This draft claims no closure of the ledger obligation. Positive capacity for the chosen actual collar is distinct from an identification with classical annulus modulus, and no uniform statement about arbitrary further domain shrinking is assumed. The exact remaining modulus comparison and physical marking hypotheses will be recorded after the proof. No MLC, H1-H4, arbitrary-depth or canonical KKL Wave conclusion is claimed. Status records and workflows remain unchanged.

## Attribution

The actual all-period domain construction and the trial-energy upper bound belong to the preceding archived contribution. This work targets the explicit nondegeneration gap identified in its Boundary section. OpenAI ChatGPT, GPT-6 Astra Pro performs proof search, Lean development and validation. Human review: none. Original contributions are released under the repository's CC0 terms.
