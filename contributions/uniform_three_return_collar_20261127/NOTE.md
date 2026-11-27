---
ledger: NOV26_OPEN_3P_MODULUS
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; Lean proof development and independent AI scope review
human_review: none
---

<a id="uniform-three-return-collar-20261127"></a>

# Uniform selected three-return collars

Ledger statement being addressed:

> Uniform physical three-return modulus: Two strict Rouche margins do not bound all arbitrarily shrunk 3p collars by one universal physical modulus (F04).

## Claim

This draft investigates a canonical collar for the actual normalized three-return, with a fixed outer disk of radius 3/10 and a source containment radius of 13/50. The intended new step is simultaneous control of the full intermediate phase domains, so that no unquantified shrinking is needed. The first proof modules now establish the full annular exclusion and whole-disk phase estimates for every constructed actual signed tip of period p >= 17, together with a uniform physical Dirichlet-energy bound. The canonical domain and exact fiber conclusions are being integrated.

## Evidence

The active normalization is F(z)=f_c^p(d*z)/d with d=f_c^p(0)>0, outer radius 1/6 and inner radius 3/20. The source component is selected from the full inverse image under F^3. These radii replace the preliminary 3/10 and 13/50 coefficient-normalization calculation above.

`ThreeReturnEstimates.lean` proves for every actual signed tip constructed by PR #238, for p >= 17:

- the whole closed band 3/20 <= |z| <= 1/6 maps outside the target by a strict additional margin 1/500;
- throughout the whole outer disk, |F(z)-1| < 51/1000 and |F^2(z)-(1-kappa)| < 19/100;
- all three phase images remain in the actual approximation disk of radius 23/20;
- F^3(0) lies inside the same fixed target disk.

`ThreeReturnAnnulus.lean` constructs a global Lipschitz potential at every physical scale d>0, zero on any inner plate contained in the closed disk of radius 3*d/20 and one outside the disk of radius d/6. Its actual planar Dirichlet energy is at most 19*pi < 60, so the reciprocal Lipschitz variational capacity exceeds 1/60. The integral uses the real Frechet derivative and planar Lebesgue measure. This is not an asserted identification with a uniformizing-annulus modulus.

Both new modules compiled locally without warnings with pinned Lean 4.32.0. Their application to the canonical source closure, complete target surjectivity, and exact degree is the next proof step.

All accepted results will be stated as Lean theorems in the pinned repository project and checked by the existing CI and transitive-axiom audit. Progress and proof revisions will be committed to this pull request.

## Dependencies

- NOV26_TIP_THEOREM and the actual finite and all-period primitive-tip estimates cited by research/tip_family_theorem/AUDIT.md, finding F04.
- Existing exact real interval and complex remainder infrastructure in the repository.
- PR #238 contains independent all-period actual-parameter construction. Any use of that work will be explicitly declared as a dependency; its crossing-curve result is not this contribution's claim.

## Boundary

The ledger row remains open while this is a draft. A uniformly chosen collar does not give a bound for every arbitrarily shrunk collar. The exact relation between the intended canonical result and the row will be recorded after the proof. No canonical KKL marking, Wave width, MLC, or H1-H4 conclusion is claimed. No status-record or workflow change is proposed.

## Attribution

The existing archive supplies the tip normalization, coefficient enclosures, and strict outer Rouché margins. This work targets the additional uniform inner containment and simultaneous phase control, not a repetition of those estimates. The contribution uses the repository's CC0 terms.
