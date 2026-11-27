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

This draft constructs a canonical collar for the actual normalized three-return, with a fixed outer disk of radius 1/6 and a source containment radius of 3/20. The new step is simultaneous control of the full intermediate phase domains, so that no unquantified shrinking is needed. The compiled proof modules establish the full annular exclusion and whole-disk phase estimates for every constructed actual signed tip of period p >= 17, exact signed collisions and the unique critical point, and a uniform physical Dirichlet-energy bound. The final combined theorem and the finite-period extension are being integrated.

## Evidence

The normalization is F(z)=f_c^p(d*z)/d with d=f_c^p(0)>0, outer radius 1/6 and inner radius 3/20. The source W is the connected component containing zero of the complete inverse image of the outer disk under F^3. This selects W from the actual polynomial rather than supplying a domain or a degree as input.

`ThreeReturnEstimates.lean` proves for every actual signed tip constructed by PR #238, for p >= 17:

- the whole closed band 3/20 <= |z| <= 1/6 maps outside the target by a strict additional margin 1/500;
- throughout the whole outer disk, |F(z)-1| < 51/1000 and |F^2(z)-(1-kappa)| < 19/100;
- all three phase images remain in the actual approximation disk of radius 23/20;
- F^3(0) lies inside the same fixed target disk.

`ThreeReturnAnnulus.lean` constructs a global Lipschitz potential at every physical scale d>0, zero on any inner plate contained in the closed disk of radius 3*d/20 and one outside the disk of radius d/6. Its actual planar Dirichlet energy is at most 19*pi < 60, so the reciprocal Lipschitz variational capacity exceeds 1/60. The integral uses the real Frechet derivative and planar Lebesgue measure. This is not an asserted identification with a uniformizing-annulus modulus.

`ThreeReturnDomain.lean` proves that the whole canonical component has compact closure strictly inside the inner barrier; the restriction is proper in the literal subspace topologies and covers the entire fixed target disk. It also proves invariance under z -> -z.

`ThreeReturnDegree.lean` proves F^3(z)=F^3(w) if and only if z=w or z=-w on the complete outer disk, and proves that the actual complex derivative vanishes there exactly at zero. Its final theorems identify the critical fiber as {0}, every regular fiber as {z,-z} with distinct points, and the corresponding exact set cardinalities. These are statements about the actual polynomial values, not assigned degree labels.

`FiniteThreeReturnCertificates.lean` has independently kernel-checked the new fixed-radius integer inequalities for all fourteen archived parameter boxes p=3,...,16. Its certificate includes every intermediate factor in the complete three-return divided difference. The analytic soundness bridge for this finite extension is still being compiled, so the finite certificate is not yet advertised as the all-period collar theorem.

`ThreeReturnCovering.lean` upgrades this census to a literal two-sheet covering after deleting the critical value. It constructs local sheets in open half-planes from the signed collision theorem, and uses properness to produce evenly covered neighborhoods whose fiber set is `Fin 2`.

`ThreeReturnCollar.lean` now assembles these results into `CanonicalCollar c p`. The theorem `actual_canonical_collar` supplies every field for every `ActualTip p c` with p >= 17, and `exists_actual_canonical_collar` supplies such an actual parameter for every such p. The physical domain is proved equal to the component containing zero of the complete physical f_c^(3p) pullback of D(0,d/6). Its actual closure is strictly inside D(0,3*d/20), and the capacity and reciprocal-capacity bounds apply to this closure. The generic assembly takes only the orbit scale, critical-value inequality, boundary inequality and actual collision relation, permitting an independent finite-certificate input.

The registered proof modules compile locally with pinned Lean 4.32.0. The remaining integration work is the finite-period analytic bridge and stronger topology of the canonical source and its complement.

All accepted results will be stated as Lean theorems in the pinned repository project and checked by the existing CI and transitive-axiom audit. Progress and proof revisions will be committed to this pull request.

## Dependencies

- NOV26_TIP_THEOREM and the actual finite and all-period primitive-tip estimates cited by research/tip_family_theorem/AUDIT.md, finding F04.
- Existing exact real interval and complex remainder infrastructure in the repository.
- PR #238 contains independent all-period actual-parameter construction. Any use of that work will be explicitly declared as a dependency; its crossing-curve result is not this contribution's claim.

## Boundary

The ledger row remains open while this is a draft. A uniformly chosen collar does not give a bound for every arbitrarily shrunk collar. The exact relation between the intended canonical result and the row will be recorded after the proof. No canonical KKL marking, Wave width, MLC, or H1-H4 conclusion is claimed. No status-record or workflow change is proposed.

## Attribution

The existing archive supplies the tip normalization, coefficient enclosures, and strict outer Rouché margins. This work targets the additional uniform inner containment and simultaneous phase control, not a repetition of those estimates. The contribution uses the repository's CC0 terms.
