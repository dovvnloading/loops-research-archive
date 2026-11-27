---
ledger: NOV26_OPEN_3P_MODULUS
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="three-return-finite-capacity-20261127"></a>

# Uniform two-sided extremal length for the selected actual three-return collars

## Claim

For every integer p >= 3, the actual quadratic parameter and canonical physical three-return domains constructed by the preceding all-period realization admit the following additional estimates. Write d = criticalValue c p > 0, W = physicalSource c p, V = B(0,d/6), and K = closure W.

1. The entire closed disk of radius d/40 lies in W.
2. On that disk, the literal physical iterate satisfies
   norm of the (3*p)-fold iterate at z, plus d/150, is strictly below d/6.
3. The existing all-Lipschitz Dirichlet capacity obeys
   3/20 <= capacity(K,V) < 60. Its reciprocal therefore obeys
   1/60 < variationalModulus(K,V) <= 20/3.
4. For the family Gamma of **all continuous rectifiable curves** joining K to the target circle with open path in V minus K, the standard two-modulus and its reciprocal extremal length obey
   3/20 <= M(Gamma) <= 19*pi < 60 and
   1/60 < EL(Gamma) <= 20/3. The sharper lower bound is 1/(19*pi).

All constants are independent of p and d. The theorem constructs c and uses the literal polynomial components; domain existence, an inner-radius condition and a modulus condition are not supplied as hypotheses.

The final actual-domain assembly is in
`ThreeReturnExtremalLength.exists_physical_renormalization_with_extremal_bounds`.
The paired inequality is
`ThreeReturnExtremalLength.selected_extremalLength_strict_bounds`;
`selected_extremalLength_pos_finite` excludes both zero and infinity.

## Evidence

### What advances beyond the archive

The preceding [uniform_three_return_collar_20261127 packet](../uniform_three_return_collar_20261127/NOTE.md) constructs W and V and proves closure W subset B(0,3*d/20), proper holomorphic degree-two return, trapped critical orbit, ambient phase inclusions, and capacity(K,V) < 60. Its Boundary explicitly leaves positivity of that capacity, finiteness of its reciprocal, and the missing standard-modulus comparison open.

This contribution proves the complementary actual inner-disk estimate, positive capacity, and **direct** two-sided standard joining-curve extremal length for those same domains. The old domain, degree, topology and upper-energy results are imported. No claim of a new classical extremal-length principle is made; the generic analytic infrastructure is formalized to establish the new all-period actual-domain theorem.

### 1. Actual polynomial inradius

`ThreeReturnInradius.lean` proves norm(H(z)) < 4/25 for every norm(z) <= 1/40, where H is the actual normalized three-return. The target radius is 1/6, so the strict normalized image margin is 1/150.

For p=3,...,16, a new exact integer certificate bounds the full nonlinear iterate, including the remainder. The proof checks all fourteen certificates with Lean's kernel reduction (`decide +kernel`) and proves the interval-to-real/complex soundness statements. This is not a floating-point computation or a quadratic truncation.

For p>=17, the actual return approximation and the certified kappa interval control the three complete iterates. The model third critical image has norm at most 1/8; the actual critical-image error is at most 31*epsilon. Starting from the disk of radius 1/40, the propagated difference after three returns is at most
62*epsilon + 25*(9/5)*(1/40)^2, with epsilon <= 1/500000. Their sum is strictly less than 4/25. The existing phase estimates justify every use of the approximation.

The closed disk is connected, contains zero, and lies in the full pullback of B(0,1/6), so it lies in the actual central connected component. Scaling by d proves the physical inclusion and image margin. These are conclusions about the actual polynomial, not inputs about a stand-in domain.

### 2. Positive capacity

`CollarCapacityLower.lean` keeps the existing class of every globally Lipschitz real potential, zero on K and one outside B(0,R). If B(0,r) subset K and r,R>0, it proves capacity(K,B(0,R)) >= r/R.

For almost every horizontal slice y in (-r/2,r/2], the potential changes by one between iy and R+iy. The Lipschitz fundamental theorem of calculus and a square-integral estimate give at least 1/R energy on that slice. Fubini over a strip of width r gives r/R. The proof uses the actual planar Frechet derivative and complex Lebesgue measure, with no common bound on the competitors' Lipschitz constants. The derivative vanishes outside the target disk and the boundary circle is null, so this is the original energy functional.

### 3. Standard rectifiable-curve extremal length

`CollarExtremalLength.lean` uses precisely the density/curve definition:

- A curve is continuous on [0,1] and has finite total variation. Its original parameterization need not be Lipschitz, absolutely continuous, smooth or injective.
- Metric length is the Lebesgue integral along Mathlib's natural arclength parameterization. The module proves unit speed, Lipschitz behavior, reconstruction and equality of the relevant images.
- Admissible densities are all Borel-measurable functions from the plane to the extended nonnegative reals whose integral is at least one on every joining curve.
- M is the infimum of their whole-plane square integrals; EL is its reciprocal.

This is the standard two-modulus convention; see Kai Rajala, [Extremal length and duality](https://users.jyu.fi/~kirajala/Fuglede140824.pdf), Introduction, definition (1), and Steffen Rohde, [Topics in Geometric Function Theory, Lecture 1](https://sites.math.washington.edu/~rohde/582/lecture1.pdf), p. 2. These references identify the terminology; no unformalized theorem from them is used as a proof premise.

`CollarShellMetric.lean` supplies a sharper admissible density: height 1/(R-r_out) on the closed target disk minus the open disk of radius r_out. In natural arclength coordinates, take the curve's last contact with the closed disk of radius r_out. The remaining tail lies in the shell and has length at least R-r_out, even for curves with arbitrary earlier backtracking. Thus the shell density is admissible for every joining curve. Its exact area is pi*(R^2-r_out^2)/(R-r_out)^2. Substituting r_out=3*d/20 and R=d/6 gives M<=19*pi<60 and hence the direct standard bound EL>1/60.

For the opposite inequality, `CollarHorizontalFamily.lean` takes the last contact with compact K and the first outer-circle contact on every horizontal slice through B(0,r). It produces an actual joining segment, without any smoothness or connectedness assumption on the inner boundary. `CollarStraightLength.lean` computes that segment's exact natural arclength integral. Admissibility on the segment forces the full horizontal integral to be at least one. `CollarMetricEnergy.lean` applies Holder and Fubini to every extended-valued Borel density, including densities of infinite area, to prove M>=r/R.

The actual radii r=d/40 and R=d/6 give M>=3/20 and EL<=20/3. This is a positive-area family argument; it does not replace the entire joining family by a single chosen path.

### Lean registration and validation

The eight new modules and all public theorem declarations are registered in the existing weighted lakefile, theorem index and source table:

- `ThreeReturnInradius`
- `CollarCapacityLower`
- `CollarExtremalLength`
- `CollarMetricEnergy`
- `CollarStraightLength`
- `CollarHorizontalFamily`
- `CollarShellMetric`
- `ThreeReturnExtremalLength`

Validation uses Lean 4.32.0 and the repository's pinned Mathlib revision. The contribution intake, source-trust scanner and public-theorem registration checks pass. The existing weighted workflow builds the complete project and audits every declaration's transitive dependencies against exactly propext, Classical.choice and Quot.sound. No workflow or trust allowance is added. Head-specific build and audit results are recorded in [PR #246 checks](https://github.com/dovvnloading/loops-research-archive/pull/246/checks), with the complete development history committed in that PR.

Reproduce the new proof chain with:

```sh
cd formalization/weighted
lake build ThreeReturnExtremalLength
```

The existing CI checks the entire weighted project, not only this dependency chain. From the repository root its full audit and contribution checks are:

```sh
python3 -B code/verify_lean_coverage.py --audit weighted
python3 -B code/contribute.py check
```

## Dependencies

The selected obligation is NOV26_OPEN_3P_MODULUS, with NOV26_TIP_THEOREM as its recorded prerequisite.

The actual construction is imported through `UniformThreeReturnRenormalization`, including the finite certified parameters, analytic-tail actual parameters, proper degree-two physical map, and existing outer containment and energy upper bound. The new generic analysis uses Mathlib's arclength parameterization, Rademacher differentiability, Lipschitz FTC, Holder inequality, Fubini theorem and Lebesgue measure transformations, all as Lean theorems.

## Boundary

The result is **partial for the literal ledger obligation**, and the row must remain open.

The proved family is the fixed canonical pair
W = d * component_0((F^[3])^-1 B(0,1/6)) and V = B(0,d/6), for the actual selected parameter at every p>=3. The theorem settles positive capacity, finite reciprocal capacity, and two-sided standard joining-curve extremal length for this family.

The following larger obligations remain:

1. Bounds for every arbitrarily further-shrunk collar or arbitrary nested depth are not proved. The ledger and AUDIT F04 explicitly include that broader quantifier.
2. The analytic-tail selected actual parameter has not been identified with the archive's narrower unique signed/kneading chart 14*4^(-p)<c+2<16*4^(-p). The imported actual parameter exists in the proved broader shooting interval with its certified coefficient and orbit conditions; global uniqueness and the missing chart identification are not conclusions here.
3. No equality between Dirichlet capacity and the curve two-modulus, or between joining-curve extremal length and a round-annulus uniformization parameter, is proved or assumed. Both quantities are bounded directly and separately. The standard rectifiable-curve theorem does not need either equality.
4. No canonical KKL Wave marking, arbitrary-depth stationary system, H1-H4 or MLC conclusion follows from this packet.

No status record is changed. The scope is the constructed actual canonical collars, not arbitrary replacement domains.

## Attribution

The actual all-period domain construction, topology, degree, dynamics and upper-energy bound belong to the preceding archived contribution. This work supplies the new uniform physical inradius and the resulting capacity and standard extremal-length bounds.

OpenAI ChatGPT, GPT-6 Astra Pro performed proof search, Lean implementation, independent internal review and validation. Human review: none. Original contributions are released under the repository's CC0 terms.
