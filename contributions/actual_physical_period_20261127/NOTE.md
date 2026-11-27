---
ledger: TERMINAL_WAVE_CREST_TO_KL_SKIPPING_BINDER
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="actual-physical-period-20261127"></a>

# Actual primitive return domains, filled cores, and exact critical portraits

## Claim

For every integer p >= 17, a constructed literal quadratic polynomial
f_c(z)=z^2+c has the archive's fixed canonical proper degree-two 3p-return,
a nondegenerate compact connected full filled core, and pairwise disjoint
images of the **entire canonical open source** at all 3p physical phases.
The critical point has least preperiod 3p+1 and exact eventual period 3p;
the postcritical set has exactly 6p points; phase zero is the unique
critical phase and every positive phase is univalent; the complete physical
3p-return multiplier at its signed periodic endpoint has modulus >3/2.

The principal existence theorem is
`ActualPrimitiveReturn.exists_actual_primitive_return`. Its only inputs
are the integer p and the inequality 17 <= p. The parameter, retained
shooting itinerary, first-return exclusions, canonical domains, filled
core, exact period, and multiplier estimates are all supplied by the proof.

This is a partial result toward the named ledger obligation. It settles
the physical phase/period and filled-core interfaces for this explicit
family, not the general native marked-Wave binder.

## Evidence

### 1. Baseline and the specific advance

The initial baseline was main
`e66d25b2a8497448714379bcb283bd448d75bcc4`. This branch preserves the
concurrently merged main
`665e5f942d6b39902272fe6d8ca2dee6fbca8a6f` and its separate actual-collar
extremal-length work. A concurrent mechanical merge updated this branch
before the second proof checkpoint; all of its source and registry
entries have been retained.

The existing [uniform physical collar packet](../uniform_three_return_collar_20261127/NOTE.md)
and modules `NearTwoTip`, `ThreeReturnRealization`, and
`UniformThreeReturnRenormalization` construct a signed-tip parameter,
a proper canonical 3p-return, its ambient p-return, and three separated
phases under f_c^p. The [maximal crest packet](../actual_maximal_crest_20261127/NOTE.md)
explicitly leaves exact physical periods, primitive-branch identification,
and native marked-path gates open.

Earlier [prime-end identification notes](../../research/independent_audits/real_primitive_tip_family_prime_end_identification_20261116/NOTE.md)
already argued for a signed portrait and a real period-three return.
We do not claim those ideas as new. The new statement retains the **same
fixed complex source component**, proves exclusion for its entire parent
control disk at every intermediate original iterate, separates all 3p
full open phase domains without shrinking, and constructs the actual
nonescaping continuum with connectedness and fullness proved. The exact
physical portrait and uniform multiplier are joined to that literal
domain construction in one kernel-checked existence theorem. No claim
of literature priority is made.

### 2. Exact objects and statements

The parameter satisfies

    -2 <= c <= -2 + 20*4^(-p),
    d := f_c^p(0) > 0,      d <= 12*4^(-p),
    kappa(p,c) in [17903/10000,17904/10000],
    f_c^(6p)(0) = -f_c^(3p)(0),      f_c^(3p)(0) < 0.

Here `kappa` is the archive's exact normalized quadratic coefficient,
not a numerical surrogate. Put H(z)=f_c^p(dz)/d and R=H^3. The canonical
normalized source is the connected component through zero of
R^(-1)(B(0,1/6)); its physical scaling is U. The physical target is
V=B(0,d/6). These are the existing `source`, `physicalSource`, and
`physicalTarget`, without a newly selected smaller neighborhood.

The new retained core is exactly

    K = {z in C : for every n >= 0, f_c^((3p)n)(z) is in U}.

`physicalCore_eq_nonescaping` proves this identity for the scaled core;
scaling is not an unproved model-to-physical identification. The new
existence theorem establishes all of the following for the same c:

1. The existing physical return f_c^(3p):U -> V is proper and holomorphic,
   has the exact quadratic fiber census, and closure(U) is compactly
   contained in V. Its canonical source and the ambient p-return source
   are contractible.
2. K contains zero, is compact, connected, nontrivial, and full. Full means
   `planarFill K = K`; equivalently in this bounded setting its exterior
   is connected. K is contained in U and f_c^(3p)(K)=K.
3. For all 0 <= i < j < 3p, f_c^i(U) and f_c^j(U) are disjoint. Consequently
   the corresponding compact filled-core phases are also disjoint.
   The original quadratic is injective on every positive open phase,
   and phase zero is the unique phase containing a critical point.
4. With L=3p+1 and N=3p, the critical point first becomes periodic at time
   L and its eventual cycle has minimal period N. For arbitrary i,j,

       f_c^i(0) = f_c^j(0)
       iff i=j, or both i,j >= L and (i-L) mod N = (j-L) mod N.

   Thus the first 6p+1 orbit points are distinct, the complete critical
   orbit has cardinality 6p+1, and the postcritical set has cardinality 6p.
5. The signed point a=-f_c^(3p)(0) has minimal physical period 3p and

       |(f_c^(3p))'(a)| > 3/2.

The term primitive refers to the proved disjoint cycle of little filled
sets. It does not mean prime or first among all renormalizations of f_c:
the same construction already has an ambient p-return.

### 3. Proof architecture

**Retain the construction witness.** `ActualTipItinerary` preserves the
positive inverse shooting equation at the same intermediate-value
selection used by the existing parameter construction. This small
interface refinement is credited to that construction; it is not counted
as an independent new parameter-existence proof.

**Exclude all intermediate physical returns.** The full disk of radius
(23/20)d has radius below 1/100. Its actual polynomial iterates remain
within 1/100 of the critical orbit through time p. The retained positive
inverse itinerary puts the critical orbit above 7/5 at times 2 through
p-1, while its first image is near -2. Hence every point in that disk has
iterate norm greater than 1 at every time 1 <= j < p. The nonlinear
shadowing budget is bounded by

    8^p*((23/20)d)^2 <= (4761/25)*2^(-p) < 1/100.

This estimates the complete polynomial iteration. No derivative of a
truncated return or assumed geometric separation is used.

**Separate every open physical phase.** Divide an intermediate time into
q*p+r. A nonzero remainder r is ruled out by the parent-disk exclusion;
the two remaining positive p-step phases are separated by the existing
whole-disk enclosures. To separate arbitrary phases i and j, advance a
hypothetical intersection to the actual target V. Target-versus-phase
separation then rules it out. This argument never assumes that the open
source maps into itself.

**Identify the unique critical phase.** A one-step collision inside a
positive phase propagates to a collision of the complete return. Its
exact signed fiber census identifies the original source points up to
sign, and positive quadratic iterates are even, so the phase points
coincide. Thus every positive phase is univalent. The complete phase
disjointness excludes zero from those phases; the actual derivative
f_c'(z)=2z identifies phase zero as the unique critical phase.

**Recover the exact orbit portrait.** The signed endpoint a belongs to U
and is fixed by the 3p return. No earlier positive return is possible,
so its least period is 3p. The distinct points f_c^(3p)(0) and its negative
a have the same next image; only a is periodic, because a map is injective
on its periodic points. This locates the first periodic critical iterate
at 3p+1. Finite tail/cycle arithmetic gives the complete collision formula
and exact census.

**Construct the filled continuum.** Start from closure(U) and take the
successive complete return preimages retained in that closure. The
proper source and its exact signed sheets make each finite retained set
compact and connected; every stage contains the actual critical value.
The stages decrease. Their intersection is compact and connected, and
relative closedness of the actual inverse component excludes boundary
points. The intersection therefore equals the full nonescaping set in
the original open source. Surjectivity on the whole source supplies a
retained preimage of every core point, proving exact return invariance.

**Prove fullness without replacing the core.** If the core had a bounded
complementary component, its frontier would lie in the core. Apply the
maximum modulus principle to each entire return iterate on that component.
All iterates stay inside the source control radius; the proved complete
source-fiber exhaustion puts them in the actual source. Every point of
the proposed hole would therefore already lie in the original core, a
contradiction. Scaling transports the connected exterior and fullness to
the physical set.

**Prove uniform repulsion.** The complete normalized secant has modulus
>7/4 throughout the phase-control disk. The signed fixed point has norm
>1/10, its first normalized image has norm >9/10, and its second has norm
>1/2. The three exact chain-rule factors give a multiplier modulus >3/2.
Differentiating the literal scalar conjugacy proves equality with the
multiplier of the full original polynomial iterate.

### 4. Lean modules and validation

| Module in `formalization/weighted/` | Main role |
|---|---|
| `ActualTipItinerary.lean` | Construct the actual parameter with the retained shooting witness. |
| `ActualFirstReturnSeparation.lean` | Whole-disk shadowing and all intermediate physical return exclusions. |
| `ActualFullCycle.lean` | Full open phase separation and exact physical terminal period. |
| `ActualCriticalPreperiod.lean` | Least critical preperiod, all orbit equalities, and exact finite census. |
| `ActualPhaseUnivalence.lean` | One critical phase and univalence of every other complete phase. |
| `ActualTipMultiplier.lean` | Exact derivative factors and physical multiplier >3/2. |
| `ActualFilledReturn.lean` | Literal nonescaping core, compactness, connectedness, nontriviality, and exact image. |
| `ActualFilledReturnFullness.lean` | Fullness and connected exterior of the actual normalized and physical core. |
| `ActualPrimitiveReturn.lean` | Assemble every clause at one constructed parameter; principal existence theorem. |

Each module is a registered default target of the repository's Mathlib
Lake project, and every public theorem is listed in the theorem index.
Local verification uses the exact pinned Lean 4.32.0 toolchain and the
Git revisions in the checked-in Mathlib manifest. The repository's
transitive `collectAxioms` audit accepts only `propext`, `Classical.choice`,
and `Quot.sound`. No proof placeholder, unsafe trust escape, or new axiom
is introduced.

Portable validation commands are:

```sh
python -B code/verify_lean_coverage.py
python -B code/verify_lean_coverage.py --self-test
cd formalization/weighted
lake exe cache get
lake build ActualPrimitiveReturn
cd ../..
python -B code/verify_lean_coverage.py --audit weighted
python code/contribute.py check
```

The CI authority is [PR #248 checks](https://github.com/dovvnloading/loops-research-archive/pull/248/checks).
The final source checkpoint and observed CI results are recorded in the
PR description. All proof progress is committed in that PR. The first
intermediate weighted run was cancelled when the branch was synchronized
with concurrent main changes; that cancelled run is not counted as a
successful verification.

## Dependencies

- Target: `TERMINAL_WAVE_CREST_TO_KL_SKIPPING_BINDER`, still open. It is a
  research target, not a premise used in the Lean proofs.
- Archived actual parameter and collar modules: `NearTwoShooting`,
  `NearTwoTip`, `CriticalReturnRelationStability`,
  `QuadraticCrestDividedDifference`, `ThreeReturnEstimates`,
  `ThreeReturnDegree`, `ThreeReturnCollar`, `ThreeReturnParent`,
  `ThreeReturnRealization`, and `UniformThreeReturnRenormalization`.
- Existing general topology: `StationaryGeometricFibers` for the closed
  two-sheet critical pullback theorem, `LeastSaturatedCarrier` for compact
  decreasing connected intersections, and `ThreeReturnFullness` /
  `PlanarFullification` for planar exterior facts.
- The pinned Mathlib proofs of iteration/period arithmetic, compactness,
  connectedness, complex differentiation, and maximum modulus.

No external unformalized dynamical theorem is introduced as an assumption.

## Boundary

**The ledger obligation remains open; no status change is requested.**

The original row asks for every retained terminal Wave occurrence to
supply a literal ordered proper restriction, fixed distinct endpoint
continua, one fixed separating KL piece, a lifted horizontal multicurve,
a componentwise skip witness, all tagged access/tile/deck/localization/
obstacle/final-root data, and a uniform response-class/depth charge or an
identified first B1-B10 failure. This packet does not construct that native
Wave occurrence or instantiate its full marked protocol.

The present theorem concerns an explicitly constructed quadratic family
for p >= 17 and its fixed canonical complex domains. It does not identify
the selected parameter with a named primitive-component branch in the
source's parameter plane, prove source q/w marking or prime-end/access
transport, or interpret a radial integral as a native Wave width. The
smaller indices 3 through 16 are not included in this new unconditional
physical-period theorem. No uniqueness of the selected parameter is
asserted.

The terminal critical cycle is uniformly repelling. Repulsion of **every**
periodic cycle is not asserted. The disjoint little-set cycle is primitive;
primality relative to all competing renormalizations is not asserted.
No H1-H4, UPTCR, or MLC closure is claimed.

## Attribution

The original quadratic constructions, normalized return estimates,
canonical collars, and three f_c^p phases belong to the cited archive
modules and notes. The distinct-predecessor argument also appears in the
archive's separate near-minus-seven-fourths family. Compact nested-set
arguments, finite orbit arithmetic, the complex chain rule, and maximum
modulus are classical methods, used through the named Lean proofs. This
packet's contribution is their complete actual-domain integration with
uniform intermediate exclusion and the new full physical-cycle and
filled-core statements, not a claim of a new classical theorem.

OpenAI ChatGPT GPT-6 Astra Pro materially assisted proof construction,
Lean implementation, local kernel checking, and adversarial scope review.
No independent human specialist review has occurred. Released under CC0.
