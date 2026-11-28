---
ledger: NOV26_OPEN_OPTIMAL_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation, Lean implementation and adversarial review
human_review: none
---

<a id="marked-wave-supremum-limit-20261127"></a>

# Convergence of the unrestricted parent Wave supremum

## Claim

This is an early draft investigation. No new compiled theorem or completed progress is claimed yet. The provisional partial designation does not assert that a result has been obtained.

The target is the convergence clause for the unrestricted parent optimum in NOV26_OPEN_OPTIMAL_LIMIT. The November 23 full-path proof explicitly does not prove continuity of the optimizers or convergence of these suprema. Exact values, optimizer attainment, the covering-restricted optimum, and simultaneous child convergence are outside this claim.

## Proposed argument

Normalize by the actual positive return scale d_p. The parent surface is the disk of radius R_p/d_p minus the real slit [x_{2p}/d_p,1], with the two ending atoms over (x_{5p}/d_p,x_{3p}/d_p) and the relative homotopy class around the left tip.

Four real cutpoints converge, and R_p/d_p tends to infinity. A small explicit Lipschitz perturbation of the horizontal coordinate can match every inner mark. It preserves simple leaves, their banks, their full selected homotopy class, and disjointness.

The missing global step is quantitative control of every discarded leaf when truncating a limiting Wave. A density on N disjoint dyadic shells should bound the modulus of all escaping leaves by 3*pi/N. Combining this proved cutoff with proved modulus distortion should give convergence of the complete supremum without assuming an optimizer exists.

These are obligations to prove, not premises to be inserted into an abstract convergence certificate. The actual marked family, its Borel sublaminations, and the connection to the actual critical-orbit sequence must be made explicit.

## Evidence and validation

Implementation is in progress. A result counts only after the relevant Lean theorem compiles in the repository project and unchanged CI, without proof holes or new axioms. Existing baseline checks do not validate this proposed result.

### First compiled checkpoint

The initial analytic modules now compile locally with the repository's pinned Lean and mathlib versions. SlitWaveModulus proves the distortion of the genuine infimum over measurable densities by constructing and bounding the transported density. SlitWaveEscape constructs a common density of exact area 3*pi/N for every connected trace that crosses N dyadic shells. Hausdorff one-measure on a simple trace includes leaves of infinite length, so finite total variation is not silently imposed on the native family.

These analytic tools are classical and are not submitted as the new result. The required novelty remains convergence of the complete actual marked parent supremum. The marked-family transport, uniform passage to the supremum, literal critical-orbit specialization, and unchanged CI validation are still being completed.

The limiting surface is the plane minus the limiting slit. Its end at infinity is a cusp, whereas the finite physical surfaces satisfy the source's no-cusp standing convention. The proposed limit is therefore called the limiting marked plane-slit supremum; it is not asserted that the limiting surface itself satisfies every A.1 standing hypothesis.

### Whole-family and actual-orbit checkpoint

The compiled geometric family now requires a Borel union of disjoint simple proper leaves. It does not require a Borel set of chosen parametrizations. Each leaf has the exact opposite-bank endpoint conditions and a literal endpoint-fixed homotopy in the selected left-tip class. Finite-cut transport composes this entire homotopy and preserves the geometric Borel support.

The exhaustion argument compresses the entire Wave by a proved continuous injective coordinate map. It fixes the large inner square and maps the whole plane into a bounded square. All originally bounded leaves are retained literally. Thus the proof uses modulus subadditivity on the escaping family without asserting that an arbitrary selected subfamily is itself a Borel Wave.

ActualParentMarks also compiles. Its four coordinates are the literal values x_(2p)/x_p, x_(5p)/x_p, x_(3p)/x_p, and 1. It proves their order and convergence for the actual constructed quadratic parameters and proves the actual normalized target radius is at least 2^p/12. These geometric convergence statements are derived from the existing actual-tip estimates; they are not assumed as a replacement for the physical problem.

The final supremum theorem and its physical positive-dilation identification are still under validation at this checkpoint. No completed novelty claim is made for these intermediate modules alone.

## Dependencies and prior art

- research/independent_audits/maximal_native_wave_20261123/H3_WIDTH.md, especially Section 7.2.
- research/tip_family_theorem/THEOREM.md, Open Problem 2.
- The existing actual-tip estimates and finite critical-orbit perturbation bounds.
- The archive's explicit distinction between full-path envelopes, unrestricted marked Wave optima, and covering-restricted optima.

The analytic tools of modulus, bilipschitz transport, and annular cutoff are classical. The intended new result is their fully justified application to convergence of the actual unrestricted marked parent supremum. No worldwide priority claim is made before that result is proved and checked.

## Boundary

The obligation remains open at this checkpoint. No assumption of width transport, native marking identification, or escaping-family control will be counted as a proof of itself. If no genuine result is established, the draft will be closed to release the claim.
