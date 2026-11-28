---
ledger: NOV26_OPEN_SUBSECTOR
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="complex-central-escape-20261128"></a>

# Physical complex escape: an unsuccessful route to the native fine-subsector obligation

## Claim

**This attempt has not met the requested research standard for F12.**
It does not close or establish a decisive new subcase of
`NOV26_OPEN_SUBSECTOR`. The supporting complex-dynamical estimate described
below is retained for inspection, but it is not promoted to a native
fine-subsector theorem. No ledger status change is proposed.

The target in the ledger is:

> Fine-subsector edge escape: Old-edge spectral data do not imply iterated
> fine-subsector domination or zero-edge escape (F12).

The candidate analytic result is an explicit, period-uniform complex escape
estimate for the **actual** selected quadratic family. It is stronger than
the qualitative off-real exclusion used by this route, but the remaining
F12 obstruction concerns native marked paths and descendant crests, not
the nonescaping point set.

### Exact supporting statement

Let `ActualTip p c` hold and let p >= 17. Put f(z)=z^2+c,
d=f^p(0)>0, H(z)=f^(3p)(d z)/d, and
t=-H(0) in [117/1000,119/1000]. The physical interval radius is
r=f^(6p)(0)=d t=-f^(3p)(0).

For t>0, write E_t(z)=(|z-t|+|z+t|)/(2t) and
A_t(z)=E_t(z)+sqrt(E_t(z)^2-1). The Lean definition
`SlitJoukowski.slitAmplitude t z` expresses this amplitude via the
normalization 2z/t and the exterior Joukowski inverse of [-2,2].
It is continuous, at least one, and equals one exactly on [-t,t].

The main normalized theorem is
`ActualCentralEscape.actual_amplification`:

    |z| <= 1/6  ==>  A_t(z)^7 <= A_t(H(z))^6.

The physical theorem `PhysicalCentralEscape.physical_amplification`
uses the literal critical-orbit scale and the complete original iterate:

    |z| <= d/6  ==>  A_r(z)^7 <= A_r(f^(3p)(z))^6.

The finite escape certificate
`PhysicalCentralEscape.physical_finite_exponential_escape` states:

    (16/5)^(6^N) < A_r(z)^(7^N)
      ==> there exists n <= N with |f^((3p)*n)(z)| > d/6.

These quantifiers range over all complex points and the full unbounded
period range p>=17. The normalization is proved to commute with every
complete polynomial iterate.

The selected filled set is defined using the existing canonical component,
not supplied as a model. If

    W = ThreeReturnCollar.physicalSource c p
    K_W = {z : for every n, f^((3p)*n)(z) belongs to W},

then `physicalFilledSource_eq_orbit_interval` identifies K_W exactly
with the real interval [f^(3p)(0),f^(6p)(0)].
This is the filled set of the selected restriction, not the full
quadratic filled Julia set K(f).

The **qualitative interval identification is prior written mathematics**:
see the November 16 prime-end note, Section 2, and
[PHYSICAL_BRIDGES.md, Section 3](../../research/tip_family_theorem/PHYSICAL_BRIDGES.md).
It is included here as a machine-checked canonical-object bridge, not as
a new mathematical discovery. No worldwide priority claim is made for
the quantitative estimate.

## Evidence

### Proof of the supporting complex estimate

1. The exact third-return coefficient estimates give the stronger whole-circle
   barrier |H(z)|>1/4 when |z|=1/6. The existing weaker annular barrier is
   insufficient for the numerical comparison below.
2. The actual signed critical orbit and the actual real return estimates
   prove invariance of [-t,t]. The positive real inverse branch and the
   complete complex collision theorem prove H(z) belongs to [-t,t] if and
   only if z belongs to [-t,t], throughout the full closed control disk.
3. The exterior Joukowski address is holomorphic off the slit. Its modulus
   extends continuously across the slit; its complex phase need not.
   `SlitGreenBarrier.norm_boundary_bound` proves the appropriate maximum
   principle using only continuity of that modulus.
4. On the input circle the amplitude is at most 16/5. On its image it is
   at least 39/10. Exact rational arithmetic gives
   (16/5)^7 < (39/10)^6. Applying the maximum principle to the modulus of
   the quotient of the seventh and sixth powers yields the claimed
   inequality on the disk.
5. The power inequality iterates to
   A_t(z)^(7^N) <= A_t(H^N(z))^(6^N) along every surviving finite orbit.
   A separate finite power budget excludes a bounded infinite sequence
   with initial amplitude greater than one.
6. Exact scaling transports the result to f^(3p), the physical canonical
   source, and the original critical-orbit endpoints.

The auxiliary maximum principle and Joukowski mathematics are classical
ingredients. Formalizing them is not itself claimed as frontier progress.

### Why this does not settle the selected obligation

The amplitude is identically one on the full central interval. Thus the
new power comparison restricts to the equality 1=1 on its points. The
two prime-end accesses at an interior slit point, their cyclic positions,
their winding classes, and their retained descendant crests are additional
data that the amplitude does not encode.

The archived contour operation is g_* q0^{-1}; the required native
operation is G_* iota*. Their identification on arbitrary fine arcs is
not supplied by the filled-set theorem. In particular, q0 collapses the
whole attachment boundary to the old tip, although physical points of
that attachment lie in the target interior.

The adversarial review rejected the following possible shortcuts:

- The archive already proves fine contour-subarc exposure and saturation
  in [maximal_native_wave_20261123, Section 6](../../research/independent_audits/maximal_native_wave_20261123/NOTE.md).
  Re-proving that contour result would not settle the native obligation.
- [immersion_mark_resolution_20261124](../../research/independent_audits/immersion_mark_resolution_20261124/NOTE.md)
  already proves the connected-arc contour formula under the maximal-component
  convention and separately records the raw-path hairpin obstruction.
  Neither is new here, and that convention is not substituted for native
  immersion pullback.
- [native_mark_attack_20261124](../../research/independent_audits/native_mark_attack_20261124/NOTE.md)
  already handles maximal-component deduplication and simple-parent
  homotopy support. Unique component or homotopy support does not establish
  the complete singleton-output-path condition required for unbreakability.
- For a Wave with the original marking, the proposed fine-arc containment
  is an easy consequence of the already-archived finite native action.
  For a Wave eligible only after a fine refinement, the refined covering
  and immersion markings, filters, and finite-horizon compatibility must
  first be constructed and proved.
- Retaining one child does not imply that it retains an entire parent
  contour crest. The precise unbreakability, marking, and width-accounting
  hypotheses cannot be omitted.
- The original KKL path convention was checked directly:
  [Section 1.4](https://arxiv.org/html/2606.27272v1#S1.SS4) and
  [Appendix A.3.2](https://arxiv.org/html/2606.27272v1#A1.SS3.SSS2).
  No hidden proper-homotopy uniqueness convention was found that would
  supply the missing identification.

The existing real angular expansion factor 30/19 and precritical mesh in
the base already give stronger real-boundary expansion than one could
obtain by taking a boundary derivative of the new 7/6 estimate.
That alternative was also rejected as a proposed new advance.

### Lean validation

At commit `8354be4996fb9dc06a0a4643295d1a6b4d625626`,
the unchanged weighted CI compiled `ThreeReturnEstimates`,
`ActualCentralSlit`, `ComplexEscapeSequence`, `SlitJoukowski`,
`SlitGreenBarrier`, and `ActualCentralEscape`.
The remaining two elaboration errors were confined to the physical
wrapper: an ambiguous normalization name and an unexpanded three-return
definition. This revision repairs both. Complete build and transitive
proof-trust audit are pending at this revision.

The execution workspace was full before cloning, and no local Lean
executable was available. Source changes were committed through the
GitHub connector. The repository's unchanged CI is the compiler and
proof-trust auditor; no local compilation is claimed.

Every public theorem is registered in the existing weighted build,
theorem index, and source inventory. No workflow or ledger file was changed.

## Dependencies

The analytic estimate uses the archive's existing actual selected-tip
construction, exact high-period return approximation, complete collision
theorem, canonical source component and collar, actual real return bounds,
and physical critical-orbit calibration. The principal imported modules
are `ThreeReturnEstimates`, `ThreeReturnDegree`,
`ThreeReturnCollar`, `ThreeReturnRealization`,
`ActualThreeReturnNormalization`, and `PhysicalCentralCarrier`.

The Joukowski address uses the existing `ChebyshevFibers` exterior inverse
and derivative results. Mathlib supplies the inverse function theorem,
complex maximum principle, compactness, and exact ordered-field reasoning.
No straightening theorem is assumed in the new direct filled-set proof.

## Boundary

No qualifying resolution, decisive new subcase, counterexample, or new
obstruction for F12 was found in this attempt. The frontmatter retains the
draft's partial label for its auxiliary theorem work; it is not a claim
that the target's remaining native transport gate has been advanced.

The native all-path immersion identification, changing fine markings,
whole-crest descendant retention, and lost-family width accounting remain
unproved here. No MLC, H1-H4, unrestricted Wave amplification, arbitrary-depth
transport, or full quadratic filled-set identification is asserted.

The draft should not be presented as a completed contribution satisfying
the user's request. The repository's no-progress rule calls for releasing
the obligation rather than keeping a claim open without a qualifying result.
The commits preserve the attempted argument and its validation.

## Attribution

Research, Lean proof construction, and independent adversarial reviews
were performed by OpenAI ChatGPT GPT-6 Astra Pro. No human review occurred.
The archive's prior qualitative filled-set, real expansion, contour
dynamics, and native-path obstruction results are explicitly credited
above and are not claimed as new.
