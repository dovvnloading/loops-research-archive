---
ledger: NOV26_OPEN_SUBSECTOR
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; proof development and independent mathematical scope review
human_review: none
---

<a id="physical-cylinder-expansion-20261128"></a>

# Uniform physical cylinder contraction for the selected three-return

## Claim

This draft attacks the metric part of fine-subsector escape on the actual selected primitive family. For p >= 17 and an actual selected parameter c, write d = f_c^p(0), F(z) = f_c^p(d z)/d, H = F^3, and t = -H(0). The candidate theorem is uniform expansion of the literal real return h(x) = -H(t x)/t on [-1,1] in its cosine coordinate, with expansion factor at least 30/19 on each branch. It should imply that every actual depth-n monotonicity cylinder has physical diameter at most d t pi (19/30)^n.

This is a research target, not a proved claim at this initial commit. No theorem is counted until the Lean build and dependency audit pass.

## Evidence

The proposed new estimate is a uniform square-divided-difference bound for the actual polynomial H on its own central invariant interval. The proof will multiply the three exact divided differences of the normalized p-return and bound their two intermediate phase sums. It will then derive the angular expansion and all-depth physical cylinder estimate. No supplied conjugacy to a piecewise-linear or Chebyshev model is assumed.

The distinction from the existing qualitative contour argument is physical metric control with explicit constants, uniform in p. A topological conjugacy alone does not provide that bound.

## Dependencies

The existing actual-parameter existence, exact signed critical relation, real phase bounds, and complex divided-difference estimates from the repository will be used. The proposed estimates will be proved against their literal polynomial definitions inside the weighted Lean project.

Local Lean is unavailable in this workspace. The existing pull-request Lean workflows will be the compiler and dependency-audit record.

## Boundary

The target is the selected real primitive family, p >= 17, and its literal central three-return cylinders. It does not supply marked prime-end transport for arbitrary Waves, stationary retained-path selection, arbitrary tuning depth, or a general MLC argument. The full ledger obligation remains open.

## Attribution

The canonical family and earlier physical estimates are from the archive. The expansion mechanism uses classical real-variable calculus; the intended new mathematical content is the uniform explicit estimate on these actual return maps and its physical all-depth consequence. No claim of global mathematical priority is made before validation and comparison with earlier work.

