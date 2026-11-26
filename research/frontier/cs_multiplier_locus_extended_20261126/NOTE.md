# Extended CS dividing-multiplier locus

**Verdict: INCONCLUSIVE.** Both new levels numerically satisfy the preregistered interval at every accepted observation, with local algebraic certificates through q=9. At q=9 the PLY disk admits nonunique integer shifts at two primary points; the numerical attachment continuation selects the principal log at both precisions, but the preregistered ambiguity guard is applied conservatively. This is stronger finite evidence, not a certified dividing-mark theorem.

## Limits
Finite sampled evidence only, even when local root enclosures are rigorous. No certified wake/mark identification unless separately proved, no whole-copy upper bound, no infinite-tail assertion, no Theorem D extension or MLC/JLC claim.

## Preregistration (before new numerical computation)
For f_c(z)=z²+c, q=3,4,5,..., P_i=product of the first i denominators and P_0=1, use the actual absolute-period P_{i-1} dividing multiplier rho_i and the attachment-continued logarithm z_i=log(rho_i)/(2*pi*I), CS arXiv:1509.07843v1 printed p.52 (31)–(32), as in merged #139. Prediction: the scaled norms q_i |z_i| stay in [0.9,1.2] at the next levels q=8 (P=20160), and q=9 (P=181440) if feasible. Test on linked child centers, attachment roots, and deterministic interior child multiplier chart samples including the original four directions; use nested angular grids at radii 0.95 and 0.99 where feasible, reporting actual completed densities, maxima and any failed points. Retain ancestor observations where feasible. The observed maximum is a lower estimate of the whole-copy supremum, not an upper bound. Compare independent 50- and 80-decimal-digit runs (or higher); require agreement of reported scaled norms within 1e-10, numerical period/linkage/mark tests inherited from #139, and local interval inclusion plus proper-period exclusions for centers, parent attachment solutions and dividing cycles at centers where possible. Root anchors alone cannot pass.

Decision: PREDICTION FAILS if a numerically linked, converged non-anchor sample lies outside [0.9,1.2] by more than 1e-10 (state certification separately); PREDICTION HOLDS (finite sampled evidence only, list certified levels) if q=8 completes both precisions, passes inherited linkage checks, center and all accepted primary chart samples are inside the interval with margin 1e-10, no required primary sample fails, and q=9 either passes the same tests or is explicitly infeasible under the resource budget. Primary chart samples are the four original directions (0.99, -0.95, +0.95i, -0.95i); any accepted denser-grid violation also fails. Otherwise INCONCLUSIVE, including unresolved precision/mark checks or ambiguous log branch. Report interval certification separately from numerical linkage and coverage. Do not extrapolate a pass to the full copy or infinite tail. A certified algebraic periodic orbit is not by itself a certified dividing mark.

## Inputs
Merged #139: ../cs_multiplier_locus_numerics_20261126/NOTE.md and measure.py; independent review https://github.com/dovvnloading/loops-research-archive/pull/139#issuecomment-7183305806. Prior audit #136; no modification to either.



Preregistration commit: 23bef1a1e81b711b56565ad3deab7e6238e376e4 (pushed before new computation). Base main: def5d4633e1ed0613ced4d11d22626e5114efb19. Reused the actual #139 measure.py (blob 240f149a4a96f4df7fd527a02a6e297b0e86aa07): extend.py dynamically imports it and uses its linked-level, continuation, branch and residual checks; optional fast_source.py builds a GMP recurrence accelerator for the same iterates and derivatives, not an interval engine. Local clone unavailable; local execution used a transcription of the relevant fetched #139 functions, and CI imports the actual path and compares the committed results. Local Python 3.13.5, mpmath 1.3.0, GCC 14.2, GMP 6.3.0. No #139 files changed.

## Reproduction (repository root)
```sh
python -m pip install mpmath==1.3.0
d=research/frontier/cs_multiplier_locus_extended_20261126
python -B "$d/fast_source.py" /tmp/cs-jet.so
python -B "$d/extend.py" --fast /tmp/cs-jet.so --dps 50 --steps 8 --max-q 9 --output /tmp/cs-low.json
python -B "$d/extend.py" --fast /tmp/cs-jet.so --dps 80 --steps 16 --max-q 9 --output /tmp/cs-high.json
python -B "$d/extend.py" --fast /tmp/cs-jet.so --dense-from /tmp/cs-low.json --max-q 7 --grid 128 --steps 8 --output /tmp/cs-dense7.json
python -B "$d/extend.py" --fast /tmp/cs-jet.so --dense-from /tmp/cs-high.json --min-q 8 --max-q 8 --grid 64 --steps 8 --output /tmp/cs-dense8.json
python -B "$d/chart_inputs.py" /tmp/cs-high.json /tmp/cs-inputs.json --fast /tmp/cs-jet.so
python -B "$d/certify.py" /tmp/cs-inputs.json /tmp/cs-certs.json
python -B "$d/summarize.py" /tmp/cs-low.json /tmp/cs-high.json /tmp/cs-dense7.json /tmp/cs-dense8.json /tmp/cs-inputs.json /tmp/cs-certs.json /tmp/cs-summary.json
python -c 'import json,sys; assert json.load(open(sys.argv[1])) == json.load(open(sys.argv[2]))' "$d/results.json" /tmp/cs-summary.json
python -B code/verify_physical_bridges.py
```
C++ compiler and GMP development headers required for the accelerated runs. CI pins the Python 3.12.12 image digest, mpmath and action SHAs and has a 40-minute timeout; raw files are uploaded, never committed back. No random inputs.

## Numerical results
Each primary run has 168 observations (six at each child, retaining ancestors). Absolute cross-precision discrepancy in serialized parameter, point, multiplier or log: at most 4.526e-37; scaled norm discrepancy at most 4.219e-37. All primary numerical proper-period, linkage, residual/correction and PLY containment checks passed. Maximum 50-digit residual/correction 9.998e-39 / 5.730e-39; 80-digit 6.055e-69 / 2.947e-69. All seed factors 1. The final attachment-ratio diagnostics for q=8 and 9 were 0.000101320112923 and 0.000101165743812. These are numerical diagnostics, not bounds on errors or certification of attachment.

All values below are q times the absolute attachment-continued log divided by 2*pi*i. Primary and dense counts count observations for each ancestor, not distinct parameters. "All" combines primary and dense.

| q | Child period | Primary count | Primary range | Dense count | All range | Nonunique PLY shifts (count) |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 3 | 42 | 0.951853264568–1.043275477879 | 1408 | 0.951750280480–1.045467122152 | 0 |
| 4 | 12 | 36 | 0.962949848214–1.034755847982 | 1152 | 0.962770264262–1.036715751342 | 0 |
| 5 | 60 | 30 | 0.972025343526–1.028253396118 | 896 | 0.970941164324–1.029911284247 | 0 |
| 6 | 360 | 24 | 0.976343206978–1.023796328257 | 640 | 0.975431701019–1.025192485533 | 0 |
| 7 | 2520 | 18 | 0.979509071354–1.020573657154 | 384 | 0.978717048808–1.021764930324 | 0 |
| 8 | 20160 | 12 | 0.981925946823–1.018130454617 | 128 | 0.981231275410–1.019157200693 | 0 |
| 9 | 181440 | 6 | 0.983831119554–1.016211685415 | 0 | 0.983831119554–1.016211685415 | 2 |

At q=9 the minus and minusI primary points admit integer shifts [-1,0,1] in the PLY disk. Both numerical runs agree on the principal lift. We have not certified the continuation path; to avoid relaxing the preregistered ambiguity guard, the overall result is INCONCLUSIVE even though q=8 alone passes the finite sample prediction and q=9 provides supporting numerical evidence with no out-of-range sample. The q=9 denser grid was omitted to stay within the computation budget.

## Sampling density
Independent radial starts at equally spaced angles on each of the two radii 0.95 and 0.99 in the child multiplier chart; nested grids are subsets of the highest grid. 1,408 distinct dense parameter attempts, no failures, 4,608 ancestor observations. Below are maxima on each level's own dense chart, not certified extrema. N is angles per radius (2N parameters).
 
| q | N=4 | N=8 | N=16 | N=32 | N=64 | N=128 |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 1.045063343386 | 1.045063343386 | 1.045063343386 | 1.045388381948 | 1.045437384300 | 1.045467122152 |
| 4 | 1.036314594205 | 1.036314594205 | 1.036314594205 | 1.036647154154 | 1.036682096521 | 1.036715751342 |
| 5 | 1.029550917198 | 1.029550917198 | 1.029550917198 | 1.029858134463 | 1.029877016492 | 1.029911284247 |
| 6 | 1.024898831908 | 1.024898831908 | 1.024898831908 | 1.025141623191 | 1.025168418429 | 1.025192485533 |
| 7 | 1.021530496673 | 1.021530496673 | 1.021530496673 | 1.021713493361 | 1.021751184304 | 1.021764930324 |
| 8 | 1.018975092362 | 1.018975092362 | 1.018975092362 | 1.019110849755 | 1.019157200693 | — |

Dense chart maxima stabilize numerically; e.g. q=8 rises from 1.018975092362 at N=4 to 1.019157200693 at N=64. This increases credibility of the observed range, but the sampled hyperbolic component chart and selected descendant points are not a covering of the Mandelbrot child copy, even at a single level. The finite maximum is only a sampled lower estimate of the supremum, not an upper bound. No claim about unsampled decorations, boundary, other components or infinite tails.

## Rigorous local certificates
77 local certificates succeeded: for each q=3,4,5,6,7,8,9, a critical center of period P, the parent attachment root system of period p=P/q, the p-cycle at the center, the four period-P chart solutions with their specified multipliers, and their four p-cycles. The attachment root is not claimed to be a primitive period-P cycle. It solves the parent p-cycle fixed point equation and multiplier raised to q equals 1; the principal argument enclosure selects exp(2*pi*i/q). The center has multiplier zero. The p-cycle multipliers are enclosed at the certified parameter disks. At every root or cycle, all proper divisors of its stated period are excluded by positive interval distance to its starting point. For q=9, directly refining the low-precision candidate seeds at 80 digits independently reproduced the 55-digit chart inputs and byte-identical certificate output.

certify.py uses complex Euclidean disks with integer centers/radii scaled by 2^320. Products use exact integer arithmetic with outward rounding, including integer-square-root magnitude bounds. Let G be the equation (scalar critical return or two complex equations for chart/attachment), x0 the dyadic center, Y a fixed dyadic approximate inverse, B the product of disks, and R the vector of radii. The certificate verifies componentwise that the upper bound of |Y G(x0)| plus the row-wise bounds of |I-Y DG(B)| applied to R is strictly less than R. This proves the self-map and contraction of x-YG(x) in the weighted maximum norm; the fixed matrix is nonsingular by the strict derivative bound, hence the fixed point is a true zero. For a dividing point the scalar test is uniform over the already certified parameter enclosure. Parameter and root/chart point radii are 2^-150, dividing point radius 2^-110. Every certificate has an explicit integer proper-period separation bound and multiplier disk; the worst self-map ratio is bounded above by 1.3350569e-5. mpmath.iv (110 dps) encloses the principal logarithm from the rectangular enclosure of the multiplier disk and checks its branch cut is avoided. The multiplier disk arithmetic itself is independent of floating-point Newton error estimates. No interval certification of a continuous parameter path, wake or combinatorial dividing mark is asserted: the identification with CS remains conditional on the numerical continuation.

## Machine-readable data
results.json is the exact parsed compact summary of the local runs, with header column arrays documenting each level and the certificate columns/order. Root/center and associated point entries are 55-digit seed coordinates: floor after scaling by 2^320 to reconstruct the dyadic disk centers; radii as above. The multiplier boxes, proper-period lower bounds, contraction/self-map upper bounds and scaled log intervals in certificate records are integers in units 1e-12, rounded outward; null scaled log interval means not applicable. The full exact disk triples and chart seeds, primary and dense observations and failure lists are regenerated as CI artifacts, not discarded by the numerical computation. summarize.py checks both precisions, inherited thresholds, coverage of the requested grids and the local certificate intervals against the primary observations; CI checks exact parsed equality against results.json. The local canonical JSON has 13333 ASCII bytes and FNV-1a 0xdc911d7f (transfer check only).

## Not established
No unconditional certification of the prescribed satellite wake/mark or global logarithm lift, no certified membership of all dense points in the prescribed copy, no covering or upper bound of the whole-copy supremum, no infinite-tail result, no MLC/JLC or Theorem D claim. No rigorous identification of the eq. (32) disk as the actual locus. Even the precise local certificates are not evidence of those implications.

**Status: OPEN / METADATA — INCONCLUSIVE.** GPT-6.2 assisted research; human specialist review not performed. Local computation completed; CI must independently reproduce it.
