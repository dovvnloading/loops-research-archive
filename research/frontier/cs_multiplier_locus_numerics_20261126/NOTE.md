# CS actual dividing-multiplier locus: numerical diagnostic

**Verdict: ESTIMATE IS LOSSY (sampled evidence only); whole-copy supremum and infinite-tail behavior INCONCLUSIVE.** All preregistered finite tests pass. On the linear address through period 2520, the actual sampled radial maximum decreases from 0.34775849 to 0.14579624 while the full-disk maximum reaches 11.34877. The observed q_i L_i stays in [1.02057,1.04328]; the final sample/disk ratio is 0.0128469. This is evidence of loss in the disk estimate on the sampled actual multipliers, not a uniform upper bound on A_i, a new radial theorem, or MLC. Status: NUMERICAL EVIDENCE / METADATA only; no theorem status change.

## Limits
The whole-copy supremum is not certified by finitely many samples. Numerical continuation identifies candidate dividing cycles; no interval proof of wake membership, no proof of a uniform tail bound. The angular inference identified in merged #136 is untouched. No MLC/JLC, rigidity or nonrigidity claim. The square-growth control starts at 3, so tests the recurrence, not the unknown large initial threshold N of Theorem D.

## Preregistration (before any numerical computation)

The text of the definition, sampling plan and decision rule below is unchanged from [preregistration commit b3fdd4b](https://github.com/dovvnloading/loops-research-archive/commit/b3fdd4b342a5b5b3b14d4d9f01e7f918029c7a0a), pushed before the initial Newton trial.
Write f_c(z)=z²+c, q_i the relative satellite denominator, P_i=product_{j<=i} q_j, P_0=1. Let M_i be the actual closed tuned copy with prefix through i. CS Theorem 4.6, arXiv:1509.07843v1 printed pp.51–52, (31)–(32) p.52: the i-th dividing orbit a_i of f_c has absolute period P_{i-1}, and multiplier rho_i=(f_c^{P_{i-1}})'(a_i). With a suitable branch, their equation (32) is
    | log(rho_i)/(2*pi*I) - (1/q_i - I*R_i) | <= R_i,
    R_i = log(2)/(2*pi) * P_{i-1}/q_i.
Proposition 6.7(b), p.63, says |G^{m_i-1}(z)|<=r. For these one-digit rotations G^0 is identity, so Steps 2–3, (49) p.63 and (50)–(51) p.64, bound |z|<=r by bounding the entire disk. Define the actual radial target A_i=sup_{c in M_i}|log(rho_i(c))/(2*pi*I)| with the branch continued from log(rho_i)=2*pi*I/q_i at the attachment root. If multiple branches of (32) are possible, report this explicitly: principal-log modulus is a branch-independent lower bound on any lift's modulus, not necessarily the intended branch. Disk radius R_i and exact disk maximum B_i=sqrt(q_i^-2+R_i^2)+R_i are comparison quantities, not observations. S_i=P_{i-1}/q_i.

Sample the attachment root r_i, the center c_i of the child hyperbolic component (period P_i), and deeper centers c_j for j>=i; attempt additional boundary/near-boundary samples by child multiplier continuation if feasible. Primary statistic L_i=max observed |z_i|, including the anchor 1/q_i, a finite sampled lower estimate of A_i, not an upper bound. Also report center-only displacement |z_i(c_i)-1/q_i|, q_i L_i, L_i/B_i, and real log growth log|rho_i|/(2*pi) to distinguish branch artefacts. Track the marked parent orbit from its known root, not a free choice among periodic points. Check child linkage by continuation of its attracting orbit from the center toward multiplier 1 and comparison with the parent bifurcation; check primitive period, residuals, Newton correction and repeated precision (at least 50 and 80 decimal digits). Flag unresolved levels rather than silently substituting unrelated centers or roots. No interval certification claimed; numerical uncertainty estimated by cross-precision differences and correction estimates. Lift by continuity where available, flag ambiguity if a lift is not checked. Use no random seeds (deterministic search). Addresses: linear (3,4,5,6,7), bounded (3,3,3,3,3), square (3,9,81) through comparable periods (max 2520); square q_4=6561 implies P_4=14348907 and is not a reasonable direct-iteration control. Extend only if feasible.

Decision rule fixed now: use all accepted levels, report descriptive OLS slope of log L_i vs log S_i (linear and bounded; square S_i constant so slope undefined), endpoint slope, and leave-one-level-out slope range, plus numerical sensitivity (two precisions). Separately fit log L_i vs log q_i for nonconstant q. The sample is not an iid population; no statistical confidence interval or asymptotic inference. TRUE GEOMETRY DEGENERATES (evidence only) if at least five linked linear levels have L_i exceeding 1/2 at any of the final two levels with increasing L_i over both final steps and a positive log-log slope >=0.5 vs S_i; such samples really violate radial smallness at those finite levels, not proof of divergence. ESTIMATE IS LOSSY (sampled evidence only) if five linked linear levels and both controls (at least three square, five bounded) succeed, the linear last two L_i are <=1/2, all linear q_i L_i<=3, L_5/B_5<=0.05, and slope vs S_i<=0.25; this means sampled multipliers stay controlled despite disk blow-up, not a uniform bound on A_i. Otherwise INCONCLUSIVE. Even when the lossy rule passes, the unsampled whole locus and infinite tail remain inconclusive. Root anchors alone are insufficient. The actual domain r in CS is not numerically specified; 1/2 is only its stated upper limit, not a guarantee of entrance for any sample.

## Inputs
Merged #135 and #136 and the independent #136 review; [growth audit](../cs_growth_hypothesis_20261126/NOTE.md), [its source lock](../cs_growth_hypothesis_20261126/sources.lock.json). Independently opened and visually checked arXiv unversioned PDF stamped v1, pp.52,63,64. SHA256 inherited from #136 read-only CI exact versioned URL https://arxiv.org/pdf/1509.07843v1 : 71c03718203b91ae81f5b7e138620a086cdf038b345cf689a24ed2932d72384f (831082 bytes); author 2022 PDF https://www.ma.imperial.ac.uk/~dcheragh/Research/2015-2.pdf : b1d6b0952247efc3cd7a6e0602dbb8246b43b9edf7b3c5d0da942cc822246c25 (851587 bytes). Not hashes of the web rendering or newly downloaded bytes. Theorem D p.6 and (44) p.62; author edition (6.8) p.62, (4.1)–(4.2) pp.51–52 and Prop.6.7 pp.62–63 per #136. Theorem C is existential, not whole-class containment.


## Numerical implementation and identification checks

For F=f_c^p, start at the center of the parent component with z=0, multiplier 0 (p=1, c=0 initially). Solve F(z)-z=0 and F_z(z)-lambda=0 by two-variable complex Newton along the straight segment in the multiplier disk from 0 to exp(2*pi*I/q). This gives the attachment root r_i by the nonsingular parent-cycle equations, rather than attempting singular Newton on the period-P_i parabolic cycle at multiplier 1. The jet is accumulated at each step using F_z=A, F_c=B', F_zz=H, F_zc=D, with updates A'=2*z*A, B'_next=2*z*B'+1, H'=2*(A*A+z*H), D'=2*(A*B'+z*D). The derivative of the parent multiplier along its fixed cycle at the root is D+H*B'/(1-A). Initialize the center search at r_i+lambda/(q_i^2*(d rho/d c)), with the deterministic alternative factors in measure.py; all 13 levels converged with factor 1. Solve f_c^P_i(0)=0 by damped scalar Newton, rejecting escaped iterates. Check all proper divisors of P_i for a positive critical return gap. Separately continue the child attracting orbit from (c_i,0) to child multipliers 0.99 and 0.9999. Accept its parent linkage only if the latter parameter distance to r_i, divided by |c_i-r_i|, is <0.0002 and is <0.02 times the corresponding ratio at 0.99. This checks approach to the same root (not just period equality). For every candidate root and sampled dividing cycle, check minimal-period gaps; the r_i root is the root of the child component in this numerical identification, although its dividing orbit has period P_{i-1}.

For every ancestor dividing cycle, keep the periodic point marked by its attachment root and continue F(z)=z along the child chart path reversed from the near-root point to the center; the short connecting segment from root to the near-root point is numerical, not a certified path in M_i. Continue along the subsequent child component paths. Adaptive bisection if Newton fails or the argument increment or log-modulus increment of rho exceeds 0.2. Track angle by adding arg(rho_new/rho_old) to the attachment angle 2*pi/q_i, not by resetting the branch after each step. At each observation check the continued lift against (32), and enumerate all integer shifts in that disk. Check that the lift is in the principal strip; no alternative shift passed at any observation, even for the largest disk. This does not establish uniqueness of the log branch on all of M_i.

At depth j, sample r_j, c_j, and four parameters in the period-P_j hyperbolic component with attracting multiplier 0.99, -0.95, +0.95I, -0.95I. Evaluate all ancestor multipliers there. This yields six samples per descendant depth (including the root anchor); 90 for linear, 90 bounded, 36 square, 216 observations per precision, not independent data points. Near-boundary points are not entire limb boundaries or external decorations. Counts decrease toward the deepest level (30,24,18,12,6 for a five-level sequence); this may bias maxima down at depth. In fact every maximum occurs on the -0.95I direction of its own component, not an anchor or a deeper point. The center-only values and displacements independently exhibit the same scale trend. There is no certified parameter enclosure or exhaustive copy scan.

At both 50 and 80 decimal digits use mpmath 1.3.0 (pure Python backend locally), nominal 8 and 16 continuation subdivisions, respectively; halve on failure down to a step of 1e-5. Newton iterations capped (30 for the chart and fixed cycle, 45 for center); center damping tries 16 powers of two. Require both residual and Newton correction below 10^(12-dps) at accepted solves; primitive gap threshold and PLY disk excess tolerance are tol^0.4. Escape, nonprimitive period, failed linkage, or failed continuation is an error, not silently dropped data. The code aborts rather than emitting a success summary on a failed requested level. Compare serialized 26-significant-digit roots, centers, sample parameters, rho and lifted z across runs with tolerance 1e-22; compare labels and integer shifts exactly. This is an empirical convergence/error diagnostic, not an interval enclosure. The change of precision and grid is joint, not a formal a posteriori inverse bound.

## Results

All 13 levels accepted at both precisions. Machine-readable [summary.json](summary.json) contains all per-level primary statistics, center and maximum complex logarithmic multipliers, root/center parameters, primitive gaps, attachment ratios, ambiguity counts, fits and diagnostic thresholds (12 significant digits). Full per-sample records at both precisions, including individual periodic points, rho, lifted z, disk excesses, primitive gaps, Newton residual/correction estimates and linkage diagnostics, are regenerated by measure.py as raw JSON (26 significant digits); the workflow uploads it as an artifact and compares the compact summary by exact parsed JSON equality.

| Address | i | q_i | P_i | S_i | disk B_i | sample L_i | q_i L_i | L_i/B_i |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| linear | 1 | 3 | 3 | 0.333333 | 0.372128 | 0.347758 | 1.043275 | 0.934513 |
| linear | 2 | 4 | 12 | 0.75 | 0.346074 | 0.258689 | 1.034756 | 0.747496 |
| linear | 3 | 5 | 60 | 2.4 | 0.596575 | 0.205651 | 1.028253 | 0.344719 |
| linear | 4 | 6 | 360 | 10 | 2.218875 | 0.170633 | 1.023796 | 0.076901 |
| linear | 5 | 7 | 2520 | 51.428571 | 11.348772 | 0.145796 | 1.020574 | 0.012847 |
| bounded | 1 | 3 | 3 | 0.333333 | 0.372128 | 0.347758 | 1.043275 | 0.934513 |
| bounded | 2 | 3 | 9 | 1 | 0.461432 | 0.348113 | 1.044338 | 0.754418 |
| bounded | 3 | 3 | 27 | 3 | 0.800678 | 0.348119 | 1.044357 | 0.434780 |
| bounded | 4 | 3 | 81 | 9 | 2.040182 | 0.348119 | 1.044356 | 0.170631 |
| bounded | 5 | 3 | 243 | 27 | 5.975755 | 0.348119 | 1.044356 | 0.058255 |
| square | 1 | 3 | 3 | 0.333333 | 0.372128 | 0.347758 | 1.043275 | 0.934513 |
| square | 2 | 9 | 27 | 0.333333 | 0.153811 | 0.112938 | 1.016439 | 0.734264 |
| square | 3 | 81 | 2187 | 0.333333 | 0.075562 | 0.012369 | 1.001900 | 0.163695 |

Here p=P_{i-1} and P=P_i in the JSON. Complex values are [Re,Im]; center_z refers to z_i(c_i), not the dynamical periodic point. In particular, on the linear address the center displacement from the anchor 1/q_i drops from 0.01621559 to 0.00317047, and log|rho_i(c_i)|/(2*pi) drops from 0.01621482 to 0.00316603. The final dividing orbit at the actual period-2520 center has lifted z_5=0.142689508942-0.00316603193670 I, and at the largest sampled point z_5=0.145752008578-0.00359091101733 I. These are measurements of the absolute-period-360 dividing multiplier, not the straightened quadratic's fixed point. The full-disk maximum is nearly 78 times the sampled maximum at level 5. Bounded-type control L_i nearly plateaus while the disk grows; square control falls approximately as 1/q_i while S_i is constant.

### Rates and uncertainty

Descriptive regression log L = intercept + slope * log X over all accepted levels. Leave-one-level-out range describes sensitivity to the sampled levels, not an iid confidence interval.

| Address | X | OLS | Endpoint | Leave-one-out range |
|---|---|---:|---:|---:|
| linear | S_i | -0.164614582 | -0.172520675 | [-0.202493110,-0.133519382] |
| linear | q_i | -1.026218508 | -1.025965348 | [-1.027387241,-1.024724721] |
| bounded | S_i | 0.000189984 | 0.000235523 | [0.000004601,0.000284290] |
| bounded | q_i | undefined | undefined | constant q_i |
| square | S_i | undefined | undefined | constant S_i |
| square | q_i | -1.011461030 | -1.012278332 | [-1.023720557,-1.006557219] |

The 50- and 80-digit L_i and slopes agree exactly at the stored 26 significant digits. Largest absolute cross-precision differences among compared complex values (after serialization) were 5.53e-41 (linear), 9.03e-49 (bounded), 4.32e-41 (square); tiny differences in near-zero components can still occur. Empirical maximum Newton residual/correction over accepted operations (rounded upward):

| Address | 50-digit residual / correction | 80-digit residual / correction |
|---|---|---|
| linear | 1.00e-38 / 5.73e-39 | 3.16e-69 / 2.95e-69 |
| bounded | 1.00e-38 / 5.73e-39 | 8.99e-69 / 1.31e-69 |
| square | 1.00e-38 / 5.73e-39 | 1.65e-69 / 2.16e-69 |

These are measured residuals and corrections, not proven solution error bounds. Minimum high-precision critical primitive gaps were 0.00394149, 0.00749628, 0.04360797 respectively. Minimum sampled dividing-cycle gaps (including the convention 1 for period one) were 0.0165396, 0.0298521, 0.115528. Maximum final normalized attachment distances were 0.000101720, 0.000102219, 0.000100893 respectively; their ratios relative to 0.99 distances passed the preregistered linkage check. Maximum positive disk excess at 80 digits was <3.2e-79 (roundoff at attachment). None of the 216 high-precision observations had multiple PLY-admissible integer shifts. No sampling or conditioning uncertainty is reduced by reporting more numerical digits.

**Decision:** all linear last-two L_i <=0.5; all linear q_i L_i <=1.044<3; L_5/B_5=0.0128469<0.05; OLS vs S_i=-0.164615<=0.25; both controls succeed at required lengths. Therefore the preregistered sampled lossy rule passes and the degeneracy rule fails. Sampled multipliers are much closer to 1/q_i than to a P_{i-1}/q_i-sized locus; the finite observations support seeking a sharper radial estimate. They do not prove that the actual supremum A_i is controlled, and they cannot rule out unsampled parameters with large multipliers even at a measured level. An actual upper bound would require additional geometry or certified coverage. The finite levels are low-to-moderate type, not a demonstration of the asymptotic high-type domain.

## Reproduction and provenance

Local Python 3.13.5, mpmath==1.3.0; CI pinned Python 3.12.12 container and mpmath==1.3.0. No random seeds, external numerical data, compiled backend required, or third-party PDF committed. Base main at preregistration e4143efbddc55639581ea2471eea93206260eabd; #137 advanced main without touching source-index rows. Source hashes above are inherited from #136's CI lock, not new PDF downloads (local network DNS unavailable); primary rendered pages were independently inspected. Local generated compact summary SHA256 0adb0c726fd7146d9960e432a7b25d2f0532dbd8641cf01ee3e02843603a4bbf and raw JSON SHA256 3f6a33759c6bf0129830d3670996dace5c61e53c839b19420077f3fb32bbfe61, before transfer; raw includes numerical residual diagnostics and is not required to be byte-identical between environments. The summary is compared by exact parsed JSON equality, not whitespace.

From repo root, in a Python 3.12 environment:

    python -m pip install mpmath==1.3.0
    d=research/frontier/cs_multiplier_locus_numerics_20261126
    python -B "$d/measure.py" --output /tmp/cs-locus-raw.json
    python -B "$d/summarize.py" /tmp/cs-locus-raw.json /tmp/cs-locus-summary.json
    python -c 'import json,sys; assert json.load(open(sys.argv[1])) == json.load(open(sys.argv[2]))' "$d/summary.json" /tmp/cs-locus-summary.json
    python -B code/verify_physical_bridges.py

Read-only CI regenerates both JSONs in a disposable runner; upload is an Actions artifact, never a commit or push. The committed summary was produced by the research worker before PR creation. Code and summarized results are a numerical diagnostic, not a registered mathematical bridge; both executable sources are registered METADATA. GPT-6.2 source-reading, code generation, numerical execution and analysis; no independent human specialist verification.

**Not established:** the whole-copy supremum A_i at any level; a uniform bound or asymptotic decay of A_i; rigorous branch continuation or external-ray/wake certification for all sample points; a certified error enclosure; completeness of the near-boundary sampling; the high-type initial threshold for Theorem D in the square control; entrance to any particular small r or the NP cone; repair of the separate angular inference or multiplier-identification induction in #136; extension of Theorem D; rigidity, nonrigidity, MLC or JLC; a geometric modulus bound. The angular gap is untouched, even though sample coordinates are recorded. No public ledger status changes. The result is evidence-not-proof.
