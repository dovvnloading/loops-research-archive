# Quantitative frontier audit (2026-11-26)

Base: main at 9a70093f4dcd9e4c7733244909d8f918369d1659. This PR was opened as a draft before substantive proof development and the results were committed as they were obtained.

**Target:** the affine-shape and actual marking subproblem of VIRTUAL_END_BLOWUP_REALIZATION, with relevance to VIRTUAL_DISCONNECTED_MARKING_TRANSFER and H2 length-calibration. The frozen ledger at the base states that the former requires, for every proof-used infinite address, an authorized analytic end space with protected accesses, obstacles, sheets, chronology, actions, relative covers, proper/end-proper intervals and complete-horizon final-root naturality. We do not supply all those data, and do not promote its status.

## Main results (proposed written mathematical theorems, with exact certificates where indicated)

| Result | Proof |
|---|---|
| Actual fixed 3/9 tip: the normalized affine chart determines the entire backward history | [HISTORY.md](HISTORY.md): independent analytic proof via the asymmetric square-root singularity at the positive critical value |
| Quantitative stability and finite marker separation for each fixed depth | [HISTORY_METRIC.md](HISTORY_METRIC.md): compactness, analytic finite-order detection, chain rule |
| Physical end dimension strictly between 89/150 and 19/32, angular dimension exactly 1/2; no single uniform angular-to-physical power law | [DIMENSION.md](DIMENSION.md), [check.py](check.py): rigorous positive operator criterion and exact integer certificates |
| One pre-Schwarzian value, at any real input in the invariant interval, determines every past symbol; explicit exponential separation | [SCALAR.md](SCALAR.md), [check_scalar.py](check_scalar.py): enclosure of the **entire infinite-history family**, not a sampling argument |
| The scalar history Cantor set has exactly the physical end dimension | [SCALAR.md](SCALAR.md), §4: separate backward-suffix and forward-prefix mass bounds for the same pressure |
| One explicit affine ratio of three actual attachment marks determines the entire chart; its image is bi-Lipschitz to the scalar history set and has the same dimension | [MARKERS.md](MARKERS.md): uniform pre-Schwarzian ordering, double integral, explicit marker triple and reflected binary order |

The last result resolves the particular affine observable-quotient question left open in the prior analytic-history audit, at this native fixed tip. It is a stronger answer than continuum-many shapes or a finite marker list for each finite depth. The relevant finite-dimensional observable is a real scalar, not a finite-bit/discrete state.

## Physical inputs, evidence and review

- [Earlier direct-decoration end cofinality](../../independent_audits/decoration_end_cofinality_20261126/NOTE.md), §5, blob 53c9bbe181525c990afd2431a3bd5a547279ceea at the inspected base: exact Misiurewicz parameter isolator, first ambient q=2,n=1 physical branch and sector identification. The four actual sector lifts were checked against this source again. The actual root portrait, not an auxiliary model, is used.
- [Earlier analytic-history graph](../../independent_audits/decoration_analytic_history_end_blowup_20261126/NOTE.md), §§1–6 and 8: common analytic neighborhood, normalized suffix limits and uniform suffix stability, actual inverse formulas, pre-alpha marks and independent ordered-sector parity. Its physical inputs are retained, not independently reconstructed.
- [Earlier exponential shrinking](../../independent_audits/decoration_exponential_shrinking_20261126/NOTE.md): actual cylinder shrinking and end coding; the present work supplies the sharper dimension proof and its certificate.
- The underlying source framework is Kahn–Lyubich, *A priori bounds for some infinitely renormalizable quadratics: II. Decorations*, arXiv:math/0609046v2, §§2.1–2.2, including Lemma 2.1, as cited and instantiated in the earlier audit. This PR does not re-prove the entire source-specific landing or complex-domain construction. The general limit-geometry/scenery framework is classical: Bedford–Fisher, ETDS 17 (1997), 531–564; Bedford–Fisher–Urbański, PLMS 85 (2002), 467–492. Bibliographic metadata and published abstracts checked, not a comprehensive priority search. See SCALAR.md for citations. No theorem from those scenery papers is required by the new proofs.

The two independent standard-library checkers ran locally under Python 3.13.5. The executed source bytes match the committed Git blobs.

| Certificate | Result | Git blob |
|---|---|---|
| Pressure inequalities on 512 depth-nine physical states at each of two exponents | strict lower/upper relative gaps at least 154/298 ppm | c6b387955c2963e7db6ae8bd57f4ea43d9bd4d1d |
| All-history pre-Schwarzian enclosures on 4096 closed cells, 20 refinement rounds | minimum L-minus-R separation at least 6911 ppm (rounded down); branch derivative at most 5/12 | a2b15423f430efbb64ca531861fdb4ce2fb60a33 |

Run from the repository root, without Python -O (assertions are the certificate checks):

~~~sh
python -B research/frontier/quantitative_frontier_audit_20261126/check.py
python -B research/frontier/quantitative_frontier_audit_20261126/check_scalar.py
~~~

## Adversarial review checklist

1. A normalized affine limit is not a general conformal invariant. Analytic injectivity in HISTORY.md uses the actual asymmetric critical value and a common continuation domain. Reflection cannot hide that singularity. The scalar certificate gives an independent, quantitative proof of injectivity.
2. The all-history enclosures start from a proven uniform bound using the chain-rule geometric series. Each step includes both branches and the complete outward image of each closed input cell. Inductively they enclose every infinite history, without asserting iteration convergence. The final strict disjointness is checked on every cell; the derivative sign is positive for L and negative for R.
3. Pressure tests use outward square-root and rational-power enclosures, positive integer test vectors, and independently verified strict inequalities rather than a numerical eigenvalue or an assumed convergence rate. The analytic probability argument uses the correct forward-prefix word order. The scalar set proof explicitly reverses the relevant word concatenation for suffix cylinders.
4. Two selected angles per physical point remain distinct. The upper representative has the reflected affine R branch; the angular contraction is 1/4 but neither the real cylinder length nor the full complex native cylinder diameter has a universal single-exponent relation to it.
5. Marker ratio injectivity uses constant sign of the pre-Schwarzian difference over the full real interval and positivity of the normalized real derivatives. The three marks are actual pre-alpha attachments, not precritical points. The resulting order is reflected binary, not ordinary lexicographic in the L/R letters.
6. The new results concern fixed-tip affine charts, actual physical/angle sets, and length observables. They do not supply universal modulus/width estimates or uniform constants over a varying tower. No claim of a finite-bit encoding, new relative-cover construction, root authorization, or solution of MLC is made.

## Status

VIRTUAL_END_BLOWUP_REALIZATION, VIRTUAL_DISCONNECTED_MARKING_TRANSFER, H1–H4 and UPTCR remain open. No frozen ledger, manuscript, or central proof-bridge register changes are proposed: the work directly analyzes the already supplied actual branches and charts rather than introducing a new model-to-physical identification. The submitted notes and code are the evidence for the proposed fixed-parameter subclaims, for independent review before integration. No full repository test or Lean formalization was performed. No worldwide priority claim; a fixed-tip result is not a universal renormalization theorem.

AI assistance: OpenAI GPT-6.2 materially assisted the repository/source investigation, proof search, adversarial checks, exact arithmetic code and execution, and drafting. Independent human specialist verification has not yet been performed.
