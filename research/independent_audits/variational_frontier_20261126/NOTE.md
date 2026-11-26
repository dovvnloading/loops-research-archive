# Variational frontier investigation (2026-11-26)

**Result:** a written analytic theorem on the actual selected primitive-tip family and a sharp general round-neck approximation hierarchy. The global H2_CALIBRATION, H2_RESPONSE_REALIZATION and H3_COERCIVITY gates remain open; no ledger status changes.

Base main: 9a70093f4dcd9e4c7733244909d8f918369d1659. Research PR: [#174](https://github.com/dovvnloading/loops-research-archive/pull/174), opened before the mathematical derivations.

## Proof map

| File | Precise advance | Dependency |
| --- | --- | --- |
| [RANK_ONE.md](RANK_ONE.md) | Exact inner infinite-exterior response plus intrinsic rank-one neck correction, relative error coth L−1 rather than the previously used sech L | Dirichlet principle, trace and Fourier identities, Green function |
| [SPECTRAL.md](SPECTRAL.md) | Actual selected family has exactly one collapsing positive response eigenvalue; fixed-shape comparison O(4^(−p)); explicit lower bound for both inner eigenvalues; second-order expansion and limiting eigenline | Rank-one theorem, source's all-period orbit estimates and identified actual slit surface |
| [MULTIPOLE.md](MULTIPOLE.md) | Nested finite-rank response corrections, error O((r/R)^(2N+2)); exact Hilbert-space Schur update and intrinsic dipole formula with explicit quartic relative remainder | Rank-one variational construction, not a finite graph proxy |
| [SHARPNESS.md](SHARPNESS.md) | For each N, an actual regular planar electrode domain with strictly positive coefficient at the first omitted order; cannot improve the error exponent in general | Multipole theorem, maximum principle, harmonic expansion |

The selected actual surfaces have identically zero buffered canonical WAD. This work does not identify the exterior response with that WAD; it quantifies a distinct physical observable. The two uniformly positive directions come from an explicit half-annulus family in the actual upper half-plane, not from a conjectural spectral floor. The dying direction is the outer electrode, and its resistance has a logarithmic-capacity correction.

## Reproduce

From repository root, with Python 3 and only the standard library:

    python -B research/independent_audits/variational_frontier_20261126/check_bounds.py
    python -B research/independent_audits/variational_frontier_20261126/check_multipole.py

Executed locally, with the following results:

* 1,000 rational orbit-parameter cells (six orbit enclosures and uniform length/gap bounds).
* 1,836 rational Fourier-factor cases.
* 625 rational scalar Schur-complement cases.
* 72 rational multi-mode Schur cases, including singular Gram matrices and exact displaced-energy identity.
* 435 rational multipole remainder cases.

Both remote script blob SHAs matched the locally executed bytes: check_bounds.py 652e9bf8217facad92396478e633e93972e95055 and check_multipole.py b3400a9148c807cf46a9e10d61310fec54dbfe54. These are Git blob IDs, not SHA-256 hashes. No full local checkout, repository-wide test run, Lean proof, or successful CI run is claimed.

## Adversarial proof audit

* **Trace replacement:** use the original end trace on the round circle; never independently choose or silently impose its value. The full infinite-exterior nonconstant response remains in every variational integrand.
* **Zero mode:** the mean constraint is coercive only on the zero-inner-trace space; the nonempty electrode boundary is essential. The capacity identification explicitly checks the flux jump cancellation across the artificial circle.
* **Relative error:** prove the pointwise integrand inequality before infimization. No lower bound on a response eigenvalue, inverse response norm, or common approximate-graph kernel is used.
* **Actual geometry:** the orbit interval check uses the worst-case q=4^(−13) and covers the whole source chart J. Uniform interval lengths and gaps are proved, not inferred from finite-p strictness. The map to the fixed limiting geometry is explicitly bi-Lipschitz, identity near the outer circle, and preserves both slit banks.
* **Overlapping width tests:** for inner coercivity the two semicircle families may overlap. Use max ≥ half sum, not unproved parallel additivity.
* **Second spectral term:** first separate the limiting zero line, then invert only the positive two-dimensional block; its spectral floor is proved independently. The actual-to-fixed-shape comparison controls p-dependent potentials uniformly.
* **Multipole refinement:** the baseline contains every decaying mode; only the finite-cylinder excess is truncated. Reflection reduces correction rank only because the domain and each electrode label are fixed by conjugation.
* **Sharpness:** positivity in the symmetry sector forces a nonzero first allowed multipole. The counterexample establishes optimal exponents, not sharp universal constants or minimal terminal dimension.

The intended analytic claims are supplied as written proofs rather than machine-certified theorems. The proof search was self-audited by the same assistant; this is not independent peer review. Numerical values for the limiting inner response, capacity and second-order spectral invariant have not been certified.

## First remaining physical obstruction

The next missing input is not another Fourier inequality: the geometry must supply the appropriate future-compatible neck, trace identification, and bounded marked response data on *all* relevant dynamical blocks. In particular the actual unequal-footprint interface and preservation of returning classes, Value and sheet information under dynamical transitions are not consequences of this theorem. The zero canonical WAD on the selected family precludes simply declaring it to be the inner response. The sequence of selected parameters is not an infinite renormalization tower. H4 rigidity and MLC remain open.

We intentionally leave the ledger and central bridge registers unchanged: this is a direct analytic subcase, not a proposed promotion of a model-to-physical or global gate entry. No exhaustive review of priority in the potential-theory literature or of the entire archive was performed. Classical Dirichlet-to-Neumann, capacity, Fourier, variational and spectral methods are credited as standard; the source-defined selected-family application and preceding archive constructions are attributable to Matthew Robert Wesney. OpenAI ChatGPT GPT-6.2 materially assisted proof search, derivation, source inspection, adversarial checking, and exact arithmetic code. No human specialist verification has been performed.
