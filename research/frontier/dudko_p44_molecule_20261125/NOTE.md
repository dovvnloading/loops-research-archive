# P44-GM-1 — golden-mean pacman return calibration

**Status: imported** (known DLS/DL theorem specialized at the golden mean; exact scalar arithmetic proved below). No novelty or ledger-status change. Problem 4.4 remains **open**.

**Reviewed claim.** For the minimal-period local pacman operator R constructed by Dudko–Lyubich (DL) Proposition 5.41 at rotation angle t=(√5−1)/2, the fixed Siegel pacman has a one-complex-dimensional unstable manifold, and the eigenvalue of DR on its tangent is (7+3√5)/2=φ⁴, with φ=(1+√5)/2. This is an existential choice of the standard pacman and operator from the cited literature, not a claim about every local DLS normalization.

The original preregistration is preserved in [5bfa7f74a5a410be0a091d5d4e60fb44570467e0](https://github.com/dovvnloading/loops-research-archive/commit/5bfa7f74a5a410be0a091d5d4e60fb44570467e0), dated 2026-11-25, before the verifier. It specified a two-prime-step return and a multiplier coordinate. Independent review confirms these identifications for the DL construction only. The DLS construction alone permits a multiple of the minimal period. For another operator the eigenvalue conclusion is conditional on the existence of a hyperbolic fixed pacman with one complex unstable dimension, a locally biholomorphic α-fixed-point multiplier on its unstable manifold, and action of exactly T² on its neutral multiplier arc. None of these hypotheses for an arbitrary different operator is certified here.

## Primary-source review

- Dudko, *On the MLC Conjecture and the Renormalization Theory in Complex Dynamics*, [arXiv:2512.24171v1 §4.5](https://arxiv.org/html/2512.24171v1), Interpolation Problem 4.4: “Develop a Virtual Molecule version of the Near-Degenerate Regime.” The [published ICM 2026 PDF, p. 133 (physical p. 18)](https://epubs.siam.org/doi/pdf/10.1137/25M1807101#page=18) confirms the statement with lowercase typography. The setting is a primitive first quadratic-like renormalization, with virtual scales between the original copy and M^(n), not the next satellite copy M^(n+1) whose decoration contains the primitive copy. The two virtual cases are bounded-type satellite and near-neutral. The proposed virtual Julia sets are connected hulls of corresponding Cantor small Julia sets in J_f, containing the critical orbit only up to suitable first returns. Dudko distinguishes bounds deduced from assumed uniform hyperbolicity from the goal of constructing a priori control. Problems 4.3 and 4.4 together with the preceding arguments are proposed as a route to full MLC, not a proof of it.
- Dudko–Lyubich–Selinger (DLS), *Pacman renormalization and self-similarity of the Mandelbrot set near Siegel parameters*, JAMS 33 (2020), 653–733, [arXiv:1703.01206v3](https://arxiv.org/abs/1703.01206v3) (latest version, 29 December 2019). [p. 4](https://arxiv.org/pdf/1703.01206v3#page=4), (1.1) and Theorem 1.1: periodic rotation data give a periodic Siegel pacman with hyperbolicity. [p. 28](https://arxiv.org/pdf/1703.01206v3#page=28), Theorem 3.16: a compact analytic local self-renormalization is constructed. [p. 29](https://arxiv.org/pdf/1703.01206v3#page=29), Lemma 3.18: its action on indifferent rotation numbers is a positive iterate of the prime map; Remark 3.19 explicitly leaves the minimal iterate to DL. [pp. 61–62](https://arxiv.org/pdf/1703.01206v3#page=61), Theorem 7.7 and proof: one-dimensional unstable and codimension-one stable manifolds, with the constant α-fixed-point multiplier level equal locally to the stable manifold, and multiplier parametrizing the unstable manifold. This is a local theorem for the source-defined pacman, not an arbitrary raw quadratic polynomial.
- Dudko–Lyubich (DL), *Local connectivity of the Mandelbrot set at some satellite parameters of bounded type*, GAFA 33 (2023), 912–1047, [arXiv:1808.10425v4](https://arxiv.org/abs/1808.10425v4). [p. 31](https://arxiv.org/pdf/1808.10425v4#page=31), §3.2.6–3.2.7, Lemma 3.1 and the paragraph immediately after it, before (3.4): the unstable eigenvalue is expressly identified with the derivative of the m-step prime rotation map using the multiplier parametrization. Lemma 3.1's reference to DLS Lemma 3.17 is a numbering mismatch in v3; the result is Lemma 3.18, as correctly cited in DL §3.2.6. [pp. 73–74](https://arxiv.org/pdf/1808.10425v4#page=73), Proposition 5.41: DL constructs a new sector and pacman f_{*,new} whose local operator realizes the minimal prime period. Its proof explicitly invokes DLS Theorems 2.7 and 7.7 for the new operator. This supplies the extra clock hypothesis, not just the abstract periodicity of the angle.
- DLS Appendix C, [§C.3 p. 89](https://arxiv.org/pdf/1703.01206v3#page=89), is the unnumbered Molecule Conjecture, not Conjecture C.2 (§C.4 starts on [p. 90](https://arxiv.org/pdf/1703.01206v3#page=90)). It conjectures a fast piecewise analytic hyperbolic operator with a one-dimensional unstable direction, compact horseshoe of precompact bi-infinite orbits, parameter semiconjugacy away from the cusp, parabolic enrichment of the natural extension, hybrid stable lamination near mother hedgehogs and enriched unstable parameter neighborhoods. The prose's codomain of ρ is Mol; the away-from-cusp diagram uses ∂Mol minus the cusp. Local factorization is by prime steps, which have parabolic behavior at the cusp. The final paragraph expressly includes Theorem 7.7 in the conjecture. None of the global conjectural assertions is imported as a theorem.

The reviewer inspected the DLS and DL PDF statements and version stamps, the Dudko arXiv v1 HTML and published PDF. DLS and DL printed page numbers equal physical one-based PDF pages. The arXiv survey PDF exceeded the web reader's size limit. Raw PDF bytes were unavailable locally; CI must retrieve the exact versioned PDFs, check version stamps and page anchors, generate fingerprints, and compare to the committed record. Page locators are not proof verification, and SHA-256 is a reproducibility fingerprint, not independent authenticity verification.

<!-- SOURCE LOCK BEGIN -->
Generated by source_lock.py. Physical PDF pages are one-based. Anchor matches are locators, not independent theorem verification.

- **Dudko 2512.24171v1**: SHA-256 `8ede4bf8ccfe25a4f325cad41cb729f08f8b1d0d7103ed6dbc89015b1ff8d904` (12764975 bytes); [PDF](https://arxiv.org/pdf/2512.24171v1).
  - Problem 4.4: [18](https://arxiv.org/pdf/2512.24171v1#page=18).
  - Section 4.5: [18](https://arxiv.org/pdf/2512.24171v1#page=18).
- **DLS 1703.01206v3**: SHA-256 `d5d86b1166563221c4a6f57662bd7709c63de8a6ae3968da846304ede91454b5` (3256391 bytes); [PDF](https://arxiv.org/pdf/1703.01206v3).
  - Theorem 1.1: [4](https://arxiv.org/pdf/1703.01206v3#page=4).
  - Theorem 3.16: [28](https://arxiv.org/pdf/1703.01206v3#page=28).
  - Lemma 3.18: [29](https://arxiv.org/pdf/1703.01206v3#page=29).
  - Remark 3.19: [29](https://arxiv.org/pdf/1703.01206v3#page=29), [63](https://arxiv.org/pdf/1703.01206v3#page=63).
  - Theorem 7.7: [61](https://arxiv.org/pdf/1703.01206v3#page=61).
  - Theorem 7.7 multiplier coordinate: [61](https://arxiv.org/pdf/1703.01206v3#page=61), [66](https://arxiv.org/pdf/1703.01206v3#page=66).
  - C.3 Molecule Conjecture: [89](https://arxiv.org/pdf/1703.01206v3#page=89).
  - C.4 following heading: [90](https://arxiv.org/pdf/1703.01206v3#page=90).
  - C.3 statement page range: [89](https://arxiv.org/pdf/1703.01206v3#page=89).
- **DL 1808.10425v4**: SHA-256 `4a8f0f8c3ffd96c6a5a364340f2a7394fc75d0f355a7576040286c47365baec8` (3369779 bytes); [PDF](https://arxiv.org/pdf/1808.10425v4).
  - Lemma 3.1 / multiplier derivative: [31](https://arxiv.org/pdf/1808.10425v4#page=31).
  - Unstable eigenvalue identification: [31](https://arxiv.org/pdf/1808.10425v4#page=31).
  - Proposition 5.41: [73](https://arxiv.org/pdf/1808.10425v4#page=73).
<!-- SOURCE LOCK END -->

## Exact specialization

Let t=(√5−1)/2 and u=1−t. Then t²+t=1, 1/2<t<1, 0<u<1/2, t≠u. The irrational t has continued fraction [0;1,1,…]. DLS (1.1), (3.7) uses the prime map T, not the ordinary Gauss map:

- T(x)=x/(1−x) for x in [0,1/2];
- T(x)=(2x−1)/x for x in [1/2,1].

Since 1/t=1+t, T(t)=2−1/t=1−t=u and T(u)=u/(1−u)=t. Thus t has minimal prime period 2, not 1, and both points lie strictly inside their branches, away from 0, 1/2 and 1. Choose the minimal-period operator furnished by DL Proposition 5.41; DLS Theorem 7.7 supplies the one-complex-dimensional unstable manifold W^u and multiplier coordinate for that operator.

To identify the derivative, let μ(f) be the multiplier on W^u and x=(log μ)/(2πi), choosing the local logarithm branch with x(f_*)=t. The coordinate is locally biholomorphic. For real x near t the associated pacmen are indifferent, so Lemma 3.18 gives x(Rf)=T²(x(f)) modulo integers; choose the germ fixing t. Both sides are holomorphic near t (the rational branches have nonzero denominators), so the identity theorem gives equality of germs. Differentiation at the fixed point identifies DR restricted to T_{f_*}W^u with (T²)'(t), just as stated in DL §3.2.7. This is not an inference from combinatorics alone and does not compute the full Banach-space spectrum by a matrix.

The two derivatives are T'(t)=1/t² and T'(u)=1/(1−u)²=1/t², hence

    λ=(T²)'(t)=t^(-4)=(2+t)²=5+3t=(7+3√5)/2>1,
    λ²−7λ+1=0.

By the imported hyperbolicity and unstable dimension this is the unique unstable eigenvalue for the chosen local operator. For a return realizing 2k prime steps the corresponding scalar is λ^k, provided it has the same coordinate identification. One prime step is not a fixed-point return at t. The minimal-period theorem is indispensable for the stated number.

As an independent scalar check the branch Möbius matrices are U=[[2,−1],[1,0]] and L=[[1,0],[−1,1]]. Their product LU=[[2,−1],[−1,1]] has determinant 1 and derivative 1/(1−t)²=t^(-4). The verifier uses exact rational arithmetic in Q[t]/(t²+t−1); it checks the brackets, denominators, orbit, matrix product, derivative and polynomial identities, and rejects equality of the one- and four-step scalars with the two-step scalar. It uses no numerical spectral fit, tolerance or discretization. The analytic status and dimension fields in results.json are imported facts, not outputs proved by the arithmetic.

## Limits and hostile checks

This is an imported local periodic-Siegel calibration, not a new theorem or a primitive near-molecule virtual Julia-set construction. No virtual bounds, finite-return critical-orbit containment, distortion/width/modulus comparisons, uniformity over the molecule, arbitrary-rotation result, satellite cascade modulus estimate, compact horseshoe, global fast operator, cusp/parabolic extension, KKL Lemma 6.24, Problem 4.3, Problem 4.4, new ledger theorem, or MLC is established. No implication from this scalar to virtual geometry is supplied. This is a limitation of the present argument, not an impossibility theorem for other methods. In particular the locally sourced multiplier coordinate must not be transferred to an independently defined operator without proof, and the periodic slice avoids cusp degeneracy.

## Reproduce

From repo root (Python 3.12; the arithmetic needs no dependencies):

```sh
cd research/frontier/dudko_p44_molecule_20261125
python -B verify.py --output /tmp/p44-results.json
cmp results.json /tmp/p44-results.json
python -m pip install pypdf==5.9.0
python -B source_lock.py --update-note
python -B source_lock.py --show-statements
```

For an offline replay use the exact PDFs named 2512.24171v1.pdf, 1703.01206v3.pdf, 1808.10425v4.pdf via --pdf-dir /path/to/pdfs and compare their hashes to sources.json. The show-statements flag prints source pages locally. No PDFs are committed. CI checks arithmetic bytes, source fingerprints, version stamps, anchors and regenerated NOTE against the committed files. Any missing/mismatched provenance fails; no bot writeback or skipped verification. CI runs for this PR's changed paths, corresponding main pushes and explicit dispatch. TSV registration is standalone (EXPLORATION for verify.py, METADATA for source_lock.py); it changes no ledger or physical bridge status. The JSON contract checker does not require entries for this directory.

Prior CI: 45740858335 / 139645213163 reproduced the arithmetic but failed the source-lock SyntaxError; 45740852068 / 139645192288 also failed the writeback and required-lock steps. Both repo-wide checks reported the two unindexed scripts. The quoting correction in 5cf61a195cc74c1fc5ac2ef5bcd26f9857860578 had no CI. These are historical failures, not green evidence.

AI disclosure: author disclosed ChatGPT (GPT-6.2) source comparison, mathematical argument and verifier/workflow construction. Independent reviewer: ChatGPT (GPT-6.2), source verification, scope/status correction and CI repair. No human specialist verification claimed. Mathematics credited to the cited authors.
