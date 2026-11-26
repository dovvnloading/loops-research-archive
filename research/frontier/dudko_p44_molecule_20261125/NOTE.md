# Claim (preregistered 2026-11-25, before verifier)

**P44-GM-1.** At the source-defined periodic Siegel pacman with rotation number θ=(√5-1)/2, the local renormalization return realizing exactly one two-step cycle of the prime rotation-number map (Dudko–Lyubich–Selinger, arXiv:1703.01206v3, (1.1)) has one complex unstable direction. Its unstable eigenvalue is (7+3√5)/2, provided the multiplier coordinate is the local transverse parameter of that return, as asserted for the source operator. Test this value and the identification of the return against the actual source; if either identification fails, report the precise conditional or negative result instead of substituting a different operator.

Preregistration: commit [5bfa7f74a5a410be0a091d5d4e60fb44570467e0](https://github.com/dovvnloading/loops-research-archive/commit/5bfa7f74a5a410be0a091d5d4e60fb44570467e0), before arithmetic verifier and calculation. Claim unchanged.

**Decision: YES for the suitably constructed minimal-period local operator.** Status: **proved** (exact specialization of **imported** hyperbolicity and minimal-period theorems; finite exact arithmetic certificate). The infinite-dimensional analytic facts are imported, not proved by code. Problem 4.4 remains **open**. No novelty claim.

## Limits

This is a periodic Siegel boundary slice of the molecule hyperbolicity program (DLS Appendix C), not a virtual primitive Julia-set construction. No statement about virtual bounds, arbitrary rotation numbers, the entire fast molecule horseshoe, satellite cascade moduli, KKL Lemma 6.24, or MLC is preregistered. Distinguish the prime combinatorial clock from a possibly higher iterate of an analytic self-operator. No new global archive gate is claimed.

In particular, the result does **not** establish:
- A priori bounds in any primitive near-molecule copy, or a virtual Julia set with the requisite finite-return critical-orbit containment.
- A comparison of the derivative with distortion, widths, puzzle moduli, or geometric degeneration at the virtual levels.
- Uniform hyperbolicity over the molecule or a compact horseshoe, existence of a global fast operator, or extension across cusp/parabolic enrichment.
- An unstable eigenvalue for every choice of DLS local operator, a numerical enclosure of the full Banach derivative, or an eigenvalue for one prime step at a fixed point (the golden angle is not fixed by one step).
- Problem 4.3, Problem 4.4 itself, a new ledger theorem, or MLC.

The survey's virtual near-Molecule problem concerns primitive first quadratic-like renormalizations; this periodic Siegel object is a calibration for the possible hyperbolicity input, not itself an example of the primitive virtual regime. No bridge from the calibration to virtual bounds is supplied. The strongest bounded negative conclusion about that bridge here is that no such bridge follows from the imported local theorem and the two-step calculation alone; this is not an impossibility theorem for other methods.

## Primary sources and exact statement locators

Dudko, *On the MLC Conjecture and the Renormalization Theory in Complex Dynamics*, [arXiv:2512.24171v1](https://arxiv.org/html/2512.24171v1), §4.5, **Interpolation Problem 4.4** (verbatim):

> Develop a Virtual Molecule version of the Near-Degenerate Regime.

Immediately afterward, the author says the two remaining problems plus the preceding arguments should imply full MLC, and distinguishes obtaining bounds a posteriori from an assumed uniform hyperbolicity from constructing control a priori. The virtual levels are those between the original copy and the last relevant satellite scale before a primitive first renormalization; the intended objects are connected hulls in the Julia set of Cantor small Julia sets with restricted critical-orbit inclusion. The survey distinguishes virtual bounded-type satellite and virtual near-neutral regimes. The present test addresses neither geometrically.

Dudko–Lyubich–Selinger (DLS), *Pacman renormalization and self-similarity of the Mandelbrot set near Siegel parameters*, JAMS 33 (2020), 653–733, [DOI](https://doi.org/10.1090/jams/942), [arXiv:1703.01206v3](https://arxiv.org/html/1703.01206v3), Appendix C, **§C.3 The Molecule Conjecture** (unnumbered; not Conjecture C.2 and not §C.4 of the final version).

The precise passage begins at §C.3 with the definition of renormalization horseshoe and continues until the heading §C.4. Its core clause is:

> hyperbolic and piecewise analytic with one-dimensional unstable direction

The full statement, including the diagram and parabolic qualifications, is available verbatim in the primary PDF at the page range below; the local extraction command prints the source pages, rather than republishing the long passage here. In paraphrase, it posits a fast pacman operator on a molecule-associated space, a compact horseshoe of precompact two-sided orbits, a continuous surjective semiconjugacy to the fast parameter map away from the cusp, a compactification of the natural extension with additional parabolic direction data, a codimension-one stable lamination characterized by hybrid conjugacy near the mother hedgehog, and an unstable parameterization by a locally parabolically enriched parameter neighborhood. The fast operator locally factors into prime steps but the prime map degenerates near the cusp. In the source the prose gives the codomain of rho as Mol, whereas the displayed away-from-cusp diagram uses the boundary with cusp removed; consult the displayed conditions, not an inferred correction. DLS expressly includes its periodic-type hyperbolicity theorem in this broader conjecture.

Dudko–Lyubich (DL), *Local connectivity of the Mandelbrot set at some satellite parameters of bounded type*, GAFA 33 (2023), 912–1047, [DOI](https://doi.org/10.1007/s00039-023-00637-8), [arXiv:1808.10425v4](https://arxiv.org/html/1808.10425v4). This additional source is essential: the original DLS construction alone does not fix the exact return period.

### Version and page lock

The exact versioned PDF bytes are not accessible from the local sandbox (network unavailable). HTML versions were consulted directly, and the following page locators were independently checked in the PDFs served by arXiv (first-page version stamps verified) or SIAM. These are printed page numbers; the arXiv pages also equal one-based physical PDF page numbers. The workflow downloads exact versioned PDFs and records their SHA-256 and extracted page anchors here. No checksum is guessed; failure of the download or locator leaves an explicit review blocker.

- Dudko, ICM 2026 published [PDF, p. 133 (physical page 18)](https://epubs.siam.org/doi/pdf/10.1137/25M1807101#page=18), Problem 4.4 and §4.5. The published sentence has lowercase typography; the arXiv v1 wording above is retained. The arXiv v1 PDF page remains to be locked by CI (web PDF size limit).
- DLS v3 [p. 4](https://arxiv.org/pdf/1703.01206#page=4), equation (1.1) and Theorem 1.1; [p. 28](https://arxiv.org/pdf/1703.01206#page=28), Theorem 3.16; [p. 29](https://arxiv.org/pdf/1703.01206#page=29), Lemma 3.18 and Remark 3.19; [pp. 61–62](https://arxiv.org/pdf/1703.01206#page=61), Theorem 7.7 and proof; **[p. 89](https://arxiv.org/pdf/1703.01206#page=89), entire §C.3 Molecule Conjecture** (visually checked; §C.4 begins on p. 90).
- DL v4 [p. 31](https://arxiv.org/pdf/1808.10425#page=31), §§3.2.6–3.2.7, Lemma 3.1 and subsequent derivative identification; [pp. 73–74](https://arxiv.org/pdf/1808.10425#page=73), Proposition 5.41 and proof including the new hyperbolic operator. Note that Lemma 3.1 cites DLS Lemma 3.17, but the rotation map is Lemma 3.18 in the v3 PDF, as DL §3.2.6 correctly cites.

<!-- SOURCE LOCK BEGIN -->
PDF byte hashes are not yet verified. Manually checked primary PDF page locators are listed immediately above. A source-lock run is necessary to obtain the exact PDF fingerprints; the final static correction is committed with [skip ci] to honor the six-run limit. See sources.json for the incomplete provenance record.
<!-- SOURCE LOCK END -->

## Proof

Write t=(√5−1)/2, u=1−t. Then t²+t=1, 1/2<t<1, 0<u<1/2, and t≠u. In particular t is irrational, has periodic continued fraction [0;1,1,…], and satisfies the periodic-rotation hypothesis directly by the following calculation.

DLS (1.1), repeated as (3.7) in Lemma 3.18, defines T(x)=x/(1−x) for 0≤x≤1/2 and T(x)=(2x−1)/x for 1/2≤x≤1. Use 1/t=1+t. Then
```
T(t) = 2 − 1/t = 1 − t = u
T(u) = u/(1−u) = (1−t)/t = t
```
Thus t has **minimal prime period 2**, not 1. Both points lie strictly in their respective branch interiors.

DLS Theorem 1.1 gives the periodic Siegel pacman; Theorem 3.16 constructs its local analytic self-renormalization, and Theorem 7.7 gives hyperbolicity and the one-complex-dimensional unstable manifold, with multiplier as local coordinate. All refer to the standard source-defined pacman, not to the raw quadratic polynomial on an arbitrary domain. DLS Lemma 3.18 supplies the rotation map for an iterate, and Remark 3.19 defers optimality of that iterate. DL §3.2.6 imports this setting. **DL Proposition 5.41** proves that the local operator may be constructed with renormalization period equal to the minimal T-period; its proof constructs a new sector/pacman and invokes DLS analytic and hyperbolicity theorems. Choose that operator, R, not the unspecified original DLS normalization. This checks the extra hypothesis of exactly two prime steps and preserves the local hyperbolic setting.

DL §3.2.7, immediately following Lemma 3.1 and before (3.4), identifies the unstable eigenvalue with (T^m)'(t), because the multiplier parametrizes the unstable manifold. Apply this with m=2, justified above. For clarity, the local log of the multiplier e^(2πi x) is a holomorphic coordinate near the nonzero fixed multiplier; the derivative of a return at a fixed point is unchanged by a locally invertible change of coordinate. Thus we do not confuse the derivative of the rotation-number return with an unrelated finite-dimensional matrix eigenvalue.

On the upper branch T'(t)=1/t². On the lower branch T'(u)=1/(1−u)²=1/t². The chain rule yields
```
λ = (T²)'(t) = t^(−4) = (2+t)² = 5+3t = (7+3√5)/2 > 1.
λ² − 7λ + 1 = 0.
```
DLS hyperbolicity and the unstable dimension then show that this is the unique unstable eigenvalue on that one-dimensional complex space. This completes the stated local claim. No assumption of an already constructed fast molecule operator is used.

For an independent algebra check, the two Möbius branch matrices are U=[[2,−1],[1,0]], L=[[1,0],[−1,1]]. Their composition LU=[[2,−1],[−1,1]] has determinant 1 and derivative 1/(1−t)²=t^(−4). The verifier uses rational arithmetic in Q[t]/(t²+t−1), checks each denominator, the two exact orbit steps, strict rational brackets, matrix multiplication and both derivative identities. No discretization, floating point, arbitrary tolerance, or eigenvalue fit is involved.

## Hostile self-check

1. **Clock:** a proof using DLS alone is insufficient for the exact number; its allowed return length could be 2k, giving λ^k. DL Proposition 5.41 is indispensable. An operator taking two prime steps is an existential choice, not every local operator. The verifier checks that one- and four-step derivatives do not equal the chosen two-step derivative.
2. **Coordinate:** the unstable derivative identification is explicitly sourced from DL after Lemma 3.1. It is not inferred from the combinatorics alone. The arithmetic certificate establishes the scalar only, not compactness or a Banach-space spectral gap.
3. **Hypotheses:** both branches are strictly away from 1/2 and from the cusp, the orbit is exactly periodic and irrational; DLS/DL supply the pacman rather than an assumed arbitrary holomorphic map. This bypasses the near-parabolic degeneracy, and hence cannot be used as a certified near-neutral bound.
4. **Relation to P4.4:** periodic Siegel hyperbolicity is an explicitly included special case of the DLS conjecture, and is relevant to the conditional hyperbolicity strategy mentioned by Dudko. It does not prove uniformity, supply virtual Julia-set geometry or solve the survey problem.
5. **Review:** no human specialist has checked the source applications or proof. Page locator matches text, not theorem correctness; PDF SHA-256 is a reproducibility fingerprint, not independent authenticity verification.

## Reproduce

From repo root (Python 3.12, no dependencies for exact certificate):
```sh
cd research/frontier/dudko_p44_molecule_20261125
python -B verify.py --output results.json
python -m pip install pypdf==5.9.0
python -B source_lock.py --update-note
python -B source_lock.py --show-statements
```
For an offline replay, supply the exact PDF files named 2512.24171v1.pdf, 1703.01206v3.pdf, 1808.10425v4.pdf via `--pdf-dir /path/to/pdfs`. Check their SHA-256 against sources.json. The show-statements command prints the original statement pages including any adjacent text; view the actual PDF to recover typography and the diagram. No full PDF is committed.

Machine-readable: results.json records the exact arithmetic result and its mathematical scope; sources.json records input versions, hashes, page anchors and missing anchors. CI failure to download or find any anchor is a provenance failure, not a falsification of the algebraic identity. The workflow is limited to this branch, this directory/PR, or explicit dispatch. No existing archive files or ledger entries are changed; no new physical bridge is asserted.

CI history: initial setup-python 3.12.12 was unavailable for ubuntu-latest (26.04); switched to a pinned Python 3.12.12 container. The second PR run (45740722534, verify job 139644762806) executed the exact verifier successfully, printing the expected certificate; the subsequent git diff check failed inside the container. The final batch uses bytewise cmp and explicitly trusts only the checked-out workspace for branch writeback. This records the actual check result, not a green CI claim. The third push/PR pair exhausted the allocated six runs. Static inspection found an escaped-quote syntax defect in source_lock.py in that batch. The final correction removes that defect without triggering another run; the corrected downloader is untested in CI, and the exact PDF-byte hashes remain unverified.

AI disclosure: ChatGPT (GPT-6.2) performed source comparison, proof specialization, exact verifier and workflow construction. Human specialist verification: none yet. The primary-source theorems are attributed to their authors, not to AI.
