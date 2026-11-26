# Coverage atlas: the remaining slowly growing satellite case

**Claim (imported atlas; open residual).** The published bounded-relative-period theorem of Dudko–Lyubich covers all primitive, satellite and mixed bounded-type Feigenbaum parameters. The explicit infinite satellite tuning address
`S(1/3) S(1/4) S(1/5) ...` is outside the sufficient hypotheses of the independently checked MLC theorems below. It is the smallest address in the specified affine numerator-one family and ordering, not an absolute smallest open class. This is an inventory of source-stated implications, not a new MLC case.

## Limits and terminology

* We do not establish that the limiting parameter is unique, MLC fails there, every member of an open row is unresolved, every syntactic row is nonempty, or that no unknown/published theorem covers the address. A global minimum is not defined without an ordering. "Open" means no independently audited implication covers the entire indicated cell. The preprint-only K, CS, EE and KKL statements and the real/vein manuscript are separately recorded, not counted as published MLC coverage. A verified published base theorem plus the verified finite-tuning transfer is conditional on its stated fiber hypothesis. The atlas is not a proof audit of the published arguments.
* Use successive **maximal** quadratic-like tuning copies, with absolute periods P_i and relative periods r_i=P_i/P_(i-1). P/S describes the relative type after straightening; Kahn's absolute primitive cofinal condition is deliberately separate. Mixed is split into eventually P, eventually S, and infinitely many of both. A finite prefix can be restored by Schleicher's Corollary 3.2 (IMS 1998/13b, p. 6): triviality of fibers is invariant under tuning. Only transfer a theorem when the tail's singleton fiber is established; MLC alone should not be casually substituted for fiber triviality. Thus eventual-S words can use the satellite hypotheses on a tail, eventual-P words the primitive conditions, and real-essential tails need not have a real original parameter.
* Relative period bounded type is not the same as continued-fraction bounded type. For satellite t_i=a_i/q_i, reduced, r_i=q_i. Finite rational continued fractions may have bounded digits but unbounded lengths and denominators. High type means every source-defined signed digit is large, not necessarily quadratic growth or bounded denominator. For unbounded-period rows with satellite levels, distinguish bounded digits, unbounded digits with minimum per satellite level tending to infinity, and unbounded digits without that property. Finite many satellite levels have bounded digits. Real all-satellite words have only 1/2 and cannot be unbounded.
* The decision grid in atlas.json refines these axes by the first true applicable sufficient predicate; predicates are the full source hypotheses, not numerical approximations. Some tests (SL with class-wide bounds, puzzle/decoration separation) need geometric inputs. Preprint-only and unverified reported MLC statements are tagged but not counted as published coverage; K's unbounded-period cells are syntactically empty because cofinal bounded ratios imply bounded maximal relative periods. The residual cells explicitly negate every earlier applicable sufficient test; they are not an enumeration of all mathematical open problems. This is a finite audit grid, not a decidability algorithm for infinite addresses.

## Source ledger and coverage

The theorem/page locator, exact relevant hypotheses (paraphrased), source link, coverage kind and candidate-by-candidate exclusion are in [atlas.json](atlas.json), keyed by theorem ID. Page numbers refer to the linked source, not to a guessed journal repagination. Sources were read at theorem-statement level, not re-proved. PDF fingerprinting is a separate reproducibility check, not evidence of mathematical correctness.

* **Y**: Hubbard's exposition of Yoccoz, Theorem III (p. 469, not 468 or 496), finitely renormalizable, outside the target.
* **L, Lreal, Ldensity**: Lyubich Acta 1997 Rigidity Theorem (p. 187), §2.5 (198–199), Thm IV' (239), VIII (281) and Density Theorem (188). SL alone does not yield bounds; rigidity of two bounded representatives alone is not a proof that an entire class is a singleton. The real VIII hypothesis is uniformly large **essential** periods, not simply unbounded periods. Real density does not resolve nonreal points of a complex combinatorial fiber.
* **K, KLdec, KLmol**: Kahn bounded primitive Main Theorem (§1.2–1.3, p. 4); Kahn–Lyubich Decorations Main Theorem/Cor. 1.1 (58), molecule Main Theorem/Cor. 1.1 (IMS preprint pp. 1–2, §2.3 pp. 6–7 and Lemma 2.5). Kahn explicitly lists Part I as not formally published; its bounded cofinal period ratios force all maximal relative periods bounded, already covered by DL26. The Decorations condition requires every relevant relative copy to lie in a fixed finite set of decorations (§2.2 p. 64). The Molecules condition records cofinal absolute primitive renormalizations and permits intervening satellite levels, so it is tested also for recurrent mixed words. Uniform anti-molecule condition is not a synonym for arbitrary primitive renormalizations.
* **DL23, DL26**: the former GAFA paper Thm 1.1 concerns special stationary molecule-return bounded satellite parameters; the latter IHÉS 143 (2026), 97–141, [DOI 10.5802/pmihes.2](https://doi.org/10.5802/pmihes.2), published 2 June 2026, Thms A/B (arXiv:2309.02107v3 p. 3, definition of bounded relative periods pp. 10–11) gives every bounded relative-period sequence, including period doubling and nonreal mixed types.
* **CS, C**: Cheraghi–Shishikura Thm D (p. 6), (6.8) (62), QG_N. Signed CF digits must square-grow both within and between rotations. Cheraghi's 2010 rigidity theorem requires SL and a priori bounds, not mere high-type rotations. CS is a statement-verified arXiv preprint (1509.07843v1); journal publication UNVERIFIED, so its QG cells are open/reported in this published-coverage grid.
* **Lev1, Lev2, Levadd**: Levin, arXiv:0710.4406v4, Thms 1–2 and Addendum Thm 1(1). Important additional satellite/fast-growth criteria; note the distinction between absolute and relative periods. Theorem 2 illustrates that MLC and JLC are different.
* **EE, KKL**: 2026 arXiv v1 papers extend the primitive near-cusp frontier in precisely specified families. EE §4.0.1 gives E1–E3, with the MLC statement at §8 p. 18; the latter argument is **not** audited here. EE E2 excludes a pure satellite shared-base-point configuration, not merely by the numerical period formula. KKL Thm C p. 4 is a stated MLC application of A/B and puzzle input cited as DKLP in preparation (p. 71), primary text UNVERIFIED. Keep these stated applications separate from fully checked imports; neither applies to pure satellites. No investigation of the companion threads' proof obligations.
* **TUN**: Schleicher, On Fibers and Renormalization of Julia Sets and Multibrot Sets, IMS 1998/13b (arXiv:math/9902156v1), Corollary 3.2 p. 6, verified in the IMS preprint scan, not counted as a separate published MLC base case. Fiber triviality is preserved by every finite tuning. Theorem 3.1 on the attached decorations provides the setup. No new initial case is supplied; finite-prefix tuning of a known trivial fiber is an imported transfer.
* **LY, LvS, GS, DKL**: Lyubich–Yampolsky published p. 1220 gives real bounds and JLC; Levin–van Strien main theorem gives JLC. Graczyk–Świątek's journal theorem text is UNVERIFIED, so no theorem number is guessed. Dudko survey [14] cites a 2022 manuscript reporting real-line/vein MLC; primary manuscript UNVERIFIED. Thus the real residual rows are documentary gaps, not claims that MLC along the real line remains an open mathematical problem.

<!-- audit:start -->
**Audit grid:** 172 cells: 110 covered; 62 open.
**Audit label:** imported / open.
**Candidate cell:** S/unbounded/nonreal/unbounded_digits_min_tends_infty/residual.
**Candidate formula:** t_i=1/(i+2), i>=1.
**Candidate order:** Within nonreal-at-first-step, positive numerator-one affine strictly increasing denominator words q_i=a+b(i-1), integers a>=3,b>=1, order lexicographically by (b,a); (1,3) is minimum. Not absolute minimum over all words or all open subclasses.

| ID | Statement status | Coverage kind | Locator | Independent verdict |
|---|---|---|---|---|
| C | statement_verified | conditional_mlc | Rigidity Theorem, pp. 1–2 (author PDF) | verified; SL and a priori bounds required |
| CS | statement_verified | reported_mlc | Theorem D p. 6; signed continued fractions pp. 5–6; (6.8) and example p. 62 | downgraded; statement verified, journal publication UNVERIFIED |
| DKL | UNVERIFIED | reported_mlc | UNVERIFIED primary manuscript; survey §4.3 after Theorem 4.1 and ref. [14] | UNVERIFIED primary manuscript; no MLC credit |
| DL23 | statement_verified | mlc | Theorem 1.1, pp. 3–4 (arXiv) | verified; stationary construction only |
| DL26 | statement_verified | mlc | Theorems A and B p. 3; definitions §2.2.5 pp. 10–11 (arXiv v3) | verified; published all bounded relative periods |
| EE | statement_verified | reported_mlc | §4.0.1 E1–E3 p. 9; MLC statement §8 p. 18 (unnumbered; proof not audited) | downgraded to reported preprint application; proof dependencies not audited |
| GS | UNVERIFIED | not_mlc | journal theorem/page UNVERIFIED | UNVERIFIED primary theorem; no MLC credit |
| K | statement_verified | reported_mlc | Main Theorem §1.2 and application §1.3, p. 4 | downgraded; statement verified, journal publication UNVERIFIED |
| KKL | statement_verified | reported_mlc | Theorems A,B p. 3; C p. 4; reference DKLP p. 71 | downgraded to reported preprint application; DKLP UNVERIFIED |
| KLdec | statement_verified | mlc | Main Theorem and Cor. 1.1, p. 58; Thm 1.2 and Remark 1.2 p. 59; §§2.1–2.2, pp. 61–64 | verified; locator and full condition corrected |
| KLmol | statement_verified | mlc | Main Theorem p. 1; Cor. 1.1 p. 2; §2.3 and Lemma 2.5 pp. 6–7 (IMS preprint) | verified; mixed scope and section corrected |
| L | statement_verified | conditional_mlc | Rigidity Theorem and Cor. 1.1 p. 187; §2.5 pp. 198–199; Thm IV' p. 239 | verified; conditional, full class hypotheses required |
| LY | statement_verified | not_mlc | Theorem 1.1, Complex Bounds Theorem and Local Connectivity Theorem p. 1220 | verified; bounds and JLC only; finite-stage hypothesis corrected |
| Ldensity | statement_verified | not_mlc | Density Theorem, p. 188 | verified; real density only |
| Lev1 | statement_verified | mlc | Theorem 1 p. 1 (arXiv) | verified |
| Lev2 | statement_verified | mlc | Theorem 2 pp. 3–4 (arXiv) | verified |
| Levadd | statement_verified | mlc | Addendum Theorem 1(1), separate p. 1 (PDF page 42) | verified; publication details corrected |
| Lreal | statement_verified | mlc | Theorem VIII, §12.1, p. 281 | verified |
| LvS | statement_verified | not_mlc | Main theorem p. 1 (preprint) | verified; JLC only |
| TUN | statement_verified | conditional_mlc | Theorem 3.1 and Corollary 3.2, p. 6 (IMS PDF); Introduction p. 2 | verified preprint transfer only; no independent coverage credit |
| Y | statement_verified | mlc | Theorem III, p. 469 (printed; PDF page 3) | verified; locator corrected |
| survey | statement_verified_html | survey | HTML v1 https://arxiv.org/html/2512.24171v1; §4.2–4.5, Thm 4.1/4.2, Problems 4.3/4.4; PDF page UNVERIFIED | verified HTML v1; PDF pagination UNVERIFIED |
<!-- audit:end -->

## Explicit residual and minimality relative to a declared order

Let i start at 1, q_i=i+2, t_i=1/q_i, P_0=1 and P_i=product(q_j,j=1..i)=(i+2)!/2. At each step tune by the main-cardioid satellite copy with rotation t_i. The nested nonempty compact copies have a nonempty intersection by compactness. The first 1/3 limb is nonreal; subsequent tuning stays there. Standard satellite tuning supplies the infinite address, not a singleton assertion.

The word has only satellite levels, no cofinal absolute primitive subsequence, and unbounded relative periods. All signed CF digits eventually exceed any fixed threshold, but each is a single digit q_i, and q_(i+1)=q_i+1<q_i^2. Thus CS's growth fails even after discarding any finite prefix. It also fails each Levin growth test: log |a_i|=0, log q_i/P_(i-1) tends to zero, |t_(i+1)|^(1/q_i) tends to 1, P_(i-1)/q_i tends to infinity and q_i/P_(i-1)^2 tends to zero. These follow directly from factorial growth, and persist for every tail. Every straightened tail begins with rotation 1/q for q>=3, ruling out a real tail; unbounded limb denominators rule out the fixed finite secondary-limb hypothesis. DL23's bounded stationary construction and DL26's uniform period bound both fail. All predicates requiring cofinal primitive renormalizations fail, including the mixed-capable molecule condition; the reported 2026 applications fail E2 (EE) or prime primitive type (KKL). The finite-tuning transfer TUN cannot help without a covered tail: every tail of this address still fails the same tests. For the unavailable real/vein manuscript we cannot certify a negative beyond its stated real/vein scope; no unspecified vein extension is assumed. See the per-theorem checks in atlas.json, including non-MLC results.

Order only the affine positive numerator-one strictly increasing words q_i=a+b(i-1) with integers a>=3 (nonreal at first step) and b>=1 by (b,a). The pair (1,3) is the minimum, hence the simplest such explicit slow-growth residual in that ordering. The choice of affine family and ordering is a research convention, not a theorem that every conceivable complexity measure has this minimum. The grid's class is S/unbounded/nonreal/unbounded_digits_min_tends_infty/residual.

## Comparison to Dudko's survey

Dudko arXiv:2512.24171v1 (30 Dec 2025), [HTML §4](https://arxiv.org/html/2512.24171v1#S4), §4.2–4.5: Theorem 4.1 reports all bounded ql-type MLC. §4.3 immediately reports real/vein coverage citing manuscript [14]. Problem 4.3 in §4.4 asks for remaining unbounded satellite pseudo-Siegel bounds; our slow pure-satellite word matches that direction. Problem 4.4 in §4.5 asks for virtual near-molecule interpolation at primitive levels approaching the molecule, not this pure-satellite word. The 2026 primitive preprints postdate that survey. KKL's remark immediately after Theorem C explicitly places the combination with bounded satellite types outside that paper's scope. Theorem 4.2 on neutral quadratic pseudo-Siegel bounds is not by itself the missing parameter-plane satellite theorem. Agreement on bounded type and on the direction of Problem 4.3; no discrepancy on the explicit residual. The survey reports additional real/vein coverage that cannot be checked from the unavailable manuscript; it is not counted here. Neither the survey nor this limited search proves exhaustive noncoverage. PDF pagination of the survey was not accessible in the statement-reading pass; sections and problem numbers are verified from arXiv HTML v1.

## Inputs and SHA-256

A versioned PDF is preferred where accessible; older published/author PDFs use the cited stable URL. The exact-version web endpoints for K, Levin and Levin–van Strien could not be rendered directly; alternate arXiv PDFs with the matching visible versions were read. The survey was read in versioned HTML; PDF pagination is UNVERIFIED. This is statement verification, not independent comparison of PDF bytes to CI hashes. The recorded hash covers the bytes retrieved by CI, not a claimed match to a PDF the web reader rendered earlier. UNVERIFIED means no byte lock / no available primary statement as distinguished in the atlas. No third-party full PDFs committed.

<!-- hashes:start -->

| PDF input | SHA-256 / retrieval status |
|---|---|
| https://annals.math.princeton.edu/articles/12963 | UNVERIFIED (no primary PDF locator) |
| https://arxiv.org/pdf/0710.4406v4 | 8e5a59b111c0d841d5deb3ab7adb12b556896a2916c1e4cc8418fe41789335cd |
| https://arxiv.org/pdf/1808.10425v4 | 4a8f0f8c3ffd96c6a5a364340f2a7394fc75d0f355a7576040286c47365baec8 |
| https://arxiv.org/pdf/2309.02107v3 | e88462e43b3c172cf309d5b3d38caa21ee8f43876bac1e07cce84b309dfb8c6b |
| https://arxiv.org/pdf/2512.24171v1 | 8ede4bf8ccfe25a4f325cad41cb729f08f8b1d0d7103ed6dbc89015b1ff8d904 |
| https://arxiv.org/pdf/2601.21905v1 | 5eb36430a51a3fb6a1c04db15713aebc86068118450893ba2042021e4a8db725 |
| https://arxiv.org/pdf/2606.27272v1 | 4c08805384b473dc0e55d76491c52c9fbe7c027e6da301f2c365a170ed7d9140 |
| https://arxiv.org/pdf/math/0609045v3 | 46e7ff4d5cc8ea190e439f45b2e4ed7308c1cf588a666daa5150eeb0b435c9c0 |
| https://arxiv.org/pdf/math/9504227v1 | b623bd34992cc3e821cef350c824df4b38478e6ac05436283902f5a5a17ecce7 |
| https://commack.math.stonybrook.edu/~mlyubich/papers/acta.pdf | a286b6d3c874c803c1d56a669b5850e79c903190534aeab4840664b8e631bf16 |
| https://pi.math.cornell.edu/~hubbard/hubbard.pdf | 53c3ff3e06fc512cc6af809fc55cb374941d6eaada64bf8c98a291dc8179c2e9 |
| https://www.ma.imperial.ac.uk/~dcheragh/Research/2010-1.pdf | c62ea484883ccb860286aab19a21d31bfdb22d102a792594d5b8986f6769c72d |
| https://www.ma.imperial.ac.uk/~dcheragh/Research/2015-2.pdf | b1d6b0952247efc3cd7a6e0602dbb8246b43b9edf7b3c5d0da942cc822246c25 |
| https://www.math.stonybrook.edu/preprints/ims07-04.pdf | 0225b5e1416d62eadb3f9b1ae9d5d3c4c4287b0d572167c744e9bae900220e53 |
| https://www.math.stonybrook.edu/preprints/ims98-13b.pdf | 1095be3a23d83cbc8acafe1c8ff7e24d787ffe791cdf8ea90b4f2b9686af8195 |
| https://www.numdam.org/item/10.24033/asens.2063.pdf | a0c77541efe273aa180f31cbb67093b9931d7b73389e6bb8947452998b13bba5 |
| https://www.numdam.org/item/AIF_1997__47_4_1219_0.pdf | 52c67b9960e4dd632db2aa56a0763312eb0bf6a3b43b33ce98698962e2fdc429 |

<!-- hashes:end -->

## Reproduce

From this directory, run:

```sh
python3 -B verify.py
python3 -B verify.py --lock        # network; regenerates source manifest and this hash block
python3 -B verify.py --check-lock  # offline structural consistency of manifest
```

Python 3.12, standard library only. The checker enumerates a fixed grid independently, checks every row's unique key, precedence, status and references, and checks that the explicit example accounts for every catalog entry. Its finite integer checks are regressions, not a proof of infinite combinatorics, geometric realizability, paper validity or literature completeness. A source that fails download remains explicitly UNVERIFIED; retrieval failure is not negative mathematical evidence.

**Status:** imported (source inventory and scoped implications), open (residual relative to audit). No ledger gate is promoted. Reviewed against main 85cb9ff1aacbf61de06c7479e1bcd4621f6a3940. The independent AI review checked primary theorem statements and corrected source locators, coverage scope and published/preprint distinctions; no independent human specialist proof audit has taken place.
