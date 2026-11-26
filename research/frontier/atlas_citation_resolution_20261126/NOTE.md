# Atlas citation resolution — imported

## Summary of changes

This is a source-statement and bibliographic overlay of merged #132 and #134, not a proof or new MLC case. **20 grid rows: 4 VERIFIED, 0 CORRECTED, 16 STILL UNVERIFIED.** Separately, the four unresolved source-ledger records: 1 VERIFIED (Ldensity), 0 CORRECTED, 3 STILL UNVERIFIED (DKL, DKLP, GS). One ancillary bibliographic CORRECTED item: Dudko’s survey is published in ICM 2026 proceedings, vol. 5, pp. 116–135, DOI 10.1137/25M1807101, not just arXiv/HTML. The published survey still references DKL as a manuscript. No coverage credit follows.

**Grid consequences:** 172 total, 110 covered, 62 open before and after. Of the 62: A=4 (statement-only preprints), B=42 (unchanged empty cells), C=0, UNVERIFIED=16. Changed cell IDs: none. No covered row loses coverage and no preprint is promoted to journal coverage. The 42 B cells and 110 covered cells are not independently re-proved. Source-level affected IDs are computed from the original atlas and #134 source references; affected means referenced, not changed. Ldensity and GS have no direct coverage edge; their relevance to the real residuals is contextual, as recorded in the cell entries.

## Limits / what is NOT established

- The 14 residual cells are not individual theorem citations. They are search gaps defined by negated sufficient predicates. The linked positive theorems and the survey’s questions do not classify their complements. No claim of exhaustive literature coverage, nonemptiness, or global openness.
- The two downgraded finite-prefix rows remain unresolved. The EE and KKL tail statements are accessible, but no independent whole-tail trivial-fiber antecedent for TUN is established by this audit. Pointwise MLC is not automatically equivalent to trivial fiber (Schleicher, arXiv:math/9902155, abstract); Lyubich §2.5 p. 198 discusses the global infinitely renormalizable rigidity problem. CS D, in contrast, gives shrinking whole parameter copies.
- EE §8 is an outline, not an independent proof audit. KKL C cites DKLP input; no independent verification of that input. DKL and DKLP primary texts could not be located; GS publisher metadata was accessible, not its primary theorem pages. No invented theorem numbers/pages or verbatim text for them.
- Publication searches used arXiv records, author/institution pages and exact-title/venue searches on 2026-11-26. “Preprint only located” means no journal record found, not proof of nonpublication. The 2022 CS author revision is distinguished from the 2015 arXiv version. Published survey ≠ published DKL proof.
- Source evidence gives brief exact quotations where accessible and mathematical paraphrases of hypotheses/conclusions; not full verbatim reproduction. Where no quote is supplied, consult the identified primary passage. Historical source hashes are copied from #134’s ledger as provenance, not represented as newly downloaded bytes; web-rendered source pages cannot be independently hashed in this environment. The four repository inputs below are freshly SHA-256 locked and verified by CI.
- No new MLC proof, new case, claim of closure of a gate, or change to #132/#134 files. No proof of any claim from a finite checker. AI disclosure: ChatGPT (GPT-6.2) performed this primary-statement comparison and generated the checker; no human verification asserted. Independent reviewer should inspect the cited passages.

## Inputs (exact repository bytes)

| Input | SHA-256 | Git blob |
|---|---|---|
| `research/frontier/mlc_coverage_atlas_20261126/atlas.json` | `0f9bc28a8f5392e50f7b9e30a5b2c5ba8fc5f73b9c6d9400545cac0c883df284` | `4bacf79fa2e5749e4364086221348cac63cc78fb` |
| `research/frontier/mlc_open_cells_20261126/open_cells.json` | `a5b0c6c101abf935bc556ed95ea07176b6fd43d57d0a0b3f6f8de292390ad92a` | `8bb55ddd1366921424c10a9b41881ff25e49d36c` |
| `research/frontier/mlc_open_cells_20261126/sources.json` | `a81bdc095c6e566bbfd63c272928e9faacb854366f3730a8ce421692193e558a` | `f000c2c94ffd2a232b6036265800f93b23fff958` |
| `research/frontier/mlc_open_cells_20261126/input_hashes.json` | `c767d5fe8bea49d1904c412537fdcc5a41f6978fb498976f0096d7bdae067f71` | `14fc641c4027d579e98eeb65a285832254a2b7fd` |

Baseline main commit `f15d77d4e43373a32bab90624c4c60f023f7a1b2`. Reviews read: [#132](https://github.com/dovvnloading/loops-research-archive/pull/132), [#134](https://github.com/dovvnloading/loops-research-archive/pull/134). Cell identifiers, attributed hypotheses, precise evidence crosswalk, publication metadata, blockers and before/after states: [resolution.json](resolution.json).

### Source locator register

| Source | Primary locator or explicit blocker | Historical SHA-256 (not a new retrieval) |
|---|---|---|
| Ldensity | [Dynamics of quadratic polynomials, I–II](https://commack.math.stonybrook.edu/~mlyubich/papers/acta.pdf) — Density Theorem, printed p. 188 (PDF page 4) | `a286b6d3c874c803c1d56a669b5850e79c903190534aeab4840664b8e631bf16` |
| L | [Dynamics of quadratic polynomials, I–II](https://commack.math.stonybrook.edu/~mlyubich/papers/acta.pdf) — Rigidity Theorem p. 187; §2.5 pp. 198–199 (PDF pp. 14–15); Theorem IV′ (prior locator only) | `a286b6d3c874c803c1d56a669b5850e79c903190534aeab4840664b8e631bf16` |
| Lreal | [Dynamics of quadratic polynomials, I–II](https://commack.math.stonybrook.edu/~mlyubich/papers/acta.pdf) — Theorem VIII, printed p. 281 (PDF p. 97) | `a286b6d3c874c803c1d56a669b5850e79c903190534aeab4840664b8e631bf16` |
| LY | [Dynamics of quadratic polynomials: complex bounds for real maps](https://www.numdam.org/item/AIF_1997__47_4_1219_0.pdf) — Complex Bounds Theorem and Local Connectivity Theorem, printed p. 1220 | `52c67b9960e4dd632db2aa56a0763312eb0bf6a3b43b33ce98698962e2fdc429` |
| C | [Combinatorial rigidity for some infinitely renormalizable unicritical polynomials](https://www.ma.imperial.ac.uk/~dcheragh/Research/2010-1.pdf) — Rigidity Theorem, p. 2 | `c62ea484883ccb860286aab19a21d31bfdb22d102a792594d5b8986f6769c72d` |
| DL26 | [MLC at Feigenbaum points](https://arxiv.org/pdf/2309.02107v3) — Theorems A and B p. 3; relative periods p. 11 | `e88462e43b3c172cf309d5b3d38caa21ee8f43876bac1e07cce84b309dfb8c6b` |
| KLdec | [A priori bounds for some infinitely renormalizable quadratics: II. Decorations](https://www.numdam.org/item/10.24033/asens.2063.pdf) — Theorem and Corollary 1.1, printed p. 58; definition pp. 57–58 | `a0c77541efe273aa180f31cbb67093b9931d7b73389e6bb8947452998b13bba5` |
| KLmol | [A priori bounds for some infinitely renormalizable quadratics: III. Molecules](https://www.math.stonybrook.edu/preprints/ims07-04.pdf) — Main Theorem p. 1; Corollary 1.1 p. 2; molecule condition pp. 6–7 (preprint pagination) | `0225b5e1416d62eadb3f9b1ae9d5d3c4c4287b0d572167c744e9bae900220e53` |
| Lev1 | [Rigidity and non-local connectivity of Julia sets of some quadratic polynomials](https://arxiv.org/pdf/0710.4406) — Theorem 1, p. 1 (arXiv pagination) | `8e5a59b111c0d841d5deb3ab7adb12b556896a2916c1e4cc8418fe41789335cd` |
| Lev2 | [Rigidity and non-local connectivity of Julia sets of some quadratic polynomials](https://arxiv.org/pdf/0710.4406) — Theorem 2, pp. 3–4 | `8e5a59b111c0d841d5deb3ab7adb12b556896a2916c1e4cc8418fe41789335cd` |
| Levadd | [Addendum to: Rigidity and non-local connectivity of Julia sets of some quadratic polynomials](https://arxiv.org/pdf/0710.4406) — Addendum Theorem 1(1), addendum p. 1 (PDF p. 42) | `8e5a59b111c0d841d5deb3ab7adb12b556896a2916c1e4cc8418fe41789335cd` |
| EE | [A priori bounds for some infinitely renormalizable quadratics: IV. Elephant eyes](https://arxiv.org/pdf/2601.21905v1) — §4.0.1 E1–E3 p. 9; §8 pp. 18–19, unnumbered MLC assertion | `5eb36430a51a3fb6a1c04db15713aebc86068118450893ba2042021e4a8db725` |
| KKL | [MLC for parabolically bounded primitive renormalization](https://arxiv.org/pdf/2606.27272v1) — Theorem C p. 4; definition of rigidity and Theorems A/B p. 3; §3.1 p. 19; §7 p. 56; bibliography p. 71 | `4c08805384b473dc0e55d76491c52c9fbe7c027e6da301f2c365a170ed7d9140` |
| CS2015 | [Satellite renormalization of quadratic polynomials](https://arxiv.org/pdf/1509.07843) — Theorem D p. 6; QG_N equation (44) p. 62 | not available |
| CS | [Satellite renormalization of quadratic polynomials](https://www.ma.imperial.ac.uk/~dcheragh/Research/2015-2.pdf) — Theorem D pp. 5–6; QG_N equation (6.8) p. 62 | `b1d6b0952247efc3cd7a6e0602dbb8246b43b9edf7b3c5d0da942cc822246c25` |
| TUN | [On fibers and renormalization of Julia sets and Multibrot sets](https://www.math.stonybrook.edu/preprints/ims98-13b.pdf) — Theorem 3.1 and Corollary 3.2, p. 6 | `1095be3a23d83cbc8acafe1c8ff7e24d787ffe791cdf8ea90b4f2b9686af8195` |
| TUNscope | [On fibers and local connectivity of Mandelbrot and Multibrot sets](https://arxiv.org/abs/math/9902155) — Abstract; §7 Proposition 7.4 (HTML; PDF page not checked) | not available |
| survey | [On the MLC Conjecture and the Renormalization Theory in Complex Dynamics](https://epubs.siam.org/doi/pdf/10.1137/25M1807101) — §4.3 Theorem 4.1 and following paragraph p. 131; §4.4 Problem 4.3 p. 132; §4.5 Problem 4.4 and [14] p. 133 | `8ede4bf8ccfe25a4f325cad41cb729f08f8b1d0d7103ed6dbc89015b1ff8d904` |
| DKL | Local Connectivity of the Mandelbrot Set along the Real Line — Dudko, published ICM survey, p. 131 after Theorem 4.1 and bibliography [14] p. 133 | not available |
| DKLP | Elephant puzzles — KKL Theorem B discussion p. 3 and bibliography p. 71 | not available |
| GS | [Generic hyperbolicity in the logistic family](https://annals.math.princeton.edu/articles/12963) — Publisher bibliographic record only, no theorem text | not available |

## Reproduce

From repository root, Python 3.12, standard library only (no pip dependencies):

```sh
python -B research/frontier/atlas_citation_resolution_20261126/verify.py
```

The checker rejects changed input hashes, duplicate keys, missing/extra target cells, incompatible source/impact mappings and unsupported promotions; independently recomputes before/after status counts. It does not validate the mathematical truth of the cited theorems. Workflow uses read-only permissions and never writes to the repository.

**Status label: imported.**
