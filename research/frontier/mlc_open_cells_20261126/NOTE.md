# Open cells follow-up — imported + open

**Claim.** In the 62 noncovered *syntactic* rows of #132, 42 are empty by explicit combinatorial contradictions; 6 match a preprint's stated sufficient hypotheses (A, statement-level, relative to the audited catalogue); 14 remain unclassified, including the reserved cell. No C (“genuinely open against all published and preprint results”) is certified.

**Limits.** This is a partial classification, not the requested complete mathematical trichotomy. In particular, the unavailable primary 2022 DKL real/vein manuscript prevents both verification of A and certification of C for the real/vein gap. A cell may contain points covered by a different theorem even though its entire conjunction has no known covering theorem. First-true predicate precedence can conceal later overlaps. A is not a claim of proof verification or that no published theorem covers a subset. The specific reserved cell is deferred, not classified. No new MLC case. No minimality claim for a partition of actual unknown parameters.

## Inputs and precise locators

Base input: merged #132 (squash commit b25d26d9151fbaf5c8acf4bf00c6b56e42cd3a4c), `research/frontier/mlc_coverage_atlas_20261126/atlas.json` Git blob 4bacf79fa2e5749e4364086221348cac63cc78fb; NOTE blob 8cca33120eea79b4495a0234858b0af0aac80164; [review](https://github.com/dovvnloading/loops-research-archive/pull/132#issuecomment-7181975461). The atlas is the universe; no IDs are redefined.

The [source table](sources.json) records version, primary URL, theorem/page, short literal excerpts (math notation transcribed), and prior atlas SHA-256 where available. VERIFIED means the relevant statement was opened, not the proof or publication chain certified. The arXiv v1 Cheraghi–Shishikura PDF and the later author PDF are distinct: QG_N is (44) in v1 and (6.8) in the 2022 revision, both p. 62; D p. 6. EE §4.0.1 p. 9, §8 p. 18; KKL A/B p. 3, C p. 4, DKLP p. 71. TUN Cor. 3.2 p. 6. DKL [14] is an unavailable manuscript; GS primary text and Ldensity independent quotation not verified. Survey §4 read in HTML v1; PDF page UNVERIFIED.

CI committed the local input SHA-256 values: atlas.json `0f9bc28a8f5392e50f7b9e30a5b2c5ba8fc5f73b9c6d9400545cac0c883df284`; NOTE.md `1fc12e81238178eecea08757d7f8669ad1715d078e27f47e1fbda1395f80fde0`. The exact v1 CS PDF SHA-256 is `71c03718203b91ae81f5b7e138620a086cdf038b345cf689a24ed2932d72384f`; the survey HTML v1 SHA-256 is `95bce68c6fa2fce3b258c970f894765f7a60436006d496ee5d11fc40e9ff6f04`. All 16 prior primary PDF locks with URLs matched newly downloaded bytes. DKL and DKLP primary text remain UNVERIFIED, with no assigned digest. The previous atlas byte locks below are inherited provenance. `input_hashes.json` is the CI-generated SHA-256 manifest for local inputs and newly downloaded source bytes (UNVERIFIED when unreachable; hashes do not certify hypotheses). Network unavailable in the worker sandbox. CI fetches without storing third-party PDFs in git.

- Y: SHA-256 `53c3ff3e06fc512cc6af809fc55cb374941d6eaada64bf8c98a291dc8179c2e9` — Theorem III, p. 469 (printed; PDF page 3)
- L: SHA-256 `a286b6d3c874c803c1d56a669b5850e79c903190534aeab4840664b8e631bf16` — Rigidity Theorem and Cor. 1.1 p. 187; §2.5 pp. 198–199; Thm IV' p. 239
- Lreal: SHA-256 `a286b6d3c874c803c1d56a669b5850e79c903190534aeab4840664b8e631bf16` — Theorem VIII, §12.1, p. 281
- Ldensity: SHA-256 `a286b6d3c874c803c1d56a669b5850e79c903190534aeab4840664b8e631bf16` — Density Theorem, p. 188; theorem statement not independently re-quoted in this follow-up
- K: SHA-256 `46e7ff4d5cc8ea190e439f45b2e4ed7308c1cf588a666daa5150eeb0b435c9c0` — Main Theorem §1.2 and application §1.3, p. 4
- KLdec: SHA-256 `a0c77541efe273aa180f31cbb67093b9931d7b73389e6bb8947452998b13bba5` — Main Theorem and Cor. 1.1, p. 58; Thm 1.2 and Remark 1.2 p. 59; §§2.1–2.2, pp. 61–64
- KLmol: SHA-256 `0225b5e1416d62eadb3f9b1ae9d5d3c4c4287b0d572167c744e9bae900220e53` — Main Theorem p. 1; Cor. 1.1 p. 2; §2.3 and Lemma 2.5 pp. 6–7 (IMS preprint)
- DL23: SHA-256 `4a8f0f8c3ffd96c6a5a364340f2a7394fc75d0f355a7576040286c47365baec8` — Theorem 1.1, pp. 3–4 (arXiv)
- DL26: SHA-256 `e88462e43b3c172cf309d5b3d38caa21ee8f43876bac1e07cce84b309dfb8c6b` — Theorems A and B p. 3; definitions §2.2.5 pp. 10–11 (arXiv v3)
- CS: SHA-256 `b1d6b0952247efc3cd7a6e0602dbb8246b43b9edf7b3c5d0da942cc822246c25` — Theorem D p. 6; QG_N equation (6.8) p. 62; signed CF pp. 5–6
- C: SHA-256 `c62ea484883ccb860286aab19a21d31bfdb22d102a792594d5b8986f6769c72d` — Rigidity Theorem, pp. 1–2 (author PDF)
- Lev1: SHA-256 `8e5a59b111c0d841d5deb3ab7adb12b556896a2916c1e4cc8418fe41789335cd` — Theorem 1 p. 1 (arXiv)
- Lev2: SHA-256 `8e5a59b111c0d841d5deb3ab7adb12b556896a2916c1e4cc8418fe41789335cd` — Theorem 2 pp. 3–4 (arXiv)
- Levadd: SHA-256 `8e5a59b111c0d841d5deb3ab7adb12b556896a2916c1e4cc8418fe41789335cd` — Addendum Theorem 1(1), separate p. 1 (PDF page 42)
- EE: SHA-256 `5eb36430a51a3fb6a1c04db15713aebc86068118450893ba2042021e4a8db725` — §4.0.1 E1–E3 p. 9; MLC statement §8 p. 18 (unnumbered; proof not audited)
- KKL: SHA-256 `4c08805384b473dc0e55d76491c52c9fbe7c027e6da301f2c365a170ed7d9140` — Theorems A,B p. 3; C p. 4; reference DKLP p. 71
- LY: SHA-256 `52c67b9960e4dd632db2aa56a0763312eb0bf6a3b43b33ce98698962e2fdc429` — Theorem 1.1, Complex Bounds Theorem and Local Connectivity Theorem p. 1220
- LvS: SHA-256 `b623bd34992cc3e821cef350c824df4b38478e6ac05436283902f5a5a17ecce7` — Main theorem p. 1 (preprint)
- survey: SHA-256 `8ede4bf8ccfe25a4f325cad41cb729f08f8b1d0d7103ed6dbc89015b1ff8d904` — HTML v1 §4.3 after Thm 4.1; §4.4 Problem 4.3; §4.5 Problem 4.4; ref. [14]; PDF pagination UNVERIFIED
- TUN: SHA-256 `1095be3a23d83cbc8acafe1c8ff7e24d787ffe791cdf8ea90b4f2b9686af8195` — Theorem 3.1 and Corollary 3.2, p. 6 (IMS PDF); Introduction p. 2

## Empty-cell proofs (B)

Let P_j be the absolute periods of successive maximal renormalizations and r_j=P_j/P_(j-1) their integer relative periods. A finite prefix affects neither boundedness nor eventual digit-growth properties. Use the atlas interpretation of locus (real original parameter) and type.

- **B1 (k):** if j_m is an infinite cofinal subsequence with P_(j_(m+1))/P_(j_m) <= M, each intervening r_j divides that quotient. All r_j beyond j_1 are at most M; finitely many earlier ratios have finite maximum. Contradiction to unbounded.
- **B2 (eventually P, unbounded satellite digits):** finitely many rational satellite rotations have finitely many CF digits; their union has a finite maximum. Both unbounded-digit alternatives are impossible.
- **B3/B4 (real):** conjugation fixes the real parameter and its canonical maximal renormalization; the straightening is real by uniqueness and conjugation equivariance. Induct on levels. At a real satellite step the dividing rotation is taken to its negative by conjugation; it is nonzero mod 1, so equals 1/2. Equivalently the only conjugation-invariant nontrivial primary limb is the 1/2 limb. Relative satellite period is 2 and digit is 2. Eventual S with finite primitive prefix is bounded (B3); recurrent real cannot have unbounded satellite digits (B4).
- **B5 (QG_N):** use source signed CF, nearest integer digits at least 2. In the reduced t=a/q, |1/t|=q/|a| <= q and nearest integer b_1 <= q+1/2; hence b_1 <= q. The within-level inequalities make b_1 minimal, and the cross-level inequality makes the next first digit at least q² >= b_1². Thus min digit tends to infinity. A finite prefix cannot fix either contrary alternative. 
- **B6 (real EE):** the dividing fixed point for a real infinitely renormalizable straightened quadratic is real; conjugation reverses the nontrivial dividing rotation so it is 1/2. E1 forces q=2; E3 forces p=q+b uniformly bounded. 
- **B7 (real KKL):** in the source definition of parabolically bounded family, a finite collection of fixed templates generates 1/q-limb parabolic tails, in addition to finitely many isolated types. Distinct conjugate primary limbs cannot contain a common real infinitely renormalizable point (their wakes are disjoint); the only nontrivial invariant limb is 1/2. Indeed the actual tail images lie in the 1/(n+1) limbs, n>=q>=2 (KKL §3.1 p. 19), so none is real; at most the finite individual types can be real. Thus periods are bounded. B6/B7 use source-defined types, not arbitrary real near-parabolic geometry.

The rule order in the JSON counts each row once even when multiple contradictions apply. These proofs address syntactic emptiness, not existence in the remaining rows.

## Statement matches (A)

For nonempty candidates with refinement qg, ee, kkl, the positive refinement is the *full* named source predicate, not merely a growth-rate proxy. See per-row hypotheses. CS Theorem D gives shrinking parameter copies, EE §8 states MLC for its family, and KKL Theorem C asserts rigidity of the stated family. For eventual types, a finite tuning transfer is only valid after the tail fiber is known trivial (TUN Cor. 3.2); no inference from Julia local connectivity. EE and KKL proof dependencies (especially unpublished DKLP) are not audited. Later published results can overlap some A cells (especially qg vs Levin); “only” means no independently established whole-cell published coverage in this catalogue.

## Candidate residual fronts vs Dudko

There are three natural nonreal *candidate* fronts modulo finite prefixes, plus a real/vein documentation gap. They are not certified C classes:

- Eventually satellite: Problems 4.3 (§4.4) calls for remaining unbounded satellite ql cases, after neutral bounds Theorem 4.2. The latter alone is not a parameter-plane result.
- Eventually primitive: Problem 4.4 (§4.5) asks for a virtual molecule version of the near-degenerate regime, extending beyond uniform separation from the molecule. EE/KKL cover specified subfamilies; their failure is not equivalent to failure of the more general puzzle criterion in KKL B.
- Recurrent mixed: interaction of the two fronts; §4.5 discusses combining the regimes toward MLC. The survey's problems are analytic bottlenecks, not a disjoint partition of combinatorial addresses. KKL remark after C explicitly leaves mixing with bounded satellites out of that theorem.
- Real/vein gap: §4.3 following Theorem 4.1 reports real-line and vein MLC [14]. Real residuals are therefore not justified as genuinely open. Nonreal does not imply off every vein. The primary statement and scope are UNVERIFIED.

There is no established discrepancy in either direction between *genuine* open sets: the survey is not an exhaustive decision table and the atlas residuals are only negations of particular sufficient predicates. No mathematically minimal C partition is proved.

## Explicit audit witness (not a certified C witness)

For the bounded-digit eventually-satellite candidate, use the pure satellite address S(t_1)S(t_2)..., t_i=[0;3,...,3] (i entries). Take all + signs in the nearest-integer CF (all nonterminal remainders have magnitude <1/2); q_0=1, q_1=3, q_i=3q_(i-1)+q_(i-2), so 3^i <= q_i <= 4^i, and 1/4 <= t_i <= 1/3. Nested copies exist by tuning, without claiming singleton intersection. For any fixed finite tail, absolute periods grow as the product of previous q_j. Therefore log q_i/P_(i-1) -> 0; log |a_i|/P_(i-1) -> 0. CS QG_N fails even within each word and across levels (first digit always 3). Levin 1 fails both exponential tests; Levin 2 has |t_(i+1)|^(1/q_i) -> 1; addendum 1(1) fails bounded product times |t_i|. Original Levin 7's product-smallness hypotheses also fail. DL26 periods unbounded; DL23 special stationary bounded-type construction inapplicable. Y requires finite renormalizability. K, KLdec, KLmol, EE, KKL C require primitive levels/types absent on every tail. Lreal VIII and LY/LvS real hypotheses fail because every tail begins with a rotation distinct from 1/2; L/C SL fails since infinitely many distinct primary limbs occur (fixed finite collection of truncated secondary limbs impossible). Ldensity/GS concern real density, not complex MLC. KKL B as a general puzzle criterion not excluded by this calculation; DKLP and DKL primary unavailable. TUN alone provides no base case. Thus witness only to the specified audited exclusions, not universal noncoverage.

No checked explicit address for the eventually-primitive or recurrent-mixed front is asserted: their geometric anti-molecule and puzzle-family conditions must be verified on an explicit sequence of primitive types. The reserved cell is marked “see residual thread”; its particular address is not assessed.

## Reproduce

From repository root:

```sh
python3 -B research/frontier/mlc_open_cells_20261126/verify.py
python3 -B research/frontier/mlc_open_cells_20261126/verify.py --strict  # expected to fail until all nonreserved rows resolved
python3 -B research/frontier/mlc_open_cells_20261126/hash_inputs.py  # network; writes input_hashes.json
```

Structural validation checks exact 62 IDs, duplicate keys, class/evidence tags, source locators, and provenance manifest consistency; it cannot prove mathematical coverage or noncoverage. Strict mode deliberately does not pass on unresolved rows. 

**Not established:** exhaustive literature coverage; nonemptiness of A or residual cells; a global C classification; minimal C classes; C witnesses for all fronts; proof validity of recent preprints; real/vein primary hypotheses; any new MLC case.

**Status: imported + open.** Standalone documentary audit; no physical bridge or gate promotion. AI-assisted source inspection and reasoning; no independent human proof verification.
