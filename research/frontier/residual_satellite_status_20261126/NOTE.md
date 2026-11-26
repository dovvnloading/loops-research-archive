# Residual satellite address: source-statement audit

**Verdict: GENUINELY OPEN (scoped to the independently checked literature).** No tail of the address S(1/3) S(1/4) S(1/5) ... satisfies the rigidity theorem of Cheraghi–Shishikura. Their high-type *existence* theorem does apply after a sufficiently long finite prefix, but it is not a rigidity theorem. The cross-level quadratic growth hypothesis in their Theorem D fails for every tail. No other audited theorem supplies the missing singleton fiber. This is a negative applicability audit, not a new MLC case or a proof of exhaustive noncoverage.

## Limits and target

This answers the source question raised by merged [#132](https://github.com/dovvnloading/loops-research-archive/pull/132), its [atlas note](../mlc_coverage_atlas_20261126/NOTE.md), atlas.json and [independent review](https://github.com/dovvnloading/loops-research-archive/pull/132#issuecomment-7181975461). Base main b25d26d9151fbaf5c8acf4bf00c6b56e42cd3a4c. The atlas's other theorem exclusions are inherited as such, not newly independently audited here. No other cells or ledger entries are modified. “Open” means no verified sufficient implication for the specified address, not a logical proof that no such result exists.

Index the tail by i ≥ 1, starting denominator L ≥ 3. Write q_i = L+i−1, t_i = 1/q_i, and P_i = q_1 ... q_i, P_0=1. Use maximal relative satellite renormalizations. The nested nonempty compact tuned copies have nonempty intersection; do not assume it is a singleton. Every tail is nonreal in the first 1/L limb and its relative periods are unbounded.

## 1. Cheraghi–Shishikura: two different theorems

Primary sources: [arXiv:1509.07843](https://arxiv.org/abs/1509.07843), latest listed version **v1**, submitted 25 September 2015; [arXiv PDF](https://arxiv.org/pdf/1509.07843v1) (rendered unversioned endpoint shows v1, internal date July 19, 2018); [author PDF](https://www.ma.imperial.ac.uk/~dcheragh/Research/2015-2.pdf) (internal date September 9, 2022; not an arXiv v2). Journal publication UNVERIFIED. Page references below are printed pages, not guessed journal pages.

### Exact combinatorics and normalization

ArXiv p. 4 defines satellite polynomial-like (PL) renormalization: a quadratic-like proper degree-two return, with critical orbit in the small filled Julia sets, which all meet at the same fixed point. The prescribed rational is the combinatorial rotation of this cycle. At each successive straightening, satellite tuning by 1/q has this type, not a primitive return. The source uses signed representatives in (−1/2,1/2] and signed continued fractions with digits b≥2 and signs ε=±1 (pp. 5–6; §6.1, (38), p. 56). For t=1/q with q≥3, the signed nearest-integer Gauss step subtracts the integer −q from −1/t=−q and terminates at zero. Thus the expansion is exactly one digit b=q, sign +1. There is no alternative longer canonical expansion or sign obstruction.

ArXiv p. 2 defines the near-parabolic parameter domain by 0<|α|≤ρ and |Re α|≥|Im α|. The actual normalized logarithmic multiplier α is complex, not the rational combinatorial rotation t. The top and bottom near-parabolic renormalizations involve different marked fixed points and normalizations (pp. 2–4). The small positive real number 1/q lies in the numerical cone for q≥ceil(1/ρ), but this does NOT prove that the actual analytic multiplier of every representative is there. In particular, one cannot identify a rational satellite rotation with an analytic multiplier or silently replace a PL return by a near-parabolic (NP) return.

### Theorem C: yes for high-type existence

ArXiv Theorem C p. 5 (author PDF Theorem C p. 4) asserts existence of a parameter for prescribed infinite satellite combinatorics when the source's uniform threshold N is met by every signed digit. The quantifier is “there is c ∈ M”. It supplies an infinitely PL-renormalizable and compatible NP-renormalizable representative; the one-digit rotations use the bottom steps of the prescribed NP tower. The threshold is uniform, not chosen independently at each level. For every L≥max(3,N), b_i=q_i≥N for all i. Therefore the combinatorial hypotheses hold for that tail and its existence conclusion applies. The source's construction supplies the required normalization for the representative it constructs; there is no need for an extra negative sign or for small initial q to satisfy the threshold. This does not establish that *every* member of the combinatorial class is that representative, nor does hyperbolicity of NP renormalization (Theorem B) supply this missing inclusion by itself.

### Theorem D: no for every tail

ArXiv Theorem D p. 6, definition of QG_N p. 6 and equation (44) p. 62; author PDF Theorem D p. 6, QG_N p. 5 and (6.8) p. 62. Its conclusion includes “combinatorially rigid” and local connectivity, with exponential shrinking of the nested combinatorial classes. In the notation b_(i,j) for signed CF digits and m_i for the length, its actual sufficient conditions are:

- b_(1,1)≥N;
- b_(i,j+1)≥b_(i,j)^2 for 1≤j<m_i;
- b_(i+1,1)≥q_i^2 for every i, where q_i is the reduced denominator of t_i.

For one-digit rotations the p. 62 specialization is exactly q_1≥N and q_(i+1)≥q_i^2 (numerator ±1). Here m_i=1, so within-level growth is vacuous. The first digit can be made arbitrarily large, but q_(i+1)=q_i+1<q_i^2 for every q_i≥3: q_i^2−q_i−1≥5. Hence no finite prefix removal, no larger choice of starting denominator, and no smaller uniform threshold repairs the cross-level condition. This is a universal inequality, not a numerical extrapolation. Theorem D's whole-class shrinking cannot be obtained from C's existential claim by logic alone. This is the exact obstruction to *using the theorem*, not a necessary condition for MLC or proof that an actual NP class condition fails.

## 2. Finite tuning: valid conditional transfer, no antecedent here

[Schleicher, On Fibers and Renormalization of Julia Sets and Multibrot Sets, IMS 1998/13b](https://www.math.stonybrook.edu/preprints/ims98-13b.pdf), also arXiv:math/9902156v1. Primary IMS scan: introduction p. 2, Theorem 3.1 and Corollary 3.2 p. 6, proof pp. 6–7. Cor. 3.2 states invariance of trivial fibers under tuning; its proof notes “the fiber of any point in M' must entirely be contained in M'”. Theorem 3.1 supplies the little-copy/decoration separation setup. Journal publication of this source UNVERIFIED.

The exact required input is triviality of the parameter fiber, not just pointwise local connectivity. If a tail satisfied CS Theorem D, its whole nested combinatorial copies would shrink exponentially in diameter. Schleicher's fiber containment for each tuned copy would then force the fiber of the limiting point to be the singleton intersection. This supplies the stronger hypothesis, and the finite prefix could be restored by the composition of tuning maps, preserving triviality in both directions. This would be a chain using the CS preprint and IMS preprint transfer (publication status unverified), not a new theorem. For this address, D does not apply on any tail. C gives no diameter bound for the whole class and hence no singleton fiber. The tuning transfer therefore has no established antecedent. In particular, merely replacing “trivial fiber” by “MLC at that point” is unjustified.

## 3. Other possible routes

The following primary statements were opened and checked at the indicated locators (not their entire proofs). Short quoted anchors identify the relevant condition.

**Dudko–Lyubich, MLC at Feigenbaum points**, [arXiv:2309.02107v3](https://arxiv.org/pdf/2309.02107v3), Theorems A/B p. 3, §2.2.5 pp. 10–11. [Published DOI 10.5802/pmihes.2](https://pmihes.centre-mersenne.org/articles/10.5802/pmihes.2/), Publ. Math. IHÉS 143 (2026), 97–141. Bounded type means “if the relative periods are bounded by” a common finite bound. Their bounded-type Feigenbaum theorem includes satellite combinatorics, but q_i→∞ on every tail. No.

**Dudko–Lyubich, Uniform a priori bounds for neutral renormalization**, [arXiv:2210.09280](https://arxiv.org/abs/2210.09280), source text §1.1, Theorems 1.1–1.3. Neutral bounds concern Siegel/neutral maps, including irrational rotation and mother-hedgehog statements. PDF pagination and exact version UNVERIFIED; source text was accessible but PDF was not rendered. [Part II, arXiv:2509.23031v2](https://arxiv.org/pdf/2509.23031v2), Theorems 1.1–1.2 pp. 3–4, Definition 2.1(III) p. 7: “bounded-type rotation number” of a ql Siegel map. This does not mean a sequence of rational satellite dividing rotations whose denominators tend to infinity. Neither neutral-map bounds nor the existence of an NP representative gives the needed unbounded satellite parameter rigidity theorem. In [Dudko's survey, arXiv:2512.24171v1](https://arxiv.org/html/2512.24171v1), §4.4, Theorem 4.2 and Problem 4.3 distinguish these settings; the latter asks: “Establish pseudo-Siegel a priori bounds in the remaining unbounded satellite ql cases.” Survey PDF pagination UNVERIFIED. The survey is corroboration, not an impossibility theorem. The real/vein manuscript cited in §4.3 [14] remains UNVERIFIED; no claim about all veins.

**Kahn–Lyubich, Elephant Eyes**, [arXiv:2601.21905v1](https://arxiv.org/pdf/2601.21905v1), §4.0.1 E1–E3 p. 9; §8 p. 18. E1 has rotation 1/q; E3 p=q+b with bounded b, so the arithmetic p=q alone is not the relevant exclusion. E2 requires “K0 is the only little Julia set contained in Υ.” The domain Υ is the central open puzzle piece bounded by rays at the dividing fixed point and its opposite; in the pure satellite case every little filled Julia set contains the common dividing fixed point on its boundary. The central little filled Julia set is not contained in the open domain as required. Merely allowing closed puzzle pieces would not establish the source's geometric construction: §§4.0.2–4.0.3 use distinct collapsed little sets and translation sectors; §8 uses unbranched annuli disjoint from the other little sets. Pure satellite shared-base-point geometry supplies none of that separation. E1 and a formal b=0 do not establish the full hypothesis. The stated MLC application is preprint-only here; its dependencies are not audited in this thread. No use of or edits to the cell-classification thread.

**Kahn–Kapiamba–Lyubich**, [arXiv:2606.27272v1](https://arxiv.org/pdf/2606.27272v1), Theorem C p. 4: “Any parabolically bounded family of prime primitive types is rigid.” Pure satellite returns are not prime primitive; mixed extension is outside the stated scope. Preprint; cited DKLP in preparation UNVERIFIED.

**Cheraghi**, [Combinatorial rigidity for some infinitely renormalizable unicritical polynomials](https://www.ma.imperial.ac.uk/~dcheragh/Research/2010-1.pdf), Rigidity Theorem p. 2, SL definition p. 13. The hypothesis is “satisfying the a priori bounds and SL conditions”. The latter uses finitely many truncated secondary limbs; the straightened maps in this address begin in limbs of unbounded denominators, so no finite such family works. This published theorem is not a high-type-only result. The [author's research list](https://www.ma.imperial.ac.uk/~dcheragh/research.html) lists Complex Feigenbaum phenomena of high type (with M. Pedramfar) under manuscripts in preparation. No accessible primary theorem establishing MLC for arbitrary high-type satellite addresses was identified; manuscript, precise theorem, page and publication status UNVERIFIED. A manuscript title is not a rigidity result.

**Levin**, [arXiv:0710.4406v4](https://arxiv.org/pdf/0710.4406v4), Theorem 1 p. 1, Theorem 2 pp. 3–4, Addendum Theorem 1(1) PDF p. 42 (separately printed p. 1). Thm 1 requires a positive limsup of log numerator or log denominator divided by the absolute simple-return period; Thm 2 requires “lim sup” of |t_(i+1)|^(1/q_i) strictly below one. The addendum requires bounded prior product times |t_i| and positive limsup of denominator divided by squared prior product. Here P_(i−1)≥3^(i−1), log|numerator|=0, log(q_i)/P_(i−1)→0, exp(−log(q_i+1)/q_i)→1, P_(i−1)/q_i→∞, q_i/P_(i−1)^2→0. All these exclusions hold on every tail and every relevant subsequence. No inference about JLC is made.

## 4. Source inputs and reproduction

The SHA256 values below fingerprint the bytes downloaded by CI, not a claim that the web-rendered copy was byte-compared to them. The statement-reading and byte-provenance steps are distinct. HTML and unversioned endpoints may change; UNVERIFIED means retrieval failed, not a mathematical exclusion. Full third-party PDFs are not committed. Source links, version differences and theorem/page locators are above. The exact absent manuscripts are not assigned fictitious hashes.

<!-- BEGIN SOURCE LOCK -->

| Source | Input URL | SHA256 |
|---|---|---|
| CS-arxiv | <https://arxiv.org/pdf/1509.07843v1> | 71c03718203b91ae81f5b7e138620a086cdf038b345cf689a24ed2932d72384f |
| CS-author | <https://www.ma.imperial.ac.uk/~dcheragh/Research/2015-2.pdf> | b1d6b0952247efc3cd7a6e0602dbb8246b43b9edf7b3c5d0da942cc822246c25 |
| CS-version | <https://arxiv.org/abs/1509.07843> | 6426203313859c50b91a7885ff575093d34b7fdcfb6eab77f9750c70445157f6 |
| TUN | <https://www.math.stonybrook.edu/preprints/ims98-13b.pdf> | 1095be3a23d83cbc8acafe1c8ff7e24d787ffe791cdf8ea90b4f2b9686af8195 |
| DL26 | <https://arxiv.org/pdf/2309.02107v3> | e88462e43b3c172cf309d5b3d38caa21ee8f43876bac1e07cce84b309dfb8c6b |
| DL-neutral | <https://arxiv.org/pdf/2210.09280> | 05ee1c1ca66bfd4f7c4e6f4b97875e34e629f0ed52344a5ffae24704e6247acf |
| DL-neutral-II | <https://arxiv.org/pdf/2509.23031v2> | 3432ae7667313cf04cb3c9368f2b816679fbbca0fb0f40105fac0bcfba900cea |
| EE | <https://arxiv.org/pdf/2601.21905v1> | 5eb36430a51a3fb6a1c04db15713aebc86068118450893ba2042021e4a8db725 |
| KKL | <https://arxiv.org/pdf/2606.27272v1> | 4c08805384b473dc0e55d76491c52c9fbe7c027e6da301f2c365a170ed7d9140 |
| C2010 | <https://www.ma.imperial.ac.uk/~dcheragh/Research/2010-1.pdf> | c62ea484883ccb860286aab19a21d31bfdb22d102a792594d5b8986f6769c72d |
| Levin | <https://arxiv.org/pdf/0710.4406v4> | 8e5a59b111c0d841d5deb3ab7adb12b556896a2916c1e4cc8418fe41789335cd |
| survey | <https://arxiv.org/html/2512.24171v1> | 88339ff2d95cef8a6255bad70d15839807e97342e5dde33a5f1698d0baa1ccd9 |
| C-list | <https://www.ma.imperial.ac.uk/~dcheragh/research.html> | 4573027037a153c06cf6306b2d66ca614fb5ff320ef9c7178469b8366fca35d3 |
| DL-publisher | <https://pmihes.centre-mersenne.org/articles/10.5802/pmihes.2/> | 5fd9f5ab502db366d67f2012b59f2b37a313d0448956e12abd6216af970f3456 |

<!-- END SOURCE LOCK -->

Python 3.12, standard library only. From the repository root:

    python3 -B research/frontier/residual_satellite_status_20261126/verify.py
    python3 -B research/frontier/residual_satellite_status_20261126/verify.py --lock
    python3 -B research/frontier/residual_satellite_status_20261126/verify.py --check-lock

The first tests finite exact rational/integer regression; the general inequalities are proved in §1 and §3. The second retrieves sources and rewrites only this NOTE's hash block and sources.lock.json; the third checks lock format and exact correspondence with the NOTE table offline. CI green does not certify completeness of downloads, proof correctness, or MLC. The verifier is a standalone METADATA source, not a physical bridge or an extra MLC premise.

## 5. Status and nonclaims

**Status label: GENUINELY OPEN (scoped source audit; no verified covering implication).** Exact failed CS hypothesis: b_(i+1,1)≥q_i² for all i, on every finite tail. A uniform high-type threshold and sign condition are satisfiable; actual NP normalization exists for a representative by C. There is no established full-fiber rigidity or exponential shrinking for this address, no verified published or preprint chain that resolves it, and no proof here that the address has multiple parameters, a nontrivial fiber, nonlocal connectivity, or any particular JLC behavior. No claim of a complete literature search, no negative theorem about other high-type satellite sequences, no new MLC case, and no promotion of any archive ledger gate. Unavailable sources remain UNVERIFIED rather than silently excluded.

AI disclosure: GPT-6.2 performed source-statement comparison, exact arithmetic and verifier/workflow drafting. No independent human specialist verification has occurred. This contribution is for separate review.
