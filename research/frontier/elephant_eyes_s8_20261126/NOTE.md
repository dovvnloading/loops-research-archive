# Elephant Eyes §8: shared-base-point objection

**Claim — NO GAP (a), for the specified pure satellite objection only.** In Kahn–Lyubich, *Elephant Eyes*, arXiv:2601.21905v1, §4.0.1, p. 9, E2 places the entire central **filled** little Julia set inside the open central puzzle domain. The common fixed attachment point of a pure satellite cycle is excluded. E1 also sends that central domain into a different open sector, so the first two little sets cannot share any point. The pure satellite configuration proposed in the prior audit cannot satisfy the stated hypotheses.

**Limits / status:** proved (the narrow topological exclusion) / no-gap (this objection only). This is a standalone source audit; no archive lemma, ledger change, or model-to-geometry identification is used. No new a priori bound is proved or imported here. In particular the quantitative amplification argument, its iteration to uniform bounds, other possible renormalization types, and the local-connectivity/rigidity implications of §8 are not independently audited. The conclusion is not that every assertion of the paper has been verified.

## Inputs and provenance

- Jeremy Kahn and Misha Lyubich, [arXiv:2601.21905v1, PDF](https://arxiv.org/pdf/2601.21905v1), [versioned HTML](https://arxiv.org/html/2601.21905v1). [Unversioned abstract and submission history](https://arxiv.org/abs/2601.21905), consulted 2026-11-26 UTC: only v1, dated 29 January 2026, is listed. Printed page numbers coincide with one-based PDF page numbers. Key pages: §4.0.1 and start of §4.0.2, p. 9; Lemmas 4.1–4.3, §5.0.1, p. 10; §7.1, p. 15; Theorem 7.1 and Lemma 7.2, p. 16; §8, pp. 18–19. PDF page images for pp. 9, 10, 15, 16, 18, 19 and HTML were inspected. Expected PDF SHA-256: `5eb36430a51a3fb6a1c04db15713aebc86068118450893ba2042021e4a8db725` (prior recorded download; not a fresh local byte hash). The CI verifier independently fetches the versioned PDF, checks this fingerprint and page markers, and writes `sources.json`. The source lock is evidence of bytes and locations, not evidence of a mathematical proof.
- Context only: merged PR #127, `research/frontier/dudko_p43_satellite_moduli_20261125/NOTE.md`, Elephant Eyes paragraph; base blob `bdd1ec1fd470ca36605cbc103d8553e06fbdcc87`. Its objection motivates the audit and its prior PDF hash is a byte-comparison target; none of its mathematical claims is used as a premise. The verifier records its SHA-256 for provenance. The only mathematical source is the authors' paper.

## Exact source language and proof

Section 4.0.1, p. 9, starts with an even quadratic-like map with connected Julia set and two repelling fixed points. Its q external rays land at alpha, and their symmetric preimages land at -alpha. Cutting by this graph produces open domains: the central domain Upsilon, and q-1 sectors each at alpha and -alpha. In particular alpha and -alpha lie on the cutting graph, not inside Upsilon. Here **domain** means open connected set; adjoining boundary landing points would instead give a closure, not the domain in the text. The definition of the cycle in the same paragraph explicitly uses filled little Julia sets K_n, with K_0 containing 0.

The decisive exact E2 sentence (p. 9, notation transcribed):

> E2. $K_0$ is the only little Julia set contained in $\Upsilon$.

This is the assertion of unique containment, not merely an assertion that the critical point lies in Upsilon. In particular $K_0\subset\Upsilon$, so $\alpha\notin K_0$ and $-\alpha\notin K_0$. A pure satellite cycle attached to alpha would require $\alpha\in K_0\cap K_j$ for every j; contradiction. This argument is insensitive to how many rays meet there.

There is an independent, even simpler check not requiring an identification of the common point with alpha. E1 on p. 9 first specifies rotation $1/\mathfrak q$, and gives the degree-two map $f:\Upsilon'\to S_1$ onto the first noncentral sector, where $\Upsilon'=\Upsilon\cap U'$. For a renormalization of the map $f:U'\to U$, the entire $K_0$ is in $U'$ (the return and intermediate iterates are defined on the filled set). Thus E2 gives $K_0\subset\Upsilon'$, and the little-cycle definition gives $K_1=f(K_0)\subset S_1$. Since $S_1\cap\Upsilon=\varnothing$, we have
$$K_0\cap K_1=\varnothing.$$
This contradicts a pure satellite cycle in which all p=q little sets have a common base point, even if that point is not named. It excludes this configuration for every admissible q>1, not just asymptotically. Compactness of the filled set inside the open central domain also excludes merely touching its boundary at the attachment point.

### Hypothesis-by-hypothesis hostile check

| Stated input | Candidate: pure satellite at the parent fixed point |
|---|---|
| Even quadratic-like map, connected Julia set, both fixed points repelling (§4.0.1, p. 9) | Not the exclusion; such requirements alone do not imply disjointness. |
| E1: rotation 1/q and sector mapping (p. 9) | Rotation 1/q is compatible with the satellite combinatorics; sector mapping is the disjointness argument once E2 holds. |
| E2: K_0 contained in the central domain and unique there (p. 9) | **Fails**: the closed filled set contains the ray landing point on the domain boundary. Alternatively E1+E2 imply disjoint K_0, K_1. |
| E3: p=q+b, b bounded and b<q (p. 9) | p=q, b=0 satisfies the written numerical constraints. We do not assume b>0 to rule out the candidate. |
| §7.1 class and Theorem 7.1 thresholds (pp. 15–16) | The class requires the preceding combinatorics. No choice of large q, large p or large local weight repairs failure of E2. |

A drawing with closed sectors and a common vertex can have the desired cyclic order, with one piece in each closed sector. It is not a counterexample to E2. Replacing the domains by their closures is a change of hypotheses. A punctured piece with the vertex removed is not the compact filled Julia set required by §4.0.1. Neither model survives the literal reading.

### Check of the amplification setting

Section 7.1, p. 15, restricts the class Q to renormalizable pseudo-ql maps with elephant-eye combinatorics and parameters q at least the lower cutoff and b at most the upper cutoff. Its translation domains contain whole little sets in consecutive sectors, with local weight comparability (P1) and two-short-arc concentration (P2). Its Translation Property explicitly requires “$L$ pairwise disjoint translation domains” for arbitrary large N,L and sufficiently large p. If all little sets shared a point, two such domains containing respective whole sets could not be disjoint. This is a consistency check of the setup, not an independent proof of the Translation Property. Do not treat P1/P2 or the derived property as a substitute for E2.

Theorem 7.1, p. 16 (Amplification Theorem), asserts $\mathcal W^{\rm ver}\ge\lambda\mathcal W_{\rm loc}$ for any specified $\lambda>1$, sufficiently large N,L and lower cutoffs on $\mathcal W_{\rm loc}$ and p, within that setting. It is a weight inequality, not a statement for arbitrary satellite cycles. Lemma 7.2, p. 16, uses a buffer annulus in the pseudo-domain complement of the union of little sets around an individual set. The literal §4.0.1 E2 exclusion precedes these arguments; pseudo-ql terminology alone is not being used to resolve a collision by separating sheets.

## §8 and significance

Section 8, p. 18, asserts that the definite-modulus fundamental annuli avoid the noncentral top-level little Julia sets. It does not separately construct such annuli there; it invokes the preceding bounds. The MLC outline continues on p. 19. In the proposed touching configuration, if an inner disk contains the shared point and another connected little set also meets the outside of the outer disk, the latter must meet the collar between them: otherwise it would be separated into two nonempty relatively open parts. This is a valid conditional topological observation, but its antecedent is not an example in the elephant-eye class. Also, touching alone does not force an arbitrary collar to intersect the other piece if that entire piece is inside the inner disk; the objection concerns a collar isolating one piece, not a collar around a whole bouquet.

**Significance:** no erratum to the theorem is indicated by this pure-satellite objection, and no main conclusion is invalidated by it. At most an expository clarification (not a new hypothesis or a repair) could follow E2: the central filled little set is contained in the open puzzle domain, hence misses the landing points of the cutting rays, and E1 implies disjointness from its first image; pure satellite bouquets are excluded. The earlier paragraph should not be read as a counterexample to the paper. This audit leaves the quantitative annulus construction and any further concerns about the main theorem outside the claim.

**Not established:** uniform modulus lower bounds, a proof of Theorem 7.1 or its iteration, the general disjointness of all cycles of arbitrary satellite type, an actual new parameter, bounds for touching bouquets, applicability beyond the literal E2 class, any new local connectivity or MLC theorem, or a new ledger/bridge implication. No specialist human review has been performed. GPT-6.2 assisted with source comparison, the exclusion argument and verifier construction.

## Reproduce

From the repository root, Python 3.12; no random samples or numerical geometry. Network access is needed for the PDF. The only Python dependency is pinned.

```sh
python3 -m pip install -r research/frontier/elephant_eyes_s8_20261126/requirements.txt
python3 -B research/frontier/elephant_eyes_s8_20261126/verify.py --output /tmp/elephant-sources.json
cmp /tmp/elephant-sources.json research/frontier/elephant_eyes_s8_20261126/sources.json
python3 -B code/verify_physical_bridges.py
```

The verifier checks the fixed PDF SHA-256 and section/page markers, not the interpretation of E2. Inspect the cited page images for the mathematics. CI commits only the generated source manifest on the named branch if initially absent, then checks exact reproduction on the PR. No PDFs are redistributed. A failed download or mismatch is a failure, not a successful certificate.
