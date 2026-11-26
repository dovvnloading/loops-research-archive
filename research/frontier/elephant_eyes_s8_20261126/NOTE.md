# Elephant Eyes §8: shared-base-point objection

**Final research label: NO GAP (a) — the shared-base-point objection only.** Verified conditional topological exclusion under the written elephant-eye hypotheses E1–E3; standalone source audit (METADATA), not a proof of the paper's quantitative results. In particular E1+E2 exclude the common-point pure satellite bouquet at one parent renormalization level. E1–E3 also exclude pairwise contact of distinct little filled Julia sets at that level, as shown below. This is not a claim about arbitrary satellite cycles or a general proof of unbranched a priori bounds.

## Primary source and scope

Jeremy Kahn and Misha Lyubich, *A priori bounds for some infinitely renormalizable quadratics: IV. Elephant Eyes*, [arXiv abstract/history](https://arxiv.org/abs/2601.21905), [versioned PDF](https://arxiv.org/pdf/2601.21905v1), [versioned HTML](https://arxiv.org/html/2601.21905v1). The history checked on 2026-11-26 UTC lists only v1 (29 January 2026). Printed pages match one-based PDF pages. Independent review checked the PDF page images for pp. 9, 10, 15, 16, 18, 19 and the versioned HTML. The mathematical argument below is a deduction from §4.0.1, not a machine proof.

Context only: merged #127, [its NOTE at the original base](https://github.com/dovvnloading/loops-research-archive/blob/4b11268b2234127f472aaa76a97be3f8f66763aa/research/frontier/dudko_p43_satellite_moduli_20261125/NOTE.md), blob `bdd1ec1fd470ca36605cbc103d8553e06fbdcc87`. The Elephant Eyes paragraph says large q and p=q+O(1) alone do not establish the hypotheses; it gives a conditional collar obstruction for a pure satellite cycle with touching pieces, explicitly applying no Elephant Eyes result to its examples. It does **not** exhibit a cycle satisfying E1–E3 that contradicts §8. Its conditional observation is correct (see below); treating it as an actual gap in the paper would be unsupported. Its recorded PDF fingerprint is a comparison target, not a mathematical premise.

## Hypotheses and separation

§4.0.1, p. 9: the even quadratic-like map f:U'→U has connected Julia set and both fixed points repelling. The q>1 rays landing at α and symmetric rays landing at −α partition U into the open central domain Υ and sectors S_i, Z_i, 1≤i≤q−1. The landing points are on the cutting graph. The authors define the period-p cycle using little **filled** Julia sets K_n, n=0,…,p−1, K_0 containing 0. We use the usual cycle identity f(K_i)=K_{i+1 mod p}; all members are in U' since the iterates of the renormalization are defined on K_0 and the cycle returns to K_0.

E2, §4.0.1, p. 9 (notation transcribed):

> E2. $K_0$ is the only little Julia set contained in $\Upsilon$.

Thus K_0⊂Υ, not just 0∈Υ. In particular α, −α∉K_0. A pure satellite bouquet attached to the parent α would contain α in every K_i; it fails E2. Taking closures of the open domains or deleting the base point from a filled set would change the hypotheses.

E1 specifies rotation 1/q and maps Υ'=Υ∩U' onto S_1 with degree two, and maps S_i'=S_i∩U' univalently onto S_{i+1} for 1≤i≤q−2. Hence E1+E2 imply K_1⊂S_1, disjoint from K_0⊂Υ. This already excludes **any common point of all p sets**, irrespective of its name, provided p≥2. Neither rotation 1/q alone nor the numerical constraints in E3 alone exclude a bouquet; setting b=0 in p=q+b, b bounded and b<q is numerically permitted, not a proof of realization. E1's sector mapping together with E2 is essential to the argument independent of the identity of the attachment point.

A stronger separation check addresses whether a touching pair rather than a single common point could occur under the full written hypotheses. By induction using the displayed E1 sector maps, K_i⊂S_i for 1≤i≤q−1 as long as i<p; thus K_0,…,K_{min(q,p)−1} lie in mutually disjoint open domains. If p≤q, all p sets are already disjoint (indeed p<q would contradict the same sector itinerary at the return). Otherwise E3 gives q<p<2q. For two distinct indices i,j modulo p, orient the pair so that d=(j−i) mod p satisfies 1≤d≤floor(p/2)<q. If x∈K_i∩K_j, then f^{(-i mod p)}(x) belongs to K_0∩K_d, impossible by the sector itinerary. Therefore all distinct K_i are pairwise disjoint under E1–E3. This argument is in the original quadratic-like setting, not a claim about arbitrary pseudo-domain identifications. It uses the actual filled sets and cyclic dynamics; it does not use a quantitative theorem, and it would not imply a uniform separation or modulus bound over varying maps. The footnote in §4.0.2, p. 9, discusses extending that discussion beyond E2; it does not remove E2 from the definition used here.

## Amplification and §8

§4.0.3, p. 10, introduces translation domains and Lemmas 4.2–4.3. §5.0.1, p. 10, passes to the pseudo-ql setting. §7.1, p. 15, defines Q as renormalizable pseudo-ql maps “with the elephant eye combinatorics”, q bounded below, b bounded above, p=q+b. Its translation domains contain whole little sets, with P1 local weight comparability and P2 concentration on two short arcs; the Translation Property asserts L mutually disjoint translation domains for arbitrary large N,L and sufficiently large p. A bouquet sharing one point cannot have two disjoint domains each containing a whole member. This is a consistency check, not a proof of the Translation Property or of the analytic passage to pseudo-ql maps.

Theorem 7.1 (Amplification Theorem), §7.2, p. 16, asserts $\mathcal W^{\mathrm{ver}}\ge\lambda\mathcal W_{\mathrm{loc}}$ for any amplification factor λ>1, sufficiently large N,L, and lower cutoffs on local weight and p, within the §7.1 setting. Lemma 7.2's proof, p. 16, uses a maximal immersed buffer annulus in the pseudo-domain minus the union of little sets, around an individual K_s. Neither statement is being proved here, and an immersed annulus is not by itself the ordinary unbranched annulus of §8. The exclusion in the preceding section concerns the original planar configuration.

§8, p. 18, says that the fundamental annuli of the a priori bounds “do not intersect any non-central little Julia sets” (of the top level). It invokes the bounds and states their unbranched property; it does not introduce a pure satellite bouquet or identify any touching pieces at that level. Page 19 outlines the MLC argument (Steps 0–3). Thus the shared-point hypothesis of the #127 conditional objection is not a configuration exhibited by §8 or allowed at a level satisfying E1–E3. E2 alone need not establish all pairwise separations; the proof above uses E1 and E3 as well.

The collar observation itself is valid: for an ordinary annulus between nested disks, if a connected second filled set meets both the interior of the inner disk (e.g. at an attachment point) and the exterior of the outer disk, it must meet the intervening open collar. Otherwise the inner closed disk and the closed exterior split that connected set into two nonempty relatively closed disjoint parts. A common point alone does not force every collar to cross the second set: it might lie entirely in the inner disk. Neither the pure bouquet nor a pair of touching pieces at the top elephant-eye level is an admissible counterexample by the preceding argument. This only disposes of this particular obstruction, not the existence or quality of the annuli.

**Limits (explicit):** The broader quantitative claims of the paper remain unaudited, including the estimates and proof of Theorem 7.1, their iteration to uniform a priori bounds, the construction and definite modulus of ordinary unbranched annuli, and the local-connectivity, rigidity and MLC implications in §8. Pairwise disjointness is not a uniform quantitative bound. No general no-gap verdict, new a priori bound, actual parameter, result for touching bouquets, application beyond E1–E3, or ledger/model-to-geometry implication is established. No specialist human certification is claimed; this is an AI-assisted source audit and independent AI review.

## Verifier and reproduction

`verify.py` uses pinned `pypdf==5.4.0`, downloads the fixed v1 PDF, rejects a non-PDF response, wrong SHA-256 or page count, and missing normalized page markers on pp. 9, 10, 15, 16, 18, 19. The committed `sources.json` records 398123 bytes, 20 pages, SHA-256 `5eb36430a51a3fb6a1c04db15713aebc86068118450893ba2042021e4a8db725`, the actual required markers, and the SHA-256 of the contextual #127 NOTE (`b3479920d93525438d9a08838a76f8e14449e362b706c3275819f7d0d79b3663`). The prior head's CI [run 45745302134](https://github.com/dovvnloading/loops-research-archive/actions/runs/45745302134), job 139659771033, reported a matching versioned PDF digest and markers and successful manifest comparison and registration. This is a CI-recorded byte hash, not a separate local download by the reviewer. The verifier records the contextual NOTE hash rather than hard-coding it; exact manifest comparison in CI checks it. The verifier does **not** check latest-version history, the mathematical interpretation, any topology or quantitative theorem, or the truth of this NOTE. Source and interpretation were checked separately against arXiv.

From the repository root, Python 3.12; network access required, no numerical geometry or random samples:

```sh
python3 -m pip install -r research/frontier/elephant_eyes_s8_20261126/requirements.txt
python3 -B research/frontier/elephant_eyes_s8_20261126/verify.py --output /tmp/elephant-sources.json
cmp /tmp/elephant-sources.json research/frontier/elephant_eyes_s8_20261126/sources.json
python3 -B code/verify_physical_bridges.py
```

The final workflow always requires exact reproduction of the committed manifest (no auto-commit fallback), then checks source registration. A missing manifest, failed download, or mismatch fails CI. It also runs on main so the source lock is checked after merge. The only registry change is this verifier's METADATA row; no ledger changes. No PDF is included.
