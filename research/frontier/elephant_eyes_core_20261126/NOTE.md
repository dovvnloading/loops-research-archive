# Elephant Eyes: core amplification audit

**Verdict: BOUNDED NEGATIVE / OPEN — equation (7.5), §7.5, p. 18, arXiv:2601.21905v1.** I could neither establish nor refute the asserted lower bound
     
    Σ_{n∈I_l} ν_n ≥ (2N+1)(1−ε) W_0 / 2.

The printed argument establishes, at its stated correspondence interface, a single packet of weight at least W_0/2; its final containment assertion does not explicitly supply the multiplicity needed for the displayed factor 2N+1. A finite incidence diagnostic isolates the missing implication. It is **not** a configuration of a quadratic-like map satisfying E1–E3. I do not assert that (7.5) is false, that the proof cannot be repaired, or that Theorem 7.1 or MLC fails. This is a source audit, not an alternative theorem.

## 1. Version, scope and context

Jeremy Kahn and Misha Lyubich, *A priori bounds for some infinitely renormalizable quadratics: IV. Elephant Eyes*, [abstract/history](https://arxiv.org/abs/2601.21905), [v1 PDF](https://arxiv.org/pdf/2601.21905v1), [v1 HTML](https://arxiv.org/html/2601.21905v1). History checked 2026-11-26: v1, 29 Jan 2026, only listed version. Printed pages = PDF page numbers. Inspected text and relevant page images. Throughout, W denotes the paper's extremal width/arc-diagram weight, not Euclidean size. Pullback stars and boldface pseudo-domains are important; suppress boldface only in the algebra below.

Read CONTRIBUTING.md and RESEARCH_MAP.md and the discussion/reviews of merged [#131](https://github.com/dovvnloading/loops-research-archive/pull/131), [#132](https://github.com/dovvnloading/loops-research-archive/pull/132), [#134](https://github.com/dovvnloading/loops-research-archive/pull/134), [#144](https://github.com/dovvnloading/loops-research-archive/pull/144), [#129](https://github.com/dovvnloading/loops-research-archive/pull/129) and [#138](https://github.com/dovvnloading/loops-research-archive/pull/138). #131 excludes the specific section-8 common-point objection via E2 (and E1); that is not proof of a width bound. Atlas coverage by EE is at the level of a preprint statement, not proof certification. #129 and #138 motivate a single-load-bearing-inequality audit; their positive repair hypotheses are not inputs here. No atlas/ledger or other thread edits.

## 2. Chain map (locators in EE v1)

Theorem 7.1 is an amplification theorem about a single renormalizable pseudo-quadratic-like map with the stated combinatorics, not literally a theorem phrased as a uniform lower modulus bound on the whole infinite tower. Separate the statement, its proof, and the further dynamical applications. Arrows below indicate proof dependencies or cited interfaces, not independent certification of every lemma.

| Node / page | Input → output / downstream use |
|---|---|
| §4.0.1 E1–E3, p. 9 | Even QL map with connected Julia set and both fixed points repelling; E1: rotation 1/q, double cover of S_1 from central Υ′, univalent S_i′ and Z_i′ → S_{i+1} (i≤q−2), final sectors map to the union of Υ, Z_i and the symmetric rays; E2: K_0 is the only little filled Julia set in Υ; E3: period p=q+b with b bounded, assuming b<q for simplicity. Thus S_i contains only K_i for 1≤i≤q−b. Use the full geometric hypotheses, not just p=q+b. |
| Lemma 4.1, p. 10 | Hubbard-tree return geometry: at most two-to-one, with bounded number of edges (≤b+1); used in the local flux comparison. |
| Lemma 4.2, p. 10 | Translation domains Ω_l and the p-return pullback retain the central sector interval; enables windows around K_l and Ω'. |
| Lemma 4.3, p. 10 | Short horizontal connections with both ends retained in a translated interval do not pull off away from K_1; used to constrain eligible indices for pull-off in §7.5. Not a numerical multiplicity assertion. |
| Lemmas 3.1–3.2, p. 2; Lemma 3.3, Cor. 3.4, Lemma 3.5, Prop. 3.6, Thm. 3.7, pp. 3–4; Lemma 3.8, p. 5 | Canonical lamination and width bookkeeping for the marked disk/surface; thin/thick control, localization. Foundational geometry, not deductions from E1–E3 alone. |
| Lemmas 3.9–3.10, pp. 6–7; Cor. 3.11, p. 7 | Boundary marking, proper-domain and thin/thick error control; additive error proportional to number of marked pieces. |
| Lemma 3.12, pp. 7–8; Lemma 3.13, p. 8 | Width under covers, embeddings and pullback; parallel/series bookkeeping. These compare properly typed curve families, not counts of their translates. |
| Lemmas 3.14–3.15, pp. 8–9 | Key estimate on segment subdivision and loss of arc weight under restrictions; input to §5 and to accounting for newborn arcs in §§6–7. |
| §5.0.1 & Lemma 5.1, pp. 10–11 | Pseudo-QL domain with little Julia sets removed; local widths W_n; W_loc=max W_n; compare local widths along orbit, and W^ver at outer boundary (half the corresponding inner-boundary width). |
| Lemmas 5.2–5.3, p. 11 | Local fluxes: pullback comparison using §3 and 4.1; bounded multiplicative comparison. |
| Lemma 5.4, Corollaries 5.5–5.6, p. 11 | Segment diagram weights and peripheral components; 3.14 controls loss. |
| Lemma 5.7, Corollary 5.8, pp. 11–12 | Short segments and control of mass on others. |
| Cor. 5.9, Lemma 5.10, Corollaries 5.11–5.12, p. 12 | Failure of amplification bounds long/arc-segment weight; 3.15 participates in the arc-segment comparison. |
| Theorem 5.13, Corollary 5.14, pp. 12–13 | Under non-amplification, horizontal weight concentrated on short arcs; comparable local weights/fluxes for initial translation range n≤κq. |
| Lemmas 6.1–6.2, pp. 13–14 | Separating vertical curves and fast pull-off of horizontal arcs in <p steps. §7.5 invokes an adaptation to V; §6 itself treats bounded combinatorics. |
| Lemma 6.3 and Corollary 6.4, p. 14 | Bounded-combinatorics newborn vertical weight and loss. The §6 accounting is a useful comparison: two-to-one gives one half of an input packet, not a window multiplier. |
| §7.1 P1, P2, Translation Property, (7.1), p. 15 | For sufficiently large p relative to fixed N,L, L disjoint translation domains Ω_l, each with 2N+1 sites. Local comparability and concentration on short horizontal arcs; series estimate for width in a window. Uses 4.2 and §5 conclusions. |
| Theorem 7.1, p. 16 | For any λ>1, sufficiently large local-width threshold and sufficiently large p (depending on chosen N,L,λ), W^ver ≥ λ W_loc. Quantifiers are crucial. Proof by contradiction: find definite vertical mass in suitable pullbacks of many disjoint windows. |
| Lemma 7.2, p. 16 | Reduction: for each Ω_l a site K_s within κN of its center and n≤3p with W((f^n)*Ω_l minus K_{s−n})≥δ W_loc; local degree ≤8, total ≤8^N and immersed buffer in the target. The covering estimate and (7.1) yield a nonperipheral site of vertical weight ≥c W_loc/N. Disjoint windows and L≥2λN/c force amplification. This is a conditional reduction, not yet a proof that the vertical mass exists. |
| Lemma 7.3, p. 17 | If Ω_l lacks definite vertical weight, (7.1) and Covering Lemma control the width of Ω_l minus K_l and of pullbacks: ≤C W_loc/√N, assuming W_loc large. Thus almost all relevant local weight is confined to O(N) horizontal arcs in a specified pullback. |
| §7.5 (7.2)–(7.6), pp. 17–18 | Fast pull-off + confinement + newborn horizontal bound + total loss. The disputed step is (7.5); both final cases require order N·W_loc loss. Lemma 7.2 then closes 7.1 if this loss creates the requisite vertical mass. |
| §8, pp. 18–19 | Authors assert unbranched a priori bounds and invoke Hu–Jiang/Jiang for JLC, and outline MLC by uniform qc Thurston equivalences. See §5 below for limitations. |

The geometric definitions and transformation rules preceding §4 are inputs, not consequences of the combinatorics. The table is a proof-roadmap audit of the numbered interfaces and the two paths (§6 bounded and §7 large period), not a fresh proof of §3–6. In particular it does not establish the proper-domain embeddings needed for all uses of the covering estimates.

## 3. Selected estimate: why (7.5) is load-bearing

Fix N, M=2N+1 and a window Ω_l as in §7.1; I_l=[l−N,l+N] modulo p. The weights W_n^K of §5.0.1 are widths at K_n in the punctured ambient domain U minus the union of the little filled Julia sets; local weights in 6.3 instead refer to U^p minus that union. A width in a restricted window is not automatically the same as the global local weight. In §7.5 the starred pullbacks are of the centered window from §7.1, with Ω′ from §4.0.3; the latter lemma explicitly retains the inner sites only, with boundary losses of order b. Use the notation of §7.5: Ω' is the returned/pulled-back window from §4.0.3; V=(f^{l+p})*Ω contains K_0. The sums refer to pull-off events in the successive window pullbacks; ν_n measures the total horizontal weight removed from the (n−1)-st window at its next pullback, and η_n is the part of W_0 used for newborn horizontal arcs.

The paper's preceding displays are

    newborn horizontal weight ≤ (2ν_n+η_n)/4 + O(N),             (7.2)
    loss ≥ ν_n/2 − η_n/4 − O(N),                               (7.3)
    Σ η_n ≤ M W_1.                                              (7.4)

Equation (7.5) is the only lower bound in these three lines of accounting with a factor M. Conditional on the stated error bounds and a consistent identification of the index sets, summation gives

    total loss ≥ M[(1−ε)W_0−W_1]/4 − O(N²),                    (7.6)

which has positive order N·W_loc when W_0 exceeds W_1 by a definite fraction of W_loc and W_loc is sufficiently large for fixed N. In the near-equal case the printed proof replaces (7.2) by ε' W_loc+ν_n/2, so the loss bound is Σν_n/2−M ε' W_loc; again the M factor in (7.5) is needed. A mere W_0/2 lower bound for the whole sum cannot support either conclusion for large N. This algebra is conditional on the other inequalities, and does not independently validate (7.2), (7.4), or the replacement estimate.

### Line-by-line check, §7.5 pp. 17–18

| Printed step (in order; paraphrased except indicated) | Audit against definitions / preceding results |
|---|---|
| Non-amplification; select window and V containing K_0; apply 6.1 in adapted setting. | Plausible reduction via §7.3–7.4. 6.1 is a statement about separating curves, not about the number of arc occurrences. Adaptation to all pulled-back pseudo-domains is assumed here, not independently established. |
| Every horizontal α beginning on K_l pulls off within p iterations, citing 6.2. | 6.2 in §6 is fast pull-off in the bounded-combinatorics argument. Its first part uses the no-periodic-horizontal-arc principle (Pilgrim; K Lemma 4.7), then the two separating curves and the periodic orbit labels. The source explicitly derives equality of widths under the covering and nondecrease under the immersion into U (EE 3.12(iii)). Even granting its adapted version, it gives existence of a first bad step for each α, not many distinct bad steps for one α. |
| By 4.3, the event n(α) belongs to I_l. | 4.3 provides the restriction to the indices where a connection can pull off (central/near-critical region), provided the arc is retained in the relevant translation domains. Specifically 4.3 assumes (f^n)*Ω omits K_1 and the endpoints are at combinatorial distance at most N−b from the stated base K_{l−N}. Its proof uses 4.2 and univalence on the window. This restricts the support of a count; it is not a lower bound for the mass assigned to every index. |
| Essential arcs, ξ=ε/(3d), carry at least (1−ε) W_l. | Degree/valence bound d and thin/thick bookkeeping from §3. The essential-width statement for a given K_l is not an assertion of M independently countable families. §7.4 localizes width in a pullback; relating that localization for every start site to the particular V used in the next paragraph requires tracking the restriction. |
| Define ν_n and η_n; estimate newborn weight and loss. | (7.3) follows from (7.2) by subtraction at the level of the stated weights. Treat the birth and η estimates as interfaces, not as established inequalities of arbitrary curve families. |
| Sum η_n using at most M contributing windows and bound by M W_1. | This is the asserted upper multiplicity bound (7.4). Upper multiplicity is not lower multiplicity. |
| Define K_m in V and A_0, horizontal arcs beginning on K_0 fitting in V. Again 4.3 puts n(β) in I. | Need the essential packet's weight in this precise V (not just the earlier confined pullback). Even granting the full weight W_0, membership of n(β) in an eligible index set is only a support constraint. Distinguish I_l, I in V and I_0 as printed: no silent identification of them with one another or with indices of all L windows. |
| The correspondence β ↦ (f^{n(β)−1})*β is at most two-to-one; total weight of terminal arcs ≥ W_0/2. | A single-packet estimate follows if the source packet has that width, each terminal arc has at least its source weight under the proper pullback/immersion comparisons of 3.12, and duplicates are counted at most twice. For essential mass only the analogous bound is (1−ε)W_0/2. This is a *conditional* verification of the counting inference; degree two by itself is not a proof of every pseudo-domain identification. See K, Lemmas 2.5, 2.6, 2.10, below. |
| Each terminal arc “fits into one of the 2N+1 domains” (p. 18); (7.5) is concluded. | **Unresolved step.** Existence of an eligible window for each terminal arc and a two-to-one map of a single packet imply a lower bound on a union/total once. They do not, as stated, give M copies of the packet or lower bounds on the sum of M different event weights. If the paper intends all translates of A_0 and a two-to-one correspondence on the disjoint union of those translates, it needs that stronger statement with domain containment, transported weights and multiplicity across the translates. I cannot verify that statement from 4.2–4.3, 6.1–6.2, 7.3, or the printed paragraph. I also cannot rule it out in an actual EE map. |
| Sum and split cases. | Conditional algebra above. No independent path to the order-N loss was identified in the selected argument. |

The p. 14 bounded argument provides an internal comparison: fast pull-off and the two-to-one correspondence are used to lower-bound total pulled-off weight by half of a packet. In §7.5 the window membership sentence is new; it is exactly the passage from a single packet to an M-scaled packet that needs verification. There may be an implicit shift/index construction, but it must preserve width and count terminal arcs in the correct summands, not merely produce multiple names for one curve.

### Precise sufficient interface; not a repair claim

Let P_m be tagged initial essential packets, one for each of M sites. Suppose (A) each has weight ≥(1−ε)W_0 (or the sum of initial weights has this M-scaled lower bound); (B) each source occurrence has an eligible terminal occurrence (tagged by the actual pull-off step and a canonical horizontal arc of that step's window); (C) its weight does not decrease; (D) every terminal occurrence is hit at most twice in the *whole disjoint union* of initial packets; and (E) the terminal occurrence weights, counted once per actual event, are included in Σ_{n∈I_l}ν_n. Then summing (C), using (D), gives (7.5). An averaged version of (A) with definite positive fraction would suffice for order-N loss with adjusted constants.

This is an explicit target for a geometric repair, not an asserted consequence of the published hypotheses. In particular, local comparability P1 or repeating the one-packet proof M times without (D)–(E) is insufficient. Nor does an arc belonging to several geometric windows automatically mean its width appears in several distinct ν_n.

### Incidence diagnostic (not a dynamical counterexample)

In an abstract incidence model, two tagged source arcs each of weight W_0/2 map to one terminal occurrence of weight W_0/2. The occurrence lies in an eligible domain, and has exactly two preimages. Assign it to one of M eligible event rows, all other rows zero. Total pulled-off weight W_0/2 satisfies the single-packet count and the membership condition, yet is less than M(1−ε)W_0/2 for M≥5 and ε=1/10. This verifies the logical distinction between these two *explicit counting premises* and the asserted conclusion. It does not model the conformal surface, covering, canonical lamination, actual f, or E1–E3. In particular zero rows are not claimed realizable. No actual counterexample; hence BOUNDED NEGATIVE, not GAP.

## 4. Primary-source cross-checks

The following source texts were opened; locators refer to their own printed pages.

* [K] J. Kahn, *A priori bounds ... I. Bounded primitive combinatorics*, [arXiv:math/0609045v3](https://arxiv.org/pdf/math/0609045v3) (matching v3 header on rendered PDF). Lemma 2.5, p. 14, compares weighted arc diagrams under covering pullback; Lemma 2.6, p. 14, compares diagrams under homotopic embeddings with compatible ends; Lemma 2.10, pp. 16–17, gives a domination/weight control for the arc comparisons. Lemmas 4.5, 4.7, p. 25, are in the superstable model: contraction of lengths of lifted paths for the Poincaré metric of the complement of the critical orbit, hence no periodic horizontal arc. The proof of 4.7 is actually supplied in K, from 4.5; it is the named Pilgrim interface used in EE 6.2. None of these statements gives the tagged M-packet multiplicity (A)–(E) in EE. The proof of K's 4.7 refers to Pilgrim's thesis theorem 5.8; I could not obtain that thesis text and do not import the theorem. I use K only to check the stated comparison interface, not to extend its model by analogy.
* [KL1] J. Kahn & M. Lyubich, *Quasi-Additivity Law in Conformal Geometry*, [arXiv:math/0505191v2](https://arxiv.org/pdf/math/0505191v2) (v2, rendered PDF). Covering Lemma, pp. 31–32: finite-degree holomorphic map of the nested domains, proper restriction of specified local degree, and a target collar with the specified modulus relation (or the small-modulus alternative); the width form, when the relevant width is sufficiently large, bounds source width by 2η⁻¹d² times target width. EE invokes a covering estimate in 7.2 and 7.3. This estimate compares conformal widths after the collar hypotheses have been checked; it does not count initial or terminal packets. No use of it to justify (7.5)'s factor M was found. I have not independently verified all collar hypotheses of EE's applications.
* [L1] M. Lyubich, *Dynamics of quadratic polynomials, I–II*, [Acta Math. 178 (1997), pp. 185–297](https://commack.math.stonybrook.edu/~mlyubich/papers/acta.pdf), §9.2 and Theorem VI, p. 250 (journal numbering; secondary limbs plus a priori bounds); §11 and §7.5 cited by EE §8 for the qc construction. This is downstream, not an input to (7.5). The extra uniform ray-configuration control for unbounded elephant eyes cannot simply be read off from a theorem assuming secondary limbs.
* [L2] Lyubich's [book manuscript](https://www.math.stonybrook.edu/~mlyubich/book.pdf), §24.4, Lemma 24.8 pp. 335–336 (rotation of ray portraits), Lemmas 24.10–24.11 pp. 337–338 (univalent maps on noncritical sectors and degree two on the central strip), §28.4.1–2 p. 391 (definition and primitive/satellite distinction), Lemma 28.20 pp. 391–392 (DH pre-renormalization under its ray assumptions). These are context for EE §4; none proves (7.5). Rendered text was opened; page-image retrieval failed because the PDF exceeded the web renderer's size limit. Mutable URL; byte-lock separately by CI. No extension of the polynomial statements to pseudo-QL maps inferred from this book.
* EE (7.5) itself explicitly cites 4.3, not an external theorem for the extra M factor. The internal citations above, and K/KL1, were checked against the original sources; no external theorem is invoked from memory. Other references in the bibliography are not thereby audited.

## 5. Downstream boundaries

K, Theorem 7.13, p. 45, identifies the canonical renormalization diagram with the appropriate subdiagram of the original map; Theorem 7.3, p. 37, supplies a restriction/width-to-modulus interface. K's bounded primitive iteration, Lemmas 8.4, 8.5, pp. 48–49, and 8.8–8.9, p. 50, uses its own hypotheses. These are relevant analogues, not automatic EE conclusions. Conditional on the identification of the renormalization local width with the child outer width, closure under iteration, and uniform thresholds, Theorem 7.1 implies a recurrence of the form W_child≤max(T,W_parent/λ) at large-period levels; that is how a large-width contradiction can produce uniform positive modulus. Bounded-period interleavings and ordinary unbranched annuli require their own uniform interfaces. EE does not present a separately numbered infinite-tower theorem and a detailed iteration proof between 7.5 and 8. I did not independently establish that bridge.

EE §8 p. 18 says the bounds are unbranched and cites [HJ], [J], [McM], [L1 §9.2] for JLC. Its MLC outline, pp. 18–19, is a qc-equivalence construction: (0) uniform exterior conjugacy; (1) uniform ray-configuration adjustment using little Mandelbrot copies on Ecalle–Voronin cylinders; (2) puzzle-based equivariance on top-level little sets; (3) restore initial dilatation near the little sets and iterate without loss. [C] and [DLP] are cited in step 1, alongside [D1], [La] for parabolic limits. The Jan 2026 footnote explicitly describes the DLP/Kapiamba project as forthcoming. I did not locate a completed version supplying that uniform estimate; those citations and HJ/J/McM are recorded as unverified downstream obligations, not results imported into the selected proof. Even proving (7.5) would not independently certify §8.

**Not established:** falsehood of (7.5) for a realized map; truth or falsehood of the other estimates, uniform a priori bounds, unbranchedness, JLC or MLC; completeness of the auxiliary lemma proofs; an erratum-level repair; a new ledger gate or atlas status; independent human verification. In particular the #131 exclusion of a shared point supplies no quantitative packet multiplicity. No work in the local_dilatation thread.

## 6. Inputs, hashes, reproduction and status

Sources are listed in sources.lock.json. EE v1: 398123 bytes, SHA-256 5eb36430a51a3fb6a1c04db15713aebc86068118450893ba2042021e4a8db725 (also the merged #131 lock). K v3: 888490 bytes, SHA-256 46e7ff4d5cc8ea190e439f45b2e4ed7308c1cf588a666daa5150eeb0b435c9c0. L1: 6177728 bytes, SHA-256 a286b6d3c874c803c1d56a669b5850e79c903190534aeab4840664b8e631bf16. K and L1 comparison digests from merged atlas source lock; the new read-only verifier checks them independently by download. KL1 v2: 359892 bytes, SHA-256 e9339d5461c25226acd46043783f508f672853c277e7e75b06a9583ef7b58c37 (measured in PR check run 45778160390, job 139766808576). L2 contextual PDF hash pending next CI download; explicitly not locked yet. Rendered PDFs and HTML were used for reading; byte identity is checked separately, not assumed solely from the rendering. Unverified downstream bibliographical entries are not proof inputs or byte-locked.

From repo root (Python 3.12):

    python -m pip install pypdf==5.4.0
    python -B research/frontier/elephant_eyes_core_20261126/verify.py --offline
    python -B research/frontier/elephant_eyes_core_20261126/verify.py
    python -B code/verify_physical_bridges.py

The offline diagnostic checks exact rational arithmetic and the abstract incidence example; the online run additionally downloads PDF bytes, checks locked sources and EE page locators, and prints SHA-256. Network failure is a CI failure, not a mathematical conclusion. No CI commit-back. Registration METADATA only.

**Status: OPEN / BOUNDED NEGATIVE (source-level audit of one estimate).** AI-assisted source reading, logical analysis and reproducibility code; not independently human-reviewed. Await separate PR reviewer.
