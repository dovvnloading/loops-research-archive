# Literal KKL (6.25): covering-only obstruction and open native question

**Claim / verdict — OPEN — covering-only obstruction (inclusion-maximal reading; native applicability unproved).** The independently reviewable result is a counterexample to the following restricted inference: for a marked wave in a degree-two annular cover, existence of an admissible source subwave with bounded discarded source width does not imply bounded discarded source width for every inclusion-maximal source subwave whose image is a wave ending at a designated target multi-interval. This is the same inclusion-order predicate on source subfamilies as the literal reading of KKL's selection, but in a strictly larger, covering-only class. It is not a counterexample to native (6.25), not an obstruction proved for the actual filtered restrictions of KKL, and not a refutation of width-maximal selection. Neither (M), (B), nor (E) below is established in the native setting.

**Limits.** The model below is a counterexample to the covering-level maximality inference, not to KKL 6.24, not to DL 5.2, and not to a claimed realization of a parabolically bounded quadratic-like map. The actual F, Hubbard-tree markings, filtered restrictions and N-step unbreakability are not realized. We do not establish (6.26), (6.27), (6.29), (6.25), (6.30), Lemma 6.31, (6.34), Proposition 6.23, or the correctness or falsity of KKL's main theorem. No alternative complete proof is claimed. No archive-internal mathematical theorem, lemma, or ledger status is a premise. The previous audit provided the initial hash expectations only; its mathematical conclusions are not premises. The mathematical argument below is derived from the versioned primary sources and elementary conformal geometry; the verification is a finite arithmetic/source diagnostic, not mathematical proof verification.

## 1. Inputs and source locators

All pages are one-based PDF pages, equal to the printed page numbers here. Exact versions, not unversioned latest PDFs:

| Primary source | SHA-256 of PDF (expected; verified by isolated workflow) | Relevant locators |
| --- | --- | --- |
| Kahn–Kapiamba–Lyubich, [MLC for parabolically bounded primitive renormalization, arXiv:2606.27272v1](https://arxiv.org/pdf/2606.27272v1), 73 pp. | 4c08805384b473dc0e55d76491c52c9fbe7c027e6da301f2c365a170ed7d9140 | §3.1 p. 19 (parabolic bound); §3.2 Thm D and Thm 3.6 pp. 20–21; §6 pp. 39–51; Prop. 6.23 and Lemma 6.24 pp. 49–50; Lemma 6.31 and (6.32)–(6.34) pp. 50–51; §A.1 pp. 56–57; Lemmas A.10/A.11 p. 62, A.12 p. 63, A.13 p. 64, A.14/A.15 p. 65. |
| Dudko–Lyubich, [MLC at Feigenbaum points, arXiv:2309.02107v3](https://arxiv.org/pdf/2309.02107v3), 41 pp. (KKL's DL23b, bibliography p. 72) | e88462e43b3c172cf309d5b3d38caa21ee8f43876bac1e07cce84b309dfb8c6b | §5, definition of wave above a side and Lemma 5.2 pp. 34–35; proof of Lemma 5.2 in particular p. 35. |

The reviewer checked the versioned PDF page images directly. The expected hashes came from the previous audit; the committed source_lock.json and successful isolated workflow output reproduce them. The verifier downloads the PDFs (or reads the specified cache), checks digest, page count and selected normalized text anchors, and writes the lock. A locator is not a mathematical hypothesis check. KKL A.13 p. 64 correctly cites DL23b Lemma 5.2; DL23a is a different work (KKL p. 72). We compare statements, not assume that one proves the other.

## 2. Quantifiers and exact missing bound

KKL p. 49, Proposition 6.23 proof, defines the selection as “the maximal subwave so that $F_*^n A_n$ is a wave ending at $\mathbf{L}_0$”. Lemma 6.24, equation (6.25), asserts $\mathcal W(A_n\setminus A_{n+1})=O(1)$ for $0\le n<N-1$. Equation (6.28), p. 50, instead compares widths: $\mathcal W(A_{n+1})\ge\mathcal W(A'_{n+1})$. The word maximal is not qualified there; the latter inequality suggests a width-maximizing intention, not a consequence of inclusion-maximality alone. This note tests only the inclusion-maximal reading, not the authors' intent.

Fix the native setting of KKL §6 and §6.2: a periodically repelling primitively renormalizable psi-quadratic-like relation, a fixed parabolic bound b (rotation 1/q, at most b components in each limb and the critical-limb image condition of §3.1, p. 19), the marked complement of its Hubbard tree, and a wave A ending at the critical block L_0. As in KKL Prop. 6.23, put N=b+3 and A_0=A^(N-ubr) minus A^sh. Here unbreakability is the singleton successor condition at each step (definition at the end of p. 44 and beginning of p. 45); short is defined on p. 40 by absence of a limb in the crest of any leaf. Constants may depend on b, not q or analytic widths (§3.2 p. 20 and §6 p. 39). For 0<=n<=N-2 let A_n be a choice at the stated previous stage and M=A_(n+1) an arbitrary inclusion-maximal subwave (if such a choice exists) for which the (n+1)-step image is a wave ending at L_0.

Write phi_j(a)=F_*^j(a) as a single untagged path, defined for each original leaf under consideration. Let psi=phi_(n+1) restricted to A_n, T=psi(A_n) (possibly not a lamination) and C=psi(M). Because a subfamily of a wave is subordinate to the same base, adding a single omitted parent with successor already in C changes neither the image nor its ending property. Under literal inclusion-maximality, interpreting waves and subwaves as hereditary families of leaves (KKL A.1, p. 57; no extra closedness or regularity requirement), M=psi^{-1}(C) inside A_n. This is a set statement, not a multiplicity statement. For output paths t in T define:

* I = paths whose singleton is not a wave ending at L_0 (includes non-simple and wrong-ending paths).
* K_C = paths t outside C for which {t} is a wave ending at L_0 but C union {t} is not such a wave.

Every t outside C lies in exactly one of I or K_C: otherwise a parent could be added. Thus

    D=A_n \ M = D_I union D_K,
    D_I = psi^{-1}(I),  D_K = psi^{-1}(K_C),  (preimages inside A_n).

The exact required relative bound, in parent width, is

    (M) sup over admissible native (F,A,n,M) with fixed b
        [ W(D_I) + W(D_K) ] < infinity.

By monotonicity and finite subadditivity this is equivalent to uniform (6.25), up to a factor two. It separates endpoint/simplicity failures from incompatibility. Even granting a uniform bound for D_I, the exact remaining necessary and sufficient estimate is

    (B) W(psi^{-1}(K_C)) <= C_b    for EVERY maximal C.

A conditional sufficient output-side target, not asserted as equivalent, is W(I)+W(K_C)<=C_b, with width taken for actual path families even if not laminations. For clarity, if the filtered restriction family of each intermediate subfamily meets A.11's lamination hypothesis, the following elementary degree accounting explains this target. Given any family E of outputs, the full degree-two cover lifts have width at most 2 W(E): pull back any admissible metric, whose area is doubled and whose lifted lengths are unchanged. For each intermediate family D_j=phi_j(D) with j<=n, every parent has at least one retained proper occurrence in the filtered restriction of D_j, by the singleton-successor definition and the two filters in KKL A.3.2 p. 63. If these occurrences form a lamination as in A.11 (p. 62), domination gives W(D_j)<=W(retained restrictions)<=2 W(D_(j+1)). Iterating gives W(D)<=2^(n+1) W(psi(D)). This reasoning is only a sufficient reduction under the stated A.11 hypothesis; it does not establish that hypothesis for arbitrary nonembedded filtered occurrences. It is not coefficient-one subtraction and it never counts distinct outputs as distinct sheets. The exact parent-width formulation (M) needs no such analytic reduction.

The printed proof has three distinct problems:

1. KKL A.13 p. 64 is an ending-at assertion; DL 5.2 pp. 34–35 assumes a degree-m cover of closed annuli and a single boundary interval on the bounded side of every input leaf, disjoint from its endpoints. For the (6.26) invocation the actual input is the filtered restriction, not S_n. Neither the ending block nor the fact that the output is a singleton certifies that common interval. Further, A.13 also does not itself assert that the extracted wave has no short leaves. KKL's A.14 (p. 65) is typed for laminations and a crest hypothesis; it is not an extraction or a relative-loss estimate. The paragraph around (6.19) in the proof of Prop. 6.10 asserts a wave over the pulled-back crest for a particular unbreakable portion, but does not by itself prove a common nonempty interval for arbitrary centrally-ending S_n. We do not substitute Prop. 6.21's proof, which itself invokes A.13. Prop. 6.22 (p. 49) invokes A.15 only for localized waves away from the critical block; its hypothesis does not cover K_C.
2. DL 5.2 states retained width of a genuine subwave, not a general relative complement bound or a comparison for an independently chosen maximal wave. Its proof uses discarded outermost layers, with a shift argument; no use is made here of an unproved quantitative Borel relative-discard extension. Subadditivity W(U union V)<=W(U)+W(V) alone gives a lower, not upper, bound on W(V) by subtracting W(U). This does not rule out additivity for suitable disjoint measurable sublaminations; any such argument must identify the parent families and justify its applicability. In (6.29) p. 50 the printed right side uses S_(n+1), while the extraction at (6.26) was from F_*S_n; the primed preimage in the sentence before (6.28) also has an unprimed index in the displayed equality. Even correcting these labels does not give the required inequality for the lost parents.
3. Inclusion-maximality does not order widths of incomparable choices. A width-maximizing selection is a different reading: if parent widths are additive for the relevant partition, a sufficiently large retained parent width would control discarded width. The covering example does not refute that reading. A bounded-discard existential packet P is insufficient for (B) unless one proves that its omitted portion cannot be blocked by M at large width. The annular example below isolates this last failure even when the existential extraction loses bounded actual width.

## 3. Explicit covering-only obstruction (proved elementary model)

Use the closed flat cylinders X=(R/2Z) x [0,1] and Y=(R/Z) x [0,1], with complex coordinate x+iy. The map f:X->Y, (x,y)->(x mod 1,y), is a holomorphic degree-two covering in the interiors and a degree-two covering of the closed annuli. All curves below are semicircles in y>=0, with their diameter on the lower boundary. Let R=1/5, c=1/2, d=67/40, t=7/40, k>=2, epsilon=R*2^(-k), delta=epsilon/4.

* P: all upper semicircles centered at c with radii r in [epsilon,R].
* Q: all upper semicircles centered at d with radii s in [t-delta,t+delta].

The source supports are disjoint: P has x in [3/10,7/10], while Q has x in [3/2-delta,37/20+delta], strictly within (1,2). Their heights are <1, and all endpoints lie on y=0. Each packet is a continuous annular-sector foliation by disjoint embedded proper arcs. Their union is a disjoint lamination on X subordinate to the lower boundary (even to a proper arc containing both support intervals). Each packet maps injectively to Y: its horizontal support lies strictly in a fundamental strip of width one. Thus every leaf's image is a single embedded proper arc. The packets are not above a common source interval: their bounded-side boundary arcs are disjoint.

For an explicit target marking, cut the bottom circle at 0, 1/4, 1/2+epsilon/2, 1/2+3epsilon/4, 3/4, 4/5, 9/10; use the complementary open intervals, and mark the entire upper boundary. Let L=(1/4,1/2+epsilon/2) be the designated target ending interval (not a dynamical limb). Each P-image has left endpoint in L, right endpoint in (1/2+3epsilon/4,3/4); each Q-image has left endpoint in L, right endpoint in (4/5,9/10). Their bounded-side intervals contain the open marked interval J=(1/2+epsilon/2,1/2+3epsilon/4). This verifies the target marking using KKL A.1 pp. 56–57. Each path is subordinate to a multi-interval of length at least three, not to one of length at most two: the bounded-side route traverses the entire J, and in the complementary direction the path is not homotopic rel endpoints to a boundary arc (and that route also traverses at least one intermediate marked interval). Thus each packet image separately is a marked wave ending at L and above J. Use the pulled-back marking on X. Each source leaf crosses a whole lift of J on its bounded-side boundary arc, hence meets the marked-path definition. The source base can be taken as the proper multi-interval (1/4,19/10), since both supports lie strictly inside it and each semicircle deforms rel endpoints into its diameter. The connected source ending multi-interval E_s=(c+epsilon/2,1+c+3epsilon/4) contains precisely the right endpoint of each P leaf and the left endpoint of each Q leaf, not their other endpoints. Its length is 1+epsilon/4, so f(E_s) is the entire target bottom circle. This is analogous only to the boundary-image identity F_* L_0=partial_C T in KKL p. 43 (after Prop. 6.6); it is not a realization of the same L_0 under an actual immersion. In particular the chosen P source endpoint maps outside L. E_s and L are distinct artificial multi-intervals; no native nonshortness or source-to-target endpoint correspondence is claimed.

For every pair r,s, the endpoints in Y interlace:

    c-r < (d-1)-s < c+r < (d-1)+s.

Indeed (d-1)-s belongs to [c-delta,c+delta], strictly between c-epsilon and c+epsilon. The last endpoint is at least 17/20-delta>c+R. Two upper semicircles with strictly interlaced diameter endpoints intersect in the open half-plane: their center distance is strictly between the absolute difference and sum of their radii, so their circles meet in two reflected points, one above y=0. Consequently no projected P leaf can be added to the image of Q, and conversely. P and Q are each inclusion-maximal subfamilies of P union Q whose image is a wave ending at L. Both have positive width. This obstruction is not a failure of leafwise injectivity, not a multiplicity collision, and not a set-versus-occurrence confusion.

For completeness compute widths directly from the extremal-metric definition (width = modulus of the path family). On an upper half-annular sector of radii a<=u<=b the admissibility condition for the semicircle of radius u is integral_0^pi rho(u,theta) u dtheta >=1. Cauchy–Schwarz implies integral_0^pi rho(u,theta)^2 u dtheta >=1/(pi*u). Integrating in u gives the lower bound log(b/a)/pi for area; rho=1/(pi*u) on the sector and zero elsewhere attains it. Boundary choices of density do not affect area. Because the source supports are disjoint, the same proof and the sum of the two extremal metrics give exact additivity in THIS model:

    W(P) = k log(2)/pi,
    W(Q) = log((t+delta)/(t-delta))/pi,
    W(P union Q) = W(P)+W(Q).

The covering is an isometry on each packet, hence W(f(P))=W(P) and W(f(Q))=W(Q). As k grows, W(P) tends to infinity and W(Q) tends to zero; for k>=2, delta<=1/80 so W(Q)<=log(15/13)/pi. The existential choice P therefore satisfies even the relative discard bound W((P union Q)\P)<=log(15/13)/pi. But the inclusion-maximal choice Q has loss W((P union Q)\Q)=k log(2)/pi, unbounded. In this model all successors are eligible, I is empty, and the blocked term is the entire loss. The maximum-width admissible choice in this particular example is P: W(P)>W(Q) since 2^k>=4>15/13, and a nonempty admissible family cannot mix packets. Thus the model refutes precisely the generic inference for inclusion-maximal choices, not the width-maximizing interpretation suggested by (6.28). It does NOT disprove DL Lemma 5.2 (pp. 34–35): the whole source has no common interval on the bounded side of every leaf, and each individual packet has an injective image anyway. Whether the actual native filtered restrictions admit this kind of incompatible pair (or instead possess extra compatibility/common-interval structure) is unproved.

## 4. Native hypothesis checklist and failed proof route

| KKL requirement | Cover model / status |
| --- | --- |
| Degree-two cover of annular complements | Yes, explicit holomorphic unbranched annulus cover, but no native branched extension or relation certified. |
| Wave in the marked complement, actual central limb ending | Artificial marked wave and source/target ending blocks only; not the same native L_0 or a Hubbard-tree marking. In particular, E_s projects onto the bottom boundary, but the endpoint correspondence of the native restriction is not checked. |
| Periodically repelling primitively renormalizable psi-ql F (§2.4–2.5) | Not supplied. |
| Parabolic b-bound, 1/q rotation, critical limb image and bounded components (§3.1) | Not supplied; k is a width parameter, not b or q. |
| Restriction by the actual immersion with both A.3.2 filters (p. 63) | Not supplied. No identification of the cover input with a filtered restriction of A_n. |
| A_0=A^(N-ubr)\A^sh, N=b+3; earlier central-ending waves for n>0 | Not supplied; no iteration of F, only a single cover, and no dynamical short/long classification. |
| Every selected parent has a singleton successor at every required step | Verified only for the single covering operation, not the native iterated relation. |
| Inclusion-maximal admissible choice and unbounded relative loss | Yes in the cover model, not in the native problem. |

In particular one cannot transplant the second packet into the native central-ending, nonshort, N-unbreakable class without proving its realization and disjointness properties under all the marked dynamics. A possible positive approach is to derive from the native restrictions a no-blocking (or bounded-blocking) estimate (B). The disjoint-cover model rules out relying only on degree, the abstract ending predicate and existence of a bounded-discard choice in this broader class. It does not establish that native restrictions exhibit blocking, and it leaves open whether native structure rules out the example. The checked primary-source arguments did not furnish that structure; no assertion is made that no such theorem exists. A proof of (M) or a realized sequence violating it for fixed b would settle the requested literal question.

## 5. Different choice, downstream, and significance

At the level of (6.30) only, arbitrary maximality is unnecessary. The alternative exact existence target is

    (E) There exist nested subwaves B_0=A_0,...,B_(N-1)
        with F_*^j B_j a wave ending at L_0 and W(B_j\B_(j+1))<=C_b
        for 0<=j<N-1.

Finite subadditivity gives directly W(A^(N-ubr))<=W(A^sh)+W(B_(N-1))+(N-1)C_b. The telescope is elementary and works even if literal (6.25) is false. In the covering example selecting P rather than Q gives this one-step estimate. No native existence statement (E) is established by the example or by DL 5.2 alone. One must at least prove an existential **parent-relative** one-step discard bound for a chain with continued central ending and unbreakability, not just a large retained image. The printed proof of Lemma 6.31 (p. 50) discusses central-ending leaves and alignment, without an explicit appeal to maximality; we do not certify that the lemma or its subsequent width bounds survive replacing the sequence. Proposition 6.23 also needs (6.34), not just the telescope; it therefore is not proved here even for a differently chosen sequence.

**Significance:** The printed proof uses (6.25) to get (6.30), then combines (6.30) and (6.34) in Proposition 6.23 (pp. 49–51). Proposition 6.20 (pp. 48, 51) uses 6.23, and the printed route continues via Proposition 6.11 (pp. 45, 48), Proposition 6.2 (pp. 40, 45), Lemma 6.1 (pp. 39–41), Proposition 3.9 (pp. 21, 39–40), Theorem 3.6 (pp. 20–21) and Theorem D (p. 20). This is a proof-certification issue on the route to the main beau-bounds/rigidity conclusions (Theorems A and C, pp. 3–4), not evidence that those conclusions are false. The model alone does not establish a new gap in the native hypotheses; it only shows why inclusion-maximality alone cannot justify the comparison. No erratum-level repair is certified: (E) would suffice for the telescope but the remaining native estimates must also be justified.

## 6. Reproduce / scope of checks

From repository root, Python 3.12:

    p=research/frontier/kkl_6_25_literal_20261126
    python3.12 -m venv /tmp/kkl-625
    . /tmp/kkl-625/bin/activate
    python -m pip install --no-deps -r "$p/requirements.txt"
    python "$p/verify.py" --model-only
    python "$p/verify.py"
    git diff --exit-code -- "$p/source_lock.json"

Optional offline PDF cache: --cache /path/to/pdfs containing the versioned filenames. The exact rational checks test strict source disjointness, the endpoint/marking inequalities uniformly over each radius interval at k=2,...,128 (including source base and E_s), and the algebraic width-ratio bounds (no sampling of actual paths). The analytic proof is the argument in §3, not these finite tests. No downloaded copyrighted PDFs are committed. The source lock records versioned PDF checksums and page hits. CI uses pinned Python dependency and action SHAs, writes the generated lock back on the audit branch only, and checks exact reproduction on pull requests. No model-to-physical bridge, ledger status change, or archive proof contract is claimed; the verifier is registered as standalone METADATA. No other research thread is changed.

AI disclosure: the original author disclosed ChatGPT assistance in source comparison, proof search, construction and verifier authoring. A separate AI review narrowed the status, clarified the marked model and strengthened rational/source checks; no independent human or specialist peer verification is represented.
