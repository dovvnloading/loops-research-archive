# Width-maximal selection: a multiscale covering obstruction

**Claim — PROVED (covering-only counterexample); OPEN (native KKL).** For each integer \(k\ge1\) there is a fixed-degree-two holomorphic covering of closed annuli, with a fixed number of marked intervals, a source marked wave \(S\) ending at a connected block \(E\), and a designated target block \(L\), such that every leaf has an embedded, eligible image ending at \(L\), yet every admissible source subwave \(M\) (its untagged image must be a wave ending at \(L\)) has
\[
 \mathcal W(S)=2ka,\qquad
 \mathcal W(M)\le ka,\qquad
 \mathcal W(S\setminus M)\ge ka,\qquad a=\pi^{-1}\log(5/4)>0.
\]
The maximum \(ka\) is attained explicitly, with discard exactly \(ka\). Thus width-maximal selection, even with exact attainment, fails to guarantee bounded loss in the covering-only class; indeed no choice works there. This is alternative (b), not a counterexample to native Lemma 6.24 or Proposition 6.23.

**Limits.** No actual periodically repelling primitive pseudo-quadratic-like relation, parabolic \(b\)-bound, Hubbard tree, immersion restriction with the two filters, or \(N\)-step stationary sequence is realized. The source ending block \(E\) and target ending block \(L\) are artificial; they are not identified as the same native critical limb by an immersion. Neither a native width-maximizing rule nor its failure is established. The model deliberately does not have an existential bounded-discard candidate; it does not refute width maximization *given* such a candidate. It does not contradict DL Lemma 5.2. No native (6.25)–(6.30), Lemma 6.31, (6.34), Proposition 6.23, or main theorem proof or disproof is supplied. No archive lemma is used. The executable is evidence-not-proof: it checks exact arithmetic and source identity, not dynamical realization or analytic validity.

## 1. Inputs and locators

All pages below are one-based PDF pages (also printed page numbers). The primary sources were read in their versioned PDF page images; the PDF bytes cannot be downloaded in the local sandbox. The following expected SHA-256 digests are from the preceding source locks, to be independently checked by the workflow in this directory (no PDF is committed).

| Source | SHA-256 | Locators |
|---|---|---|
| Kahn–Kapiamba–Lyubich, [MLC for parabolically bounded primitive renormalization, arXiv:2606.27272v1](https://arxiv.org/pdf/2606.27272v1), 73 pp. | 4c08805384b473dc0e55d76491c52c9fbe7c027e6da301f2c365a170ed7d9140 | §3.1 p. 19, §6.1 pp. 42–45, Prop. 6.23 and Lemma 6.24 pp. 49–50, Lemma 6.31 and (6.32)–(6.34) pp. 50–51, §A.1 pp. 56–57, A.10/A.11 p. 62, A.3.2 p. 63, A.13 p. 64, A.14/A.15 p. 65, bibliography p. 72 |
| Dudko–Lyubich, [MLC at Feigenbaum points, arXiv:2309.02107v3](https://arxiv.org/pdf/2309.02107v3), 41 pp. | e88462e43b3c172cf309d5b3d38caa21ee8f43876bac1e07cce84b309dfb8c6b | §5 definition and Lemma 5.2 pp. 34–35 |

Bibliography clarification: KKL v1 PDF p. 64 calls the relevant source DL23b, identified on p. 72 as the Feigenbaum paper; DL23a there is the different 2023 GAFA satellite paper. The arXiv HTML labels differ. We use the versioned PDF and the specified Lemma 5.2, not the label alone. This work imports no non-elementary theorem as a premise. KKL §A.1 supplies the marked-path definitions; DL 5.2 is compared, not used to derive the model. The two preceding frontier notes were read for scope only, not invoked as mathematical lemmas.

## 2. Exact covering-level question

KKL Prop. 6.23 p. 49 fixes \(N=b+3\) and \(A_0=A^{N\text{-ubr}}\setminus A^{\rm sh}\). The proposed width-maximal replacement of the induction chooses \(A_{n+1}\subset A_n\) maximizing parent width under the condition that \(F_*^{n+1}A_{n+1}\) is a wave ending at \(\mathbf L_0\). For \(S_n=F_*^n A_n\) the printed proof obtains (6.26) by A.13 and then attempts to transfer the retained image width back to parent loss in (6.29). Even if a maximizer exists, its definition alone does not justify either estimate.

The restricted one-step question we refute is this: given a degree-two covering \(f:X\to Y\) of marked closed annuli, a marked source wave \(S\) ending at a connected multi-interval \(E\) of boundary degree at most two (even \(f(E)\) the full target boundary), and a target interval \(L\), suppose every singleton image is an embedded marked path ending at \(L\). Must there exist an admissible \(M\subset S\) with \(\mathcal W(S)-\mathcal W(M)=O(1)\), or with \(\mathcal W(S\setminus M)=O(1)\), by maximizing source width? Here the constant must be independent of widths and geometric scales with degree and number of marked intervals fixed. Admissibility requires the actual images, not representatives of their homotopy classes, to form a lamination subordinate to a common base. This is strictly weaker in hypotheses than the native KKL relation, but retains the degree, marked ending, and singleton-cover requirements. Both proposed conclusions are false even when the image of every eligible subfamily lies over a common target interval. The model checks *all* hypotheses of this restricted claim below.

## 3. Construction

Use complex coordinates \(x+iy\) on the cylinders
\[
 X=(\mathbb R/2\mathbb Z)\times[0,1],\qquad
 Y=(\mathbb R/\mathbb Z)\times[0,1],\qquad f(x,y)=(x\bmod 1,y).
\]
The cylinder interiors are conformal annuli via exponentiation; the maps extend continuously to the displayed ideal boundaries, are unbranched degree-two covers there, and are local Euclidean isometries. Both annular conformal types are fixed as \(k\) varies.

Put \(c=1/2\), \(r_i=4^{-i}/10\) for \(0\le i<k\), \(\epsilon=r_{k-1}\), and \(h=5/4\). An upper semicircle of center \(d\) and radius \(u\) is the proper arc \(d+u e^{i\theta}\), \(0\le\theta\le\pi\), with endpoints on the lower boundary. In \(X\) take:
\[
 P_i=\{\text{semicircles centered at }c,\quad r_i\le u\le h r_i\},\qquad
 Q_i=\{\text{semicircles centered at }1+c+r_i/2,\quad r_i\le v\le h r_i\}.
\]
Write \(S=\bigcup_{i=0}^{k-1}(P_i\cup Q_i)\). Every packet is a compact continuously parametrized family of pairwise disjoint embedded arcs, with interiors in the annulus; all radii are strictly positive. Every \(P_i\) lies within the first fundamental strip \(0<x<1\); every \(Q_i\) within the second \(1<x<2\). Indeed the first packet's horizontal range is contained in \([3/8,5/8]\), the second in \([1+17/40,1+27/40]\), and maximum height is \(1/8<1\). Thus \(f\) is injective on each packet and on every leaf.

Mark the lower circle of \(Y\) at cuts \(0,1/4,c+\epsilon/2,c+3\epsilon/4,3/4\); the complementary open intervals are the marking; mark the upper boundary as one whole circle. Pull this marking back by \(f\) to \(X\). Write
\[
 L=(1/4,c+\epsilon/2),\quad J=(c+\epsilon/2,c+3\epsilon/4),
 \quad R=(c+3\epsilon/4,3/4).
\]
All projected left endpoints belong to \(L\): in a \(P_i\) they are \(c-u\), and in a \(Q_i\) they are \(c+r_i/2-v\le c-r_i/2\). All projected right endpoints belong to \(R\), since they are at least \(c+r_i\ge c+\epsilon\) and at most \(c+7r_i/4\le27/40<3/4\). Therefore every bounded-side boundary arc contains the whole marked interval \(J\), and its endpoints avoid \(J\). Each path is homotopic rel endpoints to its diameter within the closed half disk. It cannot be subordinate to a multi-interval of combinatorial length at most two: the marked endpoint intervals \(L,R\) have \(J\) between them in one direction and at least two other marked intervals in the other. The analogous statement in \(X\) holds with the corresponding lifts. This verifies the KKL §A.1 p. 57 marked-path requirement without any implicit replacement of paths by arcs.

All source leaves are subordinate to the proper multi-interval with endpoints \(1/4,1+3/4\) (the interior of the union of consecutive closed marking intervals); all target leaves are subordinate to \((1/4,3/4)\) in the same sense. Define the source ending multi-interval
\[
 E=(c+\epsilon/2,\ 1+c+3\epsilon/4).
\]
Every \(P_i\) has its right endpoint in \(E\) and its left outside; every \(Q_i\) has its left endpoint in \(E\) and its right outside. The image of \(E\) is the entire lower circle since its length is \(1+\epsilon/4\); the restriction has at most two preimages per point. The source and target blocks are not identified by native dynamics. The entire union \(S\) will be a wave once disjointness is checked; all eligible images then have target common crest \(J\) and end in \(L\).

### 3.1. Compatibility exactly at distinct scales

At the same scale \(r=r_i\), the projected \(P_i\) and \(Q_i\) endpoints strictly interlace for **every** \(u,v\in[r,5r/4]\):
\[
 c-u < c+r/2-v < c+u < c+r/2+v.
\]
Indeed the largest left \(P\)-endpoint is \(c-r<c-3r/4\), the smallest left \(Q\)-endpoint; the largest left \(Q\)-endpoint is \(c-r/2<c+r\); the largest right \(P\)-endpoint is \(c+5r/4<c+3r/2\), the smallest right \(Q\)-endpoint. Equivalently the center distance \(r/2\) satisfies \(|u-v|\le r/4<r/2<u+v\). The two circles meet at two reflected points; the upper one lies strictly in \(Y^\circ\). Thus no admissible family can contain even one leaf from each of \(P_i,Q_i\). Their images are distinct, so identifying coincident untagged paths cannot remove these intersections.

At distinct scales \(s<r\), \(s\le r/4\). The diameter interval of **every** smaller projected semicircle lies in \([c-5s/4,c+7s/4]\). The diameter interval of **every** larger projected semicircle contains \([c-r/2,c+r]\). Strict inclusion follows from
\[
 5s/4\le 5r/16<r/2,\qquad 7s/4\le 7r/16<r.
\]
For circles with centers on a line, strict inclusion of diameter intervals implies strict inclusion of the disks: the center distance plus the smaller radius is less than the larger radius. Consequently semicircles of different scales do not meet, including their endpoints. The full small half disk is inside the innermost half disk of each larger packet. This also proves that the half-annular sector supports for distinct scales of the same sheet in \(X\) are disjoint. Within each packet the leaves have different radii; between sheets all supports are disjoint. Hence \(S\) is a disjoint lamination and is a marked wave ending at \(E\), as asserted.

It follows that \(M\subset S\) is admissible if and only if for every \(i\) it meets at most one of \(P_i,Q_i\). Necessity is the actual crossing; sufficiency follows from different-scale nesting and same-packet disjointness, and the common target base and ending verified above. This equivalence holds for arbitrary subfamilies (in particular Borel or compact families). It does not rely on a choice of one lift for each untagged successor.

### 3.2. Exact extremal widths and attainment

Use the modulus definition of extremal width (the infimum of the area integral of the squared nonnegative admissible density, with line integral at least one on every leaf). On an upper half-annular sector with radii \([r,hr]\), any admissible density \(\rho\) satisfies, for each radius \(u\),
\[
 1\le \left(\int_0^\pi \rho(u,\theta)u\,d\theta\right)^2
 \le \pi u\int_0^\pi \rho(u,\theta)^2u\,d\theta.
\]
Integrating gives area at least \(\pi^{-1}\log h\); the density \(1/(\pi u)\) on that sector, zero elsewhere, attains equality. The boundary arcs of sectors cause no area contribution; assign the same density there for the end-radius semicircles. This proves every packet has width \(a=\log(5/4)/\pi\) directly, without using a general transverse-additivity assertion. For a union of any full packets in \(X\), the supports are pairwise disjoint, so integrating each lower bound over its own sector and summing the extremal densities proves exact width \(a\) times the number of packets. In particular \(\mathcal W(S)=2ka\).

Every admissible \(M\) is contained in a union of at most \(k\) full packets. Monotonicity gives \(\mathcal W(M)\le ka\). At each index at least one entire packet is omitted; the union of these \(k\) omitted packets lies in \(S\setminus M\), so \(\mathcal W(S\setminus M)\ge ka\). The explicit selection \(M_*=\bigcup_i P_i\) is admissible, attains the maximum \(ka\), and has complement \(\bigcup_i Q_i\) of width exactly \(ka\). No existence theorem for maxima is needed. Every width-maximizer has width deficit exactly \(ka\) and actual discard at least \(ka\); every other admissible choice has at least as large a deficit. Since \(k\) is arbitrary, both quantities are unbounded at fixed covering degree, fixed annulus moduli and fixed number of marked intervals. The projected full selected packets are also supported on disjoint sectors across scales, so their image width is exactly \(ka\). No image lamination, even without the target-ending restriction, can have width exceeding \(ka\), because the same-scale crossings prevent mixing. This also obstructs the covering-only extraction with additive loss as in broad A.13.

## 4. Hypothesis checks and precise negative boundary

| Condition | Verification |
|---|---|
| Holomorphic cover of closed annuli, degree two | Explicit quotient, local isometry; both boundaries covered twice. |
| Source marked wave, ending connected block of degree at most two | §3, §3.1; \(E\) proper, its image the full boundary, both packet types end there. |
| All singleton images eligible, proper, simple, ending at designated \(L\) | §3, endpoints in \(L,R\), genuine paths, f injective on each leaf. |
| Images of admissible subfamilies are waves | Exact compatibility characterization, common base and \(J\). |
| Exact width-maximizer and unbounded source loss | §3.2; attained for all \(k\), no approximation or regularity premise. |
| DL 5.2 common *source* interval | **Fails for \(S\)**: the bounded-side diameter arcs of a \(P\)-leaf and a \(Q\)-leaf are in different fundamental strips and disjoint. Each separate sheet packet union is above its respective lift of \(J\); it is already injectively mapped, so satisfies the conclusion with zero loss. The common target interval \(J\) cannot serve as a common source interval. No application of DL 5.2 is made to \(S\). |
| KKL primitive relation, parabolic combinatorics, marked Hubbard complement, filtered immersion, nonshort \(N\)-unbreakable parents | Not supplied. Only one covering step exists; no native \(b,q,N\) or same-critical-limb iteration is asserted. |

This is a multiscale obstruction rather than a comparison of two incomparable maximal choices with an already available low-loss candidate. Indeed if widths of subfamilies of a given wave are additive for the relevant partitions, and some admissible \(P\) has \(\mathcal W(S\setminus P)\le C\), a maximizer \(M\) necessarily satisfies \(\mathcal W(S\setminus M)=\mathcal W(S)-\mathcal W(M)\le\mathcal W(S)-\mathcal W(P)=\mathcal W(S\setminus P)\le C\). This elementary conditional observation is not refuted. Our construction instead shows that existence of the candidate is a substantive analytic/geometric hypothesis, even with singleton simplicity, fixed degree, and target common crest. No claim of arbitrary sublamination additivity is needed for our counterexample.

## 5. Native width-deficit formulation and downstream check (bounded negative result)

The exact one-step inequality needed for the width-maximal strategy at the level of the *consumed* (6.30) is weaker than (6.25). For each native admissible parent \(B=A_n\), put
\[
 H_{n+1}(B)=\sup\{\mathcal W(D):D\subset B,\ 
     F_*^{n+1}D\text{ is a wave ending at }\mathbf L_0\},
\]
allowing the empty family. For finite parent width (the meaningful near-degenerate finite-width setting), the missing uniform inequality is
\[
 \boxed{\quad \mathcal W(B)-H_{n+1}(B)\le C_b
       \quad(0\le n<N-1).\quad} \tag{W}
\]
It is sufficient to prove (W) for the constructed sequence, not every admissible parent. If (W) holds, take a subwave within 1 of the supremum at each step (no exact maximizer assumption), giving \(\mathcal W(A_n)\le\mathcal W(A_{n+1})+C_b+1\). Telescoping the scalar widths and using the elementary modulus subadditivity of \(A^{N\text{-ubr}}\subset A^{\rm sh}\cup A_0\) gives precisely the shape of (6.30), with fixed \(b\). No assertion of bounded relative discard, no subtracting a subadditive inequality, and no identification of image and parent widths is involved. More exactly, existence of a whole admissible chain with terminal width deficit bounded is the consumed requirement; the per-step uniform version (W) is sufficient, not necessary for every possible parent. The covering example has \(H_1(S)=ka\), so its one-step width deficit is \(ka\) and (W) is false in that larger class.

DL 5.2 pp. 34–35 supplies a retained-width bound for a common-interval covering packet. It cannot be applied to an arbitrary centrally-ending native filtered restriction merely from its ending condition. Even if applied to a directed packet, its retained width is measured on the cover, not on the parent \(B\). A proof of (W) requires a native compatibility/directional selection and a quantitative transfer back to parent-width *deficit*; one cannot deduce it from the displayed DL bound plus an upper bound on the discarded output width without checking what source parents were lost. KKL A.11 p. 62 is a domination lemma for specified laminations, not that deficit transfer. We make no use of A.13, Prop. 6.21, or an unproved relative-discard extension of DL. In particular (W) remains OPEN natively.

Direct downstream inventory in KKL §6: pp. 49–50 use the comparison (6.28) only inside Lemma 6.24; (6.30) is the resulting scalar telescope. Lemma 6.31 p. 50 uses central ending of each iterated leaf and unbreakability to infer a common separating component; its displayed argument does not invoke maximality, but the actual geometric inference and degree-one assertion are not verified here (the proof also mentions \(A_N\) although the constructed chain stops at \(A_{N-1}\)). Equations (6.32)–(6.34) pp. 50–51 use that terminal component property, domination and bounded-degree pushforward, not the maximizing rule. In particular (6.30) alone does not imply (6.34). Proposition 6.20 p. 51 uses only the bound of 6.23, and later Section 6 uses the resulting propositions, not the selected sequence itself. This is a syntactic inventory of selection use, not a certification of Lemma 6.31, (6.32)–(6.34), or Proposition 6.23 after changing the selection. No full repair is claimed.

**Significance:** This rules out replacing inclusion-maximality by width-maximality as a generic covering-level fix; the repeated conflicts cannot be absorbed into a constant merely by optimizing the choice. It leaves open whether the actual stationary marked dynamics preclude such conflicts and furnish (W) and the terminal bound. Thus there is no certified erratum-level repair of the printed argument on this line: the printed route from (6.30)/(6.34) through Proposition 6.23 to Proposition 6.20 and the main beau-bounds/rigidity conclusions remains unverified here. This is not evidence that the main theorem is false.

## 6. Reproduction and status

From repository root, Python 3.12:

    p=research/frontier/kkl_width_maximal_20261126
    python3.12 -m venv /tmp/kkl-width-maximal
    . /tmp/kkl-width-maximal/bin/activate
    python -m pip install --no-deps -r "$p/requirements.txt"
    python "$p/verify.py" --model-only
    python "$p/verify.py"
    git diff --exit-code -- "$p/source_lock.json"

The optional --cache /path/to/pdfs expects the exact versioned PDF filenames. The verifier checks source digests, page counts and text anchors; it uses rational interval extrema for endpoint interlacing, nesting, markings and support separation, and enumerates full-packet choices at small horizons. These finite checks are not proofs of any analytic or native assertion. The written proof above is independent of the finite range. CI records the generated lock on the dedicated branch only, and PR verification checks exact reproduction. No physical identification is claimed; the verifier is registered as standalone METADATA, with no ledger or bridge-status change. Status: **proved** for the restricted counterexample, **open** for (W) and native repair, **evidence-not-proof** for finite/source checks.

AI disclosure: ChatGPT GPT-6.2 performed source comparison, proof search, construction, arithmetic diagnostic authoring and editing; no independent human or specialist review has been performed.
