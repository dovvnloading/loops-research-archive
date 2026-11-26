# KKL width maximization with a bounded-discard candidate: the Borel case

**2026-11-26. Status: PROVED for the finite-width Borel selection implication; CONDITIONAL for a native stationary application; OPEN for native existence of the required candidate and downstream geometry.**

This is a follow-up to [#130](https://github.com/dovvnloading/loops-research-archive/pull/130), [#133](https://github.com/dovvnloading/loops-research-archive/pull/133), and the [N1 audit #129](https://github.com/dovvnloading/loops-research-archive/pull/129), based on main at a06a8dea848092d8499c923b02ab7c6176cb60e2. It answers the stronger bounded-candidate question left open in [#133, §4](../kkl_width_maximal_20261126/NOTE.md) in the proper Borel category. The answer is affirmative, with the sharp comparison constant one and no assumption that a maximizer exists. A generalization to nonmeasurable choices is false, even for a single injectively projected marked packet in a degree-two annular cover.

**Attribution:** finite additivity for disjoint curve families is the classical Parallel Law, not a new general extremal-length theorem. The contribution is to verify its precise measurable-carrier hypotheses at the parent-family comparison, give the countable and exact-envelope formulations, derive a robust finite-horizon conditional selection result, and exhibit the failure outside the measurable category. No claim of priority in the general modulus literature is made.

## 1. Source and target

* Kahn–Kapiamba–Lyubich (KKL), [arXiv:2606.27272v1, §6.2](https://arxiv.org/html/2606.27272v1#S6), Lemma 6.24, equations (6.25), (6.28), (6.29), (6.30), and Appendix A.1 (versioned HTML checked; PDF pp. 49–50 and 56–57 are inherited locators from #129/#133). The printed proof uses a maximal centrally-ending continuation and compares its parent width with the width of a candidate.
* Jeremy Kahn, [A priori bounds for some infinitely renormalizable quadratics: I. Bounded primitive combinatorics, IMS 2006/5](https://www.math.stonybrook.edu/preprints/ims06-05.pdf), §3.1, printed p. 10 and footnote 7. A proper lamination is a Borel geometric union of disjoint proper paths. The source page image was checked.
* Kahn–Lyubich, [The Quasi-Additivity Law in conformal geometry](https://annals.math.princeton.edu/2009/169-2/p05), Ann. Math. 169 (2009), 561–593, [PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v169-n2-p05.pdf), §4.1–4.2, printed pp. 589–590. The admissible-metric definition of width and the equality case of the Parallel Law are explicit there. Both page images were checked. We supply the measurable-support proof below rather than invoke equality without its necessary measurable interpretation.
* Archive inputs only for the explicitly conditional extensions: [BOWR, Theorem and §§5, 7–8](../../mlc_unified/kkl_stationary_n1_borel_ordered_wave_realization_20260726.md), [Borel width envelope, Theorem 1.1](../../mlc_unified/kkl_stationary_n1_borel_width_envelope_20260726.md), [N1, Theorem N1 and §3](../../mlc_unified/kkl_stationary_relative_wave_continuation.md). Their integrated native applicability is not independently reproved here.

Source locators were checked as specified above, not a fresh byte-hash audit. Target is the measurable parent-loss interface in Lemma 6.24 / the N1 stationary continuation, not a new ledger closure.

## 2. Parent width is additive on measurable disjoint carriers

Fix a Riemann surface V with a smooth conformal background metric ds and its area dA. For a path family G in the interior of V, use the strong (every-leaf) admissibility convention

\[
 W(G)=\inf\left\{\int_V\rho^2\,dA:\rho\ge0\text{ measurable},
                   \int_\gamma\rho\,ds\ge1\quad(\gamma\in G)\right\}.
\]

Densities are actual pointwise functions, not merely equivalence classes modulo area-null sets. One may use Borel densities and extended nonnegative integrals; for locally rectifiable paths integrate on compact subarcs and take the increasing limit. For any other path-length convention used in the source, the following argument applies whenever identical densities on the entire interior trace give identical length. No metric is assigned to an ideal endpoint.

**Lemma 1 (measurable Parallel Law, countable form).** Let G_j be countably many path families in the same V, with pairwise disjoint Borel carriers U_j containing all their respective interior traces. Then

\[
 W\left(\bigcup_j G_j\right)=\sum_j W(G_j)
 \quad\text{in }[0,+\infty].
\tag{1}
\]

Proof. For any admissible density rho of the union, its restriction to U_j, zero elsewhere, has exactly the same length on each path of G_j. Thus its area on U_j is at least W(G_j). Disjointness and countable integration imply the lower bound, and taking the infimum preserves it. Conversely, if the sum is finite, choose for each j a density of area at most W(G_j)+epsilon 2^(-j) (index j>=1). Restrict each to U_j. Patch the restricted densities on their disjoint carriers, zero outside their union. The resulting measurable density is admissible on every constituent path and has area at most the sum plus epsilon. Let epsilon decrease to zero. If the sum is infinite, the lower bound already gives equality. This uses no minimizer, disintegration, local product chart, transverse regularity, or conformal rectangle representation. QED.

Let S be a proper Borel lamination, and write U(M) for the union in V of the interiors of the leaves in a subfamily M of S. In particular, if U(M) is Borel, then U(S minus M)=U(S) minus U(M) is Borel, since distinct leaf interiors are disjoint. Hence

\[
 W(S)=W(M)+W(S\setminus M).
\tag{2}
\]

This is an identity in the **parent** V. It is not an identity on an untagged output that may have overlapping curves. It does not require a Borel parameterization of leaves: the Borel carrier alone suffices. If a joint Borel injective leaf evaluation on a standard-Borel leaf space is available, Lusin–Souslin supplies the Borel carriers for all Borel code subsets. Conversely the carrier-Borel subsets themselves form a sigma-algebra on the leaf set; (1) makes width a measure on that sigma-algebra. With finite W(S), this is a finite measure, not an assumption of a transverse invariant measure for a different lamination or dynamics.

## 3. Answer to the bounded-candidate question

**Theorem 2.** Let S be a finite-width proper Borel parent Wave. Let A be any nonempty class of admissible subwaves of S, each with Borel geometric carrier. Suppose there exists P in A satisfying W(S minus P)<=C. Write

\[
 H=\sup_{D\in A}W(D).
\]

For every M in A satisfying W(M)>=H-epsilon, with epsilon>=0, one has

\[
 \boxed{W(S\setminus M)\le C+\epsilon.}
\tag{3}
\]

Proof. By (2), and only subtracting finite quantities,

\[
 W(S\setminus M)=W(S)-W(M)
 \le W(S)-W(P)+\epsilon=W(S\setminus P)+\epsilon.
\]

QED. For every epsilon>0 an approximate maximizer exists by the definition of supremum; exact attainment is not needed. For an exact maximizer take epsilon=0. More precisely,

\[
 \inf_{D\in A} W(S\setminus D)= W(S)-H.
\tag{4}
\]

The theorem requires neither a covering nor an order on leaves. In the degree-two annular models of #130 and #133, it applies to the proper Borel source Waves, with admissibility defined by their actual projected Waves. It works for every eligible Borel choice of almost-maximal parent width. The #130 inclusion-maximal small packet is not width-maximal. The #133 multiscale obstruction has no uniformly bounded-discard candidate. Neither counterexample conflicts with (3). In fact (3) holds for an arbitrary candidate P with a well-defined complement width <=C, even if its carrier is not Borel, as long as H>=W(P): the Parallel Law inequality alone gives W(S)-W(P)<=C. It is the maximizing M that needs a measurable carrier for the exact discard identity.

This resolves the stronger **Borel** covering-level question of #133 §4. It is not a proof of existence of P under native KKL hypotheses. Nor does it turn inclusion-maximality into width maximization.

### Exact Borel hull and set-theoretic candidates (with the stated envelope input)

Suppose the standard-Borel injective evaluation and Theorem 1.1 of the archive's width-envelope note apply to S. For arbitrary D contained in S, of finite width, choose Borel code supersets E_j of D with W(E_j)<=W(D)+1/j. Their intersection E is Borel, contains D and, by monotonicity, has

\[
 W(E)=W(D).
\tag{5}
\]

The same equality is trivial for infinite width by using S. Thus the outer width on arbitrary leaf subsets equals the outer measure obtained by taking infima over Borel supersets for this finite Borel width measure. This derives an exact hull from the already recorded approximate envelope; no assumption of additivity on arbitrary subsets is made.

For a direct holomorphic covering f:V->Y, suppose P is a possibly non-Borel set of source leaves, all of whose images form a disjoint eligible Wave in the set-theoretic sense (coincident images may be identified), and W(S minus P)<=C. Put D=S minus P and take its exact Borel hull E from (5). Then P_0=S minus E is Borel and contained in P, with W(S minus P_0)=W(D). Its projected geometric support is Borel: a covering of second-countable surfaces admits countably many open local-homeomorphism charts; the image of a Borel set in each chart is Borel, and their union is countable. The remaining actual image paths remain disjoint after identifying coincident paths, retain the common base and the same designated ending predicate. Hence P_0 is a proper Borel admissible candidate. This argument is for direct coverings. The native immersion-and-filter operation requires the corresponding Borel successor and heredity interface, not just this open-map argument.

## 4. Conditional native consequence and a robust finite horizon

Use precisely the parent object A_n and the next centrally-ending selection in KKL (6.25)–(6.29). Assume finite parent width, disjoint proper leaves, Borel parent and selected carriers, and an actual admissible source candidate P_n with W(A_n minus P_n)<=C_b. Choose A_(n+1) within epsilon_n of the supremum of parent widths of proper Borel admissible choices. Equation (3) gives

\[
 W(A_n\setminus A_{n+1})\le C_b+\epsilon_n.
\tag{6}
\]

Thus the specific maximal-choice inference from a *proved parent-relative candidate* and parent-width comparison is valid. The printed (6.26) is not a parent-relative candidate bound; (6.29) is not repaired by (1). The DL extraction, leafwise direction, filtered occurrence transfer and terminal geometry remain separate requirements.

A single good chain suffices for a weaker uniform guarantee even for other near-maximal choices, under explicit heredity:

**Theorem 3 (chain comparison).** Let S=B_0 ⊃ B_1 ⊃ ... ⊃ B_m be one proper Borel chain, with B_j eligible at stage j and W(B_(j-1) minus B_j)<=C_j, each C_j finite. Suppose the stage-j admissibility predicate is hereditary on Borel subfamilies of B_j. Let S=A_0 ⊃ ... ⊃ A_m be any chain chosen within epsilon_j of the supremum of eligible Borel parent subfamilies at each stage j. Then

\[
 W(A_{j-1}\setminus A_j)
 \le \sum_{i=1}^{j}C_i+\epsilon_j,\qquad
 W(S\setminus A_m)\le
 \sum_{i=1}^{m}(m-i+1)C_i+\sum_{j=1}^{m}\epsilon_j .
\tag{7}
\]

Proof. The eligible comparison at stage j is Q_j=A_(j-1) intersect B_j. It is a proper Borel parent subfamily and hereditary eligibility gives its output condition. Its omitted part is contained in S minus B_j, a disjoint union of the first j losses of the good chain. Lemma 1 bounds their width by sum_{i<=j} C_i. Apply (3) to Q_j and the near-maximal A_j. Sum the resulting inequalities over the disjoint discarded carriers of A_0,...,A_m. QED.

For the native successor, one sufficient verification of heredity is the following explicit conditional interface: there are standard-Borel source and target leaf codes; the actual unique untagged j-step successor is Borel and countable-to-one on B_j; its full image is a proper Borel Wave. Then the image of every Borel source subset is Borel by the countable-section Lusin–Novikov theorem, and its geometric support is Borel by injective evaluation on target codes. The Wave base and ending condition pass to subsets. Under an actual degree-two cover with filtered proper restrictions, the countable-to-one requirement follows if every parent admits at least one genuine retained lift of its designated successor: a given proper successor path has at most two lifts up to reparameterization, and the immersion image of each lift has nonempty interior trace in at most one parent leaf. Iteration gives at most 2^j parents when all intermediate leaves form laminations and each step has this property. These are typed conditional statements, not a new verification of the full native BOWR or filtered-restriction theorems.

For m=N-1=b+2 and a good N1 chain with each C_j<=C_b, (7) gives a finite bound depending only on b and the approximation tolerances, even if the original N1 construction only controls its own chosen chain. The estimate is at most m(m+1)C_b/2 plus the sum of the tolerances, not a sharp linear-in-b bound. If a bound is desired only for the consumed scalar telescope (6.30), the original good chain already has the better sum of its own losses. Neither this comparison nor (6) proves Lemma 6.31 or (6.34).

## 5. Why measurability is indispensable: an explicit annular countermodel

Even if all projected paths are compatible and a zero-discard candidate exists, the statement for arbitrary (nonmeasurable) width-maximizing selections is false.

Fix T>0, R=1/10, r_0=R exp(-T), c=1/2. Let X=(R/2Z)×(0,1) and Y=(R/Z)×(0,1), where R in the cylinder notation means the real line; equivalently their circumferences are 2 and 1. Let f reduce the horizontal coordinate modulo 1. These are conformal annuli and a degree-two holomorphic cover. For each t in [0,T] let gamma_t be the upper semicircle centered at c with radius r=r_0 exp(t), its endpoints on the ideal bottom boundary. All paths lie in the first fundamental strip, so their images are embedded and pairwise disjoint. Mark the bottom target circle at 0, 1/4, c+r_0/2, c+3r_0/4, 3/4 and pull the marking back to X; mark the top as one component. Each leaf has left endpoint in (1/4,c+r_0/2) and right endpoint in (c+3r_0/4,3/4), crests over the intervening marked interval, and is subordinate to (1/4,3/4). The endpoint intervals are separated by an intermediate interval on either route around the circle, so the paths satisfy the marked-path condition (as in #133). The source and target marking counts are fixed as T varies. The full family S is proper Borel, is itself admissible, and has zero discarded width.

For any parameter subset E of [0,T], write S_E={gamma_t:t in E}. With lambda^* denoting Lebesgue outer measure,

\[
 \boxed{W(S_E)=\lambda^*(E)/\pi.}
\tag{8}
\]

Indeed the half-annular coordinates (t,theta), theta in (0,pi), give ds=r dtheta along a leaf and dA=r^2 dt dtheta. For every admissible density, Cauchy–Schwarz gives
\[
  \int_0^\pi \rho(c+r e^{i\theta})^2 r^2\,d\theta\ \ge 1/\pi
\]
on E. The set of parameters satisfying this inequality is measurable (for Borel densities by Tonelli), so its area integral bounds lambda^*(E)/pi from below. For Lebesgue-measurable densities use Tonelli outside a null parameter set; removing that set does not alter outer measure. For the converse take any Borel superset H of E in [0,T], and use rho=1/(pi r) on the corresponding half-annular carrier, zero elsewhere. Its area is lambda(H)/pi and every leaf of S_E has length exactly one. Infimize over H. This proves (8) without assigning a density to a nonmeasurable set.

Under ordinary choice, partition [0,T] into E and E^c each of full outer measure T. For completeness: well-order all positive-measure compact subsets of the interval (there are at most continuum many, and each has continuum many points). By transfinite recursion choose two distinct previously unused points in each compact, assigning one to E and the other to E^c; assign leftover points arbitrarily. At each stage fewer than continuum many points were chosen, so the construction succeeds. Neither part contains a positive-measure compact set, because the other part meets every such set. By inner regularity both have inner measure zero and thus both have outer measure T.

By (8), M=S_E has width W(S)=T/pi, hence is a width maximizer among the set-theoretically compatible subfamilies. Yet W(S minus M)=T/pi as well, which is unbounded as T grows. The admissible competitor P=S discards nothing. M is **not** a proper Borel lamination: intersect its carrier with the continuous transverse ray t -> c+i r_0 exp(t); its inverse image is E, which is not even Lebesgue measurable. This is a counterexample only to the enlarged nonmeasurable assertion, not to KKL's proper-lamination category or to the classical Parallel Law with measurable carriers.

The model also makes the difference between a measure on Borel leaf subsets and outer width on all subsets concrete. No finite numerical experiment can decide this nonmeasurable construction; (8) and the compact-set argument are the reproducible proof.

## 6. Status, dependencies, and review

* **PROVED (written elementary argument):** measurable disjoint-carrier additivity, countable version; the bounded-candidate implication (3)–(4) for all finite-width proper Borel near-maximizers; the finite-horizon comparison with its explicit heredity hypothesis; nonmeasurable countermodel (8).
* **CONDITIONAL:** exact Borel hull (5) when the recorded envelope hypotheses hold; native application (6)–(7) when the actual admissible candidate/chain and Borel successor hypotheses have been established.
* **OPEN:** unconditional native candidate/extraction from KKL hypotheses, literal inclusion-maximal relative loss, the printed (6.29), terminal alignment and width comparison, Proposition 6.23 in full, MLC. Neither prior covering counterexample is withdrawn. Infinite parent width is excluded from subtraction and optimization conclusions.

No model-to-physical identification, ledger status promotion, external source hash verification, formal Lean certification, or numerical claim is made. The proof is self-contained at the measurable-carrier level; no executable is needed to establish it. The optional envelope/native applications explicitly identify their archive dependencies rather than promote them. This isolated note changes no central ledger, README, source register or existing audit. Human specialist review remains outstanding.

AI disclosure: ChatGPT GPT-6.2 assisted in source checking, proof construction, scope checking and drafting. The classical Parallel Law is credited to its source, not claimed as a novel general theorem.
