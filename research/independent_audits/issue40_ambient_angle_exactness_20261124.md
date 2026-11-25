# Issue #40 — ambient-angle exactness bypass of the PF/zero-edge split (2026-11-24)

> **Status (2026-11-25): historical, conditional.** The review target of this PR is the [canonical-localization certificate](issue40_canonical_localization_uniqueness_failure_20261124.md). What is proved below is plane topology of explicitly defined contour maps and model dynamics. Every transfer to the native KKL interval action is conditional on the source-identification hypotheses stated in the note, and in particular on using the geometric contour formula of Prop. 6.5; the certificate shows that the printed A.3.2 maximal-subset definition does not produce that formula on the canonical 3/9-tip localization. Read "theorem", "identity" and "proved" in that conditional sense. No ledger entry is promoted, Issue #40 stays open, and there has been no specialist review.

New route following the monotone prime-end bridge and finite-host marked-gate sandwich in this PR. We prove a general contour-collapse theorem for nested locally connected dendrites, including infinitely many attached components, and an ambient-angle exactness theorem for the induced interval action. With the marked identification established in the companion notes under their explicit hypotheses, this eliminates the need for a separate small-Julia-side nonreturn proof or a weighted-edge argument to exclude periodic intervals. This is a conditional native repair, not an unconditional closure of Issue #40 or the analytic Wave Lemma.

## 1. General nested dendrite contour collapse

Let A⊂B be nondegenerate subcontinua of a compact planar dendrite K. In particular all these continua are locally connected, full, with empty interior. Let C_A,C_B denote their exterior prime-end circles and h_A,h_B the exterior conformal uniformizations; write L_A,L_B for their continuous landing maps.

**Theorem 1.** There is a canonical continuous monotone degree-one surjection

    r_{B,A}: C_B → C_A

with the following description.

* If the model point L_B(b) belongs to A, r_{B,A}(b) is the unique old ideal limit of h_A^{-1}h_B at b.
* If L_B(b) is outside A, in a component X of B\A, then r_{B,A}(b) is the unique old host angle e_X of the closure of the exteriorized component h_A^{-1}(X).
* Every component contour, with its root gates, collapses to its host angle. Different components sharing an angle may be in the same collapsed fiber. Distinct root accesses must not be identified merely because their planar landing point coincides.

No assumption of finitely many components of B\A is made.

Proof. Each component X of B\A has closure a subdendrite meeting A at one root: two distinct contacts would contradict the unique arc property. The closures of the components form a null family (only finitely many have diameter above a given positive number). For a direct proof, if distinct components had diameter at least epsilon, choose points at distance at least epsilon/2 from their respective roots, and pass to a subsequence on which those points converge. The arc between points in distinct components passes through their roots and cannot have diameter tending to zero, contrary to uniform local arcwise connectedness of the compact dendrite.

Exteriorize A to the closed unit disk D, forming the compact full obstacle

    L = D ∪ h_A^{-1}(B\A).

For a component X let Y_X be the closure of h_A^{-1}(X) in the closed exterior disk. It is compact and connected, and its intersection with the unit circle is nonempty and lies in the landing fiber of its root. The union D∪Y_X is full: any bounded complementary component would be an open subset of the full obstacle L outside D, but L\D has empty interior. By the compact-plane Mayer–Vietoris sequence and Alexander duality, D∩Y_X is connected. It is contained in a totally disconnected landing fiber (a nonconstant univalent map cannot have a constant boundary value on an arc, by analytic uniqueness). It is therefore one point e_X. This proves unique angular attachment, including when the root has multiple distinct accesses.

The Y_X form a null family as well. Otherwise take a sequence of distinct X_n with Y_Xn of diameter bounded away from zero, with physical roots converging to x in A. Physical diameters tend to zero by the previous paragraph. Any Hausdorff cluster limit of the exteriorized closures is a compact connected subset of the unit circle landing fiber over x: they stay bounded in exterior coordinates, and the only possible limits land at x. The landing fiber is totally disconnected. This contradicts the positive lower bound on diameters.

Group all Y_X at a fixed angle e into Y_e, including e. By the null property these are compact connected sets. They are pairwise disjoint: outside the circle the original components are distinct, and on the circle each has just its one angle. They also form a null family since any two points in Y_e are at distance at most twice the supremum of the constituent diameters (all constituents contain e).

Each Y_e is nonseparating in the plane. Any bounded component of its complement cannot meet the connected exterior of L containing infinity, so would be an open subset of L. As L\D has empty interior, such an open component would have to lie in the interior of D. But that interior is connected to infinity in the complement of Y_e: use a point of the unit circle different from e, a small neighborhood disjoint from the compact Y_e, and then a point in the dense exterior of L outside D. This is a contradiction.

Collapse each Y_e to a point, with all remaining points singleton. This is a closed equivalence relation by the null-family property: a convergent sequence of equivalent pairs from infinitely many groups has equal limit coordinates. The classes are compact connected nonseparating continua. Moore's sphere decomposition theorem gives a quotient sphere. The quotient is one-to-one on D and a homeomorphism near infinity; identify its image of D with D by an orientation-preserving homeomorphism of the quotient sphere extending the inverse disk chart (Schoenflies). The resulting monotone sphere map Q is the identity on D, maps each Y_e to e, has Q^{-1}(D)=L and unique inverse image of infinity.

Apply Theorem 1 of issue40_monotone_model_prime_end_bridge_20261124.md to this monotone sphere map and the target closed disk. It extends to a continuous monotone degree-one map from the exterior prime-end circle of L onto the unit circle. Identify the former with C_B by the conformal exteriorization of A restricted to the exterior of B. This defines r_{B,A}.

The map is independent of the choice of the quotient identification: if L_B(b) is in B\A, exteriorized approaches converge to the corresponding point in Y_X and Q takes that point to e_X. If L_B(b) is in A, the old external coordinate cluster set lies in the old landing fiber at that point, is connected, and hence is a singleton (equivalently use analytic boundary uniqueness). Since Q fixes the unit circle, its induced angle is precisely this old limit. These two descriptions account for all b and prove uniqueness. The description covers source root accesses through their individual old limits, not their planar point names. QED.

A contour collapse need not agree with a continuous extension of the actual inclusion on an attached component: the latter approaches an *interior point* of the old exterior. It is a separate boundary map. It can collapse whole intervals even though both continua are locally connected.

## 2. Nested coherence

**Theorem 2.** For nondegenerate subdendrites A⊂B⊂K,

    r_{K,A} = r_{B,A} r_{K,B}.                               (2.1)

Proof. Fix an ambient prime end t with landing point x. If x∈B, r_{K,B}(t) is the limit in the B exterior coordinate of an ambient approach at t. If x∈A, compose the old coordinate change and use the unique old limit of Theorem 1. If x∈B\A, the component of B\A containing x is contained in the component of K\A containing x. Their host angles agree, by sequences tending to the unique root of the larger component (or by the uniqueness of the old limit along the smaller component, which attaches to A at the same root). Thus (2.1) holds.

If x∉B, let X be its component of K\B, with root y∈B and B-host b. If y∉A, X together with y is in the same component of K\A as the component of B\A containing y, so the host in A is again the same. If y∈A, choose points of X tending to its root. Their B-exterior coordinates converge to b by unique host attachment. Their A-exterior coordinates converge to the A-host of their component of K\A. But the model landing of b is y∈A, so by the unique old limit property this latter limit is r_{B,A}(b). This proves (2.1) in the remaining case. QED.

The host agreement used above is elementary: a connected subset of K\A whose closure meets A belongs to exactly one component, and its root must be that component's unique root. Its nonempty exteriorized cluster at A lies in the singleton host of the larger component.

## 3. Dynamical coherence and exactness

Suppose now P is the degree-d topological polynomial model of a periodically repelling polynomial, K its full invariant dendrite, A⊂K a forward invariant nondegenerate subdendrite containing the critical values, and B=P^{-1}(A)⊂K a full connected continuum. Thus A⊂B, and P maps the exterior of B onto the exterior of A as an unbranched degree-d covering. The covering has a prime-end boundary map p_0:C_B→C_A. In the KKL application this boundary map is also obtained from Theorem 3 of the companion prime-end bridge; it is the actual induced model covering, not a separately selected Markov map. Let D_K:C_K→C_K be the model ambient external-angle dynamics. It is topologically exact: the physical polynomial's exterior Böttcher map is multiplication by d on the angular circle, and the ambient prime-end transfer m_K factors it onto D_K. Every nonempty open target set has a nonempty open inverse image; multiplication by d maps some interval in that inverse image onto the whole circle after finitely many iterates. Surjectivity of m_K proves the claim. (One can also use the angular parametrization of the locally connected model directly.) Here d≥2.

**Theorem 3.**

    r_{K,A} D_K = p_0 r_{K,B}.                               (3.1)

Proof. If the ambient end lands in B, exterior approaches to that end have a unique limit in the B coordinate. Their images under P have unique limit p_0 of that B end in the A coordinate. This is exactly the old limit in r_{K,A} of the ambient image, which lands in A. The fact that the induced covering agrees with limits along the model exterior follows from the actual prime-end covering square, or from the covering in the model plane.

If the end lands in X, a component of K\B, then P(X) is contained in a component Y of K\A. Choose points of X tending to its root. They approach its B-host in exterior coordinates. Their images approach the root of Y (the image of the root belongs to A), and hence approach its A-host in exterior coordinates. By the boundary covering this host is p_0 of the B-host. The ambient image lands in Y, so this is exactly its r_{K,A} image. QED.

The model polynomial in Kiwi, Adv. Math. 184 (2004), Proposition 4.2 and Theorems 5.12–5.13, is a branched covering of the plane, not just a map of the abstract dendrite. This is relevant to the use of the covering in (3.1).

Define the complete model interval action (on sets, including open and closed inputs)

    Phi(I) = p_0(r_{B,A}^{-1}(I)).

Set q=r_{K,A} and s=r_{K,B}. From (2.1), q=r_{B,A}s, and from (3.1), qD_K=p_0s. Since s is onto, for every subset I of C_A,

    Phi(I) = q(D_K(q^{-1}(I))).                             (3.2)

Indeed s(q^{-1}I)=r_{B,A}^{-1}I, and the equality follows by applying p_0. This is a set equality, not a commuting single-valued map of C_A. It is compatible with expanding attachment fibers and the separate closed-endpoint rule.

**Corollary 4 (eventual saturation).** Every nonempty open interval I in C_A, marked or unmarked, satisfies Phi^n(I)=C_A for some finite n. More generally the same holds for any set containing a nonempty open interval. In particular there is no proper periodic open interval, nor a proper finite cycle of positive closed crests under the complete model operation.

Proof. From (3.2),

    Phi^n(I) ⊃ q(D_K^n(q^{-1}(I)))

by induction, since q^{-1}q enlarges sets. The inverse image of a nonempty open interval under continuous onto q is nonempty open. By exactness of D_K it maps onto the ambient circle in finitely many steps. This proves saturation. The whole circle is fixed. Inclusion-monotonicity gives the extension to sets containing an interval. QED.

If one works in the physical Böttcher angle circle and writes q_phys=q m_K, the time bound is explicit for any particular interval: if q_phys^{-1}I contains an open angular interval of length delta>0, choose n with d^n delta>1. It is important that the inequality is strict, since equality for an open interval can give a punctured circle. There is no claim of a uniform bound independent of the size of arbitrary unmarked intervals or of renormalization type. There is also no claim that Phi on arbitrary unmarked model intervals is the physical source pullback on arbitrary unmarked physical intervals. Only the original marked domain is transported in the companion notes.

This nonreturn mechanism requires neither a positive edge weight nor an expanding Perron eigenvalue. It proves exactness of the complete model interval **relation** by comparison to the ambient external angle map, rather than arguing incorrectly that positive core entropy alone excludes every periodic interval.

## 4. Consequence for the repaired marked KKL proposition

Apply the marked identification of issue40_marked_gate_sandwich_20261124.md, under its stated saturated-lift, singleton-marking, finite-host and Prop. 6.5 assumptions. Then every nonempty original open physical marked interval saturates eventually: its sequence is identified exactly with the complete model action. The same holds for positive closed intervals (or by monotonicity). This removes the separate conditional edge-multiplicity and whole-little-Julia-side charts from the *nonreturn argument*. They remain relevant if one separately wants the stronger weighted inequality demanded by the historical issue.

Use Prop. 6.6 and Appendix A.3.4 for nonempty disjoint refined atom pullbacks. A proper image cannot decrease combinatorial length: if its pullback is a connected open interval and the covering image is proper, the covering is injective there. The image of each included source atom pullback contains at least one distinct target atom. The full image saturates, and the whole circle is fixed. The same length inequality holds for closed marked intervals by counting their contained open atoms; the closed pullback is an actual closed interval. If the final length is below the full-circle length, equality at both ends of a finite orbit forces all intermediate lengths equal. For a critical limb consisting of r≤6b atoms, at most r+k-1 cyclic open length-k intervals meet it. (For positive closed intervals meeting an open critical limb, intersecting the limb implies at least one common open atom.) The bound is at most the total number of cuts if wraparound makes the naive count larger. Thus 6b+k distinct critical visits with no length growth yield a repeated proper marked interval, impossible by Corollary 4. If the input or output saturates, the repaired conclusion is saturation or strict growth, as in PR #38. Do not claim strict growth from a full circle.

For the positive proper closed crests of an actual short-wave chain, each critical visit has an inclusion of the form I_{j+1}⊃F_*^{m_j}I_j. These inclusions and nondecreasing length are sufficient for the same finite-state count: on a plateau of equal positive length below saturation, inclusion between two closed intervals of that length is equality. A repeated state would contain its own iterate and, by monotonicity and eventual saturation, force the whole circle. Thus the number of positive short crest states is bounded by the sum of the relevant critical-interval counts for k<12b, below the 216b² budget in Lemma 6.4. This statement requires actual positive connected marked closed crests; it does not by itself prove that all source waves satisfy those hypotheses (in particular a singleton crest needs separate treatment). No equality of open-image closure with closed-image action is used.

## 5. Source checks, hostile audit and limits

* Theorems 1–3 concern actual planar continua and the full attached contour, not only rational ray names. Infinite ambient attachments are handled using the null-family property and the Moore quotient. Without local connectivity of the model, the null-family argument need not hold.
* In the physical non-LC situation the model r_{B,A} is transported only by the marked-gate comparison. A continuous boundary quotient of the physical inclusion on all unmarked ends is not asserted.
* In KKL's periodically repelling setting the straightened quadratic polynomial and its Kiwi model supply the ambient exact map. The hypotheses that the chosen old/preimage carriers are the saturated lifts and that the original cuts lift uniquely are still source-authentication steps, as is the access-sensitive interpretation of Prop. 6.5. The conditional theorem should not be reported as an unconditional proof of the source.
* The exactness statement is strictly stronger than a one-off finite check of nonreturn in a physical slit example. It is independent of a comparison between a graph incidence matrix and an individual proper path. It also explains why full-circle saturation, rather than strict growth in every case, is the correct formulation.
* No new CI, formal proof verification, or independent peer review is claimed. This does not prove the Wave Lemma's analytic width amplification or MLC, and does not itself verify all the acceptance criteria of Issue #40. Keep the issue and PR open/draft for review.
