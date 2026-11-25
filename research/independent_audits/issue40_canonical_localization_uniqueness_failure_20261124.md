# Issue #40 — first-failure certificate for the literal maximal-subset restriction

**2026-11-24.** This replaces the previous plan to establish globally unique exclusion lifts by a calculation on the actual canonical renormalization. It is a counterexample to the **unrestricted subset quantifier** of KKL v1 Appendix A.3.2 together with Propositions 6.5–6.6 as printed, and a repair of the interval restriction in the concrete locally connected case. It is not a counterexample to the authors' intended geometric contour action, width theorem, or MLC. Independent review is requested.

**Sources.** KKL, [arXiv:2606.27272v1](https://arxiv.org/pdf/2606.27272v1), §§2.2–2.3, pp. 11–12 (canonical localization); §1.4 (proper paths); §6.1, pp. 42–43 (Propositions 6.5–6.6); A.1 (subordination); A.3.2, p. 62 (maximal subset, with uniqueness in the entire restriction family before testing subordination). Kahn, [arXiv:math/0609045v3](https://arxiv.org/pdf/math/0609045), Theorem 7.12 and §§7.4.2–7.4.3, pp. 44–45, establish the local-cover construction and its commuting maps. We use those actual covering spaces, not a finite sheet diagram.

**Revision 2026-11-25 (response to the PR #119 review).** §0 fixes the two readings of the restriction family and says which section uses which. §1.1 lists the standing hypotheses of KKL §6 against the 3/9 example and sorts the conclusions into general propositions and example-specific ones. §4 is marked as holding only under the maximal-lift reading and only in this locally connected slit. §5 lists what remains open. A non-specialist re-read (Claude, Anthropic) compared the wording of KKL v1 §§2.1–2.3, §3.1, the opening of §6, §6.1 and A.3.2 with the PDF text and re-derived §§1–3. That is not the specialist review the PR asks for, which is still outstanding.

## 0. Conventions: two readings of "restriction", and where each is used

KKL A.3.2 defines the pullback of a proper target path γ as the set ι^*γ of proper source paths contained in ι^{-1}(γ), and the pullback ι^*X of a connected ideal subset X as the maximal ideal subset Y of the source with the property

    P_X(Y):  for every proper target path γ, if ι^*γ is a single path γ' and γ' is subordinate to Y, then γ is subordinate to X.

The text does not say whether "contained in" refers to traces or to lifts. The two readings are kept apart from here on.

**(T) Trace reading.** ι^*γ consists of every proper source path whose trace lies in ι^{-1}(trace γ), up to reparameterization.

**(L) Maximal-lift reading.** ι^*γ is the family of occurrences (J, γ'), where J is an open subinterval of the parameter interval of γ and γ' is a continuous lift of γ restricted to J (so ι∘γ' = γ on J) that is proper and cannot be extended to a larger subinterval. Two occurrences are equal only if they have the same J and the same lift. For an embedding this is the occurrence-indexed maximal-component convention of [the selected-slit note](immersion_mark_resolution_20261124/NOTE.md), §2. For an immersion with several sheets, different lifts over the same J are different occurrences.

Under (T) the family is never a singleton. If δ is a proper path with trace in ι^{-1}(γ), the hairpins of Proposition 2.1 of the selected-slit note are distinct proper paths inside the same trace; inserting an interior backtrack in δ (run to an interior point, return a short way, run forward again) likewise gives a proper path with the same trace that is in general not a reparameterization of δ. So under (T) the hypothesis of P_X(Y) is never met, every Y satisfies it, and ι^*X is the whole ideal boundary for every X. This is true for every immersion and uses nothing from §§1–2 below.

| Section | Reading used | Remark |
|---|---|---|
| §1 | none | covering-space topology of the canonical localization only |
| §2, endpoint lemma and no-unique-exterior statement | (L) | "no unique restriction meets the exterior" is also true under (T), trivially |
| §3, nonmaximality of the geometric block J | (L) for the argument given | also true under (T), where it is the degenerate statement above and needs neither the 3/9 tip nor E_B |
| §4, exact raw formula, singleton witnesses, connected-interval repair | (L) only | the witnesses are single maximal lifts; under (T) they are not singletons and the raw subset is the whole ideal boundary, so nothing in §4 is asserted under (T) |

Neither literal reading reproduces the formula of Proposition 6.5. The proof of Proposition 6.5 in KKL works with proper source paths near the tree that are at the same time proper target paths, after T' has been identified with a subset of K. That operational use is what "the intended geometric contour action" means in this note.

## 1. The actual canonical immersion has infinitely many exterior sheets

Take an ordinary degree-two quadratic-like restriction of a quadratic polynomial P, with connected filled set, prime primitive renormalization period n>1, disjoint little cycle L=union(L_j), distinguished central little set K=L_0. Assume a second prime primitive renormalization so that the canonical first renormalization is an instance of §6. In particular use the archive's certified real, critically preperiodic 3/9 tip: [exact phase/root certificate](../../results/tip_root_interval_geometry.json), [physical 3/9 marking certificate](../../results/tip_KKL_tree_marked_breakage_20261109.json) and [analytic input and marking proof](tip_KKL_native_tree_marking_and_marked_wave_breakage_20261109.md), §1. The inherited primitive-type, connected-restriction and Misiurewicz/local-connectivity inputs are analytic, not consequences of a finite transition table. Use a sufficiently large round target disk U (e.g. radius 4 at that parameter), and U^n=P^{-n}(U), the actual iterated source disk.

Set S=U minus L, S'=U^n minus P^{-n}(L). For this ordinary parent the iterated immersion is the inclusion S' into S, since the entire old cycle is contained in its full preimage. KKL §2.3 takes the localizations at K before and after the iterate. Write (V,K_t), (V',K_s) for these genuine localized disks with the distinguished copy of K in each, and j:V'→V for the localized inclusion. The exterior projections pi:V minus K_t→S, pi':V' minus K_s→S' are covers associated to the cyclic subgroups generated by the peripheral loops about K. They satisfy pi j = inc pi' off the distinguished sets. Both projections, and j, identify the distinguished copies bijectively with K in physical coordinates near K. This is Kahn Theorem 7.12, not an extra global injectivity hypothesis.

There is an extra component E of P^{-n}(L) outside L. To see this take a generic point in K avoiding the finite critical values of P^n. It has 2^n preimages in U^n; exactly two are in K, since the central return has degree two; no other old cycle component maps into K under P^n. The full preimage of the finitely many disjoint compact full little sets has finitely many disjoint compact full components. Choose a Jordan loop about one extra component E disjoint from the old and other preimage components. Its based class a in pi_1(S') maps trivially into pi_1(S), because the filled-in E is disjoint from L and its small enclosing disk lies in S. But a has winding number one about a point of E. Every element of the source peripheral subgroup around K has winding number zero about that point.

Let W be the component of pi^{-1}(S') in V minus K_t containing j(V' minus K_s). The map j restricted to V' minus K_s is a covering onto W: over each small simply connected disk of S', both localization covers have homeomorphic sheets, and the commuting inclusion maps each source sheet onto a target sheet. Path lifting proves surjectivity onto that component. At a basepoint of W, lift a^m in the source localization for every integer m. Its endpoints map under j to the same target point, since the target loop is null homotopic; they are distinct because a nonzero power of a cannot belong to the peripheral subgroup (winding about E). Equivalently the index of that subgroup in the inverse image of the target peripheral subgroup is infinite. Transport along paths in W proves:

    j: V' minus K_s → W is an infinite-sheeted covering.

This is an all-point conclusion on W, not just two chosen lifts in a finite tile. A punctured physical neighborhood of K_t is contained in W. The filled-set condition remains true: j^{-1}(K_t)=K_s, with j bijective on K_s. Extra sheets occur in the exterior and are not extra copies of the filled set.

### 1.1 Which §6 hypotheses the 3/9 example meets, and which conclusions are general

KKL §6 (its opening, with §2.5 and §3.1) works with a ψ-ql map F:(U',K)→(U,K) that is periodically repelling, primitively renormalizable (the renormalization prime and primitive) and parabolically b-bounded. T is the Hubbard tree of the small Julia cycle, T'=f^{-1}(T), and U minus T carries the ideal marking by the sides of the tree vertices. In this note F is the canonical first renormalization (V',K_s)→(V,K_t) of the parent P.

| §6 standing hypothesis | Status at the 3/9 tip | Basis |
|---|---|---|
| F is a ψ-ql map | met | F is the renormalization RP constructed in KKL §2.3; this needs the period-3 renormalization of P to be prime and primitive, which is inherited from the archive's certified tip inputs |
| periodically repelling | met | the critical orbit is strictly preperiodic (x_18 = −x_9), so every cycle of P is repelling; inherited certificate plus the standard Fatou count |
| primitively renormalizable | met | second renormalization of relative period 3 with pairwise disjoint small Julia intervals K_0, K_1, K_2; inherited certified geometry |
| K locally connected, so T is defined directly | met | K is a dendrite, T = A = [x_6,x_3], T' = B = [-x_3,x_3]; inherited from PR #74 |
| parabolically b-bounded, condition (1): rotation number 1/q | met with q = 2 | the hybrid class is real and renormalizable of period 3, hence in the 1/2-limb |
| parabolically b-bounded, conditions (2)–(3) | met with b = 3 | there are three small Julia sets and two limbs; for a single map these are finite conditions, and b matters only for uniformity over a family |
| width hypotheses of Lemma 6.1 and Propositions 6.2–6.3, and HTND | not used, not checked | Propositions 6.5–6.6 are stated for the standing F with no width hypothesis, and nothing here concerns width |
| ideal marking (ten target atoms, twenty covering-source atoms) | inherited | PR #74 census, not re-derived here |

No "inherited" row is proved in this note, and none is covered by CI: the finite regression suite and the Lean build do not test them.

Scope of the conclusions:

* **General propositions.** §1 holds for every ordinary quadratic-like parent with connected filled set and a prime primitive renormalization of period n>1: the canonical localized immersion is an infinite-sheeted covering over the exterior region W. The endpoint lemma of §2 holds for every holomorphic immersion between annuli of finite modulus. The no-unique-exterior statement of §2 holds whenever the §6 map F is such a canonical renormalization. It does not hold for an ordinary quadratic-like F with ι an inclusion, where the exterior has one sheet; that is the PR #74 representative.
* **Specific to the 3/9 tip.** The inner-circle nonmaximality of §3, which uses the dendrite K, the slit pair A⊂B, the countable host set E_B and the block J = S_5, and all of §4.
* **Not established in this note.** Any statement for a non-locally-connected K, and any statement about the path selection of Proposition A.12 or the width and crest arguments of §§6.2–6.3.

## 2. Consequence for proper restrictions on the actual next-stage tree annuli

Take the next prime primitive Hubbard tree A in K_t and its full preimage B' in K_s under the canonical degree-two return g. Via j identify B' with B in K_t, with A subset B. The actual surfaces of §6 are M=V minus A and M'=V' minus B'. Their inner ideal circles are C_A,C_B, and M' also has an outer ideal circle O'. The immersion is j, not the embedded restriction used in PR #74. Removing A and B' leaves the exterior covering of §1 unchanged.

**Endpoint lemma.** Every maximal parametrized lift of a proper path in M under the immersion M'→M is proper. In round-annulus coordinates an endpoint of a maximal lift must leave every compact subset: an interior accumulation would permit a local inverse continuation. Its cluster lies on one ideal circle. If it contained two points, connected terminal pieces would traverse a fixed nontrivial angular arc along a sequence tending to that circle. At every angle of that arc the immersion has a radial subsequence tending to the same target coordinate (the target path has a limit at its endpoint or at an interior truncation). Fatou's radial-limit theorem and boundary uniqueness for bounded holomorphic functions on an annulus would force the immersion to be constant. Thus the lift has one limit in the ideal circle at each end. This applies to both ends, including outer ends; neither a finite number of lifts nor a pointwise boundary extension is assumed.

If a target proper path gamma meets W at a time t, choose a point w=gamma(t) in W. Every one of the infinitely many preimages of w in V' minus K_s initiates a maximal lift. The endpoint lemma makes them proper. Even allowing reparameterization, there are infinitely many distinct restriction paths: a single such path can contain only finitely many distinct preimages of w. Otherwise these discrete preimages would accumulate at a proper endpoint. The image path would then approach the interior point w at its truncation time (a proper target endpoint cannot limit to w); eventually it lies in a small evenly covered disk in W, where a single lift must remain in one sheet and continue to an interior point. This contradicts escape to the ideal boundary.

Consequently, if gamma has a unique proper restriction at all, that restriction is entirely in K_s minus B'. Indeed a source point outside K_s would map to W and give infinitely many restrictions. The restriction has no outer endpoint since K_s is compact in V'. In addition gamma itself lies in K_t minus A: if it left K_t after meeting it, it would pass through the punctured neighborhood of K_t contained in W, again violating uniqueness.

The no-unique-exterior conclusion is also valid if the phrase "contained in the inverse image" is read more broadly than maximal parametrized lifts, since the infinitely many maximal proper lifts are included in the broader family.

## 3. Counterexample **on the inner circle**, not just the outer boundary

Use the certified 3/9 tip above. Its canonical renormalization is periodically repelling and its germ is the physical degree-two G=P^3 of PR #74. The canonical filled K is a locally connected dendrite; its next-cycle tree and full preimage, in the actual distinguished local coordinates, are precisely

    A=[x_6,x_3],     B=[-x_3,x_3],     x_j=P^j(0).

This is the existing analytic geometry of PR #74; here the *global* source and target are the canonical disks V',V, with the exterior multiplicity of §1. The inner marking therefore has the same ten original target and twenty covering-source atoms; the outer geometry is not identified with the embedded disks.

The components X of K minus B are relatively open (local connectivity), hence at most countably many. Each closure meets B at a single root (unique arcs in a dendrite). It approaches one of the two slit-side accesses at that root, or the single tip access: for an interior root, approach from both sides would require arcs in X between arbitrarily close points to go around a distant tip, contradicting uniform local arcwise connectedness of the subdendrite closure(X). Let E_B be this countable set of actual host accesses. A proper path in K_s minus B' stays in one component and both its ideal endpoints belong to E_B. By §2 this is true of every **unique** restriction. In particular uncountably many inner accesses can never be an endpoint of a unique restriction. No such access is supplied by a finite matrix.

Choose, for example, the original open target atom I_2, the upper side of [x_9,x_18]. Its geometric attachment pullback J is a single old slit-side arc (S_5 in the physical certificate), with nonempty open complement. The sole added component [-x_3,x_6) has a different host. Choose b in an open arc strictly outside closure(J) and outside the countable set E_B.

Under the printed maximal-subset predicate, if J is admissible, so is J union {b}. Indeed a unique restriction cannot have endpoint b. A path subordinate to J union {b} with endpoints in J is already subordinate to J: given any neighborhood of J, take a smaller one avoiding a small disjoint neighborhood of b; a connected path representative with endpoints in J cannot enter that isolated neighborhood. Therefore adding b creates no new violating unique restriction. If J were not admissible it would also fail to be the prescribed maximal subset.

Thus J cannot be the maximal subset of the actual inner ideal circle, even if the outer circle were silently excluded. This contradicts the literal combination of A.3.2 and Proposition 6.5. There is also a simpler outer defect: adjoining the entire O' to any admissible subset preserves admissibility, since unique restrictions have inner endpoints and subordination can be tested in disjoint inner and outer collars. Every maximal subset contains O', contrary to Proposition 6.5. The inner defect shows that merely restricting the ambient subset to C_B is insufficient.

This argument uses the exact global canonical construction of KKL §§2.2–2.3, the literal uniqueness quantifier on p. 62, and the known native physical tree at a certified parameter. It does **not** rely on the abstract countermodel in PR #39 or the embedded-representative pullback formula whose generalization is being tested.

## 4. Narrow repair in this native locally connected example (reading (L) only)

This section uses reading (L) of §0 throughout: a restriction is an occurrence-indexed maximal parametrized lift, as in the preceding direct path audit. Under reading (T) none of the singleton witnesses below is a singleton, the raw subset is the whole ideal boundary, and the formula for X_raw is not claimed. Let r:C_B→C_A be the physical slit contour collapse: preserve old sides and collapse the entire closed added contour over [-x_3,x_6] onto the old left-tip access. It is not the boundary extension of j over added material.

For every b in E_B, take the actual arc in its component X of K minus B from the root to an interior point, and return along it. If the root lies in B minus A, prepend the arc through the added slit from x_6 and append its reverse; otherwise begin at the old root. The resulting proper target path is in K minus A with both ideal endpoints r(b). Its unique maximal proper restriction is precisely the out-and-back excursion in X, since j is bijective on K and all other portions are in B minus A. It is subordinate to {b}. The target loop is subordinate to an interval I precisely when r(b) belongs to I.

Conversely, by §2 any target path with unique restriction is in K minus A. It stays in one of its dendrite components, whose single host access is r(b) if the unique source restriction has host b in E_B. Both paths have trivial relative winding: the closure of the corresponding component with its single host access adjoined embeds as a dendrite in the ideal compactification, so its based loops are null homotopic; annular collar homotopy gives subordination to the host singleton. Hence for the maximal-parametrized interpretation the raw greatest subset is exactly

    X_raw(I) = O' union (C_B minus (E_B intersect r^{-1}(C_A minus I))).

This formula confirms that for any two different original inner atoms the raw pullbacks overlap at all of C_B minus E_B, as well as O'. It is not a partial marking. The proof of the nonmaximality in §3 does not require the converse or this formula.

The host set E_B is dense. Here is a direct verification, without assuming Proposition 6.5. If some open slit-side arc has no hosts, choose a smaller subarc away from the tips. The attached component closures are a null family: otherwise points in distinct components at distance uniformly bounded below from their roots have a convergent subsequence, but their connecting arcs must pass through their roots, contradicting uniform local arcwise connectedness of K. A sequence of attached points approaching the smaller subarc from its side must therefore either come from one component (giving a host there) or from shrinking distinct components (their roots and one-sided hosts converge to the same subarc). Both are impossible. There is thus a one-sided free collar of the slit containing no other part of K. Local boundary reflection or crosscuts give a nonempty open arc of the *ambient* K prime-end circle landing on B. In the hybrid straightening of G, the external angular map doubles; the hybrid neighborhood homeomorphism identifies these ambient prime-end circles. Every nonempty open angular interval eventually covers the ambient circle. The landing map is continuous and onto K, so a finite iterate of B would contain K. But G(B)=A, A is forward invariant, and A is strictly smaller than K (the certified K_3 contains a non-real cross). Contradiction.

By density, for an open proper I with distinct marked endpoints, **the greatest relatively open admissible subset of the inner circle** is r^{-1}(I). Any open set adding an exterior point, including an exterior extreme gate, would contain an excluded host witness. For a positive proper closed I, the greatest connected closed nondegenerate admissible inner interval is r^{-1}(I); any larger such interval would contain an excluded host in an exterior open arc. Equivalently for these inputs, take the inner interior of X_raw(I) in the open case, and the closure of that inner interior in the closed case. This recovers the ten geometric blocks, their correct endpoint births and the source-derived edge incidence in the canonical native example without the unrestricted maximal-subset claim. A punctured circle with a single omitted zero-fiber cut needs separate endpoint bookkeeping (regularization might fill it); in this slit its degree-two covering image saturates either way.

**Proposed source correction:** specify connected inner intervals of the same open/closed type in the interval restriction, or give the actual geometric contour operation directly. The present proof validates that correction for this canonical LC slit. It does not establish it for arbitrary non-LC fibers or prove that all analytic path-selection and width arguments remain valid after the definition is corrected.

**The repair is specific to this locally connected slit.** The one-host-per-component statement, the density of E_B and the contour map r all use that K is a dendrite and B a real slit. Nothing is asserted for non-LC fibers, where a host need not be a single access. The repair says nothing about which restrictions Proposition A.12 selects for a marked path, and it re-proves no width or crest statement of §§6.2–6.3 or Lemma 6.4 under the corrected definition.

## 5. Review disposition

This is a focused first-failure certificate under the literal printed quantifier, not a new claim of closure of the corrected global theorem. The crucial review questions are whether the intended uniqueness was global in the entire proper restriction family (as the displayed text states), and whether some additional restriction on the eligible subsets was intended but unstated. The counterexample disappears if one changes the definition to the connected geometric interval, which is exactly why those alternatives must be distinguished. No CI result or independent specialist review is asserted. Keep the issue and relevant ledger entries open pending independent checking; do not infer that the MLC theorem is false.

**Response to the PR #119 review (2026-11-25).**

1. *Trace family versus maximal lifts.* Separated in §0. §4 is restricted to reading (L). §3 is recorded as holding under both readings, trivially under (T).
2. *Hypotheses and scope.* §1.1 lists the §6 standing hypotheses against the 3/9 example and separates general propositions from example-specific conclusions. A specialist check of the canonical localization (§1), the endpoint lemma (§2) and the inherited slit and primitive-type inputs has **not** taken place. The non-specialist re-read of 2026-11-25 found no error in §§1–3 and one point that deserves a specialist's eye. §1 takes the exterior of the localization to be the cover of U minus L for the cyclic peripheral subgroup about K. The other candidate, the universal cover of U minus (L minus K), would make the lifted inclusion carry further lifts of K onto the distinguished one, because a loop about an extra preimage component E is trivial in the target; that contradicts the ψ-ql requirement ι^{-1}(K)=K' of KKL §2.1. So the cyclic reading is the one consistent with the definition, but it should be confirmed against Kahn §7.4 by someone who knows that construction.
3. *LC-specific repair.* §4 and the proposed source correction are confined to this locally connected slit. Still open and untouched by this note: non-LC fibers, the path selection of Proposition A.12, and the width and crest arguments of §§6.2–6.3 and Lemma 6.4 under a corrected definition. The eight companion notes of this PR each carry a status banner saying that they are historical, conditional or a separate special case.

No ledger entry is promoted and Issue #40 stays open. Nothing here bears on the truth of the KKL theorems or of MLC.
