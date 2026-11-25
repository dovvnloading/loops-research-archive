# Issue #40: continuum sector escape, side-weight growth, and closed crests at the physical 3/9 tip

> **Status (2026-11-25): separate special case.** This note concerns the embedded physical representative G:V_3→U_3, whose immersion is the inclusion, under the maximal-parametrized-lift reading of restriction stated in §2. That is reading (L) of the [canonical-localization certificate](issue40_canonical_localization_uniqueness_failure_20261124.md), §0; compare the occurrence-indexed convention of [the selected-slit note](immersion_mark_resolution_20261124/NOTE.md). It is not a statement about the canonical localization, whose exterior is infinite-sheeted and where the same pullback identity fails as printed. Whether KKL's restriction agrees with reading (L) is a source-identification question that is not settled here. No ledger entry is promoted, Issue #40 stays open, and there has been no specialist review.

2026-11-24. Written analytic continuation of merged [PR #74](https://github.com/dovvnloading/loops-research-archive/pull/74), **not a general non-LC KKL proof**. No new synthetic interval automaton, numerical simulation, or ledger change.

## 1. Source and imported hypotheses

Source: Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §§2.1, 2.3, 2.5, 6.1, especially Propositions 6.5–6.9; Appendix A.1 (marking, wave and crest), A.3.2 and A.3.4 (restriction versus cover and closed action). The latter explicitly warns that open-image closure and closed-input image may differ.

Use the existing physical degree-two map G=f_c^3:V_3→U_3=D(0,1/4), with f_c(z)=z²+c, at the certified parameter in [the merged attachment audit](issue40_native_attachment_edge_incidence_20261115/NOTE.md). All notation x_j=f_c^j(0), K_0=[x_9,x_18], K_1=[x_12,x_3], K_2=[x_6,x_15], T=[x_6,x_3], T'=[-x_3,x_3], and the ten target/twenty covering-source atoms is that audit's. We import its analytic quadratic-like restriction, real dendrite/slit identification, original marking and exact physical edge traces (the interval-pullback identification is now proved directly in §2). We also import the existing analytic straightening of the connected inner restriction f_c^9=G^3 on K_0 to z²−2; see [root interval certificate](../../results/tip_root_interval_geometry.json), notably the normalized inner parameter and orbit. These are analytic inputs, not inferred from passing arithmetic tests. In particular the hybrid conjugacy restricts to a homeomorphism of the two actual filled Julia intervals, conjugating their first-return maps. The small Julia cycle is K_0→K_1→K_2→K_0.

All results below concern this particular native physical representative. They do not assume a global prime-end quotient for a wild carrier, a boundary extension of an immersion at a newly attached component, or representative-independent path restriction counts.

## 2. Real slit contour and a precisely typed extension to finer sectors

Write C=[T]^pe and C'=[T']^pe for the inner ideal circles, using the actual annuli U_3\T and V_3\T'. Let π:C→T and π':C'→T' be landing maps. Each is a doubled real interval: two distinct accesses to each interior point, with the two ends glued at each tip. For example, the exterior of a real segment [a,b] is uniformized by the Joukowski map (a+b)/2+(b−a)(w+w^{-1})/4 for |w|>1; the smaller annular neighborhoods have the same inner access circles. This describes actual crosscut approaches, not an abstract tree isomorphism.

There is a *contour code* r:C'→C defined on the actual doubled slit as follows:
- On the upper/lower copies of (x_6,x_3), retain the same physical point and side; retain the single right-tip access.
- Collapse the entire closed added contour B_X over [-x_3,x_6], including the two distinct source x_6 gates, onto the unique old left-tip access a over x_6.

The order of the doubled slit makes r continuous, orientation-preserving and monotone (connected fibers). This assertion is confined to this real slit: on the interior of the added contour the inclusion immersion takes a source-boundary approach to the target *interior*, not to a. Thus r is not a pointwise extension of the holomorphic immersion. Its nontrivial fiber is B_X, with interior source atoms S_19,S_0,S_1. All original marked cuts are different from a; a is strictly inside I_0. At each original marked cut there is exactly one source access in its r-fiber. This follows from the actual slit topology and marked gate census in PR #74.

Let p:C'→C be the genuine degree-two annular covering G_* of §6.1, not r. In particular π' and π satisfy

    π∘p = G∘π'.

For a connected open or closed access arc D (or the whole circle), define the explicit **slit-contour extension**

    Ψ(D) = p(r^{-1}(D)).

**Direct audit of the pullback (independent of Proposition 6.5).** The earlier version imported the attachment-union conclusion from Proposition 6.5. That is insufficient for an independent test of that conclusion. We can instead prove the identity from Appendix A.3.2 for this embedded quadratic-like representative. Interpret restrictions as maximal parametrized lifts of subpaths, as in the restriction operation used by Proposition A.12, rather than arbitrary proper paths whose images happen to lie in a path trace. KKL §1.4 permits proper paths with coincident ideal endpoints; the marking exclusions of Appendix A.1 are not imposed on the proper-path test defining the subset in A.3.2.

First, a useful endpoint fact: every maximal lift of a proper target path under a holomorphic immersion between finite-modulus annuli is proper. Work in round-annulus coordinates on both surfaces. At either endpoint of its maximal parameter interval the lift must escape compact subsets, since otherwise a local inverse at an interior cluster point would extend it (or the target would approach its ideal boundary from an interior image point). Its cluster set lies on one boundary circle. If it contained two points, angular projection of the connected terminal pieces of the lift would traverse a fixed nontrivial arc along a subsequence approaching that boundary. On each angle of that arc there would be a radial sequence at which the bounded holomorphic immersion tends to the endpoint value of the target path. That endpoint value exists in target round-annulus coordinates, even at an interior truncation time. Almost-everywhere radial limits and boundary uniqueness for bounded holomorphic functions would force the immersion to be constant. Thus the lift has one ideal limit at each end. This argument uses only the standard Fatou and Privalov boundary theorems, not Proposition 6.5.

Put J=r^{-1}(D). To show that J satisfies the implication in A.3.2, let a target proper path gamma have exactly one proper restriction gamma' subordinate to J. The inclusion has no other sheets. By the endpoint fact each component of the times for which gamma lies in the source complement is a proper restriction. Hence there is exactly one such component, the parameter interval of gamma'. At an interior endpoint of gamma' its landing is on T', not the outer boundary of V_3, because gamma' has both ideal endpoints on J in the inner boundary. The portions before or after gamma' (if present) therefore lie entirely in the real attachment T' minus T: leaving that attachment without entering the source complement is impossible since T' is compactly contained in V_3. Both target endpoints are on the inner circle.

Let A(z) be the unit angular coordinate of the Joukowski inverse for T. On the target annulus it is a degree-one angular retraction; it extends to the identity in the corresponding inner-circle coordinate. The real added slit lies on its single radial ray, so A is constant on the attachment, equal to a in those coordinates. On the source annulus A composed with the inclusion extends continuously at the inner ideal circle with boundary values exactly r (old sides and the two x_6 gates have their stated limits). Therefore the angular class of gamma is the angular class of gamma' composed with this map, with constant initial and terminal pieces. Since gamma' is subordinate to J, that class is subordinate to D. In an annulus, the relative homotopy class of an inner-to-inner path is determined by its lifted endpoints in the angular universal cover; being subordinate to a connected proper boundary arc means that both endpoints and their connecting lifted interval lie in a single lift of that arc. The same statement for the whole circle has no winding restriction. Thus gamma is subordinate to D. This proves admissibility of J, including open and closed inputs and the punctured-circle case.

To prove greatestness, test **each individual excluded prime end** b of the source. If b is on the inner circle with r(b) outside D, choose a small contractible proper loop based at b in the ideal collar of the source. Its two endpoints coincide at b, so it is subordinate even to the singleton {b}. If b lands on the old slit, the inclusion of this loop is a target proper path based at the old access r(b). If b lands strictly on the added slit, prepend the real segment from x_6 to that landing point and append its reverse. Those segments lie in the target but outside the source, and start and finish at the old tip access a. At either gate over x_6 the first construction applies. In every case the loop is the unique maximal proper restriction, and the target path is not subordinate to D because its endpoint r(b) is excluded. No admissible subset in the A.3.2 test can therefore contain b, even as an isolated point. If b is instead a source outer prime end, use an exterior arc from the target outer circle to its landing point on the Jordan boundary of V_3, a small proper source loop based at b, and the reverse exterior arc. Again the sole restriction is the loop, but the target endpoints are outer, outside D. This excludes the whole source outer circle as well. The Jordan-domain input here is the actual compactly contained quadratic-like representative of PR #74, not a claim about a general immersed outer boundary.

We have proved that J satisfies the test and every admissible subset is contained in J. Thus J is the greatest subset, not merely an inclusion-maximal candidate. It follows directly that

    ι*D = r^{-1}(D),   F_*D = Ψ(D) = p(r^{-1}(D))

for every nonempty connected open or closed inner access arc of this real slit (also the whole circle). In particular the original marking, the omitted-root endpoint, the closed-root birth, and arbitrary refined subarcs pass the actual proper-path test. This does not turn unmarked arcs into source-marked Waves. It also does not establish the same identity for a noninjective immersion: the exclusion loops can acquire additional proper lifts on other sheets, in which case the uniqueness antecedent in A.3.2 is unavailable. That is a concrete limitation, not a new assumed contour identity.

Ψ is inclusion-monotone, preserves connectedness, and sends the whole circle to the whole circle. For any D in its domain,

    G(π(D)) ⊂ π(Ψ(D)).                                      (1)

Indeed for each e∈D choose an old source access e' landing at π(e), with r(e')=e. At a choose either of the two x_6 gates (not an arbitrary added point). At the other old tip choose its single source access. Then p(e')∈Ψ(D) and lands at G(π(e)). Iteration of (1) gives G^n(π(D))⊂π(Ψ^n(D)) for every n. No pointwise holomorphic boundary identification of r is used.

## 3. Analytic zero-sector escape for arbitrary positive slit subarcs; no uniform subatomic bound

**Theorem A (physical slit extension).** Every nondegenerate connected open or closed sector D contained in a zero-old-edge atom (I_0,I_2,I_5,I_8, or its closure) eventually contains, under Ψ, a complete marked old edge side and then saturates. This includes arbitrarily small genuine access subarcs, not just the four whole original atoms. The escape time cannot be bounded uniformly over all such subarcs, even at this one parameter.

Proof of eventual escape. The physical landing projection of a nondegenerate arc of a doubled real interval contains a nondegenerate real interval. Take a nondegenerate closed interval J in the interior of π(D)∩K_j; even when D contains a tip, choose J in one of its real-side interiors. Moving at most two steps along the cycle (if starting in K_1 or K_2) produces a nondegenerate interval in K_0: each of those two branch maps is a homeomorphism. By (1) the corresponding landing projection of the iterated Ψ-image contains this interval.

The first-return map H=G^3|K_0 is conjugate to Q(x)=x²−2 on [-2,2] by the imported straightening. With x=2 cos(πt), t∈[0,1], Q is conjugate to the full tent map t↦2t on [0,1/2] and t↦2−2t on [1/2,1]. Each closed dyadic interval [k/2^s,(k+1)/2^s] is mapped by the s-th tent iterate onto [0,1], as follows inductively from its two full branches. Every nondegenerate interval contains one such dyadic interval. Consequently some H^s maps the real interval under consideration onto K_0. This is a continuum exactness proof, not finite marking orbit enumeration.

Two further G-steps map K_0 onto K_2. By (1), for some m the landing projection π(Ψ^m(D)) contains all K_2, hence contains x_6. There is exactly one target access over x_6, namely a, so a∈Ψ^m(D). The next r-pullback contains the **whole closed** B_X (not merely one representative gate). Its covering image contains I_9,I_0,I_1, hence contains complete old E_20 side atoms. Moreover Ψ(I_0) has the open consecutive word (I_8,I_9,I_0,I_1,I_2); its full source block at the next pullback has 1+2+5+2+1=11 covering atoms. A degree-two covering of the circle with ten target atoms maps eleven consecutive full covering atoms and their interior cuts onto C, not merely onto C minus a cut. Thus Ψ²(I_0)=C. By monotonicity Ψ^{m+3}(D)=C.

Explicit nonuniformity / adversarial small-sector check. The Chebyshev map has the interior fixed point -1, which is not critical. Its physical conjugate y∈int K_0 is fixed by H. Its G-orbit lies in the three small Julia interiors: an endpoint at either of the other two phases would return to an endpoint of K_0, contradicting H(y)=y in the interior. It is noncritical since the only critical point of the degree-two G is 0 and H(0) is an endpoint. Either prime-end side over y follows an orbit of old accesses wholly inside the zero-edge atoms; the side can flip, which does not affect the argument. No point on this finite physical orbit is an attachment root or a marked cut. Near each access r is locally a homeomorphism (indeed exactly the same real point and side), and p is a local homeomorphism. Given any integer N, choose small neighborhoods of the first N+1 accesses inside their corresponding zero-edge atoms. By continuity of the finite composition of these local maps, there is a nondegenerate closed subarc D_N about the initial access, contained in the first neighborhood, whose first N iterates all remain in those neighborhoods. This gives proper, zero-edge Ψ-images for N steps; it is not a sampling argument. The eventual escape proved above does not contradict this: its dyadic cylinder depth depends on the starting sector.

The narrow corrected statement for finer physical sectors is **eventual escape with a size-dependent time, not a uniform time bound over arbitrary subatomic sectors**. This is not a counterexample to KKL Proposition 6.9 for its original marked multi-intervals or to bounded critical visits of actual short Waves. It prevents using a stronger arbitrary-subarc uniform time hypothesis without an extra lower size or native full-marked-atom condition.

## 4. Proper side-weight expansion from the *same* physical source; a separate support counterexample

Define d_e(D) as the number (0,1,2) of complete open old prime-end edge-side atoms of type e in D, and d as a column indexed by (E_20,E_0α,E_α1). This is a side-occurrence count, not a count of distinct physical edge names, not a WAD valuation, and not the measure of a path representative. The old physical edge words and the output-row/input-column matrix from PR #74 are

    T_F = [[0,0,1],[1,0,1],[1,1,0]],
    w=(φ,1,φ), φ=(1+sqrt(5))/2, w T_F=φ w.

**Theorem B (same-slit side expansion).** For a connected original open multi-interval or its closure D, if Ψ(D) is not the whole circle, then

    d(Ψ(D)) ≥ T_F d(D),   w d(Ψ(D)) ≥ φ w d(D).

In particular the second inequality is strictly increasing when w d(D)>0.

Proof. Each complete old edge-side atom in D is represented in r^{-1}(D) by its actual same-side interval over that physical edge (possibly subdivided by the covering marking). The real edge traces of PR #74 give exactly one full corresponding target side for each occurrence of an output edge in the old physical image word. This uses the real derivative sign on the entire edge and the distinct upper/lower accesses; an intervening vertex gap contributes no edge. Every occurrence comes from this same r-pullback and p-image, not an independently chosen finite edge matrix. The source r-pullback is a connected arc. Since p is a circle covering of degree two, a proper nonsaturated image forces p injective on the arc: in angular coordinates where p doubles, an open arc of length greater than a half-turn or a closed arc of length at least a half-turn already maps onto the entire circle. An open half-turn maps onto a punctured circle injectively. Thus distinct old source side occurrences cannot share a target access in a nonsaturated image. This proves the componentwise inequality, and the left Perron identity gives the weighted inequality. Added attachment-side occurrences may only increase it. The proof counts both distinct physical sides when appropriate; it does not count the two sides as two separate physical graph edges in the definition of T_F.

**Native support-count counterexample.** Take the proper original marked interval D=(I_1,I_2,I_3,I_4), where the notation includes the internal cuts. It contains one side of each of the three old edges. Its actual source block has 2+1+1+3=7 covering atoms, with proper image (I_3,I_4,I_5,I_6,I_7,I_8,I_9). That image contains each of the same three edge *names*. The weight of the set of distinct physical edge names is therefore identical before and after, namely 2φ+1. Strict growth of that deduplicated support weight is false. It is precisely the side-occurrence multiplicity, not deduplicated support, that has the asserted Perron inequality.

A simple non-enumerative saturation bound follows: w d(D)≤2(2φ+1) for every arc, and any nonzero w d(D)≥1. Five successive nonsaturated steps after a positive side mass would give mass at least φ^5=5φ+3>4φ+2, impossible. Every full zero-edge atom acquires an edge or saturates within three steps by the prior physical census. Hence all nonempty original marked multi-intervals saturate within eight steps, even without enumerating all ten saturation times.

This is no-collision for *actual ideal side occurrences on the slit*. It is not no-cancellation for arbitrary immersed path restrictions in the pseudo-ql category or an extremal-width estimate.

## 5. Exact closed-crest action and sharper marked bound in this representative

No marked endpoint equals the sole nontrivial-fiber target access a. Since r is a homeomorphism off B_X, for every original proper open marked multi-interval I one has

    r^{-1}(closure I) = closure(r^{-1}(I)).

At an exterior endpoint of I its r-fiber is a singleton approached from the included side; all interior fibers, including B_X if present, are included in their entirety. This proves equality, rather than assuming it for a general immersion. The covering p is continuous on the compact source circle, so p(closure J)=closure(p(J)) for all J. Therefore

    F_*(closure I) = closure(F_* I)                         (2)

in this one marked model, including the open-half-turn/punctured-output case (closing the puncture may saturate). Intermediate open images are again original marked multi-intervals, so (2) iterates. If a finer cut is instead placed at a, the r-preimage of its endpoint includes all B_X, while a one-sided open interval approaches only one of its gates; (2)'s *pullback* equality then fails. This is the precise endpoint-loss mechanism ruled out by the original marking at this tip, not an argument for the general source equality.

For completeness the original PR #74 physical words give a sharper bound of five steps for all nonempty open marked multi-intervals. Here is a compact derivation using just monotonicity and the already-derived source blocks (not a new finite model). Starting at each atom, the last proper open image before saturation has the following block; the displayed source atom total is strictly greater than ten, so its next image is the whole circle, including every cut.

| initial atom | last proper block (cyclic inclusive atom indices) | next source count | first full-circle step |
|---|---|---:|---:|
| I_0 | 8,9,0,1,2 | 11 | 2 |
| I_1 | 1,…,7 | 12 | 4 |
| I_2 | 8,9,0,1,2 | 11 | 4 |
| I_3 | 6,7,8,9,0,1,2,3 | 16 | 5 |
| I_4 | 7,8,9,0,1,2,3,4 | 16 | 4 |
| I_5 | 8,9,0,1,2 | 11 | 3 |
| I_6 | 6,7,8,9,0,1,2,3 | 16 | 4 |
| I_7 | 7,8,9,0,1,2,3,4 | 16 | 5 |
| I_8 | 8,9,0,1,2 | 11 | 4 |
| I_9 | 3,…,9 | 12 | 4 |

Any nonempty original marked interval contains a full atom; all marked closures contain their open cores. Thus by monotonicity and (2) every such interval or closure saturates within five steps. For an actual Wave with a nonempty crest C_0 equal to the closure of a connected positive marked block, suppose there is a chain of source-defined critical visits with connected, positively marked closed crests C_j and exponents m_j≥1, so F_*^{m_j} C_{j-1}⊂C_j (the definition in §6 before Proposition 6.3, with "wave over" typed by A.1). Iterating monotonicity yields F_*^{m_1+…+m_j} C_0⊂C_j. At five transitions the left-hand side is the entire inner circle. A Wave crest cannot contain the entire circle since its nonempty marked ends are excluded. This bounds such actual positive connected crest chains by four successor transitions in the physical model. Neither an arbitrary pushed child nor a disconnected or zero-core crest is silently assigned the critical-visit inclusion. There is no claim of a universal shortness or width-amplification estimate.

## 6. Literal maximal-length endpoint case in Proposition 6.9

As written, A.1 permits a connected open multi-interval that omits just one marked cut from a circle. In the physical tip choose such an I, omitting any of the ten original cuts. Its length is ten. Its actual r-pullback omits one source cut (no original cut has a nontrivial fiber); the genuine degree-two covering maps that set onto the entire target circle. All subsequent iterates are the circle, still of length ten. Every iterate meets the critical limb, so for n≥6b+9 the literal visit-count hypothesis of Proposition 6.9 holds but its strict length conclusion fails. The entire-circle initial state is an even simpler instance. This is a genuine native *maximal-length/saturation* counterexample to the unqualified wording, not a failure in the short proper length regime used for Lemma 6.4. A necessary wording correction is to allow the alternative of saturation or restrict the claim to initial length strictly less than the total number of marked atoms. In this physical model the latter version follows from the five-step saturation bound (b≥1 and a positive initial length give n≥6 from the visit count). This is not a proof of that corrected general theorem.

## 7. Verification boundary and remaining general theorem

The proof above uses the existing real-slit, connected quadratic-like, Chebyshev straightening and physical marking geometry as analytic premises. The identity of the full interval pullback with the contour code is proved in §2 directly from the maximal-path test, without importing Proposition 6.5. The dyadic-cylinder argument, local periodic-access obstruction, same-source side inequality, endpoint-fiber equality and saturation corollary are written proofs, not kernel formalizations. The sharp marked bound is a short cross-check of the existing native source words; it is not evidence for a general non-LC atlas. Hostile checks to apply: do not identify x_6's two source gates; do not count an open half-turn as the full circle; do not drop the nontrivial r-fiber from a closed cut at a; do not assign positive old-edge charge to an arbitrary positive-width Wave; do not apply the arbitrary-subarc nonuniformity result to the original fixed marking; and do not call the support-weight failure or maximal-length case a counterexample to the proof-used short regime.

The general Issue #40 acceptance remains unmet. In particular:
- Need a real non-LC contact/access atlas or equivalent proper-path argument for general exceptional interfaces. The real-slit r is not a construction for those wild carriers.
- Need actual same-path noncancellation and a dual-edge witness for hypothetical proper critical returns, not merely the side-occurrence inequality on this slit.
- The general zero-sector gate transfer and closed-crest transport (including actual proof-selected canonical Wave families) remain open, as does uniform width amplification.
- No specialist independent verification or new CI result is asserted.

Keep Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, H1–H4, UPTCR and MLC open. This note isolates a complete continuum argument and an explicit obstruction in the physical representative without promoting the global research ledger.
