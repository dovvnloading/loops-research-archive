# Source-level Kahn–Lyubich 3/9 tip audit: explicit first puzzle and two actual localization collisions

**Audit date 2026-11-06; issue #29.** This note pushes the *same-parameter* Kahn–Lyubich (KL) construction beyond abstract 3/9 polynomial-like domains. It identifies the **first ambient and second polynomial-like α-puzzles and decoration stops**, proves exact rational real brackets for its vertices and critical escape, and realizes the already-proved canonical-localization noninjectivity theorem **separately** at the physical period-3 and period-9 primitive returns. It also gives a **point-level first failure** of the most obvious 9-to-3 map of the corresponding *deleted* surfaces. It **does not** construct the complete 9-to-3 localization sheet/prime-end natural transformation asked for in #29; that issue must remain open.

**Proof trust.** Finite rational and signed 2^-224 interval statements are recomputed by [TipKLPuzzle.lean](../../TipKLPuzzle.lean), the new [exact Python test](verify_tip_kl_puzzle.py), and the previously merged [TipComplexMargins.lean](../../TipComplexMargins.lean). Intermediate-value, Rouché, polynomial-like connectedness, PCF ray landing, puzzle topology, covering-space, and the written source theorems are *imported classical analytic/topological results*, **not Lean-formalized**. The named fixed-point ray identifications and puzzle graph conventions also require independent expert scrutiny. All global MLC proof statuses remain unchanged.

## 1. Source, definitions, and the distinct clocks

Primary source: J. Kahn and M. Lyubich, [*A priori bounds for some infinitely renormalizable quadratics: II. Decorations*](https://www.math.stonybrook.edu/preprints/ims06-06.pdf), **§2.1, printed pp. 5–6; Lemma 2.1 on p. 6; §2.2, printed pp. 7–8**. This audit uses **that** source's notation.

* The *top* Yoccoz puzzle uses the dividing fixed point α, whose rays rotate by combinatorial rotation number **1/q** in this real case. The first decoration escape depth is the **least** positive integer n for which f^{qn}(0) lies in the **interior** of an off-critical depth-one piece Z^1_κ, not merely any point outside Y^1.
* Once n is known, **P=Y^{(n−1)q+1}**, **V^0=Y^{nq+1}**, and the two univalent f^q-pullbacks **Q_L,Q_R** of P have **depth nq+1** and attach at α,α′=−α. Lemma 2.1 produces 2^n pairwise disjoint *closed* pieces Q^v inside P of depth (2n−1)q+1, univalent under **f^{nq}**.
* The *terminal* primitive period **p** of the modified principal nest (§2.2) is a **different clock**; in the current testbed it is represented by the known period-three restriction f³ and later period-nine restriction f⁹. There is no source identity q=3 or nq=9. The 9-to-3 physical difference is **f⁶**, whereas the *first* top-puzzle branch time is **f²**.

The earlier [source-verification note](paper2_decorations_source_realization_20261105.md) explains why replacing q indiscriminately with nq corrupts the root arrow, while treating the two source clocks as identical would be worse.

## 2. Exact actual parameter and top dividing ray labels

Let f(z)=z²+c_tip, with c_tip the unique root of P₁₈(c)+P₉(c)=0 in

\[
\left(\frac{-607918036626757496169199575185708826140}{2^{128}},
      \frac{-607918036626757496169199575185708826139}{2^{128}}\right).
\]

The [tip audit](period27_misiurewicz_tip_ray_access_20261106.md) proves strictly preperiodic critical dynamics (preperiod 10, repelling period 9), and the [complex audit](nonattracting_tip_complex_two_scale_20261106.md) proves two **primitive** physical quadratic-like restrictions f³:V₃→U₃ and f⁹:V₉→U₉, with connected full little filled Julia sets K₉⊂K₃, strict disjoint phase cycles, and **U₃=D(0,1/4)**, **U₉=D(0,1/32)**.

At this real quadratic c∈(−2,−3/4) the **dividing α-fixed point** is the negative root of z²−z+c=0; α′=−α is its second f-preimage. The standard real-quadratic α ray portrait has ambient rays **1/3 and 2/3** landing at α, cyclically exchanged by doubling; this is the q=2, rotation-number 1/2 case of the fixed-point ray theorem used by KL §2.1 and Milnor *Dynamics in One Complex Variable*, §18. The positive fixed point β has the ray 0. The other two rays landing at α′ are **1/6,5/6**, derived from f^{-1}(α) and the location of α versus α′.

For **the precise real tip**, exact orbit inequalities yield

\[
 7/8<\alpha'<1,\qquad 1<x_2=f^2(0),\qquad 0<x_3=f^3(0)<1/4.
\]

The right depth-one puzzle piece **Z^1_κ** is the component attached at α′ with positive real interior to the right of α′. Since α′<x₂<β, and the orbit is bounded and avoids all α-preimages, **x₂∈int Z^1_κ**. Thus the smallest KL escape index is **n=1**, and the actual source top-puzzle data are

\[
\boxed{q=2,\quad n=1,\quad P=Y^1,\quad V^0=Y^3,\quad
\operatorname{depth}(Q_L)=\operatorname{depth}(Q_R)=3,\quad nq=2.}
\]

Here P has exactly two source vertices **α and α′**. The two **distinct** closed pieces Q_L=Q^α and Q_R=Q^{α′} are given by **KL Lemma 2.1** and attach at those respective vertices, while V^0 occupies the critical middle gap (KL Figure 2.1). Their closed disjointness **comes from the named source lemma**, not from the generic assertion that open pullback components do not meet.

### The first critical Jordan piece and rational ray/access table

Define b_-<0 to be the negative real root of f(b)=α′ and let t>0 solve f(t)=b_-; then f²(t)=α′ and f³(t)=α. The exact rational checks show

\[
 5/16<t<7/16,\quad
 \text{and the other central vertex is }-t.
\]

The boundary vertices of the critical piece V^0=Y³ are **−t and +t**, and f³ sends each to α. Truncate each source external ray at an ambient positive equipotential as KL §2.3 prescribes. Standard PCF local connectivity, real symmetry and the orientation-preserving Böttcher conjugacy give actual landing in the following table; the modular angle arrows are checked separately, with their **geometric** landing left explicitly attributed to those classical inputs.

| Actual point / role | Physical ambient rays (strict cyclic pairs) | f-ray image | Puzzle role / depth | Prime-end side |
|---|---|---|---|---|
| β, positive fixed point | 0 | 0 | non-dividing fixed point; not a P vertex | not assigned |
| α, negative dividing fixed point | 1/3, 2/3 | exchanged | **P=Y¹** vertex, KL q=2 | separate KL O/ξ/η marking not built |
| α′=−α | 1/6, 5/6 | 1/3,2/3 | **P=Y¹** vertex, root of Q_R | not assigned |
| b_-<0, f(b_-)=α′ | 5/12, 7/12 | 1/6,5/6 | intermediate depth-two prevertex | not assigned |
| −t, f³(−t)=α | 7/24, 17/24 | 5/12,7/12 | **V⁰=Y³** left vertex; adjacent to Q_L | not assigned |
| +t, f³(t)=α | 5/24, 19/24 | 5/12,7/12 | **V⁰=Y³** right vertex; adjacent to Q_R | not assigned |
| 0, critical point | 116791/523264, 144841/523264, 378423/523264, 406473/523264 | critical-value pair | protected actual ray accesses, **not a puzzle vertex** | no KL side transport |
| x₁₈∈K₉ | 114/511, 397/511 | doubled periodic pair | phase-9 little Julia boundary; **not a P vertex** | distinct Π₃, same Π₉ |

The **two Q pieces have depth 3** but attach at α and α′ (P vertices), **not at ±t** (V⁰ vertices). The cyclic order on the circle for the first five nontrivial pairs is checked exactly by rational comparison in the Python test. The labels O/ξ/η are the additional **Paper-2 based localization markings** and are **not** secretly inferred from upper/lower half-plane appearance. The table does not purport to enumerate every ray at every puzzle vertex of higher depth.

Since K₃⊂D(0,1/4), while the only Julia vertices on ∂Y³ are ±t with |t|>5/16>1/4, K₃ is disjoint from ∂Y³: the remaining ray/equipotential arcs are outside K(f) altogether. Connected K₃ contains 0, so it lies in **int(Y³)**. On the real line the critical piece is bounded by −t,t and the two earlier critical orbit points x₁,x₂ lie outside; x₃∈K₃⊂int(Y³). Thus the **first return of 0 to Y³ occurs at time 3**. This is consistent with the certified primitive period-three return and supplies the initial modified-nest first child, but the *full* named KL stopping nest, with its exact terminal extension/marking, has **not** yet been identified with the round disks V₃,U₃. This is a remaining gate, not an implied equality of two domains.

### The second top puzzle: apply KL to the actual quadratic-like g=f³

The next scale is **not** obtained by simply relabeling the ambient f-puzzle. Apply KL §2.1 anew to the previously certified degree-two polynomial-like germ

\[
G=f^3:V_3\to U_3,\qquad R(G)=G^3=f^9:V_9\to U_9.
\]

External angles for this **second** puzzle are **G-internal angles**, defined by straightening G and, on qualifying ambient external rays, by the already established **Levin map Π₃**. They are not arbitrary degree-eight ambient rays. This is the correct source distinction between the first- and second-stage return clocks.

**A second exact real source certificate.** The function G is real and even, with a strict **local maximum at 0**. (The quadratic coefficient a₃<0 from the existing complex expansion.) The dividing repelling fixed point of its real quadratic-like straightening is a **positive** fixed point a of G (the coordinate orientation reverses relative to z²+c). Strict rational tests give

\[
G(3/32)>3/32,\quad G(1/10)<1/10
\quad\Longrightarrow\quad
3/32<a<1/10,\quad G(a)=a.
\]

The derivative is strictly less than −1 throughout a coarser interval (1/16,1/8), checked by the Python interval method; it is repelling. Since G is even, its **other** central preimage of a is α′_G=−a. As at the ambient scale, the standard *internal* dividing fixed point ray portrait has **1/3 and 2/3** landing at a, so **q_G=2**.

Let b_G>0 be a real solution of G(b_G)=−a, and let t_G>0 solve G(t_G)=b_G. Six new exact dyadic/rational inequalities (independently checked in both [Lean](../../TipKLPuzzle.lean) and [Python](verify_tip_kl_puzzle.py)) give

\[
\begin{aligned}
&G(17/100)>-3/32,\qquad G(7/40)<-1/10,\\
&G(1/32)>7/40,\qquad G(1/16)<17/100.
\end{aligned}
\]

By IVT, they produce

\[
17/100<b_G<7/40,\qquad
1/32<t_G<1/16,\qquad
G^2(\pm t_G)=-a,\quad G^3(\pm t_G)=a.
\]

The exact critical orbit obeys **G²(0)=x₆<−1/10<−a**, and G(0)=x₃>1/16. Relative to the *G-internal* real α-puzzle, the first q_G=2 critical return therefore already lies in the **interior of the off-critical depth-one piece** attached at α′_G (the other side from the ambient f-puzzle). Its least KL decoration escape index is **n_G=1**.

The actual source pieces at the second scale are therefore

\[
P_G=Y_G^1,\quad V_G^0=Y_G^3,\quad
Q_{L,G}=Q_G^{a},\quad Q_{R,G}=Q_G^{-a},
\quad\operatorname{depth}(Q_{\bullet,G})=3.
\]

KL Lemma 2.1 supplies pairwise disjoint source branches **under G²=f⁶**; this is the internal symbolic two-step clock, **not** the true primitive **G³=f⁹** quadratic-like return. The critical central Y³_G vertex pair is **±t_G**. The internal rays at a,−a have angles 1/3,2/3 and 1/6,5/6; the next two-generation internal pullbacks give the 5/12,7/12 and 5/24,7/24,17/24,19/24 labels with positive/negative assignment determined by the real orientation reversal. **Their full ambient angle preimages are not certified here.** The proof uses standard real-symmetric **quadratic-like straightening**, local connectivity of the PCF little Julia, and the source KL puzzle-topology theorem; it does not assert that the round-disk boundaries are the literal KL puzzle boundaries.

Since K₉⊂D(0,1/32) but |t_G|>1/32, the little K₉ is disjoint from the finite Julia vertices on the critical depth-three G-puzzle boundary, and it cannot meet the external-ray/equipotential arcs. Thus connected K₉ containing 0 lies in **int Y³_G**. The first two critical G-iterates x₃>1/16 and x₆<−1/10 lie outside that real central piece, while **G³(0)=x₉∈K₉⊂int Y³_G**. Therefore **the first return of 0 to the second top critical piece has G-time 3, i.e. physical time 9**.

This supplies an **actual source-level 3-then-9 top-puzzle/first-return match**, under the named classical inputs and without confusing the two KL decoration clocks with the two primitive return clocks. It is **not** the complete KL modified principal nest and does not establish its canonical localization's marked germ identity on every puzzle piece or the based O/ξ/η transport between these nested return levels.


## 3. Separate actual Kahn canonical-localization witnesses at p=3 and p=9

We can do more than list possible nonfaithful ray angles. The [Paper-1 source-locked canonical-localization theorem](../mlc_unified/kl_canonical_localization_forced_collision.md) supplies an **actual based loop/coset collision for every ordinary primitive stage** once an off-cycle component of the pulled-back little Julia set is identified. The two primitive stages at this tip meet the earlier complex phase disjointness assumptions. Here is a finite **real-point certificate** of such a component **for each stage**.

Set g=f³. The exact sign inequalities, checked by Lean and independently by Python, are

\[
\begin{aligned}
&g(1)<0<g(17/16),\\
&g(6/5)<1<17/16<g(49/40),\\
&g(31/25)<6/5<49/40<g(5/4).
\end{aligned}
\]

IVT produces a nested sequence of **actual real points**

\[
s_1\in(1,17/16),\ g(s_1)=0;\quad
s_2\in(6/5,49/40),\ g(s_2)=s_1;\quad
s_3\in(31/25,5/4),\ g(s_3)=s_2.
\]

In particular **f³(s₁)=0∈K₃** and **f⁹(s₃)=0∈K₉**. Independently certified **complex** outer phase disks f^j(V₃), j=0,1,2, do not meet (1,17/16). The same is true for **all nine complex inner phase disks** f^j(V₉), j=0,…,8, versus (31/25,5/4). These are strict signed-integer separation statements, *not* floating-point plotted impressions. Thus

\[
s_1\in(f^3)^{-1}K_3\setminus B_3,\qquad
s_3\in(f^9)^{-1}K_9\setminus B_9,
\quad B_p=\bigcup_{j=0}^{p-1}f^j(K_p).
\]

The preimages lie in **extra components**, not in the central one: the central component of the preimage of K_p is K_p inside its certified central proper quadratic-like restriction, and the others have no overlap with B_p by the primitive phase separation. This is also the structural conclusion proved in the cited Paper-1 theorem for a general primitive stage.

To make the based-cover notation literal, choose once and for both scales a common **ambient polynomial-like base** f:U¹→U⁰ with U⁰=D(0,3), U¹=f^{-1}(U⁰); K(f) lies within U¹⊂⊂U⁰ since c_tip∈(−2,−1). For p=3 and 9 let U^p=f^{-p}(U⁰) and F_p=f^p. At each stage use the **source's own** deleted surfaces and subgroups

\[
\Omega_{s,p}=U^p\setminus F_p^{-1}B_p,\quad
\Omega_{t,p}=U^0\setminus B_p,
\]
\[
H_{s,p}=\operatorname{im}\pi_1(D_{K_p}\setminus K_p,z_*),\qquad
H_{t,p}=\operatorname{im}\pi_1(D'_{K_p}\setminus K_p,z_*),
\]
where the homomorphisms are into π₁(Ω_{s,p}), respectively π₁(Ω_{t,p}); neighborhoods and based paths are chosen as in the source Paper-1 localization theorem (a standalone homomorphism target is not implied by this shorthand).

For each p, let X_p≠K_p be the pulled-back component containing s₁ or s₃, choose a small Jordan neighborhood D_{X_p} disjoint from B_p and the other pullback components, and choose a based path η_p in Ω_{s,p} from z_* to ∂D_{X_p}. The loop

\[
\gamma_p=\eta_p\cdot\partial D_{X_p}\cdot\eta_p^{-1}
\]

has winding number 1 about s₁ (p=3) or s₃ (p=9). Every class in H_{s,p} has winding number 0 there, because it can be represented inside D_{K_p}. But D_{X_p} is disjoint from B_p, so the loop contracts in Ω_{t,p}. Hence, with a_p:Ω_{s,p}↪Ω_{t,p} the **physical inclusion**,

\[
\boxed{[\gamma_p]\in a_{p*}^{-1}(H_{t,p})\setminus H_{s,p}
\qquad(p=3,\ 9).}
\]

Kahn's *actual connected* localization covers therefore have **two different source cosets identified by their based localized inclusion** at each of the two concrete periods. This is an instance of the existing Paper-1 canonical sheet theorem, now with **exactly bracketed real extra-preimage witnesses** on the nonattracting two-scale tip. We are not equating these cosets with the finite 64:1 escaping-Böttcher inverse-ray map or with the separate Levin angle maps Π₃,Π₉.

## 4. A source-domain obstruction to naive 9-to-3 functoriality

The previous progress establishes **two legitimate one-scale** based localization groupoids, not a map *between* them. There is an immediate first **source-domain mismatch** when one tries to create the interscale comparison by either ambient identity or the physical f⁶.

The exact signs

\[
g(1/16)>1/16,\qquad g(1/8)<1/8
\]

give by IVT a real fixed point a∈(1/16,1/8) of g=f³. Since a lies in the invariant real interval I₃, **a∈K₃**. It is **not in B₉**. Indeed, the nonzero phase classes mod 3 lie outside K₃ by the three-phase separation. In phase class zero the three continua K₉, f³(K₉), f⁶(K₉) are pairwise disjoint and cyclically permuted by g. A g-fixed point in one of them would belong to the next, a contradiction. Thus

\[
\boxed{a\in B_3\setminus B_9,\qquad f^3(a)=f^6(a)=f^9(a)=a.}
\]

Consequently the target punctured surfaces satisfy **a strict reverse inclusion**

\[
\Omega_{t,3}=U^0\setminus B_3\quad\subsetneq\quad
\Omega_{t,9}=U^0\setminus B_9.
\]

The proposed **identity** arrow from the *period-nine source* target surface to the *period-three* target surface is **not even defined on a**, because a belongs to the former but is deleted from the latter. Nor is the obvious **f⁶** candidate such a map: f⁶(a)=a is also deleted at period three. The same exact point witnesses the mismatch of the source deleted surfaces: a∈U⁹ and f⁹(a)=a∉B₉, so a∈Ω_{s,9}, but f³(a)=a∈B₃ so a∉Ω_{s,3}. Neither identity nor f⁶ maps Ω_{s,9} into Ω_{s,3}.

This is a **literal, source-defined punctured-surface first-failure certificate for the two naïve arrows**. It does **not** establish that no other, properly marked, based KL/Kahn natural transformation could exist, and it does not manufacture a canonical one from a pointwise inverse image or an ordinary exterior angle collision. The arrows in Paper 1 localize a physical **inclusion within one primitive scale**, not automatically a transition across different deleted sets. The opposite-direction inclusion Ω_{t,3}↪Ω_{t,9} exists, but is **not** the requested 9-to-3 sheet map; its source subgroups and prime-end markings have not been checked for the needed lifting and coset conditions.

This also explains why the genuine Levin observations in the [two-scale ray audit](levin_tip_p2_carathéodory_two_scale_20261106.md) cannot by themselves close #29:
\[
\Pi_9(114/511)=\Pi_9(397/511)=0,
\qquad
\Pi_3(114/511)=5/7,\quad \Pi_3(397/511)=2/7.
\]
They are legitimate ray-angle maps on two *different* straightenings, but there is **no proof** here that either one identifies the based coset groupoid or its O/ξ/η side labels.

## 5. Remaining hard gates and reproducibility

| Issue #29 objective | After this audit |
|---|---|
| (1) Same-parameter 3/9 **complex** primitive geometry | **Existing merged PR #31** + imported Rouché/Riemann–Hurwitz; unchanged |
| (2) Source q,n, P, V⁰ and Q_L,Q_R **at both top levels** | **Identified at both scales** with q=2,n=1, P=Y¹, V⁰=Y³ in the appropriate external coordinates of f and G=f³; physical first returns 3 and 9. **Complete terminal modified principal nest and marked source-domain identification still open** |
| (3) Proof-used α/α′/Y³ vertex landing table | **First-level actual ambient angles and second-level internal-angle top portrait**, with imported PCF/real-ray landing, verified finite modular arrows and real brackets. **Actual ambient lifts of all second-level vertices, higher-depth and O/ξ/η side table still open** |
| (4) Two scale-specific **based localization coset collisions** | **Explicit off-cycle inverse witnesses s₁,s₃ at each primitive stage**, and a based-loop formula by Paper-1 topology. **No interscale groupoid/naturality, side transport, or complete sheet marking** |
| (4) First proposed 9→3 surface arrow test | **Certified first failure** of identity and f⁶: a∈B₃\B₉ and f⁶(a)=a. Other source-defined arrows not excluded |
| (5) Older period-27 center versus triple-airplane component | Still **not independently settled** by this audit; no center-to-tip inference is made |
| Global 465-entry ledger / H1–H4 / UPTCR / MLC | **Unchanged, open** |

Reproduce from repository root:

~~~sh
lake build TipKLPuzzle TipComplexMargins TipRayPortrait
python research/independent_audits/verify_tip_kl_puzzle.py
python research/independent_audits/verify_tip_complex_domains.py --check-manifest
python research/independent_audits/verify_tip_levin_transport.py
~~~

**No full closure claim.** Closing #29 still requires **ambient lifts and full marked boundaries for the newly constructed second-stage g₃ internal top puzzle** (via the valid Levin correspondence), the complete modified principal nest and terminal first-return identification, **all** proof-used real/prime-end sides, and a based interface with actual subgroup inclusion/reflection and sheet/coset path-groupoid naturality. At the first missing object, the correct result is the documented failed obligation, not an invented map. A specialist must independently check the geometric ray and source-puzzle interpretations.

**Provenance:** Developed with OpenAI GPT-6, using separately cited classical sources and the archive's previous certified finite statements. The new Lean/Python steps certify only their encoded rational arithmetic; green CI is not mathematical peer review.
