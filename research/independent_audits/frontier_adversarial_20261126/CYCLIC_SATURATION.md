# Least saturation on actual cyclic Julia diagrams

Base main: 47806d64c64688bdf27c817f036cfdbfa85ce1d5. Date: 2026-11-26.
Targets: H1_CELL_TREE_EXTRACTION and MAPPING_TELESCOPE under H1_MARKED_CONSTRUCTION.
Status: written set-theoretic theorem on actual quadratic Julia continua, partial for H1. No ledger promotion.

## 1. The gap addressed

The preceding [least-tree audit](../h1_cell_tree_extraction_20261126/NOTE.md), §§1–3, constructs least saturated carriers by bottom-up/top-down recursion on a finite tree. The [cyclic telescope audit](../h1_mapping_telescope_20261126/NOTE.md), §1(S1), assumes an actual saturated cyclic inverse diagram before producing its collars. A tree recursion cannot simply be used on a cycle. Here we eliminate the existential choice of saturated continua for any *supplied* finite physical diagram, with a precise closure bound and exact degree/localization tests. We do not manufacture the source-defined seed/anchor diagram, establish protected access completeness, or assert that its tests pass for all virtual blocks.

## 2. Physical category and component lemma

Let f(z)=z²+c with connected K(f)=J(f) of empty interior, and write X=J(f). Every subcontinuum of X is full: any bounded complementary component would lie in X because the connected exterior of X is in the unbounded complementary component. Two intersecting subcontinua have connected intersection by Janiszewski (their union is full). Consequently the intersection of all subcontinua containing a nonempty compact S⊂X is a continuum, denoted [S]_X; finite intersections are connected and compactness gives the arbitrary intersection. We use the least-tree audit §1 and its classical separation input, not local connectivity.

For nonempty continuum C⊂X and a with f(a)∈C, let T_a(C) be the component of f⁻¹(C) containing a. The following facts include singleton C:
* If c∉C, f⁻¹(C) has two compact disjoint components, exchanged by negation, and each maps homeomorphically onto C.
* If c∈C, f⁻¹(C) is one continuum and maps onto C with degree two counting multiplicity, including the double preimage of c.
* T_a(C) is monotone for inclusion among such C.

For proof choose nested closed Jordan neighborhoods of C, shrinking to C, by exterior uniformization of the full continuum (round disks for a singleton). If c∉C choose them avoiding c; the two inverse branches exist on the simply connected open neighborhoods, and the branches are labeled by a. If c∈C choose each open neighborhood containing c; the inverse disk under a translated square map is connected (the two sheets meet at the critical point), and the compact nested inverse disks have connected intersection. Complete invariance puts all these limiting inverse sets in X. Monotonicity follows from connectedness and the common anchor.

**Continuity lemma.** Suppose C_n increases, f(a)∈C_0, and C=closure(⋃ C_n). Then
    closure(⋃ T_a(C_n)) ⊂ T_a(C).
Equality holds if either c∉C or c∈C_N for some N.

In the first case choose a single inverse branch on a neighborhood of C avoiding c; it is continuous on C and agrees at a. In the second case, from N onward T_a(C_n)=f⁻¹(C_n). For each x∈f⁻¹(C), approximate f(x) by y_n∈⋃C_n and choose roots of y_n-c tending to x (including x=0); this proves equality. These arguments also prove the assertion for any increasing sequence of compact connected sets, without path connectivity. The *only possible* failure of continuity from below is a newly reached critical value, absent from every finite-stage target.

## 3. Least cyclic saturation theorem

Take a finite directed graph V,E (loops and cycles allowed). Every arrow u→v represents one actual physical step f, not an abstract transition. Expand iterates into one-step arrows first, with their actual intermediate anchors. At each vertex v fix a point a_v∈X and a nonempty compact seed S_v⊂X containing a_v. Require f(a_u)∈S_v for each arrow u→v; this can always be enforced by adding those specified anchor images. Degree prescriptions, if any, apply per arrow and hence must agree for arrows sharing a target. Insert c in the seeds of every required degree-two target.

A saturated solution is a tuple of continua F_v⊂X containing S_v such that for every arrow u→v,
    F_u = T_{a_u}(F_v).
In particular f(F_u)=F_v. Initially ignore restrictions other than the seeds and saturation; the all-X tuple is such a solution.

Define H_v^0=[S_v]_X and simultaneously
    H_v^(n+1) = [ H_v^n ∪ ⋃_(u→v) f(H_u^n)
                        ∪ ⋃_(v→w) T_{a_v}(H_w^n) ]_X.           (1)
At a limit of increasing tuples take H_v^∞=closure(⋃ H_v^n).
Each operation is well-defined and monotone. The closures are continua in X. Every saturated solution contains every iterate and every limit, by induction: its forward images and selected inverse components contain the indicated terms, and it contains the least hull.

**Theorem A (unprescribed degrees).** Repeatedly run (1) for countably many finite iterations, take the increasing limit, and restart from that limit if necessary. There is a fixed point no later than ω·(|V|+1), with ordinal multiplication in the indicated order. The resulting tuple is the unique least saturated solution.

**Proof.** At any such limit H, f(H_u)⊂H_v by continuity and the forward inclusions from (1). If every arrow has continuity in the component lemma, also T_{a_u}(H_v)⊂H_u. The forward inclusion puts connected H_u containing a_u inside T_{a_u}(H_v), so equality holds. Thus the limit is fixed. If the limit is not fixed, at least one target has newly acquired c during this block only at its limit. That vertex never loses c in subsequent blocks and cannot be responsible for a later nonfixed limit. There are at most |V| such vertices; therefore at most |V| nonfixed blocks, and the following block is fixed. Minimality follows from the inductive containment above, or by taking intersections of all saturated solutions. QED.

**Theorem B (specified degree word).** If every arrow has specified degree d_e∈{1,2}, a *single* countable closure suffices either to construct the least solution of that degree word or to prove none exists. At the limit H test c∉H_v at every degree-one target. If a test fails, no saturated solution of the required word exists, since every such solution contains H. Otherwise degree-two targets contain c from the initial seeds, and degree-one targets avoid c even at the limit. Hence the continuity lemma applies to every arrow and H is fixed; the degree tests prove its word is exactly the prescribed one.

This is not a finite-time computational algorithm for arbitrary compact subsets of an unknown Julia set. It is a countable mathematical construction, and tests on the limit are genuine analytic obligations. In particular, the proof does not replace a strict avoidance test on the limit by a finite-stage numerical sample.

## 4. Exact location and collision tests

Add arbitrary closed admissible locations L_v⊂X, and prescribed pairwise disjointness of named carriers (e.g. different sibling components or primitive phases). For the fixed tuple H of Theorem A/B, existence of a solution with these additional restrictions is equivalent to H_v⊂L_v and the indicated disjointness tests on H; also test any required univalent targets not already tested in Theorem B. Required quadratic targets were inserted into S. Necessity is coordinatewise minimality. Sufficiency is H itself. A failure of one of these monotone restrictions at any intermediate stage is permanent.

If nondegenerate carriers are required in a weakly connected component of the diagram, assume at least one seed there is nondegenerate. Both forward images and saturated inverse components of nondegenerate continua are nondegenerate, so this propagates through the diagram. Alternatively a cycle containing the quadratic step forces 0 and f^m(0) in its critical source after one full circuit of length m. They are distinct: a periodic critical point would give a superattracting basin and contradict empty interior. Thus the one-quadratic-cycle case below needs no independently supplied nondegenerate seed.

## 5. Why the critical limit test is real

On the actual polynomial f(z)=z²−2, X=[−2,2], take C_n=[−2+1/n,−1], n≥1, and anchor a=1. The selected inverse components are [1/√n,1]. Their closed increasing union is [0,1]; but the limiting target is [−2,−1] and its actual inverse is [−1,1]. The missing half is a real sheet collision, not an abstract order-theoretic pathology. This witnesses the failure of unconditional inverse-component continuity, not sharpness of the ω·(|V|+1) bound for cyclic diagrams.

A separate actual cyclic obstruction on this same f uses vertices 0,1 with arrows 0→1 and 1→0, anchors 0,−2, seeds {0,2},{−2}, and degrees (2,1). Initially H_0=[0,2], H_1={−2}; both degree tests hold. One iteration forces H_1=X by f([0,2])=X; the next forces H_0=X by T_0(X)=X. The required degree-one target H_0 now contains c=−2. No choice of larger saturated carriers can repair that word. This does not rule out any source-defined virtual block not identified with these data.

## 6. Precise scope

This supplies the missing least-saturation construction between the finite-tree method and the cyclic S1 hypothesis of the telescope audit. It uses no local connectivity, no choice of arbitrary connecting arcs, no finite-time approximation to a limit, no assumption about marked-width calibration, and no alteration to the canonical ledger. The next step is to check the degree and admissible location tests on actual native virtual seed diagrams, then separately produce the source-prescribed marking and peripheral cover. The existence of such seed/anchor data is not inferred from a symbolic word. No claim of general literature novelty or priority.

AI disclosure: GPT-6.2 developed and wrote the arguments. No human specialist review or Lean verification. The proof is submitted for adversarial review; subsequent commits will record applications and limitations.
