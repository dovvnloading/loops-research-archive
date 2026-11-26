# Intersection, divisibility, and a native all-period obstruction

Base: 47806d64c64688bdf27c817f036cfdbfa85ce1d5.
Continuation of [cyclic saturation](CYCLIC_SATURATION.md) and [cyclic rigidity](CYCLIC_RIGIDITY.md).
Targets: MAPPING_TELESCOPE, H1_CELL_TREE_EXTRACTION (partial). No ledger promotion.

## 1. Exact arithmetic of actual physical return periods

Retain f(z)=z²+c, connected empty-interior K(f)=J(f)=X. Call m≥1 *admissible* if f^m has a connected quadratic-like filled set containing 0. By CYCLIC_RIGIDITY.md this is equivalent to a saturated cyclic carrier of degree word (2,1,...,1), and that carrier is unique. Denote its filled set by K_m and its phase continua by A^m_j=f^j(K_m), j modulo m. These are actual physical sets; m=1 is allowed and K_1=X. No maximal-renormalization or combinatorial convention enters the definition.

**Intersection lemma.** Let C_1,C_2 be subcontinua of X with nonempty intersection, and let W_1,W_2 be components of f⁻¹(C_1), f⁻¹(C_2) with nonempty intersection. Then W_1∩W_2 is exactly a connected component of f⁻¹(C_1∩C_2).

Indeed the target and source intersections are connected by hereditary unicoherence proved in CYCLIC_SATURATION.md §2. Pick x in W_1∩W_2. The component T of f⁻¹(C_1∩C_2) containing x is contained in both W_i by connectedness, and W_1∩W_2⊂T because it is connected and maps into C_1∩C_2. The component lemma also gives f(W_1∩W_2)=C_1∩C_2 and its degree is two exactly when c lies in both targets. The statement does not require interiors or arcs.

**Theorem 1 (lcm and nesting).** For any admissible m,r, put l=lcm(m,r). Then l is admissible and for every integer j,
    A^l_j = A^m_(j mod m) ∩ A^r_(j mod r).              (1)
In particular
    K_l = K_m ∩ K_r,                                   (2)
    K_r ⊂ K_m  if and only if  m divides r.             (3)

**Proof.** For 0≤j<l put B_j equal to the intersection in (1). It is nonempty because x_j=f^j(0) belongs to both phases, and is a continuum. The intersection lemma gives one-step saturation in this l-cycle. A target intersection contains c exactly when j+1 is congruent to 1 modulo both m and r, i.e. the source index j is 0 modulo l. Thus the product degree is exactly two and B_0 contains 0. Recognition and uniqueness from CYCLIC_RIGIDITY.md prove (1) and (2). If m divides r then l=r and (2) gives inclusion. Conversely if K_r⊂K_m, its rth forward image is K_r⊂A^m_(r mod m). This latter phase contains 0, which by the prescribed one-step degree word happens only at phase 0. Thus m divides r. QED.

This argument provides an exact source-set inclusion diagnostic, not just a necessary relation on abstract periods. It applies even if the individual phase continua touch. The lcm theorem is not a claim that arbitrary two prescribed periods are admissible, nor that every admissible period is maximal in an external renormalization convention.

## 2. Overlap at distinct phases is at most one periodic point

**Theorem 2.** If m is admissible and i≠j modulo m, then A^m_i∩A^m_j is empty or a singleton fixed by f^m.

**Proof.** If an intersection is nonempty, all its forward phase intersections B_k=A^m_(i+k)∩A^m_(j+k) are nonempty. The intersection lemma gives an actual saturated m-cycle for B_k. No target can contain c because i+k+1 and j+k+1 cannot both be phase 1. All degrees are one. If B_0 were nondegenerate, it would be full, invariant and a component of (f^m)⁻¹(B_0) by the same component-tree argument used in CYCLIC_RIGIDITY.md §2. The attracting/parabolic basin hypothesis of BOPT Theorem B is vacuous as before, so B_0 would be a polynomial-like filled set of degree one (the degree is determined by the exact preimage count).

Such a filled set cannot be nondegenerate. If the polynomial-like convention excludes degree one, this already contradicts the conclusion; otherwise the proper degree-one restriction P:U'→U is a conformal isomorphism and its inverse ψ:U→U' has relatively compact image in U. Conjugate by a Riemann map U→D; its image lies in |z|≤a<1. Schwarz–Pick applied to ψ/a in those disk coordinates bounds the hyperbolic derivative of ψ by a (the factor (1−|ψ/a|²)/(1−|ψ|²) is ≤1). The iterated inverse images of the relatively compact U' consequently shrink to one point, and the filled set, contained in all of them, has at most one point. This contradicts nondegeneracy. Thus B_0 is a point, and f^m-invariance fixes it. QED.

**Corollary 3 (comparability whenever one return is primitive).** Suppose m,r are admissible, and at least one cycle has pairwise disjoint phases. Then m divides r or r divides m.

Proof by contradiction: d=gcd(m,r), with m/d,r/d both ≥2. Without loss let the m-cycle be primitive. Choose two distinct phase indices i_1,i_2 modulo m congruent mod d and two distinct phase indices j_1,j_2 modulo r in the same residue class. Put A=A^m_(i_1), A'=A^m_(i_2), B=A^r_(j_1), B'=A^r_(j_2). Every cross intersection is nonempty: the Chinese remainder theorem supplies a common forward critical orbit index for the relevant pair. In fact (1) identifies each cross intersection with a nondegenerate l-phase, but nonemptiness suffices. A,A' are disjoint, while B∩B' is empty or a singleton by Theorem 2. The union C=A∪B∪A' is a continuum in X because B meets both A and A'. Its intersection with B' is
    (A∩B') ∪ (A'∩B') ∪ (B∩B').
The first two sets are nonempty disjoint compacta, and the last has at most one point. This union is disconnected (a singleton can attach to at most one of two disjoint compacta). That contradicts hereditary unicoherence of X. QED.

For two noncomparable touching cycles the same argument implies that in each common residue class all m-phases must meet pairwise, and all r-phases must meet pairwise. They in fact share a common point: pick two distinct m-phases A,A' with intersection {a}; each r-phase in that residue meets both and, by connectedness of its intersection with A∪A', contains a. Since two distinct r-phases intersect at most at a, each remaining m-phase meets both and also contains a. The common points advance under f through the d residue classes. We do not deduce the remaining angular rotation/access condition needed to exclude noncomparable satellite/satellite periods by this argument alone. This is the precise boundary of Corollary 3.

## 3. Actual source inventory: exactly two physical periods can carry it

Use the source-locked actual 3/9 Misiurewicz tip from [the cell-tree audit](../h1_cell_tree_extraction_20261126/NOTE.md), §§4.1–4.2, and [two-scale complex return proof](../nonattracting_tip_complex_two_scale_20261106.md). Keep its notation:

* f has K=J and actual connected degree-two filled sets K3, K9 for f³ and f⁹ respectively, K9⊂K3; both cycles are primitive.
* The native second direct-decoration root I=[−a,a] is an actual interval in K3, with a the dividing root of G=f³ and a∈(3/32,1/10). Its finite decoration atoms K_w, plus all infinite end fibers, have compact union U with [U]_X=I. The two endpoint atoms ±a belong to U.
* K9 is the actual terminal interval inside the escape gap, a strict subset of I, and contains 0. The root branch clock is f⁶; the terminal return clock is f⁹. These are different physical maps.

These are imported as the named archive's written physical identifications, not inferred from the numerical labels or finite integer regression. No new interval certificate for the parameter is claimed.

**Theorem 4 (complete all-period inventory test).** Among all physical times m≥1, a saturated cyclic carrier with one quadratic step, critical source phase zero, and containing the entire actual root inventory U in that phase exists exactly for m∈{1,3}. In particular it does not exist for time 6 (decoration clock), time 9 (terminal clock), or any larger time.

**Proof.** A saturated critical source containing U is a continuum and hence contains I=[U]_X. Thus K9⊂I⊂K_m. By (3), m divides 9, so m∈{1,3,9}. At m=9 uniqueness gives exactly K9, which strictly misses the endpoint atoms of I. At m=3 the source-defined K3 contains I, and at m=1 the full X contains I. Each is an actual saturated cycle. This proves the classification for every integer m without a cutoff. QED.

**Explicit extra-critical-step certificate at the native 6-clock.** Even without polynomial-like recognition, suppose a saturated six-step cyclic carrier H contains I at phase zero, and has only that one critical source. Invariance of H_0 under f⁶ and containment K9⊂H_0 force f⁶(K9)=D_6⊂H_0. The next three physical steps carry D_6 onto K9 because f⁹(K9)=K9. Consequently H_3 contains 0, making step 3 quadratic as well as step 0. This contradicts degree word (2,1,1,1,1,1). The certificate uses actual terminal phase sets, not a symbolic identification of the 6-clock with the 9-clock.

This rules out an entire natural class of shortcuts: no enlargement or re-marking of the native second-decoration hull can turn it into a saturated degree-two *cyclic* return at the decoration or terminal clock. Its physical primitive period-3 carrier is available, but cannot be called the period-6 or period-9 carrier. A successful virtual construction using this inventory must change the category (e.g. partial/noncyclic arrows, distinct carriers for decoration and terminal phases, or other genuinely authorized source geometry). We do not assert that the source requires precisely the rejected saturation/period/inventory combination; the theorem is a physical obstruction to that combination, not a counterexample to universal H1 as written.

## 4. Dependencies, limitations and independent checks

The new statements use the component lemma, Janiszewski/fullness and the recognition/uniqueness proof in the two preceding commits. For Theorem 2 the BOPT theorem is the same independently inspected primary statement (author PDF, printed p.17); the degree-one contradiction is given directly. The elementary CRT argument is exact. No MLC or JLC theorem, uniform modulus, infinite renormalization bound, or identification of the native marks with all protected Wave accesses has been established. The proof of Corollary 3 deliberately stops short of the satellite/satellite comparability problem. No claim of novelty of ordinary renormalization lattice properties in the literature; the contribution is the explicit source-carrier reduction and the native all-period obstruction. This is not a formal Lean proof or an independent human review.

AI disclosure: GPT-6.2 performed the derivation and repository source comparison.
