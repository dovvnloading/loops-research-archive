# Issue #40 — weighted trace, angular growth, and positive crest audit (2026-11-24)

This supplements the three preceding monotone-transfer, marked-gate, and ambient-exactness notes. All transfers to the actual KKL category remain subject to the source-identification hypotheses recorded there. The following statements explain what those transfers would establish for the remaining numbered acceptance requirements of Issue #40.

## 1. Same-source complete edge traces

Use the actual model A=T_com, B=P^{-1}A, and the original side marking, with the finite vertex sets of KKL §2.5. Assume the original vertices are forward invariant as a family (the small Julia cycle and branch vertices of that construction), and the critical point belongs to a small Julia vertex. Use the marked-gate identity of issue40_marked_gate_sandwich_20261124.md. The preimage vertices are the components of the preimage of the union of original vertices. The preimage edges are the components of P^{-1}(original open edges). These are the same objects appearing in the model covering p_0 and contour collapse r_0, not separately chosen symbolic transitions.

For each old open graph edge e, subdivide it by its intersections with the preimage vertices. These intersections are connected subintervals (including possibly points or intervals adjoining the ends): subcontinua of a dendrite contain the unique arc joining any two of their points. There are finitely many because there are finitely many original vertices and the degree-d branched covering has at most d connected preimage components of each. Each intervening open edge segment maps homeomorphically onto a complete original target edge. Indeed P(e) stays in A by forward invariance, the endpoints of e are mapped into original vertices, and all subdivision endpoints lie in preimage vertices. Each intervening segment maps locally injectively into a single target open edge, since there is no critical point there; a locally injective continuous map of intervals is strictly monotone in suitable coordinates. The limits at both ends are target vertices, so the image is the entire target edge. These segments are whole preimage edges: an extension across either endpoint would enter a preimage vertex. Conversely any preimage edge contained in the old graph edge occurs once in this list. This gives a finite oriented traversal word for e (including orientation when the target edge is given an orientation), and its multiplicity vector is the corresponding column of T_F in output-row convention. If the source uses the transposed convention, transpose this formula and use the corresponding Perron vector.

Each old e has two distinct open side atoms. Over a segment which is a preimage edge, the two source side arcs are ordinary locally two-sided contour arcs of B; away from the segment endpoints there is no extra branch, because the preimage branch loci are in the preimage vertices. Under the inclusion contour r_0 they belong to the corresponding two sides of e in A. Under the same covering p_0, each maps to the full appropriate side of the target edge. This follows by local orientation preservation of the branched covering off its critical points and by the two distinct prime-end accesses of an interior point of an open edge. The marked-gate identity transfers these whole arcs and their positions, not merely their landing points, to the physical ideal circle. In particular no old edge traversal can be lost when a source side interval is thickened by an attachment contour.

Let v(I) count the included side atoms by original edge name, separately counting the two distinct sides (entries 0,1,2). For an open marked I (or positive closed I) whose F_* image is proper, its connected actual pullback is mapped injectively by p. In covering coordinates this is the elementary fact that any interval longer than one covering turn surjects onto the circle; an open interval of exactly one turn is injective onto a punctured circle. Thus distinct source side arcs included in the same pullback have disjoint target side arcs. Each included old side of e produces the full column just computed, with further contributions possible from the complete added contours. This proves

    v(F_*I) >= T_F v(I).

For a positive left Perron eigenvector w with w T_F=lambda_F w, lambda_F>1 (KKL §2.5), it follows that

    w v(F_*I) >= lambda_F w v(I).

If v(I) is nonzero, the increase is strict. It would be wrong to replace side multiplicities by the support set of edge names, or to invoke the spectral radius without establishing the same-source trace. This argument supplies the model trace and its physical marked transfer under the stated hypotheses.

For a nonempty source-eligible marked zero-edge sector, the ambient-angle theorem gives eventual saturation. Therefore it either acquires a complete edge-side atom before saturation or saturates (possibly in one step). This is an alternative to enumerating the degree-one and degree-two local gate maps; it uses the actual degree-d covering and ambient degree-d angle map instead. It does not prove a uniform escape time for arbitrarily small unmarked physical sectors.

## 2. An expanding angular mass, including zero-edge intervals

Let q_phys be the map from the physical ambient polynomial Böttcher circle onto the model carrier prime-end circle, obtained by composing the actual ambient prime-end transfer with the nested contour collapse. Let Phi be the complete model interval action. Define

    mu(I) = Leb(q_phys^{-1}(I)),

with Leb normalized angular measure. Every nonempty open interval has positive mu. By the exactness note,

    q_phys^{-1}(Phi(I)) ⊃ D(q_phys^{-1}(I)),

where D is multiplication by d on ambient angles. If I is a connected open or closed interval and Phi(I) is proper, the inverse-image interval under monotone q_phys has angular length at most 1/d (strictly less in the closed case, unless it is a degenerate zero-length interval). Consequently multiplication by d is injective there and

    mu(Phi(I)) >= d mu(I).

This is a genuine monotone angular mass for the contour relation until saturation, not the Euclidean width of a wave or a Perron weight on graph edges. In particular it handles every positive marked atom, even when its edge mass is zero. For singleton closed inputs it gives a useful dichotomy: if the singleton's ambient angular fiber has positive length, it also eventually saturates; if its fiber is a singleton, no positive-mass conclusion follows. Do not silently equate a singleton crest with a positive closed interval.

## 3. Proper-base crest positivity

Here is the elementary noncrossing argument for a class of actual waves, with all its hypotheses visible. Use the KKL Appendix A.1 ideal marking and proper-path validity rule: a path cannot be subordinate to a multi-interval of length at most two. Let a nonempty lamination of such simple paths have a **proper** base B, with its two ends defined as minimal marked intervals in that base, each leaf having one endpoint in each end. Cut the inner circle outside B and use its induced linear order. The paths are subordinate to B, so they can be represented in a collar in the order determined by their endpoints; in the annular universal cover, endpoints of two disjoint leaves cannot interlace.

Minimality of B means its extreme atoms contain leaf endpoints. They are contained in the two end intervals. If one end contains both extremes, it contains all of B and the crest is empty. Otherwise for a nonempty crest the two ends contain opposite extremes of B, and cannot overlap; the crest is precisely the closed gap between them. In particular it is a connected closed marked interval, allowing a singleton provisionally.

Suppose the nonempty gap is a singleton cut c. The last atom of the left end must contain a left endpoint of a leaf a, and the first atom of the right end must contain a right endpoint of a leaf b, by minimality. These atoms are adjacent. If either leaf has both endpoints in these two adjacent atoms, it is subordinate to their two-atom interval (its subordination inside the proper base fixes the homotopy direction), contrary to validity. Thus a has its right endpoint strictly farther right than the first atom of the right end, while b has its left endpoint strictly farther left than the last atom of the left end. The four endpoints have interlacing order

    b_left < a_left < b_right < a_right.

Such leaves must intersect in the universal cover, contradicting lamination disjointness. Hence any nonempty crest in this proper-base setting contains a whole atom. The argument uses actual noncrossing of the paths; an arbitrary pair of overlapping endpoint ranges is not a lamination certificate.

Furthermore each leaf crests over the entire common gap, since the leaf is subordinate to the proper base and its endpoints lie in opposite end intervals. If the wave is short in the sense of §6 (no leaf crests over an entire limb), the common gap cannot contain a full limb. Therefore it meets at most two consecutive partial limb intervals, and since every limb has at most 6b atoms (Lemma 4.8), its combinatorial length is below 12b. This derives the positivity and shortness bound for nonempty proper-base crests rather than just declaring that a closed crest is an open atom.

**Scope limitation.** This proof assumes a proper base and the source end-interval convention just specified. An arbitrary lamination subordinate to the full inner circle could have leaves in different cyclic homotopy directions; a cut outside its base need not exist. A proof for that case must either establish that the proof-used short critical-visit waves have proper bases or deal with the full-circle base and its possible endpoint-range ambiguities separately. The argument is not presented as a universal wave-crest theorem for all interpretations of Appendix A.1.

## 4. Closed-crest inclusion count

For a chain of proof-used short waves having positive proper closed marked crests I_j as above, the source critical-visit definition (§6) supplies

    I_{j+1} ⊃ F_*^{m_j}(I_j),  m_j >= 1,

and the right side meets the critical limb. Use the **closed** marked action supplied by the marked-gate theorem. If no crest saturates, the included-atom lengths are nondecreasing. At a fixed positive length k below the total marking size, equal-length inclusion of two closed connected marked intervals is equality. The number of such critical states is at most r+k-1, with r<=6b (a positive closed marked interval intersecting an open critical multi-interval shares an open atom). No state can repeat during a constant-length plateau: a repetition along a chain of inclusions would, by monotonicity, force all positive iterates of that state to remain inside itself, contrary to eventual saturation. Thus the length-k plateau contains at most 6b+k-1 critical states. Summing for 1<=k<12b yields

    sum_{k=1}^{12b-1} (6b+k-1) = (12b-1)^2 < 216b^2

for positive integer b. The first wave in a chain need not be a critical visit; adding one initial state is still strictly below 216b². This validates the count with a substantial margin for the indicated class, with actual closed endpoint births included. If a closed crest saturates it cannot be a short wave over that full circle (every limb would be included). The proof does not require F_*(closure I)=closure(F_*I).

## 5. Issue #40 status after these arguments

1. Prime-end circles, separate cover and immersion, actual collar coordinates: constructed in the saturated-lift setting.
2. Complete marked host/attachment correspondence and open/closed extreme gates: constructed using the source interval and component assertions of Prop. 6.5, the singleton cuts, and finite host family. The full individual contours, not only host points, enter the marked block. The proof is not an independent validation of all maximal proper-path assertions in A.3.2.
3. Same-source edge incidence and strict positive Perron growth: proved by model subdivision and transferred through the marked identity, conditional on native model/marking identification.
4. Positive zero-edge marked sector escape: proved by ambient exactness, a different mechanism from local gate enumeration. Arbitrary unmarked physical subarc dynamics are not claimed.
5. Actual positive proper-base closed crests: positivity, shortness and critical visit count proved in the specified class. Full-circle bases and precise source conventions remain to be authenticated.

The remaining tasks are now chiefly to authenticate the saturated canonical KKL small Julia/tree lift and singleton original marking, the precise Prop. 6.5 path/access semantics including closed gates, and the proper-base or alternative crest geometry of all waves used by the source. The topological proofs in this PR require independent review. There is no new formal verification or CI assertion, and neither the repair issue nor the Wave amplification ledger entry should be closed on this basis alone.
