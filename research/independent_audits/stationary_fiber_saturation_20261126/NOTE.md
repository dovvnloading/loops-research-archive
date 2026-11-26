# Stationary geometric carrier: fiber saturation and the remaining obstruction

Date: 2026-11-26. Working proof packet, opened for incremental review.

## Target and scope

This packet follows the actual quadratic construction in [stationary predecessor lift](../stationary_nonlc_predecessor_lift_20261126/NOTE.md), especially its explicit distinction between the least physical carrier S and the full monotone lift T*. It targets the unresolved saturation/access identifications in KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT and KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION. No global ledger promotion, analytic width estimate, or MLC claim is intended.

Use the hypotheses and notation of that note: X=K(f)=J(f) is a full empty-interior continuum, hence hereditarily unicoherent; p:X→Y is the Kiwi monotone dendrite quotient, pf=gp; nonsingleton fibers have pairwise disjoint forward images, each of which is a complete fiber; K_i are the disjoint primitive cycle of compact connected little filled Julia sets with f(K_i)=K_(i+1 mod P). Let S be their least physical continuum hull, B their model hull and T*=p^{-1}(B).

## First lemma: periodic continua cannot share a wandering fiber

Let A,D be disjoint subcontinua of X with f^m(A)⊂A and f^m(D)⊂D for some common positive m. Then p(A) and p(D) are disjoint.

Proof. Otherwise a complete fiber C meets both A and D. It is nonsingleton, so C and f^m(C) are disjoint by the stated wandering-fiber property. Both continua A∪C∪D and A∪f^m(C)∪D are connected, since each connecting fiber meets both A and D. Their intersection is exactly A∪D, a disconnected set. This contradicts hereditary unicoherence. QED.

This generalizes the predecessor note's disjoint periodic-mark argument to any two forward-invariant continua sharing a return time (surjectivity on them is unnecessary). The essential imported hypothesis is the wandering-fiber property; no statement about arbitrary monotone quotients follows.

## Research question

The existing note establishes p(S)=B, S⊂T*, and exact selected-component equality for T*, but does not identify S=T* or its marked accesses. The next steps will distinguish a genuine dynamical obstruction from purely topological ambiguity; all proved and conditional statements will be explicitly scoped.

AI disclosure: OpenAI GPT-6.2 assisted proof search and exposition; no independent human verification at opening.


## 2. Exact intrinsic/ambient fiber identification (actual dynamical theorem)

**Theorem.** Let f be as above and F=f^P:U→V a connected quadratic-like restriction with filled set K_0. Let h be a Douady–Hubbard straightening conjugacy near K_0 to a quadratic polynomial Q with connected filled set K(Q); let q:K(Q)→Y_Q be its Kiwi quotient and G the induced dynamics. Then for every x∈K_0,
    
    p^{-1}(p(x)) ∩ K_0 = h^{-1}(q^{-1}(q(h(x)))) .                 (11)

There is a unique homeomorphism H:Y_Q→A_0=p(K_0) with H q h = p|K_0. It conjugates G to g^P|A_0. In particular the restriction p|K_0 is not an arbitrary monotone factor of the little return: its kernel is exactly the intrinsic wandering-continuum relation. This holds without assuming that K_0 itself is p-saturated.

**Proof.** Both filled sets have empty interior: K_0 is a subset of X, and the straightening is an ambient homeomorphism near it. All finite cycles of Q are repelling: a periodic point is in K(Q), and its return is locally topologically conjugate to a repelling iterate of f by the straightening. Equivalently the inverse germ is attracting on a neighborhood, a property impossible for a neutral or attracting forward holomorphic germ. Thus K(Q)=J(Q) and Kiwi applies on both sides. The proof only needs absence of irrationally neutral cycles for Q.

A point of K_0 has finite forward orbit for F precisely when it has finite forward orbit for f: an eventual repetition under F is an eventual repetition under f, and a finite f-orbit has a finite F-orbit. The homeomorphism h preserves this property. Use Kiwi Theorem 2 (finite-orbit points have singleton fibers), and Corollary 4.6 with its proof (every connected subset missing all finite-orbit points is contained in one fiber). These statements apply to each actual polynomial, not just to its abstract angle model.

Set C=p^{-1}(p(x)). By hereditary unicoherence of X the nonempty intersection C∩K_0 is connected. If it is a singleton it is already contained in the right side of (11). Otherwise C is nonsingleton and misses all finite-orbit points; its intersection, mapped by h, is a connected subset of J(Q) missing all finite-orbit points of Q. Kiwi implies containment in q^{-1}(q(h(x))). Conversely if D=q^{-1}(q(h(x))) is nontrivial, h^{-1}(D) is a connected subset of X missing all finite-orbit points of f, so lies in C. If D is a singleton its inverse is x and the containment is automatic. These two inclusions prove (11), including both singleton cases.

The map qh:K_0→Y_Q is a continuous surjection from a compact space to a Hausdorff space, hence a quotient map. Equation (11) means that the assignment H(q(h(x)))=p(x) is well-defined and one-to-one; it is onto A_0 by definition and continuous by the quotient property. Compactness and Hausdorffness give a homeomorphism. For u=qh(x), H(G(u))=p(F(x))=g^P(p(x))=g^P(H(u)). Uniqueness follows from surjectivity. QED.

**All primitive phases.** For 0<i<P, f^{P-i}:K_i→K_0 is a homeomorphism. Indeed f^P:K_0→K_0 has exactly two preimages counted with multiplicity of every point in K_0 (proper degree two, all preimages in the restriction belong to its filled set). For each y∈K_i choose z∈K_0 with f^i(z)=y. By the evenness of f^P and reflection invariance of K_0 (predecessor note §6), both z and -z are in K_0 and have f^i-image y. If z=0 the local multiplicity of f^P at z is at least two. Hence every distinct preimage y of a given point under f^{P-i}|K_i accounts for at least two preimages with multiplicity of the full return. There cannot be two such y, proving injectivity; surjectivity and compactness give the homeomorphism. The map conjugates the F return on K_i to the F return on K_0 by commutation of powers. Applying the same two-inclusion argument to h_i=h f^{P-i}|K_i yields (11) for all K_i and a conjugacy H_i:Y_Q→A_i. This is also true of any preimage copy on which the appropriate iterate is a homeomorphism to K_i: finite-orbit status is preserved in both directions, and intersection with any ambient fiber is connected.

**Naturality across nested returns.** If K'⊂K_0 is an actual connected little Julia set of a further quadratic-like return, its intrinsic quotient embeds into Y_Q by applying the same theorem in the straightened Q-plane. The composite embedding into Y is equal to the embedding obtained directly from f: both send the quotient class of a point of K' to p(x). The proof is equality on representatives and surjectivity of the quotient map, not a choice of a homeomorphism up to isotopy. For any finite nested chain the same argument gives composition. No global inverse-limit compactness, diameter bound, or marking/width preservation is inferred.

**Consequences for the stationary carrier.** The p-fibers of each A_i pulled back *inside K_i* now have exactly the intrinsic fiber partition of the straightened polynomial. Their induced return dynamics and finite-orbit labels agree. Moreover p|S and p|T* restrict to that same partition on each mark, and no entire nontrivial intrinsic fiber inside a marked set is lost by passing from T* to S. What may still be lost is the portion of an ambient fiber outside the marked set or in a connecting piece. In particular (11) does not imply p^{-1}(A_i)=K_i or S=T*. It gives a canonical unmarked topological intertwiner of the actual renormalization dynamics; matching the specific marked KKL collar/access and source angle lifts requires additional work.

### Sources and attribution

* Jan Kiwi, Real laminations and the topological dynamics of complex polynomials, Adv. Math. 184 (2004), 207–267, DOI [10.1016/S0001-8708(03)00144-0](https://doi.org/10.1016/S0001-8708(03)00144-0): Theorem 2 pp.209–210, Corollary 4.6 and proof p.235, Corollary 5.3 p.239, Theorem 5.12 pp.243–244. Independently checked theorem/proof excerpts in the [accessible full-text reproduction](https://www.academia.edu/91433960/Real_laminations_and_the_topological_dynamics_of_complex_polynomials); publisher bibliographic record checked separately. This is an application of Kiwi's intrinsic characterization, not a replacement or claim of priority over it.
* A. Douady and J. H. Hubbard, On the dynamics of polynomial-like mappings, Ann. Sci. Éc. Norm. Sup. 18 (1985), 287–343, [Theorem 1](https://www.numdam.org/item/ASENS_1985_4_18_2_287_0/), connected straightening. Imported as in predecessor note §9.
* D. Schleicher, [On Fibers and Renormalization of Julia Sets and Multibrot Sets](https://arxiv.org/pdf/math/9902156v1), §4, especially Proposition 4.1 pp.9–11, Theorem 4.3 pp.12–15, Corollary 4.4 p.15. These discuss preservation of triviality under renormalization; do not claim novelty for that theorem. The present proof uses the later Kiwi theorem and gives an equality of possibly nontrivial restricted equivalence relations, not merely equivalence of triviality statements. The ray-domain description in Schleicher's proof of Corollary 4.4 motivates a separate saturation route; its exact domain identification for the KKL source is not assumed in (11).

Status: written deduction from imported theorems and the predecessor note; no independent peer review or Lean check, no ledger edit.

## 3. Full saturation of the actual primitive little Julia cycle

**Theorem 3 (saturation, not merely restricted equivalence).** Under the hypotheses of Sections 1–2, for every phase i,

    p^{-1}(A_i) = K_i,     A_i = p(K_i).                       (12)

Every connected component of every finite inverse image of a K_i is likewise saturated for p. This theorem does not assert saturation of the least hull S of the union of the K_i.

### 3.1. The model has precisely the requisite local degrees

For a connected periodically repelling quadratic polynomial r, write v for its Kiwi plane quotient and R for the induced degree-two branched covering. The fiber C of v(r(0)) is a nonseparating continuum containing the critical value. Its full inverse image under r is connected. For example, take a decreasing sequence of closed Jordan disks with intersection C and critical value in their interiors. Each preimage is a single closed disk: over the Jordan interior the degree-two covering is connected because it has a branch point, and its boundary is the connected lift of the boundary circle. The intersection of these nested disks is r^{-1}(C). By the semiconjugacy, its image under v is exactly R^{-1}(v(r(0))). This is a finite connected set, hence a singleton containing v(0). Thus R has local degree two at v(0). There are no other finite critical points of R, by Riemann–Hurwitz on the sphere (the fiber of infinity is a singleton of degree two). This argument applies both to f and to the straightening Q of f^P on K_0.

The point h(0) is the critical point of Q by the neighborhood conjugacy (we may normalize Q as monic centered). The homeomorphism H of Section 2 sends its quotient q(h(0)) to p(0). For y in A_0 and 1 <= j < P, g^j(y) belongs to A_j, disjoint from A_0. In particular none of these iterates equals p(0). Multiplicativity of local degrees now gives

    deg_y(g^P) = 2 if y = p(0), and 1 otherwise.

This is exactly deg_{H^{-1}(y)}(G), for G the induced degree-two map of the straightening Q. This step would not be justified from conjugacy of restrictions alone; it uses the disjoint primitive phases and the ambient critical-point computation.

### 3.2. A local sheet-exhaustion lemma

Let b and d be orientation-preserving finite branched coverings of planes, A and D nonempty compact connected sets, b(A)=A, d^{-1}(D)=D, and H:D→A a homeomorphism satisfying b H=H d on D. Suppose the local degrees satisfy deg_{H(u)} b=deg_u d at every u in D. Then A is a connected component of b^{-1}(A).

Proof. Fix u in D and a=H(u), and write e for the common local degree. Take small local branched-covering charts at u and a, with local model z↦z^e. For target points v in A sufficiently close to b(a), all e preimages, counted with multiplicity, of H^{-1}(v) in the chart of u belong to D by complete backward invariance. They converge to u as v tends to b(a), so their images under H are in the chart of a. Conjugacy makes them preimages of v. For v different from b(a) these are e distinct points, exhausting the e local sheets of b; at v=b(a) the local inverse consists of the one point a. Consequently every point in a sufficiently small neighborhood of a whose b-image is in A is itself in A. Thus A is relatively open in b^{-1}(A), as well as closed. Connectedness makes it a connected component. QED.

### 3.3. Recover the filled set from the full lift

Apply the lemma with b=g^P, d=G, D=Y_Q and A=A_0. The set Y_Q=q(K(Q)) is completely invariant under G: q maps the complement of K(Q) bijectively onto the complement of Y_Q and Q^{-1}(K(Q))=K(Q). All other hypotheses follow from Section 2 and 3.1. Hence A_0 is a relatively open and closed connected component of (g^P)^{-1}(A_0).

Set L=p^{-1}(A_0) (full plane preimage). The set L is compact and connected by monotonicity and properness of the plane quotient. It lies in X, contains K_0, and is full since X is full with empty interior: a bounded complementary component of L would be an open subset of X. From p f^P=g^P p we have that L is relatively open and closed in (f^P)^{-1}(L). Moreover f^P(L)⊂L. In fact f^P(L)=L: the restriction to L is relatively open onto L (for each point of L take an open neighborhood disjoint from the other preimages of L, then use openness of the polynomial), and its image is nonempty and compact, hence closed; L is connected.

Write F=f^P. Every finite periodic orbit of F is repelling. Thus L is a full invariant continuum, a component of F^{-1}(F(L)), with no attracting or parabolic periodic point. **Theorem B** of Blokh–Oversteegen–Ptacek–Timorin, *Quadratic-like dynamics of cubic polynomials*, applies to an arbitrary polynomial P (not only cubics): the component condition and inclusion of immediate attracting/parabolic basins when present characterize filled Julia sets of polynomial-like restrictions. The basin condition here is vacuous. Hence L is the filled Julia set of a polynomial-like restriction F:U_L→V_L.

This restriction has degree exactly two. The sole critical point of F in L is 0, and it has local degree two: for z in L, p(f^j(z)) lies in A_j, so f^j(z) cannot equal 0 for 1<=j<P. This also excludes a second critical encounter along the orbit of 0. Since L is connected, all critical points of the polynomial-like restriction belong to its filled set (the connectedness criterion for polynomial-like maps); Riemann–Hurwitz gives degree two. The original restriction on K_0 already has degree two and its filled set is contained in L. Each x in K_0 has exactly two preimages counted with multiplicity in K_0 under F. These exhaust the degree-two preimages in L. Thus F^{-1}(K_0) intersect L = K_0, and F(K_0)=K_0.

Straighten F:U_L→V_L to a quadratic polynomial Q_L. The image of K_0 is a compact completely invariant subset of K(Q_L) containing more than one point. It contains J(Q_L) by the standard minimality of the Julia set among closed completely invariant sets with at least two points in the plane (equivalently, density of backward orbits of nonexceptional points). But K(Q_L) has empty interior, since L⊂X and the straightening is an ambient homeomorphism near L. Therefore J(Q_L)=K(Q_L), the image of K_0 is all of K(Q_L), and K_0=L. This proves (12) for i=0.

### 3.4. The other phases and pullback components

For a complete plane fiber C=p^{-1}(y), the semiconjugacy expresses f^{-1}(C) as the union of the finitely many complete fibers over g^{-1}(y). These are pairwise disjoint compact connected sets, hence exactly the connected components of f^{-1}(C). Each is relatively open there, and maps onto C by the same open-and-closed argument used above. Iteration proves that every complete fiber maps onto its corresponding complete fiber under f^i.

For y in A_i choose u in A_0 with g^i(u)=y, possible because f^i(K_0)=K_i. The full fiber over u belongs to K_0 by (12) at i=0, so its f^i-image is the whole fiber over y and belongs to K_i. This proves (12) for all phases. Also, by the semiconjugacy, f^{-n}(K_i)=p^{-1}(g^{-n}(A_i)). Each fiber meeting one connected component of that set is contained in that component, because it is connected. Thus every such component is saturated.

### 3.5. References and exact proof boundary

* Jan Kiwi, *Real laminations and the topological dynamics of complex polynomials*, Adv. Math. 184 (2004), 207–267, Proposition 4.2, Corollary 4.6, Theorem 5.12: the quotient, induced branched cover and fiber characterization used in Sections 1–3.
* A. Blokh, L. Oversteegen, R. Ptacek, V. Timorin, *Quadratic-like dynamics of cubic polynomials*, Theorem B, full proof §4, manuscript pp. 17–18: https://people.cas.uab.edu/~ablokh/QL-revised-short-v-11-30-15.pdf . The general-polynomial statement was checked in the source text, not inferred from the paper's title. The immediate-basin clause is vacuous here. This imported theorem is essential to the argument, not a new result of this PR.
* A. Douady and J. H. Hubbard, *On the dynamics of polynomial-like mappings*, Ann. Sci. École Norm. Sup. 18 (1985), 287–343: straightening and the connected-filled-set critical-point criterion. Standard polynomial dynamics: J=boundary of K, and minimality among closed completely invariant sets with at least two finite points.
* The earlier predecessor note proves disjointness of the geometric marks; it does not itself prove their full saturation. The new argument above upgrades the restricted equivalence of Section 2 to a full-plane identity. It does not rely on an unproved assertion that every dynamical renormalization domain is described by rational cuts.

**Scope:** Actual primitive polynomial-like renormalization with pairwise disjoint phases, a periodically repelling ambient quadratic, and the canonical Kiwi plane quotient. Nothing in this proof assumes a priori local connectivity of X. It does not treat satellite phases meeting at a point, abstract combinatorial carriers, arbitrary maps with irrationally neutral cycles, saturation of S, or geometric/analytic control of the Wave collar. All imported statements and the argument require independent human review before any ledger promotion.
