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
