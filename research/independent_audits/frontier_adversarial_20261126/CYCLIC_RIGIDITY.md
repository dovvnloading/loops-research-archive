# A rigidity dichotomy for the one-quadratic cyclic carrier

Base main: 47806d64c64688bdf27c817f036cfdbfa85ce1d5.
Continuation of [least cyclic saturation](CYCLIC_SATURATION.md).
Status: written theorem with explicitly imported polynomial-like recognition and straightening, partial for MAPPING_TELESCOPE/H1.

## 1. The claim

Fix f(z)=z²+c with connected K(f)=J(f) of empty interior. Fix a physical time m≥1, not an abstract virtual period, and index phases modulo m. Consider tuples F_0,...,F_(m−1) of continua in X=J(f) satisfying:

* 0∈F_0; F_j is a connected component of f⁻¹(F_(j+1)).
* The one-step degrees are (2,1,...,1), counted with multiplicity.

There is **at most one** such tuple for this f and m. It exists if and only if f^m admits a quadratic-like restriction with connected filled set containing 0. If it exists, F_0 is exactly that filled set and F_j=f^j(F_0). No freedom remains to enlarge a phase to absorb a new mark while preserving this physical time, saturation and degree word.

This is a recognition/reduction theorem for the precise saturated physical input of the [cyclic telescope audit](../h1_mapping_telescope_20261126/NOTE.md), not an assertion that an arbitrary virtual return is an ordinary renormalization. We do not require pairwise disjoint phases, and we do not assert primitive rather than satellite type. A polynomial-like restriction at m=1 is included; no minimal-period convention is implicit.

## 2. Recognition, both directions

Write P=f^m. By one-step saturation F_j maps onto F_(j+1) and each point of the target has exactly the specified number of preimages in the source, with local multiplicities. Every component of f⁻ʳ(F_0) is obtained by successively pulling back one of the finitely many components at the preceding step. Indeed at each step the component lemma of CYCLIC_SATURATION.md §2 produces one or two compact disjoint components for each previous component; inverse sets of distinct previous components are disjoint compact sets. A finite family of pairwise disjoint compact sets cannot have a connected subset meeting two of them. Every such pullback component maps onto its parent.

Following the specified phase chain backwards therefore identifies F_0 with a component of P⁻¹(F_0), not just with a forward invariant subset. By multiplication of local multiplicities the number of P-preimages in F_0 of each point of F_0 is two. F_0 contains 0 and P(0), which are distinct because a periodic critical point would give a superattracting basin, impossible for empty-interior K(f). In particular it is nondegenerate. It is full by the least-hull lemma.

Apply Blokh–Oversteegen–Ptacek–Timorin (BOPT), *Quadratic-like dynamics of cubic polynomials*, Theorem B, printed p.17 of the author PDF (see §6). The theorem is for a general polynomial, despite the paper's title: an invariant full continuum which is a component of the inverse of its image, and contains the immediate basins or parabolic domains of any such periodic points on it, is a polynomial-like filled set. Here P has no finite attracting or parabolic periodic points at all: an open basin or petal would be an open subset of K(P)=K(f). Thus the additional hypothesis is vacuous. The degree of the resulting restriction is two because all preimages in its domain of points of its filled set lie in that filled set, and we already counted their multiplicities. Hence F_0 is an actual quadratic-like filled set of P.

Conversely let P:U'→U be a degree-two polynomial-like restriction with connected filled set Y containing 0. The equality K(P|U')=Y makes P⁻¹(Y)∩U'=Y; since Y is compactly inside U', it is both relatively open and closed in the global P⁻¹(Y), and connected, so is one full inverse component. Y⊂K(f) because its P-orbit is bounded and there are only finitely many intermediate f-iterates between consecutive P times (all polynomial images of a fixed bounded set are bounded). It is nondegenerate and full. The component argument above shows that f^j(Y), 0≤j<m, are the successive ancestor components of Y in the global pullback tree. Their one-step degrees multiply to two. Since the first source contains 0, its target contains c, so its first degree is two; every other degree is one. This gives the required tuple.

## 3. Uniqueness: no alternative saturated hull at the same time

Let there be two such tuples F and G. They both contain every phase of the forward orbit of 0. In particular use the anchors a_j=f^j(0), seeds {a_j,f(a_(j−1))} (indices cyclic, so the extra seed in phase zero is P(0)), and insert c in the degree-two target. The degree-prescribed construction of CYCLIC_SATURATION.md gives a least tuple H⊂F,G: it cannot fail because both witnesses exist. Its phase zero contains 0 and P(0), hence is nondegenerate.

For every y∈H_0, both P|H_0 and P|F_0 have exactly two preimages of y with multiplicity. Since H_0⊂F_0, the sets of these preimages are identical. Consequently H_0 is completely invariant relative to the polynomial-like return on F_0. Apply connected-case Douady–Hubbard straightening to this actual return: the conjugacy on neighborhoods carries F_0 to K(Q) for a quadratic polynomial Q. Because F_0 has empty interior, K(Q)=J(Q). The image L of H_0 is a nondegenerate compact subset of J(Q) and satisfies Q⁻¹(L)=L: all global Q-preimages of its points lie in K(Q), and the relative invariance accounts for them all. In the complement of L every iterate of Q omits any three distinct points of L, so Montel's theorem makes the family normal there. Therefore J(Q)⊂L, and L=J(Q). Thus H_0=F_0. Repeating for G gives H_0=G_0, and the other phases are its forward images. QED.

This proof does not use local connectivity, a priori bounds, or rigidity across parameters. It is uniqueness of the *physical carrier inside a fixed polynomial* at a specified time and degree, not uniqueness of a parameter with specified combinatorics.

## 4. An orbit-only exact criterion and the mark absorption obstruction

Use the canonical seeds in §3. Theorem B of CYCLIC_SATURATION.md constructs their increasing limit H after a single countable block, by simultaneous forward images, selected inverse components and least Julia hulls. Then:

* If c belongs to any target other than phase 1 (indices modulo m), no such restriction exists at physical time m.
* If c avoids every such target, the tuple is fixed and gives a quadratic-like restriction by §2. No additional unknown carrier-existence hypothesis remains at the unmarked set level.
* If locations L_j, pairwise phase disjointness, or additional source atoms are prescribed, test them directly on H. Because §3 proves uniqueness, an atom outside H cannot be accommodated by an enlarged alternative degree-two saturated cycle at the same physical time.
* If a required connected obstacle meets H_j and is not contained in it, the requested separated-or-absorbed marking is impossible on such a cycle: a connected set cannot meet both members of a disjoint compact pair, and there is no permissible larger carrier. If it is disjoint or contained, this particular test passes. For finite forward-closed connected obstacle inventories, the complement-of-H union gives the separated compact remainder, provided it contains the other required marked points. A general infinite inventory still requires a compactness/separation test.

The minimal hull in §3 is determined by the critical orbit and the actual polynomial; it is not determined by the combinatorial period alone. The criterion is an exact mathematical equivalence, not an effective algorithm to decide an arbitrary parameter from a finite number of orbit samples. It does not provide uniform moduli or any new rigidity in the parameter plane.

## 5. Actual archive application and the failure boundary

For the archive's real 3/9 Misiurewicz tip, the [cell-tree audit](../h1_cell_tree_extraction_20261126/NOTE.md), §4, records the genuine period-nine filled interval K9=[x9,x18] with x_j=f^j(0), x18=−x9 and a proper degree-two return. The analytic identification of that interval and its phase cycle is imported from the named source-locked archive proofs; the present note does not independently recompute the parameter enclosure.

At physical time m=9 the canonical seed closure must recover exactly K9 and its eight images by the theorem. More concretely: the phase-zero seeds contain x0 and x9. Nine forward one-step propagation rounds force x18 into phase zero; the Julia hull of the two endpoints is precisely K9, since K9 is a real interval and itself a subcontinuum of X. Every saturated witness is K9 at phase zero and its images elsewhere. Eight further rounds force each phase to contain the corresponding image; containment in the known cycle gives equality. Thus the countable construction actually stabilizes by round 17 for this particular physical input (an upper bound, not a minimal-round claim).

By contrast, the exact two-phase Chebyshev failure in CYCLIC_SATURATION.md §5 is a genuine obstruction to that physical time/degree word. The same mechanism must be applied before interpreting a retimed virtual return as a saturated cycle; if it is not the ordinary quadratic-like filled set at its physical time, one of the assumptions fails. A genuine nonordinary virtual construction may use an open chain, degree changes, partial surfaces or nonperipheral covers; this theorem does not rule those out. It explains why simply relabeling an ordinary saturated cycle cannot supply the missing native nonordinary geometry.

The actual 3/9 tip example proves no uniform bound across parameters or arbitrary virtual scales. No H1 ledger row is promoted. In particular no conclusion about protected accesses, WAD width, H2–H4, UPTCR or MLC is drawn.

## 6. Source verification and attribution

* A. Blokh, L. Oversteegen, R. Ptacek, V. Timorin, *Quadratic-like dynamics of cubic polynomials*, author PDF https://bpb-us-w2.wpmucdn.com/sites/uab.edu/dist/0/610/files/2025/09/QL-revised-short-v-11-30-15.pdf , Theorem B, printed p.17 (PDF page index 16; theorem text and rendered page inspected). The archive's prior cyclic telescope audit uses the same recognition theorem. No new proof of this imported theorem or byte-hash claim is made.
* A. Douady and J. H. Hubbard, *On the dynamics of polynomial-like mappings*, Ann. Sci. Éc. Norm. Sup. 18 (1985), 287–343, Theorem 1 pp.296–297, https://www.numdam.org/item/ASENS_1985_4_18_2_287_0/ . Connected straightening and its conjugacy on the filled set; standard Montel normal-family criterion. The straightening source citation is inherited from the archive.
* The least-hull argument, component continuity and countable construction are in the preceding commit. No claim that the above recognition/uniqueness theorem is new to the mathematical literature; its explicit reduction of the archive's saturation and mark-enlargement problem is the contribution.

AI disclosure: GPT-6.2 developed the written deductions, checked the BOPT theorem statement and drafted this note. No independent specialist review or Lean formalization.
