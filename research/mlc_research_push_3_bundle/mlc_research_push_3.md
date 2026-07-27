# Research Push III: end rescaling, adaptive plumbing response, and finite-horizon transfer

**Project:** A marked-width reduction of Mandelbrot local connectivity  
**Status:** theorem-level research note; no unconditional proof of MLC is claimed  
**Date:** 2026-07-24

---

## Executive result

The manuscript's next geometric obstruction was the infinite-address end of the first direct-decoration pullback system. Finite cylinders carry actual polynomial branches, but their Euclidean realizations collapse toward connected end impressions. A literal nondegenerate analytic map on the unrescaled planar impression is therefore the wrong target.

This note develops the corrected analytic category and then pushes through the first quantitative coupling estimate.

The main results are:

1. **Canonical direct-limit end surface.** Every infinite address has a direct-limit Riemann surface canonically biholomorphic to the normalized root quadratic-like domain. The finite retimed covering/immersion pairs descend to the exact normalized root pair.
2. **Exact finite realization.** Every finite, depth-graded proof diagram on finitely many end surfaces has a realization at finite cylinder depth by genuine iterates of the original map. Dynamical paths are actual iterates; presentation changes remain explicitly typed conformal coordinate maps.
3. **Intrinsic finite pseudo-puzzle transfer.** A finite externally marked puzzle or pseudo-puzzle atlas can be constructed on an externally marked connected quadratic-like map from its own external class. This avoids using uniqueness of a hybrid conjugacy or downstream rigidity.
4. **Recursive finite-scale virtual portraits.** A finite decorated quadratic-like chain can be unfolded recursively on normalized end surfaces. The construction is functorial relative to the declared external markings and finite source atlases.
5. **Exact fiberwise width and response.** Extremal length, finite-electrode Dirichlet-to-Neumann response, and any fully transported conformally natural finite WAD/Value module are exactly invariant under the end coordinate.
6. **Serial puzzle-neck estimate.** The ray/equipotential cells along an address form a series of conformally repeated quadrilaterals. Their electrical resistances add. A depth-
   \(m\) tail has conductance at most
   \[
   \left(\sum_{j=1}^m R_{a_j}\right)^{-1}.
   \]
7. **Adaptive nodal-response theorem.** For a finite proof-use family of end bubbles, the response of a sufficiently deep physical materialization differs from the disconnected nodal response by an explicitly bounded positive-semidefinite perturbation. Given any predetermined tolerance \(\varepsilon>0\), finite depths can be chosen so the operator-norm error is at most \(\varepsilon\).
8. **Direct-decoration finite-horizon inflation.** A finite normalized end diagram with one quadratic relative stage can be materialized as an actual finite-horizon pseudo-quadratic-like program with exact critical chronology and arbitrarily small plumbing-response error.
9. **Strict-transition transfer.** Any source-licensed strict root-block contraction in an error-stable gauge survives the virtual end materialization with the same homogeneous contraction coefficient and a prescribed additive plumbing error.

The important qualification is equally precise:

> The direct-limit surface is a source-faithful rescaling pro-object built from actual finite pullbacks. It is not, by itself, an identification of Dudko's proposed Cantor family with nondegenerate small Julia continua inside the original unrescaled plane.

Accordingly, this note closes several formal and quantitative subgates, but it does not by itself promote the original global virtual-Cantor realization theorem or MLC.

---

# Part I. Source boundary and exact setup

## 1. What the sources provide and what remains open

The direct-decoration source supplies an actual ray/equipotential puzzle, a least critical escape depth, actual first-return domains, and two univalent pullbacks of the relevant separator. It also records that the pullback pieces are attached along boundary rays and that extremal length and width obey the conformal, series, and parallel laws.

The current virtual-Molecule proposal does not supply a completed analytic family at every infinite address, a protected global carrier, a finite future-observable coupling state, a mixed backward transition, compactness, or rigidity. Those remain source-facing theorems.

The present note uses only:

- actual finite pullback branches;
- a finite externally marked root quadratic-like portrait;
- the source ray/equipotential geometry of the direct-decoration puzzle;
- standard conformal invariance and Dirichlet principles;
- the finite carrier and compiler modules already proved in the manuscript and Research Pushes I-II.

No a priori bound, compactness conclusion, phase-parameter theorem, rigidity theorem, or MLC conclusion is assumed.

## 2. Direct-decoration inverse system

Let \(P\) be a closed Jordan puzzle disk and put

\[
 g=f^q.
\]

Let \(\mathcal A\) be a finite alphabet; in the first direct-decoration application \(\mathcal A=\{0,1\}\). Assume that for every \(a\in\mathcal A\) there is a closed Jordan pullback

\[
 Q_a\subset P
\]

such that

\[
 g:Q_a\longrightarrow P
\]

is a conformal homeomorphism. Write

\[
 \phi_a:P\longrightarrow Q_a
\]

for its inverse branch. For a word \(w=a_1\cdots a_m\), define

\[
 \phi_w=\phi_{a_1}\circ\cdots\circ\phi_{a_m},
 \qquad
 Q_w=\phi_w(P),
\]

and

\[
 h_w=g^m|_{Q_w}:Q_w\longrightarrow P.
\]

Thus \(h_w=\phi_w^{-1}\).

Two operations must remain distinct:

- **dynamical shift:** \(g(Q_{aw})=Q_w\), deleting the first letter;
- **geometric parent:** \(Q_{wa}\subset Q_w\), deleting the last letter in the reverse direction.

## 3. Root portrait

Let

\[
 F=f^r|_A:A\longrightarrow B
\]

be a connected quadratic-like restriction with

\[
 K\Subset A\Subset B\Subset\operatorname{int}P,
\]

where \(K\) is its filled Julia set. Let

\[
 \jmath:A\hookrightarrow B
\]

be inclusion. The root pseudo-quadratic-like pair is

\[
 (F,\jmath):A\rightrightarrows B.
\]

Fix a finite root marking \(\mathcal M\), including every item used later:

- protected prime-end chains and endpoint phases;
- ideal intervals and their cyclic order;
- selected component, parent, sheet, and critical-word data;
- obstacle and localization records;
- finite response electrodes and Value-feature rows;
- certified enlargement maps.

For a finite word \(w\), set

\[
 A_w=h_w^{-1}(A),
 \qquad
 K_w=h_w^{-1}(K).
\]

The finite retimed pair is

\[
 G_w=F\circ h_w=f^{q|w|+r}|_{A_w}:A_w\longrightarrow B,
\tag{3.1}
\]

\[
 I_w=\jmath\circ h_w=f^{q|w|}|_{A_w}:A_w\longrightarrow B.
\tag{3.2}
\]

The common univalent prefix cancels in the relative map:

\[
 G_w\circ I_w^{-1}=F\circ\jmath^{-1}
\tag{3.3}
\]

on \(\jmath(A)\).

The relative critical word of \((G_w,I_w)\) is therefore exactly the root critical word. The absolute word of \(G_w\) is the \(q|w|\)-step univalent prefix followed by the word of \(F\).

---

# Part II. Canonical end-rescaling surfaces

## 4. Geometric-prefix maps

Fix an infinite address

\[
 \omega=a_1a_2\cdots\in\mathcal A^{\mathbb N},
\]

and write \(w_m=\omega|m\). The correct map from one geometric prefix presentation to the next is

\[
 t_m=h_{w_{m+1}}^{-1}\circ h_{w_m}:
 A_{w_m}\longrightarrow A_{w_{m+1}}.
\tag{4.1}
\]

It is a conformal isomorphism satisfying

\[
 h_{w_{m+1}}\circ t_m=h_{w_m}.
\tag{4.2}
\]

Consequently,

\[
 G_{w_{m+1}}\circ t_m=G_{w_m},
 \qquad
 I_{w_{m+1}}\circ t_m=I_{w_m}.
\tag{4.3}
\]

The same compatibility holds for \(K_{w_m}\) and every pulled entry of \(\mathcal M\).

## 5. Canonical direct limit

### Theorem 1 - End-rescaling pseudo-quadratic-like surface

Define

\[
 \widehat A_\omega=\varinjlim(A_{w_m},t_m).
\]

Then:

1. The maps \(h_{w_m}\) induce a biholomorphism
   \[
   h_\omega:\widehat A_\omega\longrightarrow A.
   \tag{5.1}
   \]
2. The compatible finite maps induce holomorphic maps
   \[
   \widehat G_\omega,\widehat I_\omega:
   \widehat A_\omega\longrightarrow B
   \]
   with
   \[
   \widehat G_\omega=F\circ h_\omega,
   \qquad
   \widehat I_\omega=\jmath\circ h_\omega.
   \tag{5.2}
   \]
3. The direct-limit carrier
   \[
   \widehat K_\omega=\varinjlim(K_{w_m},t_m)
   \]
   is carried homeomorphically to \(K\). It is compact, connected, nonempty, and full in the normalized end surface.
4. The pair
   \[
   (\widehat G_\omega,\widehat I_\omega):
   \widehat A_\omega\rightrightarrows B
   \]
   is marked-isomorphic to the root pair \((F,\jmath)\).
5. Its proper degree, local degrees, relative critical word, protected prime-end action, cyclic order, obstacles, localization, response electrodes, and all finite data in \(\mathcal M\) are exactly the root data.

#### Proof

Take the quotient of \(\bigsqcup_mA_{w_m}\) by the equivalence generated by \(z\sim t_m(z)\). Since every transition is a conformal isomorphism, the quotient has a unique Riemann-surface structure making all level maps conformal.

Equation (4.2) makes

\[
 h_\omega([z,m])=h_{w_m}(z)
\]

well defined. It is a conformal bijection onto \(A\), proving (5.1). Equation (4.3) makes the finite pairs constant on equivalence classes, yielding (5.2). The carrier and all marked data descend by the same argument. Under \(h_\omega\), every assertion is exactly the corresponding root assertion. ∎

### Corollary 2 - Relative uniqueness

Once the root normalization and the finite inverse branches are fixed, any direct-limit presentation whose coordinate agrees with all \(h_{w_m}\) is uniquely marked-biholomorphic to \(\widehat A_\omega\).

This uniqueness is relative to the declared root normalization. It is not a rigidity statement about arbitrary hybrid presentations.

## 6. Dynamic shift

Let

\[
 \sigma(a_1a_2\cdots)=a_2a_3\cdots.
\]

At finite levels,

\[
 g:A_{a_1\cdots a_{m+1}}
 \longrightarrow A_{a_2\cdots a_{m+1}}
\]

is conformal and obeys

\[
 h_{a_2\cdots a_{m+1}}\circ g
 =h_{a_1\cdots a_{m+1}}.
\tag{6.1}
\]

### Theorem 3 - End-shift naturality

The maps in (6.1) induce a biholomorphism

\[
 \widehat S_\omega:
 \widehat A_\omega\longrightarrow\widehat A_{\sigma\omega}
\]

such that

\[
 h_{\sigma\omega}\circ\widehat S_\omega=h_\omega.
\tag{6.2}
\]

Hence the dynamic shift is the identity in normalized coordinates. Moreover,

\[
 \widehat G_{\sigma\omega}\circ\widehat S_\omega
 =\widehat G_\omega,
\qquad
 \widehat I_{\sigma\omega}\circ\widehat S_\omega
 =\widehat I_\omega.
\tag{6.3}
\]

Every transported finite marking commutes with the shift.

#### Proof

Use \(g\) from a sufficiently deep level of the \(\omega\)-system to the corresponding level of the \(\sigma\omega\)-system. Equation (6.1) gives compatibility with the geometric-prefix maps. The induced direct-limit map satisfies (6.2), hence is biholomorphic and gives (6.3). ∎

### Remark 4 - Two identities with different metadata

Both \(t_m\) and the normalized shift become identities under the root coordinate, but they are not the same operation:

- \(t_m\) changes geometric presentation depth;
- \(g=f^q\) is an actual forward dynamical iterate and changes the address by left shift.

They must remain separately typed in every proof ledger.

## 7. Exact scope

Theorem 1 constructs a canonical **rescaled analytic fiber** from actual finite pullbacks. It does not prove that the planar impression

\[
 E_\omega=\bigcap_mQ_{\omega|m}
\]

is itself a nondegenerate small Julia set, nor that Dudko's full proposed Cantor component family has already been identified in the original plane.

This distinction is essential. The direct-limit object is a pro-exact renormalization object; source identification with a particular planar virtual component remains a separate theorem.

---

# Part III. Compact support relation and finite physical realization

## 8. Normalized carrier bundle

Let

\[
 \Omega_\partial=
 \{w\#^\infty:w\in\mathcal A^{<\mathbb N}\}
 \cup\mathcal A^{\mathbb N}
\]

be the rooted-end compactification. Define

\[
 \mathscr K=\Omega_\partial\times K.
\]

For a finite address \(w\#^\infty\), define

\[
 \operatorname{ev}_w(z)=\phi_w(z).
\tag{8.1}
\]

At an infinite address retain the planar support \(E_\omega\).

Define the relation

\[
 \mathcal R\subset\mathscr K\times P
\]

by

\[
 ((w\#^\infty,z),x)\in\mathcal R
 \iff x=\phi_w(z),
\tag{8.2}
\]

and

\[
 ((\omega,z),x)\in\mathcal R
 \iff x\in E_\omega.
\tag{8.3}
\]

### Theorem 5 - Closed support relation

The relation \(\mathcal R\) is closed and has compact fibers. It is equivariant in the sense that

\[
 f^q\bigl(\mathcal R(a\xi,z)\bigr)
 \subseteq\mathcal R(\xi,z),
\tag{8.4}
\]

with equality on finite fibers and equality on an infinite support whenever

\[
 f^q(E_{a\omega})=E_\omega.
\]

#### Proof

Let \(((\xi_n,z_n),x_n)\in\mathcal R\) converge to \(((\xi,z),x)\). If \(\xi\) is finite, it is isolated in \(\Omega_\partial\), so the evaluation word is eventually constant and continuity gives the claim.

If \(\xi=\omega\) is infinite, then for every fixed \(k\), all sufficiently large finite words \(\xi_n\) begin with \(\omega|k\), and all sufficiently close end addresses have the same fixed prefix. Thus eventually

\[
 x_n\in Q_{\omega|k}.
\]

Since the cylinder is closed, \(x\in Q_{\omega|k}\) for every \(k\), hence \(x\in E_\omega\). Equivariance follows from \(f^q\circ\phi_{aw}=\phi_w\) and the end-support identity. ∎

### Remark 6 - What the support relation does not assert

The relation deliberately does not select a point of a non-singleton impression. More refined source data may later produce a smaller relation or a point-valued landing map. Nothing in the current direct-decoration input licenses such a choice uniformly.

## 9. Depth-graded finite diagrams

A finite normalized proof diagram \(\mathcal D\) consists of finitely many normalized end-fiber nodes and finitely many edges of the following types:

1. root dynamical restrictions;
2. covering/immersion pairs;
3. dynamic shifts;
4. geometric presentation changes;
5. certified package/enlargement squares;
6. finite marked outputs.

The diagram must carry an integer **shift grading** \(s(v)\) on its nodes such that:

- a root dynamical edge preserves \(s\);
- a presentation or enlargement edge preserves \(s\);
- a forward shift edge \(u\to v\) satisfies \(s(u)=s(v)+1\).

Equivalently, every two directed paths with the same endpoints have the same net number of shift edges after presentation edges are ignored. If this fails, the diagram is not a single finite-level physical diagram and must first be unfolded by duplicating the conflicting node.

## 10. Finite realization theorem

### Theorem 7 - Exact finite realization of a depth-graded end diagram

Let \(\mathcal D\) be a finite depth-graded diagram. Assume all root restrictions and root marked squares are actual. Then there is an integer \(M\) such that every node \(v\) can be represented at physical prefix depth

\[
 m(v)=M+s(v)\ge0,
\]

and the following hold:

1. Each normalized end carrier is represented by an actual finite cylinder pullback.
2. Each root branch \(f^{r_e}\) is represented by the retimed pair
   \[
   (f^{qm(v)+r_e},f^{qm(v)}).
   \]
3. Each shift edge is represented by the actual map \(f^q\).
4. Every purely dynamical path is a genuine iterate on a nonempty actual domain, with exact summed exponent and complete chronological critical word.
5. Presentation changes are represented by their explicit conformal coordinate maps; they are not mislabeled as polynomial iterates.
6. Every component, parent, sheet, obstacle, localization, prime-end, cyclic-order, relative-cover, response, and Value record agrees with the normalized diagram.
7. Certified enlargement and presentation squares commute exactly.

#### Proof

Choose \(M\ge-\min_vs(v)\). At a node \(v\), pull all root domains and markings back by the cylinder chart of depth \(m(v)\). Root edges use (3.1)-(3.2). The grading makes every shift source exactly one level deeper than its target, so (6.1) realizes the shift by \(f^q\). Presentation maps use (4.1).

Every generating square follows from (4.3), (6.1), and the corresponding actual root square. Compositions of dynamical edges are actual compositions of polynomial restrictions. Their critical chronology is the chronological concatenation verified by the stagewise critical-degree ladder and critical-spine assembly from Research Push II. Finiteness lets one common \(M\) work for all compactly contained root data. ∎

### Corollary 8 - Pro-exactness

Every finite theorem invocation on a normalized end surface has an exact finite-cylinder representative. A holomorphic map on the unrescaled impression \(E_\omega\) is not needed for a finite proof horizon.

### Corollary 9 - No horizon cycle

The normalized end surface is constructed before a stopping rule. After a finite horizon is frozen, Theorem 7 chooses a materialization depth. Thus analytic existence and horizon selection are not defined from each other.

---

# Part IV. Intrinsic finite pseudo-puzzle atlases and recursion

## 11. Why arbitrary hybrid presentation is not enough

A hybrid conjugacy is not a rigidity theorem, and its uniqueness must not be assumed. Consequently, a recursive virtual selector should not depend on choosing one arbitrary hybrid conjugacy and then declaring its pulled puzzle canonical.

The correct finite object is the externally marked pseudo-puzzle of the quadratic-like map itself.

## 12. Intrinsic finite external atlas

Let

\[
 H:U\longrightarrow V
\]

be a connected quadratic-like map with a declared external marking. Fix a finite forward-compatible list of rational external angles, an equipotential level in the external annulus, and a finite pullback depth. Assume the corresponding periodic or preperiodic accesses are source-authorized; when Euclidean landing is unavailable, work in the prime-end compactification.

Use the external class of \(H\) to construct the selected ray/access arcs and equipotential arcs. Pull them back by actual iterates of \(H\), and take the actual connected components cut out by this finite graph.

### Theorem 10 - Intrinsic finite pseudo-puzzle atlas

The preceding construction yields a finite marked pseudo-puzzle atlas with:

1. actual open component domains;
2. actual branch restrictions \(H^n\);
3. exact integer return times;
4. exact total and local degrees and chronological critical words;
5. actual component, parent, sheet, and obstacle records;
6. prime-end phase and cyclic order fixed by the external marking;
7. first-return and niceness properties determined from the actual orbit and pullback graph;
8. functorial transport under an externally marked conjugacy of the declared finite atlas.

If a straightening polynomial is used to import the finite combinatorial list, the embedded atlas on \(H\) is still defined by the external class and actual pullbacks of \(H\), not by an unproved uniqueness of the hybrid conjugacy.

#### Proof

The external marking fixes the angular phase of the degree-two external covering. The finite ray/equipotential graph is therefore determined in the prime-end external class. Its pullbacks are actual pullbacks under \(H\). Components, return exclusions, parent relations, and degree words are read from these actual pullbacks. A marked conjugacy preserving the finite external graph carries components and branches to the corresponding components and branches. No rigidity or uniqueness of a global hybrid conjugacy is used. ∎

## 13. Decorated quadratic-like chains

A finite decorated chain consists of externally marked connected quadratic-like maps

\[
 F_0,F_1,\ldots,F_s
\]

such that, for each \(j<s\):

1. the straightening/external combinatorics of \(F_j\) lies in the declared direct-decoration class;
2. a finite intrinsic atlas of the form in Theorem 10 is fixed;
3. the next portrait \(F_{j+1}\) occurs as an actual localized renormalization in the terminal gap of that atlas;
4. all finite markings required at the next scale are contained in the authorized localization.

These are source data. The theorem below compiles them; it does not manufacture an unprovided next renormalization.

### Theorem 11 - Recursive fibered portrait compiler

Every finite decorated chain admits a recursive normalized realization with:

1. a compact finite-depth product address space;
2. one canonical direct-limit end surface at every infinite address of each completed scale;
3. actual finite-word retimed pairs;
4. exact dynamic shifts and separately typed geometric-parent maps;
5. an intrinsic finite pseudo-puzzle atlas at the next scale;
6. exact critical, sheet, access, obstacle, and terminal data;
7. prefix-local construction: scale \(j+1\) uses only the normalized map and declared finite atlas at scale \(j\);
8. exact finite physical realization of every finite multi-scale diagram;
9. covariance, rather than unproved equality, under a change of externally marked presentation.

#### Proof

Proceed by induction. The one-scale case is Theorems 1, 3, 5, 7, and 10. At scale \(j\), every end fiber is marked-isomorphic to the normalized map \(F_j\). Apply its declared intrinsic atlas and localize the actual next portrait \(F_{j+1}\). Then apply Theorem 1 fiberwise.

A finite multi-scale diagram uses finitely many scales and addresses. Starting at the deepest scale, choose finite prefix representatives; then recursively choose prefixes at the preceding scales large enough to realize the already finite pulled diagram. Theorem 7 gives actual iterates at every stage. A different marked presentation induces marked isomorphisms of the declared finite atlases and hence a covariant recursive system. ∎

### Exact scope

Theorem 11 removes the **formal recursion circularity** for a finite source-supplied decorated chain. It does not prove that every virtual-Molecule block supplies the required intrinsic atlas, localized next portrait, protected carrier, or uniform finite observable quotient.

---

# Part V. Exact fiberwise width and response

## 14. Marked conformal state

Let \(X\subset A\setminus K\) be the root marked complement localization carrying a declared curve family \(\Gamma\) and finitely many smooth or prime-end electrodes. Put

\[
 X_w=h_w^{-1}(X),
 \qquad
 \widehat X_\omega=h_\omega^{-1}(X).
\]

Transport every marked curve, electrode, component label, and orientation by the same maps.

### Theorem 12 - Exact marked-width identity

For every finite word \(w\) and infinite address \(\omega\),

\[
 \operatorname{Ext}_{X_w}(h_w^{-1}\Gamma)
 =\operatorname{Ext}_X(\Gamma)
 =\operatorname{Ext}_{\widehat X_\omega}(h_\omega^{-1}\Gamma).
\tag{14.1}
\]

Where finite and nonzero, reciprocal extremal widths are equal as well. There is no address-depth error.

#### Proof

Extremal length is invariant under marked conformal isomorphism. ∎

### Theorem 13 - Exact finite-electrode response identity

Let \(\Lambda_X\) be the Dirichlet-to-Neumann response matrix of the root marked surface in a fixed electrode order. Then

\[
 \Lambda_{X_w}=\Lambda_X
 =\Lambda_{\widehat X_\omega}.
\tag{14.2}
\]

Parallel gluing and Schur-complement elimination commute with this equality.

#### Proof

Two-dimensional Dirichlet energy is conformally invariant. The marked conformal maps retain electrode order and orientation. Schur complements and parallel sums are algebraic operations on the same matrix. ∎

### Corollary 14 - Exact fiberwise WAD/Value transport

Any finite WAD, response, or Value state whose complete defining data are natural under the marked conformal isomorphism satisfies

\[
 Z_w=Z_\omega=Z.
\tag{14.3}
\]

This applies only when all coefficient rows, endpoint frames, incidence maps, and future observations defining \(Z\) have been retained.

### Corollary 15 - Identity virtual chart

The pure univalent address corridor is an identity chart on the fully transported normalized homogeneous state. It supplies neither strict contraction nor expansion. It must be grouped with a root dynamical, entropy, pseudo-Siegel, transient, or shear-resolving block that supplies the strict margin.

Fiber-internal chart error is zero. Coupling to a common physical carrier is a separate issue addressed next.

---

# Part VI. Serial puzzle necks

## 15. Root neck quadrilaterals

In the source direct-decoration puzzle, a child pullback \(Q_a\) is bounded laterally by the appropriate external-ray sides and has a deeper outer equipotential arc than \(P\). Choose a closed subquadrilateral

\[
 C_a\subset P\setminus\operatorname{int}Q_a
\]

whose horizontal sides lie on the parent and child equipotential cross-sections and whose vertical sides lie on the two authorized ray/access sides. The subquadrilateral is chosen away from vertices, protected collars, and obstacles.

Let \(\mathcal V_a\) be the family of curves in \(C_a\) joining the two equipotential cross-sections, and define its resistance

\[
 R_a=\operatorname{Ext}_{C_a}(\mathcal V_a)>0.
\tag{15.1}
\]

For a fixed actual block, the alphabet is finite, so

\[
 R_*=\min_{a\in\mathcal A}R_a>0.
\tag{15.2}
\]

No uniform lower bound over all blocks is asserted.

For \(w=a_1\cdots a_m\), define

\[
 C_{w,j}=\phi_{a_1\cdots a_{j-1}}(C_{a_j}),
 \qquad 1\le j\le m.
\tag{15.3}
\]

These are conformal copies with resistance \(R_{a_j}\).

## 16. Serial-exhaustion hypothesis

The marked address localization is called **serially exhaustive** if every authorized curve joining the deep cylinder side to the parent exterior contains, in chronological order, a subcurve crossing each \(C_{w,j}\) from its child cross-section to its parent cross-section.

This is a geometric statement about the declared localization and walls. It is satisfied by the ray/equipotential sector when its side rays are retained as boundary or protected walls. A claimed application must record the two side walls and both cross-sections at every stage.

### Theorem 16 - Serial resistance growth

Under serial exhaustion, the effective resistance \(R(w)\) from the depth-\(m\) cylinder to the parent side obeys

\[
 R(w)\ge\sum_{j=1}^mR_{a_j}\ge mR_*.
\tag{16.1}
\]

Consequently, the two-terminal conductance \(c(w)=R(w)^{-1}\) satisfies

\[
 c(w)\le
 \left(\sum_{j=1}^mR_{a_j}\right)^{-1}
 \le\frac1{mR_*}.
\tag{16.2}
\]

#### Proof

The interiors of the pulled quadrilaterals are pairwise disjoint. Every authorized connecting curve contains a crossing of each cell in series. The extremal-length Series Law gives the first inequality. Conformal invariance gives the exact resistance \(R_{a_j}\) of each pulled cell. The remaining inequalities are immediate. ∎

### Failure certificate

A failed use of Theorem 16 must identify the first stage at which one of the following occurs:

- a side wall is absent;
- a protected collar or obstacle destroys the quadrilateral;
- the child/parent cross-sections cease to be disjoint;
- an authorized bypass avoids the declared cell;
- the localization leaves the source puzzle sector.

Merely observing that two pieces share boundary rays is not a failure; the relevant object is the positive-modulus ray/equipotential quadrilateral between their cross-sections.

---

# Part VII. Adaptive nodal-response approximation

## 17. Finite collection of end bubbles

Let \(S=\{\omega_1,\ldots,\omega_s\}\) be the finite set of end addresses read by a resolved proof horizon. Choose a separating prefix depth \(d\) so that the words \(\omega_i|d\) are pairwise distinct. Beyond depth \(d\), choose additional tail lengths \(\ell_i\ge1\).

Cut the physical marked surface across the parent-side cross-section of the last \(\ell_i\)-cell serial neck for each selected address. The cuts are pairwise disjoint after the separating depth. The cut surface has:

- one base component, containing all shared prefixes and external terminals;
- one bubble component for each selected end address, carrying the exact normalized finite response module.

Let

\[
 \Lambda_{\mathrm{phys}}
\]

be the response matrix before cutting, and let

\[
 \Lambda_{\mathrm{node}}
\]

be the block-diagonal response of the cut normalization, in the same global terminal order. The latter is the electrical response of the nodal limit: a node has zero capacity, so the normalization components have independent constant modes.

For the \(i\)-th tail put

\[
 \mathcal R_i=\sum_{j=d+1}^{d+\ell_i}R_{(\omega_i)_j},
 \qquad
 c_i=\mathcal R_i^{-1}.
\tag{17.1}
\]

By Theorem 16, the actual tail conductance is at most \(c_i\).

## 18. Energy comparison

We use the convention

\[
 x^T\Lambda x=
 \min\{\text{Dirichlet energy of a function with terminal values }x\}.
\tag{18.1}
\]

### Theorem 17 - Quantitative nodal-response approximation

On the quotient by componentwise constants,

\[
 0\preceq
 \Lambda_{\mathrm{phys}}-\Lambda_{\mathrm{node}}.
\tag{18.2}
\]

Moreover, for every terminal vector \(x\),

\[
 0\le
 x^T(\Lambda_{\mathrm{phys}}-\Lambda_{\mathrm{node}})x
 \le
 \left(\sum_{i=1}^sc_i\right)
 \operatorname{osc}(x)^2,
\tag{18.3}
\]

where

\[
 \operatorname{osc}(x)=\max_jx_j-\min_jx_j.
\]

Hence

\[
 \left\|
 \Lambda_{\mathrm{phys}}-\Lambda_{\mathrm{node}}
 \right\|_{\mathrm{op}}
 \le
 2\sum_{i=1}^sc_i
 \le
 2\sum_{i=1}^s\frac1{\ell_iR_{*,i}},
\tag{18.4}
\]

where \(R_{*,i}\) is the minimum cell resistance on the selected tail.

#### Proof

Cutting the necks removes nonnegative coupling energy and lets the normalization components choose their attachment constants independently. Therefore the minimum energy cannot increase after cutting, proving (18.2).

Let \(u_\infty\) be the collection of energy minimizers on the cut components. On every component with terminals, the maximum principle puts the free attachment value between the minimum and maximum terminal values of that component. On a component without terminals, choose its constant to match an adjacent value. Thus the difference between the two endpoint values of every cut neck is at most \(\operatorname{osc}(x)\).

Join the two endpoint values across the \(i\)-th neck by its two-terminal energy minimizer. Its energy is at most \(c_i\operatorname{osc}(x)^2\). Together with \(u_\infty\), these interpolants give an admissible function on the connected physical surface. This proves (18.3).

Finally,

\[
 \operatorname{osc}(x)^2\le2\|x\|_2^2,
\]

which gives the operator bound. The last inequality is Theorem 16. ∎

### Corollary 18 - Explicit adaptive depth

Fix a tolerance \(\varepsilon>0\) before materialization. If every selected tail has cell resistance at least \(R_*>0\), then choosing

\[
 \ell_i\ge
 \left\lceil\frac{2s}{\varepsilon R_*}\right\rceil
\tag{18.5}
\]

for every \(i\) gives

\[
 \|\Lambda_{\mathrm{phys}}-\Lambda_{\mathrm{node}}\|_{\mathrm{op}}
 \le\varepsilon.
\tag{18.6}
\]

More efficiently, one may choose individual lengths satisfying

\[
 \sum_i\frac{2}{\ell_iR_{*,i}}\le\varepsilon.
\tag{18.7}
\]

The depth may be arbitrarily large, but it is finite and is exact side data. No uniform lower bound on \(R_*\) is needed: a small root resistance is compensated by a longer univalent tail.

### Corollary 19 - Absolute error budget

Choose a universal plumbing budget \(E_{\mathrm{pl}}>0\) as part of the block specification. After the proof horizon is frozen, choose materialization depths by (18.7) with \(\varepsilon=E_{\mathrm{pl}}\). Then the entire end-plumbing response contributes at most the predetermined additive error \(E_{\mathrm{pl}}\), independently of:

- satellite period;
- raw address depth;
- the number of univalent prefix steps;
- the Euclidean diameters of the physical cylinders.

The number \(s\) is paid for by greater presentation depth, not by a worse error constant.

## 19. Future-equivalence aggregation

Suppose selected bubbles are partitioned into classes \(\mathcal C_1,\ldots,\mathcal C_k\) such that every future observable, port order, response matrix, and Value coefficient is constant on each class. If the quotient imposes identical terminal potentials on copies in one class, then parallel gluing gives the exact class response

\[
 \Lambda_{\mathcal C_j}^{\mathrm{tot}}
 =|\mathcal C_j|\,\Lambda_j.
\tag{19.1}
\]

After normalization by the class replication count, the response is \(\Lambda_j\). The plumbing perturbation remains bounded by (18.4).

This removes dependence on raw address count once a future-faithful finite class quotient is available. It does not prove that the number \(k\) is universally bounded; that remains the uniform-observability problem.

---

# Part VIII. Protected finite materialization

## 20. Finite representatives avoid inaccessible end impressions

A non-singleton end impression need not offer a source-authorized singleton planar port. The finite-horizon proof does not need to attach directly to that impression.

For every selected end address, choose the finite representative supplied by Theorem 7 at the materialization depth. Its carrier is a conformal pullback of the root carrier and has the transported root port and protected marking. Distinct selected words can be chosen pairwise incomparable and lie in pairwise disjoint gap cells.

### Theorem 20 - Protected finite physical carrier for an end diagram

Assume the root packet and port certificate satisfies the fixed-packet closure audit, and all transported obstacles and collars remain inside their authorized gap cells. Then every finite depth-graded end diagram has a sufficiently deep physical realization whose selected finite carriers admit one protected regulated global carrier with:

1. pairwise disjoint completed packets;
2. one explicit unprotected singleton port on every selected finite carrier;
3. preservation of all protected prime-end chains and cyclic order;
4. avoidance of every unselected finite pullback and every end support;
5. exact transport under all used shift and root branch maps;
6. exact compatibility with the serial neck cross-sections used in Theorem 17.

#### Proof

Choose pairwise incomparable representatives after the maximum common-prefix depth. Pull the root packets, free ports, collars, and obstacles into their gap cells. The direct-decoration gap-cell and finite protected-carrier theorems from Research Push I give disjoint fullifications, port survival, connected common free domain, and the protected connector. Theorem 7 supplies exact dynamical branches and marked squares. Because the serial neck cells lie in the authorized address sectors outside the local packets, they can be retained simultaneously. ∎

### Exact scope

The theorem closes the protected carrier problem for a **finite materialized direct-decoration end diagram** under the explicit root packet/port and serial-neck certificates. It does not prove the corresponding certificate for every unconstructed virtual-Molecule component, dam, fjord, or protected terminal-tree access.

---

# Part IX. Finite-horizon inflation and transition transfer

## 21. Direct-decoration finite-horizon inflation

### Theorem 21 - Quantitative finite-horizon inflation

Let \(\mathcal D\) be a finite depth-graded normalized end diagram with:

1. actual intrinsic pseudo-puzzle branches;
2. one declared quadratic relative stage and all remaining relative stages univalent;
3. complete critical-spine retention and relative-cover data;
4. a root protected packet/port certificate;
5. serially exhaustive address necks;
6. a predetermined response-error tolerance \(\varepsilon>0\).

Then \(\mathcal D\) has an actual finite physical realization satisfying:

- locally saturated pseudo-quadratic-like stages;
- a selected relative return of degree two;
- exact chronological critical word;
- exact component, sheet, access, obstacle, and endpoint data;
- a protected global finite carrier;
- exact fiberwise widths and response modules;
- total end-plumbing response error at most \(\varepsilon\);
- finite actual iterate horizon;
- naturality under every certified final-root enlargement.

#### Proof

Use Theorem 7 for finite physical branches, the critical-spine telescope and finite-horizon assembly from Research Push II for the selected degree-two return, Theorem 20 for the carrier, Theorems 12-13 for exact fiber modules, and Corollary 18 to choose tail depths making the plumbing perturbation at most \(\varepsilon\). Every chosen depth is finite, so the total iterate horizon is finite. Certified enlargement squares pull back under the same charts. ∎

### Consequence

This proves the direct-decoration instance of finite-horizon inflation. It does not prove the universal `H1_FINITE_HORIZON_INFLATION` node, which also covers arbitrary virtual-Molecule, neutral, and mixed source configurations.

## 22. Error-stable contraction transfer

Let \(Z\) be the normalized geometric/response/Value state of the root block, and let \(L\) be a nonnegative homogeneous gauge satisfying the manuscript's error-stability estimate

\[
 L(Z+\Delta)\le L(Z)+C_L\|\Delta\|
\tag{22.1}
\]

for response perturbations in the declared norm.

Assume a source-licensed root block has a strict forward estimate

\[
 L(Z_{\mathrm{out}})
 \le\mu L(Z_{\mathrm{in}})+E_{\mathrm{root}},
 \qquad 0<\mu<1.
\tag{22.2}
\]

### Theorem 22 - Strict root transition survives virtual end materialization

For any preassigned \(E_{\mathrm{pl}}>0\), choose finite materialization depths so that

\[
 \|\Delta_{\mathrm{pl}}\|
 \le E_{\mathrm{pl}}/C_L.
\]

Then the materialized virtual end block satisfies

\[
 L(Z^{\mathrm{vir}}_{\mathrm{out}})
 \le
 \mu L(Z^{\mathrm{vir}}_{\mathrm{in}})
 +E_{\mathrm{root}}+E_{\mathrm{pl}}.
\tag{22.3}
\]

Equivalently, at the preceding checkpoint,

\[
 L_{\mathrm{in}}
 \ge
 \mu^{-1}L_{\mathrm{out}}
 -\mu^{-1}(E_{\mathrm{root}}+E_{\mathrm{pl}}).
\tag{22.4}
\]

Thus the homogeneous backward factor \(\lambda=\mu^{-1}>1\) is unchanged by the virtual address tail.

#### Proof

The normalized univalent corridor is the identity by Corollary 15. The only additional state perturbation is the physical plumbing coupling. Theorem 17 and the chosen depths bound it by \(E_{\mathrm{pl}}/C_L\). Apply (22.1) to (22.2), then rearrange. ∎

### Corollary 23 - Identity cycles are harmless only when grouped

A cycle consisting only of virtual rescaling edges remains an identity cycle and cannot supply strict contraction. Once it is grouped with a root block satisfying (22.2), the complete block has the same strict homogeneous coefficient \(\mu\), with only the prescribed additive plumbing charge.

This closes the direct-decoration chart-interface issue. It does not prove that every mixed block has a source-licensed strict root alternative.

## 23. Planar-free finite-interface execution

Call a direct-decoration proof program **finite-interface** when, in every complete block:

1. every theorem call reads a finite depth-graded diagram and finitely many marked outputs;
2. every end-fiber operation is conformally natural in the normalized coordinate;
3. interaction between distinct end fibers is read only through a finite protected carrier, a finite-electrode response, and explicitly retained finite Value features;
4. all quantitative inequalities are stable under a preassigned additive response perturbation; and
5. the proof-use horizon and error budget are frozen before materialization depth is chosen.

### Theorem 24 - Pro-exact execution sufficiency

Let a finite-interface block be supplied with its actual root restrictions, critical-spine data, intrinsic finite atlases, packet/port certificates, and serially exhaustive address necks. Then, for every prescribed plumbing budget \(E_{\mathrm{pl}}>0\), the complete block has an actual finite physical execution on finite cylinders such that:

1. every dynamical arrow is an actual restriction of an iterate of the original polynomial;
2. every component, sheet, critical word, relative-cover, prime-end, obstacle, and localization record is exact;
3. one protected finite carrier realizes all proof-used atoms and accesses;
4. every normalized fiberwise response and retained Value feature is exact;
5. the total cross-fiber response perturbation is at most \(E_{\mathrm{pl}}\); and
6. every error-stable strict block inequality survives with that prescribed additive charge.

No point-valued landing map on \(E_\omega\), no nondegenerate planar continuum inside \(E_\omega\), and no identification of the direct-limit carrier with a planar infinite-address small Julia set is used.

#### Proof

Take the finite union of all diagrams and unfold every shift-grading conflict. Theorem 7 gives one exact finite-cylinder realization of every dynamical and marked square. Theorem 20 gives the protected finite carrier. Allocate the prescribed error budget among the finitely many selected address tails and use Corollary 18 to choose finite depths. Theorem 17 controls their total response perturbation. Exact fiber observables descend by Theorems 12-13, and Theorem 22 transfers every error-stable strict inequality. All selected depths are finite and are chosen only after the horizon and budget are fixed. ∎

### Corollary 25 - Planar identification is not a finite-interface prerequisite

Within the direct-decoration category, `PLANAR_VIRTUAL_COMPONENT_IDENTIFICATION` is not a logical prerequisite for a proof module satisfying the finite-interface contract. The unresolved source-facing task is instead to prove that every relevant mixed block supplies the root atlases, packet/port certificates, serial necks, and uniformly adequate finite observable interface required by Theorem 24.

This is a dependency deletion, not a claim that Dudko's proposed planar Cantor family has been constructed.

---

# Part X. Revised ledger effect

## 24. Defensible new proved subnodes

### `VIRTUAL_END_DIRECT_LIMIT`

Every infinite direct-decoration address has a canonical normalized direct-limit Riemann surface carrying the exact finite-word pseudo-quadratic-like portrait and marking.

### `DEPTH_GRADED_END_DIAGRAM_REALIZATION`

Every finite shift-consistent normalized end diagram has an exact finite-cylinder realization, with dynamical and presentation edges correctly typed.

### `INTRINSIC_FINITE_PSEUDOPUZZLE_ATLAS`

An externally marked connected quadratic-like map carries the finite source-authorized pseudo-puzzle atlas defined by its external class and actual pullbacks.

### `RECURSIVE_FIBERED_PORTRAIT_COMPILER`

Every finite source-supplied decorated quadratic-like chain has a recursive normalized realization and exact finite multi-scale materializations.

### `DIRECT_DECORATION_FIBER_RESPONSE_IDENTITY`

All fully transported finite fiberwise widths and responses are exactly invariant under address rescaling.

### `DIRECT_DECORATION_SERIAL_NECK`

Source ray/equipotential cells provide additive serial resistance along every certified address corridor.

### `ADAPTIVE_NODAL_RESPONSE_APPROXIMATION`

A finite end package can be materialized so its physical response is within any preassigned operator-norm tolerance of its nodal normalization, with the explicit depth formula (18.5)-(18.7).

### `DIRECT_DECORATION_PROTECTED_END_MATERIALIZATION`

Every finite end diagram satisfying the root packet/port certificate has a protected physical carrier at sufficiently deep finite prefixes.

### `DIRECT_DECORATION_FINITE_HORIZON_INFLATION`

Every finite direct-decoration end diagram satisfying the listed analytic certificates inflates to an actual degree-two finite-horizon pseudo-quadratic-like program with prescribed plumbing error.

### `DIRECT_DECORATION_STRICT_TRANSITION_TRANSFER`

Every source-licensed strict root contraction transfers through a materialized direct-decoration end with the same homogeneous coefficient and preassigned additive plumbing error.

### `PLANAR_FREE_FINITE_INTERFACE_EXECUTION`

Every direct-decoration block satisfying the finite-interface contract can be executed on actual finite cylinders with a protected carrier and arbitrarily prescribed plumbing error, without selecting a nondegenerate planar infinite-address component.

## 25. Correction to earlier promotion claims

Two distinctions prevent theorem laundering:

1. A normalized direct-limit fiber is not automatically an identification with Dudko's actual planar Cantor small-Julia component.
2. A recursive atlas is canonical only relative to its declared external marking and intrinsic finite source atlas; arbitrary hybrid-presentation uniqueness would be a rigidity assumption.

Therefore the original source-facing nodes should be **split**, not silently promoted:

- `VIRTUAL_DISCONNECTED_MARKING_TRANSFER`
  - `RESCALED_END_MARKING_TRANSFER`: proved here;
  - `PLANAR_VIRTUAL_COMPONENT_IDENTIFICATION`: open.
- `VIRTUAL_CANTOR_PACKAGE_REALIZATION`
  - `FIBERED_PROEXACT_CANTOR_PACKAGE`: proved here;
  - `ACTUAL_PLANAR_CANTOR_COMPONENT_FAMILY`: open;
  - `GLOBAL_PROTECTED_CARRIER_COUPLING`: open.
- `VIRTUAL_PREFIX_LOCAL_SCALE_SELECTOR`
  - `INTRINSIC_FINITE_ATLAS_COMPILER`: proved here;
  - `SOURCE_UNIVERSAL_VIRTUAL_SCALE_AUTHORIZATION`: open.

No unconditional reduction in the original MLC open count should be claimed until the manuscript formally accepts these splits and proves that the rescaled category is the required source object. In the split ledger, eleven substantial subnodes move from unspecified gaps to proved modules.

---

# Part XI. Mandatory attacks

## 25. Attacks passed

### A. Geometric parent versus shift

The geometric map \(t_m\) and the actual forward map \(f^q\) remain distinct before normalization.

### B. Inconsistent finite diagrams

Theorem 7 requires a shift grading. A merge with conflicting shift counts is unfolded rather than falsely materialized.

### C. Presentation edges mislabeled as dynamics

Only dynamical paths are claimed to be polynomial iterates. Geometric presentation changes remain explicit conformal maps.

### D. Wild end impression

No point of a non-singleton impression is selected. Finite physical carriers attach to finite representatives with actual singleton ports.

### E. Hybrid-rigidity circularity

The finite atlas is built intrinsically from the external class and actual pullbacks. Uniqueness of an arbitrary hybrid conjugacy is not assumed.

### F. Vanishing root neck

No universal lower bound on \(R_*\) is assumed. The materialization depth adapts to the actual positive resistance.

### G. Raw number of bubbles

The total error is kept fixed by allocating smaller conductance to each bubble. Raw count is paid in depth, not in the error constant.

### H. Chart-cycle neutrality

Identity tails are not claimed strict. Strictness is inherited only after grouping with an independently strict root block.

### I. Value observability

Response aggregation is asserted only on future-equivalence classes preserving all coefficient rows. A uniform class bound is not inferred.

## 26. Remaining attacks

The following remain open and are not hidden by the new category:

- identification of the normalized fiber with Dudko's intended actual planar small-Julia component family;
- universal source authorization of intrinsic virtual atlases at every mixed scale;
- protected analytic ports for all terminal-tree, dam, fjord, and attachment data;
- a universal finite future-observable quotient for simultaneous global WAD/Value interactions;
- exact KKL ideal-interval and relative-cover action on the complete coupled carrier;
- uniform virtual tame, Wave, and zero-entropy/shear realization;
- a strict root-block alternative for every mixed block;
- discounted error control for all non-plumbing chart and localization terms;
- geometric coercivity of bounded marked potential;
- mixed-tower phase-parameter rigidity and exclusion of invariant line fields.

---

# Part XII. The next irreducible theorem

## 27. Universal finite-interface authorization and global response quotient

Theorem 24 removes planar infinite-address identification from the critical path for every module satisfying its interface contract. The next source-facing theorem should therefore have two different clauses.

### Clause A - Universal source authorization

For every actual virtual-Molecule or mixed block, construct before the stopping execution:

1. the externally marked normalized root portraits and their intrinsic finite pseudo-puzzle atlases;
2. the finite decorated chain required by every admissible continuation;
3. actual critical-spine, relative-cover, packet/port, protected-access, obstacle, and serial-neck certificates;
4. a frozen finite-interface demand schema that is complete for Wave, Wanderers, covering, quasi-additivity, response, and width calls; and
5. exact enlargement morphisms preserving all of the preceding data.

This clause must be proved from source dynamics, independently of any downstream a priori bound, compactness, rigidity, or MLC conclusion.

### Clause B - Uniform global future quotient

For the complete finite proof horizon, quotient the coupled normalized fiber network by future observational equivalence and prove:

1. universally bounded terminal/core/WAD dimensions, or a source theorem giving an equivalent uniformly controlled response form;
2. exact descent of every branch, endpoint frame, WAD transport, and Value coefficient row;
3. compatibility with the protected global carrier, relative covers, and all presentation changes;
4. a complete positive-entropy, pseudo-Siegel, transient, or calibrated-shear root alternative; and
5. a discounted error budget including plumbing, localization, congestion, and chart-change terms.

Once Clause A is proved, Theorem 24 supplies the end rescaling, exact finite materialization, protected carrier, and arbitrarily small plumbing error without requiring a planar infinite-address component. Once Clause B is proved, the remaining route is MBTT, geometric coercivity, and mixed-tower rigidity.

### Independent source refinement - Planar component identification

It remains mathematically meaningful to identify the normalized fibers with Dudko's intended actual planar Cantor small-Julia family. Such a theorem would strengthen the geometric interpretation and may simplify source authorization, but it is not a logical prerequisite for the finite-interface route proved here. A failure certificate should still record the first address, claimed planar component, actual end support, prescribed return, and failed marking field.

---

# Conclusion

The infinite direct-decoration address is no longer an undefined analytic placeholder. It has an exact normalized direct-limit surface, every finite computation on that surface has a genuine finite-cylinder realization, and the source ray/equipotential geometry gives a quantitative serial neck. For a finite proof package, the entire physical-to-nodal response discrepancy can be forced below any predetermined additive budget by an explicit finite depth choice. Any strict source root transition then survives with the same homogeneous factor.

The remaining obstruction has become sharply source-facing:

\[
 \boxed{
 \text{authorize the finite normalized interface for every mixed block,}
 }
\]

and

\[
 \boxed{
 \text{compress its complete global future interaction without losing Value or access data.}
 }
\]

Planar identification of the infinite-address components remains an open geometric refinement, but Theorem 24 shows that it is not required for a finite-interface execution. Universal source authorization, uniform future compression, MBTT, coercivity, and rigidity remain open.
