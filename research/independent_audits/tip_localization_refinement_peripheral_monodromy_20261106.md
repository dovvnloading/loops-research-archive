# Actual 9-to-3 localization transport on the common exterior

**Audit date: 2026-11-06. Target: Issue #29, objective 4; Paper 1's canonical localization subgroup interface.** This note proves an interscale comparison of the actual target localization covers after an explicit restriction to their common exterior. The map is holomorphic, natural for every finite path, and has countably infinite sheet fibers. It also proves that the exterior inclusion in the opposite direction has no lift between the two canonical target covers, and that the restricted comparison cannot extend continuously to its entire uniformizing prime-end circle. The separate [first-child audit](tip_kl_terminal_first_child_20261106.md) identifies both terminal modified nests with \(\chi=1\). The remaining objective-4 obligation is compatibility with the selected KL prime-end sides and filled or protected pieces; those incidences are not established here. The 465-entry ledger, H1–H4, UPTCR, and MLC are unchanged.

## 1. Source data, exact geometry, and the restriction being made

The localization construction used here is Jeremy Kahn, *A priori bounds for some infinitely renormalizable quadratics. I. Bounded primitive combinatorics*, [arXiv:math/0609045v3](https://arxiv.org/pdf/math/0609045v3), **§7.4.1, definitions on printed p. 43 and Theorem 7.12 with its proof on p. 44; §§7.4.2–7.4.3, pp. 45–46**. Its definitions are recorded in [Paper 1's source-locked definitions](../../papers/paper1_canonical_localization/extracted/F_kahn_source/definitions.tex). In particular, a marked-pair morphism \(g:(S,A)\to(T,B)\) must satisfy \(A=g^{-1}(B)\); localization functoriality is not asserted for an arbitrary comparison of filled sets.

The covering-space argument is an application of [canonical sheet resolution, §§2–5](../mlc_unified/kl_localization_sheet_resolution_factorization.md), especially the pullback-component subgroup \(a_*^{-1}(H_t)\). The present contribution supplies its actual two-scale planar input. It does not attribute this particular restriction or its component selection to Kahn or to Kahn–Lyubich. For the still-separate puzzle and marking requirements, the primary source is Kahn–Lyubich, *A priori bounds … II. Decorations*, [arXiv:math/0609046v2](https://arxiv.org/pdf/math/0609046v2), **§§2.1–2.2, printed pp. 5–8**, also available as [IMS 2006/6](https://www.math.stonybrook.edu/preprints/ims06-06.pdf).

Work at the exact nonattracting parameter \(c_{\rm tip}\) of [the two-scale complex certificate](nonattracting_tip_complex_two_scale_20261106.md), with \(f(z)=z^2+c_{\rm tip}\). That certificate proves, using its exact rational margins and the stated classical analytic inputs, proper degree-two restrictions \(f^p:V_p\to U_p\), \(p=3,9\), connected full filled sets \(K_p\), pairwise disjoint phase domains, and \(K_9\subset K_3\). Write

\[
C_r=f^r(K_3)\quad(0\le r<3),\qquad
D_{r,k}=f^{r+3k}(K_9)\quad(0\le r,k<3).
\]

The nine \(D_{r,k}\) are pairwise disjoint, the three \(C_r\) are pairwise disjoint, and

\[
D_{r,k}\subset C_r.                                      \tag{1.1}
\]

Indeed, \(f^3(K_3)=K_3\), so this last containment also follows directly from \(K_9\subset K_3\). Fix the common ordinary outer Jordan disk \(U^0\) containing these sets, as in [the previous target-complement audit, §4](tip_kl_top_puzzle_and_localization_complement_20261106.md), and put

\[
B_3=\bigcup_r C_r,\quad B_9=\bigcup_{r,k}D_{r,k},\qquad
\Omega_3=U^0\setminus B_3,\quad
\Omega_9=U^0\setminus B_9.
\]

The actual base map is

\[
i:\Omega_3\hookrightarrow\Omega_9.                       \tag{1.2}
\]

The reverse identity is undefined on the whole of \(\Omega_9\), as already certified in the preceding audit. We instead restrict the period-nine cover along (1.2). No \(f^6\) map, external-angle collapse, or identification of the two whole exteriors is used.

### Fullness of every phase continuum

Here the free-group calculation uses full phase continua, not only their disjointness. This follows from the certified polynomial-like restrictions. For \(p\in\{3,9\}\), set \(E_j=f^j(V_p)\), \(0\le j\le p\), so \(E_p=U_p\). Every factor \(f:E_j\to E_{j+1}\) is proper: given a compact set \(L\subset E_{j+1}\), lift points of \(E_j\cap f^{-1}(L)\) to \(V_p\); their \(f^p\)-images belong to the compact set \(f^{p-j-1}(L)\subset U_p\), and properness of \(f^p:V_p\to U_p\) supplies compactness upstairs and hence in \(E_j\).

The degrees of these proper factors multiply to two. The first factor has local degree two at 0, so it has degree two and every later factor has degree one. Thus \(f^{p-j}:E_j\to U_p\) is conformal for \(1\le j<p\). It carries \(f^j(K_p)\) bijectively onto \(K_p\), since \(f^p(K_p)=K_p\). Fullness of \(K_p\) transfers to relative fullness of \(f^j(K_p)\) in the disk \(E_j\). As \(f^j(K_p)\Subset E_j\), relative fullness in this planar disk implies fullness in the plane: any bounded complementary component would have closure inside \(E_j\), contradicting relative fullness. This proves the required fullness of all \(C_r,D_{r,k}\). No local connectivity of their boundaries is needed.

## 2. The actual inclusion on fundamental groups

Choose a basepoint \(x\in\Omega_3\). Choose pairwise disjoint closed Jordan neighborhoods \(N_r\Subset U^0\setminus\{x\}\) of \(C_r\), and inside each \(\operatorname{int}N_r\) choose pairwise disjoint Jordan neighborhoods \(M_{r,k}\) of its three \(D_{r,k}\). Fullness and disjointness allow these choices with the continua in their interiors. Use a compatible system of access arcs from \(x\), first to the coarse neighborhoods and then to the fine ones inside them.

A disk minus finitely many pairwise disjoint full continua has the homotopy type of a disk with that many holes. To see this without imposing boundary regularity, replace each continuum by a Jordan neighborhood; the region between it and that neighborhood is a topological annulus and contributes precisely its peripheral generator. Van Kampen, or cutting the resulting finite surface along the chosen access arcs, gives

\[
G:=\pi_1(\Omega_3,x)=F(a_0,a_1,a_2),\qquad
\pi_1(\Omega_9,x)=F_0*F_1*F_2,
\]
\[
F_r=F(b_{r,0},b_{r,1},b_{r,2}).
\]

Here \(a_r\) is a positive meridian around \(C_r\) and \(b_{r,k}\) a positive meridian around \(D_{r,k}\), with their chosen access arcs. Numbering the inner meridians in the corresponding planar boundary order gives

\[
i_*(a_r)=A_r=b_{r,0}b_{r,1}b_{r,2}.                    \tag{2.1}
\]

If a different cyclic order is chosen, permute the three factors; the proof below is unchanged. Compatible access arcs are what make (2.1) a simultaneous based formula. Independently of these choices, the winding vector of \(i_*(g)\) is constant on each triple

\[
\{D_{r,0},D_{r,1},D_{r,2}\}.                            \tag{2.2}
\]

**Lemma 2.1 (injectivity).** The map \(i_*:G\to F_0*F_1*F_2\) is injective.

**Proof.** Write a nontrivial reduced coarse word as alternating nonzero powers of the \(a_r\), with adjacent block indices different. Each nonzero power of \(A_r\) is a nontrivial element of the free factor \(F_r\). Its image is therefore a reduced nonempty word in the free product \(F_0*F_1*F_2\), and cannot be the identity. This proves injectivity for all words, not just for homology classes. ∎

## 3. The restricted fine cover is universal

Let

\[
p_3:\widehat\Omega_3\to\Omega_3,\qquad
p_9:\widehat\Omega_9\to\Omega_9
\]

be the exterior restrictions of Kahn's target localizations at \(K_3=C_0\) and \(K_9=D_{0,0}\). With access-compatible based lifts, their subgroups are

\[
H_3=\langle a_0\rangle\le G,\qquad
H_9=\langle b_{0,0}\rangle\le\pi_1(\Omega_9,x).           \tag{3.1}
\]

These are the images of the annular local neighborhoods in the source definition. Changing the lift or its access conjugates the relevant subgroup.

**Theorem 3.1 (actual pullback subgroup).** For every conjugate of \(H_9\),

\[
i_*^{-1}(h^{-1}H_9h)=\{1\}.                            \tag{3.2}
\]

Consequently every connected component \(R\subset p_9^{-1}(\Omega_3)\), with the restricted projection \(p_R:R\to\Omega_3\), is a universal cover of \(\Omega_3\).

**Proof.** If \(i_*(g)=h^{-1}b_{0,0}^{\,n}h\), abelianization gives winding \(n\) around \(D_{0,0}\) and zero around \(D_{0,1}\). Property (2.2) forces \(n=0\). Thus \(i_*(g)=1\), and Lemma 2.1 gives \(g=1\). A component of the pullback of \(p_9\) along \(i\) has subgroup \(i_*^{-1}(h^{-1}H_9h)\). Since \(i\) is an inclusion, that component identifies with a component \(R\subset p_9^{-1}(\Omega_3)\). Its subgroup is trivial by (3.2), so it is universal. ∎

The use of the free-product proof is essential: equal winding vectors alone would not prove injectivity of \(i_*\), because commutators have zero winding.

## 4. A based holomorphic 9-to-3 comparison and its infinite fiber

Fix such a component \(R\), a point \(u_9\in R\) over \(x\), and the access-compatible point \(u_3\in\widehat\Omega_3\) over \(x\). Since

\[
L:=(p_R)_*\pi_1(R,u_9)=\{1\}\ \le\ H_3,                \tag{4.1}
\]

the covering lifting criterion gives a unique based map

\[
q:(R,u_9)\longrightarrow(\widehat\Omega_3,u_3),\qquad
p_3q=p_R.                                               \tag{4.2}
\]

This is an actual comparison from a **restricted component of the period-nine localization** to the period-three localization. The maps \(R\hookrightarrow\widehat\Omega_9\) and \(i:\Omega_3\hookrightarrow\Omega_9\) give its relation to the unrestricted period-nine cover. The base map in (4.2) is \(\operatorname{id}_{\Omega_3}\); in the archive's subgroup notation it is exactly \(H_s=L=1\le K=H_t=H_3\).

The map \(q\) is a surjective covering. Surjectivity follows by projecting a path from \(u_3\) to any point of the connected \(\widehat\Omega_3\), lifting it from \(u_9\), and using uniqueness of path lifting. Local covering charts show both the covering property and holomorphicity: in such a chart \(q\) is a branch of \(p_3^{-1}\circ p_R\). Moreover \(R\) is simply connected, so \(q\) is the universal cover of \(\widehat\Omega_3\); its deck group is \(H_3\cong\mathbb Z\). Every fiber is therefore countably infinite.

For a concrete collision, let \(\gamma_3\) be the access-based positive meridian of \(K_3\), representing \(a_0\). Its lift to \(\widehat\Omega_3\) starting at \(u_3\) is closed. Its lift to \(R\) starting at \(u_9\) is not closed. If \(u_{9,n}\) is the endpoint of the lift of \(\gamma_3^n\), then

\[
u_{9,n}\ne u_{9,m}\quad(n\ne m),\qquad
q(u_{9,n})=u_3\quad(n\in\mathbb Z).                     \tag{4.3}
\]

The winding witness is a specific point of the certified dynamical configuration:

\[
w=x_3=f^3(0)\in D_{0,1}=f^3(K_9)\subset K_3,
\qquad w\notin K_9.                                    \tag{4.4}
\]

Here \(0\in K_9\) and phase separation proves the exclusion. The physical meridian \(\gamma_3\) has winding one at \(w\); every element of every conjugate of \(H_9\) has winding zero there. Thus no nonzero power of this meridian fixes any period-nine sheet over \(x\). Equation (4.3) is an infinite collision between actual sheets of the restricted covers, independent of the earlier exterior-ray collision.

The comparison is unique after its stated component and basepoint choices. No unbased or puzzle-marked canonical choice of \(R,u_9,u_3\) is claimed.

## 5. Full path transport, with the coset convention fixed

Use the archive's endpoint convention: a cover with subgroup \(H\le G\) has fiber \(H\backslash G\), and continuing the endpoint \(Hg\) by a based loop \(v\) sends it to \(Hgv\). Its project notation \(G/H=\{gH\}\) is related by \(Hg\mapsto g^{-1}H\); no group structure on a nonnormal coset set is implied.

With this convention the based-fiber map of (4.2) is exactly

\[
\{1\}\backslash G\longrightarrow H_3\backslash G,
\qquad g\longmapsto H_3g,                               \tag{5.1}
\]

and it commutes with the complete right monodromy action:

\[
q_x(gv)=H_3gv=q_x(g)\cdot v.                            \tag{5.2}
\]

For the fiber of \(q\) over \(u_3\), this is \(L\backslash H_3\cong\mathbb Z\), or \(H_3/L\) after the archive's inversion identification. This fiber keeps all powers in (4.3).

The assertion extends beyond based loops. For every path \(\delta:y\to z\) in \(\Omega_3\), let \(M_R(\delta)\) and \(M_3(\delta)\) denote the endpoint transport bijections on the fibers of \(p_R,p_3\). Uniqueness of path lifting gives

\[
q_z\circ M_R(\delta)=M_3(\delta)\circ q_y.                \tag{5.3}
\]

These transports depend only on endpoint-fixed homotopy classes and respect identity paths, inverses, and concatenation. Thus \(q\) defines a natural transformation of the full fiber functors on \(\Pi_1(\Omega_3)\), and a functor between their categories of elements. No finite-word truncation, bounded winding approximation, or finite sheet quotient is used.

The conclusion is **noninjectivity on sheet objects over a fixed basepoint**. It is not categorical nonfaithfulness: a covering map induces an injective map on each fixed-endpoint set of path homotopy classes. In particular, the functor just constructed is faithful on Hom sets even though it identifies the infinitely many objects in (4.3).

## 6. The opposite canonical-cover lift is obstructed

Although \(i:\Omega_3\to\Omega_9\) is an actual holomorphic inclusion, there is no map

\[
\widehat i:\widehat\Omega_3\longrightarrow\widehat\Omega_9,
\qquad p_9\widehat i=i\,p_3.                            \tag{6.1}
\]

Indeed, the lifting criterion would require \(i_*(H_3)\le h^{-1}H_9h\) for some choice of the fine basepoint. But \(i_*(a_0)=A_0\) has winding one at \(w\in D_{0,1}\), whereas that entire conjugate subgroup has winding zero there. This defeats every basepoint choice. Equivalently, a path-natural map from the coarse fiber functor into the restricted fine fiber functor would have to send the \(\gamma_3\)-fixed coarse sheet to a \(\gamma_3\)-fixed fine sheet, and no such fine sheet exists.

This is a precise obstruction to the lift of the **specified inclusion**. It does not prohibit every holomorphic comparison with some other base map. Conversely, (4.2) is not a lift of a reverse map on the unrestricted exteriors: it exists because the period-nine cover was first restricted to \(\Omega_3\).

## 7. A continuous extension to the whole prime-end circle is impossible

**Theorem 7.1 (deck-limit obstruction).** Let \(\overline R^{\rm pe}\) be the conformal ideal-circle compactification of \(R\), also called its uniformizing prime-end closed disk. This is not the compactification by ordinary topological ends. For every Hausdorff space \(Y\) containing \(\widehat\Omega_3\) by an injective topological embedding, the map \(q:R\to\widehat\Omega_3\subset Y\) fails to extend continuously to at least one point of \(\partial\overline R^{\rm pe}\). In particular, it has no continuous extension to the entire prime-end circle into a Hausdorff compactification of the coarse localized exterior \(\widehat\Omega_3\).

**Proof.** The simply connected Riemann surface \(R\) is conformally the unit disk. Indeed, uniformization applies, and its nonconstant bounded holomorphic projection into the bounded domain \(\Omega_3\) excludes the plane by Liouville's theorem; compactness excludes the sphere. Choose a uniformization \(\phi:\mathbb D\to R\). Its extension defines the uniformizing prime-end closed disk; this construction is independent of the choice of \(\phi\), since disk automorphisms extend to the circle. It also agrees with the Carathéodory prime-end completion in a planar realization: \(R\) is a simply connected domain in the annular exterior of the fine local pair.

By §4, \(q\) is a universal cover with nontrivial cyclic deck group. Let \(\tau\ne\operatorname{id}\) be a generator, and put \(T=\phi^{-1}\tau\phi\in\operatorname{Aut}(\mathbb D)\). A nonidentity deck transformation has no interior fixed point. The elementary classification of disk automorphisms therefore makes \(T\) hyperbolic or parabolic, and its positive iterates converge to the same boundary fixed point \(\zeta_+\in\partial\mathbb D\) for every starting point in \(\mathbb D\). This also follows directly by conjugating to a positive dilation or a nonzero translation of the upper half-plane. If \(T\) is hyperbolic, the negative iterates similarly converge to its other boundary fixed point.

Choose \(u,v\in R\) with \(q(u)\ne q(v)\), possible because \(q\) is onto the nontrivial surface \(\widehat\Omega_3\). Both sequences \(\tau^n(u)\) and \(\tau^n(v)\) converge to the prime end corresponding to \(\zeta_+\), but their images are the distinct constant sequences

\[
q(\tau^n(u))=q(u),\qquad q(\tau^n(v))=q(v).
\]

Continuity at that prime end would force these two distinct embedded interior points to equal its image in \(Y\), contradicting the uniqueness of limits in a Hausdorff space. ∎

This is a failure of full prime-end extension for the **actual restricted comparison** (4.2), not merely a failure of a symbolic label map. It does not identify the deck-limit prime end with any selected KL \(O,\xi,\eta\) side or rule out comparison on a protected ideal interval that avoids the deck-limit points. Establishing those incidences remains a separate obligation.

## 8. The first unproved marked-pair obligation

At the filled level, set

\[
T_3=\Omega_3\cup K_3,\qquad T_9=\Omega_9\cup K_9.
\]

The identity inclusion \(T_3\to T_9\) is undefined at \(w=x_3\): this point belongs to \(K_3\subset T_3\), while \(w\in D_{0,1}\) is removed from \(T_9\). Thus the exterior inclusion (1.2) does not supply a morphism of these marked pairs to which Kahn's localization functoriality could automatically apply. The construction of \(q\) instead uses restriction and covering classification directly on the exteriors.

To turn (4.2) into the selected KL marked transition, one still has to specify the appropriate filled or prime-end completion of the restricted component, construct its relation to the [now identified terminal first-child pieces](tip_kl_terminal_first_child_20261106.md), identify the source \(O,\xi,\eta\) sides and their based access paths, and prove that the chosen comparison carries each such marking to the required coarse marking. Equation (5.3) then controls the transport of any paths that have actually been assigned, but it does not itself assign their prime ends or side labels. Nor does path naturality on compact parameter intervals imply properness or end control at an ideal boundary.

Accordingly, the earlier statement that *no actual interscale sheet comparison has been constructed* can now be narrowed: a based comparison with infinite sheet fibers is proved on the explicitly restricted common exterior, and its extension to the whole prime-end circle is obstructed. A comparison compatible with the selected filled or protected prime-end pieces remains unconstructed. The argument neither identifies Levin angle fibers with these sheets nor closes any global rigidity or MLC obligation.

## 9. Verification and attribution

The only dynamical numerical dependencies are the already certified phase separation, degree-two restrictions, nonescape of 0, and nesting in the [complex-domain audit](nonattracting_tip_complex_two_scale_20261106.md). Its existing reproduction commands are

```sh
lake build TipComplexMargins
python research/independent_audits/verify_tip_complex_domains.py --check-manifest
```

The new results above are proofs for all reduced free words and all homotopy classes of paths. They are not finite enumerations, and no new finite checker is presented as a substitute for them. Neither the phase-fullness argument nor the covering/groupoid proof is formalized in Lean here. Their dependencies are the cited certified geometry, elementary planar topology and van Kampen, and the covering results proved in the archive's sheet-resolution note.

**Attribution and review:** Kahn supplies the localization construction; Kahn–Lyubich supply the distinct puzzle framework; the earlier archive audits supply the exact dynamical domains. OpenAI GPT-6 assistance was used for the present proof search, source-interface comparison, and exposition. No independent human specialist review has been performed or is claimed.
