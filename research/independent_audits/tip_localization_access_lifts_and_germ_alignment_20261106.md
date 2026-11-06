# Boundary access lifts and finite germ alignment for the actual localization comparison

**Date: 2026-11-06. Target: Issue #29, objective 4.** The [common-exterior theorem](tip_localization_refinement_peripheral_monodromy_20261106.md) constructs a based holomorphic comparison \(q:R\to\widehat\Omega_3\) from a restricted component of the period-nine localization to the period-three localization. This note proves its exact boundary-extension domain, the complete integer-valued lifts of physical coarse accesses, and compatibility of the canonical localized return with any fixed finite puzzle construction sufficiently close to its filled Julia set.

The comparison extends over two open prime-end intervals and fails at their two common endpoints. It is a universal covering of an annulus, not a KL map between two universal-cover tiles. Lifting it to a target universal tile gives a biholomorphism; consequently its infinite annular fibers alone do not prove a collision between the selected KL tile-side markings. The subsequent [native canonical comparison](tip_iterated_direct_canonical_localization_embedding_20261106.md) now supplies a different, correctly typed fine-to-coarse projection, an actual native KL source immersion, and a failure at its named outer/Julia-side joints. This note explains the boundary behavior of the earlier annular comparison and why that additional source identification was necessary. No ledger, H1–H4, UPTCR, or MLC status is changed.

## 1. Exact objects and source conventions

Retain the actual parameter and physical filled sets \(K_9\subset K_3\) of the [complex certificate](nonattracting_tip_complex_two_scale_20261106.md). Put

\[
B_3=\bigcup_{j=0}^{2}f^j(K_3),\qquad
B_9=\bigcup_{j=0}^{8}f^j(K_9),\qquad
\Omega_p=U^0\setminus B_p.
\]

Here \(U^0\) is the common bounded outer Jordan disk. Kahn's period-three target localization is a local marked disk

\[
(\widehat T_3,\widehat K_3)\longrightarrow
(T_3,K_3),\qquad T_3=\Omega_3\cup K_3.
\]

Write \(S=\widehat T_3\setminus\widehat K_3=\widehat\Omega_3\), with exterior projection \(p_3:S\to\Omega_3\). The preceding note proves that every component \(R\) of the period-nine exterior cover restricted to \(\Omega_3\) is simply connected. Its based comparison satisfies

\[
q:R\longrightarrow S,\qquad p_3q=p_R,\qquad
\operatorname{Deck}(q)\cong\mathbb Z.                    \tag{1.1}
\]

The source references used here are:

- Jeremy Kahn, [*A priori bounds … I*, arXiv:math/0609045v3](https://arxiv.org/pdf/math/0609045v3): marked-pair, local-pair, and local-cover definitions, **printed p. 43**; **Theorem 7.12, printed p. 44**, including the construction by gluing a genuine neighborhood of the compact root; dynamical localization in §7.4.2.
- Kahn–Lyubich, [*A priori bounds … II. Decorations*, IMS 2006/6](https://www.math.stonybrook.edu/preprints/ims06-06.pdf): ordinary puzzle construction, **§§2.1–2.2, printed pp. 5–8**; pseudo-piece and tile construction, **§3.2, pp. 11–12**; branch/inclusion maps, **Lemma 3.4, pp. 12–13**; the ideal-boundary tiling, **§3.2.4, p. 13**.
- The archive's [source-locked localization theorem and proof](../../papers/paper1_canonical_localization/extracted/F_kahn_source/thm_03.tex), [dynamical localization](../../papers/paper1_canonical_localization/extracted/F_kahn_source/thm_04.tex), and [ideal-boundary source audit](../mlc_unified/direct_decoration_outer_port_footprint.md), §§2.1–2.2 and 9.

The symbols have different roles which must remain distinct. KL's \(O\)-boundary is the union of the \(\lambda_i\) sides of its glued pseudo-piece tiles. Its \(J\)-boundary is tiled by \(\xi_i,\eta_i\); the boundary associated with a vertex is

\[
\partial^{v_i}\mathbf Y=\eta_i\cup\xi_{i+1}.
\]

These labels belong to specified **glued pseudo-pieces and their individual tiles**. They are not automatic labels for the two boundary circles of \(S\). The two infinite-wrapping endpoints of a tile's \(\lambda_i\) are actual points of that tile's conformal ideal circle. Kahn's ideal closure of a non-simply-connected hyperbolic surface instead uses the quotient of the closed universal disk with the deck-group limit set removed. For an annulus, the two removed deck-limit points are therefore distinct from the retained boundary circles of the quotient.

## 2. The coarse localized exterior has finite positive modulus

**Theorem 2.1.** There is a conformal isomorphism

\[
\psi:S\longrightarrow A(r,1)=\{r<|z|<1\},
\qquad 0<r<1.                                          \tag{2.1}
\]

It may be chosen to associate the boundary adjacent to \(\widehat K_3\) with \(|z|=r\).

**Proof.** The localization is a local marked disk, so its connected exterior \(S\) is an annulus. By the conformal classification of annuli, it is a finite-modulus round annulus, a punctured disk, or a punctured plane. The projection \(p_3\) is a nonconstant bounded holomorphic function because its image lies in the bounded disk \(U^0\). A punctured-plane coordinate would extend this bounded function across both 0 and infinity, making it constant; this case is impossible.

Suppose instead that \(S\) were a punctured disk, and express \(p_3\) in that coordinate. Its boundedness gives a removable singularity at the puncture, with limiting value \(a\in\mathbb C\). Choose \(w\in K_3\) with \(w\ne a\), possible because \(K_3\) is nondegenerate. On sufficiently small circles about the puncture, \(p_3-w\) extends without zeros over the bounded disk, so its winding is zero. But those circles generate \(\pi_1(S)\), whose image under \(p_3\) is the peripheral subgroup around \(K_3\). Their images have winding \(+1\) or \(-1\) around every \(w\in K_3\), a contradiction. Thus both conformal boundary components are nondegenerate and \(0<r<1\). Interchanging the two ends if necessary gives the stated assignment. ∎

No numerical lower bound for \(\operatorname{mod}(S)\) is claimed. The proof uses nondegeneracy of \(K_3\) and the actual peripheral subgroup, rather than an assumed smooth Julia boundary.

## 3. The exact ideal-boundary extension and its two exceptional endpoints

Let \(a=\log r<0\), and let

\[
\mathcal S_a=\{w\in\mathbb C:a<\operatorname{Re}w<0\}.
\]

Since \(R\) is simply connected, \(\psi q\) has a holomorphic logarithm. After choosing its value at the basepoint, universal-cover uniqueness makes this logarithm a conformal isomorphism

\[
\ell:R\longrightarrow\mathcal S_a,\qquad
\psi q=\exp\circ\ell.                                   \tag{3.1}
\]

A positive generator \(\tau\) of \(\operatorname{Deck}(q)\) satisfies

\[
\ell(\tau u)=\ell(u)+2\pi i.                             \tag{3.2}
\]

The ideal circle of \(R\) consists of the two open intervals corresponding to

\[
I_K:\ \operatorname{Re}w=a,\qquad
I_{\mathrm{ext}}:\ \operatorname{Re}w=0,
\]

together with two endpoints \(\zeta_+,\zeta_-\) corresponding to \(\operatorname{Im}w\to+\infty,-\infty\). These are the two distinct fixed prime ends of the hyperbolic deck generator. In particular, the parabolic alternative left open in the preceding general deck-limit argument does not occur here.

**Theorem 3.1 (maximal boundary extension).** The comparison has a unique continuous extension

\[
q^{\rm pe}:
\overline R^{\,\rm pe}\setminus\{\zeta_+,\zeta_-\}
\longrightarrow\overline S^{\,\rm pe},                  \tag{3.3}
\]

which is a covering of surfaces with boundary. In (3.1) it is exactly

\[
\{a\le\operatorname{Re}w\le0\}
\longrightarrow\{r\le|z|\le1\},\qquad w\longmapsto e^w.   \tag{3.4}
\]

Each of its two boundary restrictions is a universal covering of a circle, with all fibers equal to \(\mathbb Z\)-torsors. It has no continuous extension at either \(\zeta_+\) or \(\zeta_-\) into any Hausdorff space containing \(S\) by an injective topological embedding.

**Proof.** Formula (3.4) defines the extension and its covering charts, including half-disk charts at the boundary. The ideal identifications come from the conformal uniformizations, so no physical-boundary local connectivity is being assumed. Density of the interior proves uniqueness.

For either endpoint choose \(u,v\in R\) with \(q(u)\ne q(v)\). The sequences \(\tau^n u,\tau^n v\) approach \(\zeta_+\) as \(n\to+\infty\), and \(\zeta_-\) as \(n\to-\infty\). Their images remain the distinct constant points \(q(u),q(v)\). Continuity at either endpoint would violate uniqueness of limits in a Hausdorff space. This proves both the stated failure and maximality among extensions to additional ideal points with such a target. ∎

The open-interval extension and the whole-circle obstruction are complementary assertions. In particular, an arbitrary compact subinterval of \(I_K\) or \(I_{\mathrm{ext}}\) presents no boundary-continuity obstruction. A subinterval on which the imaginary coordinate changes by less than \(2\pi\) maps injectively; larger intervals can contain deck-related boundary points.

## 4. A physical collar and the complete lifts of its accesses

Choose a Jordan local neighborhood \(D\Subset T_3\) of \(K_3\), and put \(C=D\setminus K_3\). Kahn's construction supplies a distinguished holomorphic section

\[
\sigma:D\longrightarrow\widehat T_3,\qquad
\pi_3\sigma=\operatorname{id}_D.
\]

Its restriction identifies \(C\) with an annular collar \(\widehat C\subset S\) adjacent to \(\widehat K_3\). The inclusion \(\widehat C\hookrightarrow S\) induces an isomorphism on fundamental groups. Consequently

\[
\widetilde C=q^{-1}(\widehat C)
\]

is **connected** and \(q:\widetilde C\to\widehat C\) is universal. It is the component of \(p_R^{-1}(C)\) containing a chosen \(u_9\) over \(x\in C\) when the based coarse point is chosen as \(\sigma(x)\). Other components of \(p_R^{-1}(C)\) must not be silently identified with this distinguished one.

The inner prime-end circle of \(C\) identifies through \(\sigma\) with the inner prime-end circle of \(S\). Let \(\epsilon\) be any physical access represented by a curve in \(C\) converging to a definite inner prime end. For each choice of initial lift over its starting point, its lift in \(\widetilde C\) converges to a unique point of \(I_K\), and all such endpoint lifts are

\[
\{\tau^n\widetilde\epsilon:n\in\mathbb Z\},\qquad
q^{\rm pe}(\tau^n\widetilde\epsilon)=\sigma^{\rm pe}(\epsilon).
                                                               \tag{4.1}
\]

To verify convergence, use a sufficiently small proper arc of the target boundary circle about \(\epsilon\). A curve converging to \(\epsilon\) is eventually contained in its annular sector. Each lift of that sector is a finite-width boundary chart on \(I_K\), so the selected lifted curve has a finite, unique boundary coordinate. Its endpoints cannot be one of the two infinite-wrapping points.

This applies to the actual \(G=f^3\) puzzle accesses established in the [internal-puzzle ray audit](tip_internal_puzzle_ambient_lifts_20261106.md), including the two \(G\)-internal dividing accesses \(1/3,2/3\), whose ambient labels are \(7/9,2/9\), respectively. The corresponding ray portions sufficiently near \(K_3\) lie in \(C\). Equation (4.1) gives actual prime-end lifts of these accesses.

The angular labels here refer to the chosen external marking of the polynomial-like germ. They are not asserted to equal the arguments of the global annulus coordinate \(\psi\). The marking identifies the relevant boundary points by an orientation-preserving boundary homeomorphism. Choosing one real lift of that homeomorphism, or one based access lift, assigns an integer origin; without that additional choice (4.1) is a torsor, not a distinguished enumeration. There is no choice of one lift invariant under the nontrivial deck action.

The physical coarse access alone also does not select an \(O,\xi,\eta\) incidence in an independently specified fine pseudo-piece. Such an incidence requires the actual tile, its gluing seam, and the chosen based identification.

## 5. Why the annular collision is not automatically a KL tile collision

Let \(t:\widetilde S\to S\) be any based universal cover used as an annular tile. Since \(q:R\to S\) is itself universal, there is a unique based lift

\[
\widetilde q:R\longrightarrow\widetilde S,\qquad
t\widetilde q=q.                                       \tag{5.1}
\]

**Proposition 5.1.** The map \(\widetilde q\) is a biholomorphism. It extends homeomorphically to the entire conformal ideal circles of these two disks, including the two wrapping endpoints.

**Proof.** Universal-cover uniqueness gives a based inverse over \(S\). Both maps are holomorphic in covering charts. Uniformizing the two disks turns \(\widetilde q\) into a disk automorphism, which extends to a circle homeomorphism. ∎

Thus the distinct points identified by \(q\) are distinct once the target universal tile retains their winding coordinates. The same holds for the boundary lifts in (4.1). The obstruction at \(\zeta_\pm\) concerns projection to the annulus; it does not obstruct (5.1).

KL's \(\lambda_i,\xi_i,\eta_i\) further depend on a specified physical external component, a lift of its finite gluing interval, and the attachment to the central puzzle piece. After such identifications, the universal annulus tile is a valid source object. But \(q\) alone does not supply a map between two such marked tiles, and (5.1) shows why its infinite annular fiber cannot simply be relabeled as noninjectivity of a tile-to-tile map. A marked collision would have to survive those additional identifications.

## 6. The localized return agrees with the physical germ on all finite puzzle data

Let \((\widehat i_3,\widehat F_3)\) be the canonical dynamical localization of the physical return \(f^3\) at \(K_3\), with source and target projections \(\pi_s,\pi_t\). Their source construction gives actual neighborhoods of their compact marked sets on which both projections are biholomorphic. Naturality yields

\[
\pi_t\widehat i_3=\pi_s,\qquad
\pi_t\widehat F_3=f^3\pi_s.
\]

After restricting these neighborhoods, \(\widehat i_3\) is embedded and the ordinary return

\[
\widehat G=\widehat F_3\circ\widehat i_3^{-1}
\]

satisfies

\[
\pi_t\widehat G=G\pi_t,\qquad G=f^3,                     \tag{6.1}
\]

on a neighborhood of \(\widehat K_3\). This is a biholomorphic identification of germs, obtained from the gluing construction and commuting maps, not an assumption of injectivity on the whole localized source.

**Theorem 6.1 (finite puzzle alignment).** Fix a finite combinatorial construction of physical \(G\)-puzzle pieces and their branches, ray portions truncated at the chosen initial equipotential, and equipotential arcs, with maximal used iterate \(N<\infty\). The initial equipotential can be chosen sufficiently close to \(K_3\) that this finite configuration and its used forward images lie in the germ neighborhood of (6.1). Access paths selected inside these small puzzle pieces then lie there as well. The resulting data transport biholomorphically to the canonical localized germ, preserving their actual branch maps, cyclic orders, and selected accesses.

**Proof.** Let \(W\) be a physical neighborhood of \(K_3\) on which (6.1) and all needed local coordinates are defined. Since \(G(K_3)=K_3\), the finite intersection

\[
W_N=\bigcap_{j=0}^{N}G^{-j}(W)
\]

is an open neighborhood of \(K_3\). The chosen straightening/external marking supplies small Jordan equipotential neighborhoods \(U_h\) with

\[
K_3\Subset U_h,\qquad
\bigcap_{h>0}\overline U_h=K_3,
\]

and with the usual local height relation under \(G\). For sufficiently small \(h>0\), \(\overline U_h\subset W_N\). Every piece and boundary portion of the finite puzzle based at that height lies in \(\overline U_h\), and every used forward image lies in \(W\). Applying the inverse germ projection transports the full finite configuration and (6.1) transports its branch identities. A biholomorphism preserves the oriented local access and boundary order. ∎

In particular, the two \(P_G,Q_{G,L},Q_{G,R}\) branches and the [terminal \(Y_G^3,Y_G^6\) first child](tip_kl_terminal_first_child_20261106.md) can be placed in the common physical/localized germ. Shrinking the initial equipotential leaves the ray-defined Julia sectors and the already established return/stopping times unchanged. No explicit numerical height is asserted. The theorem concerns a small-height representative; it does not move already prescribed global access paths into the germ neighborhood or identify additional winding carried by such paths.

There is also an exact tile statement **for the restricted representative**. If both constructions use the restricted ordinary map on these same small neighborhoods, each ambient annulus and each finite gluing component is carried biholomorphically by (6.1). Its based universal cover lifts this biholomorphism, and the lifts glue with the central copies. The two resulting restricted pseudo-piece constructions therefore have matching \(\lambda,\xi,\eta\) labels after the stated based choices.

This does not identify the entire pseudo-pieces of the **original larger canonical \(\psi\)-map**. Their tiles may be universal covers of annuli extending outside the common germ neighborhood. Replacing those annuli by the small restricted ones changes the ambient representative. The germ argument supplies no common-coordinate identity for the full original tile maps and no control on their additional ideal sides. This is the same distinction emphasized in the archive's [outer-port source audit](../mlc_unified/direct_decoration_outer_port_footprint.md), §§3–4: local agreement does not establish its global common-coordinate hypothesis.

The [subsequent native proof](tip_iterated_direct_canonical_localization_embedding_20261106.md), §§6–8, avoids assuming such a global coordinate identity. It retains the full canonical carriers, uses the iterated marked preimage identity to check their ranges, and uses the degree-one annular winding to separate the actual fine sheets. Its source is a native coarse-stage pseudo-piece immersed in the fine canonical surface, not an asserted identification with a fine-native pseudo-piece.

## 7. Results and their use in the native comparison

The source-locked comparison has finite-modulus annular target, a hyperbolic cyclic deck group, two exceptional prime ends, and an exact continuous covering extension everywhere else. Every actual physical coarse access has its complete integer-valued family of lifts. The canonical localized return admits a faithful biholomorphic realization of all fixed finite physical puzzle data sufficiently near \(K_3\), and of pseudo-pieces constructed from the same restricted representative.

Theorems 3.1 and 6.1 provide ingredients for a source-marked comparison; Proposition 5.1 prevents using the earlier annular sheet collision as a substitute for that construction. The [native comparison's Theorems 7.1 and 8.1](tip_iterated_direct_canonical_localization_embedding_20261106.md) now construct an actual native coarse-stage KL source immersion into the fine canonical surface and prove its infinite fine-to-coarse sheet fiber and failure at the specified \(\lambda/\eta\) and \(\lambda/\xi\) joints. That is the explicit-failure alternative, not a positive theorem preserving every protected marking. A separately specified positive transition between complete fine-native and coarse-native pseudo-pieces would still require its own construction.

**Trust and attribution.** The new statements are written proofs using the already certified dynamical input, elementary covering theory, conformal classification of annuli, removable singularities, and the cited Kahn/KL constructions. No finite enumeration is offered as a proof of these uniformization or all-path assertions; no new Lean formalization is claimed. OpenAI GPT-6 assistance was used for proof search, source comparison, and exposition. No independent human specialist review is represented.
