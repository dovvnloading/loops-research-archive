# Iterated and direct canonical localizations, with a source-named interscale failure

**Date: 2026-11-06. Target: Issue #29, objective 4, source-defined comparison or first explicit sheet/side failure.**

This note constructs the comparison supplied by Kahn's **smaller-root** localization at the actual nested period-three and period-nine filled Julia sets. The iterated canonical target, obtained by localizing at \(K_9\) inside the canonical period-three target, embeds holomorphically into the direct period-nine target. Its localization projection is a genuine fine-to-coarse-ambient map, with \(K_9\) marked on both sides.

A native KL pseudo-piece for the actual canonical coarse \(\psi\)-map, with its geometric separator chosen in the physical \(G=f^3\) germ, lifts into this iterated fine surface. On every one of its universal-cover tiles, integer deck translates give distinct canonical fine sheets with the same coarse image. The resulting fine-to-coarse composite fails to extend continuously at the **source-named** \(\lambda_i/\eta_i\) and \(\lambda_i/\xi_i\) infinitely wrapping joints. The proof identifies those joints on the whole glued native KL pseudo-piece, rather than assigning side labels to an arbitrary annular boundary.

The comparison and failure are stated with their exact domains and root markings. They are not an equality of direct and iterated canonical renormalizations, an assertion that a full-root morphism \(K_9\to K_3\) exists, or an identification with KL Lemma 3.4's within-stage inclusion. The 465-entry ledger, H1–H4, UPTCR, and MLC are unchanged.

## 1. Actual geometry and the primary source map

At the exact nonattracting tip, write

\[
C_r=f^r(K_3),\qquad
D_{r,k}=f^{r+3k}(K_9),\qquad 0\le r,k<3.
\]

The [complex certificate](nonattracting_tip_complex_two_scale_20261106.md) and [phase-fullness argument](tip_localization_refinement_peripheral_monodromy_20261106.md) give pairwise disjoint full continua, with \(D_{r,k}\subset C_r\). Put

\[
B_3=\bigcup_rC_r,\qquad B_9=\bigcup_{r,k}D_{r,k},
\qquad \Omega_p=U^0\setminus B_p,
\]
\[
T_3=\Omega_3\cup K_3,\qquad T_9=\Omega_9\cup K_9,
\]

for the same bounded outer Jordan disk \(U^0\). Let

\[
\pi_3:(\mathcal V_3,\mathcal K_3)\longrightarrow(T_3,K_3),
\qquad
\pi_9:(\mathcal V_9,\mathcal K^{\rm dir}_9)
             \longrightarrow(T_9,K_9)
\]

be Kahn's canonical target localizations. These are local covers of marked pairs; in particular, \(\pi_3^{-1}(K_3)=\mathcal K_3\) and \(\pi_3\) bijects these compact sets. There is a genuine neighborhood of \(\mathcal K_3\) on which \(\pi_3\) is biholomorphic.

The primary source is Jeremy Kahn, [*A priori bounds … I*, arXiv:math/0609045v3](https://arxiv.org/pdf/math/0609045v3): the marked/local-cover definitions are on **printed p. 43**, localization and its naturality are **Theorem 7.12, p. 44**, canonical renormalization is **§7.4.3, p. 45**, and the nested-period comparison is **Theorem 7.13(2), pp. 45–46**.

More specifically, the proof of Theorem 7.13(2) on **p. 46** uses the coarse local cover to map the coarse renormalized surface minus its next small cycle into the direct fine exterior. It proves this by separating points outside and inside the coarse filled set, then applies Schwarz contraction to obtain a length inequality. The marked restriction below is precisely that source map, with the next central root restored. The subsequent embedding and sheet/side results are additional deductions proved here.

Define the three lifted inner phases

\[
\mathcal D_k=(\pi_3|_{\mathcal K_3})^{-1}(D_{0,k}),\qquad
\mathcal B_{\rm in}=\bigcup_{k=0}^{2}\mathcal D_k,
\qquad \mathcal A=\mathcal D_0.
\]

Let

\[
\Omega_{\rm it}=\mathcal V_3\setminus\mathcal B_{\rm in},
\qquad
T_{\rm it}=\Omega_{\rm it}\cup\mathcal A
          =\mathcal V_3\setminus(\mathcal D_1\cup\mathcal D_2).
\]

These are the exterior and marked target used for the next period-three renormalization of the coarse degree-two germ \(G=f^3\).

## 2. The correctly typed marked morphism and its localization

**Proposition 2.1.** The restriction

\[
m=\pi_3|_{T_{\rm it}}:
(T_{\rm it},\mathcal A)\longrightarrow(T_9,K_9)          \tag{2.1}
\]

is a holomorphic marked-pair immersion.

**Proof.** Outside \(\mathcal K_3\), the coarse projection takes values in \(\Omega_3\subset\Omega_9\), so it meets none of \(B_9\). Inside \(\mathcal K_3\), its bijection onto \(K_3\) has

\[
B_9\cap K_3=D_{0,0}\cup D_{0,1}\cup D_{0,2}.
\]

Thus \(\pi_3^{-1}(B_9)=\mathcal B_{\rm in}\), and deleting \(\mathcal D_1,\mathcal D_2\) gives the claimed range. Moreover \(m^{-1}(K_9)=\mathcal A\), exactly the source's marked-morphism condition. The local-cover projection \(\pi_3\) is locally biholomorphic, including on its glued root neighborhood, so \(m\) is an immersion. ∎

Localize (2.1). Write

\[
\rho:(\mathcal V_{3,3},\mathcal K^{\rm it}_9)
          \longrightarrow(T_{\rm it},\mathcal A)
\]

for the iterated canonical target. Theorem 7.12 gives a unique commuting holomorphic immersion

\[
J:(\mathcal V_{3,3},\mathcal K^{\rm it}_9)
       \longrightarrow(\mathcal V_9,\mathcal K^{\rm dir}_9),
\qquad
\pi_9J=m\rho=\pi_3\rho.                                 \tag{2.2}
\]

The root map is the prescribed bijection induced by \(\pi_3\), so \(J\) is canonical up to the unique isomorphisms of the localization construction. There is no arbitrary choice of an exterior component in its definition. Basepoints below only express its covering data.

Both marked roots in (2.1) represent \(K_9\). The [full-root obstruction](tip_interval_root_and_marked_morphism_obstruction_20261106.md) for a morphism from an interval root \(K_9\) onto the branched root \(K_3\) therefore does not apply.

## 3. Compatible based groups and complete fiber transport

Choose a physical Jordan neighborhood \(N\) of \(K_3\) whose closure lies in the genuine coarse germ neighborhood and avoids \(C_1,C_2\). Choose \(x\in N\setminus K_3\), and lift it through the distinguished local section of \(\pi_3\). The three inner meridians can all be drawn in

\[
N\setminus(D_{0,0}\cup D_{0,1}\cup D_{0,2}).
\]

Use their images under the section as based meridians of \(\Omega_{\rm it}\). Extend the same physical access system to the remaining six fine phase continua. This gives simultaneous identifications

\[
\Gamma:=\pi_1(\Omega_9,x)=F_0*F_1*F_2,\qquad
F_r=F(b_{r,0},b_{r,1},b_{r,2}),
\]
\[
\pi_1(\Omega_{\rm it})=F_0,\qquad
m_*:F_0\hookrightarrow\Gamma
\quad\hbox{is the literal free-factor inclusion}.        \tag{3.1}
\]

The first equality for the iterated exterior follows because \(\mathcal V_3\) is a disk with three full compact deletions. Its fundamental group can be generated entirely in the lifted copy of \(N\).

With based lifts chosen from the same neighborhood of \(K_9\), the two fine localization subgroups are

\[
H=\langle b_{0,0}\rangle\le F_0,\qquad
H=\langle b_{0,0}\rangle\le\Gamma.
\]

Consequently

\[
H_s=H=m_*^{-1}(H_t).                                    \tag{3.2}
\]

The source fine exterior is therefore the distinguished connected component of the pullback of the direct fine exterior cover along \(m\). Its based-fiber map is the injection

\[
H\backslash F_0\longrightarrow H\backslash\Gamma,\qquad
Hg\longmapsto Hg.                                       \tag{3.3}
\]

Here the notation is the archive's endpoint convention: continuing by a loop \(v\) sends \(Hg\) to \(Hgv\). Project notation \(F_0/H\) or \(\Gamma/H\) is related by inversion, not by an assumed group structure on a nonnormal quotient.

For every path \(\delta:y\to z\) in \(\Omega_{\rm it}\), uniqueness of lifting gives

\[
J_z\,M_{\rm it}(\delta)
  =M_9(m\circ\delta)\,J_y.                               \tag{3.4}
\]

This is a natural transformation of the complete fiber functors on \(\Pi_1(\Omega_{\rm it})\), with the direct functor pulled back along \(m\). It supplies the induced category-of-elements functor for all objects and all path classes, including arbitrary integer winding. No finite sheet quotient is used.

Equation (3.2) alone does not imply that \(J\) is injective: the base immersion \(m\) is not an embedding. The next argument addresses its different physical fibers explicitly.

## 4. The canonical comparison is a strict open embedding

Put

\[
\beta_r=b_{r,0}b_{r,1}b_{r,2},\qquad
\Gamma_c=\langle\beta_0,\beta_1,\beta_2\rangle,\qquad
C=\langle\beta_0\rangle .
\]

These are the compatible peripheral words of the three coarse phase continua. The [common-exterior proof](tip_localization_refinement_peripheral_monodromy_20261106.md) gives the injective map \(\pi_1(\Omega_3)\to\Gamma\) with image \(\Gamma_c\), and

\[
\Gamma_c\cap g^{-1}Hg=\{1\}\quad(g\in\Gamma).
                                                               \tag{4.1}
\]

Free-product normal form also gives

\[
F_0\cap\Gamma_c=C.                                      \tag{4.2}
\]

Indeed, a reduced word in nonzero powers of the \(\beta_r\) can lie in the free factor \(F_0\) only if every syllable has index 0.

**Theorem 4.1.** The map \(J\) in (2.2) is a holomorphic embedding with strict open image.

**Proof, outside the coarse root.** Let

\[
S_3=\mathcal V_3\setminus\mathcal K_3.
\]

The coarse projection \(S_3\to\Omega_3\) is a covering, and the inclusion \(S_3\hookrightarrow\Omega_{\rm it}\) maps its fundamental group to \(C=\langle\beta_0\rangle\). Since a power of \(\beta_0\) has equal winding about all three inner continua, while every conjugate of \(H\) has zero winding about \(\mathcal D_1\), the pullback of the iterated fine cover to \(S_3\) has trivial subgroup on each component. Its components are indexed by

\[
H\backslash F_0/C.
\]

Each is universal over \(S_3\), and its composite projection to \(\Omega_3\) is also universal. On the direct side, (4.1) says that the components over \(\Omega_3\), indexed by

\[
H\backslash\Gamma/\Gamma_c,
\]

are universal over \(\Omega_3\). The map \(J\) sends their indices by

\[
HfC\longmapsto Hf\Gamma_c.                              \tag{4.3}
\]

This index map is injective. If \(f,g\in F_0\) have the same image, write \(g=h f a\) with \(h\in H\), \(a\in\Gamma_c\). Then \(a=f^{-1}h^{-1}g\in F_0\cap\Gamma_c=C\), so their source double cosets coincide. On each component, \(J\) is a biholomorphism by uniqueness of universal covers over \(\Omega_3\). Hence it is injective on all points projecting physically outside \(K_3\).

**Inside the coarse root but outside the fine root.** For a physical point \(y\in K_3\setminus B_9\), the coarse local cover has exactly one preimage, because it bijects \(\mathcal K_3\) with \(K_3\) and no exterior point maps into \(K_3\). Thus any possible collision under \(J\) lies in a single fiber of \(\rho\), where injectivity is exactly (3.3), with basepoints transported along the same path. Points of \(D_{0,1},D_{0,2}\) have been removed, so no additional stratum remains.

**On the fine root.** The map \(J\) bijects \(\mathcal K^{\rm it}_9\) with \(\mathcal K^{\rm dir}_9\). Its marked-morphism property prevents an exterior point from mapping into the target root. Together the three cases prove global injectivity. An injective holomorphic immersion is a biholomorphism onto its open image.

**Strictness.** The preceding audit certifies

\[
z_*=\frac{31}{1024}\in K_3\setminus B_9.
\]

Over this point the coarse projection has its single root preimage. After compatible change of basepoint inside \(N\setminus B_9\), the image of its fine fiber is exactly \(H\backslash F_0\) inside \(H\backslash\Gamma\). The direct fine sheet \(Hb_{1,0}\) is not in that image, since \(F_0\) is a free factor and \(H\subset F_0\). Thus \(J\) is not surjective. ∎

This is a proof of a **strict open embedding**, not a claim that it is a proper map. Kahn §7.4.4, p. 46, describes a different postcritical-set renormalization for which iterated and direct renormalization agree exactly. That alternative construction must not be substituted for the ordinary canonical construction here.

## 5. The actual restricted fine-to-coarse map

Let \(\mathcal U=J(\mathcal V_{3,3})\subsetneq\mathcal V_9\). The embedding defines a source-native fine-to-coarse-ambient comparison

\[
\mathcal L=\rho\circ J^{-1}:
(\mathcal U,\mathcal K^{\rm dir}_9)
\longrightarrow(T_{\rm it},\mathcal A)
\subset\mathcal V_3.                                   \tag{5.1}
\]

It is a local cover of the **same smaller root** \(K_9\). Its exterior is the connected cover of \(\Omega_{\rm it}\) with subgroup \(H\le F_0\). Consequently its fiber is the full countably infinite set \(H\backslash F_0\), with its path transport. For example, distinct powers of \(b_{0,1}\) give distinct fine sheets with one coarse image.

Explicitly, view this exterior map as a morphism from the fine cover to the identity cover of the coarse base \(\Omega_{\rm it}\). Then the complete subgroup datum is

\[
a=\operatorname{id}_{\Omega_{\rm it}},\qquad
H_s=\langle b_{0,0}\rangle=H
\ \le\
K=a_*^{-1}(H_t)=F_0,\qquad H_t=F_0.                    \tag{5.2}
\]

Its endpoint fiber is \(H\backslash F_0\), or \(F_0/H\) under the archive's inversion convention. This is the noninjective fine-to-coarse leg; it is distinct from the equality (3.2) controlling the injective direct/iterated comparison \(J\).

The restriction \(\mathcal U\) is defined by the canonical morphism (2.1) and its localized embedding, not by the undefined reverse identity \(\Omega_9\to\Omega_3\). Nor is (5.1) the physical map \(f^6\). The direct and iterated objects are both fine-level localizations; \(J\) compares them, while \(\rho\), or equivalently \(\mathcal L\), goes from the fine level into the coarse ambient surface.

## 6. A native KL pseudo-piece for the canonical coarse map

Let \(\mathbf G=(i,g):\mathcal V_3^1\to\mathcal V_3\) be the **actual canonical period-three \(\psi\)-quadratic-like map**. Its embedded polynomial-like germ agrees with physical \(G=f^3\). Let \(\mathcal V_3^m\), \(\mathcal K_3^m\), and \(i^m:\mathcal V_3^m\to\mathcal V_3\) denote its source-defined pullback tower and inclusion immersions. The iterated marked identities give

\[
(i^m)^{-1}(\mathcal K_3)=\mathcal K_3^m,
\qquad
i^m:\mathcal K_3^m\longrightarrow\mathcal K_3
\ \hbox{a bijection}.                                  \tag{6.1}
\]

They are Kahn's tower identities, not an assumption that \(i^m\) is globally injective. See Kahn I **§7.3.2, pp. 42–43**, and the archive's [source-locked pullback proposition](../../papers/paper1_canonical_localization/extracted/F_kahn_source/thm_02.tex).

Choose the geometric separator \(P_G=Y_G^1\) in the embedded ordinary restriction of this actual coarse map. The [finite germ-alignment theorem](tip_localization_access_lifts_and_germ_alignment_20261106.md), §6, allows its entire finite graph to lie in the common physical/localized germ. This retains its actual Julia sectors, first-return data, and the three inner root continua.

Now form the **native** source pseudo-piece

\[
\mathbf P=\Psi_{\mathbf G}(P_G)
\]

using the full canonical carriers of \(\mathbf G\), as in KL II **§3.2.1, pp. 11–12**. Its tiles are universal covers of

\[
A_m=\mathcal V_3^m\setminus\mathcal K_3^m,\qquad m=1.
\]

They are not replaced by universal covers of the smaller ordinary carrier. The geometric central copy is identified with its lift to \(\mathcal V_3^m\). Let \(\pi_{\mathbf P}:\mathbf P\to\mathcal V_3^m\) be the native path/tile projection and set

\[
\Pi=i^m\circ\pi_{\mathbf P}:
\mathbf P\longrightarrow\mathcal V_3.                   \tag{6.2}
\]

The central source root is the copy

\[
\mathcal A^m=(i^m)^{-1}(\mathcal A)
          \subset\mathcal K_3^m
\]

inside \(P_G\), corresponding under the embedded germ to physical \(K_9\). The [side atlas's phase-avoidance proof](tip_kl_pseudopiece_side_atlas_20261106.md), §4, says that the geometric \(P_G\) avoids the other two inner phase sets. On a native tile, (6.1) says that \(i^m\) sends every point of \(A_m\) outside \(\mathcal K_3\), hence outside all three inner roots. Thus the full native object has

\[
\Pi(\mathbf P)\subset T_{\rm it},\qquad
\Pi^{-1}(\mathcal A)=\mathcal A^m.                       \tag{6.3}
\]

This is a global range and inverse-marked-set check for the native carriers. It does not extrapolate a physical collar coordinate over them.

The native KL gluing gives a simply connected surface. It is hyperbolic: the composition \(\pi_3\Pi\) is a bounded nonconstant holomorphic map into \(U^0\), so uniformization and Liouville's theorem exclude the plane. Thus \(\mathbf P\) is a conformal disk with the conformal ideal circle used by the source. The pair \((\mathbf P,\mathcal A^m)\) is local because \(\mathcal A^m\) is a full compact continuum in its central interior. The map \(\Pi\) is a holomorphic marked-pair immersion. Kahn Theorem 7.12, with the source pair already local, therefore gives the unique holomorphic immersion

\[
e:(\mathbf P,\mathcal A^m)\longrightarrow
(\mathcal V_{3,3},\mathcal K^{\rm it}_9),
\qquad \rho e=\Pi.                                    \tag{6.4}
\]

It agrees with the prescribed root map near \(\mathcal A^m\). Put \(e_{\rm dir}=Je\). The actual native-source diagram has

\[
e_{\rm dir}:\mathbf P\longrightarrow\mathcal U
        \subset\mathcal V_9,\qquad
\mathcal L e_{\rm dir}=\rho e=\Pi.                     \tag{6.5}
\]

This is an immersion of a native KL pseudo-piece for the canonical coarse map into the actual fine canonical surface, followed by the correctly typed canonical fine-to-coarse projection.

The path compatibility is complete. For every path \(\delta\) in \(\mathbf P\setminus\mathcal A^m\), the path \(e\circ\delta\) is the unique \(\rho\)-lift of \(\Pi\circ\delta\) from its prescribed initial sheet. In the endpoint convention of §3,

\[
M_{\rm it}(\Pi\circ\delta)(e(\delta(0)))=e(\delta(1)).
                                                               \tag{6.6}
\]

Composing with \(J\) and using (3.4) gives the identical path-class statement in the direct fine cover. These identities respect all endpoint-fixed homotopies, inverses, and concatenations. The integer orbits below are explicit objects in this full sheet/path system, not a replacement for it.

## 7. A source-defined infinite fine-sheet collision on each native tile

Let \(\widehat A_i\subset\mathbf P\) be either of its two native universal-cover tiles, and let \(t_i\) be its positive deck generator. The core of \(A_m\) maps under \(i^m\) with degree **\(+1\)** to the core of \(\mathcal V_3\setminus\mathcal K_3\). Indeed, \(i^m\) is biholomorphic on a neighborhood of the compact root by (6.1) and the immersion property; a sufficiently small positive peripheral loop is therefore mapped to a positive peripheral loop. This computes the induced annular degree without asserting a global embedding. The map used here is the inclusion immersion \(i^m\), not the degree-\(2^m\) dynamical map \(g^m\).

The annulus \(A_m\) has finite positive modulus. To check this premise, compose its inclusion immersion with \(\pi_3\), obtaining a nonconstant bounded holomorphic map to \(\Omega_3\) that has winding \(+1\) around every point of physical \(K_3\). If \(A_m\) were a punctured disk, removability would give one limiting value at the puncture, while the nonzero winding around two distinct points of \(K_3\) makes that impossible. A punctured plane is excluded by bounded removability at both ends. This is the argument of the [access-lifts note, Theorem 2.1](tip_localization_access_lifts_and_germ_alignment_20261106.md), now applied to \(\pi_3i^m\). Hence its universal tile is a finite-width conformal strip, with two distinct hyperbolic deck endpoints.

In \(\Omega_{\rm it}\), the mapped positive core has winding vector

\[
\bigl(\operatorname{wind}_{\mathcal D_0},
      \operatorname{wind}_{\mathcal D_1},
      \operatorname{wind}_{\mathcal D_2}\bigr)=(1,1,1).
\]

Let \(\nu_i\) denote its based class after the chosen tile access. No nonzero power of \(\nu_i\) belongs to any conjugate of \(H=\langle b_{0,0}\rangle\): it has nonzero winding around \(\mathcal D_1\), whereas every element of every such conjugate has winding zero there. This conclusion needs no chosen ordering of three literal meridian factors.

Equivalently, for the homomorphism \((\nu_i)_*:\mathbb Z\to F_0\) induced by the native carrier annulus,

\[
(\nu_i)_*^{-1}(g^{-1}Hg)=\{0\}
\qquad(g\in F_0).
\]

Thus every component of its pulled-back fine cover is universal, with all integer sheet transport retained.

**Theorem 7.1 (actual native-tile fine-sheet fiber).** For every \(z\in\widehat A_i\), the points

\[
e_{\rm dir}(t_i^n z),\qquad n\in\mathbb Z,
\]

are pairwise distinct actual points of the direct period-nine canonical surface, and

\[
\mathcal L\bigl(e_{\rm dir}(t_i^n z)\bigr)
=\Pi(z)
\quad(n\in\mathbb Z).                                  \tag{7.1}
\]

**Proof.** For integers \(r,s\), a tile path between \(t_i^r z\) and \(t_i^s z\) projects to the \((s-r)\)-th power of the annular core. Its image under the fixed-depth inclusion \(i^m\), with \(m=1\), represents the corresponding conjugate of \(\nu_i^{\,s-r}\) in \(\Omega_{\rm it}\). If \(e(t_i^s z)=e(t_i^r z)\), its fine-cover lift would close, placing that word in the relevant conjugate of \(H\). The winding calculation excludes this unless \(s=r\). The embedding \(J\) preserves distinctness in the direct fine target. Finally, the native tile projection is deck invariant, so (6.5) gives their common coarse image. ∎

This proves separation **within each deck orbit**. It does not assert that \(e\) embeds the entire native tile: the base immersion \(i^m\) can identify points having different carrier projections. The trivial pullback subgroup makes the tile isomorphic to a component of the pullback cover, but projection of that pullback to the fine surface need not be injective when the base map is an immersion.

The collision in (7.1) is an infinite **sheet/object fiber**, not categorical nonfaithfulness on fixed-endpoint path homotopy classes. It is not the earlier exterior-ray \(f^6\) collision. Its points are actual canonical fine sheets, and its parametrizing tile is the specified native KL source object with its retained integer coordinate.

## 8. The first failure occurs at native KL outer/Julia-side joints

The finite geometric accesses of \(P_G\) give the two seam intervals of the [side atlas](tip_kl_pseudopiece_side_atlas_20261106.md). Under the embedded root collar they determine the corresponding ordered endpoints on the native inner prime-end circle. Their rational angle labels are **topological access markings**; they need not be numerical angular coordinates in a conformal uniformization of the full native annulus.

For each native tile, its \(O\)-side is \(\lambda_i\), and its two remaining inner sides are \(\xi_i,\eta_i\). With the atlas's positive orientation, the **source-defined infinitely wrapping joints** are

\[
\omega_i^-=\lambda_i\cap\xi_i,\qquad
\omega_i^+=\lambda_i\cap\eta_i.                         \tag{8.1}
\]

These are precisely the incidences of KL II **§3.2.4, printed p. 13**, applied to the native pseudo-piece. They are not the finite vertex incidence \(\eta_i\cap\xi_{i+1}\), which belongs to adjacent tiles.

For every fixed interior point \(z\) of the tile,

\[
t_i^n z\longrightarrow\omega_i^+
\quad(n\to+\infty),\qquad
t_i^n z\longrightarrow\omega_i^-
\quad(n\to-\infty),                                    \tag{8.2}
\]

in the ideal closure of the **whole glued native pseudo-piece** \(\mathbf P\). The gluing component is confined between two finite lifted accesses, and its finite geometric equipotential lies inside the full carrier. Sufficiently far positive or negative strip tails therefore meet no central gluing seam or other tile. Their successive transverse crosscuts give the two infinitely wrapping prime ends. This is also the source's explicit characterization of the joints in (8.1); it does not require a numerical conformal coordinate for the transported physical angles.

**Theorem 8.1 (native named-side extension failure).** The actual source-defined composite

\[
\mathcal L e_{\rm dir}=\rho e=\Pi:
\mathbf P\longrightarrow\mathcal V_3
\]

has no continuous extension at either \(\omega_i^-\) or \(\omega_i^+\) into any Hausdorff compactification containing \(\mathcal V_3\) by an injective topological embedding.

**Proof.** Choose \(z,w\in\widehat A_i\) with \(\Pi(z)\ne\Pi(w)\). Such points exist because the tile projection is a covering and \(i^m\) is a nonconstant holomorphic immersion. For \(n\to+\infty\), both \(t_i^n z,t_i^n w\) converge to the actual native joint \(\omega_i^+\), while

\[
\Pi(t_i^n z)=\Pi(z),\qquad
\Pi(t_i^n w)=\Pi(w).
\]

These are distinct constant interior values of the coarse surface. A continuous extension at \(\omega_i^+\) would force them to have the same limit, impossible in a Hausdorff space. Negative iterates give the identical contradiction at \(\omega_i^-\). ∎

This identifies an explicit failure at the native source's named \(O/J\) joints, in addition to the actual fine-sheet collision (7.1). It does not assume that \(e\) or \(e_{\rm dir}\) already extends those joints to separately identified prime ends of the canonical fine disk. Rather, it proves that a compatible boundary extension of the entire stated comparison from this marked native KL source cannot exist there.

## 9. Scope, dependency boundary, and attribution

The construction proves all of the following with the stated domains: the source-defined nested marked morphism, its canonical localized comparison \(J\), a strict open embedding into the direct fine target, complete based fiber/path naturality, a genuine fine-to-coarse local cover on that image, a native canonical-stage KL pseudo-piece immersion into it, and an infinite sheet fiber together with failure at its named wrapping joints.

Three distinctions remain essential:

1. **Same smaller root.** The canonical map marks \(K_9\) on both sides. It does not contradict the obstruction to a holomorphic morphism between the full roots \(K_9\) and \(K_3\).
2. **Target surfaces versus dynamical pairs.** The proof constructs target localizations and their source-native projections. It does not assert a global isomorphism of direct and iterated renormalized return/source legs. Germ compatibility is inherited, but a stronger global dynamical-intertwining statement would require its own diagram.
3. **This projection versus KL's inclusion map.** Theorem 8.1 concerns \(\rho e\), or its direct-fine realization \(\mathcal L e_{\rm dir}\). It is not the within-stage inclusion of KL Lemma 3.4, whose ideal extension is a different source assertion. Nor does it rule out a separately specified protected transition restricted away from these joints or retaining additional unwrapped data.

The former arbitrary-common-exterior boundary obstruction has thus been upgraded at this interface: the failure is now witnessed by actual canonical fine sheets in an explicitly identified native KL tile, and its endpoint occurs at actual \(\lambda_i/\xi_i/\eta_i\) incidences. No all-purpose impossibility claim for other maps is made.

**Verification and attribution.** Finite phase, root, and puzzle facts are the cited existing exact certificates and the deterministic side atlas. The new free-product, double-coset, localization, and all-integer wrapping results are written proofs; no finite search is substituted for their quantifiers, and no new Lean formalization is claimed. Kahn supplies the localization and nested source map; Kahn–Lyubich supply the tile and boundary definitions. OpenAI GPT-6 assistance was used for proof search, independent AI cross-checks, source comparison, and exposition. No independent human specialist review is represented.
