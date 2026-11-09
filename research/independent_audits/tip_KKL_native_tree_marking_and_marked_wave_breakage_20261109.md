# Native KKL tree markings, surviving marked breakage, and an exact sharp width calculation

**2026-11-09. Research draft for Issues #62 and #40.** This note advances from the ordinary KL W-to-V duplicated-tile example of draft PR #67 to the **actual Hubbard-tree-complement marking construction of Kahn–Kapiamba–Lyubich (KKL), Sections 2.5 and 6.1 and Appendix A**. The ambient representative is the archive's certified physical degree-two quadratic-like map

\[
G=f_{c_*}^3:V_3\longrightarrow U_3=D(0,1/4),
\]

with the identity inclusion \(\iota:V_3\hookrightarrow U_3\). This is an ordinary quadratic-like member of KKL's pseudo-quadratic-like category. It is **not** identified with the unrestricted canonical localization or with \(\Psi_G(W)\to\Psi_G(V^0)\). We compute the genuine inner pullback marking, verify refinement and end-properness, and construct marked paths and a marked wave whose two restrictions both survive KKL's filters. The same target relative-endpoint homotopy class also has a representative with only one restriction.

This is **not a counterexample to KKL**: their construction is set-valued and explicitly accommodates breakable paths. The refuted stronger assertion is that a marked target arc class alone determines the number of surviving restrictions of every representative. We also exhibit a sharp equality case for the harmonic-series width estimate, rather than inferring strict gain just from multiplicity. No global H1–H4, UPTCR, MLC, large-rotation wave-amplification, or ledger status is changed.

## 1. Exact physical inputs and the native Hubbard tree

Write \(f(z)=z^2+c_*\), \(x_k=f^k(0)\). The previously certified algebraic parameter lies between

\[
\frac{-607918036626757496169199575185708826140}{2^{128}}
<c_*<
\frac{-607918036626757496169199575185708826139}{2^{128}}.
\]

The source certificate gives \(x_{18}=-x_9\), the proper degree-two central representative \(G:V_3\to U_3\), and the three disjoint small Julia intervals

\[
K_0=K_9=[x_9,x_{18}],\quad
K_1=G(K_0)=[x_{12},x_3],\quad
K_2=G^2(K_0)=[x_6,x_{15}].
\]

The dividing fixed point \(\alpha\) of \(G\) is positive and satisfies \(3/32<\alpha<1/10\). The exact ordering needed below is

\[
x_6<x_{15}<x_9<0<x_{18}<\alpha<x_{12}<x_3.
\tag{1.1}
\]

For orientation only, \(x_3\approx0.18782\), \(x_6\approx-0.14732\), \(x_9\approx-0.02284\), \(x_{12}\approx0.18259\), and \(x_{15}\approx-0.12988\). None of the verification uses these rounded decimals.

**Proposition 1.1 (actual native tree and one new attachment).** The KKL Hubbard tree for the period-three small-Julia cycle of this physical \(G\), and its preimage in the degree-two source \(V_3\), are

\[
\boxed{T=[x_6,x_3],\qquad T'=G^{-1}(T)\cap V_3=[-x_3,x_3].}
\tag{1.2}
\]

Consequently \(T'\setminus T=[-x_3,x_6)\) has exactly one component, attached at the left endpoint \(x_6\) of \(K_2\).

**Proof.** The inherited Misiurewicz and straightening input makes \(K_3\) a locally connected full continuum with empty interior, hence a dendrite. The already certified invariant real interval \([x_6,x_3]\) is contained in \(K_3\). Its endpoints belong to the full small-Julia cycle. Uniqueness of arcs in a dendrite implies that the smallest connected subset containing that cycle is exactly this real interval, which is KKL's Section 2.5 definition of \(T\).

The polynomial \(G=f^3\) is even. Its derivative is \(G'(z)=8z f(z)f^2(z)\). The exact interval test proves \(f(z)<0<f^2(z)\) throughout \([-x_3,x_3]\), so \(G\) is strictly increasing on its negative half and strictly decreasing on its positive half. Moreover \(G(0)=x_3\) and \(G(\pm x_3)=x_6\). Thus every value of \(T\) has its two real preimages, counting multiplicity, in \([-x_3,x_3]\). The interval lies in the central source component: its image is in \(T\Subset U_3\), it is connected and contains zero. The map on that component has degree **two**, not the global polynomial degree eight. These two real preimages therefore exhaust its fiber and prove (1.2). The strict inequality \(-x_3<x_6\) is certified by interval arithmetic. The same image containment makes \(T'\subset K_3\). \(\square\)

In what follows, the two maps are therefore precisely

\[
g=G:V_3\setminus T'\to U_3\setminus T,
\qquad
\iota:V_3\setminus T'\hookrightarrow U_3\setminus T.
\tag{1.3}
\]

The first is a degree-two unramified covering and the second an embedding. The two restrictions found below will be **disjoint subpaths**, not two full lifts under a noninjective map.

## 2. Constructing the actual KKL marking, not an arbitrary arc labeling

There are no branch points of the interval tree. The marked vertex set of KKL Section 2.5 is therefore

\[
\widehat{\mathcal K}=K_0\cup K_1\cup K_2\cup\{\alpha\}.
\]

Take its sides on the inner Carathéodory boundary of \(T\), and form the **induced** ideal marking as in Appendix A.1. The complementary edge-side intervals are included by this induced-marking operation. A terminal interval such as \(K_2\) contributes one connected side through the tip; the middle interval \(K_0\) contributes two. This gives ten inner atoms, indexed in the following cyclic order:

| Target atom | Actual physical side |
|---:|---|
| \(I_0\) | terminal side of \(K_2\), through left tip \(x_6\) |
| \(I_1\) | upper edge \((x_{15},x_9)\) |
| \(I_2\) | upper side of \(K_0\) |
| \(I_3\) | upper edge \((x_{18},\alpha)\) |
| \(I_4\) | upper edge \((\alpha,x_{12})\) |
| \(I_5\) | terminal side of \(K_1\), through right tip \(x_3\) |
| \(I_6,I_7,I_8,I_9\) | corresponding lower sides in reverse order |

There are five physical cut locations \(x_{15},x_9,x_{18},\alpha,x_{12}\), each with distinct upper and lower accesses. The outer ideal circle can be taken as one whole-component marking atom, as allowed in Appendix A.1. The calculations here concern the inner circle; they do **not** assert that the inclusion is proper on its outer boundary.

The covering marking \(\mathcal I'=g^*\mathcal I\) has twenty inner atoms \(S_0,\ldots,S_{19}\). The source real cut locations, in increasing order, are

\[
-x_{12},\ x_6,\ x_{15},\ -\alpha,\ x_9,\ x_{18},\
\alpha,\ -x_{15},\ -x_6,\ x_{12}.
\tag{2.1}
\]

Index \(S_0\) through the left tip \(-x_3\), then the upper intervals, \(S_{10}\) through the right tip \(x_3\), and the lower intervals in reverse. Exact orbit identities and evenness give the preimages of all five target cut locations: for example \(G(\pm x_{12})=x_{15}\), \(G(\pm x_6)=x_9\), \(G(\pm x_{15})=x_{18}\), and \(G(\pm\alpha)=\alpha\). The identity \(x_{18}=-x_9\) supplies the remaining pair. This is the **complete cut preimage**, not a sample-based guess. Monotonicity of the degree-two real map, with preservation/reversal of the upper side on the negative/positive branches, fixes

\[
\boxed{g(S_s)=I_{s\bmod10}.}
\tag{2.2}
\]

### Proposition 2.1 — explicit maximal inner pullback and source refinement

Apply KKL Proposition 6.5 to the actual tree inclusion (1.3). It describes \(P_i=\iota^*I_i\) as the original side preimage together with the Carathéodory boundary of attachments incident there. The **only** attachment is at the tip of \(I_0\). In the genuine source marking, its new boundary occupies \(S_{19},S_0,S_1\). The resulting exact connected blocks are:

| \(i\) | \(P_i\), in cyclic source order | Length |
|---:|---|---:|
| 0 | \(S_{18},S_{19},S_0,S_1,S_2\) | 5 |
| 1 | \(S_3,S_4\) | 2 |
| 2 | \(S_5\) | 1 |
| 3 | \(S_6\) | 1 |
| 4 | \(S_7,S_8,S_9\) | 3 |
| 5 | \(S_{10}\) | 1 |
| 6 | \(S_{11},S_{12},S_{13}\) | 3 |
| 7 | \(S_{14}\) | 1 |
| 8 | \(S_{15}\) | 1 |
| 9 | \(S_{16},S_{17}\) | 2 |

Interior cut points between atoms of a displayed block are included; its two outer endpoints are omitted, giving an open multi-interval. These blocks are pairwise disjoint and exhaustive on the inner circle up to their endpoints. Hence the inner pullback marking is defined and \(g^*\mathcal I\) refines it. Every block's end-atoms lie over \(T\), so the inclusion is **end-proper on every one of the ten inner pullback intervals**. It is proper on all except \(P_0\), whose middle attachment sides map physically to \(T'\setminus T\), in the **interior** of the target surface. This is a concrete realization of the distinction illustrated by KKL Figure A.1 and Proposition 6.6.

This paragraph **uses** KKL Proposition 6.5 after establishing its native geometric hypotheses. It is not an independent new proof of that proposition. In particular, the operation that collapses the attachment boundary to the old left tip is only a useful encoding of the pullback blocks. It is **not** the actual boundary extension of \(\iota\) at attachment-side points; those points map into the target interior.

## 3. A fully marked breakable path with exactly two surviving restrictions

Fix

\[
q=-\frac18,\qquad w_s=-\frac5{32},\qquad
\gamma_w(t)=\frac{q+w}{2}+\frac{q-w}{2}e^{2\pi it},
\quad0<t<1.
\tag{3.1}
\]

The endpoint at \(t=0\) is the upper access to \(q\), and at \(t=1\) its lower access. They are distinct ideal points despite having the same physical impression. Exact arithmetic certifies

\[
x_{15}<q<-\alpha,\qquad -x_{12}<w_s<x_6.
\tag{3.2}
\]

The small circle has center \(-9/64\) and radius \(1/64\). An outward rational disk enclosure of **all** its closed disk gives

\[
|G(z)|<1/20<1/4
\quad\text{and clearance to }\partial U_3>1/5.
\tag{3.3}
\]

Its center lies in \(T'\subset V_3\). Since the disk is connected and lies in \(G^{-1}(U_3)\), it is entirely in the central component \(V_3\). This certifies the full curve, not finitely sampled points.

**Theorem 3.1.** The proper target path \(\gamma_{w_s}\) is a path in the **actual** marked surface \((U_3\setminus T,\mathcal I)\). Its filtered restriction consists of exactly two proper marked source paths, with endpoint-atom pairs

\[
(S_3,S_1),\qquad (S_{19},S_{17}).
\tag{3.4}
\]

Both survive Appendix A.1's short-multi-interval exclusion and Appendix A.3.2's single-pullback-interval exclusion. Their dynamical pushforwards have target endpoint pairs

\[
(I_3,I_1),\qquad(I_9,I_7),
\tag{3.5}
\]

so \(F_*\gamma_{w_s}=g_*\iota^*\gamma_{w_s}\) contains exactly two paths: it **breaks in KKL's actual marked sense**.

**Proof.** The circle meets the real line only at \(q\) and \(w_s\). The latter is outside \(T\) but strictly inside the newly attached part of \(T'\), so the full target path is proper and its source restriction is exactly its upper and lower open semicircles. There are no other interior intersections with \(T'\). Their finite slit prime-end endpoints are exactly (3.4), by the physical cut order (2.1).

The target endpoint atoms are \((I_1,I_9)\); the shortest connected marked boundary multi-interval containing both has length three. For the upper and lower source pieces the shortest spans also have length three: \((S_1,S_2,S_3)\) and \((S_{17},S_{18},S_{19})\). Thus none can be subordinate to a multi-interval of length at most two. Their coarse endpoint pairs are \((P_1,P_0)\) and \((P_0,P_9)\). Since these are different open pullback intervals, neither piece is subordinate to any single \(P_i\). Both therefore remain after the **actual marking filters**, unlike an untested two-copy example.

Equation (2.2) gives (3.5); these pairs again have shortest marked span three. The two images are distinct. Indeed \(G\) is injective on the negative-real-half-plane portion of \(V_3\): evenness and degree two imply that any two preimages in \(V_3\) are opposite points, and both cannot have negative real part. The two semicircles lie in that half-plane and are disjoint. \(\square\)

## 4. Same target arc class, different marked restriction count

Replace \(w_s\) by \(w_b=-13/64\). Then \(w_b<-x_3\), so the larger circle avoids \(T'\) at every interior time. Its center is \(-21/128\), radius \(5/128\). Exact disk arithmetic yields

\[
|G(z)|<21/100<1/4,
\qquad \operatorname{dist}(G(z),\partial U_3)>1/25
\tag{4.1}
\]

throughout the closed disk; its center is again in \(T'\). Hence the whole disk belongs to \(V_3\).

The unique proper source restriction has endpoints \((S_3,S_{17})\), shortest marked span seven, and coarse endpoints \((P_1,P_9)\). It survives both filters. Its single dynamical image has endpoint pair \((I_3,I_7)\) and shortest span five. Therefore \(\gamma_{w_b}\) is **unbreakable** at this step.

But varying \(w\) continuously from \(-5/32\) to \(-13/64\) gives a proper homotopy **relative to the same two ideal endpoints** in \(U_3\setminus T\): every \(w<x_6\), the disks are nested inside the certified larger disk, and every circle avoids \(T\) except its two endpoint approaches at \(q\). Thus

\[
\boxed{[\gamma_{w_s}]=[\gamma_{w_b}],\qquad
\#\iota^*\gamma_{w_s}=2,\quad\#\iota^*\gamma_{w_b}=1,}
\tag{4.2}
\]

where both counts include the actual KKL filters.

**Precise consequence.** The number of surviving marked restrictions of an arbitrary representative is **not a function of its target relative-endpoint arc class alone**. Any algorithm that uses only that arc class or its endpoint word and silently assigns a single restriction count is invalid even for this physical native example. This does not contradict Appendix A.3.3: its domination relation is defined by the **existence of representatives** with specified restrictions, not by requiring every representative to have identical restrictions. Nor does it assert a failure for canonical hyperbolic-geodesic representatives or any other separately prescribed path family.

## 5. An entire marked wave and sharp harmonic-series equality

The marked breakage is not confined to one curve. Set

\[
c_0=-9/64,\qquad r_0=3/256,\quad r_1=1/64,
\qquad\gamma_r(t)=c_0+r e^{2\pi it},\quad r_0<r<r_1.
\tag{5.1}
\]

These disjoint concentric circles, with their right-hand point omitted, form a lamination \(S\) of proper target paths. Their right endpoints range over \((-33/256,-1/8)\), strictly in the same upper/lower target edge intervals \(I_1,I_9\); their left crossings range over \((-5/32,-39/256)\), strictly in the attachment atoms \(S_1,S_{19}\). The exact checker proves these **whole-range** inclusions. All leaves lie in the small certified disk (3.3). The lamination is a wave subordinate to the left boundary multi-interval \((I_9,I_0,I_1)\), with crest \(I_0\). Every leaf has precisely the two surviving source restrictions of Theorem 3.1.

Use \(\zeta=\log(z-c_0)\), with angle \(0<\operatorname{Im}\zeta<2\pi\) on the slit annulus swept out by these paths. It maps the target wave to the vertical foliation of a rectangle of horizontal width \(\log(r_1/r_0)=\log(4/3)\) and vertical height \(2\pi\). Removing the new tree attachment cuts this rectangle along height \(\pi\). Each source half-wave is consequently the same-width rectangle of height \(\pi\). For the extremal **width** convention in KKL,

\[
\boxed{
\mathcal W(S)=\frac{\log(4/3)}{2\pi},\qquad
\mathcal W(S'_+)=\mathcal W(S'_-)=\frac{\log(4/3)}{\pi}=2\mathcal W(S).
}
\tag{5.2}
\]

The usual rectangle calculation applies to the family in the ambient surface as well: its leaves fill this strip, and density outside the strip cannot improve the extremal-length problem for these specified paths. Equivalently, the rectangle computation follows from Cauchy–Schwarz and the extremizing constant density there.

Here \(\iota\) is an **embedding**, so the extra joint-injectivity hypothesis of KKL Lemma A.11 holds, unlike the duplicated-tile setting of PR #67. The harmonic-series inequality is sharp:

\[
\boxed{
\mathcal W(S)
=\left(\mathcal W(S'_+)^{-1}+\mathcal W(S'_-)^{-1}\right)^{-1}.
}
\tag{5.3}
\]

Moreover \(G\) is conformal and injective on the entire wave support in the negative half-plane. Both pushed child waves retain the width in (5.2); their bases are \((I_1,I_2,I_3)\) and \((I_7,I_8,I_9)\), with crests \(I_2\) and \(I_8\), the two sides of the critical small Julia interval \(K_0\). Thus this particular physical stage exhibits exact two-child marked breakage and **doubling of each child width**, while the series comparison itself has **no strict surplus**. These are local calculations at one stage, not a uniform large-q amplification result.

## 6. What has and has not been resolved

**Resolved for this representative:** a native Hubbard tree, its full one-step preimage and attachment; the maximal inner pullback marking by KKL Proposition 6.5; the actual 20-to-10 refinement; all inner end-properness predicates; two examples that pass the real path-subordination filters; representative-dependent marked breakage; and an exact marked-wave width calculation.

**Not resolved:** the complete arbitrary-path groupoid of the canonical localized map, the remaining nine-generator connector words in Issue #62, canonical-geodesic or proof-selected wave behavior, iterated/non-locally-connected attachment cases, large-rotation or global KKL estimates, or global H1–H4/UPTCR/MLC. The locally connected degree-two physical representative used here must not be silently replaced by the larger canonical psi-map. Our example realizes a behavior KKL already permits; it is not evidence that their stated theorem is false. Mathematical novelty and independent specialist validation have not been established.

## 7. Reproduction, certificate boundary, and attribution

Run from the repository root:

```sh
python research/independent_audits/verify_tip_KKL_tree_marked_breakage.py --check-manifest
lake build TipKKLTreeMarking
```

The Python checker reads the original exact parameter and real phase manifest, recomputes outward dyadic orbit intervals at precision \(2^{-256}\), validates the complete real cut orders, derives the two maps on atoms from physical sample locations and the exact cut-preimage proof, verifies all coarse block endpoint tests and both KKL exclusion filters, and certifies both **whole complex disks** and the **whole marked-wave endpoint ranges**. It does not infer the analytic result from sampled curves. The Lean layer checks the finite partition, cyclic block, refinement and path-filter arithmetic. Neither formalizes dendrites, Carathéodory prime ends, complex quadratic-like restrictions, the source KKL pullback theorem, nor extremal width.

**Primary source:** Kahn–Kapiamba–Lyubich, *MLC for parabolically bounded primitive renormalization*, arXiv:2606.27272v1 (2026), Section 2.1 (ordinary quadratic-like maps as a subclass), Section 2.5 (native tree/vertices), Section 6.1 Propositions 6.5–6.6 (attachment and marking), Appendix A.1 (markings and subordination), A.3.2 Lemma A.11 and Proposition A.12 (restriction/width), A.3.3–A.3.4 (representatives and breakage). https://arxiv.org/html/2606.27272v1

**Previously certified repository inputs:** `nonattracting_tip_complex_two_scale_20261106.md` for G:V3→U3, its degree/connectedness and the real invariant interval; `tip_interval_root_and_marked_morphism_obstruction_20261106.md` and `results/tip_root_interval_geometry.json` for exact small Julia intervals; `tip_kl_terminal_first_child_20261106.md` for the real dividing fixed-point/germ convention. The new proof does **not** rely on the C4 wake root-sheet theorem of PR #64. GPT-6 assisted this source-grounded synthesis and exact checker. Independent specialist review remains necessary; no ledger theorem status is promoted.
