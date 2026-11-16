# Prime-end and KKL marking identification for the real primitive-tip family

**Audit dated 2026-11-16. Additive proof, all integers p >= 3.** This note discharges the specific *family-dependent* identification assumed in [the uniform family theorem](../real_primitive_tip_family_uniform_20261116/NOTE.md), without editing that theorem or any old certificate. The argument uses named, independently published theorems. **It does not identify an extremal Wave, give a canonical width, or prove a larger parameter-chart uniqueness statement.** In particular the source short-arc spans are **3, 3, 7** (not 3, 3, 3), and the covered spans are **3, 3, 5**, as corrected by [the ten-period audit](../real_primitive_tip_family_unconditional_20261116/NOTE.md).

## Precise statement and provenance

Let \(f=f_{c_p}:z\mapsto z^2+c_p\), \(x_j=f^j(0)\), \(G=f^p\), \(P_p=x_{6p}+x_{3p}\), and \(A=[z^2]G=\prod_{j=1}^{p-1}2x_j<0\). Here \(c_p\) is the *selected* root of \(P_p=0\), with the signed real itinerary \(+--+-+\) and the strict two-line order (O1),(O2) from the merged family certificates. For \(3\le p\le12\) use the ten **adjacent rational \(2^{-256}\)** parameter brackets and \(U_p=D(0,R_p)\), with \(R_3=1/4\), \(R_p=2^{-p}\) for \(p\ge4\), from [the finite audit](../real_primitive_tip_family_unconditional_20261116/NOTE.md). For \(p\ge13\) use the *explicit* near-\(-2\) kneading chart of [the all-period audit](../real_primitive_tip_family_all_p_20261116/NOTE.md), with \(R_p=2^{-p}\), \(q=4^{-p}\), \(-1795/1000<\tau=A x_p<-1785/1000\), \(3/(20q)<|A|<17/(100q)\) and complete-disk estimate \(|e_\tau(w)|<88q\) on \(|w|\le21/10\). Write \(V_p=\operatorname{component}_0(G^{-1}(U_p))\), \(G:V_p\to U_p\) the already certified proper degree-two quadratic-like map.

**Identification theorem (all p >= 3, relative only to the cited general theorems).** Set \(t=x_{6p}=-x_{3p}>0\), and
\[
 K_0=[-t,t],\quad K_1=[x_{4p},x_p],\quad K_2=[x_{2p},x_{5p}],\quad
 \mathcal T=[x_{2p},x_p],\quad \mathcal T'=G^{-1}(\mathcal T)\cap V_p=[-x_p,x_p].
\]
Then (i) \(G\) has a **prime, primitive, period-three** quadratic-like renormalization whose **actual small filled Julia sets**, not merely proposed orbit intervals, are exactly \(K_0,K_1,K_2\); (ii) \(K(G)\) is a locally connected dendrite, and the Kahn–Kapiamba–Lyubich (KKL) Hubbard tree of the renormalization is **exactly** \(\mathcal T\), with its dividing fixed point \(\alpha\in(t,x_{4p})\); (iii) the inner ideal-boundary circles of \(U_p\setminus\mathcal T\) and \(V_p\setminus\mathcal T'\) have, **as the actual Carathéodory/prime-end markings**, respectively ten and twenty atoms given by the five actual cuts and their ten inverse cuts; (iv) the physical single attachment is \([-x_p,x_{2p}]\) on the left, with source sides \(S_{19},S_0,S_1\), and the induced KKL covering, immersion restriction, three-edge matrix and 2-crossing-versus-1-avoiding *filtered proper path classes* are the explicit tables below.

“Relative only to the cited general theorems” means no *additional hypothesis about this family* is taken on faith. The analytic existence and inequalities in (i) are proved below (new arithmetic checks); the *topological* consequences use Douady–Hubbard straightening, the standard Misiurewicz local-connectivity theorem, McMullen's almost-disjointness theorem, the Carathéodory prime-end extension, and KKL's precisely numbered definitions and propositions. Neither the Python code nor Lean formalizes these external theorems.

## 1. New uniformly proper three-return restriction

**Lemma 1 (new, arithmetic plus Rouché and Riemann–Hurwitz).** For every \(p\ge3\), put
\[
 h(w)=A\,G(w/A),\quad H=h^3=A\,f^{3p}(w/A),\quad r=3/10,\quad
 W=\operatorname{component}_0(H^{-1}(D(0,r))).
\]
Then \(W\Subset D(0,r)\), \(H:W\to D(0,r)\) is proper of degree **exactly two**, its unique critical point is zero, \(|H(0)|<r\), and, on \(|w|=r\), the strict Rouché gap versus the **exact** quadratic Taylor term of \(H\), uniformly for every \(|y|\le r\), exceeds \(1/8\). Moreover the disk \(D(0,r/|A|)\) lies in the original \(V_p\), and its entire image under \(G\) lies in \(U_p\). The \(H\)-filled Julia set thus defines a genuine three-return renormalization of \(G\) after shrinking to a neighborhood on which the two intermediate \(G\)-iterates are defined.

**Proof for \(p\ge13\).** In the normalized chart \(h=g_\tau+e_\tau\) where \(g_\tau(w)=w^2+\tau\), \(q\le4^{-13}\), \(\tau\in[-1795/1000,-1785/1000]\) and \(|e_\tau|\le88q\) on \(|w|\le21/10\), by equations (13),(14) of the merged all-period proof. Set \(v=\tau^2+\tau\). Direct rational inequalities give
\[
 7/5<v<10/7,\quad 0<v^2+\tau<13/50,\quad
 4|\tau|v>99/10,\quad 2v+4\tau^2<16,\quad4|\tau|<8.
\]
For \(|w|\le r\), the successive whole-disk bounds are \(|g_\tau(w)|\le|\tau|+r^2<19/10\) and
\(|g_\tau^2(w)|\le v+2|\tau|r^2+r^4<9/5\). The same disks for \(h\) stay inside the \(21/10\) error domain. Thus the *entire* complex error obeys
\[
 |h(w)-g_\tau(w)|\le88q,\quad
 |h^2(w)-g_\tau^2(w)|\le440q,\quad
 |h^3(w)-g_\tau^3(w)|\le1848q;
\]
the factor 4 in each recursion bounds the sum of moduli of the two preceding iterates. There is no Taylor truncation or real-only orbit comparison. Expand exactly
\[
 g_\tau^3(w)=\underbrace{(v^2+\tau)}_{u_3}
       +\underbrace{(4\tau v)}_{B}w^2
       +\underbrace{(2v+4\tau^2)}_{C}w^4+4\tau w^6+w^8.
\]
For \(|w|=r\), all \(|y|\le r\),
\[
 |Bw^2|-|h^3(w)-y-Bw^2|
 \;>\;{99\over10}r^2-
       \left({13\over50}+16r^4+8r^6+r^8+1848\,4^{-13}+r\right)
 \;>\;{1\over8}. \tag{1}
\]
The two strict numerical claims and all intermediate containment claims are tested using only \(\mathbb Q\) in the new verifier. Rouché counts two solutions of \(h^3(w)=y\) in \(D_r\) for *every* target \(y\) in the closed disk, with none on \(\partial D_r\). The orbit critical point 0 has local degree 2 for \(h^3\): it is the only critical of \(h\) near zero and the two intermediate images are not critical (also follows from \(|h'(w)-2w|\le256q\) at \(w=\tau,v+O(q)\)). As \(|h^3(0)|<r\), both local solutions near that critical value lie in the same preimage component \(W\). Properness, Riemann–Hurwitz and the degree count give the asserted quadratic-like disk.

Finally \(|A|>3/(20q)\) and \(|h(w)|<19/10\) on \(D_r\) imply
\[
 |G(w/A)| < (38/3)q <2^{-p}\quad(p\ge13),
 \qquad r/|A|<2^{-p}.
\]
Hence the connected source disk \(D(0,r/|A|)\) lies in \(V_p\), not just in \(U_p\).

**Proof for \(3\le p\le12\).** The new verifier reads the *original, unchanged* finite-results JSON as data, checks that each bracket is adjacent at denominator \(2^{256}\), and **independently rechecks** the two strict endpoint signs and strictly negative derivative of \(P_p\) throughout the full bracket using outward \(2^{-512}\) intervals. It then evaluates \(d_j=f_c^j(0)\) and \(a_j=[z^2]f_c^j(z)\) (so \(a_1=1\), \(a_{j+1}=2d_j a_j\)) for \(j\le3p\), and bounds every term of order at least four on a whole complex disk of radius \(\rho=r/|A|\) via
\[
 T_1=0,\qquad
 T_{j+1}=2|d_j|T_j+(|a_j|\rho^2+T_j)^2. \tag{2}
\]
Each step uses an outward \(2^{-192}\) rational **upper** rounding of the tail, not a floating-point estimate. Upper and lower bounds for \(|A|,\rho,|a_{3p}|\) enclose the exact coefficient \([w^2]H=a_{3p}/A\). For **each** \(p=3,\ldots,12\) the verifier proves
\[
 \underbrace{|A|_{\rm lo}|a_{3p}|_{\rm lo}(r/|A|_{\rm hi})^2}
 _{\text{lower bound for the quadratic term}}\;
 -\underbrace{|A|_{\rm hi}(|d_{3p}|_{\rm hi}+T_{3p})-r}
 _{\text{upper bound for the full perturbation}}
 \;>\;1/8,\tag{3}
\]
plus \(|A|_{\rm hi}|d_{3p}|_{\rm hi}<r\), \(\rho<R_p\), and \(|d_p|+|A|\rho^2+T_p<R_p\). Formula (2) includes *all* nonlinear terms. The p=3 exceptional original radius \(R_3=1/4\) is respected. As in the large-period case, Rouché and Riemann–Hurwitz finish the claim. This is a finite family of strict **certificates**, not sampling or interpolation.

It is important that (1) and (3) concern the **new 3p-return**, with normalized gap \(>1/8\), whereas the old all-period result's \(>1/25\) concerns the distinct original \(p\)-return \(G\).

## 2. The little Julia sets really are intervals

**Lemma 2 (proved using external theorem DH85).** The filled Julia set of \(H\) in Lemma 1 is **exactly** \(A[-t,t]=[-u,u]\), where \(u=|A|t\). Consequently the physical small filled Julia set of \(G^3=f^{3p}\) is \(K_0=[-t,t]\), and the other two sets are exactly \(K_1,K_2\).

**Proof.** The tip relation \(x_{6p}+x_{3p}=0\) and evenness of every positive iterate of \(f\) give the **exact** relations
\[
 G^3(0)=-t,\qquad G^3(-t)=G^3(t)=t.
 \tag{4}
\]
The strict real order and the two-sheeted monotonicity from the merged family certificates give
\[
 G([-t,t])=[x_{4p},x_p]=K_1,\quad
 G(K_1)=[x_{2p},x_{5p}]=K_2,\quad G(K_2)=[-t,t]=K_0. \tag{5}
\]
All three disjoint compact intervals lie in \(V_p\), because the larger invariant \(\mathcal T\) lies in \(V_p\) (proved below). Thus \(G^3(K_0)=K_0\); equivalently \(H([-u,u])=[-u,u]\). The interval is connected, contains zero, is contained in \(D_r\) by Lemma 1 and the critical-value bound (or by \(|A|t=|H(0)|<r\)), and lies in the central preimage component \(W\). Therefore \([-u,u]\subset K(H)\). By the **connectedness criterion** in Douady–Hubbard [DH85, Proposition 2] or KKL §2.1, the degree-two filled Julia set \(K(H)\) is connected.

Now invoke [DH85, Theorem 1 (Straightening Theorem)]: a quadratic-like map with connected filled Julia set is hybrid conjugate on neighborhoods to a uniquely determined monic centered quadratic \(Q_\gamma(z)=z^2+\gamma\). The critical orbit (4) is
\[
 0\longmapsto u\longmapsto -u\longmapsto -u,\quad u\ne0.
\]
Hybrid conjugacy preserves this exact critical portrait. For \(Q_\gamma\), the equation \(Q_\gamma^3(0)=Q_\gamma^2(0)\) is **exactly**
\(\gamma^3(\gamma+2)=0\). Since the critical point is not fixed, \(\gamma\ne0\), hence \(\gamma=-2\). The filled Julia set of \(z^2-2\) is the **arc** \([-2,2]\); the hybrid conjugacy carries its two endpoints (the critical value \(-2\) and its fixed image \(2\)) to \(u\) and \(-u\). Consequently \(K(H)\) is a topological arc with endpoints \(\pm u\). An arc cannot properly contain the entire straight segment joining its endpoints as a subarc: uniqueness of the arc between two points forces
\[
                         K(H)=[-u,u].
\]
Rescaling and (5) give all three claimed **filled Julia sets**. No assumption that a drawn real segment is a little Julia set has been imported.

**Intermediate domains and primitivity.** Their images (5) are pairwise disjoint by strict cut order, so the renormalization is **primitive** in KKL §2.3's definition. To make it a renormalization of the original \(G:V_p\to U_p\) (not just a polynomial-like restriction of the entire polynomial \(f^{3p}\)), note \(K_0\cup K_1\cup K_2\Subset V_p\), and each \(G^j\) is holomorphic near the respective compact phase set. Shrink the quadratic-like source/target neighborhoods of \(K(H)\) in the standard way (e.g. by pulling back sufficiently small equipotential collars under the straightening; this is the *restriction of a polynomial-like map near its filled Julia set* in DH85 §1 and KKL §2.1) so that the first two intermediate images stay in \(V_p\) and the three phase neighborhoods are disjoint. This restriction does not change \(K(H)\). The finite and large-period disk inequalities already give the required starting neighborhood; no uniform modulus of the shrunken collars is asserted.

## 3. Primeness, periodic repulsion and local connectivity

**Lemma 3 (no earlier renormalization, relying precisely on McMullen).** There is no period-two quadratic-like renormalization of \(G\) with connected filled Julia set containing its critical point. Hence the primitive period-three renormalization of Lemma 2 is **prime**, as required by KKL §2.3.

**Proof.** First, \(T=[x_{2p},x_p]\subset[-x_p,x_p]\), and (by real monotonicity and the same cut order) \(G([-x_p,x_p])=T\) and \(G(T)\subset T\). The entire real interval \([-x_p,x_p]\) lies in \(V_p\), by the merged realization proofs. Hence \(T\subset K(G)\); every \(z\in K(G)\) has bounded \(f\)-orbit, since the finitely many intermediate \(f^j(K(G))\), \(0\le j<p\), are compact.

The critical orbit of the *global* polynomial \(f\) is strictly preperiodic: (4) gives \(f^{9p}(0)=f^{6p}(0)=t\ne0\), and zero cannot belong to the eventual cycle (if it did, its period would divide \(3p\), forcing \(f^{3p}(0)=0\), in conflict with \(-t\ne0\)). Thus \(f\) is a **Misiurewicz quadratic polynomial**, with connected, locally connected Julia set that is a dendrite; this is the named external **Misiurewicz local-connectivity/dendrite theorem** [Lyubich, *Conformal Geometry and Dynamics of Quadratic Polynomials*, Theorem 27.4; also Milnor, *Dynamics in One Complex Variable*, Corollary 17.4 and Theorem 17.5 for subhyperbolic polynomials]. Since \(K(G)\) is connected by its trapped critical point, it is a subcontinuum of this dendrite; it is therefore a dendrite as well. In a dendrite the arc between two real points of \(T\) is the actual real subsegment (since that segment is already in \(T\)).

Suppose \(L\subset K(G)\) were the connected small filled Julia set of a degree-two \(G^2\)-renormalization containing 0. The \(G^2\)-critical orbit stays in \(L\), so \(x_{2p}=G^2(0)\) and \(x_{4p}=G^4(0)\) lie in \(L\). Dendrite arc uniqueness forces \([x_{2p},x_{4p}]\subset L\). That segment contains zero, and (5) and monotonicity imply \(G([x_{2p},x_{4p}])=[x_{5p},x_p]\). Hence
\[
  [x_{5p},x_{4p}]\subset L\cap G(L)
\]
is a **nondegenerate** real interval. By the external **almost-disjoint little Julia sets theorem** [McMullen, *Complex Dynamics and Renormalization*, **Theorem 7.3**], *distinct* small filled Julia sets of a quadratic-like renormalization meet in at most one repelling periodic point. Therefore \(L=G(L)\). But then \(0\in L=G(L)\) has a preimage \(y\in L\) under \(G\); as \(G(0)=x_p>0\), \(y\ne0\). Both \(0\) and \(y\) are distinct critical points of \(G^2\) in the domain of the alleged connected degree-two renormalization, impossible by Riemann–Hurwitz (degree two has exactly one simple critical point). Contradiction. Since the only integer period strictly between one and three is two, the period-three renormalization is prime.

**Repulsion, Carathéodory landing and symmetry.** The same global Misiurewicz theorem makes every periodic point of \(f\), hence of \(G=f^p\), repelling; it supplies the periodic-repulsion hypothesis in KKL §§2.4–2.5. Its local connectivity and the **Carathéodory extension of the external Böttcher uniformization** [Milnor, Corollary 17.4; Carathéodory's theorem] imply every global Julia point, in particular \(x_{2p},x_{3p},x_{4p},x_{5p},x_{6p},x_p,\alpha\), is the landing point of at least one external \(f\)-ray. These orbit/fixed points are preperiodic and therefore have eventually periodic ray accesses. Complex conjugation preserves the global polynomial, its external map, the fixed-point marking, and pairs upper/lower accesses. **No specific external angle is used or certified here**; a ray-angle atlas is not silently substituted for the prime-end slit model.

## 4. KKL's *actual* Hubbard tree and ideal-boundary circles

**Lemma 4 (physical KKL tree).** KKL §2.5 defines the Hubbard tree to be the *smallest connected subset of \(K(G)\)* containing the whole cycle of little filled Julia sets, **not** the convex hull of arbitrarily chosen orbit points. By Lemmas 2–3 those sets are the real \(K_0,K_1,K_2\). Their leftmost and rightmost points are \(x_{2p}\) and \(x_p\), and \(T=[x_{2p},x_p]\) is already a connected subset of \(K(G)\). Since \(K(G)\) is a dendrite, any connected subset containing these endpoints must contain their unique real arc \(T\). Thus KKL's tree is *exactly* \(T\). The fixed point \(\alpha\in(x_{6p},x_{4p})\) belongs to the **interior** of this arc; its removal disconnects \(K(G)\), so it is KKL's dividing fixed point \(\alpha_G\), as characterized in **KKL §2.4**. There are no hidden off-real edges in the *Hubbard hull*, even though the larger full Julia dendrite has other branches.

**Lemma 5 (Carathéodory prime-end marking, no conjectural access).** \(U_p\setminus T\) is an annulus with locally connected boundaries, one a round circle and the other a closed real segment. Likewise \(V_p\setminus T'\) is an annulus; the original proper degree-two map has a Jordan source and \(T'\Subset V_p\). Cut such an annulus by a small crosscut joining the two boundary components; the resulting simply connected slit domain has locally connected boundary. Apply **Carathéodory's prime-end boundary-extension theorem** (for the simply connected slit domain) and glue back the paired crosscut edges. This constructs the two ideal-boundary circles in **KKL Appendix A.1**, whose definition via \((\partial\mathbb D\setminus\Lambda)/\Delta\) agrees with the prime-end circles for an annulus. An interior real point of the slit has precisely **two** local prime-end accesses, one from the upper and one from the lower half-plane; a slit endpoint has **one**. To see that there are no unseen accesses, take a sufficiently small Euclidean disk about an interior slit point: deleting the slit divides it into exactly the upper and lower connected local sectors. At an endpoint, deleting the terminal slit leaves one local sector. Shrinking crosscuts in those sectors gives single-point impressions, as required by Carathéodory. Reflection swaps the two interior accesses and fixes the endpoint access.

The five **real physical target cuts**, in strict increasing order,
\[
 a=x_{5p}<b=x_{3p}<d=x_{6p}<e=\alpha<h=x_{4p},
\]
therefore mark five pairs of prime ends on the inner circle, hence exactly **ten** open atoms \(I_0,\ldots,I_9\) in cyclic order. The outer boundary circle contributes **one whole-component atom**, not ten. The source tree preimage \(T'=G^{-1}(T)\cap V_p=[-x_p,x_p]\) follows from the two real sheets and the proper degree-two count: the real critical preimage component maps exactly onto \(T\), exhausting degree two. The ten inverse cuts in the source have the strict physical order proved in (O2):
\[
 -x_{4p}<x_{2p}<x_{5p}<-\alpha<x_{3p}<
 x_{6p}<\alpha<-x_{5p}<-x_{2p}<x_{4p}.
\]
They give **twenty** upper/lower source atoms \(S_0,\ldots,S_{19}\) and a separate unmarked outer circle. This proves that the finite order labels are the actual KKL ideal marking on each annular *slit complement*; no assumption about unnamed ambient ray angles has been used.

## 5. Attachment, covering and immersion: explicit tables

**Single attachment and properness.** Since \(x_{2p}>-x_p\) and \(x_p\) is the right endpoint, \(T'\setminus T\) has **one** connected component, the open-left extension \([-x_p,x_{2p})\), whose closure attaches to \(T\) only at \(x_{2p}\). Its Carathéodory boundary contributes exactly the consecutive source sides \(S_{19},S_0,S_1\). This is the attachment specified in **KKL Proposition 6.5**: for the inclusion/immersion \(\iota:V_p\setminus T'\hookrightarrow U_p\setminus T\), \(\iota^*I\) is the union of its inverse-side accesses and the Carathéodory boundaries of added tree components attached at \(I\). Crucially this is a **set-valued restriction of proper paths**, not a pointwise continuous map of every source ideal endpoint. It is therefore legitimate that the source attachment lies in a pulled-back *block* but has no individually proper target ideal endpoint.

**Covering \(G_*\).** On \(V_p\setminus T'\) the original \(G\) has no critical point and is a proper unbranched holomorphic degree-two cover of \(U_p\setminus T\). It extends to the corresponding *ideal boundary covering* in **KKL Appendix A.3.1**. Choosing \(S_0\) above the leftmost source sheet and \(I_0\) above the matching target sheet, and respecting the increasing/decreasing real sheet orientations, the actual covering table is
\[
                         G_*(S_s)=I_{s\bmod 10},\quad 0\le s<20.
\]
Every target atom has exactly two source atoms. The fact that the two half-planes are exchanged under the orientation reversing real branch accounts for the cyclic numbering; it is not an extra analytic hypothesis.

**Immersion \(\iota^*\), as consecutive source blocks.** Read by KKL Proposition 6.5 and the single attachment, the target-to-source blocks are precisely
\[
\begin{array}{c|l}
 I_0&S_{18},S_{19},S_0,S_1,S_2\\
 I_1&S_3,S_4\\
 I_2&S_5\\
 I_3&S_6\\
 I_4&S_7,S_8,S_9\\
 I_5&S_{10}\\
 I_6&S_{11},S_{12},S_{13}\\
 I_7&S_{14}\\
 I_8&S_{15}\\
 I_9&S_{16},S_{17}
\end{array}
\]
The first block contains **all three** attached source sides. Its end sides are proper but its entire attached block is not fully proper under \(\iota\); the other blocks have no attachment. The displayed blocks partition the twenty cyclic source atoms once. **KKL Proposition 6.6** and **Appendix A.3.2 and A.3.4** then supply exactly the action on multi-intervals and filtered restrictions, with the geometry just established supplying their hypotheses.

**Old real edges and filtered proper restrictions.** Let the old edges be \(E_0=(a,b), E_1=(d,e), E_2=(e,h)\). The images of the ordered cut endpoints, in their index labels, are \([2,4,4,3,0]\); checking edge coverage by endpoint order gives (rows output, columns input)
\[
 M=\begin{pmatrix}0&0&1\\1&0&1\\1&1&0\end{pmatrix}.
\]
For the *crossing-attachment* isotopy class of a proper path with the source endpoints in the indicated atoms, restricting via the KKL immersion yields the two admissible proper classes with endpoints
\[
    (S_3,S_1),\qquad(S_{19},S_{17}),
\]
and for the *avoiding-attachment* class yields the single admissible class \((S_3,S_{17})\). KKL Appendix A.1's filtered-path convention requires the shorter arc to contain **more than two** atoms. The actual inclusive short-arc lengths in the twenty-atom circle are respectively **3, 3, 7**; under \(G_*\) they yield \((I_3,I_1)\), \((I_9,I_7)\), \((I_3,I_7)\), whose ten-atom short-arc lengths are **3, 3, 5**. All three pass the strict \(>2\) filter. The crossed class therefore has **two** and the avoiding class **one** proper restrictions; nothing is claimed about non-proper paths absorbed by the attached block. These are **topological isotopy/ideal-marking counts**, not assertions of equal extremal widths or of canonical annular Waves.

The finite blocks, covering degrees, attachment, matrix and the corrected \(3,3,7\) / \(3,3,5\) counts are decidable in the new Lean file; Lean **does not prove** the Carathéodory or straightening identifications used to give those labels their physical meaning. The earlier exact finite verifiers independently compute the same real cut and source-side orders.

## 6. Exact scope, external dependencies, and remaining debt

| Claim for the designated \(c_p\), every \(p\ge3\) | Status | Justification |
|---|---|---|
| Existence in the specified chart, exact tip identity and strict cuts | **Unconditional arithmetic/analysis** | Existing read-only p=3..12 and p>=13 certificates; old \(G\) Rouché margin \(>1/25\) for p>=13 |
| New \(G^3\) quadratic-like return and \(>1/8\) normalized Rouché gap | **Unconditional arithmetic + standard Rouché/Riemann–Hurwitz** | Equations (1)–(3); new verifier checks all finite brackets and worst-case \(q=4^{-13}\) |
| Little filled Julia sets equal the three real intervals | **Established using named external theorem** | DH85 Proposition 2 and Theorem 1; critical portrait singles out \(z^2-2\) |
| Primeness, primitivity and physical Hubbard tree | **Established using named external theorems** | Disjoint real phases; McMullen Theorem 7.3; Misiurewicz dendrite theorem; KKL §§2.3–2.5 |
| Prime-end circles, five/ten real cuts, one source attachment, covering and immersion table, 2/1 filtered proper path classes | **Established using named external theorems** | Carathéodory prime ends, KKL §6.1 Propositions 6.5–6.6 and Appendix A.1, A.3.1, A.3.2, A.3.4; explicit slit and symmetry argument |
| Named external-ray *angle* sequences or a canonical ray puzzle | **Not claimed, not needed for the marking** | Ray landing follows from LC, not a specific angular atlas |
| An unrestricted KKL-maximal or canonical Wave, its conformal width, a universal geometric radial-circle witness or strict Wave gain for all p | **OPEN** | The 2/1 topological restriction count does not give physical widths or globally admissible circular path families |
| Uniqueness beyond the explicitly specified near-minus-two chart / full maximal real primitive window, MLC | **OPEN** | Neither this proof nor the source certificates address it |

**Exact external theorem ledger (not Lean axioms).**
1. A. Douady and J. H. Hubbard, [*On the dynamics of polynomial-like mappings* (1985)](https://pi.math.cornell.edu/~hubbard/PolyLikeMaps.pdf), **Proposition 2 (connectedness criterion), Theorem 1 (Straightening)**, and §1 on restrictions/filled Julia sets.
2. C. T. McMullen, [*Complex Dynamics and Renormalization*](https://abel.math.harvard.edu/~ctm/papers/home/text/papers/real/book.pdf), **Theorem 7.3 (Almost disjoint Julia sets)**; invoked only to exclude a hypothetical competing period-two renormalization.
3. M. Lyubich, [*Conformal Geometry and Dynamics of Quadratic Polynomials*](https://www.math.stonybrook.edu/~mlyubich/book.pdf), **Theorem 27.4 (Misiurewicz Julia set locally connected and a dendrite)**. Also J. Milnor, [*Dynamics in One Complex Variable*](https://abel.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf), **Corollary 17.4 and Theorem 17.5** (Carathéodory landing and subhyperbolic local connectivity, numbering in the freely available draft).
4. Classical **Carathéodory boundary-extension/prime-end theorem** for simply connected domains with locally connected boundaries, applied after cutting each slit annulus; see Milnor Corollary 17.4 for the uniformization/ray-landing formulation and the explicit local-sector proof above for the slit double sides.
5. J. Kahn, H. Kapiamba, M. Lyubich, [*MLC for parabolically bounded primitive renormalization*, arXiv:2606.27272v1](https://arxiv.org/abs/2606.27272v1), **§2.1 (quadratic-like maps), §2.3 (prime/primitive renormalization), §2.4 (dividing fixed point), §2.5 (Hubbard tree), §6.1 Propositions 6.5–6.6 (immersion and induced ideal marking), Appendix A.1 (ideal circles and >2 filter), A.3.1 (covering pushforward), A.3.2 (immersion restriction; Proposition A.12), A.3.4 (combinatorial action)**. KKL is used here as a *precisely stated general theorem*, not as an unexplained assertion that a real cut model must equal its physical prime-end model.

## Reproduce and audit

From the repository root, with Python 3.12 (no external Python packages):

    python research/independent_audits/real_primitive_tip_family_prime_end_identification_20261116/verify.py
    python -m unittest discover -s research/independent_audits/real_primitive_tip_family_prime_end_identification_20261116 -p 'test_*.py' -v
    lake env lean research/independent_audits/real_primitive_tip_family_prime_end_identification_20261116/RealPrimitiveTipPrimeEndDiscrete.lean

The verifier is read-only on the previous JSON, independently checks its root witnesses, has exact Fraction arithmetic and strict outward interval bounds for complete holomorphic-disk remainders, and checks worst-case \(p=13\) for a monotone \(q\)-bound valid for all larger periods. Adversarial tests mutate inputs **in memory**, never the merged files. The dedicated workflow also reruns the existing all-period/ten-period/six-period regression commands, existing research-validation mirrors, and the Lean kernel/build. We have not modified any existing source, Native Wave Transfer file, crest asymptotics, or canonical-width file. This note, not a change to the earlier conditional note, is the explicit **discharge** of its cited family-specific prime-end hypothesis with standard external mathematical theorems separated from machine-checked arithmetic.
