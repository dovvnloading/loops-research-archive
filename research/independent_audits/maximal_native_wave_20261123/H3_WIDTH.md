# Selected real slits: full-path conformal comparison and a repaired strict gain

**Date:** 2026-11-23. **Status:** a proposed written analytic proof, conditional
on the explicit physical input package of [NOTE.md](NOTE.md), §1, and using
the intrinsic access and all-winding class results proved there. The full
immersion marking MARK/H2 remains open and is not an input to this
independent-supremum comparison. No assumption of local H3 is made. This is not an external referee certification, a formalized proof,
or a result about MLC. GPT-6 Astra Pro assisted the derivation and checks.

## 1. Exact result, dependencies, and what is new

Let \(G=f_{c_p}^{\,p}:V\to U=D(0,R_p)\), \(p\ge3\), be the selected
physical quadratic-like restriction in the companion note, and write

\[
 r=x_p,\quad \ell=x_{2p},\quad a_0=x_{5p},\quad
 b_0=x_{3p},\quad h_0=x_{4p},\quad e=\alpha_p.
\]

The two actual slit domains are
\(\Omega=U\setminus[\ell,r]\) and
\(\Omega'=V\setminus[-r,r]\). Their intrinsic ideal boundaries and relative
homotopy classes are given by NOTE, §2; the source marking is the pullback
of the target marking by the actual covering in §4. These are the
SLIT-CLASSES inputs, independent of the unresolved immersion-pulled
marking in §3. In particular

\[
 -r<-h_0<\ell<a_0<-e<b_0<0<e<h_0<r.
 \tag{1.1}
\]

Let \(P_p\) be the supremum of the conformal widths of all unbuffered
KKL A.1 Waves on \(\Omega\) with base \((I_9,I_0,I_1)\). Let
\(C_p^+,C_p^-\) be the independently taken suprema for the source bases
\((S_1,S_2,S_3)\), \((S_{17},S_{18},S_{19})\).
The closed crests are respectively \(\overline I_0,\overline S_2,
\overline S_{18}\); saying merely \(I_0,S_2,S_{18}\) suppresses their
two cut endpoints. The supremum definitions do not require attainment.

**Theorem 1.1.** Under the stated physical inputs, the complete parent
quadrilateral foliations below are admissible simple A.1 Waves with
exactly their prescribed minimal bases and closed crests. Every admissible
parent or child leaf is included in the indicated complete lifted path
family. The conformal square-sum densities are admissible for every such
leaf, and the source-excluded boxes remove the claimed positive energy.
In particular,

\[
 0<P_p<\infty,\qquad
 0<C_p^+=C_p^-=:C_p<\infty,
\]
\[
 D_p=\frac1{C_p^+}+\frac1{C_p^-}-\frac1{P_p}
      =\frac2{C_p}-\frac1{P_p}>\frac1{100}
 \quad\text{for every selected }p\ge3.
 \tag{1.2}
\]

This proves the specific **local H3 implication** isolated in the
[v2 referee scope](../../../papers/tip_family_preprint_v2_20261116/sections/referee_scope.tex).
It is conditional on the physical degree-two restrictions, filled
intervals, order, and analytic all-period chart bounds, rather than on
the full immersion H2 or H3. The companion note supplies the intrinsic
ideal-class bridge on each surface. No statement here identifies a
contour inverse image with the native geometric-trace restriction.

The segment and semidisk constructions, finite constants, omitted boxes,
and the intended independent gain already appear in the November 16
[finite](../tip_family_finite_p_wave_gain_20261116/NOTE.md),
[limiting](../tip_family_limiting_wave_gain_20261116/NOTE.md), and
[canonical](../tip_family_canonical_wave_gain_20261116/NOTE.md) gain notes.
They are not new constructions here. The contribution is the complete
all-path and minimal-base proof using the actual hyperbolic ideal collar,
the explicit SC normalization and both-child positivity, and a concrete
correction to the infinite-tail arithmetic.

**The correction is material.** The old limiting checker formed the
physical coordinate-error coefficient as
\((30\cdot15246+88(4^j-1))/3\). Its proved input is
\(30\cdot15246+88(4^j-1)/3\). With the correct box, its old
\(P_p>2/3\) certificate does not follow. The rigorous replacement used
here is

\[
 P_p>\frac{13}{20},\qquad C_p<\frac{63}{50},\qquad
 D_p>\frac{40}{819}>\frac1{100}\quad(p\ge13).
 \tag{1.3}
\]

The old executable checker and its direct dependent assertions have been
corrected, with a dated erratum and an adversarial recurrence-based
regression. A failure of the widest-box certificate is not a
counterexample to the stronger floor. A separate
[corrected all-period proof](../tip_family_wave_gain_correction_20261123/NOTE.md)
isolates the actual \(p=13\) parameter and uses the corrected uniform box
starting at \(p=14\). That route proves \(P_p>2/3\) and
\(D_p>11/126\) for every \(p\ge13\). Both certificates are retained:
(1.3) is the broader single-box estimate, while the separate proof supplies
the sharper bound.

## 2. Width convention and the exact Schwarz–Christoffel normalization

For a curve family \(\Gamma\), use its conformal width, or modulus,

\[
 \mathcal W(\Gamma)=
 \inf_{\rho}\int \rho^2\,dA,\qquad
 \int_\gamma\rho\,|dz|\ge1\quad(\gamma\in\Gamma).
 \tag{2.1}
\]

This is the reciprocal of extremal length. It is monotone under inclusion
of curve families. On a rectangle \((0,H)\times(0,L)\), the family
connecting its two vertical sides has width \(L/H\).
The constant density \(1/H\) gives the upper bound. For the family of all
horizontal segments, Cauchy–Schwarz gives
\(\int_0^H\rho(x,y)^2\,dx\ge1/H\) for each \(y\), hence the same lower
bound after integration. Thus the open horizontal foliation already has
the entire crossing family's width. Its width as a family in a larger
ambient surface is unchanged: restricting an ambient metric to the
rectangle and extending a rectangle metric by zero give both inequalities.
This is the convention in [KKL Appendix A.2.1](https://arxiv.org/html/2606.27272v1#A1.SS2.SSS1).

### Lemma 2.1 — four electrodes, including the normalization constant

In the right half-plane \(\mathbb H_R=\{\Re z>0\}\), take
\(u_1<u_2<u_3<u_4\) on the imaginary boundary and electrodes
\(i(u_1,u_2)\), \(i(u_3,u_4)\). Put

\[
 \kappa=
 \frac{(u_2-u_1)(u_4-u_3)}
 {(u_3-u_1)(u_4-u_2)}\in(0,1),\qquad k=\sqrt\kappa .
 \tag{2.2}
\]

A Schwarz–Christoffel primitive with derivative

\[
 F'(z)=\prod_{j=1}^4(z-iu_j)^{-1/2}
 \tag{2.3}
\]

has, after a rotation and translation, image
\((0,H)\times(0,L)\), with the two electrodes as its vertical sides, where

\[
 L=\frac{2K(k)}{\sqrt{(u_3-u_1)(u_4-u_2)}},\qquad
 H=\frac{2K(\sqrt{1-k^2})}
          {\sqrt{(u_3-u_1)(u_4-u_2)}}.
 \tag{2.4}
\]

Here
\(K(k)=\int_0^{\pi/2}(1-k^2\sin^2 t)^{-1/2}\,dt\).
Consequently the full electrode-joining path family has width

\[
 E=\frac{L}{H}=\frac{K(k)}{K(\sqrt{1-k^2})},
 \qquad \widetilde\rho(z)=\frac{|F'(z)|}{H}
 \tag{2.5}
\]

is admissible for **every** such path, and
\(\int_{\mathbb H_R}\widetilde\rho^2\,dA=E\).

**Proof.** Choose analytic square-root branches on \(\mathbb H_R\).
The [SC rectangle theorem](https://dlmf.nist.gov/19.32) applies to these
four ordered prevertices; the
point at infinity is a regular boundary point because \(F'(z)=O(z^{-2})\).
For clarity, the normalization can also be read directly from its side
integrals. Rotate the domain to the real half-plane and use

\[
 v=\frac{(u_4-u_3)(t-u_1)}
         {(u_3-u_1)(u_4-t)}.
\]

The four endpoints become \(0,\kappa,1,\infty\). The differential acquires
the constant \(1/\sqrt{(u_3-u_1)(u_4-u_2)}\). The first electrode and
the intervening gap have respective absolute integrals

\[
 \int_0^\kappa\frac{dv}{\sqrt{v(\kappa-v)(1-v)}}=2K(\sqrt\kappa),
\]
\[
 \int_\kappa^1\frac{dv}{\sqrt{v(v-\kappa)(1-v)}}
 =2K(\sqrt{1-\kappa}).
 \tag{2.6}
\]

The substitutions \(v=\kappa\sin^2 t\) and
\(v=\kappa+(1-\kappa)\sin^2 t\) prove these equalities.
The gap is the side separating the two electrode sides, so its length is
\(H\), not \(L\). Every connecting path in the rectangle has horizontal
variation at least \(H\). Pulling back its density \(1/H\) proves
admissibility; conformal area gives \(HL/H^2=L/H\). The rectangle argument
following (2.1) proves equality. The same length inequality holds for any
continuous curve using its metric length, including a nonrectifiable curve.
\(\square\)

For symmetric boundary points \((-B,-A,A,B)\), \(0<A<B\), this gives

\[
 k=\frac{B-A}{B+A}.
 \tag{2.7}
\]

This derivation fixes the possible factor-two, reciprocal, and wrong-side
normalization ambiguities.

## 3. All physical leaf classes and the quotient metric

### Lemma 3.1 — three-atom bases force the two end atoms

Every A.1 leaf subordinate to the proper three-atom multi-interval
\((I_9,I_0,I_1)\) has one endpoint in \(I_9\) and the other in \(I_1\).
Every leaf subordinate to \((S_1,S_2,S_3)\) has endpoints in \(S_1,S_3\);
the reflected assertion holds below.

Indeed, NOTE, Lemma 2.2, puts both lifted endpoints in the same lift of the
base. If they belonged to one atom or two adjacent atoms, their lifted
interval would lie in a multi-interval of length at most two. That leaf
would be short and excluded by the A.1 definition. The only remaining
pair is the two end atoms. Conversely a simple path in this selected lift
between the end atoms cannot be subordinate to any one- or two-atom
multi-interval. The other way around the ideal circle is a different
relative-endpoint deck class. This argument uses the complete ideal
collar criterion, not only physical endpoint impressions.

In particular every relevant physical leaf, however much it wanders in
the surface, has exactly the following selected log lift:

* For the parent, use
  \(\pi_P(z)=m-r_P\cosh z\), \(\Re z>0\), where
  \(m=(\ell+r)/2\), \(r_P=(r-\ell)/2\). Its endpoints lie in
  \(i(-b,-a)\) and \(i(a,b)\), where
  \(a=\arccos((m-a_0)/r_P)\), \(b=\arccos((m-b_0)/r_P)\).
  Positive and negative \(t\) are opposite slit banks. The selected
  interval crosses the left tip \(t=0\), with no extra deck turn.
* For the upper child, use \(\pi_C(z)=r\cosh z\).
  Define
  \(a_c=\arccos(h_0/r)\), \(b_c=\arccos(-\ell/r)\),
  \(c_c=\arccos(-a_0/r)\), \(d_c=\arccos(e/r)\).
  Its endpoints lie in \(i(e_1,e_2)\), \(i(e_3,e_4)\), where
  \((e_1,e_2,e_3,e_4)=(\pi-d_c,\pi-c_c,\pi-b_c,\pi-a_c)\).
  In increasing \(t\), these are \(S_3,S_1\), respectively.
  All four angles are ordered in \((0,\pi)\).

The physical log domains \(D_P=\pi_P^{-1}(\Omega)\) and
\(D_C=\pi_C^{-1}(\Omega')\) are invariant under \(z\mapsto z+2\pi i\).
Every such lifted leaf is contained in \(\mathbb H_R\) and joins the
stated electrodes. No hypothesis that its entire lift stays between the
endpoint heights is imposed.

### Lemma 3.2 — square-sum periodization with the physical Jacobian

Let \(\widetilde\rho\) be an admissible comparison density on the entire
right half-plane for one selected four-electrode family. For
\(\pi=\pi_P\) or \(\pi_C\), define the physical density by

\[
 \rho(\pi z)^2|\pi'(z)|^2
   =\sum_{n\in\mathbb Z}
       \widetilde\rho(z+2\pi in)^2 .
 \tag{3.1}
\]

The derivative is nonzero in the open half-plane and is deck-periodic,
so this is well-defined. For the SC metric the sum is locally convergent:
its squared terms are \(O(|n|^{-4})\). Each selected lift has
\(\rho(\pi z)|\pi'(z)|\ge\widetilde\rho(z)\), so every physical leaf has
length at least one. If \(D=\pi^{-1}(\text{physical domain})\), Tonelli
and a fundamental deck domain give the exact identity

\[
 \int_{\text{physical domain}}\rho^2\,dA
 =\int_D\widetilde\rho^2\,dA
 \le \int_{\mathbb H_R}\widetilde\rho^2\,dA.
 \tag{3.2}
\]

Thus the area of this **one** admissible metric bounds every competing
Wave width and hence its supremum. The argument permits arbitrary
proper leaves in the selected class, not only a preferred foliation.
It does not assert that the full-plane comparison foliation projects
injectively, or that its width is attained on the physical surface.

The same proof applies to a deck-invariant vertical strip containing
the complete physical lift. In fact

\[
 |\pi_P(s+it)-m|\ge r_P\sinh s,\qquad
 D_P\subset\{0<s<L_+\},\quad
 L_+=\operatorname{arsinh}\frac{R_p+|m|}{r_P}.
 \tag{3.3}
\]

The conformal map \(z\mapsto\exp(i\pi z/L_+)\) takes this strip to the
upper half-plane. Its four electrode images and Lemma 2.1 give the
finite-strip upper envelope with

\[
 k_{L_+}
 =\frac{\sinh(\pi(b-a)/(2L_+))}
        {\sinh(\pi(b+a)/(2L_+))}.
 \tag{3.4}
\]

Every physical parent leaf is therefore included in both the stated
finite-strip envelope and the full-plane envelope
\(K((b-a)/(b+a))/K(\sqrt{1-((b-a)/(b+a))^2})\).
This supplies the target all-path inclusion required by local H3 as
well as the child inclusion. Their finiteness follows from their strictly
ordered electrodes.

## 4. Embedded parent foliations and their exact minimal base

For the quantitative parent constructions, use the positive scale

\[
 \lambda_p=-A_p>0,\qquad X_j=\lambda_p x_{jp},\qquad
 \rho_p=\lambda_p R_p,\qquad
 m=\frac{X_2+X_1}{2},\quad r_P=\frac{X_1-X_2}{2}.
 \tag{4.1}
\]

The physical map in this coordinate is the positive-order normalization
\(\widehat G(\xi)=\lambda_pG(\xi/\lambda_p)\), not the oppositely ordered
\(w=A_pz\) chart. The parent angles \(a,b\) are invariant under this
positive scaling. We use \(\pi_P(z)=m-r_P\cosh z\).

### 4.1 The circular segments for \(p=3,4\)

Take \(T=31/10\), \(h=83/100\) for \(p=3\), and \(h=88/100\) for \(p=4\).
Put

\[
 d=\frac{T^2-h^2}{2h},\quad L=\frac{T^2+h^2}{2h},\quad
 Q=\{\Re z>0,\ |z+d|<L\}.
 \tag{4.2}
\]

Then \(0<\Re z<h\), \(|\Im z|<T<\pi\). The physical certificates give
\(b<T\) and

\[
 |m|+r_P\cosh h<\rho_p.
 \tag{4.3}
\]

Hence \(\pi_P(Q)\) lies wholly in the physical target, because
\(|\cosh(s+it)|\le\cosh s\). This bound holds on the entire domain.

The Möbius map \(\psi(z)=(z-iT)/(z+iT)\) sends the straight diameter and
the circular boundary arc to two rays. On \(Q\) its argument runs between
\(-\pi\) and \(-\pi+\theta\), where
\(\theta=2\arctan(h/T)\). Thus \((-\psi)^\gamma\), with the branch
\(0<\arg(-\psi)<\theta\) and \(\gamma=\pi/\theta\), is a conformal
bijection to a half-plane. On \(it\), \(-T<t<T\), its boundary value is
\(\exp(-2\gamma\operatorname{atanh}(t/T))\). Writing

\[
 u=\gamma\operatorname{atanh}(a/T),\qquad
 v=\gamma\operatorname{atanh}(b/T),
\]

the four ordered positive boundary points are
\(e^{-2v},e^{-2u},e^{2u},e^{2v}\). Substitution in (2.2) gives

\[
 k=\frac{\sinh(v-u)}{\sinh(v+u)},\qquad
 W_{\rm seg}=\frac{K(k)}{K(\sqrt{1-k^2})}.
 \tag{4.4}
\]

### 4.2 The semidisks for \(5\le p\le12\) and \(p\ge13\)

Take \(R=7/5\) in the first range and \(R=5/2\) in the tail, and put
\(Q_R=\{\Re z>0,\ |z|<R\}\). In both cases \(b<R<\pi\).
The map

\[
 \chi_R(z)=\frac{2Rz}{R^2-z^2},\qquad
 \chi_R(it)=iB_R(t),\qquad B_R(t)=\frac{2Rt}{R^2+t^2}
 \tag{4.5}
\]

is a conformal bijection to the right half-plane. Indeed its real part is
\(2R\,\Re z\,(R^2-|z|^2)/|R^2-z^2|^2>0\); its derivative has no zero in
the open semidisk, and its two boundary arcs map to the imaginary axis,
with the only pole on the boundary at \(R\). Equivalently the two roots
of its inverse quadratic have product \(-R^2\), so at most one can be
inside the semidisk; the boundary degree is one. Lemma 2.1 gives

\[
 k_R=\frac{B_R(b)-B_R(a)}{B_R(b)+B_R(a)},\qquad
 W_R=\frac{K(k_R)}{K(\sqrt{1-k_R^2})}.
 \tag{4.6}
\]

For \(5\le p\le12\), the exact finite certificate proves (4.3) with
\(h=7/5\). For the tail, the corrected widest physical coordinate box
proves \(|m|<2\), \(0<r_P<2\). The elementary Taylor bound
\(e^{5/2}<13\) gives

\[
 |\pi_P(s+it)|<2+\frac22(13+1)=16
 <\frac3{20}2^{13}\le\lambda_pR_p
 \quad(0<s<5/2).
 \tag{4.7}
\]

The last inequality is the separate all-period physical chart bound
\(\lambda_p>(3/20)4^p\). Thus the entire projected tail semidisk, not a
finite sample of leaves, lies in every physical target.

### 4.3 The projected rectangle foliation is an A.1 Wave

Each domain above is simply connected and Jordan, with the two complete
electrodes \(i(-b,-a)\), \(i(a,b)\) on its straight boundary. Its SC map
to a rectangle pulls the open horizontal foliation back to simple disjoint
proper arcs. They have endpoints in the interiors of the two electrodes.
The whole domain has \(|\Im z|<T<\pi\) or \(|\Im z|<R<\pi\), so no two
points differ by \(2\pi in\) for nonzero \(n\). Consequently the exponential
is injective there. Joukowski is injective on the exterior of the unit
disk. Therefore the **entire** foliation projects as simple disjoint arcs
in the physical target.

A log leaf in this simply connected domain is homotopic relative to its
endpoints to the short diameter collar across \(t=0\). Such a collar also
exists in the actual physical domain, by NOTE, Lemma 2.1. Thus the
projected leaf is subordinate to \((I_9,I_0,I_1)\). The two endpoint atoms
are separated by \(I_0\), and Lemma 3.1 excludes every short class.
Every leaf has this same selected homotopy class. No proper sub-multi-
interval of this three-atom base contains both endpoint atoms. Thus the
minimal base is exactly \((I_9,I_0,I_1)\), the minimal ends are \(I_9,I_1\),
and their set difference is the closed crest \(\overline I_0\).

This proves an admissible A.1 Wave, with width exactly (4.4) or (4.6) by
the rectangle calculation. It follows that \(P_p\ge W_{\rm seg}\) or
\(P_p\ge W_R\), respectively. No optimizer or equality with \(P_p\) has
been presumed.

## 5. Both child suprema are positive, and their common full-path cap

The compact slit \([-r,r]\Subset V\) has a complete conformal collar.
Consequently \(D_C\) contains \(\{0<s<\epsilon\}\) for some \(\epsilon>0\).
Take the Jordan rectangle

\[
 Q_\epsilon=\{0<s<\epsilon/2,\ e_1<t<e_4\},
 \tag{5.1}
\]

with electrodes \(i(e_1,e_2)\), \(i(e_3,e_4)\). Its modulus is strictly
positive and finite: a Jordan quadrilateral with four distinct ordered
marked points is conformal to a nondegenerate finite rectangle.
Its open horizontal rectangle foliation pulls back to disjoint simple
arcs. Since \(e_4-e_1<\pi<2\pi\), their whole domain projects injectively.
The same collar homotopy and short-class argument gives exactly the base
\((S_1,S_2,S_3)\), ends \(S_1,S_3\), and closed crest \(\overline S_2\).
Thus \(C_p^+>0\).

Complex conjugation preserves \(G,U,V\), the slit, and conformal width,
and exchanges the upper and lower specified source bases. It sends every
competitor in either class to one in the other and is its own inverse.
Hence \(C_p^-=C_p^+>0\), not merely an equality of two formal expressions.

By Lemmas 2.1 and 3.2, the exact full-half-plane upper comparison is

\[
 C_p\le E_p=
 \frac{K(\sqrt{\kappa_c})}{K(\sqrt{1-\kappa_c})},\qquad
 \kappa_c=
 \frac{(b_c-a_c)(d_c-c_c)}
      {(c_c-a_c)(d_c-b_c)}.
 \tag{5.2}
\]

This bounds every actual child competitor. The parent full-lift metric
of §3 similarly bounds \(P_p\) by a finite number. Together with the
parent construction and (5.1), all three reciprocals in (1.2) exist.

For the tail it is useful to enlarge \(S_1\) from \((-h_0,\ell)\) to
\((-r,\ell)\), and \(S_3\) from \((a_0,-e)\) to \((a_0,b_0)\), on their
same respective accesses. The real order (1.1) proves these containments.
In the reflected angular coordinate their four endpoints are

\[
 0,\quad b_c=\arccos(-\ell/r),\quad
 c_c=\arccos(-a_0/r),\quad d_*=\arccos(-b_0/r).
 \tag{5.3}
\]

The true four-electrode family is a subset of this enlarged all-path
family. The SC width \(E_p^{\rm coarse}\) from (2.2)–(2.5) therefore gives
\(C_p\le E_p\le E_p^{\rm coarse}\). This bound requires no quantitative
tail estimate for the dividing fixed point \(e\).

## 6. Strict removal of actual source energy for \(3\le p\le12\)

The physical source bound used here is proved independently of the parent
embedding. The finite coefficients satisfy

\[
 G(z)=r+A_pz^2+E(z),\qquad
 |A_p|R_p^2>|r|+\sup_{|z|\le R_p}|E(z)|+R_p.
 \tag{6.1}
\]

Thus \(|G(z)|>R_p\) on \(|z|=R_p\), and the central preimage component
containing 0 is compactly inside \(D(0,R_p)\). This is the strict Rouché
barrier used in NOTE, Lemma 1.1. It is not an inference from the parent
quadrilateral.

For the child SC derivative in (2.3), with prevertices \(e_1,\ldots,e_4\),
the exact gap side can also be bounded without evaluating an elliptic
integral:

\[
\begin{split}
 H&=\int_{e_2}^{e_3}
 \frac{dt}{\sqrt{(t-e_1)(t-e_2)(e_3-t)(e_4-t)}}\\
 &\le \frac{\pi}
 {\sqrt{(e_2-e_1)(e_4-e_3)}}
 =\frac{\pi}{\sqrt{(d_c-c_c)(b_c-a_c)}}.
\end{split}
 \tag{6.2}
\]

The inequality follows by bounding the two outside factors from below
and using the beta integral for the remaining two factors.

Choose a positive integer \(s_p\) for which \(r\sinh(s_p)>R_p\).
The finite checker establishes this by the strict rational inequality

\[
 r_{\rm low}\left(
 \frac12\sum_{n=0}^{24}\frac{s_p^n}{n!}-\frac12\right)>R_p.
 \tag{6.3}
\]

It implies the desired inequality because \(e^{s_p}\) exceeds its
positive Taylor partial sum and \(e^{-s_p}<1\). The certified choices for
\(p=3,\ldots,12\) are respectively

\[
        (s_p)=(2,2,2,3,4,4,5,6,6,7).
 \tag{6.4}
\]

On the open unit box
\(B_p=\{s_p<s<s_p+1,\ 0<t<1\}\),

\[
 |\pi_C(s+it)|=r|\cosh(s+it)|
       \ge r\sinh s>R_p.
 \tag{6.5}
\]

Consequently \(B_p\) and all of its deck translates are outside the
entire physical source lift \(D_C\). For every \(z\in B_p\), all
\(0<e_j<\pi<4\), so
\[
 |z-ie_j|<s_p+5,\qquad |F'(z)|^2>(s_p+5)^{-4}.
\]
Combining this with (6.2) and the unit area of \(B_p\) gives

\[
 \int_{B_p}\widetilde\rho^2\,dA>
 \frac{(b_c-a_c)(d_c-c_c)}{16(s_p+5)^4}.
 \tag{6.6}
\]

Each finite physical root packet gives
\((b_c-a_c)(d_c-c_c)>9/100\). Since \(s_p\le7\), this is greater than
\(9/(100\cdot16\cdot12^4)>1/5{,}000{,}000\).
The exact area identity (3.2), rather than a slogan about strict domain
monotonicity, now yields

\[
 C_p\le E_p-\frac1{5{,}000{,}000}<E_p
 \qquad(3\le p\le12).
 \tag{6.7}
\]

One omitted box has been counted once upstairs. The periodized physical
metric retains the selected lifted density along every physical leaf:
restricting its domain cannot alter that leaf's length because the leaf
was already inside the domain. Conjugation gives exactly the same bound
for the reflected child. For any other finite \(p\), boundedness of \(V\)
also supplies some omitted box, but no uniform tail saving is needed
in (1.3).

## 7. The quantitative inputs, with the infinite-tail error repaired

### 7.1 Finite periods

The ten parameter packets are read as untrusted dyadic brackets. The
checker re-establishes the polynomial endpoint signs, a signed derivative
on the whole parameter interval, the real cut orders, the fixed-point
branch, and the strict complex Rouché barrier. Positive scaling, angles,
the full-domain gate (4.3), the SC expressions and (6.3)–(6.7) are then
evaluated with exact rationals and outward \(2^{-512}\) intervals.

The transcendental primitives use alternating arctangent remainders,
the positive atanh/log and sinh series with geometric tails, and

\[
 \frac{2K(\sqrt m)}{\pi}
 =\sum_{n=0}^{\infty}
   \left(\frac{\binom{2n}{n}}{4^n}\right)^2m^n.
 \tag{7.1}
\]

The omitted elliptic sum is bounded above by \(q^N/(1-q)\) when
\(m\le q<1\), since its coefficients are at most one. Thus the intervals
certify strict rational premises; no floating point comparison decides a
sign. The formulas and normalization have already been proved above.

| Periods | Embedded parent lower bound | Actual child upper bound | Rational defect lower bound |
|---|---:|---:|---:|
| \(p=3\) | \(49/100\) | \(487/500\) | \(300/23863>1/100\) |
| \(p=4\) | \(511/1000\) | \(197/200\) | \(7400/100667>7/100\) |
| \(5\le p\le12\) | \(581/1000\) | \(247/250\) | \(43500/143507>3/10\) |

The child bounds are on the independent suprema by §3 and §6, while the
parent bounds come from actual embedded Waves by §4. Taking reciprocals
therefore gives precisely the displayed lower bounds for
\(2/C_p-1/P_p\).

### 7.2 Every period \(p\ge13\), with no extrapolation

Let \(u_j=(w\mapsto w^2+\tau_*)^j(0)\) for the distinguished limiting
root and \(q=4^{-p}\). The established physical chart inputs are

\[
 |X_1+u_1|\le15246q,\qquad
 |X_j+u_j|
 \le\left(30\cdot15246+
          88\sum_{i=0}^{j-1}4^i\right)q
 \quad(j=2,3,5).
 \tag{7.2}
\]

Their two sources must be added: the parameter displacement contributes
\(30\cdot15246q\); the dynamical perturbation recurrence
\(\varepsilon_{j+1}=4\varepsilon_j+88q\), \(\varepsilon_0=0\),
contributes \(88(4^j-1)q/3\). The erroneous former coefficient was smaller
by \(20\cdot15246=304920\), before multiplication by \(q\).

All periods lie in the single widest \(p=13\) interval box; its errors
shrink monotonically with \(p\). On the **correct** box, direct outward
evaluation gives

\[
 \frac{658663060}{10^9}<W_{5/2}<
 \frac{749148532}{10^9},\qquad
 \frac{1155037409}{10^9}<E_p^{\rm coarse}\text{ (box value) }<
 \frac{1253261059}{10^9}.
 \tag{7.3}
\]

The second interval encloses the coarse expression evaluated over the
whole physical box; it is not a lower bound on the actual \(C_p\).
The first likewise encloses the explicit parent competitor, not its
unrestricted supremum. In particular
\(W_{5/2}>13/20\) and \(E_p^{\rm coarse}<63/50\).
The whole-domain and deck gates remain valid on this wider corrected box
by (4.7). We obtain

\[
 D_p>\frac2{63/50}-\frac1{13/20}
      =\frac{100}{63}-\frac{20}{13}
      =\frac{40}{819}>\frac1{100}.
 \tag{7.4}
\]

This is one interval theorem for every \(p\ge13\), not sampling of that
tail or continuity of optimizers. The faulty coefficient has been fixed
in the original limiting checker and a regression reconstructs both
terms of (7.2) independently. The limiting \(p=\infty\) numerical
enclosures and the finite-period rows are unaffected.

The stronger \(P_p>2/3\), \(D_p>11/126\) conclusion also remains available
through the distinct corrected route: exact isolation at \(p=13\), then
uniform bounds for \(p\ge14\). Its verifier is
[`verify_all_periods.py`](../tip_family_wave_gain_correction_20261123/verify_all_periods.py).
This does not assert that the single widest box in (7.3) proves that floor.

## 8. Scope and reproducibility

The proof above discharges the named **local H3** comparison from the
explicit actual-slit physical package and the companion intrinsic ideal
atlas and covering marking. It does not consume the open full immersion
MARK/H2 claim or identify independent children with restrictions of every
parent. It does not discharge global H1–H4 in the MLC closure proposition,
prove an all-parameter ideal atlas, or remove the upstream physical
chart hypotheses by passing a test.

The gain compares three independently optimized unbuffered A.1 suprema.
It neither constructs simultaneous parent/child optimizers nor asserts
that every parent can be restricted to both children. For a single
leafwise pairable family, one must additionally exhibit for every leaf
both surviving children in the specified classes and injectivity of the
immersion on their union. Under those conditions KKL Lemma A.11 gives
\(P_{\rm pair}\le C_p/2\); the corresponding reciprocal defect is
nonpositive. The present result instead implies
\(P_p>C_p/2\ge P_{\rm pair}\). There is no contradiction and no iterated
KKL amplification theorem. Buffered canonical WAD weights and the
four-hole peripheral comparison belong to local H4 and are not proved
by this argument. The separate [matched outer-buffer proof](OUTER_BUFFER_EXCLUSION.md)
now supplies that selected peripheral comparison and zero outer
coefficients for \(p\ge11\), while leaving inner coefficients and
amplification undetermined.

Run the new arithmetic record and the corrected targeted regressions:

~~~sh
python3 -B research/independent_audits/maximal_native_wave_20261123/verify_width.py
python3 -B -m unittest discover -s research/independent_audits/tip_family_limiting_wave_gain_20261116 -p 'test_*.py' -v
python3 -B -m unittest discover -s research/independent_audits/tip_family_finite_p_wave_gain_20261116 -p 'test_*.py' -v
python3 -B -m unittest discover -s research/independent_audits/tip_family_hypothesis_M_discharge_20261116 -p 'test_*.py' -v
~~~

The checker records exact arithmetic implications and catches the former
coefficient error. The SC theorem, all-path lifting, complete projected
foliation, and omitted-energy interpretation are the written mathematics
above. They are not converted into formal theorems by successful execution.
