# All-period realization lemma for the near-\(-2\) real primitive-tip family

**2026-11-16. New theorem, with an explicitly bounded parameter chart; independent of the Native Wave Transfer regenerators.** This note closes the *existence, strict real-order and proper quadratic-like* realization gap for the distinguished family for **every integer \(p\ge13\)**. Together with the separately merged exact certificates for \(3\le p\le12\), this makes the real/holomorphic **realization input** of the finite family theorem available for every \(p\ge3\). It does **not** reprove KKL/prime-end identification, establish a canonical Wave, or assert uniqueness in an unspecified *maximal* real component. The exact parameter chart and the sense of uniqueness are stated next, rather than inferred from the equation alone.

## Statement and precise scope

Write \(f_c(z)=z^2+c\), \(x_j(c)=f_c^j(0)\), \(G_c=f_c^p\), and
\[
 q=4^{-p},\qquad d(c)=x_p(c),\qquad
 A(c)=\prod_{j=1}^{p-1}2x_j(c),\qquad \tau(c)=A(c)d(c).
\]
For each \(p\ge13\) use the **explicit near-\(-2\) primitive chart**
\[
 {\cal C}_p=\{c=-2+\varepsilon:\;14q<\varepsilon<16q,\ |d(c)|<14q,\ -2<\tau(c)<1/4\}.
 \tag{C}
\]
The designated **kneading window** \({\cal K}_p\subset {\cal C}_p\) is the subset with the prefix \(x_1<0\), \(x_j>0\) for \(2\le j\le p\), and signed \(G\)-returns \((x_p,x_{2p},x_{3p},x_{4p},x_{5p},x_{6p})\) of signs \(+--+-+\). This is a non-circular specification using only inequalities on a *parameter interval*: \(P_p(c)=0\) is **not** part of the definition. The chart is the near-\(-2\), first-return, rescaled central primitive copy; no assertion is made that (C) is the entire maximal real primitive window.

**Theorem (all large periods, explicit constants).** For **every** integer \(p\ge13\):

1. \(P_p(c):=x_{6p}(c)+x_{3p}(c)\) has **exactly one** zero \(c_p\) in \({\cal K}_p\). The zero is simple, and \({\cal K}_p\) contains an explicit connected subwindow \(-1795/1000<\tau(c)<-1785/1000\) on which \(P_p\) has this unique root. Its parameter has the rigorous semiconjugacy asymptotic
   \[
   \boxed{\left|c_p+2-\frac{3\pi^2}{2}4^{-p}\right|<500p\,16^{-p}.}\tag{A}
   \]
   Thus \(c_p\to-2\) and \(c_p+2\sim (3\pi^2/2)4^{-p}\). Uniqueness here is throughout the precisely defined signed chart \({\cal K}_p\), **not** across the whole real line or an unspecified larger component. In particular the period-\(p\) center \(x_p=0\), other solutions of \(P_p=0\), and the period-three center \(x_{3p}=0\) are excluded by strict signs.
2. The positive fixed point \(\alpha=\alpha_p\) of \(G\) in \((x_{6p},x_{4p})\) is unique, and the **strict** real order is
   \[
   x_{2p}<x_{5p}<x_{3p}<0<x_{6p}<\alpha<x_{4p}<x_p,
   \tag{O1}
   \]
   \[
   -x_p<-x_{4p}<x_{2p}<x_{5p}<-\alpha<x_{3p}<x_{6p}<\alpha<-x_{5p}<-x_{2p}<x_{4p}<x_p.
   \tag{O2}
   \]
   On \([-x_p,x_p]\), \(G\) is strictly increasing to the left of zero and decreasing to its right; there is no earlier critical return to the central small interval.
3. With \(R_p=2^{-p}\), \(U_p=D(0,R_p)\), and \(V_p\) the component containing zero of \(G^{-1}(U_p)\),
   \[
      V_p\Subset U_p,\qquad G:V_p\longrightarrow U_p
   \]
   is a **proper holomorphic map of degree exactly two**. Its Rouché dominance margin on \(|z|=R_p\), uniform in \(p\ge13\), obeys
   \[
      |A_p|R_p^2-|x_p|-T_p-R_p
      \;\ge\;\frac3{20}-12\,4^{-p}-\frac1{128}-2^{-p}
      \;>\;\frac1{25},\tag{R}
   \]
   where \(T_p\le1/128\) bounds the complete nonlinear remainder, not only a truncated Taylor series.

The parameter signs, cut inequalities and Rouché estimates in this theorem are unconditional claims about \(f_c\); the identification of the marked real slit with *the entire* KKL ideal circles, prime-end accesses, complete little Julia trees and actual analytic extremal widths remains under the **same explicitly cited interpretation hypotheses** as in the prior finite-family theorem.

## Proof, I: the Chebyshev phase and an explicit escape-time estimate

Everything in this proof uses rational inequalities, the elementary bounds \(157/50<\pi<22/7\), \(1-\theta^2/2\le\cos\theta\le1-\theta^2/2+\theta^4/24\), \(\sin\theta\ge2\theta/\pi\) on \([0,\pi/2]\), and standard Rouché/Cauchy/Schwarz theorems. The verifier checks the numerical boundary constants *exactly* at \(p=13\); \(p4^{-p}\) and \(p^24^{-p}\) decrease for integers \(p\ge13\). It also proves a rational enclosure of \(\pi\) using Machin's identity and alternating arctangent series. No floating-point estimate is used in the argument.

Fix \(p\ge13\), \(q=4^{-p}\), and \(14q\le\varepsilon\le16q\). The positive repelling fixed point of \(f_c\) is
\[
 \beta=\frac{1+\sqrt{9-4\varepsilon}}2,
 \quad \lambda=2\beta=4-\delta,
 \quad\delta=\frac{4\varepsilon}{3+\sqrt{9-4\varepsilon}}\in(0,\varepsilon).
\]
Put \(y_j=\beta-x_j\). Starting at \(j=2\), the *exact* recurrence is
\[
 y_{j+1}=\lambda y_j-y_j^2,\quad
 y_2=\frac83\varepsilon-\varepsilon^2
      -\frac{4\varepsilon^2}{3(3+\sqrt{9-4\varepsilon})^2},
 \quad \frac83\varepsilon-2\varepsilon^2<y_2<\frac83\varepsilon.
 \tag{1}
\]
Set \(y_j=2(1-\cos\theta_j)\), with \(\theta_j\ge0\), and set \(\Theta=2^{p-2}\theta_2\), \(\kappa=\varepsilon/q\). At \(\varepsilon=0\), \(y\mapsto4y-y^2\) is exactly the Chebyshev doubling semiconjugacy \(z=2\cos\theta\), \(\theta\mapsto2\theta\). Directly from (1), \(y=2(1-\cos\theta)\), and the alternating cosine series,
\[
 \frac\kappa6(1-\varepsilon)<\Theta^2<\frac\kappa6(1+3\varepsilon),
 \qquad \frac{38}{25}<\Theta<\frac{41}{25},
 \qquad \theta_j<\frac{41}{50}\quad(2\le j<p).\tag{2}
\]
For \(j<p\), \(\lambda-y_j>3\). Hence \(\theta_{j+1}\ge\theta_j\), while the Chebyshev map gives \(\theta_{j+1}\le2\theta_j\). Using \(y_{j+1}=(4y_j-y_j^2)-\delta y_j\), the mean-value derivative \(d\theta/dy=(2\sin\theta)^{-1}\), \(y_j\le\theta_j^2\), \(\sin(2\theta_j)\ge\sin\theta_j\), and \(\pi<4\), one gets the *explicit perturbation inequality*
\[
 (2-\varepsilon)\theta_j\le\theta_{j+1}\le2\theta_j.
 \tag{3}
\]
The angle interval in (2) makes all inverses and sines in this argument single-valued; in particular this is **not** a comparison through the cosine turning point. Iterating (3) and (2) yields
\[
 |\theta_p-\sqrt{\kappa/6}|\le(p+6)\varepsilon,
 \qquad |x_p-2\cos\sqrt{\kappa/6}|\le3p\varepsilon.
 \tag{4}
\]
Indeed \(\beta-2\in(-\varepsilon/2,0)\), and \(2(p+6)+1/2\le3p\) for \(p\ge13\). With \(\sqrt{14/6}<77/50\), \(\sqrt{16/6}>81/50\), \(\pi/2\in(157/100,11/7)\), and \(\sin t\ge t-t^3/6\) for the small endpoint gaps, (4) gives the **strict** bounds
\[
 x_p(-2+14q)>1/20,
 \qquad x_p(-2+16q)<-1/20.\tag{5}
\]
The orbit has \(x_1<0\), \(13/10<x_j<2\) for \(2\le j<p\) throughout this entire \(\varepsilon\)-interval, not merely at the eventual root.

We also need **transversality** rather than endpoint signs alone. Differentiation with respect to \(\varepsilon\) gives \(Y_j=dy_j/d\varepsilon\), \(Y_2=3-2\varepsilon-1/\sqrt{9-4\varepsilon}\), \(\lambda'=-2/\sqrt{9-4\varepsilon}\), and
\[
 Y_{j+1}=(\lambda-2y_j)Y_j+\lambda'y_j.
\]
Set \(r_j=\varepsilon Y_j/y_j\). The exact ratio recurrence is
\[
 r_{j+1}=\left(1-\frac{y_j}{\lambda-y_j}\right)r_j
        +\frac{\varepsilon\lambda'}{\lambda-y_j}.
 \tag{6}
\]
Here \(r_2>99/100\), \(0<y_j<7/10\) for \(2\le j<p\), successive \(y_j\) grow by a factor greater than 3, \(\sum_{j=2}^{p-1}y_j<21/20\), and \(\sum y_j/(\lambda-y_j)<7/20\). The product inequality \(\prod(1-a_j)\ge1-\sum a_j\), \(|\lambda'|<1\), and \(p\varepsilon<1/300000\) give \(r_p>1/2\). As \(\theta_p>3/2\), \(y_p>9/5\), so
\[
 \frac{dx_p}{dc}=\beta'-Y_p<-\frac{1}{20q}.
 \tag{7}
\]
Thus every prescribed \(|d|\le14q\) has a **unique** parameter in \((-2+14q,-2+16q)\). At any such parameter with \(|d|\le12q\), (4) and \(\kappa_*=3\pi^2/2\) give (A): \(|2\cos\sqrt{\kappa/6}|\le12q+48pq\), and the derivative of \(2\cos\sqrt{\kappa/6}\) has absolute value \(\sin(\sqrt{\kappa/6})/(6\sqrt{\kappa/6})>1/10\) on \([14,16]\). Therefore \(|\kappa-\kappa_*|<120q+480pq\le500pq\).

## Proof, II: the normalized first-return coefficient and a global two-variable remainder

Write \(f_c^j(z)=d_j+a_jz^2+E_j(z)\), \(d_j=x_j\), \(a_1=1\), \(a_{j+1}=2d_ja_j\). The angle bound above implies \(a_p=A<0\). Put \(\Theta_j=2^{j-2}\theta_2\). Since \(0\le\Theta_j-\theta_j\le(p\varepsilon/2)\Theta_j\) for \(2\le j<p\), one has
\[
 1-\varepsilon\ \le\ \frac{2x_j}{4\cos\Theta_j}\ \le\ 1+p\varepsilon
 \quad (2\le j<p).\tag{8}
\]
Here \(\cos\Theta_j>33/50\), \(\theta_j\le\Theta_j<41/50\), and \(|\beta-2|<\varepsilon/2\); the right inequality follows from the cosine Lipschitz bound, and the left follows from \(\cos\theta_j\ge\cos\Theta_j\). Use the exact doubling identity
\[
 \prod_{j=2}^{p-1}\cos\Theta_j
   =\frac{\sin\Theta}{2^{p-2}\sin\theta_2}.
\]
Together with \(\sin\Theta>99/100\), \(38/25<\Theta<41/25\), \(1\le\theta_2/\sin\theta_2\le1+3\varepsilon\), \((1-\varepsilon)^{p-2}\ge1-p\varepsilon\), and \((1+p\varepsilon)^{p-2}\le1+2p^2\varepsilon\), this yields
\[
 \boxed{\frac3{20}<-Aq<\frac{17}{100}}.\tag{9}
\]
All the strict boundary inequalities are checked with exact fractions in the verifier at \(p=13\).

Differentiating \(d_{j+1}=d_j^2+c\) and \(a_{j+1}=2d_ja_j\), using \(|d_j|<2\) for \(j<p\), gives the explicit simple bounds
\[
 |d_j'|\le\frac{4^j}{3},\qquad |a_j|\le4^{j-1},\qquad
 |a_j'|\le\frac{16^{j-1}}3\quad(1\le j\le p).
 \tag{10}
\]
Consequently \(\tau'=A'd+Ad'>7/(1000q^2)>0\) whenever \(|d|\le14q\): from (7) and (9), \(Ad'>3/(400q^2)\) while \(|A'd|\le14/(48q)\). At \(d=14q\) one has \(\tau<-21/10\), and at \(d=-14q\) one has \(\tau>21/10\). Thus \(\tau\) traverses \([-2,1/4]\) exactly once, with a unique parameter for each \(\tau\) in that interval. In particular \(\tau\in[-1795/1000,-1785/1000]\) implies \(0<d<12q\).

For any radius \(r\), let \(s=r^2\), \(t_j=4^js\). Whenever \(t_p\le1\), the exact squaring recurrence and \(|d_j|\le2\) give, on the **whole complex disk** \(|z|\le r\),
\[
 |E_j(z)|\le T_j,\quad
 T_{j+1}=2|d_j|T_j+(|a_j|s+T_j)^2,
 \qquad T_j\le t_j^2/128.\tag{11}
\]
For the induction, \(T_1=0,T_2=s^2\le t_2^2/128\), and for \(j<p\), \(t_j\le1/4\) and
\[
 \frac4{128}+\left(\frac14+\frac1{512}\right)^2
   <\frac{16}{128}.
\]
There is **no discarded higher-order term**. Differentiating the complete \(E_j\)-recurrence in \(c\), (10) and the strict numerical inequality
\[
 \frac{2}{3\cdot128}+\frac4{128}
  +2\left(\frac14+\frac1{512}\right)
    \left(\frac1{48}+\frac1{512}\right)<\frac{64}{128}
\]
likewise give \(|\partial_cE_j(z)|\le4^jt_j^2/128\) at fixed \(z\).

Apply these estimates to \(r=16q\) (so \(t_p=256q<1\)). Then
\[
 |E_p(z)|\le512q^2,\qquad |\partial_cE_p(z)|\le512q\quad(|z|\le16q).
 \tag{12}
\]
Cauchy's estimate on the smaller \(|z|\le14q\) gives \(|\partial_zE_p(z)|\le256q\), improving to \(171q\) on \(|z|\le13q\). Define the **exact** normalized holomorphic map and parameter
\[
 h_\tau(w)=A\,G_c(w/A)=w^2+\tau+e_\tau(w),
 \qquad e_\tau(w)=A E_p(w/A).\tag{13}
\]
For every real parameter with \(|d|\le14q\), \(-2\le\tau\le1/4\), and \(|w|\le21/10\), the estimates above give
\[
 |e_\tau(w)|<88q,\quad
 |\partial_we_\tau(w)|\le256q,\quad
 |\partial_\tau e_\tau(w)|<30000q^2.
 \tag{14}
\]
For the last inequality, \(|A'|\le(48q^2)^{-1}\), \(|A|\in(3/(20q),17/(100q))\), \(|\partial_c(w/A)|<2\) and (12) yield \(|\partial_c e|<200\); divide by \(\tau'>7/(1000q^2)\). On \(|w|\le19/10\), the sharper bound \(|\partial_we|\le171q\) applies. These are **complex-disk** error estimates for the full iterate \(f_c^p\), not numerical comparisons of individual real points.

## Proof, III: the one-root quadratic model and the whole signed chart

Let \(g_\tau(w)=w^2+\tau\) and \(u_k(\tau)=g_\tau^k(0)\). On
\[
 J=[-1795/1000,-1785/1000],
\]
exact rational interval evaluation of the six iterates and their derivatives gives
\[
 u_6(-1795/1000)+u_3(-1795/1000)<-1/20,\qquad
 u_6(-1785/1000)+u_3(-1785/1000)>1/20,
 \tag{15}
\]
\[
 \frac{d}{d\tau}(u_6+u_3)>2,
 \quad |u_k|<9/5\ (0\le k\le6),
 \quad |u_k'|<25\ (0\le k\le5).\tag{16}
\]
As \(|h_\tau^k(0)|<19/10\), define the rigorous error envelopes (all arithmetic is rational)
\[
 E_0=D_0=0,\quad
 E_{k+1}=4E_k+88q,
 \quad D_{k+1}=4D_k+25(2E_k+171q)+30000q^2.\tag{17}
\]
The induction comparing (13) with \(g_\tau\) bounds the orbit error by \(E_k\) and the \(\tau\)-derivative error by \(D_k\), including the dependence of \(c,A\) on \(\tau\). At the worst case \(p=13\), **exact rational verification** yields
\[
 E_6+E_3<1/500,
 \qquad D_6+D_3<1/5.
 \tag{18}
\]
Hence \(h_\tau^6(0)+h_\tau^3(0)\) has opposite signs at the endpoints of \(J\) and **strictly positive derivative throughout \(J\)**. The intermediate value theorem gives exactly one \(\tau_*\in J\), hence exactly one \(c_p\) there, with \(P_p(c_p)=0\). The derivative in \(c\) at that root is nonzero, since \(\tau'>0\), \(A<0\), and \(P_p=(h^6(0)+h^3(0))/A\).

For uniqueness in the **entire specified signed chart** \({\cal K}_p\), not just \(J\), the exact invariant real interval of \(g_\tau\) for \(-2\le\tau\le0\) bounds \(|u_k|\le2\) through six iterates. The comparison \(E_{k+1}^{\rm wide}=(21/5)E_k^{\rm wide}+88q\) gives \(E_6^{\rm wide}+E_3^{\rm wide}<1/400\) for \(p\ge13\), while the perturbed orbit stays in \(|w|<21/10\). The verifier **exhaustively** covers the following six closed *non-root* segments by 1000 rational subintervals apiece, proving \(|u_6+u_3|>1/400\) on every subinterval (in the interval sense):

| Non-root segments of \(\tau\) | Other small neighborhoods |
| --- | --- |
| \([-2,-1.989]\), \([-1.988,-1.982]\), \([-1.980,-1.894]\) | \([-1.989,-1.988]\), \([-1.982,-1.980]\), \([-1.894,-1.892]\) |
| \([-1.892,-1.795]\), \([-1.785,-1.756]\), \([-1.753,-0.01]\) | \(J\), \([-1.756,-1.753]\), \([-0.01,0]\) |

In the first three other neighborhoods the *true* normalized orbit respectively has \(h^4(0)>0\), \(h^5(0)<0\), and \(h^5(0)<0\), contradicting the required normalized return signs \(-++-+-\). In \([-1.756,-1.753]\), let \(v=h^3(0)\); the interval model gives \(|v|<1/40\). On the segment from \(0\) to \(v\), the full derivative satisfies
\[
 |(h^3)'(w)|\le(1/20+256q)(18/5+256q)(3+256q)<1.
\]
The *exact* identity
\[
 h^6(0)+h^3(0)=v\left(2+\int_0^1(h^3)'(sv)\,ds\right)
\]
forces \(v=0\) at any zero, contradicting **strict** \(x_{3p}<0\). Finally, for \(-0.01<\tau<0\), Schwarz's order-four estimate from (12), \(E_p(z)=O(z^4)\), gives
\[
 |e_\tau(\tau)|\le88q\left(\frac5{12}|\tau|\right)^4<|\tau|/100;
\]
therefore \(h^2(0)=h(\tau)=\tau(1+\tau)+e_\tau(\tau)<0\), incompatible with \(x_{2p}<0\). For \(\tau\ge0\), \(x_p\le0\) already contradicts the chosen signs. Thus **no other zero with the specified kneading signs exists in (C)**. The distinct other polynomial roots have actually been excluded, not mistaken for the designated tip.

At the unique root, \(h^6(0)=-h^3(0)\) exactly. The rational model intervals and the errors \(E_k\) prove the twelve strict inequalities in the **reverse** order
\[
 -w_1>-w_4>w_2>w_5>-w_\alpha>w_3>-w_3>w_\alpha>-w_5>-w_2>w_4>w_1,
 \tag{19}
\]
where \(w_j=h^j(0)=A x_{jp}\). Here \(w_\alpha\in(-1,-4/5)\) is the unique fixed point of \(h\) in that interval: \(h(-1)+1>0\), \(h(-4/5)+4/5<0\), and \(h'(w)<0\) there. In fact the exact rational cut bounds put the **whole** interval \([w_4,-w_3]\) inside \([-9/5,-1/10]\); \(h'(w)=2w+\partial_we_\tau(w)<0\) throughout this interval because \(|\partial_we_\tau|<171q\). Hence this is also the **only** fixed point between the prescribed \(x_{6p}\) and \(x_{4p}\), not merely the only fixed point in a chosen smaller interval. Because \(A<0\), (19) is precisely (O2), and (O1) follows. Equation (4) gives the positive intermediate orbit; (11) with \(r=16q\) bounds the perturbation of every \(f^j(z)\) for \(|z|\le x_p<12q\), keeping \(f_c(z)<0\) and \(f_c^j(z)>0\) for \(2\le j<p\). This proves the stated strict two-sheeted monotonicity. The image \(G([-x_p,x_p])=[x_{2p},x_p]\subset U_p\) is connected to zero, hence this real pullback lies in the central component \(V_p\).

## Proof, IV: uniform Rouché and properness

For \(r=R_p=2^{-p}\), \(s=r^2=q\), so \(t_p=4^ps=1\) in (11). The full complex disk estimate gives \(T_p\le1/128\), and (9), \(|d|<12q\), and \(R_p\le2^{-13}\) imply the strict uniform inequality (R). For every \(w\in\overline{U_p}\), on \(|z|=R_p\),
\[
 |G(z)-w-Az^2|\le|d|+T_p+R_p<|A|R_p^2.
\]
Rouché therefore counts **exactly two zeros with multiplicity** of \(G(z)-w\) inside \(U_p\), with no zeros on its boundary. Because \(G(0)=d\in U_p\) and zero has local degree two, both solutions near \(w=d\) belong to the central component. Properness and continuation force the full degree-two cover \(V_p\to U_p\). As no boundary of the preimage component meets \(\partial U_p\), \(V_p\Subset U_p\). This is a proof for every \(p\ge13\), **not** an extrapolation from finitely many Rouché numbers.

## Reproducibility, audit checks, and limits

Run from the repository root:

```sh
python research/independent_audits/real_primitive_tip_family_all_p_20261116/verify.py
python -m unittest discover -s research/independent_audits/real_primitive_tip_family_all_p_20261116 -p 'test_*.py' -v
```

The standard-library-only verifier uses `Fraction` for every fixed universal inequality (including a rational Machin enclosure of \(\pi\)), exact interval evaluation of the quadratic model on the **entire** root interval and **6000** rational exclusion subintervals, and an independent outward-rounded \(2^{-512}\) interval check of an **adjacent \(2^{-256}\) bracket** for the actual \(p=13\) parameter. That last bracket is
\[
 \frac{-231584152930559666515303967650834348256481862329075540046349754537259200892081}{2^{256}}
 < c_{13} <
 \frac{-231584152930559666515303967650834348256481862329075540046349754537259200892080}{2^{256}}.
\]
Both endpoint signs, the strictly negative full-hull derivative and the negative \(x_{39}\) are rechecked from iteration; **the decimal seed is not a premise**. Adversarial tests detect the neighboring wrong-kneading polynomial root and a shifted \(p=13\) bracket. The CI workflow additionally re-runs both previously merged audits and the existing research-validation and Lean regression commands. The universal proof is ordinary analysis with exact rational boundary checks; **it is not a Lean formalization of Rouché or all-period real dynamics**.

**Combined theorem and exact remaining debt.** The merged [`uniform`](../real_primitive_tip_family_uniform_20261116/NOTE.md) and [`unconditional`](../real_primitive_tip_family_unconditional_20261116/NOTE.md) audits independently certify the finite realization conditions for each \(p=3,\dots,12\); the theorem above provides them for **every \(p\ge13\)**. Therefore the earlier **period-uniform finite real/marked family implication can now be applied with unconditional *existence, strict cuts, and proper degree-two quadratic-like realization* for every \(p\ge3\)**. The discrete covering/immersion labels, real-edge matrix and closed-crest type implication remain as stated in that theorem, **under its cited prime-end/KKL marking identification**. No new assumption of realization of \(c_p\) is needed.

Still **not** established here are: identification of the *maximal* primitive parameter component or uniqueness across any parameter region wider than the explicitly defined near-\(-2\) chart (C); complete complex Julia/Hubbard-tree and prime-end/ideal-circle identifications beyond the cited slit/KKL interpretation inputs; uniform physical admissibility of the optional orbit-centred radial **Wave** and its KKL extremal-width identification for all \(p\); a canonical period-only width, strict Wave gain, closed-crest subsector domination, or MLC. In particular, the old correction that an avoiding source path has **seven**, not three, short-arc atoms remains in force. No existing source file or prior certificate is modified.

References: the two merged audit notes above; the cited source-locked `research/native_wave_transfer/SPECIFICATION.md`, `RESULTS.md`, and physical examples; and Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/abs/2606.27272v1), §§2.1, 2.5, 6.1 (Propositions 6.5–6.6), Appendix A.1 and A.3.2–A.3.4. The latter supply interpretive/analytic inputs and are **not** proved by this note.