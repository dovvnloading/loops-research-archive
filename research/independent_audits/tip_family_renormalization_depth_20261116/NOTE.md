# Primitive-tip renormalization at depth two: nine exact certificates and the depth obstruction

**2026-11-16.** Additive research audit. No previously merged verifier,
manifest, source, or theorem file is changed. The finite conclusions below
are **exact** consequences of rational interval arithmetic plus explicitly
identified classical analytic and dynamical theorems. The actual
straightening, tuning, KKL topological identification, and conformal-width
monotonicity are **mathematical theorem imports**, not Python or Lean proofs.
The convergence of optimal Waves with renormalization depth remains **open**.

## 0. A necessary distinction: the outer tip is a *copy*, not a tip identity

Let \(F_c(z)=z^2+c\), \(x_j(c)=F_c^j(0)\), and
\(P_n(c)=x_{6n}(c)+x_{3n}(c)\). The existing selected single-level
parameter \(c_p\) solves \(P_p(c_p)=0\) and is strictly preperiodic
for \(F_{c_p}^p\). **It is impossible** to impose that equality again
at periods \(p_1\) and \(p_1p_2\) with the *same* \(c\) and
\(p_2\ge3\) while asking for a genuine period-\(p_2\) inner tip:
the outer tip has already become fixed after its three-return
postcritical portrait, rather than having an independent inner tip.

The mathematically consistent interpretation of **tuning the
\(p_2\)-tip into the \(p_1\)-copy** is: the first return
\(G_1=F_c^{p_1}\) is a primitive quadratic-like restriction, with
straightening the *distinct* polynomial \(F_{c_{p_2}}\); its
\(p_2\)-th iterate \(G_2=F_c^{n}\), \(n=p_1p_2\), is the actual
near-\(-2\) primitive tip, satisfying \(P_n(c)=0\). The first
return need not satisfy \(P_{p_1}(c)=0\). We use that meaning
throughout, and call the parameter \(c(p_1,p_2)\). Both returns
are degree **two** on their own nested central polynomial-like domains;
this does **not** say the unrestricted polynomial \(F_c^{n}\) has
algebraic degree two.

## 1. Exactly specified charts and finite theorem

For \(p_1,p_2\in\{3,4,5\}\), set \(n=p_1p_2\),
\(A_j=[z^2]F_c^j=\prod_{r=1}^{j-1}2x_r\), and let \(s_{p_1,p_2}\)
be the following **rational** decimals. The explicit *open* chart is
\(\mathcal C_{p_1,p_2}=(s-10^{-80},s+10^{-80})\), together
with the strict branch, prefix, and marked-order tests performed by
[verify.py](verify.py). The long decimals are only **locators**;
no equation is assumed at the seed itself.

| \(p_1,p_2\) | rational seed \(s\) (decimal prefix; complete seed in verifier) | first-level Rouché margin \(>\) | second-level Rouché margin \(>\) | normalized third-return margin \(>\) |
|:--:|:--|--:|--:|--:|
| 3,3 | -1.78644152790551131044… | 0.127464 | 0.006308 | 0.170868 |
| 3,4 | -1.78921105996871074726… | 0.114089 | 0.001837 | 0.243878 |
| 3,5 | -1.79002516526106961615… | 0.110133 | 0.008030 | 0.261699 |
| 4,3 | -1.94255039418497097061… | 0.045190 | 0.002828 | 0.174909 |
| 4,4 | -1.94270420172521125062… | 0.041404 | 0.000978 | 0.245444 |
| 4,5 | -1.94274720856175380537… | 0.040344 | 0.002609 | 0.262575 |
| 5,3 | -1.98552794754653622605… | 0.111807 | 0.000817 | 0.175214 |
| 5,4 | -1.98553702124031319738… | 0.110887 | 0.000286 | 0.245758 |
| 5,5 | -1.98553952938943928931… | 0.110632 | 0.000698 | 0.262640 |

**Finite theorem (conditional only on named external topological
results).** In each chart there is **exactly one** real zero of
\(P_n\). It has the designated two-level branch, not the spurious
period-three centre or another solution of \(P_n=0\). The parameter
is a primitive, twice-renormalizable, postcritically finite real
quadratic: the central first and second returns have proper
quadratic-like restrictions of degree exactly two, and the third
return of \(G_2\) has a separate proper degree-two restriction.
The first-level straightening is \(F_{c_{p_2}}\) by real PCF kneading
rigidity as detailed in §3. The local uniqueness is **not** a claim
about the entire real axis or any maximal unspecified window. In the
specified primitive tuning copy, uniqueness also follows from the
external tuning homeomorphism once the first-level combinatorics and
straightening are fixed.

The rational radii used in **physical \(z\)-coordinates** are
\[
R_1=\begin{cases}1/4&p_1=3,\\2^{-p_1}&p_1=4,5,\end{cases}
\quad R_2=\frac{1}{10\,4^{p_1-3}(4\ \text{if }p_2=3\ \text{else }2^{p_2})},
\quad R_3=\frac{3}{10N},
\]
where \(N\) is the **unique nearest integer to the certified**
\(A_n>0\) interval midpoint (computed, not postulated, in the
verifier). On each radius \(R=R_1,R_2,R_3\), expand
\[
 F_c^j(z)=x_j+A_jz^2+E_j(z),\qquad
 T_1=0,\quad
 T_{j+1}=2|x_j|T_j+(|A_j|R^2+T_j)^2.
 \tag{1}
\]
Induction on the exact squaring recurrence proves
\(\sup_{|z|\le R}|E_j(z)|\le T_j\), with **all** higher orders
included. Every multiplication in (1) uses outward \(2^{-512}\)
integer intervals, including the radius squared; the code does not
use floats, finite-difference derivatives, sampled-circle evidence,
or truncated polynomial remainder estimates.

For \(j=p_1,n,3n\), the verifier establishes on the corresponding
circle the **strict Rouché margin**, for *every* \(|w|\le R\),
\[
\Delta_j=\inf|A_j|R^2-\sup|x_j|-T_j-R>0.\tag{2}
\]
The displayed third margin is \(\inf A_n\,\Delta_{3n}\)
(the normalized \(G_2^3\) disk target radius is \(A_nR_3\approx0.3\)),
not the unscaled \(\Delta_{3n}\). The first two columns are
unscaled. Rouché's theorem gives precisely two solutions in each
source disk for every target in the target disk, with no boundary
preimages. Critical values lie strictly inside. The component
containing zero therefore gives a proper degree-two map
\(V_j\Subset D(0,R_j)\to D(0,R_j)\). Riemann–Hurwitz/degree
count gives its single critical point. To establish a *tower* rather
than unrelated disk restrictions, the verifier also checks:

1. Entire \(F^r(D(0,R_1))\) disks are pairwise disjoint for
   \(0\le r<p_1\); entire \(F^{rp_1}(D(0,R_2))\) disks are pairwise
   disjoint for \(0\le r<p_2\); and the three
   \(G_2^r(D(0,R_3))\) phase disks for \(r=0,1,2\) are disjoint.
2. The whole complex \(G_1\)-images of the second-level phase disks
   lie strictly in \(D(0,R_1)\), and their centres lie in its *central*
   preimage component via the checked real monotone connector. In
   particular \(D(0,R_2)\subset V_1\). For the third return, the
   full images at times \(n,2n,3n\) lie in \(D(0,R_2)\), and the
   centres at \(n,2n\) lie in its central component \(V_2\).
3. The \(G_1\)-critical orbit through \(6p_2\) steps stays in its
   central connected filled Julia set, and the strict prefix and
   separation checks specify the **primitive** copy.

The strict root chart is proved by opposite endpoint signs of
\(P_n\) and a single-signed interval enclosure of
\(P_n'=x'_{3n}+x'_{6n}\) **throughout the whole chart**. The root
is thereby *exactly* specified without an algebraic expression or
calling a numerical approximation a proof.

## 2. The second marked structure, with operations separated

Normalize by the **holomorphic** affine change
\(u=-A_nz\) (at the actual parameter \(A_n>0\)). Then
\(\widehat G_2(u)=-A_nG_2(-u/A_n)\) has quadratic part
\(-u^2\) and the positive signed tip portrait. Denote its
normalized critical orbit by
\(u_r=-A_nx_{rn}\), \(1\le r\le6\), and its positive
repelling fixed point by \(\alpha\). The checker isolates \(\alpha\)
in a rational interval of radius \(10^{-10}\), proves its fixed
point equation by a sign change, and checks the complete **strict**
second-level orders:
\[
u_2<u_5<u_3<0<u_6<\alpha<u_4<u_1,
\]
\[
-u_1<-u_4<u_2<u_5<-\alpha<u_3<u_6<\alpha
 <-u_5<-u_2<u_4<u_1.\tag{3}
\]
The exact identity \(x_{6n}=-x_{3n}\) and (3) give the
real topological model in the already-proven single-level prime-end
note, **without substituting a formal table for the real cut order**.
The small Julia arcs of the prime period-three renormalization are
\([-u_6,u_6]\), \([u_4,u_1]\), \([u_2,u_5]\).
By the imported straightening and dendrite theorems, these are the
*actual* little filled Julia sets, and the second-level KKL Hubbard
tree is \([u_2,u_1]\), not an arbitrarily drawn tree. The target
slit has 10 atoms \(I_0,\dots,I_9\); the central degree-two
preimage slit has 20 atoms \(S_0,\dots,S_{19}\). The one physical
attachment is \([-u_1,u_2]\), with sides
\(S_{19},S_0,S_1\).

The **cover** \((G_2)_*\), never the immersion, is
\((G_2)_*(S_s)=I_{s\bmod10}\). The **different immersion**
\(\iota^*\) assigns successive source blocks to each target atom:

| target | immersion source atoms |
|:--|:--|
| \(I_0\) | \(S_{18},S_{19},S_0,S_1,S_2\) |
| \(I_1\) | \(S_3,S_4\) |
| \(I_2\) | \(S_5\) |
| \(I_3\) | \(S_6\) |
| \(I_4\) | \(S_7,S_8,S_9\) |
| \(I_5\) | \(S_{10}\) |
| \(I_6\) | \(S_{11},S_{12},S_{13}\) |
| \(I_7\) | \(S_{14}\) |
| \(I_8\) | \(S_{15}\) |
| \(I_9\) | \(S_{16},S_{17}\) |

The old real edges \(E_0=(u_5,u_3)\),
\(E_1=(u_6,\alpha)\), \(E_2=(\alpha,u_4)\) have cut-index
image list \((2,4,4,3,0)\) and occurrence matrix
\[
M=\begin{pmatrix}0&0&1\\1&0&1\\1&1&0\end{pmatrix}.
\]
The checker **recomputes** entries by coverage of the three old
edges, instead of merely comparing two hard-coded matrices. The
crossing-attachment proper restrictions have source endpoint
pairs \((S_3,S_1)\) and \((S_{19},S_{17})\); the avoiding class
has the single pair \((S_3,S_{17})\). Their inclusive *short*
source-arc lengths are **3,3,7**, and their pushed target lengths
are **3,3,5**. All exceed the strict KKL A.1 filter threshold two.
Each pair crosses distinct \(\iota^*\) source blocks: two crossing
and one avoiding classes survive, without claiming that arbitrary
A.1 Wave parents must have two children. Crests \(I_0,I_2,I_8\)
have no old-edge carriers; \(I_1,I_9\) are opposite accesses
to the **same** old edge \(E_0\), not two edges. These facts are
finite combinatorial consequences of (3) and the imported KKL
identification; the Python program verifies the combinatorics, not
Carathéodory prime ends or KKL's definitions themselves.

## 3. Straightening/tuning identification and its dependencies

The \(p_1\)-return is a real-symmetric quadratic-like map with
connected filled Julia set (its entire trapped critical orbit was
checked). By **Douady–Hubbard straightening**, there is a unique
real quadratic polynomial \(Q_\gamma(z)=z^2+\gamma\) hybrid equivalent
to \(G_1\), with \(\gamma\in[-2,1/4]\). The real normalization
\(H_1(w)=A_{p_1}G_1(w/A_{p_1})\) has positive quadratic
coefficient and negative critical value. Its critical signs
\(\operatorname{sgn}(A_{p_1}x_{jp_1})\), \(1\le j\le6p_2\),
are **strictly certified equal**, entry by entry, to the signs
\(\operatorname{sgn}(F_{c_{p_2}}^j(0))\) using the separately
merged \(p=3,4,5\) tip-root rational brackets. Both critical
orbits are preperiodic, with period \(3p_2\) after time \(6p_2\)
by the exact tip relation (and avoidance of zero); these finite
checks therefore identify the **entire infinite kneading word**.
Real-symmetric straightening preserves the critical order/kneading.
**de Melo–van Strien, *One-Dimensional Dynamics*, Theorem II.10.1
(Sullivan–Milnor–Douady–Hubbard)**, proves that distinct
postcritically finite real quadratic polynomials cannot have the
same eventually periodic kneading invariant. Hence
\(\gamma=c_{p_2}\). This is a **named external rigidity theorem**;
one cannot replace it by the finite sign comparisons alone.

The **Douady–Hubbard primitive tuning/homeomorphism theorem**
identifies the real parameter as the tuning of the selected
\(p_2\) tip into the primitive \(p_1\) baby copy.
Equivalently, the fixed primitive copy's straightening is injective,
so there is at most one tuned parameter with this straightening.
We do not compute a hybrid Beltrami solution, claim an explicit
closed tuning formula, or assert that the *outer* return itself is
already the \(p_1\)-tip \(c_{p_1}\).

## 4. Certified second-level canonical-width sandwich

Use the normalized coordinates (3), the actual second-level slit
\(\Omega_2=D(0,A_nR_2)\setminus[u_2,u_1]\), and base
\(B=(I_9,I_0,I_1)\) with crest \(I_0\). Write \(W_{p_1,p_2}^*\)
for the supremal KKL A.1 Wave width, and
\(W_{p_1,p_2;2}^*\) if two A.3.2-surviving children are also
required. The lower round gate and upper *full lifted* plane-slit
path family are exactly those proven in the merged
[canonical-width sandwich](../real_primitive_tip_family_canonical_width_sandwich_20261116/NOTE.md),
now applied to **certified second-level** cuts. Let
\[
m_0=(u_2+u_5)/2,\quad r_0=(u_5-u_2)/2,\quad
r_+=( -\alpha-m_0),\quad r_-=(u_4+m_0),
\]
\[
W^{\rm rad}=\frac{\log(\min(r_+,r_-)/r_0)}{2\pi}.
\tag{4}
\]
For all nine, \(r_+<r_-\), \(r_0<r_+\), and the
**complete closed maximal gate disk** (not sampled circles) is
shown to lie in the central second-return source component. Its
round leaves therefore form a genuine A.1 lamination with the right
base/crest, and both A.3.2 proper children survive.

For the upper envelope define \(m=(u_2+u_1)/2\),
\(r=(u_1-u_2)/2\),
\(a=\arccos((m-u_5)/r)\),
\(b=\arccos((m-u_3)/r)\),
\(k=(b-a)/(b+a)\). By the imported Joukowski lift,
quadrilateral extremal-length formula, and square-sum
periodization of the covering density proved in the cited
single-level audit, the **full** lifted-plane-slit width
\(Q_{\rm plane}=K(k)/K(\sqrt{1-k^2})\) bounds *all* admissible
A.1 Wave widths above, not just round leaves. Arithmetic for
\(\pi\), \(\log\), \(\cos\), \(\arccos\), square roots and the
AGM expression for \(K\) is rational with explicit outward remainders.
Consequently the strict, two-sided **actual KKL width** statement
is
\[
W^{\rm rad}\le W_{p_1,p_2;2}^*
 \le W_{p_1,p_2}^*\le Q_{\rm plane},
\qquad 0.25<W_{p_1,p_2;2}^*,\quad
W_{p_1,p_2}^*<0.775.\tag{5}
\]
Here \(W^{\rm rad}\le W_{p_1,p_2;2}^*\);
**neither** auxiliary number is claimed to be the exact
maximal width. The detailed **strict rational output enclosures**
are as follows; all endpoints are integers divided by \(10^5\):

| \((p_1,p_2)\) | \(W^{\rm rad}\) strict interval | \(Q_{\rm plane}\) strict interval |
|:--:|:--:|:--:|
| (3,3) | (25224,25225) | (76475,76476) |
| (3,4) | (25854,25855) | (77250,77251) |
| (3,5) | (25999,26000) | (77430,77431) |
| (4,3) | (25179,25180) | (76418,76419) |
| (4,4) | (25848,25849) | (77243,77244) |
| (4,5) | (25999,26000) | (77431,77432) |
| (5,3) | (25170,25171) | (76406,76407) |
| (5,4) | (25847,25848) | (77242,77243) |
| (5,5) | (26000,26001) | (77431,77432) |

**Dependence on level one:** the two *certifiable auxiliary
bounds* depend explicitly on the \(p_1\) physical cuts and vary
strictly between several rows (for example the \(p_2=3\) radial
intervals at \(p_1=3\) and \(5\) are disjoint). The published
single-level large-period sandwich \(0.26<\liminf W_p^*\)
and \(\limsup W_p^*<0.78\) is an *asymptotic in period*; it
cannot automatically be transported through an arbitrary hybrid
conjugacy at depth two. Our finite row (5) preserves a positive
width bound **without a depth-dependent factor over this grid**,
but the strict lower number is only \(0.25\), not \(0.26\).
Nothing here resolves whether the **unknown** optimal \(W^*\)
reproduces, improves, or degrades with the parent \(p_1\);
comparison of a strict lower witness with a separate strict upper
bound cannot prove such a claim. In particular we do **not**
claim \(W_{p_1,p_2}^*=W_{p_2}^*\).

## 5. Asymptotics and depth-\(k\): proved statements vs. open goals

**Fixed \(p_2\), \(p_1\to\infty\).** For each **fixed**
\(p_2\ge3\), the existing all-\(p\) chart gives for
\(q=4^{-p_1}\) the uniform normalized return
\[h_\tau(w)=A_{p_1}F_c^{p_1}(w/A_{p_1})
=w^2+\tau+e_\tau(w),\quad |e_\tau(w)|<88q
\quad(|w|\le21/10),\tag{6}\]
with the cited \(\tau\)-derivative bound \(30000q^2\), and the
chart inverse \(\tau\mapsto c\) is unique. The known
\(c_{p_2}\) is a simple postcritically finite tip root.
For a *fixed* \(p_2\), choose rational \(\delta_{p_2},m_{p_2}>0\)
such that the two endpoint iterates of the polynomial
\(Q_t(w)=w^2+t\), through time \(6p_2\), stay inside
\(|w|<21/10\) for \(|t-c_{p_2}|\le\delta_{p_2}\), and
\(|(Q_t^{6p_2}(0)+Q_t^{3p_2}(0))'|\ge m_{p_2}\) with a
constant derivative sign. These are *finite, rationally testable*
conditions; such constants exist by the simple tip root and
strict orbit separation. For all sufficiently large \(p_1\),
all error orbits stay inside the chart and the elementary
\(5\)-Lipschitz recursion yields
\[
|P_{p_2}(h_\tau)-P_{p_2}(Q_\tau)|
 \le C_{p_2}q,\qquad
 C_{p_2}=22(5^{6p_2}+5^{3p_2}-2).\tag{7}
\]
An interval derivative recursion, using
\(|\partial_w e|\le256q\) and
\(|\partial_\tau e|<30000q^2\), establishes the corresponding
strict transversality for sufficiently small \(q\). Endpoint
signs and the intermediate-value theorem then give a unique tuned
root near \(c_{p_2}\), and
\[
|\tau_{p_1,p_2}-c_{p_2}|
 \le \frac{C_{p_2}}{m_{p_2}}4^{-p_1},\tag{8}
\]
when the denominator \(m_{p_2}\) is a derivative bound on the
whole local chart (so no hidden factor two is required). This
is a **constructive fixed-\(p_2\) asymptotic conditional on
explicitly locating the finite rational \(\delta,m\)** for each
new \(p_2\); the supplied finite verifier computes the cases
\(p_2=3,4,5\), not a uniform all-\(p_2\) modulus or an explicit
universal starting period \(p_1\). The all-\(p_1\) inverse
Chebyshev estimate in its valid \(\tau\)-chart implies, for such
large \(p_1\),
\[
\left|c(p_1,p_2)+2-\frac{3\pi^2}{2}4^{-p_1}\right|
 <500p_1 16^{-p_1}.\tag{9}
\]
The leading \(4^{-p_1}\) term does **not** depend on fixed
\(p_2\). Formulae (7)–(9) are **analytic estimates under the
named all-period theorem's hypotheses**, not extrapolations
from the nine computed rows.

**Fixed \(p_1\), \(p_2\to\infty\).** The external primitive
tuning homeomorphism \(T_{p_1}\) and the merged all-period
limit \(c_{p_2}\to-2\) imply the **qualitative** limit
\(c(p_1,p_2)\to T_{p_1}(-2)\) for the same primitive copy.
The unstraightened asymptotic
\(c_{p_2}+2=(3\pi^2/2)4^{-p_2}
+O(p_2 16^{-p_2})\) is proved in the existing audit.
A **numerical rate in physical \(c\)-coordinates** needs an
explicit modulus of continuity (or quasiconformal distortion
constants) for the tuning map near the tip; none is established
here, and we do not transfer the inner rate without one.

**Depth-\(k\) conditional inheritance.** Given a finite primitive
tuning tower of degree-two quadratic-like renormalizations whose
*last* return has the certified tip identity, O1/O2 real cut
orders and proper third return, the proof of §2 applies to that
last return **regardless of \(k\)**. Thus, by induction on the
external DH/KKL marking identification, each *such tower* has
the same combinatorial type (10/20 atoms, single attachment,
separate covering and immersion, matrix \(M\), two/one proper
classes and crest carriers) at its last level. This is a
**conditional structure theorem for all finite \(k\)**, not
a certificate that every choice of \(p_1,\ldots,p_k\) has the
required uniform polynomial-like domains. The induction in
physical geometry **stops** because the available single-level
all-period Rouché bounds do not propagate with quantitative
control of nested tuning moduli, straightening dilatations,
whole-circle radial gates, or compactness/recovery of extremal
A.1 Wave families. No depth-independent width lower bound or
unrestricted canonical limit is claimed for arbitrary \(k\).

The separate [crest-transport asymptotics](../crest_transport_asymptotics_20261116/NOTE.md)
certify only finite period rows and conjecture a positive limit.
Nothing in this depth-two certificate turns that conjecture into a
proved width or transport limit.

## 6. External theorem ledger and hostile-review limitations

* **Douady–Hubbard**, *On the dynamics of polynomial-like mappings*
  (1985), [Proposition 2 and Theorem 1, straightening](https://pi.math.cornell.edu/~hubbard/PolyLikeMaps.pdf).
  Used for connected straightening and the small filled Julia arc.
* **Douady–Hubbard tuning**, as recorded in McMullen,
  [*Complex Dynamics and Renormalization*, Chapter 7](https://people.math.harvard.edu/~ctm/papers/home/text/papers/renorm/renorm.pdf)
  and Milnor's [*Periodic Orbits, External Rays and the Mandelbrot Set*,
  Theorem 8.2](https://arxiv.org/abs/math/9905169).
  Used for uniqueness in the designated primitive baby copy.
* **de Melo–van Strien**, [*One-Dimensional Dynamics*,
  Theorem II.10.1](https://www.ma.imperial.ac.uk/~svanstri/Files/demelo-strien.pdf)
  (Sullivan–Milnor–Douady–Hubbard). Used for PCF real kneading
  rigidity; finite sign matching alone cannot substitute for it.
* **McMullen**, *Complex Dynamics and Renormalization*, Theorem 7.3;
  **Lyubich**, *Conformal Geometry and Dynamics of Quadratic
  Polynomials*, Theorem 27.4; **Carathéodory** prime-end extension.
  Used *as in* the previously merged prime-end identification to
  identify the actual small Julia arcs and Hubbard slit.
* **Kahn–Kapiamba–Lyubich**, [*MLC for parabolically bounded primitive
  renormalization*, arXiv:2606.27272v1](https://arxiv.org/abs/2606.27272v1),
  §§2.1,2.3–2.5, §6.1 Propositions 6.5–6.6, Appendix A.1,
  A.3.1–A.3.4 (including Lemma A.11/Proposition A.12).
  Used for ideal markings, covering, immersion and filtered paths.
* **Classical Rouché/Cauchy/AGM/Schwarz–Christoffel/extremal
  length**, with the square-sum density pushdown proved in the
  merged width-sandwich audit. Used for (2) and (4)–(5).

**Hostile-review checklist.** No strict width lower is inferred
from an upper-envelope computation. No 3/3/3 short-arc error, no
cover/immersion conflation, no two children automatically imposed
on all A.1 parents, no unverified parameter-window uniqueness,
no finite-difference derivative proof, no truncated holomorphic
Rouché estimate, no assumption that a real slit has already been
identified with KKL ideal boundaries, no transference of a
single-level 0.26 bound through a hybrid homeomorphism, and no
claim that an interval program proves the named external theorems.
The renormalization-level asymptotics do not assume a uniform
quasiconformal tuning modulus. There are **no numerical-only
claims** in the displayed finite tables: every number is a
strict outward rational enclosure. Uncomputed physical optimal
Wave widths, depth-uniform moduli and the fixed-\(p_1\) physical
rate are **OPEN**, not numerically certified results.

## 7. Reproduction

From repository root (Python 3.12, standard library only):

```sh
python research/independent_audits/tip_family_renormalization_depth_20261116/verify.py
python -m unittest discover -s research/independent_audits/tip_family_renormalization_depth_20261116 -p 'test_*.py' -v
```

The [dedicated workflow](../../../.github/workflows/tip-family-renormalization-depth.yml)
executes these checks, pre-existing single-level audits, the
Research validation mirror, and the Lean build. Every repo file in
this PR is **new**; in particular it does not change
`research/tip_family_theorem/`,
`research/independent_audits/crest_transport_limit_proof_20261116/`,
or any earlier result/manifest.
