# Complete buffered-WAD exclusion on the selected real family

**24 November 2026. Written theorem, with exact arithmetic premises.**

For the archive's actual selected real surfaces, this note proves

\[
\boxed{q_\alpha<\frac{1999}{1000}<2\text{ for every admissible }\alpha,
\qquad W_{\rm can}(Y_p)=0\quad(p\ge10).}
\tag{1}
\]

The assertion covers **every** admissible simple ideal arc class, including
all winding choices and every essential returning class. It does not
search a finite list of deck words. The earlier result excluded only the
outer-incident coefficients; the new ingredient is a sharper ring bound
for each inner peripheral length, followed by two elementary consequences
of hyperbolic uniformization and the collar lemma.

This is a written consequence of the explicitly cited physical selected
family and classical complex/hyperbolic analysis. The Python program proves
the rational and interval inequalities in the argument. It does not
formalize uniformization, covering spaces, quadrilateral moduli, or the
collar lemma. OpenAI GPT-6 Astra Pro assisted this proof and certificate;
human specialist review has not occurred. No MLC conclusion is asserted.

## 1. The same actual canonical surface

Use the actual selected parameters, nondegenerate real filled intervals,
and positive normalization already established in
[the physical bridge](../../tip_family_theorem/PHYSICAL_BRIDGES.md),
[the all-period construction](../real_primitive_tip_family_all_p_20261116/NOTE.md),
and [the matched outer-cover proof](../maximal_native_wave_20261123/OUTER_BUFFER_EXCLUSION.md).
Write \(x_j=f_{c_p}^{\,j}(0)\), \(\sigma_p=-[z^2]f_{c_p}^{p}>0\),
and \(X_j=\sigma_p x_{jp}\). For the present range \(p\ge10\), set
\(R=\sigma_p2^{-p}\). In this conformal coordinate the surface is

\[
Y_p=D(0,R)\setminus(K_0\cup K_1\cup K_2),\qquad
K_0=[X_3,X_6],\quad K_1=[X_4,X_1],\quad K_2=[X_2,X_5],
\tag{2}
\]

with the strictly certified order

\[
-R<X_2<X_5<X_3<0<X_6<X_4<X_1<R.
\tag{3}
\]

The ideal marking consists of the four **whole** ideal circles associated
to these three slits and the outer circle. This is precisely the
four-boundary canonical surface of KKL Appendix A.2.3 and the prior
buffered-WAD audit. It is neither the ten-atom tree annulus nor the
twenty-atom source surface used in the independent unbuffered gain.
The conclusion is restricted to this **minimal whole-component marking**.
An arbitrary refinement can make paths with both ends on the same ideal
lift admissible; those paths fall outside the distinct-lift argument
below. No zero statement is made for such refinements or the tree-annulus
marking.

Let \(\ell_i\) be the translation length of the primitive peripheral
element for boundary \(i\). In the normalization of KKL A.2.4,

\[
\ell_i=\pi\,\mathcal W_{Y_p}(I_i).
\tag{4}
\]

For an admissible arc \(\alpha\), write \(q_\alpha\) for its full
universal-cover quadrilateral width. The canonical coefficient is
\((q_\alpha-2)_+\), since (2) is not the minimally marked annulus.

### The quantitative input proved below

For every \(p\ge10\),

\[
\boxed{\ell_{\rm out}<\frac{15}{4},\qquad
\ell_0<\frac{597}{100},\qquad
\ell_1<\frac{16}{5},\qquad
\ell_2<\frac{419}{100}.}
\tag{5}
\]

These are **upper bounds**, obtained from specific embedded annuli. They
are not claimed to be the actual peripheral lengths.

## 2. Exact quadrilateral, shadow, and distance conventions

Normalize a lift of the first boundary circle to the ideal interval
\(J=(0,\infty)\) in \(\mathbb H\). Any different ideal-circle lift is
\(J'=(-b,-a)\), with \(0<a<b\). Distinct boundary lifts share no
endpoint on this nonelementary, cusp-free finite-type surface. Put

\[
r=\frac ab,\qquad s=-\log r=\log\frac ba.
\]

The four-point Schwarz–Christoffel formula, in KKL's transverse-width
convention, is

\[
q(J,J')=\frac{K(\sqrt{1-r})}{K(\sqrt r)},\qquad
K(k)=\int_0^{\pi/2}\frac{dt}{\sqrt{1-k^2\sin^2t}}.
\tag{6}
\]

The geodesic boundaries of these two ideal intervals are the vertical
axis and the semicircle with diameter \([-b,-a]\). Their common
perpendicular lies on the circle centered at zero of radius \(\sqrt{ab}\).
The elementary hyperbolic distance computation gives

\[
\cosh d=\frac{a+b}{b-a},\qquad
\tanh(d/2)=\sqrt r.
\tag{7}
\]

Thus

\[
q(d)=\frac{K(\operatorname{sech}(d/2))}
            {K(\tanh(d/2))}.
\tag{8}
\]

This function is strictly decreasing in \(d>0\). Landen's quadratic
identity gives the exact two-square cutoff

\[
\begin{aligned}
q=2
&\iff r=(3-2\sqrt2)^2=17-12\sqrt2\\
&\iff s=s_*:=\log(17+12\sqrt2)\\
&\iff d=d_*:=\tfrac12\log2.
\end{aligned}
\tag{9}
\]

Indeed \((1+3-2\sqrt2)/(1-3+2\sqrt2)=\sqrt2\), which verifies
the distance normalization directly. In particular the cutoff is
\((\log2)/2\), not \(\log2\). The certificate independently checks
the Landen value, the ring-doubling factor, and the strict collar margin.

## 3. The peripheral shadow bound also handles returning arcs

The primitive stabilizer of \(J\) is
\(\tau(z)=e^{\ell_i}z\). On the negative real axis introduce the
coordinate \(u=\log(-x)\). An interval \(J'=(-b,-a)\) has length
\(s=\log(b/a)\) in this coordinate. Its \(\tau\)-translates are
disjoint and translate this coordinate by \(\ell_i\).

Different orbits of ideal intervals have disjoint images in the circle
\(\mathbb R/\ell_i\mathbb Z\). Therefore, for any finite collection
of different such orbits,

\[
\sum s(J')\le\ell_i.
\tag{10}
\]

No claim about the measure of the limit set is needed. This is only the
packing inequality for disjoint open intervals on a circle; it is the
inequality part of the usual orthospectrum/shadow picture. Oriented
relative homotopy classes starting at \(I_i\) correspond to these
orbits, by lifting their first endpoint to \(J\). This is the familiar
peripheral double-coset description, with the entire marked boundary
circle allowed at each endpoint.

Two consequences are used.

**Single incidence.** If \(\ell_i<s_*\), every class incident on
\(I_i\) has \(s\le\ell_i<s_*\), hence \(q<2\).

**Returning incidence.** An essential unoriented arc from \(I_i\) to
itself has two distinct oriented interval orbits. To see the distinction,
suppose a deck transformation identified the pair with its reversed pair.
It would exchange their two bounding geodesics and therefore exchange the
endpoints of their unique common perpendicular. It would fix the midpoint
of that perpendicular in \(\mathbb H\), impossible for a nontrivial
element of a torsion-free deck group. Both orientations have the same
\(q\), \(d\), and \(s\). Equation (10) therefore gives

\[
2s\le\ell_i.
\tag{11}
\]

Consequently \(\ell_i<2s_*\) implies \(q<2\) for **every**
essential returning class at that boundary. Classes whose two endpoints
lift to the *same* ideal interval are boundary-subordinate and already
excluded by KKL A.1. This proof does not conflate those classes with
essential returns on different lifts.

For the current application the elementary exact estimate

\[
s_*>\frac72
\tag{12}
\]

suffices. The checker proves
\(e^{1/2}<33/20\),
\((33/20)^7<169/5=17+12(7/5)<17+12\sqrt2\), using a positive
Taylor series with a geometric remainder and \((7/5)^2<2\).

## 4. A sharper annulus around each actual slit

Let \(-R\le b<a<d<c\le R\). Form

\[
A(b,a,d,c;R)=D(0,R)\setminus
\bigl([a,d]\cup[-R,b]\cup[c,R]\bigr).
\tag{13}
\]

The two outer cuts are joined through the complement of the disk; one
cut may be the degenerate boundary point when \(b=-R\) or \(c=R\).
Thus (13) is a doubly connected domain whose inner boundary is the
central slit \([a,d]\). Its upper half is the upper halfdisk, with
Dirichlet electrodes on the central slit and the complementary outer
boundary, and with free boundary on the two real gaps.

The map

\[
h(z)=z+R^2/z
\tag{14}
\]

maps that upper halfdisk conformally onto the lower half-plane. Its two
quadratic preimages have product \(R^2\), so at most one lies in the
disk; its only critical points \(\pm R\) are on the boundary. For
\(z\) in the upper halfdisk,
\(\operatorname{Im}h(z)=\operatorname{Im}z(1-R^2/|z|^2)<0\).
This fixes the electrode order, including the case where the central
electrode passes through the pole at zero on the boundary.

Canceling reciprocal factors from the cyclic four-point cross ratio
gives the positive number

\[
m=
\frac{(d-a)(c-b)}{(d-b)(c-a)}
\frac{(R^2-ad)(R^2-bc)}{(R^2-bd)(R^2-ac)},\qquad 0<m<1.
\tag{15}
\]

The upper halfdisk's quadrilateral conductance is
\(E(m)=K(\sqrt m)/K(\sqrt{1-m})\). The annulus conductance is
**twice** this number:

\[
\frac1{\operatorname{mod}A}=2E(m).
\tag{16}
\]

For completeness, the annular equilibrium potential is invariant under
complex conjugation by uniqueness. Its restriction to the upper half
has the mixed electrode/free-boundary variational problem of the
quadrilateral. Conversely the quadrilateral minimizer reflects across
its free real gaps to an admissible annular minimizer. Dirichlet energy
therefore doubles. Equivalently, double the conformal rectangle across
its two free sides: its circumference doubles and its electrode distance
does not. This explains the factor two in (16), rather than assuming it
from a diagram.

Choose the following rings in the actual surface (2):

| Boundary | \(b\) | \(a\) | \(d\) | \(c\) |
|---|---:|---:|---:|---:|
| \(K_0\) | \(X_5\) | \(X_3\) | \(X_6\) | \(X_4\) |
| \(K_1\) | \(X_6\) | \(X_4\) | \(X_1\) | \(R\) |
| \(K_2\) | \(-R\) | \(X_2\) | \(X_5\) | \(X_3\) |

Each ring is contained in \(Y_p\), since its outer cuts remove both
foreign slits. A core winds once around its named slit and around no
other slit. Thus it lifts **injectively, with primitive core degree
one**, to that boundary's peripheral cyclic cover. The injectivity is
immediate because the lift projects to the original embedded inclusion.
Modulus monotonicity for essential subannuli and (4),(16) give

\[
\ell_i\le\frac{\pi}{\operatorname{mod}A_i}
=2\pi E(m_i).
\tag{17}
\]

When a ring edge meets an actual slit endpoint or the outer circle,
one may apply the inequality to compact essential subannuli and pass
to their increasing modulus limit. Nothing assumes that artificial
real cuts are additional boundary components of \(Y_p\).

### Finite cases and the uniform tail

The checker revalidates the original exact root packets for \(p=10,11,12\)
and the existing signed-chart root isolation for \(p=13,14,15,16\).
It then computes all six actual \(X_j\), their order, \(R\), and
the three cross ratios with outward \(2^{-512}\) arithmetic.

For **every** \(p\ge17\), it uses the common box supplied by the
existing all-period physical proof:

\[
|X_1+u_1|\le15246\,4^{-17},\qquad
|X_j+u_j|\le
\left(30\cdot15246+\frac{88(4^j-1)}3\right)4^{-17}
\quad(2\le j\le5),\qquad X_6=-X_3,
\tag{18}
\]

where \(u_j\) is the exactly isolated limiting critical orbit.
The parameter-error term retains its **full** coefficient. The sixth
endpoint uses the exact defining tip equation
\(x_{6p}+x_{3p}=0\); it is **not** obtained by extending the upstream
model parameter-derivative bound beyond the fifth iterate. This avoids
an unsupported sixth-iterate use of that bound. The actual
target radius is greater than \((3/20)2^p\). We build all three rings
inside the fixed smaller disk of radius \((3/20)2^{17}\), which lies
inside every target disk in the tail. This avoids any unsupported
monotonicity claim about evaluating (15) over an unbounded radius interval.

The bounds below are rounded **upwards** from the exact intervals for
the expressions on the right of (17):

| Physical case | \(2\pi E(m_0)<\) | \(2\pi E(m_1)<\) | \(2\pi E(m_2)<\) |
|---|---:|---:|---:|
| 10 | 5.960040 | 3.133005 | 4.185655 |
| 11 | 5.959927 | 3.128257 | 4.179546 |
| 12 | 5.959898 | 3.125890 | 4.176500 |
| 13 | 5.959891 | 3.124709 | 4.174979 |
| 14 | 5.959890 | 3.124118 | 4.174219 |
| 15 | 5.959889 | 3.123823 | 4.173840 |
| 16 | 5.959889 | 3.123676 | 4.173650 |
| Every \(p\ge17\) | 5.960400 | 3.123928 | 4.173931 |

These give the three inner bounds in (5). The existing outer Joukowski
construction works with the common parameter \(t=200\) in every case:
the entire carrier ellipse lies in the relevant disk, so

\[
\ell_{\rm out}\le\frac{2\pi^2}{\log200}<\frac{15}{4}.
\tag{19}
\]

The existing exact Machin/atanh and elliptic series provide the
transcendental enclosures. A regression rejects the insufficient broad
\(p=13\) tail box if it is substituted for (18); the finite split is
part of this certificate, not an extrapolation from sampled periods.

## 5. All remaining classes are below the buffer

The boundaries have simple, pairwise disjoint closed geodesics at the
edges of their funnels. The standard hyperbolic collar lemma gives
disjoint inward collars of half-width

\[
\omega(\ell)=\operatorname{arsinh}\frac1{\sinh(\ell/2)}.
\tag{20}
\]

It applies directly to the complete Fuchsian surface; alternatively
double its compact convex core along its geodesic boundaries and apply
the closed-surface theorem. Thus the common perpendicular for **any**
class between distinct boundaries \(i,j\) has length at least
\(\omega(\ell_i)+\omega(\ell_j)\). Geodesic convexity of the core
ensures that going through a funnel cannot shorten that representative.

The two largest bounds in (5) are \(A=597/100\) and \(B=419/100\).
Therefore, for any two **different** boundary components, the lower
bound for the sum of their collar half-widths is at least
\(\omega(A)+\omega(B)\). This is independent of their homotopy
class and winding. Here is the exhaustive ten-type argument.

| Endpoint type | Exclusion |
|---|---|
| out–out, \(K_0\)–\(K_0\), \(K_1\)–\(K_1\), \(K_2\)–\(K_2\) | \(\ell_i<7<2s_*\); two oriented returning shadows |
| out–\(K_0\), out–\(K_1\), out–\(K_2\), \(K_0\)–\(K_1\), \(K_0\)–\(K_2\), \(K_1\)–\(K_2\) | The same two-collar inequality below |

For the last row the function \(\omega\) decreases, so (5),(20) imply

\[
\begin{aligned}
\cosh d
&>\cosh(\omega(A)+\omega(B))\\
&=\frac{1+\cosh(A/2)\cosh(B/2)}
         {\sinh(A/2)\sinh(B/2)}\\
&>\frac{1061}{1000}
>\frac3{2\sqrt2}
=\cosh\left(\frac{\log2}{2}\right).
\end{aligned}
\tag{21}
\]

The middle expression is enclosed in
\((1.061364497,1.061364500)\) by exact interval arithmetic. The last
strict rational comparison follows by squaring positive quantities:
\((1061/1000)^2>9/8\). Therefore \(d>d_*\), and (8),(9) give
\(q_\alpha<2\) for every distinct-boundary class.

There is also a uniform gap. For a distinct-boundary class, (7),(21)
give

\[
m=\operatorname{sech}^2(d/2)
=\frac2{1+\cosh d}<\frac{2000}{2061}.
\tag{22}
\]

For an essential returning class, (11) gives
\(s\le\ell_i/2<597/200<3\). The same Taylor certificate used for
(12) gives
\(e^s<e^3<(33/20)^6<2061/61\), hence
\(m=1-e^{-s}<2000/2061\) again. The exact elliptic series yields

\[
E(2000/2061)<1.998248146<\frac{1999}{1000}.
\tag{23}
\]

Equations (22),(23) establish the uniform full-width bound in (1).

**Reusable all-class criterion.** More generally, on a nonelementary
finite-type cusp-free hyperbolic surface with the minimal whole-circle marking,
suppose the largest peripheral length is at most \(A\), and every
other peripheral length is at most \(B\le A\). The same argument
gives, for every admissible class,

\[
q_\alpha\le E\!\left(\max\left\{
1-e^{-A/2},\ \frac2{1+C(A,B)}\right\}\right),\qquad
C(A,B)=\frac{1+\cosh(A/2)\cosh(B/2)}
                 {\sinh(A/2)\sinh(B/2)}.
\tag{24}
\]

The first term covers all returning classes; the second covers all
classes between distinct circles. Thus an all-class buffered exclusion
can be certified from two peripheral length bounds without locating
individual universal-cover endpoints or bounding deck words. Equations
(5),(21)–(23) are one actual physical application of this criterion.

All ten endpoint types satisfy **strictly** \(q_\alpha<2\), hence (1). This
argument covers infinitely many homotopy classes by class-independent
inequalities; neither the canonical support cardinality theorem nor a
finite deck search is used. In particular the complete canonical norm,
its horizontal projection, and its horizontal-plus-vertical projection
all vanish on these selected surfaces.

## 6. Consequence for the research program

The independently proved unbuffered inequality
\(D_p=1/C_p^++1/C_p^- -1/P_p>1/100\) remains a statement about
three independently optimized marked Wave families on **different
marked surfaces**. Equation (1) now settles the previously open full
buffered support question on the selected canonical surface for all
\(p\ge10\). There is no positive canonical coefficient there whose
reciprocal could supply the proposed gain, and no positive canonical
norm to which that independent defect can be uniformly calibrated.

Thus the entire large-period selected family lies in the zero-support
regime of this literal two-square-buffered canonical WAD. It cannot
witness a positive lower bound for that WAD, or serve as a growing-width
example through those coefficients. This is a new obstruction to that
specific proposed identification, not a contradiction to KKL: its
thick-thin comparison has topology-dependent additive errors, and its
large-width arguments do not require every bounded-geometry example
to have nonzero canonical support.

This theorem does **not** compute the finite \(3\le p\le9\) WADs,
identify an iterated native Wave family, settle immersion MARK, build
the global protected tower, discharge H1–H4, or prove MLC. It also does
not forbid using other surfaces, representatives, or genuinely wide
geometries for a source-faithful amplification argument.

### The precise limitation at period nine

The same exact root certificate at \(p=9\) gives a maximal fitting
whole-carrier ellipse parameter between \(101.440042\) and
\(101.440045\). Thus smaller ellipse choices, including \(t=100\),
are available, but \(t\ge102\) is not. Even the stronger full ring
\(D_R\setminus[X_2,X_1]\), which contains all these ellipse annuli,
only supplies an outer-length upper expression in
\((4.270831108,4.270831111)\). The central-length upper expression is
in \((5.960490631,5.960490634)\). Their guaranteed collar expression is
in \((1.058064473,1.058064476)\), whose upper endpoint squared is
strictly below \(9/8\). These caps therefore do **not** certify even
the \(q<2\) all-class cutoff at \(p=9\). This diagnostic concerns
the insufficiency of the stated bounds; it does not prove that any
actual coefficient is positive. It is recomputed in
`diagnose_period9_boundary` and recorded in the manifest. The proved
range remains \(p\ge10\).

## 7. Reproduction, sources, and proof boundary

Run from the repository root:

```sh
python3 -B research/independent_audits/canonical_width_attack_20261124/verify.py
python3 -B research/independent_audits/canonical_width_attack_20261124/verify.py --check-manifest
python3 -B -m unittest discover -s research/independent_audits/canonical_width_attack_20261124 -p 'test_*.py' -v
```

The deterministic output is also recorded in [certificate.json](certificate.json).
The checks re-establish the selected parameter signs, full-bracket
derivative and itinerary, then all actual cut orders and quantitative
premises. They include the two-square cutoff, returning-arc factor two,
ring-doubling normalization, and an intentionally insufficient collar
pair. No floating-point computation determines a sign, and no prior
certificate is silently treated as proof of a new analytic theorem.

Primary sources and exact roles:

1. Kahn–Kapiamba–Lyubich, [*MLC for parabolically bounded primitive
   renormalization*, v1](https://arxiv.org/html/2606.27272v1), Appendix
   A.1, A.2.1, A.2.3, A.2.4: the actual admissible class, two-square buffer,
   canonical surface and peripheral cyclic-width conventions. Their
   result is used with its stated definitions, not altered.
2. Hugo Parlier, [*Interrogating surface length spectra and quantifying
   isospectrality*](https://arxiv.org/abs/1611.02040), §2, Lemma 2.1,
   printed pp. 5–6:
   (Collar lemma): disjoint collars with half-width (20). The elementary
   hyperbolic formula in (21) is also the right-angled-hexagon estimate
   for a pair of pants, with its third cuff allowed to tend to a cusp.
   The lemma's origin is the classical collar theorem; no novelty is
   claimed for it.
3. The archive's [matched outer-cover proof](../maximal_native_wave_20261123/OUTER_BUFFER_EXCLUSION.md),
   §§2–4, already supplies the primitive-cover comparison, elliptic
   threshold and physical outer exclusion. The present proof adds the
   **inner slit/cut rings**, the returning shadow estimate, and the
   exhaustive inner exclusion.
4. The exact finite and all-period physical coordinates are credited to
   [the original root packets](../real_primitive_tip_family_unconditional_20261116/results.json),
   [the high-period isolations](../real_primitive_tip_family_canonical_width_sandwich_20261116/NOTE.md),
   and [the corrected all-period coefficient](../tip_family_wave_gain_correction_20261123/NOTE.md).

The new analytic portion is the written deduction in §§2–5. Its
arithmetic is independently executable; its continuum mathematics
remains available for specialist review and future formalization.
