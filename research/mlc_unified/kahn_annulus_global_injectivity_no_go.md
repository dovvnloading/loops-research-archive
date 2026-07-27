# Kahn annulus hypotheses do not imply global injectivity

## 1. Theorem and scope

This note gives an exact counterexample to the following invalid
strengthening of Kahn's annulus lemma:

> A holomorphic immersion
> \(I:\mathbb A(1,r^{1/d})\to\mathbb A(1,r)\) that extends to the inner
> circle with degree one must be globally injective.

The strengthening is false even when the inner-circle map is an
orientation-preserving analytic homeomorphism.

### Theorem 1.1

Let

\[
 r'=\frac{1287}{1000},
 \qquad
 d=16,
 \qquad
 r=(r')^{16}.
\]

For \(|a|<1\), write

\[
 B_a(z)=\frac{z-a}{1-\overline a z}.
\]

Set

\[
\begin{aligned}
 \mathcal A
 &=
 \left\{
   \frac{1+6i}{10},
   \frac{-3-i}{10},
   \frac{-7+2i}{10}
 \right\},\\
 \mathcal B
 &=
 \left\{
   \frac{-6+2i}{10},
   \frac{4i}{10}
 \right\},
\end{aligned}
\]

and define

\[
 R(z)
 =
 \frac{\prod_{a\in\mathcal A}B_a(z)}
      {\prod_{b\in\mathcal B}B_b(z)}.
\tag{1.1}
\]

Then

\[
 R:\mathbb A(1,r')\longrightarrow\mathbb A(1,r)
\]

is a holomorphic immersion, extends analytically across \(\mathbb T\), and
restricts to an orientation-preserving degree-one homeomorphism
\(\mathbb T\to\mathbb T\), but \(R\) is not injective.

Consequently, the hypotheses of Kahn I, Lemma `lem:ann-immerse`, justify
the embedded inner collar proved there but do not imply a global annulus
embedding.

This theorem is an abstract annulus no-go.  It is not an actual counterexample
to the dynamically generated bold Kahn--Lyubich ambient
immersion.  In particular, it does not encode the extra path-space,
fiber-product, or dynamical origin of that map.

## 2. Exact algebraic form

Expanding (1.1) and multiplying numerator and denominator by the same
nonzero complex constant gives

\[
 R(z)=\frac{N(z)}{D_0(z)},
\tag{2.1}
\]

where, in descending powers of \(z\),

\[
\begin{aligned}
N:\quad&
 2000+4000i,\ 
 19600+2200i,\ 
 28460-23880i,\ 
 4072-29046i,\\
&-6630-10210i,\ 
 -1950-1525i,
\end{aligned}
\tag{2.2}
\]

and

\[
\begin{aligned}
D_0:\quad&
 1525+1950i,\ 
 10210+6630i,\ 
 29046-4072i,\ 
 23880-28460i,\\
&-2200-19600i,\ 
 -4000-2000i.
\end{aligned}
\tag{2.3}
\]

Every coefficient is a Gaussian integer.  All later sign and
Rouché checks are therefore finite rational calculations.

## 3. Zeros and poles avoid the closed source annulus

The zeros and poles of a Blaschke factor and its reciprocal occur among

\[
 a,\quad b,\quad\frac1{\overline a},\quad\frac1{\overline b}.
\]

The points \(a\in\mathcal A\) and \(b\in\mathcal B\) lie in the unit disk.
Moreover,

\[
 \max_{a\in\mathcal A}|a|=\frac{\sqrt{53}}{10},
 \qquad
 \max_{b\in\mathcal B}|b|=\frac{\sqrt{40}}{10}.
\]

Direct squaring gives

\[
 \left(\frac{1287}{1000}\right)^2\frac{53}{100}<1,
 \qquad
 \left(\frac{1287}{1000}\right)^2\frac{40}{100}<1.
\tag{3.1}
\]

Thus every reciprocal point lies outside \(|z|=r'\).  Hence \(R\) has no
zero and no pole on

\[
 1\le |z|\le r'. \tag{3.2}
\]

In particular,

\[
 u(z)=\log|R(z)|
\tag{3.3}
\]

is harmonic on an open neighborhood of the closed annulus.

## 4. The inner-circle map is a degree-one homeomorphism

For \(|z|=1\), every Blaschke factor has modulus one.  Hence

\[
 |R(z)|=1,\qquad z\in\mathbb T. \tag{4.1}
\]

The topological degree of the restriction is

\[
 \deg(R|_{\mathbb T})
 =
 |\mathcal A|-|\mathcal B|
 =
 3-2
 =
 1.
\tag{4.2}
\]

We prove the stronger pointwise orientation statement.  If
\(z=e^{i\theta}\), then

\[
 \frac{d}{d\theta}\arg B_a(e^{i\theta})
 =
 \frac{1-|a|^2}{|e^{i\theta}-a|^2}.
\]

Therefore

\[
 \frac{d}{d\theta}\arg R(e^{i\theta})
 =
 \sum_{a\in\mathcal A}
 \frac{1-|a|^2}{|e^{i\theta}-a|^2}
 -
 \sum_{b\in\mathcal B}
 \frac{1-|b|^2}{|e^{i\theta}-b|^2}.
\tag{4.3}
\]

Put \(t=\tan(\theta/2)\).  After multiplication by the product of the
positive Poisson denominators, the sign of (4.3) is the sign of

\[
\begin{aligned}
p(t)={}&
619271t^{10}
-5100608t^9
+35876739t^8
-169721152t^7\\
&+491196326t^6
-885663808t^5
+1065558054t^4\\
&-957958592t^3
+669681731t^2
-236915328t
+60062535.
\end{aligned}
\tag{4.4}
\]

All signs in (4.4) are coefficient signs; the displayed `+ -` formatting
keeps the exact integers visible.

### Exact Sturm certificate

The exact Euclidean Sturm chain of \(p\) has degrees

\[
 10,9,8,7,6,5,4,3,2,1,0.
\]

Its signs at \(-\infty\) and \(+\infty\) are respectively

\[
 +--+++--+--,
 \qquad
 ++--+--+++-.
\tag{4.5}
\]

Each list has five sign changes.  Sturm's theorem therefore gives

\[
 N_{\mathbb R}(p)=5-5=0. \tag{4.6}
\]

Since

\[
 p(0)=60062535>0,
 \qquad
 \operatorname{lc}(p)=619271>0,
\]

we have \(p(t)>0\) for every real \(t\), and the point \(t=\infty\)
corresponding to \(\theta=\pi\) is positive as well.  Thus (4.3) is
strictly positive everywhere.

The circle map is therefore a local orientation-preserving
homeomorphism.  Together with degree one, this makes

\[
 R|_{\mathbb T}:\mathbb T\longrightarrow\mathbb T
\]

an orientation-preserving homeomorphism.

## 5. The source annulus maps outside the unit circle

On the outer source circle, parameterize

\[
 z(t)
 =
 r'\frac{1-t^2+2it}{1+t^2},
 \qquad t\in\mathbb R.
\tag{5.1}
\]

Exact substitution into (2.1) gives

\[
 |N(z(t))|^2-|D_0(z(t))|^2
 =
 \frac{656369\,q(t)}
 {320000000000000000000000000(1+t^2)^4},
\tag{5.2}
\]

where

\[
\begin{aligned}
q(t)={}&
11751160313656400426951788919t^8\\
&-137579839638925277492971300800t^7\\
&+958901799234288449551831128476t^6\\
&-4106906924234287705167320942400t^5\\
&+10779372189655006534093819771914t^4\\
&-16680328775739752952831727982400t^3\\
&+14042199262274463963774353314076t^2\\
&-5586354003042199421157378340800t\\
&+1394955241714223750805412881719.
\end{aligned}
\tag{5.3}
\]

The denominator in (5.2) is positive.

### Exact Sturm certificate

The exact Sturm chain of \(q\) has degrees

\[
 8,7,6,5,4,3,2,1,0.
\]

Its sign lists are

\[
 +--++--++
 \quad\text{at }-\infty,
 \qquad
 ++--++--+
 \quad\text{at }+\infty.
\tag{5.4}
\]

Each has four sign changes.  Hence \(q\) has no real root.  Since

\[
 q(0)=1394955241714223750805412881719>0
\]

and its leading coefficient is positive, \(q(t)>0\) on the real line and
at \(t=\infty\).  Equations (5.2)--(5.3) give

\[
 |R(z)|>1,\qquad |z|=r'. \tag{5.5}
\]

Now \(u=0\) on the inner boundary by (4.1), while \(u>0\) on the outer
boundary by (5.5).  The minimum principle gives \(u\ge0\) on the closed
annulus, and the strong minimum principle gives

\[
 |R(z)|>1,\qquad 1<|z|<r'. \tag{5.6}
\]

## 6. Uniform upper target bound

For \(s=|a|<1\) and \(\rho>1\) with \(\rho s<1\), a direct calculation on
\(|z|=\rho\) gives

\[
 \max_{|z|=\rho}|B_a(z)|
 =
 \frac{\rho-s}{1-\rho s}. \tag{6.1}
\]

The right side is increasing in both \(\rho\) and \(s\).  The maximum
modulus principle extends this bound over \(1\le |z|\le\rho\).
Furthermore,

\[
 |B_b(z)|>1
 \quad\text{for }|z|>1,
\]

so every reciprocal factor \(1/B_b\) has modulus less than one there.

Use the exact rational upper bounds

\[
 \frac{\sqrt{37}}{10}<\frac{61}{100},
 \qquad
 \frac{\sqrt{10}}{10}<\frac{32}{100},
 \qquad
 \frac{\sqrt{53}}{10}<\frac{73}{100}.
\]

Equations (1.1) and (6.1) give

\[
\begin{aligned}
 |R(z)|
 &<
 \prod_{s\in\{61/100,32/100,73/100\}}
 \frac{r'-s}{1-r's}\\
 &=
 \frac{5697579109375}{119480253283}
 <48
 <(r')^{16}
 =r
\end{aligned}
\tag{6.2}
\]

for \(1<|z|<r'\).  The last two inequalities are integer
cross-multiplications.  Combining (5.6) and (6.2) proves

\[
 R(\mathbb A(1,r'))\subset\mathbb A(1,r). \tag{6.3}
\]

Also,

\[
 r'=r^{1/16}, \tag{6.4}
\]

so the source and target moduli have exactly the relation in Kahn's
annulus lemma.

## 7. Exact exclusion of critical points

Up to multiplication by a nonzero constant, the numerator of \(R'\) is

\[
\begin{aligned}
P(z)={}&
(-1268000+501000i)z^8
+(-1247000+7116800i)z^7\\
&+(17024420+10563170i)z^6
+(33992992-21977616i)z^5\\
&-52469243iz^4
+(-33992992-21977616i)z^3\\
&+(-17024420+10563170i)z^2
+(1247000+7116800i)z\\
&+(1268000+501000i).
\end{aligned}
\tag{7.1}
\]

We isolate all eight zeros of \(P\) by exact Rouché inequalities.

For a Gaussian rational \(w\), define the rational lower and upper bounds

\[
 L(w)=\max(|\Re w|,|\Im w|),
 \qquad
 U(w)=|\Re w|+|\Im w|.
\tag{7.2}
\]

Then

\[
 L(w)\le |w|\le U(w). \tag{7.3}
\]

Let

\[
 \rho=10^{-4}
\]

and take the following Gaussian-rational centers; every displayed decimal
terminates and is therefore exact.

| \(j\) | \(c_j\) | exact multiplier \(m_j\) |
|---:|---:|---:|
| 1 | \(-1.469179+0.035737i\) | 126 |
| 2 | \(-1.187253+1.185352i\) | 362 |
| 3 | \(-0.818448+1.003716i\) | 118 |
| 4 | \(-0.680250+0.016547i\) | 451 |
| 5 | \(-0.487955+0.598410i\) | 122 |
| 6 | \(-0.421815+0.421140i\) | 192 |
| 7 | \(0.407227+0.223067i\) | 182 |
| 8 | \(1.888874+1.034668i\) | 144 |

Exact substitution into (7.1) gives, for every \(j\),

\[
\begin{aligned}
 L(P'(c_j))\rho
 >
 m_j\left[
 U(P(c_j))
 +
 \sum_{k=2}^{8}
 U\!\left(\frac{P^{(k)}(c_j)}{k!}\right)\rho^k
 \right].
\end{aligned}
\tag{7.4}
\]

No floating-point estimate occurs in (7.4): all centers, coefficients,
\(\rho\), and both sides are rational.  The accompanying validator repeats
the cross-multiplications and records the exact fractions.

On \(|\zeta|=\rho\), (7.3)--(7.4) give

\[
 |P'(c_j)\zeta|
 >
 \left|
 P(c_j)
 +
 \sum_{k=2}^{8}\frac{P^{(k)}(c_j)}{k!}\zeta^k
 \right|.
\tag{7.5}
\]

Rouché's theorem, comparing \(P(c_j+\zeta)\) with
\(P'(c_j)\zeta\), shows that every disk

\[
 \Delta_j=\{|z-c_j|<\rho\}
\]

contains exactly one zero of \(P\).

Exact squared-distance comparisons show that the eight disks are pairwise
disjoint.  Since \(\deg P=8\), they exhaust all zeros of \(P\).

For \(j=4,5,6,7\),

\[
 |c_j|+\rho<1. \tag{7.6}
\]

For \(j=1,2,3,8\),

\[
 |c_j|-\rho>1.2901>r'. \tag{7.7}
\]

Again, (7.6)--(7.7) are verified by squaring rational quantities.
Therefore \(P\) has no zero in \(1<|z|<r'\).  The denominator of \(R'\)
has no zero there by Section 3, so

\[
 R'(z)\ne0,\qquad 1<|z|<r'. \tag{7.8}
\]

Thus \(R\) is a holomorphic immersion on the source annulus.

## 8. Exact self-collision

Let

\[
 z_1=-1+\frac45i.
\]

Then

\[
 |z_1|^2=\frac{41}{25},
 \qquad
 1<|z_1|<r',
\tag{8.1}
\]

and exact substitution gives

\[
 w=R(z_1)
 =
 -\frac{559602300}{1858025273}
 +
 \frac{1886709225}{1858025273}i.
\tag{8.2}
\]

The polynomial \(N-wD_0\) has the exact factor \(z-z_1\).  After removing
that factor and multiplying by a nonzero constant, the remaining quartic
is

\[
\begin{aligned}
Q(z)={}&
(1649705408450+1129218801775i)z^4\\
&+(8374862949240-2102550942545i)z^3\\
&+(5597363347032-11487498744901i)z^2\\
&+(-2960676892680-7024430543585i)z\\
&-1525645358450-501687535025i.
\end{aligned}
\tag{8.3}
\]

Set

\[
 c=-0.570412+1.153470i,
 \qquad
 \rho_1=10^{-5}.
\]

The exact rational Taylor inequality is

\[
\begin{aligned}
 L(Q'(c))\rho_1
 >
 11\left[
 U(Q(c))
 +
 \sum_{k=2}^{4}
 U\!\left(\frac{Q^{(k)}(c)}{k!}\right)\rho_1^k
 \right].
\end{aligned}
\tag{8.4}
\]

Rouché's theorem gives a zero \(z_2\) of \(Q\) in
\(|z-c|<\rho_1\).

The exact center modulus is

\[
 |c|^2
 =
 \frac{413965722661}{250000000000}.
\tag{8.5}
\]

Squaring rational endpoints gives

\[
 1<|c|-\rho_1
 <
 |z_2|
 <
 |c|+\rho_1
 <1.287=r'. \tag{8.6}
\]

The \(z_2\)-disk is disjoint from \(z_1\), and \(D_0\) has no zero in the
source annulus.  Equations (8.2)--(8.4) therefore give

\[
 z_2\ne z_1,
 \qquad
 R(z_2)=w=R(z_1). \tag{8.7}
\]

This proves noninjectivity.

## 9. Proof completion

Sections 3--6 prove that \(R\) is a holomorphic map

\[
 \mathbb A(1,r')\longrightarrow\mathbb A(1,r)
\]

with the exact relation \(r'=r^{1/16}\), analytic inner-boundary
extension, and an orientation-preserving degree-one inner-circle
homeomorphism.  Section 7 proves that it is an immersion.  Section 8 gives
two distinct source points with the same image.  This proves Theorem 1.1.
\(\square\)

## 10. Consequence for the KL gate

The theorem closes one possible shortcut:

\[
\boxed{
\begin{array}{c}
\text{inner-circle degree one}\\
+\text{ analytic boundary extension}\\
+\text{ holomorphic immersion}\\
+\text{ Kahn's modulus relation}
\end{array}
\not\Longrightarrow
\text{global injectivity}.
}
\]

Therefore the actual direct-decoration embedding gate cannot be solved by
strengthening Kahn's inner-collar lemma through only its stated annular
hypotheses.

The actual KL question remains narrower.  One must either:

1. prove global univalence from additional dynamically generated
   path-space/fiber-product structure;
2. produce an actual KL base-annulus collision and its lifted deck
   certificate; or
3. replace the full tile by the collar-truncated, sheet-sensitive carrier
   program described in `actual_kl_tile_injectivity_gate.md`.

## 11. Adversarial audit

1. **Floating-point roots.**  Not used.  Root existence and exhaustion use
   exact rational Rouché inequalities.
2. **Uncertified square roots.**  Avoided in the Rouché estimates by the
   rational bounds \(L\le|\cdot|\le U\).  Disk classification uses exact
   squared inequalities.
3. **Boundary degree versus boundary injectivity.**  Degree is computed by
   factor count; injectivity is separately proved by the positive angular
   derivative and exact Sturm certificate.
4. **Failure to map into an annulus.**  The lower bound follows from an
   exact outer-circle Sturm certificate and the strong minimum principle.
   The upper bound is the explicit rational estimate (6.2).
5. **Critical point hidden near the outer boundary.**  All eight critical
   numerator roots are exhausted by disjoint Rouché disks; the nearest
   outer disk lies beyond \(1.2901>r'\).
6. **Collision at a pole.**  Section 3 excludes every pole from the closed
   source annulus.
7. **Approximate collision.**  The second point is an exact zero of the
   quartic factor, located by Rouché.  Equality of images is exact.
8. **Wrong modulus relation.**  The target radius is defined as
   \(r=(r')^{16}\), so \(r'=r^{1/16}\) identically.
9. **Overclaim about KL dynamics.**  The theorem refutes an abstract
   annulus inference only.  It does not construct an admissible KL
   dynamical stage and does not promote the fixed pseudo-piece embedding.
10. **Global promotion.**  VAAPC-I, UPTCR, and MLC remain open.

## 12. Status

This note proves:

- `KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO`.

It does not prove:

- `DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING`;
- `DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`;
- `VIRTUAL_WAVE_MARKED_CORRESPONDENCE`;
- VAAPC-I;
- UPTCR;
- MLC.
