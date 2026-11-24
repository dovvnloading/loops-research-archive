# Exact measure, capacity, and a physical-observable trace operator

**2026-11-23 (America/New_York). Written analytic consequences for the
selected physical `G=f^3` example.** The [reconstruction theorem](README.md)
identifies the actual landing sets with the octal sets used below. The
present note supplies their exact Hausdorff measure, quantitative
regularity, positive logarithmic capacity, and an averaging operator on
the complete actual sets. The operator also descends to the actual
interval return when that return is equipped with the explicitly defined
pullback energy. A separate comparison with planar Dirichlet energy is
not assumed.

The imported trace theorem is identified at theorem level in §4. The
other estimates below are proved directly. Section 7 gives a counterexample
to a proposed general passage from Cantor trace energy to interval
boundary energy, including the case of continuous fiber-compatible data.
It does not assert that its illustrative quotient has already been
identified with the physical landing map.

## 1. Actual objects and normalization

Retain the actual continuous normalized landing map `L`, the intervals
`C0=K9`, `C1=G(C0)`, `C2=G^2(C0)`, and the sets `Ej=L^-1(Cj)` of
the [reconstruction theorem, §§1–4](README.md). In that actual angular
coordinate,

\[
\mathcal C=E_1=
\left\{\sum_{n\ge1}a_n8^{-n}:a_n\in\{3,4\}\right\},
\qquad A_i=(\mathcal C+t_i)/16,
\quad(t_0,t_1,t_2,t_3)=(3,4,11,12).
\tag{1}
\]

These equalities, including the physical inverse-fiber and entropy
arguments establishing them, are inputs from that theorem. No equality
with the larger 96-state forward survivor is used.

Put

\[
s=\frac13,\qquad
K=7\mathcal C-3
=\left\{\sum_{n\ge1}7\epsilon_n8^{-n}:\epsilon_n\in\{0,1\}\right\}.
\]

The hull of `K` is `[0,1]`; its similarities are

\[
S_0x=x/8,\qquad S_1x=(7+x)/8.
\tag{2}
\]

Let `mu` be the Bernoulli probability giving each length-`n` cylinder
mass `2^-n`. The two first cylinders have length `1/8` and are
separated by a gap of length `3/4`. Hausdorff measure throughout uses
the convention with sums of diameter powers, without an additional
dimension-dependent normalization factor. All lengths and capacities
initially refer to the real angular coordinate.

## 2. Exact Hausdorff measure and explicit Ahlfors regularity

### Interval-mass lemma

For every real interval `J`,

\[
\boxed{\mu(J)\le |J|^{1/3}.}
\tag{3}
\]

For intervals of length at least one the assertion is immediate. For
shorter intervals, start with uniform Lebesgue probability `mu0` on
`[0,1]`, which satisfies (3), and iterate

\[
\mu_{n+1}=\tfrac12(S_0)_*\mu_n+\tfrac12(S_1)_*\mu_n.
\]

An interval meeting only one first cylinder satisfies the same estimate
by rescaling, since `(1/2)8^s=1`. For an interval meeting both, trim its
ends to its first and last support points. Let `a,b` be its masses in
the two pieces, and let `u,v` be their lengths measured from these
endpoints to the two inner tips. The inductive estimate gives
`a^3<=u`, `b^3<=v`, while `a,b<=1/2`. Consequently

\[
(a+b)^3=a^3+b^3+3ab(a+b)
\le u+v+3/4=|J|.
\]

This proves the estimate for every `mu_n`. Weak convergence to `mu`,
the Portmanteau inequality for open intervals, and then enlargement
of closed intervals prove (3).

### Hausdorff measure

The `2^n` level-`n` cylinders cover `K` with total diameter cost

\[
2^n(8^{-n})^s=1.
\]

Conversely, any set of diameter `r` is contained in a real interval
of length `r`. Equation (3), applied to every set in a cover, makes
the total cost at least `mu(K)=1`. Thus

\[
\boxed{
\mathcal H^{1/3}(K)=1,\qquad
\mathcal H^{1/3}(\mathcal C)=7^{-1/3},\qquad
\mathcal H^{1/3}(A_i)=112^{-1/3}.}
\tag{4}
\]

Similarity invariance of Hausdorff measure shows that its restriction
to `K` has half the total mass on each first cylinder and the same
self-similar rule thereafter. Uniqueness of the probability with these
cylinder masses therefore gives `mu=H^s|K`.

For `x in K` and `0<r<=1`, choose the smallest `n` for which
`8^-n<=r`. Its cylinder containing `x` lies in the closed ball of
radius `r` and has mass `2^-n`. Since `8^-n>r/8`, except for the
harmless `n=0` endpoint case, this and (3) give

\[
\boxed{\tfrac12 r^{1/3}\le\mu(B(x,r))\le(2r)^{1/3}.}
\tag{5}
\]

Open versus closed balls do not change these bounds because `mu` is
nonatomic. For an affine copy with hull diameter `D`, its normalized
Hausdorff probability `mu_D` consequently satisfies

\[
\tfrac12(r/D)^{1/3}\le\mu_D(B(x,r))
\le(2r/D)^{1/3},\qquad 0<r\le D.
\tag{6}
\]

Here `D=1/7` for `C` and `D=1/112` for each `Ai`. These are explicit
Ahlfors regularity bounds on the actual sets.

Finite additivity on the separated compact pieces in the reconstruction
theorem also gives

\[
\mathcal H^s(E_0)=2^{2/3}7^{-1/3},\quad
\mathcal H^s(E_1)=7^{-1/3},\quad
\mathcal H^s(E_2)=2^{1/3}7^{-1/3},
\]

\[
\mathcal H^s(E_0\cup E_1\cup E_2)
=(1+2^{1/3}+2^{2/3})7^{-1/3}.
\tag{7}
\]

The normalized circle distance agrees with the real angular distance
at sufficiently small scales on each piece, so these Hausdorff
measure formulas also apply in that circle metric.

## 3. Logarithmic capacity is positive, with explicit bounds

For a compact real set `F`, use

\[
I(\nu)=\iint\log\frac1{|x-y|}\,d\nu(x)d\nu(y),\qquad
\operatorname{cap}(F)=
\exp\{-\inf_{\nu\in\mathcal P(F)}I(\nu)\}.
\tag{8}
\]

Let `F` be an affine copy of `K` with hull diameter `0<D<=1`.
Let `N(x,y)` be the length of the common prefix of its two Cantor
addresses. For distinct points,

\[
\tfrac34D\,8^{-N(x,y)}\le |x-y|\le D\,8^{-N(x,y)}.
\tag{9}
\]

For every probability `nu` on `F`, Tonelli and Cauchy–Schwarz on
the cylinder masses give

\[
\mathbb E_{\nu\times\nu}N
=\sum_{k\ge1}\sum_{|w|=k}\nu(F_w)^2
\ge\sum_{k\ge1}2^{-k}=1.
\tag{10}
\]

This remains valid if the expectation is infinite; atoms themselves
give infinite logarithmic energy. The upper distance bound in (9)
implies `I(nu)>=log(8/D)` for every `nu`. The Bernoulli probability
has expectation exactly one in (10), so the lower distance bound
gives `I(mu_D)<=log(32/(3D))`. Therefore

\[
\boxed{\frac{3D}{32}\le\operatorname{cap}(F)\le\frac D8.}
\tag{11}
\]

In particular,

\[
3/224\le\operatorname{cap}(\mathcal C)\le1/56,\qquad
3/3584\le\operatorname{cap}(A_i)\le1/896.
\tag{12}
\]

### A sharper explicit trial-measure bound

For normalized `K`, take independent `mu`-distributed `X,Y`.
Conditioning on equal or different first digits gives

\[
I(\mu)=\log8+J,\qquad
J=\mathbb E\log\frac8{7+Y-X}.
\tag{13}
\]

Finite energy was already established in (11), so this rearrangement
is legitimate. With the symmetric variable `Z=Y-X`,

\[
J=\log8-\tfrac12\mathbb E\log(49-Z^2)
\le\log(2/\sqrt3).
\]

This yields `cap(F)>=sqrt(3)D/16`. The exact second moment improves
it further:

\[
\operatorname{Var}(X)=\frac{49}{4}\sum_{n\ge1}64^{-n}
=\frac7{36},\qquad \mathbb EZ^2=\frac7{18}.
\]

The convex function `-log(1-u/49)` lies below its endpoint chord
on `[0,1]`. Substituting `u=Z^2` into that chord bound in (13) gives

\[
\boxed{\operatorname{cap}(F)
\ge D\frac7{64}\left(\frac{48}{49}\right)^{7/36}.}
\tag{14}
\]

Thus the strengthened lower bounds are

\[
\operatorname{cap}(\mathcal C)\ge
\frac1{64}\left(\frac{48}{49}\right)^{7/36},\qquad
\operatorname{cap}(A_i)\ge
\frac1{1024}\left(\frac{48}{49}\right)^{7/36}.
\tag{15}
\]

These are bounds obtained from an explicit trial measure. They do
not identify Bernoulli measure as the logarithmic equilibrium measure.

On a unit-circle arc with angular diameter at most `1/2`,

\[
4|\theta-\phi|\le
|e^{2\pi i\theta}-e^{2\pi i\phi}|
\le2\pi|\theta-\phi|.
\tag{16}
\]

Hence the planar capacity of the corresponding unit-circle set lies
between four and `2pi` times the real-line capacity. Further transfer
to another conformal chart requires its actual coordinate comparison.

Zero angular length therefore does not make these actual root sets
zero-capacity exceptions. These capacity statements alone assert no
positive width for a specified canonical Wave family: an all-curve
condenser and a particular marked subfamily are different variational
problems.

### The Bernoulli trial measure is not equilibrium

In fact the normalized Bernoulli measure `mu` is **not** the ordinary
logarithmic equilibrium measure of `K`. Its energy is finite by (11),
so `K` is nonpolar and `mu` gives zero mass to every polar set. The
latter fact is stated after Theorem 3.1, printed p. 183, of
[Saff](https://pages.cs.wisc.edu/~deboor/sat/papers/14/14.pdf).
Here it also follows directly: if a polar set had positive `mu`
mass, inner regularity would give a compact subset of positive
mass. The normalized restriction to that subset would have finite
energy, since the logarithmic kernel is nonnegative on `K x K`,
contradicting its zero capacity.

Suppose `mu` were equilibrium, and put

\[
U(x)=\int\log\frac1{|x-v|}\,d\mu(v),\qquad V=I(\mu).
\]

Frostman's theorem ([Saff, Theorem 1.12(b), printed p. 174](https://pages.cs.wisc.edu/~deboor/sat/papers/14/14.pdf))
gives `U=V` quasi-everywhere on `K`, hence `mu`-almost everywhere.
The self-similar measure law implies that a `mu`-null set has
`mu`-null inverse image under `S0`. Consequently both `U(u)=V`
and `U(S0u)=V` hold for `mu`-almost every `u`.

Splitting the defining integral between the two first cylinders
gives

\[
U(S_0u)=\tfrac12\bigl(\log8+U(u)\bigr)+\tfrac12 W(u),
\qquad
W(u)=\log8-\int\log(7+v-u)\,d\mu(v).
\tag{16a}
\]

For `0<=u,v<=1`, the denominator `7+v-u` lies in `[6,8]`.
Differentiation under this nonsingular integral therefore gives

\[
\frac18\le W'(u)=\int\frac{d\mu(v)}{7+v-u}\le\frac16.
\tag{16b}
\]

Equation (16a) would force `W(u)=V-log8` for `mu`-almost every
`u`. But `W` is strictly increasing, so such a level set contains
at most one point, and `mu` is nonatomic. This contradiction proves
the claim. Similarities change logarithmic energy by an additive
constant independent of the probability measure. The corresponding
normalized Hausdorff probabilities on `C` and on each `Ai` are
therefore also distinct from their real-line logarithmic equilibrium
measures. All bounds (11)–(15) remain valid trial-measure bounds.

## 4. The precise imported trace theorem

The primary source is A. Jonsson, *The trace of potentials on general
sets*, **Arkiv för Matematik 17 (1979), 1–18**, [original
PDF](https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7301-11512_2006_Article_BF02385453.pdf).
The relevant result is **Theorem 3, printed p. 4**, with restriction
and extension operators in Theorems 1–2 on that page. Its double-integral
norm is **equation (1.4), printed p. 2**; the representative used for
restriction is specified in **§2.4, pp. 3–4**.

Our Ahlfors bounds verify its `d`-set hypothesis. Taking
`n=1`, `p=2`, `alpha=1/2`, `d=s=1/3` gives

\[
\beta=\alpha-(n-d)/p=1/6>0.
\]

The theorem supplies bounded restriction and bounded linear extension:

\[
\boxed{H^{1/2}(\mathbb R)|_F=B^{1/6}_{2,2}(F),}
\qquad F=\mathcal C\text{ or }A_i.
\tag{17}
\]

The squared norm is equivalent to

\[
\|u\|_{L^2(\mathcal H^s|F)}^2+
\iint_{F\times F}
\frac{|u(x)-u(y)|^2}{|x-y|^{2/3}}
\,d\mathcal H^s(x)d\mathcal H^s(y).
\tag{18}
\]

Restriction here uses Jonsson's corrected potential-theoretic
representative, rather than arbitrary values of an `L^2` class on a
length-zero set. This is a nontrivial finite-energy trace space on
the actual roots.

## 5. Exact energy splitting and contraction

On `K`, with `mu=H^s|K`, define

\[
\mathcal E_K(u)=\iint_{K\times K}
\frac{|u(x)-u(y)|^2}{|x-y|^{2s}}\,d\mu(x)d\mu(y).
\tag{19}
\]

Use actual Hausdorff measure to define `E_F` on any affine copy
`F`. This makes the energy exactly invariant under affine rescaling:
the measure product and denominator both scale by the factor `D^(2s)`.

Write `u_i=u o S_i`. Each within-child term in (19) has measure
factor `1/4` and inverse-distance factor `8^(2s)=4`. Consequently

\[
\boxed{\mathcal E_K(u)=
\mathcal E_K(u_0)+\mathcal E_K(u_1)+\mathcal X(u_0,u_1),}
\tag{20}
\]

where

\[
\mathcal X(u_0,u_1)=\tfrac12\iint
\frac{|u_0(x)-u_1(y)|^2}{|S_0x-S_1y|^{2s}}
\,d\mu(x)d\mu(y).
\tag{21}
\]

Since these cross distances lie in `[3/4,1]`, with
`m_i=int u_i dmu`,

\[
\mathcal X\ge\tfrac12\left(
\operatorname{Var}_\mu(u_0)+\operatorname{Var}_\mu(u_1)
+|m_0-m_1|^2\right).
\tag{22}
\]

Thus a difference of the two actual branch means has an explicit
positive energy cost.

Define

\[
Pu=\tfrac12(u\circ S_0+u\circ S_1).
\tag{23}
\]

This is well-defined on `mu`-almost-everywhere classes: a null set
has null inverse image under each similarity, by the self-similar
measure law. That law also gives `int Pu dmu=int u dmu`. Convexity
of the square and (20) yield

\[
\boxed{\mathcal E_K(Pu)
\le\tfrac12\bigl(\mathcal E_K(u_0)+\mathcal E_K(u_1)\bigr)
\le\tfrac12\mathcal E_K(u).}
\tag{24}
\]

Because all distances on `K` are at most one,
`E_K(v)>=2 Var_mu(v)`. Iteration therefore gives

\[
\boxed{
\left\|P^n u-\int u\,d\mu\right\|_{L^2(\mu)}^2
\le2^{-(n+1)}\mathcal E_K(u).}
\tag{25}
\]

On the actual `C`, these are precisely the two inverse branches
`theta -> (theta+3)/8`, `theta -> (theta+4)/8` of `T=d^3`.
The proof applies to every function of finite trace energy on the
complete actual landing set. No finite endpoint sample, immersion
marking, or unique geometric inverse-trace assertion enters it.

## 6. Descent to the actual interval return in the pullback norm

Let `H=G^3` on the actual interval `C1`. The physical input in the
[reconstruction theorem, §2](README.md) gives a conjugacy of this
return to the Chebyshev interval map, using the homeomorphism
`G^2:C1->C0` followed by the fine straightening. Thus every value
has two interval preimages counted with the fine degree-two
multiplicity; the critical value has one double preimage.

The inverse-fiber argument in that theorem has the following stronger
fiberwise form: **given an angle `theta` and any prescribed physical
`G`-preimage `x in K3` of `L(theta)`, one of the two half-angles of
`theta` lands at `x`.** Indeed their images under `L` are `u` and
`-u`. They exhaust the central degree-two fiber; at `u=0` they exhaust
its critical multiplicity.

Take any physical `H`-preimage `z in C1` of `L(theta)`, for
`theta in C=E1`. Apply this fiberwise statement successively to the
prescribed backward chain

\[
L(\theta)\longleftarrow G^2z\longleftarrow Gz\longleftarrow z.
\]

It produces an angle `eta in E1=C` with `8 eta=theta mod 1` and
`L(eta)=z`. There are exactly two such angular preimages in `C`.
For a noncritical physical value they therefore represent its two
distinct interval preimages once each; at the critical value both
represent its double preimage. This proves equality of the two
multisets, without assuming that any landing fiber is finite.

Define the actual interval Perron average, counting fine multiplicity,

\[
(Qv)(x)=\tfrac12\sum_{z\in C_1:\ H(z)=x}v(z).
\tag{26}
\]

The preceding fiberwise calculation gives the pointwise identity

\[
\boxed{P(v\circ L)=(Qv)\circ L\quad\text{on }\mathcal C.}
\tag{27}
\]

Let `mu_C` be normalized `H^s|C`, and set
`nu=L_*mu_C`. Define the explicitly stated physical-observable energy

\[
\mathfrak E(v)=\mathcal E_{\mathcal C}(v\circ L).
\tag{28}
\]

Equations (24) and (27) now prove

\[
\boxed{\mathfrak E(Qv)\le\tfrac12\mathfrak E(v),\qquad
\left\|Q^n v-\int v\,d\nu\right\|_{L^2(\nu)}^2
\le2^{-(n+1)}\mathfrak E(v).}
\tag{29}
\]

The normalized Bernoulli law preserves the mean under `P`, so (27)
also proves `int Qv dnu=int v dnu`. Consequently the operator is
well-defined on the corresponding almost-everywhere classes and
Jensen gives `||Qv||_L2(nu)<=||v||_L2(nu)`. Together with (29),
this extends it to the completion in the norm whose square is
`||v||_L2(nu)^2+mathfrak E(v)`.

### 6.1. Exact identification of the physical reference measure

Let `h:C1->[-2,2]` be the actual Chebyshev conjugacy supplied above:
the fine straightening after `G^2:C1->C0`. Thus

\[
h\circ H=q\circ h,\qquad q(y)=y^2-2.
\]

The interval `C1` is nondegenerate, and `h` is an interval
homeomorphism; its orientation may reverse. Put `eta=h_*nu` and
define the Chebyshev inverse average, including the double preimage
at `y=-2`, by

\[
(\mathcal R\psi)(y)
=\tfrac12\bigl(\psi(\sqrt{y+2})+\psi(-\sqrt{y+2})\bigr).
\tag{29a}
\]

Conjugacy gives `Q(psi o h)=(R psi) o h`. The mean preservation
already proved for `Q` therefore implies
`int R psi deta=int psi deta` for every continuous `psi`.

Write `T_m(cos t)=cos(mt)` for the Chebyshev polynomials. Parity
and `T_(2k)(z)=T_k(2z^2-1)` give

\[
\mathcal R[T_m(\cdot/2)](y)=
\begin{cases}
0,&m\text{ odd},\\
T_{m/2}(y/2),&m\text{ even}.
\end{cases}
\tag{29b}
\]

For every integer `m>=1`, repeated halving reaches an odd index.
Invariance consequently forces `int T_m(y/2) deta(y)=0`.
The arcsine probability

\[
d\alpha(y)=\frac{dy}{\pi\sqrt{4-y^2}},\qquad -2<y<2,
\]

has the same moments, since their integrals become
`(1/pi) int_0^pi cos(mt) dt`. Both probabilities have total mass
one. The polynomials `T_m(y/2)` span all polynomials, which are
uniformly dense in the continuous functions on `[-2,2]`. Hence

\[
\boxed{h_*\nu=\alpha,\qquad
\nu=(h^{-1})_*\alpha.}
\tag{29c}
\]

This identifies the measure on the actual physical interval. It
uses the proved inverse-fiber identity and the actual return
conjugacy, without identifying any binary-address cosine formula
for the landing map `L`.

### 6.2. The physical reference measure is not interval equilibrium

Write `C1=[a,b]`, with `a<b`. Its ordinary logarithmic equilibrium
probability is

\[
d\omega_{[a,b]}(x)=
\frac{dx}{\pi\sqrt{(x-a)(b-x)}},\qquad a<x<b;
\]

see [Saff, Example 1.11, printed p. 174](https://pages.cs.wisc.edu/~deboor/sat/papers/14/14.pdf).
Define the increasing affine map and the arcsine distribution
function by

\[
\ell(x)=\frac{2(2x-a-b)}{b-a},\qquad
A(y)=\tfrac12+\frac1\pi\arcsin(y/2).
\]

Suppose `nu=omega_[a,b]`. If `h` is increasing, (29c) implies

\[
A(h(x))=\nu([a,x])=A(\ell(x)).
\]

Since `A` is strictly increasing, `h=ell`. If `h` is decreasing,
the same calculation, using the absence of atoms, gives

\[
1-A(h(x))=\nu([a,x])=A(\ell(x)).
\]

The identity `1-A(y)=A(-y)` then gives `h=-ell`. Thus in either
orientation `h` agrees on `C1` with an invertible affine polynomial
`B`. The conjugacy identity becomes

\[
B(H(x))=B(x)^2-2\qquad (x\in[a,b]).
\]

Both sides are polynomials and agree on a nondegenerate interval,
so they agree identically. But the actual global polynomial is
`H=G^3=f^9`, of degree `2^9=512`: the left side has degree 512
and the right side degree 2. This contradiction proves

\[
\boxed{\nu\ne\omega_{C_1}.}
\tag{29d}
\]

The fine degree-two interval restriction used to define `Q` does
not change the degree of that global polynomial. Thus identifying
the physical reference measure with ordinary logarithmic
equilibrium on `C1` is ruled out. This statement concerns that
specific dynamical interval and makes no assertion about an
equilibrium measure on a parameter compact.

This is an operator on actual physical observables, with its energy
and reference measure defined explicitly by the actual landing map.
It supplies no unproved equivalence with planar Dirichlet energy,
ordinary interval `H^(1/2)` energy, a canonical Wave width, or a
Green equilibrium measure of nested parameter continua. Those
comparisons would be additional analytic statements.

## 7. Why a generic quotient-to-interval energy comparison fails

The following counterexample is on the actual affine model `K`, but
uses its canonical binary quotient. It defeats an inference from
Cantor regularity and compatible continuous values alone; it does
not assert an identification of that quotient with `L`.

Define

\[
F\left(\sum_{k\ge1}7\epsilon_k8^{-k}\right)
=\sum_{k\ge1}\epsilon_k2^{-k}.
\tag{30}
\]

This continuous surjection `K->[0,1]` sends `mu` to Lebesgue
measure and identifies the endpoint pairs of every complementary
Cantor gap. For a pair with common prefix of length `N`,

\[
|F(x)-F(y)|\le2^{-N},\qquad
|x-y|\ge(3/4)8^{-N}.
\]

Hence

\[
\mathcal E_K(F)\le A,\qquad A=(4/3)^{2/3}.
\tag{31}
\]

For `n>=2`, put `epsilon=2^-n`. Let `v_n` be zero on
`[0,1/2-epsilon]`, linear from zero to one on
`[1/2-epsilon,1/2+epsilon]`, and one thereafter. Put
`u_n=v_n o F`. These functions are continuous and constant on
every fiber of `F`.

The only nonconstant parts of `u_n` lie in

\[
L_n=S_0S_1^{n-1}(K),\qquad R_n=S_1S_0^{n-1}(K).
\]

Their rescaled values are `F/2` and `(1+F)/2`. Exact scale
invariance of the energy makes their total within-cylinder
contribution `E_K(F)/2<=A/2`. The contribution between the two
first cylinders is at most `A/2`.

Inside the left first cylinder, the shell which first differs from
`L_n` after `k` shared symbols, `1<=k<n`, has mass `2^-(k+1)`.
It is at distance at least `(3/4)8^-k` from `L_n`, which has
mass `2^-n`; the value difference is at most `1/2`. Counting
both orders, their total contribution is at most

\[
\frac A2\,2^{-n}\sum_{k=1}^{n-1}2^{k-1}\le A/4.
\]

The right contribution is the same; all remaining within-side pairs
have equal values. Therefore

\[
\boxed{\sup_n\mathcal E_K(u_n)\le\tfrac32(4/3)^{2/3},
\qquad\sup_n\|u_n\|_{L^2(\mu)}\le1.}
\tag{32}
\]

In contrast, the ordinary interval seminorm satisfies

\[
\begin{aligned}
[v_n]_{H^{1/2}(0,1)}^2
&\ge2\int_\epsilon^{1/2}\int_\epsilon^{1/2}
\frac{da\,db}{(a+b)^2}\\
&=4\log(1/2+\epsilon)-2\log(2\epsilon)\\
&\ge2(n-3)\log2\longrightarrow\infty.
\end{aligned}
\tag{33}
\]

Thus there is **no bounded descent**

\[
B^{1/6}_{2,2}(K)\longrightarrow H^{1/2}(0,1),
\qquad v\circ F\longmapsto v,
\tag{34}
\]

even on continuous functions constant on all quotient fibers. A gap
collapse can turn a bounded Cantor trace transition into an
arbitrarily expensive interval transition. This does not contradict
the intrinsic and pullback contractions (24), (29); it specifies
which additional energy comparison cannot be inferred in general.

## 8. Dependencies, consequence, and boundary

The exact set identification and physical degree-two fiber statements
are the [reconstruction theorem](README.md) and its named archive
sources. Jonsson's theorem is the sole non-elementary imported
trace-space theorem here. The measure, capacity, splitting,
contraction, physical-observable intertwining, and counterexample
are proved in this note.

The resulting positive mechanism avoids a maximal immersion marking:
the actual root set carries a complete inverse-branch average with
factor-`1/2` contraction in a specified, scale-invariant energy,
and that operator respects the actual interval dynamics. Applying
it to global renormalization would still require a comparison with
the relevant physical energy and charge. In particular, neither
`mu_C` nor `nu` is identified here with the Green equilibrium
measure of a parameter fiber. No MLC conclusion or general KKL
proper-restriction theorem follows without that further bridge.

Prepared with OpenAI GPT-6 Astra Pro for proof development, source
verification, and independent adversarial review. Jonsson's trace
theorem and the underlying physical landing and Chebyshev inputs
retain their original attribution. Independent human specialist
review and a Lean formalization of these analytic arguments remain
outstanding.
