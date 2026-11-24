# Parameter capacity increments and an exact physical calibration

**2026-11-23. Alternative analytic route; global MLC remains open.**

This note works directly with compact sets in the parameter plane. It proves
an exact orthogonality identity for their equilibrium-charge increments,
turns explicit physical test functions into quantitative diameter bounds,
and gives a rationally verified example using actual quadratic parameters.
The identity requires no KKL marking, Wave identification, annular separation,
or quasiconformal rigidity endgame. The unresolved dynamical task is to
produce a sufficiently strong infinite sequence of the stated parameter
certificates. The finite example does not supply that sequence.

The underlying equilibrium-potential and Dirichlet-space facts are classical.
This note claims neither a new general potential theory nor priority for its
applications. Its contribution to this archive is the explicit parameter
certificate, its normalization, the nonlinear lower recursion, and the
proved limitation of normalizing the global escape rate.

## 1. Physical objects and normalization

Write

\[
 f_c(z)=z^2+c,\qquad x_n(c)=f_c^n(0),\qquad
 G(c)=G_{\mathcal M}(c)
 =\lim_{n\to\infty}2^{-(n-1)}\log^+|x_n(c)|.
\tag{1}
\]

Thus `G(c)=log|c|+o(1)` at infinity, and the logarithmic capacity of
the Mandelbrot set is 1. The factor is **`2^{-(n-1)}`**, because the
parameter Böttcher map evaluates the dynamical Böttcher map at the critical
value `c`, not at the critical point 0. The function `G` is continuous,
vanishes on `M`, and is harmonic on its complement. These are the classical
Douady--Hubbard uniformization facts; see the source list below.

For `T>0`, fix the physical ground domain

\[
 D_T=\{c:G(c)<T\}.
\]

Its boundary is an analytic equipotential. All compacts in an application
below lie inside this **same** domain. We normalize its Green kernel by
`-Delta_z g_D(z,w)=2 pi delta_w`. For a finite-energy signed measure `nu`, put

\[
 U_D^\nu(z)=\int g_D(z,w)\,d\nu(w),\qquad
 I_D(\nu,\sigma)=\iint g_D(z,w)\,d\nu(z)d\sigma(w),
\]

and write `I_D(nu)=I_D(nu,nu)`. For a nonpolar compact `F` in `D`, let
`mu_F` be its **probability** Green equilibrium measure and let

\[
 V_D(F)=I_D(\mu_F),\qquad C_D(F)=1/V_D(F).
\tag{2}
\]

The energy of a physical test function is

\[
 \mathcal E_D(\phi)=\frac1{2\pi}\int_D|\nabla\phi|^2\,dA,
 \qquad \phi\in H_0^1(D).
\tag{3}
\]

When integrated against finite-energy measures, an `H_0^1(D)` function
is understood through its quasi-continuous representative. This makes
the pairings independent of changes on sets of capacity zero.

With these conventions, `C_D(F)` is the minimum of (3) among functions
equal to 1 quasi-everywhere on `F`. Here *quasi-everywhere* excludes a set
of logarithmic capacity zero. Finite-energy measures do not charge such
sets. The classical equilibrium identities are

\[
 U_D^{\mu_F}=V_D(F)\quad\hbox{q.e. on }F,
 \qquad 0\le U_D^{\mu_F}\le V_D(F)\quad\hbox{on }D.
\tag{4}
\]

Saff, Section 3, equations (3.8)--(3.13), gives precisely this Green-energy
normalization and (4). In this note the measures are physical parameter
equilibrium measures. Angular Bernoulli measures, dynamical maximal-entropy
measures, and equilibrium measures of a different ground domain are not
substituted for them.

## 2. Orthogonal increments on arbitrary nested compacts

**Theorem 2.1.** Let `F_0 superset F_1 superset ...` be nonpolar compact
subsets of one fixed bounded Green domain `D`. Set
`mu_n=mu_{F_n}`, `V_n=V_D(F_n)`, and `Delta_n=mu_{n+1}-mu_n`. Then

\[
 I_D(\mu_m,\mu_n)=V_n\quad(m\ge n),
\tag{5}
\]

\[
 I_D(\Delta_n)=V_{n+1}-V_n,
 \qquad I_D(\Delta_n,\Delta_m)=0\quad(n\ne m),
\tag{6}
\]

and consequently

\[
 \boxed{V_N=V_0+\sum_{n=0}^{N-1}I_D(\Delta_n).}
\tag{7}
\]

**Proof.** The measure `mu_m` is supported on `F_m subset F_n` and does
not charge the exceptional set in (4). Integrating `U_D^{mu_n}` against
`mu_m` proves (5). Expanding the quadratic energy of
`mu_{n+1}-mu_n` gives the first identity in (6). For `n<m`, expanding the
mixed energy gives

\[
 V_{n+1}-V_{n+1}-V_n+V_n=0.
\]

This proves orthogonality, and (7) follows by telescoping. No assertion
about pointwise disjoint supports of the potential gradients is used. In
general those gradients overlap. **QED**

**Dual observable bound.** For any physical test `phi_n` in `H_0^1(D)`
with positive energy,

\[
 \boxed{V_{n+1}-V_n\ge
 \frac{\left|\int\phi_n\,d(\mu_{n+1}-\mu_n)\right|^2}
 {\mathcal E_D(\phi_n)}.}
\tag{8}
\]

Indeed, Green's identity in the energy space gives

\[
 \int\phi_n\,d\Delta_n
 =\frac1{2\pi}\int_D\nabla\phi_n\cdot\nabla U_D^{\Delta_n}\,dA,
 \quad \mathcal E_D(U_D^{\Delta_n})=I_D(\Delta_n).
\]

Cauchy--Schwarz and (6) give (8). For several tests, with their actual
Dirichlet Gram matrix `A_n` and moment-difference vector `b_n`, the bound
is `V_{n+1}-V_n >= b_n^t A_n^dagger b_n`. A singular Gram matrix causes
no inconsistency: moment differences vanish on its kernel. This is only
a finite collection of probes of the actual equilibrium measure, not a
claim that a fixed finite state determines all future geometry.

For interval-certified moments, `|observed moment|>=max(|m_n|-epsilon_n,0)`
and an energy upper bound `M_n` yield the rigorous increment
`max(|m_n|-epsilon_n,0)^2/M_n`.

## 3. Diameter bounds and the direct parameter endgame

Suppose also that every `F_n` is connected. A nondegenerate planar
continuum has logarithmic capacity at least one quarter of its diameter.
For completeness, project onto the line through two points realizing its
diameter. The projection is an interval of that length. Lifting Fekete
points from the interval cannot decrease their pairwise distances, so
transfinite diameter, hence capacity, cannot decrease (Saff, Theorem 1.9,
p. 172). The capacity of an interval of length `d` is `d/4`
(Saff, Example 1.11).

If `F_n subset {|z|<=r}` and `D subset {|z|<R}`, `r<R`, Green-kernel
monotonicity and the explicit disk kernel give

\[
 g_D(z,w)\le g_{D(0,R)}(z,w)
 =\log\frac1{|z-w|}
   +\log\frac{|R^2-z\overline w|}{R}.
\]

Testing with the logarithmic equilibrium measure therefore gives

\[
 V_D(F_n)\le-\log\operatorname{cap}(F_n)
       +\log\frac{R^2+r^2}{R}.
\]

Consequently

\[
 \boxed{\operatorname{diam}F_N\le
 4\frac{R^2+r^2}{R}
 \exp\!\left[-V_0-\sum_{n<N}I_D(\Delta_n)\right].}
\tag{9}
\]

In particular, a divergent sum of the dual lower bounds (8) forces the
intersection to be a singleton. Conversely, for nested nonempty compact
continua, a nondegenerate intersection has finite equilibrium energy and
bounds all `V_n` above. If the intersection is a singleton and `V_n` were
bounded, weak compactness of the probability measures and lower
semicontinuity of Green energy would give a finite-energy unit atom, which
is impossible. Thus, for this specified nested family, divergence in (7)
is equivalent to a singleton intersection.

For applications with `F_n subset M` and `D=D_1`, one may use the completely
explicit bound

\[
 \boxed{\operatorname{diam}F_N\le20e^{-V_N}.}
\tag{10}
\]

Here `M subset {|c|<=2}`. Also `D_1 subset {|c|<4}`: for `|c|=s>=4`,
the critical-value orbit increases in modulus and (1) gives
`G(c)>=log(s-1)>=log3>1`. Substituting `r=2,R=4` proves (10).

If, separately, the `F_n` are compact connected **relative neighborhoods**
of a parameter `c` in `M`, shrinking diameters give a connected
neighborhood basis at `c`. This is a direct route to local connectivity
there; it needs neither construction of a limiting global QC conjugacy
nor a no-line-field theorem. Arbitrary connected subsets containing `c`
are insufficient: the relative-neighborhood requirement remains explicit.

The capacitary recursion corresponding to a certified increment `q_n`
is nonlinear:

\[
 C_{n+1}\le\frac{C_n}{1+q_nC_n}.
\tag{11}
\]

Its linearization at zero has derivative 1. Thus the criterion does not
require a uniform linear contraction or a positive ordinary-time Lyapunov
exponent. It also imposes no integrability condition on a return clock.

## 4. Global logarithmic bumps: no boundary extension premise

Take actual parameter coordinates `a`, `0<r<R`, with
`closed B(a,R) subset D`, and define the continuous global function

\[
 \phi_{a,r,R}(z)=
 \begin{cases}
 1,& |z-a|\le r,\\
 \log(R/|z-a|)/\log(R/r),&r<|z-a|<R,\\
 0,&|z-a|\ge R.
 \end{cases}
\tag{12}
\]

It belongs to `H_0^1(D)` and direct integration gives

\[
 \mathcal E_D(\phi_{a,r,R})=\frac1{\log(R/r)}.
\tag{13}
\]

If `B(a,R)` misses `F_{n+1}`, then (8) gives

\[
 V_{n+1}-V_n\ge
 \left(\int\phi_{a,r,R}\,d\mu_n\right)^2\log(R/r).
\tag{14}
\]

For example, an actual equilibrium-charge bound
`mu_n(B(a,r))>=eta` implies gain at least `eta^2 log(R/r)`.
These are physical planar functions, so they do not need a Sobolev
extension from an abstract ideal boundary. The annulus in (12) surrounds
a deleted patch; it is not required to separate the whole parameter fiber.

### An escape-rate certificate that eliminates the unknown charge

**Theorem 4.1.** Work in the fixed ground `D_T`. Suppose

\[
 \overline{B(a,r)}\subset F_n\subset\mathcal M,
 \quad \overline{B(a,R)}\subset D_T,
 \quad F_{n+1}\cap B(a,R)=\varnothing.
\tag{15}
\]

Define a physical escape-rate average

\[
 \overline G(a,R)=\frac1{2\pi}\int_0^{2\pi}G(a+Re^{it})\,dt.
\tag{16}
\]

Then

\[
 \boxed{V_{n+1}\ge V_n+
 \left(\frac{V_n}{T}\right)^2
 \frac{\overline G(a,R)^2}{\log(R/r)}.}
\tag{17}
\]

**Proof.** The normalized capacitary potential of `M` in `D_T` is

\[
 p_M(z)=1-G(z)/T\quad(z\in D_T),
\tag{18}
\]

including its value 1 on `M`. Moreover `V_{D_T}(M)=T`: the logarithmic
equilibrium probability measure of `M` has Green potential `T-G` in this
domain. Capacitary monotonicity for `F_n subset M` gives

\[
 p_n:=U_D^{\mu_n}/V_n\le p_M,
 \qquad
 U_D^{\mu_n}\le V_n-(V_n/T)G.
\tag{19}
\]

Inside `B(a,r)`, `U_D^{mu_n}=V_n`; the disk consists of regular interior
points of `F_n`. Write `A_s U` for the circular average about `a` of radius
`s`. For every `s<r`, `A_sU=V_n`, and continuity of circular means at
the positive radius `r` gives `A_rU=V_n`. That continuity also follows
directly from the logarithmic maximum formula in Jensen's identity below.
Jensen's formula for `-Delta U=2pi mu_n` gives

\[
 A_rU-A_RU
 =\int\left[\log\frac{R}{\max(r,|z-a|)}\right]_+\,d\mu_n(z)
 =\log(R/r)\int\phi_{a,r,R}\,d\mu_n.
\tag{20}
\]

Here `[x]_+=max(x,0)`.
By (19), the left side is at least `(V_n/T) overline G(a,R)`.
Substituting into (14) proves (17). **QED**

**The charge is in the annulus.** In the setting (15), the equilibrium
measure actually assigns zero mass to the open interior disk `B(a,r)`.
The certificate uses the weighted charge in `r<=|z-a|<R`, obtained from
(20). It does not claim that an interior parameter disk carries
equilibrium charge.

All quantities on the right side of (17) can be bounded from finite
physical data. Disk inclusion can be proved by a critical-orbit trapping
region; child separation is a parameter-domain certificate; and escaping
arcs give lower bounds for (16). If pairwise disjoint certified arcs have
angular lengths `ell_j` in radians and `G>=g_j` there, nonnegativity of
`G` elsewhere gives
`overline G >= sum ell_j g_j/(2pi)`.

For a useful exact escape bound, if `|c|<=C`, `|x_N(c)|>=L`,
`L^2-C>L`, and `q=1-C/L^2>0`, then successive orbit moduli stay above
`L` and

\[
 \boxed{G(c)\ge2^{-(N-1)}\log(Lq).}
\tag{21}
\]

Indeed `|x_{N+k+1}|>=q|x_{N+k}|^2`; iterate this inequality and use (1).
The bound is useful when `Lq>1`.

Given certified values `0<=b_n<=overline G(a_n,R_n)^2/
(T^2 log(R_n/r_n))`, the explicit recursion

\[
 0<v_0\le V_0,\qquad v_{n+1}=v_n+b_nv_n^2
\tag{22}
\]

provides lower bounds `v_n<=V_n`. Its divergence would prove shrinking by
(9). This is more flexible than requiring `sum b_n=infinity`. For example,
if `b_n>=a/(n+1)^2` and `v_0>=1/a`, induction gives
`v_n>=(n+1)/a`, even though that coefficient sequence is summable.
No such infinite coefficient estimate is asserted for the unresolved
quadratic parameter towers.

## 5. A rationally verified parameter-plane example

Take

\[
 F_0=\mathcal M,\qquad
 F_1=\overline{B(-1,3/32)},\qquad D=D_1,
 \quad a=0,\ r=1/4,\ R=1/2.
\tag{23}
\]

These are actual quadratic parameter sets. This is a calibration at a
hyperbolic parameter, not a new MLC result at an infinitely renormalizable
parameter.

1. **The parent disk lies in `M`.** For `|c|<=1/4`, the dynamical disk
   `|z|<=1/2` is forward invariant, since `|z^2+c|<=1/2`.
2. **The child disk lies in `M`.** Write `c=-1+delta`,
   `|delta|<=3/32`. For `|z|<=1/4`,

   \[
   |f_c^2(z)|\le |z|^4+2(1+|\delta|)|z|^2
                     +|\delta|+|\delta|^2
               \le249/1024<1/4.
   \]

   Thus every even critical iterate stays in this dynamical disk and the
   odd iterates are bounded as well.
3. **Separation.** Every point of `F_1` has modulus at least `29/32>1/2`.
4. **The bump support lies in `D_1`.** For `|c|<=1/2`, the elementary
   inequality
   `max(1,|z^2+c|)<=(1+|c|)max(1,|z|)^2` gives
   `G(c)<=log(3/2)<1`.
5. **An escaping circular arc.** Put `c=(1/2)e^{it}` with
   `|t|<=1/20`. Then `|c-1/2|<=1/40`. If `a_j=x_j(1/2)` and
   `e_1=1/40`, the rational recursion

   \[
   e_{j+1}=2a_je_j+e_j^2+1/40
   \]

   bounds `|x_j(c)-a_j|`. At the fifth iterate it certifies
   `a_5-e_5>11/5`. In (21), take
   `N=5`, `C=1/2`, `L=11/5`. Then
   `q=217/242` and `Lq=217/110`. A rational Taylor upper bound for
   `exp(2/3)` proves `log(217/110)>2/3`. Therefore

   \[
   G(c)>2^{-4}(2/3)=1/24
   \quad\hbox{on that entire arc}.
   \]
6. **Certified finite energy gain.** The arc has length `1/10` in its
   angular parameter. Hence

   \[
   \overline G(0,1/2)>\frac1{480\pi}>\frac1{1920}.
   \]

   Using `V_0=T=1` and `log2<1`, (17) gives the strict physical bound

   \[
   \boxed{V_{D_1}(F_1)-V_{D_1}(\mathcal M)
          >\frac1{3\,686\,400}.}
   \tag{24}
   \]

The accompanying [verify.py](verify.py) checks every rational inequality
above, including the complex-parameter orbit enclosure over the whole
arc and the exponential remainder bound. It writes no files by default.
The committed [certificate.json](certificate.json) records the exact
inputs and strict comparisons; `--check-certificate` compares it with a
fresh exact reconstruction. The numerical program does not prove the
potential-theoretic identities or an infinite dynamical schedule.

## 6. The global normalization loss is real

### 6.1 Radial probes have no signal on parameter fibers

If both `F_n` and `F_{n+1}` lie in `M`, every function of the form
`phi(c)=h(G(c))` that has a well-defined trace on `M` is constant there.
Since both equilibrium measures have mass 1,

\[
 \int h(G)\,d(\mu_{n+1}-\mu_n)=0.
\tag{25}
\]

Thus purely radial global Böttcher probes cannot distinguish the fibers.
The successful finite test above is the Euclidean bump (12), with `G`
used to bound its *physical* charge. The test itself is not radial in `G`.

### 6.2 Rescaling the escape rate cannot remove its small factor

In (19) the useful quantity is `G/T`. Replace `G` by `A G`, `A>0`.
If the same ground domain is retained, its level becomes `A T`, and

\[
 \frac{A\overline G}{AT}=\frac{\overline G}{T}.
\tag{26}
\]

The coefficient in (17) is unchanged. The physical Robin energy of `M`
also remains the original `T`; the rescaled function `A G` no longer has
the unit normalization (1), so its level label `A T` must not be substituted
for that energy. If instead the numerical level `T`
is held fixed, the physical ground changes to `D_{T/A}`. Equilibrium
measures, Green kernels, and Robin energies then change. Formula (5)
does not telescope quantities from different grounds. A comparison
between those actual grounds is an additional theorem, not a choice of
notation.

In a regime where the available global escape-rate lower bounds have
size `2^{-q_n}`, the coefficient supplied by (17), before multiplication
by `V_n^2`, has size `4^{-q_n}/log(R_n/r_n)`. When `V_n` grows only on
the order of `q_n`, this can be far too small to establish shrinking.
These are conditional scaling observations, not an asserted uniform
asymptotic for every satellite tower.

There is an exact diagnostic for a weak certificate: if the coefficients
actually fed into (22) satisfy

\[
 \sum_{n\ge0}b_n<\frac1{4v_0},
\tag{27}
\]

then that lower recursion stays below `2v_0`. Indeed an induction gives
`v_N<=v_0+4v_0^2 sum_{n<N}b_n<2v_0`. This says the **chosen lower
certificate** cannot prove divergence; it does not say that the actual
Robin energies stay bounded.

A local or renormalized Green function could improve the estimate only
after proving a physical comparison with `p_n=U_D^{mu_n}/V_n`, or directly
constructing tests with certified physical energy and charge. No uniform
QC constant, equality of angular and parameter equilibrium measures, or
ground-change bound is assumed here.

## 7. Why positive induced derivative growth fails with a finite mean clock

This motivates allowing the slow nonlinear progress above. The published
Levin--Przytycki theorem applies to a quadratic with infinitely many
satellite renormalizations. If `J_infinity` is the intersection of the
cycles of little Julia sets, every invariant probability measure supported
there has Lyapunov exponent zero. Their Corollary 1.4 also states

\[
 \lim_{m\to\infty}\frac1m
 \log |(f_c^m)'(c)|=0.
\tag{28}
\]

**Finite-mean inducing obstruction.** Let `Y subset J_infinity`, let
`F(x)=f^{tau(x)}(x)`, and suppose `nu` is an `F`-invariant probability
with `0<bar tau=int tau dnu<infinity`. Write `F'(x)` for the branch
derivative cocycle `(f^{tau(x)})'(x)`; no global differentiability of a
measurable induced map is presumed. The lifted probability

\[
 \mu=\frac1{\overline\tau}
       \int_Y\sum_{j=0}^{\tau(x)-1}\delta_{f^j(x)}\,d\nu(x)
\]

is `f`-invariant by telescoping and is supported on `J_infinity`.
The cited theorem gives `int log|f'| dmu=0`; integrability is included in
the standard nonnegative-exponent theorem cited there. The lift formula
then gives integrability along return segments and the chain rule gives

\[
 \int\log|F'|\,d\nu
 =\overline\tau\int\log|f'|\,d\mu=0.
\tag{29}
\]

Thus an expanding induced model of this actual residual core cannot have
both positive average logarithmic derivative and an integrable return
time. Infinite mean clocks or different physical observables are needed.
This does not rule out the capacity criterion, which has neither premise.

A direct parameter derivative has a related limitation. Put
`D_j=(f_c^j)'(c)`, `D_0=1`. For the infinitely renormalizable parameter,
no `D_j` vanishes, and differentiation of the critical-orbit recurrence gives

\[
 \partial_c x_n(c)=D_{n-1}\sum_{j=0}^{n-1}D_j^{-1}.
\tag{30}
\]

From (28), for every `epsilon>0` there is `A_epsilon` with
`A_epsilon^{-1}e^{-epsilon j}<=|D_j|<=A_epsilon e^{epsilon j}`.
Consequently

\[
 |\partial_c x_n(c)|\le nA_\epsilon^2e^{2\epsilon n},
 \qquad
 \limsup_{n\to\infty}\frac1n
       \log^+|\partial_c x_n(c)|=0.
\tag{31}
\]

This excludes an exponential ordinary-time transversality bound of that
specific kind. It does not imply failure of MLC, or rule out subexponential
parameter shrinking.

## 8. What would advance this route

The next genuine theorem would supply actual nested connected relative
parameter neighborhoods and an infinite sequence of physical deleted
patches for which either the direct charge bounds (14), or the completely
observable disk/escape certificates (15)--(22), force the computed lower
energies to diverge. Disk inclusion, child exclusion, escape-arc bounds,
ground-domain identity, and the infinite lower-recursion estimate are
separate checkable parts of that statement.

The current finite calibration proves one real parameter-energy gain.
The general orthogonality theorem shows why such gains add even when
their fields overlap. The present note does not prove the needed infinite
schedule, an effective local-Green comparison, arbitrary-tower compactness,
the full MARK obligation, or MLC.

## Sources and reproduction

- E. B. Saff, *Logarithmic Potential Theory with Applications to
  Approximation Theory*, Surveys in Approximation Theory **5** (2010),
  165--200. Theorem 1.9, p. 172; Example 1.11 and Theorem 1.12, p. 174; Section 3,
  equations (3.8)--(3.13), pp. 187--188.
  [Primary author preprint](https://arxiv.org/abs/1010.3760),
  [journal-hosted PDF](https://pages.cs.wisc.edu/~deboor/sat/papers/14/14.pdf).
- M. Lyubich, *Dynamics of quadratic polynomials*, Section 21,
  Theorem 5.7 and Corollary 5.8: normalized parameter uniformization and
  `cap(M)=1`.
  [Author lecture text](https://www.dance-net.org/images/files/events/rtns2008/materiales/notes_lyubich.pdf).
- G. Levin and F. Przytycki, *On invariant measures of “satellite”
  infinitely renormalizable quadratic polynomials*, Ergodic Theory and
  Dynamical Systems **45** (2025), 1843--1869, published online
  2024-11-13. Theorem 1.1 and Remark 1.2, p. 1845; Corollaries 1.3--1.4,
  p. 1846; Proposition 6.1 and its proof, pp. 1866--1867.
  [Published primary source](https://doi.org/10.1017/etds.2024.85),
  [author preprint](https://arxiv.org/abs/2212.13070).
- D. Dudko, *On the MLC Conjecture and the Renormalization Theory in
  Complex Dynamics*, ICM 2026, Problems 4.3--4.4: the remaining satellite
  and interpolation problems. This is current scope context, not an input
  to the capacity proof.
  [Primary preprint](https://arxiv.org/abs/2512.24171),
  [published proceedings](https://doi.org/10.1137/25M1807101).

```sh
python -B research/independent_audits/parameter_capacity_increment_20261123/verify.py --check-certificate
```

Prepared with OpenAI GPT-6 Astra Pro for proof development, source
verification, and exact-arithmetic certification. The classical source
results retain their original attribution. No independent human specialist
review or Lean formalization of the analytic argument has yet been performed.
