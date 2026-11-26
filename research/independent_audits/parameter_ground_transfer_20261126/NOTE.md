# Quantitative equipotential-ground transfer by physical balayage

**2026-11-26. Target: the explicitly missing changing-ground comparison in
[Parameter capacity increments](../parameter_capacity_increment_20261123/NOTE.md),
§6.2 and §8; related ledger obligation H4_RIGIDITY (OPEN).**

**Result:** proposed written analytic theorem for every nonpolar compact
subset of the actual Mandelbrot set, with a corrected conditional
multiscale shrinking criterion. The full H4_RIGIDITY statement remains
OPEN. No ledger promotion. This is not a new MLC case.

Base inspected: 62256d6449d4018897fca6c1e8b7fe8af0d4e37e. The research map,
CONTRIBUTING.md, the relevant capacity note and ledger statement were
inspected. The contribution is isolated from the concurrently developed
H1–H3 and satellite-multiplier audits. It does not claim a full audit of
all transitive dependencies of H4.

## 1. Claim and conventions

Use the physical parameter escape function \(G=G_{\mathcal M}\) in the
normalization of the preceding capacity note, equation (1):
\(G(c)=\log|c|+o(1)\) at infinity. Put
\(D_t=\{G<t\}\), \(\Gamma_t=\{G=t\}\), \(t>0\).
The external parameter uniformization \(\Phi\) identifies
\(\mathbb C\setminus\mathcal M\) with \(\{|w|>1\}\),
\(G=\log|\Phi|\). In particular \(D_t\) is a bounded simply connected
analytic Jordan domain, \(\mathcal M\Subset D_t\), and the coordinate
\(u+i\theta=\log\Phi(c)\) (modulo \(2\pi i\)) is a conformal cylinder on
every positive-level annulus. No extension of \(\Phi^{-1}\) to the unit
circle is assumed.

Use \(g_t\) with \(-\Delta g_t(\cdot,w)=2\pi\delta_w\) and zero Dirichlet
boundary, \(U_t^\nu=\int g_t(\cdot,w)d\nu(w)\),
\(I_t(\nu,\lambda)=\iint g_t(z,w)d\nu(z)d\lambda(w)\),
\(I_t(\nu)=I_t(\nu,\nu)\).
The actual probability Green equilibrium measure of a nonpolar compact
\(F\subset\mathcal M\) is \(\mu_{t,F}\), and \(V_t(F)=I_t(\mu_{t,F})\).
For \(H_0^1(D_t)\), set \(\mathcal E_t(h)=(2\pi)^{-1}\int_{D_t}|\nabla h|^2\).
These are the same conventions as equations (2)–(4) of the preceding note.
All signed Green energies below are on finite-energy measures.

**Theorem 1 (quantitative changing-ground comparison).** For every such
\(F\), \(0<s<t\), \(L=t-s\), define
\[
 B(s,L)=2\sum_{k=1}^{\infty}
 \frac{\tanh(kL)}{k}\left(\frac{ks}{\sinh(ks)}\right)^2 .
\]
Then
\[
 0\le e_{s,t}(F):=V_t(F)-V_s(F)-L
 \le B(s,L)\le\frac{\pi^2 L}{3s}. \tag{1}
\]
When \(L\ge s\), also
\[
 B(s,L)\le 4+2\log(L/s). \tag{2}
\]
Thus bounded ratios \(t/s\) suffice for uniform additive transfer, without
any geometric hypothesis on \(F\). For the entire Mandelbrot set the
error is exactly zero. The proof below gives a smaller charge-dependent
bound, not just the universal worst case.

The proof is a classical potential-theoretic argument applied to the
actual parameter domain; no claim of general potential-theory novelty or
priority is made. In particular it works for any nonpolar full continuum
with the corresponding normalized exterior uniformization. This supplies
the specified missing comparison, not the physical sequence of parameter
neighborhoods or the divergent gain required to use it.

## 2. Exact transfer identity

Let \(\nu\) be a probability of finite Green energy supported in
\(\mathcal M\). Denote by \(\beta_s\nu\) its sweep onto \(\Gamma_s\):
the average of the actual harmonic measures of \(D_s\) with poles
distributed according to \(\nu\). Equivalently, for continuous harmonic
functions on \(\overline D_s\), this probability has the same integrals
as \(\nu\). This is the classical bounded-domain balayage
(Saff, §3, p. 188, (3.14), (3.17)). Here the support is compactly inside a
smooth domain, so its boundary density is smooth. In Green normalization
it is the flux \(-(2\pi)^{-1}\partial_n U_s^\nu\,d\ell\), by Green's
identity applied to the harmonic extensions of arbitrary smooth
boundary functions. Nonnegative flux and total mass one follow from
harmonic measure.

Extend \(U_s^\nu\) by zero to \(D_t\), writing \(\widetilde U_s^\nu\).
It lies in \(H_0^1(D_t)\), and integration by parts gives in distributions
\(-\Delta\widetilde U_s^\nu=2\pi(\nu-\beta_s\nu)\).
Uniqueness of the zero-trace Dirichlet solution gives
\[
 U_t^\nu=\widetilde U_s^\nu+U_t^{\beta_s\nu}.
\]
The summands are Dirichlet-orthogonal: the second is harmonic in \(D_s\)
and the first has zero trace there and vanishes outside. Green's
energy identity therefore gives
\[
 I_t(\nu)=I_s(\nu)+I_t(\beta_s\nu).
\]

Let \(\sigma_s=(\Phi^{-1}(e^{s+i\theta}))_*(d\theta/(2\pi))\).
This is the physical uniform-angle probability on the analytic
equipotential (not a substituted measure on \(F\)). The piecewise
function \(t-\max\{s,G\}\) on \(D_t\) is constant \(L\) on \(D_s\),
harmonic on the exterior collar, zero on \(\Gamma_t\), and its
distributional Laplacian is \(-2\pi\sigma_s\) by the conformal cylinder
flux. Thus it is \(U_t^{\sigma_s}\). Its energy is \(L\).
Writing \(\eta=\beta_s\nu-\sigma_s\), the cross energy with \(\sigma_s\)
is zero because \(\eta(\Gamma_s)=0\) and the latter potential is constant
there. Consequently the exact physical identity is
\[
 \boxed{I_t(\nu)=I_s(\nu)+L+I_t(\beta_s\nu-\sigma_s).} \tag{3}
\]
No orthogonality of gradients at different parameter scales is being
asserted: the orthogonality here is a decomposition at a single smooth
ground boundary.

Applying (3) to the minimizing probabilities in the two domains
separately, and using their respective minimizing properties, gives
\[
 I_t(\beta_s\mu_{t,F}-\sigma_s)\le e_{s,t}(F)
 \le I_t(\beta_s\mu_{s,F}-\sigma_s). \tag{4}
\]
The left side is nonnegative. These are different equilibrium measures;
equality of them or of their two sweeps is not assumed. As
\(V_t(\mathcal M)=t\) by the preceding note, (4) also recovers the exact
zero-error calibration for \(F=\mathcal M\).

## 3. All-mode flux and exterior annulus bounds

### 3.1. The actual swept Fourier moments

Set \(v(u,\theta)=U_s^\nu(\Phi^{-1}(e^{u+i\theta}))\) for \(0<u<s\),
and \(v_k(u)=(2\pi)^{-1}\int v(u,\theta)e^{-ik\theta}d\theta\).
This is a nonnegative harmonic function on the cylinder, smooth up to
the outer boundary and zero there. For the swept angular moments
\(m_k=\int_{\Gamma_s}e^{-ik\arg\Phi}d(\beta_s\nu)\), conformal invariance
of normal flux gives \(m_k=-v'_k(s)\), in particular \(m_0=1\).
The mean satisfies \(v_0''=0\), \(v_0(s)=0\), \(v_0'(s)=-1\);
hence \(v_0(a)=s-a\) for each \(0<a<s\). Positivity yields
\(|v_k(a)|\le s-a\). For \(k\ne0\) solve \(v_k''=k^2 v_k\) with
its values at \(a,s\):
\[
 v_k(u)=v_k(a)\frac{\sinh(|k|(s-u))}{\sinh(|k|(s-a))}.
\]
Differentiation at \(s\), then letting \(a\downarrow0\) in the bound
(not taking a boundary trace of \(v\)), gives
\[
 \boxed{|m_k|\le\frac{|k|s}{\sinh(|k|s)}.} \tag{5}
\]
This is uniform over the physical probability \(\nu\) and the
parameter compact, even without locally connected boundary. The bound
uses the actual Green function in the collar and total charge, rather
than an angular Bernoulli measure from the dynamics. It does not
identify the individual moments of the two ground equilibria.

### 3.2. Energy of the nonconstant swept charge

For a real smooth test \(h\) compactly supported in \(D_t\), denote its
trace on \(\Gamma_s\) in the same coordinates by the Fourier series
with coefficients \(h_k\). On the cylinder \(s<u<t\), the energy
of \(h\) is at least the energy of its harmonic interpolation to zero
on the outer circle. Parseval and direct integration of the hyperbolic
sine interpolants give, in the \(1/(2\pi)\) energy normalization,
\[
 \mathcal E_t(h)\ \ge\
 \frac{|h_0|^2}{L}+
 \sum_{k\ne0}|k|\coth(|k|L)|h_k|^2 .
\]
Indeed the mode with left value \(h_k\) and right value zero is
\(h_k\sinh(|k|(t-u))/\sinh(|k|L)\); integrating the derivative of
\(\overline h_k(u)h_k'(u)\) gives the stated energy.
The omitted inner-domain energy is nonnegative. This argument
extends by density and the trace theorem to \(H_0^1(D_t)\), since the
internal contour is analytic.

The signed charge \(\eta=\beta_s\nu-\sigma_s\) has no zero mode,
and all its other moments equal \(m_k\). Weighted Cauchy–Schwarz gives
\[
 \left|\int h\,d\eta\right|^2
 \le \left(2\sum_{k\ge1}\frac{\tanh(kL)}{k}|m_k|^2\right)
       \mathcal E_t(h).
\]
Taking \(h=U_t^\eta\), with \(\mathcal E_t(h)=I_t(\eta)\) and
\(\int h\,d\eta=I_t(\eta)\), proves
\[
 0\le I_t(\eta)\le
 2\sum_{k\ge1}\frac{\tanh(kL)}{k}|m_k|^2
 \le B(s,L). \tag{6}
\]
The zero-energy case needs no division. The first bound in (6) is
data-sensitive: a certificate of the actual swept Fourier moments
may reduce the penalty significantly. The universal bound consumes
only (5), so no unavailable physical moment values are needed.

### 3.3. Explicit uniform constants and finite tail

The function \(f(x)=(x/\sinh x)^2\), continuously extended at zero,
is decreasing on the positive half-line (differentiate, using
\(x\cosh x-\sinh x>0\)). By \(\tanh(kL)\le kL\) and the integral
comparison for decreasing functions,
\[
 B(s,L)\le 2L\sum_{k\ge1}f(ks)
 \le\frac{2L}{s}\int_0^\infty f(x)\,dx
 =\frac{\pi^2 L}{3s}. \tag{7}
\]
The integral equals \(\pi^2/6\): expand
\(1/\sinh^2 x=4\sum_{n\ge1}ne^{-2nx}\), integrate the positive series
term by term, and use \(\sum n^{-2}=\pi^2/6\).

For a large ratio set \(A=L/s\ge1\). The function
\(\min(L,1/x)f(sx)\) is decreasing. Using \(\tanh(kL)\le\min(kL,1)\)
and the same integral comparison gives
\[
 B(s,L)\le 2\int_0^\infty \min(A,1/y)f(y)\,dy
 \le 2\left[1+\log A+\int_1^\infty y/\sinh^2 y\,dy\right].
\]
The last integral is
\(\coth 1-\log(\sinh 1)-\log 2<1\).
For an elementary bound, \(e^{-2}<1/7\) implies
\(1/\sinh^2 y\le(49/9)e^{-2y}\) for \(y\ge1\); the integral is then
less than \(7/12\). This proves (2). Equations (4), (6), (7)
complete Theorem 1.

For actual numerical or interval evaluation, \(q=e^{-2s}\) and a cutoff
\(N\ge0\) yield the explicit tail enclosure
\[
 0\le B(s,L)-2\sum_{k=1}^N\frac{\tanh(kL)}k f(ks)
 \le
 \frac{8s^2q^{N+1}((N+1)-Nq)}
 {(1-q)^2(1-q^{N+1})^2}. \tag{9}
\]
Expand \(f(ks)=4k^2s^2q^k/(1-q^k)^2\), drop the factor \(\tanh\),
bound the denominator below by \((1-q^{N+1})^2\), and sum the
geometric derivative. A rational or interval evaluation of the displayed
finite terms and elementary functions, including the upper tail, is
sufficient to certify a usable transfer bound. A truncated sum by itself
is a lower bound on the universal penalty and is not a safe subtraction
in the shrinking criterion.

## 4. Corrected multiscale criterion (conditional application)

Let \(F_0\supset F_1\supset\cdots\) be nonpolar compact connected
parameter sets inside \(\mathcal M\) and
\(1\ge t_0\ge t_1\ge\cdots>0\). Define
\[
 R_n=V_{t_n}(F_n)-t_n,\qquad
 d_n=V_{t_n}(F_{n+1})-V_{t_n}(F_n)\ge0 .
\]
The latter is a true same-ground gain, so the preceding capacity note,
Theorem 2.1, applies to that pair. Define the change-of-ground penalty
\(e_n=e_{t_{n+1},t_n}(F_{n+1})\) (zero for equal levels).
Then exact subtraction gives
\[
 R_{n+1}-R_n=d_n-e_n,\qquad
 0\le e_n\le B(t_{n+1},t_n-t_{n+1}). \tag{10}
\]
For example, suppose the previous note's disk/escape hypotheses (15)
hold in \(D_{t_n}\) for \(F_n,F_{n+1}\). With any certified
\(0<v_n\le V_{t_n}(F_n)\), lower bound \(\underline g_n\) on the
circular escape average and positive radii \(r_n<r'_n\) as in that
hypothesis, one can use
\[
 d_n\ge a_n=
 \frac{v_n^2\underline g_n^2}{t_n^2\log(r'_n/r_n)}.
\]
The division by \(t_n\) may compensate for a small global escape rate
if the needed physical disk and child-separation conditions are met.
They are not inferred from choosing \(t_n\) small.

More generally take any certified lower gains \(a_n\le d_n\) and
certified upper penalties \(b_n\ge e_n\) (for example (1), (2), (6),
or an upper enclosure using (9)). Then
\[
 V_1(F_N)\ge 1+R_N\ge
 1+R_0+\sum_{n<N}(a_n-b_n), \tag{11}
\]
by (1) for \(t=t_{\rm fixed}=1\), with the equal-level case immediate.
The prior note's physical diameter estimate (10) yields
\[
 \operatorname{diam}(F_N)\le
 20\exp[-1-R_0-\sum_{n<N}(a_n-b_n)]. \tag{12}
\]
Hence unbounded above partial sums suffice, since nested diameters
are nonincreasing. If the sets are connected relative neighborhoods
of the given parameter, this proves local connectivity there.
For \(t_n/t_{n+1}\le r\), one can take
\(b_n=\pi^2(r-1)/3\); this gives a simple scale-independent per-step
threshold. No actual infinite gain schedule is supplied here.
The corrected criterion is not merely to add uncorrected gains from
different grounds, which would omit \(e_n\).

## 5. Why a universal error independent of level ratios is false

### 5.1. Exact round-model check

For the synthetic compact \(K=\overline{\mathbb D}\), \(D_t\) is the
disk of radius \(e^t\). The explicit disk kernel is
\[
 g_t(z,w)=\log(1/|z-w|)+t+
                 \log|1-e^{-2t}z\overline w|.
\]
The difference of the two kernels extends continuously across the
diagonal for \(z,w\in K\). For shrinking compact disks tangent to
the unit circle at 1, \(F_\epsilon=\overline B(1-\epsilon,\epsilon)\),
\(0<\epsilon<1/2\), the difference of the two minimum energies is
bounded above and below by the maximum and minimum of the kernel
difference on \(F_\epsilon^2\). Consequently
\[
 \lim_{\epsilon\downarrow0} e_{s,t}(F_\epsilon)=
 \log\frac{1-e^{-2t}}{1-e^{-2s}}. \tag{13}
\]
At fixed \(t>0\), this tends to infinity as \(s\downarrow0\). Along
\(t\downarrow0\), \(t/s\to\infty\), its size is
\(\log(t/s)+o(1)\). Thus a logarithmic order in large ratios is already
necessary for the full-continuum analogue of the theorem; no
optimal leading coefficient is claimed for (2).

### 5.2. Actual Mandelbrot obstruction

A ratio-independent absolute bound fails on actual parameter compacts,
not just on round models. Fix \(c_*=-2\in\partial\mathcal M\) and
\(t>0\). In fact \([-2,1/4]\subset\mathcal M\): for such a real \(c\),
let \(p=(1+\sqrt{1-4c})/2\le2\), so \(c=p-p^2\ge-p\) and
\(f_c([-p,p])=[c,p]\subset[-p,p]\). For \(c<-2\), put \(a=-c>2\).
The second critical iterate is \(a^2-a>a\); for \(x\ge a\),
\(x^2-a-x\ge a(a-2)>0\), so the later real orbit escapes. This proves
the stated boundary point without a boundary-extension theorem.

For each fixed \(s>0\), take the genuine nonpolar continuum
\(F_\epsilon=[-2,-2+\epsilon]\) with \(0<\epsilon<1\). Let
\(\mathrm{rad}(D_s,c_*)\) denote the conformal radius of the simply
connected analytic Jordan domain at \(c_*\). The conformal disk
Green formula shows that \(g_t-g_s\) is continuous near
\((c_*,c_*)\) including the diagonal: subtract \(-\log|z-w|\) in
each disk formula and use the nonzero derivative of a conformal
map. Its value on that diagonal is
\(\log(\mathrm{rad}(D_t,c_*)/\mathrm{rad}(D_s,c_*))\).
The same comparison of energy minima therefore gives
\[
 \lim_{\epsilon\downarrow0} e_{s,t}(F_\epsilon)=
 \log\frac{\mathrm{rad}(D_t,c_*)}{\mathrm{rad}(D_s,c_*)}-(t-s).
 \tag{14}
\]
The conformal radius in the denominator tends to zero as \(s\downarrow0\).
For instance choose the normalized Riemann maps from the unit disk
sending zero to \(c_*\) and with positive derivative. All their images
are in the same bounded \(D_t\). If derivatives were bounded below
along a sequence \(s_j\downarrow0\), Montel would give a nonconstant
limit whose image lies in \(\{G=0\}=\mathcal M\), by continuity of \(G\).
The open mapping theorem would make \(c_*\) interior, a contradiction.
Thus (14) becomes arbitrarily large: for every proposed absolute bound
choose \(s\) first and then a sufficiently small positive \(\epsilon\).
This is a genuine obstruction on actual parameter sets to a stronger
ground-transfer assertion. These sets are not asserted to be an
infinitely renormalizable tower or relative parameter neighborhoods.
No rate of conformal-radius collapse for the Mandelbrot set is used.

## 6. Arithmetic regression (embedded, no external dependencies)

For the round model, set \(a=e^{-2s}, b=e^{-2L}\).
For a probability of finite energy in the closed unit disk with analytic
moments \(M_k=\int z^k\,d\nu\), the integrated disk kernel difference
minus \(L\) is
\(\sum_{k\ge1} a^k(1-b^k)|M_k|^2/k\).
By the disk Poisson extension, the squared modulus of the swept
moment is \(a^k|M_k|^2\). Formula (6) majorizes the exact expression
term by term by replacing \(1-b^k\) with
\(2(1-b^k)/(1+b^k)\). The following exact rational regression checks
that normalization, the uniform-charge zero modes, and finite portions
of the geometric tail estimate (9). The measures are actual uniform
circles or positive mixtures of them, not infinite-energy atoms.
Copy the standalone block to a Python 3 file and run with
python -B. No random seeds, dependencies, tolerances or floating-point
comparisons are needed.

~~~python
from fractions import Fraction as Q
import json

# Finite-energy measures: each atom of the list represents a uniform circle
# around its listed real center, of radius (1 - abs(center))/2.
# Their analytic moments are exactly the listed center's powers.
models = [
    [(Q(1), Q(0))],
    [(Q(1), Q(1, 2))],
    [(Q(1), Q(9, 10))],
    [(Q(1, 2), Q(-3, 4)), (Q(1, 2), Q(3, 4))],
    [(Q(1, 3), Q(-2, 3)), (Q(2, 3), Q(1, 4))],
]
as_ = [Q(1, 2), Q(3, 4), Q(9, 10), Q(99, 100)]
bs = [Q(1, 5), Q(1, 2), Q(9, 10), Q(99, 100)]
mode_checks = zero_modes = tail_checks = 0
for a in as_:
    for b in bs:
        for model in models:
            assert sum(w for w, _ in model) == 1
            assert all(w > 0 and abs(z) < 1 for w, z in model)
            for k in range(1, 33):
                m = sum(w * z**k for w, z in model)
                h = a**k * m*m  # squared swept Fourier moment
                actual = h * (1 - b**k) / k
                major = 2 * h * (1 - b**k) / (k * (1 + b**k))
                assert 0 <= actual <= major
                if model == models[0]:
                    assert actual == major == 0
                    zero_modes += 1
                mode_checks += 1
    # Check the tail bound in (9), divided by 8*s*s, for finite tail sums.
    for n in [0, 4, 16, 32, 64]:
        tail = sum(k*a**k/(1-a**k)**2 for k in range(n+1, n+33))
        bound = a**(n+1)*((n+1)-n*a)/((1-a)**2*(1-a**(n+1))**2)
        assert 0 < tail < bound
        tail_checks += 1
print(json.dumps(dict(disk_mode_checks=mode_checks,
                      uniform_zero_mode_checks=zero_modes,
                      finite_tail_checks=tail_checks), sort_keys=True))
~~~

Local run output:
~~~json
{"disk_mode_checks": 2560, "finite_tail_checks": 20, "uniform_zero_mode_checks": 512}
~~~
The 512 zero-mode checks are a subset of the 2560 disk-mode checks.
These are diagnostics of the algebra and normalization only. They do
not establish the continuous analytic estimates, actual harmonic
measure data at an infinitely renormalizable parameter, or an infinite
gain schedule. The regression is embedded to leave executable source
registries and concurrently edited central files untouched. No whole-repo
CI run or Lean proof is asserted.

## 7. Dependencies, scope and next obligation

* The prior parameter-capacity note, §1–3 (classical uniformization,
  probability Green normalization, Dirichlet duality, nested gains and
  fixed-ground diameter bound), §4 (optional same-ground disk/escape
  gain), and §6.2 (the missing comparison now supplied here).
* E. B. Saff, *Logarithmic Potential Theory with Applications to
  Approximation Theory*, Surveys in Approximation Theory 5 (2010),
  165–200, §3, pp. 187–188, (3.8)–(3.17), explicit disk Green kernel
  and balayage. [Source PDF](https://pages.cs.wisc.edu/~deboor/sat/papers/14/14.pdf),
  [author preprint](https://arxiv.org/abs/1010.3760). The printed page
  images for pp. 187–188 were inspected. Standard Green identity,
  harmonic Dirichlet problem, Fourier/Parseval, Montel and the open
  mapping theorem are used with their hypotheses as above.
* Douady–Hubbard parameter uniformization, inherited in precisely the
  normalization stated in the earlier note and its cited Lyubich
  lecture text. No extension to all boundary rays and no new
  dynamical theorem are imported.

The exact ledger statement of H4_RIGIDITY is that controlled marked
towers yield connected relative parameter neighborhoods forming a
basis with shrinking diameters, directly or by an applicable
trivial-fiber theorem. The present result gives one conditional
analytic endgame for actual parameter sets; it does not show that a
controlled tower supplies those sets or their gains. The first
remaining input is an actual sequence of connected relative
neighborhoods and certified local gains whose sum dominates the
actual change-of-ground penalties in (11). Large changes of ground
cannot simply be treated as free; (14) forbids a universal absolute
error, and (6) specifies what nonconstant physical charge would need
to be controlled to improve the general bound. Neither H1–H3, H4,
UPTCR, parameter rigidity, JLC, nor MLC is closed.

Attribution: credit the classical potential-theory and uniformization
sources and Matthew Robert Wesney's research archive; preserve all
source attributions of the preceding note. OpenAI ChatGPT GPT-6.2
was used for proof search, derivation, arithmetic regression, repository
inspection, source reading and drafting. No independent human
specialist verification or peer review was performed; no new
general-theory novelty or priority claim.
