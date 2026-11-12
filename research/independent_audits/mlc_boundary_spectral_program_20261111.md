# An arithmetized boundary-spectrum route to MLC

**2026-11-11 | Independent research note | MLC remains OPEN**

This is a deliberately different route from Loops' marked-width tower. It gives (i) a *necessary and sufficient* finite-polynomial uniform-Cauchy criterion for MLC, (ii) a critical spectral-energy sufficient condition, (iii) critical-Sobolev/no-power-law and inverse-logarithmic best-approximation barriers from a published ray-landing witness, and (iv) a rigorous positive-Green-level finite-coefficient error certificate. The general ingredients are classical (Douady--Hubbard, Carathéodory, Fejér, Gronwall, Cauchy--Schwarz); this note **does not claim priority**, prove MLC, or discharge H1--H4. Its contribution within this archive is a concrete independent spectral program with explicit acceptance and failure criteria.

## 1. Map, coefficients and scope

Let `M` be the quadratic Mandelbrot set and let the exterior normalized Douady--Hubbard uniformization have inverse

\[
\Psi:\{|w|>1\}\longrightarrow\mathbb C\setminus M,
\qquad
\Psi(w)=w-\tfrac12+\sum_{n\ge1}b_n w^{-n}.
\tag{1.1}
\]

The coefficients `b_n` are real rational numbers (indeed dyadic rationals) that can be computed individually by exact recursive arithmetic. The first five published coefficients are

\[
(b_1,b_2,b_3,b_4,b_5)
=(\tfrac18,-\tfrac14,\tfrac{15}{128},0,-\tfrac{47}{1024}).
\tag{1.2}
\]

See Bielefeld--Fisher--von Haeseler, *Computing the Laurent Series of the Map* `Psi: C-D -> C-M`, **Advances in Applied Mathematics** 14 (1993), 25--38, DOI `10.1006/aama.1993.1002` (including the conditional non-Hölder theorem); Ewing--Schober, *The Area of the Mandelbrot Set*, **Numerische Mathematik** 61 (1992), 59--72; and Beretta--Dimino--Fang--Martinez--Miller--Stoll, *Fractal Fract.* 6 (2022), 534, DOI `10.3390/fractalfract6100534`. Their coefficient work predates this archive: **Laurent coefficients as an MLC route are not original here**.

Write `G(z)=sum_{n>=1} b_n z^n`, analytic on `|z|<1`. Then `Psi(w)=w-1/2+G(1/w)` and, by Carathéodory's boundary correspondence for the complement of the full connected Mandelbrot set,

\[
\boxed{\mathrm{MLC}\ \Longleftrightarrow\ G\text{ extends continuously to }\overline{\mathbb D}.}
\tag{1.3}
\]

The question is **uniform angular** boundary regularity, not pointwise ray landing at selected tips.

## 2. Exact finite-polynomial criterion, without a renormalization tower

For each integer `N>=1`, define the *rational* trigonometric polynomial

\[
\sigma_N(\theta)
=\sum_{n=1}^{N}\left(1-\frac{n}{N+1}\right)b_n e^{in\theta}.
\tag{2.1}
\]

**Theorem 2.1 (uniform Fejér criterion).** With the normalization (1.1),

\[
\boxed{\mathrm{MLC}\ \Longleftrightarrow\
(\sigma_N)_{N\ge1}\text{ is uniformly Cauchy on }\mathbb R/(2\pi\mathbb Z).}
\tag{2.2}
\]

**Proof.** If MLC holds, (1.3) gives a continuous boundary value `g` for `G`. Its nonnegative-frequency Fourier coefficients are exactly `b_n` and its negative ones vanish. Fejér's theorem says the Cesàro polynomials (2.1) converge uniformly to `g`.

Conversely, if `(sigma_N)` is uniformly Cauchy, it has a continuous uniform limit `g`. For each fixed `|z|<1`, its analytic polynomials `S_N(z)=sum_{n=1}^N (1-n/(N+1)) b_n z^n` converge to `G(z)` by absolute convergence. But `S_N` are also the Poisson extensions of `sigma_N`; uniform convergence on the circle makes them converge to the Poisson extension of `g`. Hence `G` *equals* that Poisson extension inside the disk and extends continuously with boundary values `g`. Apply (1.3). `QED`

**Arithmetic corollary.** Fix integers `k,m,n>=1`. The predicate

\[
P(k,m,n):\quad\sup_{\theta}|\sigma_m(\theta)-\sigma_n(\theta)|<2^{-k}
\tag{2.3}
\]

is *decidable in principle by exact rational polynomial arithmetic*: use `x=cos(theta)`, `y=sin(theta)`, express the squared modulus of the finite trigonometric difference as a polynomial in rational `x,y`, and decide
`forall x,y: (x*x+y*y=1 -> |sigma_m-sigma_n|^2 < 2^(-2k))`
by real-closed-field quantifier elimination. Therefore MLC has the explicit arithmetical upper-bound representation

\[
\boxed{\forall k\ge1\ \exists N\ge1\ \forall m,n\ge N:\ P(k,m,n).}
\tag{2.4}
\]

This is a **Pi^0_3 description**, *not* a decision algorithm for MLC, a complexity-completeness assertion, or a claim that quantifier elimination is practical at large degrees. Unlike the marked-width reduction, its finite tests require no hypothetical canonical sheet transport; the infinite uniform quantifier remains the unsolved problem.

## 3. The critical l2-to-l1 energy gap

Define dyadic packet energies, for `j>=0`,

\[
B_j^2=\sum_{2^j\le n<2^{j+1}} n|b_n|^2.
\tag{3.1}
\]

Gronwall's area theorem for the normalized exterior univalent map gives

\[
\sum_{n\ge1}n|b_n|^2
=1-\frac{\operatorname{Area}(M)}{\pi}\le1.
\tag{3.2}
\]

Thus `sum_j B_j^2 <= 1` automatically. But **square-summable packet energy is not a uniform boundary-continuity result**: the missing upgrade is from `l2` over scales to enough `l1` or signed cancellation to control the supremum over all angles.

**Theorem 3.1 (a quantitative sufficient route).** If

\[
\boxed{\sum_{j\ge0} B_j<\infty,}
\tag{3.3}
\]

then MLC holds.

**Proof.** For every dyadic block, Cauchy--Schwarz gives

\[
\sum_{2^j\le n<2^{j+1}}|b_n|
\le B_j\left(\sum_{2^j\le n<2^{j+1}}\frac1n\right)^{1/2}
\le B_j.
\]

Consequently (3.3) implies absolute, uniform convergence of the boundary series `sum b_n exp(in theta)`, hence the extension in (1.3). `QED`

**Sharp functional-analytic negative control.** Let `a_n=1/(n log n)` for `n>=2` and `A(z)=sum_{n>=2} a_n z^n`. Then `sum n|a_n|^2=sum 1/(n log^2 n)<infinity`, but `A(r)` increases to infinity as `r up-arrow 1` because `sum a_n` diverges. Thus the `H^(1/2)`/area-energy hypothesis alone does not force continuous boundary values for *arbitrary analytic functions*. This toy series is **not** an exterior univalent Mandelbrot map and is **not** a counterexample to MLC; it isolates the exact analytic logical gap.

The condition (3.3) is **sufficient, not known necessary**, and may be too strong for the actual `M`. The exact equivalence (2.2), which permits cross-frequency cancellation, is the more flexible target.

## 4. No algebraic decay of the Mandelbrot area tail

Put `E_N=sum_{n>N} n|b_n|^2`; by (3.2), `E_N -> 0`. Bielefeld--Fisher--von Haeseler (1993) also established that **if** the Laurent boundary series extends continuously, its boundary function is *not Hölder continuous of any positive exponent*. That published input has not been re-proved in this note.

**Theorem 4.1 (conditional-on-published-theorem, but unconditional in MLC).** Assuming the Bielefeld--Fisher--von Haeseler non-Hölder statement in the cited meaning, for **every** `alpha>0`,

\[
\boxed{E_N\ne O(N^{-\alpha})\quad\text{as }N\to\infty.}
\tag{4.1}
\]

Equivalently, the area upper bounds

\[
A_N=\pi\left(1-\sum_{n=1}^{N}n|b_n|^2\right)
\]

satisfy `A_N-Area(M)=pi E_N`, and this error **cannot have a global algebraic convergence rate of any positive power**.

**Proof.** Suppose `E_N<=C N^(-alpha)` eventually, with `alpha>0`. Then for all large `j`,

\[
B_j^2\le E_{2^j-1}\le C'2^{-\alpha j},
\qquad B_j\le C''2^{-\alpha j/2}.
\tag{4.2}
\]

For `0<beta<min(alpha/2,1)`, the series `sum_j 2^(beta j) B_j` converges. For angular distance `delta`, use `|e^{in theta}-e^{in phi}|<=min(2,n delta)` and weighted Cauchy--Schwarz on each block to obtain

\[
|g(\theta)-g(\phi)|\le
C_\beta\delta^\beta\sum_j 2^{\beta j}B_j<\infty\cdot\delta^\beta.
\tag{4.3}
\]

The same block bound without `n^beta` gives absolute convergence of `sum b_n exp(in theta)`, so `g` is a *continuous boundary extension* and (4.3) makes it Hölder. Both conclusions together contradict the published non-Hölder statement. Hence the premise is false for every positive `alpha`. `QED`

**Interpretation.** This rules out a power-law decay target for `E_N` or the dyadic packet energies. It does **not** rule out summable *subpower* packet energy, compensated oscillations, or uniform Fejér convergence. It also does not independently establish the originality of this corollary: a specialist literature check is required.

### Corollary 4.2 — the exact critical Sobolev threshold

Interpreting the analytic boundary trace of `G` as a periodic distribution, the area theorem and Bielefeld--Fisher--von Haeseler's published conditional non-Hölder theorem together give the unconditional regularity classification

\[
\boxed{G|_{S^1}\in H^{1/2}(S^1),\qquad
G|_{S^1}\notin H^{1/2+\varepsilon}(S^1)
\quad\text{for every }\varepsilon>0.}
\tag{4.4}
\]

Equivalently, **the exact coefficient-summability barrier** is

\[
\boxed{\sum_{n\ge1}n|b_n|^2<\infty,
\qquad\sum_{n\ge1}n^{1+2\varepsilon}|b_n|^2=\infty
\ \text{for every }\varepsilon>0.}
\tag{4.5}
\]

**Proof.** The first weighted sum is finite by (3.2), and the standard Fourier definition of periodic Sobolev spaces gives the `H^(1/2)` trace. Suppose the second sum were finite for some `epsilon>0`. Choose `0<beta<min(epsilon,1)`. Weighted Cauchy--Schwarz yields

\[
\sum_{n\ge1}n^\beta|b_n|
\le\left(\sum n^{1+2\varepsilon}|b_n|^2\right)^{1/2}
\left(\sum n^{2\beta-1-2\varepsilon}\right)^{1/2}
<\infty.
\tag{4.6}
\]

Thus `sum b_n exp(in theta)` converges uniformly, and the elementary difference bound `|exp(in theta)-exp(in phi)| <= C_beta (n |theta-phi|)^beta` makes its limit Hölder `beta`. This contradicts the Bielefeld--Fisher--von Haeseler theorem. Hence no `epsilon>0` works. `QED`

This **critical** `H^(1/2)` membership is not a proof of MLC: periodic `H^(1/2)` does not embed into `C^0`. The preceding finite-Fejér criterion precisely asks whether *this particular* critical trace nevertheless has a continuous representative. The equivalence between (4.4) and (4.5) is classical Fourier--Sobolev theory; novelty/priority of applying it to `M` has not been independently established.

### Theorem 4.3 — a universal inverse-logarithmic *best-approximation* obstruction

The source paper's concrete landing-angle witness (Bielefeld--Fisher--von Haeseler, 1988 MPIM preprint pp. 14--15, published 1993) yields a **strictly stronger, quantitative restriction** than the abstract non-Hölder conclusion. This is a deduction using the classical Bernstein inequality, not a claim of new priority. The source establishes the following exact boundary ray landings without requiring general MLC:

\[
\theta_m=2\pi\left(\frac13+\frac1{4^m-1}\right),\quad
\theta_\infty=\frac{2\pi}{3},\quad
c_m=-1+\frac14 e^{2\pi i/m},\quad
c_\infty=-\frac34.
\tag{4.7}
\]

Here the external ray of angle `theta_m` lands at `c_m`. Assuming MLC, the continuous boundary parametrization `f(theta)=Psi(e^{i theta})` therefore satisfies, for `m>=2`,

\[
|f(\theta_m)-f(\theta_\infty)|
=\tfrac12\sin(\pi/m)\ge\frac1m,
\qquad
|\theta_m-\theta_\infty|=\frac{2\pi}{4^m-1}.
\tag{4.8}
\]

Let `T_N` be the space of **arbitrary complex trigonometric polynomials of degree at most N**, and let `N>=2`. Define `m_N=ceil(log_2 N)+8`. Then

\[
\boxed{\inf_{Q\in T_N}\|f-Q\|_{L^\infty(S^1)}
\ge\frac1{4(\lceil\log_2 N\rceil+8)}.}
\tag{4.9}
\]

In particular, if MLC is true and `g(theta)=sum_{n>=1}b_n exp(in theta)` is the continuous boundary value of `G`, its *specific Fejer approximants* satisfy

\[
\boxed{\|g-\sigma_N\|_\infty
\ge\frac1{4(\lceil\log_2 N\rceil+8)}\quad(N\ge2).}
\tag{4.10}
\]

**Proof.** The Mandelbrot set is contained in `|c|<=2`, so `||f||_infty<=2`. Let `Q in T_N` and put `e=||f-Q||_infty`. If `e>=1`, (4.9) is immediate. Otherwise `||Q||_infty<=3`. Bernstein's inequality for trigonometric polynomials gives `||Q'||_infty<=3N`. Choose `m=m_N`. Since `4^m>=65536*N^2` and `2*pi<65535/10000`,

\[
\delta_m:=|\theta_m-\theta_\infty|
=\frac{2\pi}{4^m-1}<\frac1{10000N^2}.
\]

The elementary inequality `ceil(log_2 N)<=N` implies `m<=N+8<=5N`. By the triangle inequality and (4.8),

\[
2e\ge |f(\theta_m)-f(\theta_\infty)|
-|Q(\theta_m)-Q(\theta_\infty)|
\ge \frac1m-3N\delta_m
>\frac1m-\frac3{10000N}
\ge\frac1m-\frac{15}{10000m}>
rac1{2m}.
\]

Thus `e>1/(4m)`, which implies (4.9). For the Fejer consequence, use the degree-`N` trigonometric polynomial `Q_N(theta)=exp(i theta)-1/2+sigma_N(-theta)`, whose uniform error to `f(theta)` is exactly `||g-sigma_N||_infty`. `QED`

This theorem excludes **any faster-than-inverse-logarithmic uniform accuracy** for degree-limited spectral reconstructions *if MLC holds*; it does **not** establish the matching upper bound or prove MLC. The ray-landing input (4.7) is imported from the 1988/1993 source, and the approximation argument is standard; the precise combination is new *to this Loops track*, with external priority unverified. It shows why a target such as uniform Fejer error `O(N^(-alpha))` is not merely difficult but impossible.

## 5. A rigorous finite-coefficient spectral microscope, away from the boundary

The disk `|c|<=1/4` lies inside `M`: under `f_c(z)=z^2+c`, the closed disk `|z|<=1/2` maps into itself, and contains the critical point `0`. Thus `Area(M)>=pi/16`; combining with (3.2),

\[
E_N\le\frac{15}{16}-S_N,
\qquad S_N=\sum_{n=1}^{N}n|b_n|^2.
\tag{5.1}
\]

For `|w|>=R>1`, let `P_N(w)=w-1/2+sum_{n=1}^N b_n w^(-n)`. Cauchy--Schwarz and the geometric series give a *global, rigorous, positive-potential* error:

\[
\boxed{\left|\Psi(w)-P_N(w)\right|^2
\le\left(\frac{15}{16}-S_N\right)
\frac{R^{-2(N+1)}}{(N+1)(1-R^{-2})}.}
\tag{5.2}
\]

No extrapolation, floating-point dynamics, or local connectivity assumption enters (5.2). For the five authenticated coefficients (1.2), exact fraction arithmetic yields

\[
S_5=\frac{201701}{1048576},\qquad
\frac{15}{16}-S_5=\frac{781339}{1048576},
\tag{5.3}
\]

and at `R=2` the *squared* remainder is at most

\[
\boxed{\left|\Psi(w)-P_5(w)\right|^2\le
\frac{781339}{19327352832},\quad |w|\ge2.}
\tag{5.4}
\]

This is useful for certified high-potential external-plane calculations, **not** the uniform `R downarrow 1` claim needed for MLC: the denominator `1-R^(-2)` in (5.2) degenerates. The area theorem alone cannot seal that gap.

A separate finite exact unit-circle consistency check is

\[
\sigma_1=\tfrac1{16}e^{i\theta},\quad
\sigma_2=\tfrac1{12}e^{i\theta}-\tfrac1{12}e^{2i\theta},\quad
\boxed{\|\sigma_2-\sigma_1\|_\infty=\tfrac5{48}.}
\tag{5.5}
\]

This one finite difference is **not evidence of infinite uniform convergence**.

## 6. Experiment contract and genuine next theorem

Run from the repository root:

```sh
python research/independent_audits/verify_mlc_boundary_spectrum.py
```

The checker uses only `fractions.Fraction` and the five published coefficients to verify (5.3)--(5.5) and rational squared error budgets at `R=5/4, 3/2, 2`. It does not derive the published coefficients, test infinite quantifiers, calculate Fejér sup norms at large N, prove the Bielefeld--Fisher--von Haeseler non-Hölder theorem, or certify the area theorem.

A real advance would be **one of**:

- prove the exact Fejér uniform-Cauchy statement (2.2) using new coefficient cancellation/number-theoretic dynamics;
- prove a non-power-law but summable dyadic packet majorant `sum_j B_j<infinity`;
- find and certify a weaker, angle-uniform cancellation criterion that proves (2.2) while allowing `sum_j B_j=infinity`.

A finite table of apparent convergence, or a bound only for `R>1` fixed, does **not** close MLC. Any new theorem must prove an estimate uniform over `theta` **and** all sufficiently large finite indices.

## 7. Position versus the existing Loops research

The archive's `H1_MARKED_CONSTRUCTION`, `H2_CALIBRATION`, `H3_COERCIVITY`, `H4_RIGIDITY`, and `UNIVERSAL_PROTECTED_TOWER_CLOSURE` remain **open**. No ledger node is promoted. This note does not repair KKL native prime-end markings, sheet groupoids or Wave returns; it **bypasses those as hypotheses** and transfers the open difficulty to a rigorously equivalent uniform spectral Cauchy problem. It complements, rather than invalidates, the marked-width program. The Fejér/Besov tools are classical and the Bielefeld--Fisher--von Haeseler and Ewing--Schober results predate the archive. New priority claims require specialist review.