# A cubic renewal-clock obstruction, with an explicit interval realization

**Date:** 2026-11-23. **Source snapshot:** `ae21998d70f5f92f4a175d297c7960e94653328d`.

This note connects the archive's complete clone adjacency to a nearly periodic
renewal chain and then constructs an actual piecewise affine interval map having
exactly that stationary symbolic process. It proves the sharp leading constant
for the non-Perron spectral modulus:

\[
 D^3\left(1-\frac{r_n}{t_n}\right)\longrightarrow\frac{\pi^2}{2},
 \qquad D=2n+\frac92.
\tag{1}
\]

Here `t_n` is the positive eigenvalue and `r_n` is the largest modulus of any
other eigenvalue of the **full** row-source adjacency in `CloneGraph.lean`.
The previous [strict-spectrum audit](clone_strict_spectrum_and_no_uniform_expansion_20261107.md)
proved gap collapse with a coarser bound and explicitly left the faster observed
rate unresolved. Equation (1), the probability normalization, and the interval
correlation formula below are additional results for that specified family.

**Evidence status.** The new analytic and measure-theoretic arguments in this note
are written proofs, not Lean-kernel proofs. Existing Lean modules establish the
actual adjacency's eigenvalue equation and strict Perron dominance. The companion
[verifier](verify_clone_renewal_clock.py) checks the new finite algebra in exact
integer quotient rings and, optionally, computes high-precision diagnostic values.
Neither finite regression nor numerical asymptotics substitutes for the proofs.

**Novelty boundary.** Perron normalization, renewal processes, and cubic mixing
in necklace chains are established mathematics. Parry [1], Shallit--Yamron [2],
and Wilmer [3] are relevant predecessors. The contribution claimed here is a
specific additional derivation and explicit realization for this archive's graph.
No claim of worldwide priority is made. This interval map is constructed below;
it is not identified with an actual quadratic polynomial, a native KKL tree
operator, or a protected renormalization tower.

## 1. The exact matrix and both directions of its spectral correspondence

Fix an integer `n >= 0`, put `d = 2n+5`, and use vertices `0,...,d-1`.
There is an edge `i -> i+1 mod d` for every vertex and the additional edge
`n -> n+2`. Let `A` be this 0/1 row-source adjacency.

The existing [complex polynomial proof](../../formalization/weighted/FullClonePolynomial.lean)
shows that every nonzero complex eigenvector with eigenvalue `z` satisfies

\[
 z^d=z+1.
\tag{2}
\]

The converse also concerns the actual rows. A root of (2) is neither `0` nor `-1`.
Define

\[
 v_i(z)=
 \begin{cases}
 z^i,&0\le i\le n,\\
 z^i/(z+1),&n+1\le i\le d-1.
 \end{cases}
\tag{3}
\]

For an ordinary non-wrap row, `v_(i+1)=z v_i`. At the shortcut row,
`v_(n+1)+v_(n+2)=z^(n+1)=z v_n`. At the wrap row,
`z v_(d-1)=z^d/(z+1)=1=v_0`. Thus `A v(z)=z v(z)` and `v_0=1`.
Consequently the matrix eigenvalues are exactly the roots of (2), without
needing an unproved characteristic-determinant identification.

There is a unique positive root `t` in `(1,2)`: the function `x^d-x-1`
changes sign between 1 and 2 and has positive derivative on `[1,infinity)`;
it is negative on `[0,1]`. The vector `h=v(t)` is strictly positive.
The archive's [strict-dominance theorem](../../formalization/weighted/FullCloneStrictGap.lean)
shows that all other eigenvalues have modulus smaller than `t`.
The general simplicity and dominant-root facts for `x^d-x-1` already appear
in Shallit--Yamron [2]; the identification with these particular rows is a
separate obligation discharged by the row computations above and existing Lean.

## 2. Probability normalization and the renewal clock

Define an actual stochastic matrix by

\[
 P_{ij}=\frac{A_{ij}h_j}{t h_i}.
\tag{4}
\]

Every entry is nonnegative and each row sums to 1 by `Ah=th`.
Writing `H=diag(h)`, one has `P=t^(-1) H^(-1) A H`; this proves
the precise spectral transfer, including multiplicities. It is a diagonal
similarity, not an assertion that row normalization by out-degree has this spectrum.

All rows except `n` are deterministic. At `n` the probabilities are

\[
 a=P_{n,n+1}=\frac1{1+t}=t^{-d},\qquad
 b=P_{n,n+2}=\frac t{1+t}=t^{-(d-1)},\qquad a+b=1.
\tag{5}
\]

The first return to `n` therefore has length `d` with probability `a` and
length `d-1` with probability `b`. The choices at successive returns are
independent by the Markov construction. Let

\[
 m=ad+b(d-1)=d-b,\qquad \sigma^2=ab.
\tag{6}
\]

Each return visits every vertex once except the skipped vertex `n+1`, which
is visited with probability `a`. The unique stationary distribution is

\[
 \pi_i=\begin{cases}a/m,&i=n+1,\\1/m,&i\ne n+1.\end{cases}
\tag{7}
\]

This can be checked directly: at `n+1` the incoming mass is `a/m`; at `n+2`
the incoming masses are `a/m` and `b/m`; every other vertex has one incoming
deterministic predecessor. Their sum is `[(d-1)+a]/m=1`.

The stationary entropy rate, with natural logarithms, is exactly

\[
 h(P)=\frac{-a\log a-b\log b}{m}=\log t.
\tag{8}
\]

The last identity uses the two exact powers of `t` in (5). This is the
classical Parry normalization [1]. It also maximizes entropy among stationary
Markov chains supported on this adjacency: for any such chain `Q` with
stationary law `nu`, the average of `log P_ij=-log t+log h_j-log h_i`
is `-log t`, since the last two terms cancel by stationarity. Nonnegativity
of each row's relative entropy gives

\[
 h(Q)=\log t-\sum_i\nu_i\,\mathrm{KL}(Q_i\Vert P_i)\le\log t.
\]

This proves an exact graph-process statement. It does not prescribe a measure
on a quadratic Julia set or make a combinatorial path equidistributed there.

## 3. Which roots actually determine the spectral gap?

The next argument avoids assuming that the numerically nearest conjugate roots
are the subleading ones.

For `0 <= theta < 2pi/3`, consider

\[
 F(r,\theta)=r^{2d}-r^2-1-2r\cos\theta,\qquad r\ge1.
\]

At `r=1` its value is `-1-2 cos theta<0`, it tends to infinity with `r`, and

\[
 F_r=2d r^{2d-1}-2r-2\cos\theta
 \ge2(d-1)r-2>0.
\tag{9}
\]

There is therefore a unique root `r(theta)>1`, smooth in the open angular
interval, with `r(0)=t`, limit `r(2pi/3)=1`, and `r'(theta)<0`
for `0<theta<2pi/3`. Conversely every root `z=r exp(i theta)` of (2)
with `r>1` and principal argument in the upper half-plane satisfies this
equation and lies in that interval: if `theta>=2pi/3`, the monotonicity in
(9) and `F(1,theta)>=0` exclude a solution with `r>1`.

Put

\[
 \phi(\theta)=\operatorname{Arg}(1+r(\theta)e^{i\theta}),\qquad
 K(\theta)=d\theta-\phi(\theta).
\]

For `0<theta<2pi/3`, one has `0<phi(theta)<theta`. Differentiating on
this continuous branch yields

\[
 \phi'(\theta)=
 \frac{r'\sin\theta+r^2+r\cos\theta}{1+r^2+2r\cos\theta}<1.
\tag{10}
\]

Indeed `r'<0`, and `1+r cos theta>1-t/2>0` because `r<=t<2`.
Hence `K'>d-1>0`. At the endpoints,

\[
 K(0)=0,\qquad K(2\pi/3)=\frac{(2d-1)\pi}{3}>2\pi
 \quad(d\ge5).
\tag{11}
\]

The modulus equation and phase equation `K(theta)=2pi k` together are
exactly (2). There is a unique solution `theta_1` of `K(theta)=2pi`.
Every other upper-half-plane root with modulus greater than 1 has `k>=2`
and therefore a larger angle and smaller modulus. Roots with modulus at
most 1 are also smaller than `r(theta_1)>1`. Negative real roots with
modulus greater than 1 are excluded by the same modulus argument.

Thus the **unique subleading pair** is

\[
 z_1=r(\theta_1)e^{i\theta_1},\quad\overline{z_1},\qquad
 r_n=r(\theta_1),\qquad 1<r_n<t_n.
\tag{12}
\]

This conclusion holds for every clone delay, not merely asymptotically.

## 4. The sharp cubic asymptotic

Write `D=d-1/2`, `epsilon=1/D`, `L=log 2`, and `A_k=L+2pi i k`.
For roots near 1 set `w=log z`, with the branch near zero. The identity

\[
 1+e^w=2e^{w/2}\cosh(w/2)
\]

converts (2), with the selected integer phase `k`, into

\[
 u=A_k+\log\cosh(\epsilon u/2),\qquad u=Dw.
\tag{13}
\]

Here the analytic logarithm is the one equal to zero at `cosh(0)=1`.
At `(epsilon,u)=(0,A_k)` the derivative with respect to `u` of
`u-A_k-log cosh(epsilon u/2)` equals 1. The complex analytic implicit
function theorem supplies a unique analytic solution near `epsilon=0`.
The equation is even in `epsilon`, so uniqueness makes `u(epsilon)`
even. Since `log cosh x=x^2/2+O(x^4)`, comparison of Taylor coefficients
gives the genuine analytic expansion, with a remainder bounded for each fixed `k`,

\[
 u=A_k+\frac{A_k^2}{8}\epsilon^2+O(\epsilon^4),\qquad
 w_k=\frac{A_k}{D}+\frac{A_k^2}{8D^3}+O(D^{-5}).
\tag{14}
\]

For `k=0`, the branch is real with `w_0>0` for sufficiently large `D`,
so uniqueness identifies `exp(w_0)=t`. For `k=1`, its real part is
positive and imaginary part lies in `(0,2pi/3)` for sufficiently large
`D`. In that neighborhood `log(1+exp w)=L+w/2+log cosh(w/2)` is the
principal logarithm, so (13) has phase `K=2pi`. Section 3 therefore
identifies this branch with the actual subleading root `z_1`; no root
selection is inferred merely from numerical proximity.

Taking real parts in (14) and subtracting gives

\[
 \log\frac{t}{r_n}
 =\frac{\pi^2}{2D^3}+O(D^{-5}),
 \qquad
 \gamma_n:=1-\frac{r_n}{t}
 =\frac{\pi^2}{2D^3}+O(D^{-5}).
\tag{15}
\]

The second expansion follows from `1-exp(-x)=x+O(x^2)` and `x=O(D^-3)`.
In the original delay variable, `n^3 gamma_n -> pi^2/16`. The absolute
adjacency gap also has `D^3(t-r_n)->pi^2/2`, because `t->1`; its remainder
need not be `O(D^-5)` after multiplying by `t`.

Meanwhile (14) at `k=0` gives `log t=L/D+O(D^-3)`. Thus entropy per step
decays on scale `D^-1`, whereas the slowest spectral relaxation exponent
decays on scale `D^-3`. Knowing positive entropy or graph primitivity
does not control relaxation on the entropy time scale.

In the renewal variables of (6), the same proved limit reads

\[
 \gamma_n\sim\frac{2\pi^2\operatorname{Var}(\tau_n)}
 {(\mathbb E\tau_n)^3}.
\]

Indeed `m/D -> 1` and `sigma^2=ab -> 1/4`, so this is an algebraic
consequence of (15). It identifies the small variance of the return
clock, relative to its growing mean, as the quantity controlling this
family's slow phase relaxation. This is a statement about the specified
renewal law, not an assertion for arbitrary return-time processes.

### Expansion per delay block and phase damping use different clocks

The distinction persists after the archive's natural `n`-step normalization.
As `n` tends to infinity,

\[
 t_n^n\longrightarrow\sqrt2,\qquad
 \left(\frac{r_n}{t_n}\right)^n
 =1-\frac{\pi^2}{16n^2}+o(n^{-2})\longrightarrow1.
\tag{15a}
\]

The first limit follows from `n log t_n -> (log 2)/2`; the second follows
by multiplying `log(t_n/r_n)=pi^2/(16n^3)+o(n^-3)` by `n` and
exponentiating. For every fixed real `s>=0`,

\[
 \left(\frac{r_n}{t_n}\right)^{\lfloor s n^3\rfloor}
 \longrightarrow \exp\!\left(-\frac{\pi^2s}{16}\right).
\tag{15b}
\]

Thus the same delay block has expansion bounded away from 1 and a
phase-damping factor tending to 1. On the interval realization in Section 6,
`(T_n^n)'=t_n^n` on every affine cylinder, while the normalized observable's
correlation modulus after those `n` physical iterations tends to 1.
Equation (15b) describes its envelope on the longer cubic clock; the
complex correlation itself still oscillates and is not asserted to have
that real limit. These exact graph and interval-map examples obstruct an
inference from normalized clone expansion alone to uniform mixing. Any
response or coercivity application still requires its own comparison
theorem. These examples provide no native KKL width comparison and
discharge no H2 or H3 premise.

## 5. A nonreversible mixing lower bound, with its exact scope

No reversible spectral-gap theorem is used here. Let `lambda=z_1/t` and
let `g_i=v_i(z_1)/h_i`, so `Pg=lambda g`. Stationarity gives
`pi g=pi Pg=lambda pi g`; since `lambda !=1`, one has `pi g=0`.
Normalize `max_i |g_i|=1` and choose a maximizing state `x`. For every
integer `q>=0`,

\[
 |\lambda|^q
 =\left|\sum_y(P^q(x,y)-\pi_y)g_y\right|
 \le2\|P^q(x,\cdot)-\pi\|_{\mathrm{TV}}.
\tag{16}
\]

Consequently, for fixed `0<eta<1/2`, the worst-state mixing time satisfies

\[
 t_{\rm mix}(\eta)
 \ge \frac{\log(1/(2\eta))}{\log(t/r_n)},\qquad
 \liminf_{n\to\infty}\frac{t_{\rm mix}(\eta)}{D^3}
 \ge\frac{2}{\pi^2}\log\frac1{2\eta}.
\tag{17}
\]

Integer-valued mixing time may be bounded by the ceiling of the first right
side. This proves a cubic **lower bound**; it does not assert a matching
upper bound, an exact total-variation profile, or a cutoff theorem.

Wilmer [3] proves Brownian-circle profiles for necklace chains built from a
fixed bead, with time normalization `[N+(mu-1)M]^3/(sigma^2 M)`.
Our chain has `N=d-1` links, one bead, and bead passage times 1 and 2 with
probabilities `b` and `a`. Its mean passage is `1+a`, so that normalization
is exactly `m^3/(ab)`, asymptotic to `4D^3`. This explains the agreement
with the classical phase-diffusion mechanism. However `a=1/(1+t_n)`
depends on `n`, whereas Wilmer's theorem states a fixed-bead hypothesis.
We do not import her full profile without proving the necessary uniform
extension. The direct arguments in Sections 3--5 do not need it.

## 6. An actual interval map, invariant measure, and observable

The preceding stochastic model has a concrete deterministic realization.
This construction makes every new step from matrix to actual real dynamics
explicit, while keeping its distinction from the archive's quadratic maps.

Let `s_0=0`, `s_i=sum_(j<i) h_j`, `S=sum_j h_j`, and
`I_i=[s_i,s_(i+1))`. These are actual half-open intervals partitioning `[0,S)`.
Define a Borel map `T:[0,S)->[0,S)` by

\[
 T(x)=s_{\operatorname{next}(i)}+t(x-s_i)\quad(x\in I_i),
 \qquad \operatorname{next}(i)=\begin{cases}i+1,&i<d-1,\\0,&i=d-1.
 \end{cases}
\tag{18}
\]

At each ordinary row `t h_i=h_(i+1)`, at the shortcut row
`t h_n=h_(n+1)+h_(n+2)`, and at the wrap row `t h_(d-1)=h_0`.
Thus `T(I_i)` is exactly `I_(i+1)` at ordinary rows, exactly the adjacent
union `I_(n+1) union I_(n+2)` at the shortcut row, and exactly `I_0` at
the wrap row. This proves the transition graph from the actual image
intervals. The map is affine on each `I_i` and generally discontinuous
at partition seams; no continuity claim is made.

Define a probability measure by the piecewise constant density

\[
 \frac{d\mu}{dx}=\frac{\pi_i}{h_i}\quad(x\in I_i).
\tag{19}
\]

For a Borel set `B subset I_j`, every allowed incoming branch has a
preimage of Lebesgue length `|B|/t`. Therefore

\[
 \mu(T^{-1}B)
 =\frac{|B|}{t}\sum_{i:A_{ij}=1}\frac{\pi_i}{h_i}
 =|B|\frac{\pi_j}{h_j}=\mu(B),
\tag{20}
\]

where the middle equality is precisely `pi P=pi`. Finite additivity over
the partition proves invariance on every Borel set.

More strongly, for every admissible itinerary `i_0,...,i_q`, the cylinder
`I_(i_0) intersect T^-1 I_(i_1) intersect ... intersect T^-q I_(i_q)`
maps affinely and bijectively to `I_(i_q)` under `T^q`, with slope `t^q`.
This follows inductively by taking the indicated inverse affine branch.
It has length `h_(i_q)/t^q` and consequently

\[
 \mu[i_0,\ldots,i_q]
 =\pi_{i_0}\frac{h_{i_q}}{t^q h_{i_0}}
 =\pi_{i_0}\prod_{j=0}^{q-1}P_{i_j,i_{j+1}}.
\tag{21}
\]

Inadmissible cylinders are empty. This proves the entire stationary Markov
law of the partition observation, not merely equality of one-step averages.

Now set `G(x)=g_i` on `I_i`, with `g` from Section 5. Equation (21) gives
the exact physical correlation identity

\[
 \int\overline{G(x)}G(T^q x)\,d\mu(x)
 =\sum_i\pi_i\overline{g_i}(P^qg)_i
 =\lambda^q\sum_i\pi_i|g_i|^2,
 \qquad\int G\,d\mu=0.
\tag{22}
\]

After normalizing `G` in `L^2(mu)`, the correlation modulus is
`(r_n/t_n)^q`. Thus the actual interval map, its specified invariant
measure, and its specified bounded observable exhibit precisely the cubic
relaxation scale proved above. This is a complete written realization
for (18)--(19), with no appeal to the geometry of a native KKL surface.

## 7. Contract for a different physical application

To apply this result to an independently given mathematical system, discharge
the relevant route in the following table. Defining the interval map in (18)
does not discharge these obligations for another map.

| Transition | Exact required evidence | Consequence licensed |
|---|---|---|
| Native finite operator to `A` | A bijection of actual oriented edges with these vertices, equality of every traversal multiplicity, the same row-source convention and the same time unit | Permutation similarity and the adjacency spectrum |
| Adjacency to stochastic kernel | The physical kernel is exactly (4), with the same positive eigenvector, or is conjugate to it by a specified bijection | The normalized spectrum and Markov mixing lower bound |
| Deterministic system to Markov observation | A measurable partition/address, an invariant probability measure, and the **all-finite-cylinder** identity (21) for its actual iterates | The correlation formula (22) for the pulled-back eigen-observable |
| Induced return to physical time | A proved constant return time, or the actual roof function and its joint law with the branches | A valid time conversion; a mean return time alone is insufficient |
| Correlation or graph growth to width | Quantitative comparison to the named conformal response or width on the same domains and markings | Only the comparison's stated estimate; no such comparison is supplied here |

In particular, a semiconjugate phase clock, an edge count, or a one-step
conditional distribution does not by itself prove the finite-cylinder law.
The route to a geometric width estimate remains independent. No H1--H4,
UPTCR, rigidity, or MLC gate changes status as a result of this note.

### A fixed graph does not determine a mixing rate

The stochastic-identification premise is essential even when the graph has
already been identified exactly. Fix one delay `n`, hence one adjacency `A`
and one dimension `d`. For any `0<beta<1`, keep every ordinary transition
deterministic and assign probabilities `1-beta` and `beta` to
`n -> n+1` and `n -> n+2`, respectively. Denote this chain by `P_beta`.
Its 0/1 support adjacency is **the same `A` for every beta**; both return
lengths `d` and `d-1` occur, so the chain is irreducible and aperiodic.
The stationary distribution, checked by the same incoming-mass calculation
as (7), is

\[
 \pi_i^{(\beta)}=
 \begin{cases}
 (1-\beta)/(d-\beta),&i=n+1,\\
 1/(d-\beta),&i\ne n+1.
 \end{cases}
\tag{23}
\]

Start at any vertex `x` and fix an integer `q>=0`. On the event that no
shortcut is used during the first `q` steps, the endpoint is the ordinary
cycle position `x+q mod d`. Along this unique history the shortcut vertex
is encountered some number `k<=q` of times. The event has probability
`(1-beta)^k >= (1-beta)^q`. Taking that endpoint as a singleton event and
using `max_i pi_i^(beta)=1/(d-beta)` proves

\[
 \|P_\beta^q(x,\cdot)-\pi^{(\beta)}\|_{\mathrm{TV}}
 \ge (1-\beta)^q-\frac1{d-\beta}
 \ge 1-q\beta-\frac1{d-\beta}.
\tag{24}
\]

The final inequality is Bernoulli's inequality. For every fixed horizon
`q`, the lower bound tends to `1-1/d` as `beta` decreases to zero.
Consequently, for every fixed `0<eta<1-1/d`, the mixing times
`t_mix,beta(eta)` are unbounded over `0<beta<1`, **with dimension and
support adjacency held fixed**. Each individual chain does mix; there is
no uniform bound determined by this adjacency alone.

The Parry kernel in (4) selects the particular value `beta=t/(1+t)`.
Thus equality of counted edge rows establishes the adjacency theorem but
does not select its stochastic normalization or its correlation law.
Equation (24) is an independent negative test of that transition, not a
mutation of the graph or its characteristic polynomial. It does not
alter the explicitly specified measure (19) on the constructed interval
map; a different physical measure would need its own cylinder-law proof.

## 8. Reproduction and related work

From the repository root:

```bash
python research/independent_audits/verify_clone_renewal_clock.py
# Optional numerical diagnostics require mpmath 1.3.0 or compatible:
python research/independent_audits/verify_clone_renewal_clock.py --numerics
```

The default checks perform exact algebra modulo `x^d-x-1` at finitely many
declared delays. They independently check all adjacency eigenvector rows,
all stochastic-similarity rows, stationary weights, and the mean-return
normalization, and reject a changed shortcut. They are regression tests,
not proofs of universal quantifiers. The optional output uses 90-digit
arithmetic and labels every numerical asymptotic value as diagnostic.

1. **William Parry**, *Intrinsic Markov chains*, Transactions of the AMS
   **112** (1964), 55--66. [DOI](https://doi.org/10.1090/S0002-9947-1964-0161372-1).
   Classical Perron/entropy normalization; (4)--(8) are an explicit
   application, not a newly discovered general construction.
2. **J. O. Shallit and J. P. Yamron**, *On Linear Recurrences and Divisibility
   by Primes*, Fibonacci Quarterly **22** (1984), 366--368.
   [Primary PDF](https://www.fq.math.ca/Scanned/22-4/shallit2.pdf), theorem
   on pp. 367--368. Contains simplicity and positive-root dominance for
   `x^d-x-1`; those general algebraic facts predate this archive.
3. **Elizabeth L. Wilmer**, *A local limit theorem for a family of
   non-reversible Markov chains*, Journal of Theoretical Probability **16**
   (2003), 751--770; [arXiv:math/0205189](https://arxiv.org/abs/math/0205189),
   [primary PDF](https://arxiv.org/pdf/math/0205189), Theorems 1--2.
   Supplies the established necklace-chain and Brownian-circle context.

Primary-source and archive searches were performed on 2026-11-23. Failure
to find an identical statement in a bounded search does not prove priority.
The proofs above are offered for independent specialist review.

Prepared with OpenAI GPT-6 Astra Pro assistance for derivation, literature
comparison, separate adversarial review and reproducible verification.
No human specialist review was performed during this preparation.
