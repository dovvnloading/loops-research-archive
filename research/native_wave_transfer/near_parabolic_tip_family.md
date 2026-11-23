# Primitive Chebyshev tips at the real period-three parabolic root

Let $f_c(z)=z^2+c$. For every $p=3n$ with $n\ge6$, there is a real parameter $c_p\in(-7/4,-1.74)$ and a number $e_p>0$ for which the critical orbit of the return $G=f_{c_p}^{p}$ is

$$
                 0\longmapsto -e_p\longmapsto e_p\longmapsto e_p .
$$

The critical point of the original quadratic first enters a cycle at iterate $p+1$, and that cycle has least period $p$. The closed interval $I_p=[-e_p,e_p]$ has $p$ pairwise disjoint images at times $0,\ldots,p-1$. Each closed half of $I_p$ maps monotonically onto the whole interval under $G$. Every point of $I_p$ therefore first returns at time $p$.

The parameters decrease to $-7/4$ as $p$ increases through these multiples of three. They satisfy the explicit estimates

$$
 \frac1{25}\ \le\ (p-6)^2(c_p+7/4)\ \le\ 900 .
$$

In the complex plane $I_p$ is the component containing zero of $G^{-1}(I_p)$. There is an explicit open neighborhood of $I_p$ on which each interior point of the interval has exactly two distinct preimages. These assertions, the orbit statements, the parameter ordering and the bounds above are proved in Lean. An application of published complex dynamics theorems below gives a primitive quadratic-like restriction of $G$ with filled Julia set exactly $I_p$ and straightening $z^2-2$.

### Which parameters the result selects

Write $t=c+7/4$, $k=n-2$, and $H_t(y)=-f_c^3(-y)$. The first $k$ iterates of zero stay in $[0,2/5]$, and $H_t^k(0)\in[7/20,19/50]$. In this exit window there is a unique superattracting center of exact period $p$. The tip furnished by the theorem lies to its left. Every parameter in the next exit window lies strictly to the left of every parameter in the preceding one. The existence proof allows a choice among noncentral roots in a single window. Uniqueness of that noncentral root is a separate question.

The archive had isolated individual parameters for $p=24,27,30$. For each of those periods, Lean checks that **every real parameter in the original dyadic bracket** satisfies this exit condition. The three earlier complex disk certificates provide explicit radii and separation margins for their particular parameters. The all-period argument below works without extrapolating those radii. [Original experiment](RESULTS.md#selection-and-what-the-literature-establishes) · [Archival bracket checks](../../formalization/weighted/ParabolicArchiveBrackets.lean)

### How the noncentral root is obtained

At $t=0$ the reflected return has the exact factorization

$$
 H_0(y)-y=\frac{7-4y^2-4y}{256}\,(-8y^3+4y^2+18y-1)^2 .
$$

A root $a\in[1/20,3/50]$ of the cubic traps the critical orbit on the entrance side at the parabolic parameter. For $0<t\le1/100$ and $0\le y\le2/5$, direct inequalities give

$$
 \tfrac12t+(y-a)^2\ \le\ H_t(y)-y\ \le\ 10t+20(y-a)^2 .
$$

To follow the first exit continuously in the parameter, clip each step at $2/5$. The clipped and true flights coincide up to any step strictly below the cap. At $t=1/100$ the clipped orbit reaches the cap by the fourth step. Parameter continuity then supplies a crossing of the exit window for every $k\ge4$. Write $E(t)=H_t^{k+2}(0)$. Along this crossing one can pass from $E=1/10$ to $E=0$ while keeping $0\le E\le1/10$.

The second flight starts at $E(t)$. At the center it starts at zero. Where $E(t)=H_t(0)$ it starts one step ahead. Between these two parameters it passes a last point at which its $k$-th clipped iterate is $39/100$. From that point to the center, the clipping cap is inactive on the second flight. The two remaining steps at the crossing give $H_t^{k+2}(E)<-1/10$.

The equation $H_t^{k+2}(E)+E=0$ also vanishes at the center. Evenness supplies a continuous polynomial quotient $Q$ such that
$$
 H_t^{k+2}(E)+E=E Q(t),\qquad Q(t)=2\quad\text{when }E=0 .
$$
The quotient is negative at the second-flight crossing and positive at the center. Its zero has $E>0$ and yields the required orbit with $e_p=E$. The strict gap $e_p<H_t(0)$ makes consecutive endpoint images interleave. Keeping the other two quadratic steps of each triple separates all the physical phases, including the last three near the exit. [Shooting proof](../../formalization/weighted/ParabolicTipShooting.lean) · [Full branches](../../formalization/weighted/ParabolicBranches.lean) · [Phase separation](../../formalization/weighted/ParabolicDisjoint.lean)

The two-sided rate comes from summing the step bounds through the slow part of the orbit. For $b=\sqrt t$, the bounded coordinate $x/(b+|x|)$, with $x=y-a$, gains at least $b/5$ per step. A second coordinate clips $y-a+b/2$ to $[0,b]$. It traverses that interval and gains at most $15t$ per step. Together these give $1/15\le k\sqrt t\le10$. Substituting $p=3(k+2)$ gives the constants in the theorem. [Rate proof](../../formalization/weighted/ParabolicTipRate.lean)

### The complex inverse image and the analytic corollary

Write $f=f_{c_p}$. For $1\le j<p$, the real interval $f^j(I_p)$ omits zero. Thus all its points have the same strict sign as $f^j(0)$. The corresponding open set in the complex plane is
$$
 U=\{z\in\mathbb C:\ \operatorname{Re}(f^j(z))\,f^j(0)>0
                    \text{ for }1\le j<p\}.
$$
It contains $I_p$. If $z\in U$ has $G(z)\in I_p$, surjectivity of the real return gives $x\in I_p$ with $G(x)=G(z)$. Pulling backwards through a quadratic gives two candidate signs at each step. Agreement of the real-part signs forces equality at every intermediate step. Only the initial pair $z=\pm x$ survives. Consequently $U\cap G^{-1}(I_p)=I_p$. Compactness, connectedness and this open isolation identify the entire pullback component. The same argument and the full branches count exactly two distinct preimages of every interior interval value in $U$. [Complex isolation and fiber count](../../formalization/weighted/ParabolicComplexComponent.lean)

Blokh, Oversteegen, Ptacek and Timorin's Theorem B applies to a full invariant plane continuum that is a component of its full inverse image, with a basin condition at attracting or parabolic points. The segment has connected complement and $G(I_p)=I_p$. The critical point of $f$ is strictly preperiodic, so the filled Julia set of $f$ has empty interior by Douady and Hubbard's strictly preperiodic case. The filled Julia set of an iterate equals that of the original polynomial. An attracting or parabolic basin would give it interior. This discharges the basin condition and gives a polynomial-like restriction with filled Julia set $I_p$. [Blokh et al., Theorem B, §4](https://bpb-us-w2.wpmucdn.com/sites.uab.edu/dist/0/610/files/2025/09/QL-revised-short-v-11-30-15.pdf) · [Douady and Hubbard, Orsay Notes, Chapter IV §4, p. 37](https://pi.math.cornell.edu/~hubbard/OrsayEnglish.pdf)

A preimage in the polynomial-like domain of any filled-Julia-set point itself belongs to the filled Julia set. Choosing an interior interval value outside the finitely many critical values of $G$, the fiber count gives degree two. The $p$ little filled Julia sets are the already separated intervals $f^j(I_p)$, so the restriction is primitive. The quadratic straightening has a critical orbit of exact type $0\mapsto d\mapsto d^2+d\mapsto d^2+d$, with $d\ne0$. Hence $d^3(d+2)=0$, giving $d=-2$. The application of Theorem B and the straightening theorem uses the published results. Lean checks the complex pullback, fiber count, and final parameter algebra. [Douady and Hubbard, Straightening Theorem 1](https://pi.math.cornell.edu/~hubbard/PolyLikeMaps.pdf)

### Verification and scope

From the repository root, run

```sh
cd formalization/weighted
lake exe cache get
lake build ParabolicTipFamily ParabolicArchiveBrackets
```

The pinned project uses Lean 4.32.0 and mathlib 4.32.0. The main theorem is `LoopsParabolic.near_parabolic_primitive_tips`. The family target checks the parameter sequence and the unique companion center; the separate archive-bracket target checks the three original dyadic brackets. Both are default Lake targets. [Family theorem](../../formalization/weighted/ParabolicTipFamily.lean) · [Center and window ordering](../../formalization/weighted/ParabolicCenterBranch.lean)

The result supplies a one-return family approaching a specific parabolic parameter. A depth-uniform marked-width estimate, a KKL attachment collar on this family, and the global MLC gates remain open. The constants bound the accumulation rate and leave the sharp asymptotic coefficient undetermined. ChatGPT (GPT-6) developed the argument and the Lean sources. Independent human review of the research note and its applications of the published theorems is pending.
