---
ledger: H2_CALIBRATION
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; Lean development and independent AI mathematical review
human_review: none
---

<a id="parabolic-sharp-passage-20261126"></a>

# Sharp accumulation of the actual period-three parabolic tips

Ledger statement being addressed:

> QL, WAD, sectorial, and virtual marked coordinates are calibrated on declared interfaces with universal parameters and explicit additive, relative, density-normalized, or discounted error budgets.

## Claim

The compiled Lean theorem chain proves the sharp coefficient left undetermined in
[the archive's actual near-parabolic family](https://github.com/dovvnloading/loops-research-archive/blob/f95edb7ad9314cb736764961e652ebf313187778/research/native_wave_transfer/near_parabolic_tip_family.md#verification-and-scope).

Let $f_c(z)=z^2+c$, let $k_j\to\infty$ be any sequence of natural numbers,
and choose any of the archive's actual shooting tips
$\operatorname{Shot}(k_j,t_j,e_j)$. Set
$p_j=3(k_j+2)$ and $c_j=-7/4+t_j$. The proved limits are

$$
 k_j\sqrt{t_j}\longrightarrow\frac{\pi}{7},
 \qquad
 (p_j-6)^2(c_j+7/4)\longrightarrow\frac{9\pi^2}{49},
 \qquad
 p_j^2(c_j+7/4)\longrightarrow\frac{9\pi^2}{49}.
$$

The statements apply to every allowed choice of noncentral roots.
Root uniqueness is neither assumed nor concluded. An existence theorem
instantiates them at all physical periods $18,21,24,\ldots$, using the
existing shooting construction.

The main result is *shot_sharp_parameter_accumulation*, with the ordinary
period normalization in *shot_sharp_physical_period_accumulation*, in
[ParabolicSharpPassage.lean](https://github.com/dovvnloading/loops-research-archive/blob/f95edb7ad9314cb736764961e652ebf313187778/formalization/weighted/ParabolicSharpPassage.lean).
The stronger passage theorem *channel_sharp_passage_limit* only needs a true
polynomial flight starting at zero, staying in the existing corridor through
time $k_j$, reaching its exit, and $t_j\to0^+$. Thus the second shooting
flight is not an extra premise of the asymptotic calculation.

This is a new exact coefficient for the archive's existing near-$-7/4$
family. It is distinct from the already archived near-$-2$ family.
The earlier bound was only
$1/25\le(p-6)^2(c+7/4)\le900$.

## Evidence

### 1. The actual polynomial, with its exact coefficients

Use the existing reflected third return

$$
 H_t(y)=u-\big((u-y^2)^2-u\big)^2,\qquad u=7/4-t.
$$

Choose a root $a\in[1/20,3/50]$ of
$-8a^3+4a^2+18a-1=0$. The proof uses the existing polynomial itself.
It constructs

$$
 A=\frac{11}{2}-2a^2,\qquad
 B=\frac{21}{2}-28a-14a^2,\qquad
 A\ge1,\quad B\ge1,\quad AB=49.
$$

An exact polynomial identity expresses the remainder as

$$
 H_t(a+x)-(a+x)-(At+Bx^2)
   =x^3U(a,x)+txR(a,x)+t^2S(a,t,x),
$$

where all three coefficient functions are explicit polynomials. Their
absolute values are bounded on one compact box. Consequently there is one
constant $C\ge1$, uniform over the permitted roots, for which

$$
 (1-C\delta)(At+Bx^2)
 \le H_t(a+x)-(a+x)
 \le(1+C\delta)(At+Bx^2)
$$

whenever $0\le\delta\le1$, $0\le t\le\delta^2$, and $|x|\le\delta$.
No normal-form asymptotic is imported as a hypothesis.

[Polynomial coefficients and remainder](https://github.com/dovvnloading/loops-research-archive/blob/f95edb7ad9314cb736764961e652ebf313187778/formalization/weighted/ParabolicPassageCoefficients.lean)

### 2. Discrete entry, exit, and omitted time

For $w_j=H_t^j(0)$, the existing coarse inequalities imply

$$
 \tfrac12t+(w_j-a)^2\le w_{j+1}-w_j
 \le10t+20(w_j-a)^2.
$$

For $0<\delta\le1/1000$ and $0<t\le\delta^2$, the new proof
constructs the first crossing indices $l<m$ of
$a-\delta$ and $a+\delta$. Monotonicity of the actual $H_t$, evaluated
at the fixed walls, gives

$$
 -\delta\le w_l-a\le-\delta/2,\qquad
 \delta\le w_m-a\le2\delta.
$$

This excludes an uncontrolled discrete jump across the bottleneck.
Every retained step has both endpoints in $[-2\delta,2\delta]$.
Telescoping the actual orbit displacement gives the independent outer-time
budget

$$
 \big(k-(m-l)\big)\delta^2\le\frac25.
$$

[Actual cut indices](https://github.com/dovvnloading/loops-research-archive/blob/f95edb7ad9314cb736764961e652ebf313187778/formalization/weighted/ParabolicPassageCuts.lean) ·
[Finite-flight accounting](https://github.com/dovvnloading/loops-research-archive/blob/f95edb7ad9314cb736764961e652ebf313187778/formalization/weighted/ParabolicPassageFlight.lean)

### 3. Uniform angular error per step

Put $s=\sqrt{(A/B)t}$. The exact coefficient product proves
$Bs=7\sqrt t$. For the angular coordinate
$\theta(x)=\arctan(x/s)$, the mean-value theorem and a quadratic-denominator
variation bound show that a central step whose relative drift error and
angular-denominator variation are both at most $\varepsilon$ satisfies

$$
 \left|\theta(w_{j+1}-a)-\theta(w_j-a)-Bs\right|
 \le4\varepsilon Bs.
$$

The old inverse-square estimate independently gives $k\sqrt t\le10$.
Summing the new per-step error therefore costs at most $280\varepsilon$.
This use of a coarse bound does not assume the sharp limit.

[Discrete angle estimate](https://github.com/dovvnloading/loops-research-archive/blob/f95edb7ad9314cb736764961e652ebf313187778/formalization/weighted/ParabolicPassageAngle.lean)

### 4. A finite error inequality before taking any limit

For each $0<\varepsilon\le1/2$, the proof constructs a fixed positive
$\delta\le1/1000$. For every sufficiently small positive $t$ and every
true flight satisfying the corridor and exit hypotheses, it proves

$$
 \left|7k\sqrt t-\pi\right|
 \le 280\varepsilon+
      \frac{7(2/5)}{\delta^2}\sqrt t+
      \left(\pi-2\arctan\frac{\delta}{2\sqrt{(A/B)t}}\right).
$$

The radius is chosen before the parameter tends to zero. In particular,
the estimate does not silently interchange two limits or assume a
uniform vanishing error over an expanding normalized interval.

[Finite quantitative estimate](https://github.com/dovvnloading/loops-research-archive/blob/f95edb7ad9314cb736764961e652ebf313187778/formalization/weighted/ParabolicPassageEstimate.lean) ·
[Uniform radius selection](https://github.com/dovvnloading/loops-research-archive/blob/f95edb7ad9314cb736764961e652ebf313187778/formalization/weighted/ParabolicPassageUniform.lean)

### 5. The actual parameter limit

For a fixed selected radius, the outer-time term and both angular tails
vanish as $t\to0^+$. Only then is the requested error
$\varepsilon$ made arbitrarily small. This proves $7k\sqrt t\to\pi$.

For actual shooting roots, $t_j\to0$ is derived independently from the
already proved $k_jt_j\le19/25$ and $k_j\to\infty$. Squaring the new limit
and substituting $p_j-6=3k_j$ gives the stated coefficient.
The ordinary $p_j^2$ normalization follows from
$p_j\sqrt{t_j}=3k_j\sqrt{t_j}+6\sqrt{t_j}$.

[Limit argument](https://github.com/dovvnloading/loops-research-archive/blob/f95edb7ad9314cb736764961e652ebf313187778/formalization/weighted/ParabolicPassageLimit.lean) ·
[Actual shooting-family specialization](https://github.com/dovvnloading/loops-research-archive/blob/f95edb7ad9314cb736764961e652ebf313187778/formalization/weighted/ParabolicSharpPassage.lean)

### Validation record

The entire proof chain compiled in the repository's pinned Lean 4 project
at [proof commit f95edb7ad9314cb736764961e652ebf313187778](https://github.com/dovvnloading/loops-research-archive/commit/f95edb7ad9314cb736764961e652ebf313187778).
[The weighted Lean CI run](https://github.com/dovvnloading/loops-research-archive/actions/runs/45936214478)
passed both the full build and the transitive axiom audit.

- All eight new modules compiled, including ParabolicSharpPassage.
- The full weighted build completed successfully with 8,990 build jobs.
- The axiom audit passed for all 158 weighted modules and 3,431 declarations.
  Each of the eight new modules is individually listed as using allowed
  axioms only.
- Source coverage and the proof-escape scan passed. There is no `sorry`,
  `admit`, or new axiom; compiled dependencies use only the existing
  permitted foundations `propext`, `Classical.choice`, and `Quot.sound`.
- All 23 pull-request workflows at that proof commit passed, including
  [Contribution intake](https://github.com/dovvnloading/loops-research-archive/actions/runs/45936214301)
  and [Research validation](https://github.com/dovvnloading/loops-research-archive/actions/runs/45936214472).

The packet registers 38 public theorems across the eight modules. Private
proofs and generated declarations are included in the transitive audit.
Local Lean was unavailable and the workspace disk was full; repository
CI supplied the actual compiler and kernel-audit validation.

Reproduction from the repository root:

~~~sh
cd formalization/weighted
lake exe cache get
lake build
cd ../..
python3 -B code/verify_lean_coverage.py --audit weighted
~~~

All modules are registered in the existing weighted project, theorem index,
and source map. No workflow, status record, or foundational allowlist was
changed. This final documentation update leaves the validated Lean source
unchanged.

## Dependencies

The prior archive's ParabolicChannel, ParabolicTipRate,
ParabolicTipShooting, and ParabolicTipFamily provide the actual polynomial,
the shooting roots, the coarse rate, and the physical family interpretation.
Mathlib supplies real calculus, the mean-value theorem, compact polynomial
bounds, the arctangent derivative and limits, and finite-sum/filter tools.

H2_CALIBRATION is the broader research target, not a proved premise or a
claimed consequence of this packet. Its unresolved geometric dependencies
are not assumed discharged.

## Boundary

This settles the sharp accumulation coefficient question explicitly left
open in the cited source note. It does not close the full H2_CALIBRATION
ledger row or any other canonical ledger obligation; no status promotion
is requested.

The result concerns one actual primitive family near the real period-three
parabolic parameter. It does not construct native KKL attachment collars,
prove uniform marked-width comparison, identify all virtual dynamical
objects, or build compatible all-scale marked towers. H1–H4, the universal
tower closure, and MLC remain open. The noncentral shooting root's
uniqueness is a separate question.

The physical dynamics and interval/cylinder geometry already established
for Shot remain prior archive results. The new claims are the sharp
passage law and its exact parameter coefficient, with the required
uniform discrete error estimates.

## Attribution

The channel, shooting construction, exact periods, disjoint phases, and
coarse inverse-square rate belong to the earlier archive work.
Classical parabolic passage motivates the arctangent coordinate; no
literature priority for that general method is claimed.
The contribution resolves a specific quantitative question explicitly left
open in this archive and supplies its new proof inside the existing Lean
project. Independent human specialist review remains outstanding.
