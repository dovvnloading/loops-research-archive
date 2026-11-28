---
ledger: NOV26_OPEN_DEPTH_GATES
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="three-level-physical-gates-20261127"></a>

# Arbitrary-depth physical quadratic return towers

## Claim

This contribution now attacks the missing arbitrary-depth physical induction
in NOV26_OPEN_DEPTH_GATES. The complete eight-module explicit three-level
construction compiled at f827953946d11f7260197a80b5aaebfddbabee1c. The stronger
arbitrary-depth declarations below are candidates until the unchanged
repository CI builds the full project and completes its transitive axiom audit.
No result is certified merely by source scanning or an intake check.

### Arbitrary-depth theorem

The main candidate is **DepthGate.exists_physical_tower**. For every natural
number k, it constructs one real quadratic parameter and k+1 distinct nested
physical first-return restrictions of the literal map \(f_c(z)=z^2+c\).
Every nonterminal period is strictly less than, and divides, the terminal
period. The conclusions, all about the same parameter, are:

- Each source is the component containing zero of the complete pullback of
  its stated round target. The literal iterate is proper and onto, with two
  source preimages of every noncritical target value and one of the critical
  value.
- Every nonterminal source has compact closure inside the concentric disk
  of half its target radius. Every deeper complete target disk lies inside
  every earlier source.
- All deeper-source phases at earlier-return checkpoints remain inside the
  same earlier source, including all intermediate checkpoints.
- Every source misses its own target at every positive original quadratic
  iterate before its assigned return time.
- If N is the terminal period and \(d=f_c^N(0)\ne0\), the terminal target is
  \(B(0,23|d|/20)\), its source closure lies in \(B(0,11|d|/10)\), and its
  source contains the entire closed disk centered at \(-3d/4\) with radius
  \(133|d|/2000\). These relative constants are independent of depth.
- The actual polynomial satisfies \(f_c^{6N}(0)+f_c^{3N}(0)=0\). Its normalized
  terminal return differs from \(1-\kappa z^2\), with
  \(\kappa\in[17903/10000,17904/10000]\), by at most \(1/500000\) on
  \(|z|\le23/20\).

The numerical chart and ancestor estimates are **outputs** of the
unconditional existence theorem. They are not physical tower hypotheses
assumed at the theorem's boundary.

### The closed prefix construction

DepthGateBase initializes a genuine SharpChart, with
\(N_0=17\), margin \(\mu_0=4^{-17}/10000\), radius reserve \(b_0=1/20\), and
error reserve \(\theta_0=1/1000000\). For a current chart, choose an outer
period p satisfying

\[
p\ge17,\qquad
128\,4^{-p}5^{6N}\le\frac{\mu b\theta}{10000}.
\]

DepthGateBase.exists_admissible_prefix (in the TerminalChart namespace)
proves that arbitrarily large such periods exist. DepthGatePrefix constructs
the next actual parameter interval, with

\[
N'=Np,\qquad \mu'=\frac{\mu\,4^{-p}}{100},
\qquad b'=b/2,\qquad\theta'=\theta/2.
\]

The control radius is \(23/20+b\); its positive reserve absorbs the moving
signed input scale. The normalized-map error is at most
\(1/500000-\theta\); halving its reserve pays the new normalization error.
The fixed terminal gate constants therefore survive any finite number of
prefixes, even though the positive auxiliary margins decrease.

DepthGateAncestors proves preservation of every ancestor's complete circle
barrier, small disk image bound, all-time orbit and pair bounds, first-return
gap, full-target containment and whole-source checkpoint containment. Old
radii are transported exactly by the signed outer coefficient's absolute
value; a new outer target and half-radius barrier are constructed. Its
auxiliary disk has radius \(15\,4^{-p}\), while the transported checkpoint
bound is only \((44/3)\,4^{-p}\), leaving strict nesting slack.

DepthGateRealization derives the actual complete proper components and all
first-return properties from those numerical estimates. DepthGateTower
performs the induction on the number of ancestors, selects a parameter using
the preserved opposite shooting signs, and realizes every level simultaneously.
The terminal signed scale is allowed to alternate in sign; every physical
identity retains that sign, and radii use its absolute value.

### Explicit three-level subfamily

The separately quantified theorem
`ThreeLevelFirstReturn.exists_first_return_three_level_gate`. For every triple
of natural numbers satisfying

\[
r\ge17,\qquad q\ge10r+30,\qquad p\ge20rq+100,
\]

it constructs a real parameter of the **literal** map \(f_c(z)=z^2+c\), with
three simultaneous complete physical pullback components for the return times
\(p,qp,rqp\). Writing \(x_n=f_c^n(0)\), \(A_p\) for the quadratic coefficient
of \(f_c^p\), and \(d=x_{rqp}\), the conclusions include:

- \(c\in[-2,-2+20\,4^{-p}]\), \(d>0\), and the actual relation
  \(x_{6rqp}+x_{3rqp}=0\).
- The outer and middle targets have radii \(2^{-p}\) and
  \(2^{-q}/|A_p|\); each source is the component containing zero of the
  **complete** pullback of that target. Its closure is compact and contained
  in the concentric disk of half the target radius.
- The terminal target is \(B(0,23d/20)\). Its complete central source has
  compact closure in \(B(0,11d/10)\) and contains the whole closed gate disk
  centered at \(-3d/4\) with radius \(133d/2000\).
- All three literal return restrictions are proper and onto their stated
  targets. Every noncritical target value has exactly two preimages in the
  stated source; the critical value has exactly one.
- Every middle-source phase at times \(mp\), \(0\le m\le q\), lies in the
  same outer source. Every terminal-source phase at times \(mqp\),
  \(0\le m\le r\), lies in the same middle source; every terminal-source
  phase at times \(mp\), \(0\le m\le rq\), lies in the same outer source.
- Each complete source misses its own target at every positive iterate before
  its stated return time. These are literal first returns throughout the
  sources, including intervening times that are not multiples of \(p\).

## Hard point and proof architecture

The added outer return perturbs a two-level reference map, but its terminal
critical scale is already of order \(4^{-(q+r)}\). A small absolute error is
insufficient: normalization divides by this changing, negative scale, and a
composition can acquire extra sheets if two intermediate phases become
antipodal. Both problems must be controlled on the whole complex input disk.

`ThreeLevelReference` establishes the reference bounds

\[
24\,4^{-q}4^{-r}<|x_{rq}(t)|<81\,4^{-q}4^{-r},\qquad x_{rq}(t)<0,
\]

and endpoint relation margins exceeding
\(4^{-q}4^{-r}/10000\). For all points of the normalized disk of radius
\(6/5\), it controls every intermediate reference iterate through \(rq\).
The key pair estimate is a lower bound \(4\,4^{-q}\) on the norm of the sum
of any two phase images at every time \(1\le n<rq\). Its proof separates
ordinary phases from multiples of \(q\); neither a critical-orbit-only bound
nor a checkpoint-only estimate would establish this conclusion.

`ThreeLevelPerturbation` proves a normalized iterate comparison with an
arbitrary signed moving scale. The explicit separation of \(p\) pays for the
full \(6rq\) shooting horizon, scale division and a second orbit comparison:

\[
128\,4^{-p}5^{12rq}\le4^{-q}4^{-r}/10^{12}.
\]

`ThreeLevelSelection` transports the two opposite endpoint signs through the
actual outer return, selects the original parameter by the intermediate value
theorem, and proves the sign of the actual physical scale. `ThreeLevelTerminal`
then obtains the complete terminal normalized-map error \(1/500000\) on the
disk of radius \(23/20\), together with complete signed collision control.

`ThreeLevelDomains` constructs an actual component directly from a circle
barrier and complete collision estimates. `ThreeLevelMiddle` supplies those
estimates for the middle iterate on its own target scale. `ThreeLevelPhysical`
assembles all three components and their whole-source phase inclusions.
`ThreeLevelFirstReturn` combines the block exclusions with the outer exclusion
to treat every intervening original quadratic iterate.

## Evidence

Baseline: `e8d82717b184b5f4e46c34a46b1445fc75f33a1c`.

The merged `TwoLevelPhysicalGates` result gives an unbounded **two-level**
physical family for \(q\ge17\), \(p\ge10q+30\). The archived fixed depth-three
construction and width certificates do not supply this three-variable family
of complete physical domains. The present candidate prepends another outer
period to the entire signed two-level bracket and resolves the resulting
moving-scale and between-checkpoint phase estimates. The previous theorem
cannot simply be applied twice: the next map is a normalized polynomial
iterate, not a quadratic polynomial.

Generic existence of finite multilevel quadratic renormalizations and complex
bounds is classical. This contribution does not claim first discovery of
three renormalizations, nor does a literature search establish worldwide
priority for its explicit constants. The proposed increment is the explicit
uniform physical construction and its closed arbitrary-depth prefix induction,
beyond the archived two-level theorem. The archived all-depth marking statement
assumes the physical data at every level; the present induction constructs the
physical complete domains and uniform terminal gate for its separated family.
Relevant primary context includes Lyubich--Yampolsky,
[*Dynamics of quadratic polynomials: complex bounds for real maps*](https://www.numdam.org/item/AIF_1997__47_4_1219_0/),
and Lyubich,
[*Feigenbaum--Coullet--Tresser universality and Milnor's hairiness conjecture*](https://www2.math.ethz.ch/EMIS/journals/Annals/149_2/lyubich.pdf).

## Dependencies

Inherited compiled infrastructure includes `NearTwoShooting`,
`TwoLevelOuterChart`, `TwoLevelReference`, `TwoLevelPerturbation`,
`TwoLevelSelection`, `TwoLevelGateDomain`, `TwoLevelPhysicalGate`,
`TwoLevelOuterDomain`, `ThreeReturnDomain`, `ThreeReturnDegree`, and Mathlib.
Those inherited theorems are not counted as new work. All new sources belong
to the existing `formalization/weighted` project and are registered through
`code/contribute.py lean-add`.

The local workspace has no Lean installation and insufficient free disk for
Lean and Mathlib. The existing repository CI is the compilation authority;
its source-coverage gate and transitive kernel-axiom audit remain unchanged.
Compiler diagnostics and their repairs are retained in the PR's commits and
workflow history. Human review: none.

## Boundary

`NOV26_OPEN_DEPTH_GATES` remains open. The stronger candidate constructs
arbitrary finite depth for recursively separated period choices; it does not
construct every prescribed finite tuning word. No conclusion is claimed about
canonical kneading, marked KKL prime ends, physical optimal widths,
simple connectivity or Jordan boundaries, connected filled Julia sets,
H1--H4, or MLC. In particular, the package is stated as nested physical
proper two-sheeted first returns; additional dynamical hypotheses would be
needed to promote that wording to a full renormalization theorem.

## Attribution

Proof development, mathematical scope review, and Lean repair: OpenAI ChatGPT
GPT-6 Astra Pro. The construction builds on the archive's all-period shooting
and two-level physical-domain work, with the inherited results identified
above. No independent human review or literature-wide priority claim.
