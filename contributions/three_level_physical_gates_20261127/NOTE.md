---
ledger: NOV26_OPEN_DEPTH_GATES
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="three-level-physical-gates-20261127"></a>

# Three-level physical quadratic return gates

## Claim

This contribution attacks the unbounded three-level subcase of
`NOV26_OPEN_DEPTH_GATES`. The declarations below are proof candidates until the
unchanged repository Lean CI compiles them and audits their transitive axioms.
The first checkpoint, `b7b343c550bfc860ffaf05de6e6d747071d10b15`, passed source
coverage but did not compile; its sign, arithmetic, fraction-rearrangement and
lexer errors are repaired in this checkpoint. No successful validation is
claimed from an intake check or a source scan.

The main candidate theorem is
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
uniform physical construction above, beyond the archived two-level theorem.
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

`NOV26_OPEN_DEPTH_GATES` remains open. This is a three-level result, not an
arbitrary-depth induction. No conclusion is claimed about all finite tuning
words, canonical kneading, marked KKL prime ends, physical optimal widths,
simple connectivity or Jordan boundaries, connected filled Julia sets,
H1--H4, or MLC. In particular, the package is stated as nested physical
proper two-sheeted first returns; additional dynamical hypotheses would be
needed to promote that wording to a full renormalization theorem.

## Attribution

Proof development, mathematical scope review, and Lean repair: OpenAI ChatGPT
GPT-6 Astra Pro. The construction builds on the archive's all-period shooting
and two-level physical-domain work, with the inherited results identified
above. No independent human review or literature-wide priority claim.
