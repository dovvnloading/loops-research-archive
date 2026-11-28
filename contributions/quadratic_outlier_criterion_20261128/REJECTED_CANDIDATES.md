# Candidate statements and rejection record

**Status: no retained candidate. These are pre-formalization screening notes, not new
results, and none is counted as a theorem under the requested Lean standard.**

The search was for an actual quadratic mechanism, beyond classical supporting topology,
that forces a parameter fiber to be a singleton. This file records the statements tested,
their precise failure, and the distinction between an elementary calculation and the
missing research step. It does not assert that these directions can never work.

Throughout, write

\[
f_c(z)=z^2+c,\qquad P_0(c)=0,\qquad P_{n+1}(c)=P_n(c)^2+c,
\qquad M=\{c:\sup_n|P_n(c)|<\infty\}.
\]

## 1. Thurston spectra: two different candidate statements

### 1A. Universal spectral gap

**Candidate:** there is an epsilon greater than zero such that the postcritical
Thurston pushforward operator of every quadratic polynomial with periodic critical
point has all eigenvalues of modulus at most `1 - epsilon`.

**Decision: discard; contradicted by a classical result.** Buff, Epstein and Koch,
*Eigenvalues of the Thurston operator*, in the
[author-hosted version](https://www.math.univ-toulouse.fr/~buff/Preprints/Eigenvalues/eigenvalues.pdf),
Theorems 3 and 4, pages 2--3, show that the individual eigenvalues have
`1/8 < |lambda| < 1`, while the closure of the union of the postcritical spectra
contains `1/4 <= |lambda| <= 1`. In particular, no such universal gap exists.
The preprint is also [arXiv:1707.01990](https://arxiv.org/abs/1707.01990).
The theorem numbering here refers to the linked author version.

This rejects a gap uniform over all centers. It does **not** disprove a gap on a
specified restricted sequence, nor prove that the gap degenerates along every
sequence approaching an infinitely renormalizable parameter.

### 1B. A selected sequence's contraction forces its limiting fiber to collapse

**Candidate:** for centers approximating one prescribed combinatorial fiber,
quantitative contraction of their marked Thurston pullbacks forces that fiber to
be a singleton.

**Decision: not established; do not formalize an abstract replacement.** A valid
statement still needs actual comparison data between the changing marked spaces,
control in the relevant norm rather than only spectral radius, and a proof that
the controlled quantity detects finite displacement of the actual parameter.
A list of strict spectral inequalities provides none of those implications.
The proof cannot assume a differentiable path through a connected fiber: a
connected compact set need not supply such a path.

The nearby contraction incidence criterion is also classical. Laura G. DeMarco,
Sarah C. Koch and Curtis T. McMullen, *On the postcritical set of a rational map*,
[author PDF](https://people.math.harvard.edu/~ctm/papers/home/text/papers/postc/postc.pdf),
Proposition 3.1, characterizes strict pullback contraction by the absence of a
four-point inverse-image configuration. Thus merely deriving an equivalent
finite preimage criterion would not supply the requested new idea.

No claim is made that these classical theorems prove or disprove Candidate 1B.
The failure is that this investigation has not supplied its new, load-bearing
comparison and finite-parameter argument.

## 2. Combinatorial separation or pinched-disk injectivity

**Candidate:** if a full combinatorial invariant separates each pair in a
combinatorial fiber, then the fiber is a singleton and M is locally connected
at its point.

**Decision: discard; the hypothesis restates the missing separation.** This does
not prove that internal addresses, kneading data, or Hubbard-tree information
separate actual parameters with identical full combinatorics. Replacing the
invariant by an unspecified injective coordinate supplies no dynamical content.

The topological endpoint is classical. Dierk Schleicher,
*On Fibers and Local Connectivity of Mandelbrot and Multibrot Sets*,
[arXiv:math/9902155](https://arxiv.org/pdf/math/9902155), Proposition 3.5,
proves the implication from a trivial fiber to pointwise local connectivity.
Corollary 3.6 gives the global equivalence. The archive already has a standalone
Lean theorem for the corresponding compact monotone-quotient implication in
`QuadraticMonotoneFiberTopology.lean`.

There is no construction of the canonical pinched-disk projection in that Lean
module. It accepts a continuous monotone surjection onto a Hausdorff locally
connected target. An arbitrary map with that signature must not silently be
identified with the canonical combinatorial quotient.

## 3. Actual quadratic cohomology: a precise rejected criterion

This is the most concrete alternative calculation found during this search.
It is recorded with a full statement so that a generic estimate is not mistaken
for a new actual-family rigidity mechanism.

Let `E` be the complex Banach space of bounded sequences indexed by the
nonnegative integers, with its supremum norm, and let `E_0` be its subspace of
sequences whose zeroth entry is zero. Fix `c in M`, put `x_n=P_n(c)`, and define

\[
(L_cv)_n=v_{n+1}-2x_nv_n\qquad(v\in E_0).
\]

**Candidate theorem.** Suppose there is a bounded complex linear functional
`Lambda : E -> C` such that

\[
\Lambda(L_cv)=0\quad\text{for every }v\in E_0,
\qquad\Lambda(\mathbf1)\ne0.
\]

Let `F` be a connected subset of `M` containing `c`. Suppose, as `d` tends to
`c` through `F \ {c}`, that

\[
\frac{\sup_n |P_n(d)-P_n(c)|^2}{|d-c|}\longrightarrow0. \tag{C}
\]

Then `F={c}`. If `F` is the fiber at `c` of an explicitly supplied continuous
monotone surjection from `M` onto a Hausdorff locally connected space, the
classical compact-quotient implication gives pointwise local connectivity of
`M` at `c`.

### Calculation behind the candidate

For `d in M`, the actual orbit difference `delta_n=P_n(d)-P_n(c)` belongs to
`E_0`. The two quadratic equations give exactly

\[
L_c\delta=(d-c)\mathbf1+\delta^2,
\]

where squaring is coordinatewise. Applying the functional gives

\[
(d-c)\Lambda(\mathbf1)=-\Lambda(\delta^2).
\]

The norm inequality therefore gives

\[
|d-c|\,|\Lambda(\mathbf1)|
\leq\|\Lambda\|\,\|\delta\|_\infty^2. \tag{1}
\]

Since `Lambda(1)` is nonzero, the functional has nonzero norm. For `d != c`,
(1) contradicts (C) when `d` is sufficiently close to `c`. Thus `c` is isolated
in `F`. A connected set containing an isolated point is that singleton.

### Why the candidate was rejected before formalization

The argument is a quadratic Taylor identity followed by a bounded-functional
estimate. Condition (C) is precisely a strong metric assumption on the actual
orbit map. No quadratic-specific mechanism establishing (C) on the relevant
fibers was found. Keeping the theorem would violate the request to avoid
abstract metric criteria, even though its recurrence is the actual quadratic
recurrence and its final implication can be made formally correct.

The nearby established framework is twisted cohomology and horizontal
functionals: Viviane Baladi and Daniel Smania, *Smooth deformations of piecewise
expanding unimodal maps*, DCDS 23 (2009), 685--703,
[author PDF](https://sites.icmc.usp.br/smania/smooth.pdf), Sections 3--4;
and *Linear response for smooth deformations of generic nonuniformly hyperbolic
unimodal maps*, Ann. Sci. ENS 45 (2012), 861--926,
[primary journal record](https://www.numdam.org/item/ASENS_2012_4_45_6_861_0/).
Their theorems concern their stated real/unimodal hypotheses; they are not
being misquoted as an MLC theorem for arbitrary complex quadratic fibers.
The rejection rests on the elementary argument above and the excluded metric
premise, not on an assertion that those papers contain this exact statement.

## 4. Cauchy transforms and the pushforward fixed-point equation

**Candidate direction:** construct a Cauchy transform supported on the
postcritical closure, then use a Ruelle--Thurston fixed-point obstruction to
separate parameters in one fiber.

**Decision: no retained theorem.** The fixed-point theory itself is established:
Genadi Levin, *Fixed points of the Ruelle--Thurston operator and the Cauchy
transform*, [arXiv:2002.03430v2](https://arxiv.org/pdf/2002.03430), Lemma 2.1,
gives necessary and sufficient conditions in its specified functional setting.
A new proof would still need to construct from two distinct actual parameters
in a common fiber the required nonzero object satisfying the hypotheses.
This investigation does not construct it. Simply imposing its existence or
nonexistence as a disguised rigidity assumption is not an advance.

## 5. Algebraic compression of critical orbits

### 5A. A rational generating function for the critical orbit

**Candidate:** a linear recurrence for the actual critical orbit yields a new
class of parameters at which M is locally connected.

**Decision: discard; it reduces immediately to a finite critical orbit.**
Suppose constants `a_0,...,a_m`, with `a_m != 0`, satisfy

\[
\sum_{j=0}^m a_jP_{n+j}(c)=0
\]

for every sufficiently large `n`. The polynomial

\[
Q(z)=\sum_{j=0}^m a_j f_c^{\circ j}(z)
\]

is nonzero: the summands have distinct degrees `2^j`. Every sufficiently late
critical-orbit point is a root of `Q`, hence belongs to its finite zero set.
The entire critical orbit is therefore finite. This is the already classical
postcritically finite regime, not a new infinitely renormalizable mechanism.

### 5B. Finite-dimensional span on a parameter fiber

**Candidate:** finite-dimensionality of the restrictions of all critical-iterate
polynomials to a connected parameter fiber forces that fiber to be a singleton.

**Decision: discard; elementary polynomial separation.** Since the nonconstant
polynomials `P_n` have distinct degrees, a linear dependence among their
restrictions supplies a nonzero polynomial vanishing on the fiber. Its zero
set is finite, so a connected nonempty fiber is a singleton. This puts the
separation into the assumed algebraic compression; no new quadratic dynamics
is used beyond the distinct degrees.

## 6. What a viable successor must add

The common failure is the absence of a finite-displacement argument for actual
parameters in a potentially non-path-connected fiber. The classical topological
endpoint already exists. Finite PCF rigidity and infinitesimal contraction do
not provide the missing finite-displacement argument in this investigation.

A future single-map transfer-operator route would have to specify actual
orbit-marked configurations, compare their growing marked spaces, and prove
that two distinct parameters in one fiber create a nonzero defect that the
proposed condition independently forces to vanish. That sentence is a research
problem, not a proved reduction and not a retained candidate theorem.

The requested new mathematics has not been obtained. No screened statement was
formalized simply to create a compiling but mathematically noncompliant output.
