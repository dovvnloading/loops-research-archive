# Candidate audit before formalization

Baseline: main at `637266b909d5e7566d8e39141f3b135e3405f38f`.
This is a research log, not a new theorem or a claimed obstruction to MLC.

## 1. Exact archive boundary

The open ledger hypothesis is `UNIVERSAL_PROTECTED_TOWER_CLOSURE`, called
the Universal Protected-Tower Compactness and Rigidity Proposition (UPTCR).
Its statement quantifies over every infinitely renormalizable quadratic and
requires all six clauses: actual canonical carriers; exact analytic realization;
uniformly finite response data; a universal backward transition; coercive marked
compactness; and rigidity with a singleton parameter fiber and connected relative
parameter neighborhoods. Constants are chosen before the polynomial and tower.

The written conditional implication is Theorem 7.2 of
[`mlc_closure_proposition.md`](../../research/mlc_unified/mlc_closure_proposition.md).
The ledger `UPTCR_IMPLIES_MLC` explicitly records UPTCR as its hypothesis.
None of the individual construction, compactness, or rigidity gates is discharged
by the logical implication.

[`ResearchGates.lean`](../../ResearchGates.lean) is explicitly a specification
layer. Its `conditional_local_connectivity` consumes `ComplementTheorem`,
`UniversalPackage`, and a separately assumed `TerminalBridge`.
Its `Program.locallyConnected` is an arbitrary predicate; the file is not a
Lean proof of local connectivity of a subset of the complex plane. Its own
`no_bridge_does_not_imply_local_connectivity` guards this distinction.

## 2. Candidate A: refine internal addresses to distinguish fiber points

Proposed statement: some enrichment determined entirely by angled internal
addresses distinguishes any two parameters in the same nonhyperbolic
combinatorial class.

**Rejected before formalization.** Schleicher's Theorem 3.9 identifies equality
of angled internal addresses with equality of combinatorial class. Any function
of that invariant is constant on the class. The rejection applies to constructions
that factor through the established class, not to all possible new invariants.

Reference: D. Schleicher, *Internal Addresses of the Mandelbrot Set and Galois
Groups of Polynomials* (2017), Definition 3.8, Theorem 3.9 and its proof in Section 5:
<https://amj.math.stonybrook.edu/html-articles/Files-2015-2024/16-42/>.

## 3. Candidate B: injectivity of the pinched model gives MLC

Proposed statement: an injective continuous quotient from the actual Mandelbrot
set onto its locally connected model implies local connectivity.

**Rejected as a new contribution.** The compact-to-Hausdorff bijection argument
is ordinary topology. The actual fiber-to-local-connectivity implication is
classical. The new content would have to be a quadratic-dynamical condition
forcing injectivity, proved without encoding that conclusion in the premise.

Reference: D. Schleicher, *On Fibers and Local Connectivity of Mandelbrot and
Multibrot Sets* (1999 preprint; 2004 publication):
<https://arxiv.org/abs/math/9902155>. The companion general-fiber paper is
<https://arxiv.org/abs/math/9902154>.

## 4. Candidate C: finite Thurston contraction controls an infinite fiber

Proposed statement: a uniform contraction estimate for finite postcritically
finite approximants forces triviality of the limiting parameter fiber.

**Not accepted for formalization: the essential bridge has not been proved.**
One must specify changing marked Teichmuller spaces, compatible comparison maps,
the norm, and how this information constrains the full limiting parameter fiber.
These cannot be replaced by an assumed terminal implication.

Finite contraction and postcritically finite rigidity are classical.
Buff--Epstein--Koch identify the pushforward on quadratic differentials with the
cotangent operator of pullback. Their Theorem 1.4 puts the relevant quadratic
center eigenvalues in 1/8 < |lambda| < 1. Theorem 1.5 gives global accumulation
up to the unit circle. Neither theorem states degeneration along every chosen
center sequence converging to every infinitely renormalizable parameter.

An operator norm, a spectral radius, and uniform estimates across growing
dimensions are different assertions. The suggested universal degeneration is
therefore not used as a fact here.

Reference: X. Buff, A. L. Epstein, S. Koch, *Eigenvalues of the Thurston operator*,
J. Topology 13 (2020), 969--1002, introduction and Theorems 1.4--1.5:
<https://websites.umich.edu/kochsc/eigenvalues.pdf>,
<https://doi.org/10.1112/topo.12145>.

## 5. Candidate D: rational critical-orbit generating function

Proposed statement: if z_0 = 0, z_(n+1) = z_n^2 + c satisfies a nonzero
constant-coefficient linear recurrence, then its orbit is eventually periodic.

**Rejected before formalization as an elementary general consequence of
polynomial iteration, not an MLC advance requiring a new idea.**

Indeed, write sum_(i=0)^r a_i z_(n+i) = 0 for all sufficiently large n, with
a_r nonzero. Put P(X) = sum_(i=0)^r a_i f_c^i(X). The highest degree is 2^r,
unique to its last summand, so P is nonzero. Every sufficiently late z_n
is a root of P because z_(n+i) = f_c^i(z_n). A nonzero polynomial has only
finitely many roots. A deterministic orbit confined to that finite set is
eventually periodic. The same argument works for every polynomial of degree
at least two over any field.

This is recorded only to explain the rejection. It is not offered as a novel
theorem, a Lean result, or a new MLC case.

## 6. Formalization gate

No candidate above has survived both the novelty and proof requirements.
There is no new Lean theorem at this checkpoint.

A theorem in a future checkpoint must use the actual quadratic orbit and the
actual Mandelbrot parameter locus. Main already provides
`QuadraticEscape.parameterEscape_zero_iff`, identifying zero escape with a
bounded critical orbit. It does not provide a formal parameter separation fiber
or the analytic Thurston-to-fiber bridge. Defining a convenient arbitrary set
as a 'fiber' would not supply that missing identification.

The next candidate under investigation allows polynomial-in-time recurrence
coefficients. This is only a candidate, not an established result.
