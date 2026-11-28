---
ledger: UNIVERSAL_PROTECTED_TOWER_CLOSURE
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-fiber-criterion-20261128"></a>

# Mixed quadratic susceptibility implies pointwise Mandelbrot local connectivity

**Kernel-validated conditional result.** The complete weighted Lean build and
strict transitive dependency audit passed on proof revision
`4c983dc32f31573bb62bdb9797ac91e6064b0819` in
[repository CI run 46129770396](https://github.com/dovvnloading/loops-research-archive/actions/runs/46129770396).
All three new modules compile without proof gaps or added axioms. The final
source theorem includes the implication to actual pointwise Mandelbrot local
connectivity; that implication is not left as a proposed application.

## Claim

The new pattern is to compare two actual critical orbits at finite parameter
separation, and sum the reciprocal products of their mixed coefficients.
This produces an exact obstruction to a nontrivial connected parameter fiber,
without a differentiable motion of that fiber.

Let
\[
P_0(c)=0,\qquad P_{n+1}(c)=P_n(c)^2+c,\qquad
M=\{c\in\mathbb C:\exists B\in\mathbb R\ \forall n,\ |P_n(c)|\le B\}.
\]
Define
\[
D_0(c,d)=1,\qquad
D_n(c,d)=\prod_{j=1}^n(P_j(c)+P_j(d)),\qquad
Q_n(c,d)=1+\sum_{k=1}^n D_k(c,d)^{-1}.
\]

### The actual-family criterion

Let \(q:M\to Y\) be a continuous surjection onto a Hausdorff locally
connected space, with connected point fibers. Fix \(c\in M\), and let
\(F\subset\mathbb C\) be the complex parameters in \(q^{-1}(q(c))\).
Assume:

1. For every \(d\in F\) and \(j\ge1\), the mixed factor
   \(P_j(c)+P_j(d)\) is nonzero.
2. The complex functions \(Q_n(c,\cdot)\) converge uniformly on \(F\)
   to a function \(L\).
3. \(L(c)\ne0\).

Then the fiber \(q^{-1}(q(c))\) is the singleton \(\{c\}\), and \(M\)
is locally connected at \(c\). More precisely, every neighborhood \(U\)
of \(c\) in the actual subspace \(M\) contains an open connected
neighborhood \(V\) of \(c\).

This is ordinary complex convergence. Absolute summability is not required;
the hypotheses do not assert that absolute summability fails either.
Uniformity is imposed on the specified fiber, with no complex open parameter
neighborhood of convergence required.

The Lean endpoint is
`QuadraticMixedSusceptibility.locallyConnectedAt_of_mixed_susceptibility`.
Its conclusion is the explicit connected-neighborhood basis in the subtype
of the bounded critical-orbit locus. It does not conclude an unnamed terminal
predicate, assume fiber rigidity, or defer local connectivity to a separate
identification.

The map \(q\) remains an explicit topological input. The theorem applies to
any map meeting the stated hypotheses; it does not claim that an arbitrary
map is the canonical pinched-disk projection. Construction and identification
of that canonical projection have not been formalized in this packet.

### Exact open archive hypothesis

The ledger row `UPTCR_IMPLIES_MLC` is marked proved **conditional on**
`UNIVERSAL_PROTECTED_TOWER_CLOSURE`, which remains open. The latter is the
six-clause Universal Protected-Tower Compactness and Rigidity Proposition
for **every infinitely renormalizable quadratic**:

1. canonical protected carriers;
2. exact analytic realization;
3. a uniformly finite observable response state;
4. a universal backward transition including its full error;
5. coercive marked compactness;
6. tower rigidity, singleton parameter fiber, and connected relative
   parameter neighborhoods.

The constants must be selected before the polynomial and tower and be
independent of their periods, rotation data, depths, horizons, markings,
counters, stack lengths, and ordering of regimes. The exact statement is
[the closure proposition, Sections 4–7](../../research/mlc_unified/mlc_closure_proposition.md).
The existing unconditional attempt already stops at UPTCR-1; it does not
supply the universal package.

The archive's complete analytic implication is a written conditional
reduction. Its logical gate formalizations do not themselves provide the
actual analytic instance. This packet proves a different conditional
actual-family route to the pointwise conclusion and does not close UPTCR.

## Evidence

### Candidate before formalization

The exact candidate and primary-source pre-check were committed before any
new Lean source in commit
`773f3d5bdb76d4237999479c1392cd736bf6d637`:
[RETAINED_CRITERION.md](RETAINED_CRITERION.md).
The earlier rejected nonlinear certificate is preserved in
[NONLINEAR_CANDIDATE.md](NONLINEAR_CANDIDATE.md).
The unsuccessful earlier spectral investigation remains in
[closed PR #269](https://github.com/dovvnloading/loops-research-archive/pull/269).

### Complete mathematical proof

Subtracting the two actual quadratic recurrences gives
\[
P_{n+2}(c)-P_{n+2}(d)
=(P_{n+1}(c)+P_{n+1}(d))
 (P_{n+1}(c)-P_{n+1}(d))+(c-d).
\]
Induction and nonvanishing of the mixed products give
\[
(c-d)Q_n(c,d)
=\big(P_{n+1}(c)-P_{n+1}(d)\big)D_n(c,d)^{-1}. \tag{1}
\]

If \(Q_n(c,d)\) converges, its successive differences show
\(D_n(c,d)^{-1}\to0\). If both parameters belong to the actual \(M\),
the orbit difference is bounded. Taking the limit in (1) therefore gives
\((c-d)L(d)=0\). Thus every distinct \(d\in F\) satisfies \(L(d)=0\).

The finite sums \(Q_N(c,\cdot)\) are continuous at \(c\), since all their
finitely many denominators are nonzero there. Uniform convergence on \(F\)
and \(L(c)\ne0\) isolate \(c\) in \(F\): choose one sufficiently late
finite sum with error below \(|L(c)|/4\), then use its continuity near
\(c\). Three triangle-inequality errors below \(|L(c)|/4\) are
incompatible with \(L(d)=0\). A connected set containing an isolated point
contains no other point. This proves the singleton-fiber conclusion.

For the final implication, compactness of the actual \(M\) is proved.
The already formalized continuous quadratic escape function has zero locus
exactly \(M\). The existing escape bound at the second critical iterate
implies
\[
|c|^2\le |c^2+c|+|c|\le 1+2|c|,
\]
so the coarse bound \(|c|\le3\) suffices. Hence \(M\) is closed and
bounded in \(\mathbb C\), and compact.

The map \(q\) is therefore closed. Given \(U\ni c\), first choose an
open neighborhood \(O\subset U\). The singleton-fiber result implies
\(q(c)\notin q(M\setminus O)\). The latter image is closed, so local
connectivity of \(Y\) gives an open connected neighborhood \(W\) of
\(q(c)\) avoiding it. A closed monotone surjection pulls connected sets
back to connected sets. Thus \(V=q^{-1}(W)\) is open and connected,
contains \(c\), and lies in \(U\).

The last topological fact is proved by separation of closed sets: closedness
transfers a hypothetical separation to the target; a connected fiber then
contradicts that separation. It is ordinary supporting topology, not the
novelty claim.

### Lean modules and endpoints

| Module | Main content |
|---|---|
| [QuadraticMixedSusceptibility.lean](../../formalization/weighted/QuadraticMixedSusceptibility.lean) | Actual orbit products; exact finite identity; convergent off-diagonal limit zero; uniform-limit isolation; `connected_set_eq_singleton`. |
| [QuadraticMonotoneFiberTopology.lean](../../formalization/weighted/QuadraticMonotoneFiberTopology.lean) | Closed monotone inverse-image lemma and `connected_open_basis_of_singleton_fiber`. |
| [QuadraticMixedSusceptibilityMLC.lean](../../formalization/weighted/QuadraticMixedSusceptibilityMLC.lean) | Actual Mandelbrot compactness; `monotone_fiber_eq_singleton_of_mixed_susceptibility`; `locallyConnectedAt_of_mixed_susceptibility`. |

Validation commands:

```sh
python code/contribute.py check --pr-title '[UNIVERSAL_PROTECTED_TOWER_CLOSURE] Mixed susceptibility criterion for pointwise Mandelbrot local connectivity'
cd formalization/weighted
lake exe cache get
lake build
cd ../..
python code/verify_lean_coverage.py --audit weighted
```

The three new modules expose **19 registered public theorems**. The unchanged
weighted CI workflow compiled the whole project successfully (9,266 build
jobs) and reported:

```text
AXIOM_AUDIT weighted QuadraticMixedSusceptibility: 33 declarations, 20 theorems; allowed axioms only
AXIOM_AUDIT weighted QuadraticMixedSusceptibilityMLC: 9 declarations, 8 theorems; allowed axioms only
AXIOM_AUDIT weighted QuadraticMonotoneFiberTopology: 2 declarations, 2 theorems; allowed axioms only
AXIOM_AUDIT_PASS weighted: 295 modules, 7739 declarations
```

The audit's theorem counts include internal supporting declarations and are
not the public-theorem index count. Its only permitted foundational axioms
are `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, or
new axiom is used. Contribution intake, source registration, proof-trust
checks, and all other reported workflows also passed for this proof revision.

The complete local Lean/Mathlib runtime did not fit in the workspace; actual
compilation and the full transitive audit were performed in repository CI.
A concurrent mechanical merge synchronized the PR with updated `main` before
the successful run; comparison confirmed that it left all three new Lean
sources unchanged. The final documentation edits likewise change no Lean
source, build target, or theorem registration. No workflow was modified.

## Dependencies

- Lean 4.32.0 and the repository's pinned Mathlib revision
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- `QuadraticEscape.lean`: actual orbit definition, orbit continuity, continuous
  escape function, its bounded-orbit characterization, and escape bound.
  The escape function is used to establish ordinary compactness, not as a
  density criterion.
- Mathlib complex arithmetic, limits, uniform convergence, and topology.
- The elementary closed-map separation proof is adapted from
  `LoopsStationaryMonotoneGeometry.preconnected_preimage_closed_fibers`, with
  explicit attribution in the new source. That archive module and its
  geometric machinery are not imported.

The closest classical results are screened in `RETAINED_CRITERION.md`:

- Rivera-Letelier, IMS 2000/9, Proposition 1.4(1) and the corollary of Theorem D
  already yield MLC in the absolute-summability regime. The absolute version
  was discarded.
- Cabrera–Makienko–Poirier (2020), Proposition 1.2 and Corollary 1.3, use
  conditional one-map derivative sums to establish structural instability.
  They do not supply the finite two-parameter identity on a connected fiber
  and its pointwise local-connectivity consequence.
- Li–Shen, arXiv:0911.0464, Theorem A, assumes finite renormalizability in its
  complex-polynomial derivative-growth implication; that assumption is not
  imposed here.
- Levin–Shen–van Strien, arXiv:1902.06732, provide finite transfer-operator
  transversality and holomorphic-lifting results, not this mixed infinite
  fiber criterion.
- Schleicher, *On Fibers and Local Connectivity of Mandelbrot and Multibrot
  Sets*, arXiv:math/9902155, provides the classical fiber viewpoint and
  fiber-to-local-connectivity implications. No novelty is claimed for that
  general direction of implication or for the supporting topology.

No direct consequence matching the retained analytic criterion was located
in the checked primary sources. This bounded search is not a guarantee of
universal literature priority. The proposed contribution is the exact
nonlinear two-parameter susceptibility reduction and its proved actual MLC
endpoint, not the finite algebra identity or the quotient topology separately.

## Boundary

This is a **conditional sufficient criterion**, not a proof of MLC or of any
of H1–H4, and not closure of the ledger obligation. No ledger status change is
proposed.

No new class of parameters satisfying the susceptibility hypotheses has been
proved. In particular, no infinitely renormalizable example satisfying them
has been exhibited. Establishing uniform convergence on a putative nontrivial
fiber and a nonzero diagonal limit remains the dynamical research problem.
Finite numerical sums cannot establish those hypotheses.

The supplied quotient must meet its stated hypotheses. The canonical
pinched-disk quotient and its identification with combinatorial fibers are
not constructed in Lean here. This limitation does not defer the theorem's
local-connectivity conclusion: the combined Lean theorem has that actual
conclusion directly, under its explicit map and orbit-series hypotheses.

The criterion depends on the exact quadratic recurrence. It contains no
arbitrary family of test observables: off-diagonal vanishing is derived from
two bounded critical orbits. It uses none of the excluded tower machinery,
center denominator arithmetic, encounter charges, geometric-limit arguments,
Green-potential density conditions, or projective cross-ratio jets.

Kernel validation establishes the stated conditional implication, including
its actual local-connectivity endpoint. It does not establish literature-wide
priority or verify the criterion at a new parameter; those are separate
research questions.

## Attribution

Research, source, and formalization generated by OpenAI ChatGPT GPT-6 Astra
Pro with collaborating agents of the same model. No human specialist review.
Classical supporting results and the reused elementary separation argument
are identified above and in the source. All contribution files are released
under the repository's CC0 terms.
