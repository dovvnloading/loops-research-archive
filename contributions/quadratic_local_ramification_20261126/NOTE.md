---
ledger: VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-local-ramification-20261126"></a>

# Actual quadratic ramification conservation and critical-anchor exhaustion

## Claim

For the actual complex quadratic \(f_c(z)=z^2+c\), exact local polynomial orders conserve the intrinsic degree on every fiber of every connected component of a finite pullback of an open connected target. Critical target values and repeated critical returns are included. This yields a weighted component-exhaustion test at an arbitrary anchor, exact critical-point budgets, finite-time composition laws, and a closed formula for the number of distinct analytic critical points of every iterate.

These are finite-horizon theorems for all complex parameters and all natural horizons. They are partial progress on the named obligation; the native authorized virtual-cylinder family is not realized.

## Evidence

### 1. Exact local orders and weighted degree

Let \(V\subseteq\mathbb C\) be open and preconnected, let \(f_c^{\circ n}(x)\in V\), and put
\[
C=\operatorname{Comp}_x((f_c^{\circ n})^{-1}(V)),\qquad
\nu_n(z)=\#\{0\le j<n:f_c^{\circ j}(z)=0\},\qquad m_n(z)=2^{\nu_n(z)}.
\]
The membership hypothesis ensures nonemptiness. The theorem **localMultiplicity_exact_order** certifies that \(X^{m_n(z)}\) divides the actual translated iterate difference and \(X^{m_n(z)+1}\) does not. The weight is therefore an exact polynomial local order, independently justified by the archive's nonvanishing local-factor theorem.

Write \(R=\texttt{componentReflectionRank}(c,V,n,x)\), the preexisting count of reflection-invariant steps along the actual component itinerary. The new theorem **quadratic_component_weighted_fiber_degree** proves, for every \(y\in V\),
\[
\sum_{\substack{z\in C\\f_c^{\circ n}(z)=y}}m_n(z)=2^R.
\]
The sum is over distinct actual inverse points. Neither a regular target point nor simple connectivity of \(V\) is required.

On a nonsymmetric first sheet, the quadratic is injective and zero is absent, so weights transport unchanged. On a symmetric sheet, signed inverse branches supply two copies except over the critical value; there the single inverse zero has twice the tail weight. Induction yields conservation even at that collision. The theorem **quadratic_component_defect_eq_ramification_sum** then identifies the earlier recursive target-wise defect with the sum of \(m_n(z)-1\) over the actual fiber.

### 2. Exhaustion at a critical anchor

For open preconnected \(U\subseteq V\), \(y\in U\), the actual old-component census \(\mathcal C\) inside \(C\), and a declared finite subfamily \(T\subseteq\mathcal C\), **mergerCensus_complete_iff_weighted_degree** proves
\[
T=\mathcal C\quad\Longleftrightarrow\quad
\sum_{D\in T}\ \sum_{\substack{z\in D\\f_c^{\circ n}(z)=y}}m_n(z)=2^R.
\]
This removes the regular-anchor premise of the previous degree-based test. Equal old-component degrees and univalence are not assumed. The weighted partition counts each inverse point in its unique old component, and every census entry has positive mass; a missing component makes the sum strictly smaller.

The subfamily premise concerns actual components. The existing proper_piece_mem_mergerCensus theorem can derive membership for independently supplied nonempty connected proper open pieces under its geometric hypotheses. This packet does not assert that the native virtual family supplies those hypotheses.

### 3. Intermediate times

The module proves the exact local composition law
\[
m_{m+n}(z)=m_m(z)m_n(f_c^{\circ m}(z)).
\]
It identifies the original pullback component with the pullback of its actual intermediate component, proves weighted conservation on every intermediate fiber, and proves additivity of the intrinsic reflection rank under any finite-time split. These statements retain the actual planar component throughout.

### 4. The analytic critical locus and its budget

The finite set criticalPoints is the union of actual inverse fibers of zero through times \(0,\ldots,n-1\), restricted to the specified planar set. Points are counted once. The theorem **mem_criticalPoints_iff_deriv** identifies it literally with the zero set of the complex derivative.

The new component budget is
\[
\sum_{z\in\operatorname{Crit}(f_c^{\circ n})\cap C}(m_n(z)-1)
+\operatorname{Debt}(c,V,n,x)+1=2^R.
\]
Debt is the archive's independently recursive missing-critical-charge correction. It remains present for targets with holes. The distinct critical count is bounded by this budget.

On the whole plane the proof establishes \(R=n\) and debt zero, giving the unconditional identity
\[
\sum_{z\in\operatorname{Crit}(f_c^{\circ n})}(m_n(z)-1)=2^n-1
\]
for every complex parameter and horizon, including repeated critical returns.

### 5. Exact distinct critical-point counts

For \(a_n=\#\operatorname{Crit}(f_c^{\circ n})\), actual signed inverse branching proves that the next count is \(2a_n+1\) before any positive return of zero of length at most \(n\), and \(2a_n-1\) once such a return has occurred. Lean states this using natural-number addition, avoiding hidden subtraction assumptions.

Consequently:

- If zero has no positive return before \(n\), then \(a_n=2^n-1\).
- If \(p>0\) is its first positive return and \(n\ge p\), then \(a_n=(2^p-2)2^{n-p}+1\).

The strict “before \(n\)” boundary is essential. Three exact infinite-family corollaries give one critical point for \(c=0\) at every positive horizon, \(2^{n+1}+1\) at horizon \(n+2\) for \(c=-1\), and \(2^n-1\) at horizon \(n\) for \(c=-2\).

### 6. Formal sources

| Lean module | Public theorems | Role |
|---|---:|---|
| [QuadraticLocalRamification.lean](https://github.com/dovvnloading/loops-research-archive/blob/4894e7dd1a6f7c07b92191222f4aa2ffc78f04d6/formalization/weighted/QuadraticLocalRamification.lean) | 20 | Local orders, conservation, composition, critical-anchor exhaustion |
| [QuadraticRamificationCensus.lean](https://github.com/dovvnloading/loops-research-archive/blob/4894e7dd1a6f7c07b92191222f4aa2ffc78f04d6/formalization/weighted/QuadraticRamificationCensus.lean) | 13 | Derivative critical locus, component budget, global identity |
| [QuadraticCriticalPortrait.lean](https://github.com/dovvnloading/loops-research-archive/blob/4894e7dd1a6f7c07b92191222f4aa2ffc78f04d6/formalization/weighted/QuadraticCriticalPortrait.lean) | 11 | Exact count, first-return formula, concrete families |

All 44 named public theorems are registered, and all three modules are default weighted Lake targets. Generated auxiliary declarations are also audited.

### 7. Validation

The proof-bearing commit [4894e7d](https://github.com/dovvnloading/loops-research-archive/commit/4894e7dd1a6f7c07b92191222f4aa2ffc78f04d6) passed the full project build and the unchanged transitive-axiom audit in [Weighted spectral mathlib proofs run 45901339666](https://github.com/dovvnloading/loops-research-archive/actions/runs/45901339666/job/140187578669).

The build completed successfully with 8,870 Lake jobs. The audit reported:

~~~text
AXIOM_AUDIT weighted QuadraticLocalRamification: 46 declarations, 45 theorems; allowed axioms only
AXIOM_AUDIT weighted QuadraticRamificationCensus: 30 declarations, 28 theorems; allowed axioms only
AXIOM_AUDIT weighted QuadraticCriticalPortrait: 48 declarations, 47 theorems; allowed axioms only
AXIOM_AUDIT_PASS weighted: 100 modules, 2677 declarations
~~~

The compiled counts include generated and private declarations; the source-level public theorem count is 44. The audit checks transitive dependencies of every weighted declaration and permits only propext, Classical.choice, and Quot.sound. No new axioms, sorry, admit, native_decide, or trust-policy changes were introduced.

All 23 CI workflows associated with this proof commit passed, including source coverage/trust checks, contribution intake, research validation, and model-to-geometry coverage. The existing adversarial coverage regression suite also passed all 10 tests during development. These integration checks supplement the Lean build and axiom audit.

Reproduce with the pinned Lean 4.32.0 and Mathlib v4.32.0 environment:

~~~sh
cd formalization/weighted
lake exe cache get
lake build
cd ../..
python3 -B code/verify_lean_coverage.py --audit weighted
python3 -B code/contribute.py check
~~~

The draft PR preceded proof implementation, and proof checkpoints and compiler-driven corrections were committed throughout. Corrections changed proof scripts, not statements or hypotheses. Shared-registry merges preserved concurrent research. Workflows and the trust policy were unchanged.

Local Lean execution was unavailable because the exact environment exceeded workspace capacity. The existing CI compiler and kernel dependency audit provide validation; the Python contribution check is not a mathematical proof.

## Dependencies

Ledger prerequisites: DIRECT_DECORATION_PULLBACK_COMPACTIFICATION, FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS, and INTERIOR_PULLBACK_COMPONENT_FORCING.

Existing formal modules supply:

- QuadraticCriticalWindow: exact local factorization and critical encounters.
- QuadraticCriticalTransversality: actual orbit/iterate equality and spatial derivative.
- QuadraticCriticalFiberCensus: finite inverse fibers and signed branches.
- QuadraticCylinderRamification: actual component transport.
- QuadraticComponentFiberDegree: reflection rank and distinct-point defect.
- QuadraticEnlargementDegree: merger census and aggregate deficit/debt identity.
- Mathlib: finite sums/sets, complex polynomial algebra, differentiation, connected components.

Source-facing context is [finite-cylinder commuting lift](../../research/mlc_unified/finite_cylinder_commuting_lift.md), the preceding [component fiber degree](../quadratic_component_fiber_degree_20261126/NOTE.md), and [enlargement degree conservation](../quadratic_enlargement_degree_conservation_20261126/NOTE.md).

## Boundary

The theorems concern actual quadratic iterates and actual planar components. They do not identify the authorized virtual-cylinder family with the complete census. Target selection, localization, marked accesses, chronology, sheet metadata, and native enlargement certificates remain open. The exhaustion theorem proves a criterion, not that the native family passes it.

The component budget retains its correction term. No zero-debt theorem for all simply connected or full targets is claimed. The zero-debt specialization proved here is the whole plane.

The ledger obligation stays open; no status change is proposed. H1–H4, UPTCR and MLC remain open. No literature-priority claim. Human review: none.

## Attribution

This extends the archive's critical-window, inverse-fiber, component-degree, and enlargement-census formalizations using Mathlib. The decoration/cylinder motivation comes from the Kahn–Lyubich work already cited in the archive; no external analytical theorem is newly assumed. AI assistance supplied proof development, independent statement review, integration and CI repair. The exact compiled Lean statements are the evidence.
