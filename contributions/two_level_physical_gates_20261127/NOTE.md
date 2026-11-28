---
ledger: NOV26_OPEN_DEPTH_GATES
result: partial
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

<a id="two-level-physical-gates-20261127"></a>

# Uniform physical two-level gates under explicit period separation

## Claim

For every pair of natural numbers

\[
q\ge17,\qquad p\ge10q+30,
\]

there is a real parameter of the **original quadratic polynomial**
\(f_c(z)=z^2+c\) with the physical two-level package described below.
The parameter, complete-disk estimates, pullback components, exact fibers,
and whole closed gate are conclusions, not hypotheses.

The main Lean theorem is
[`TwoLevelPhysicalGates.exists_physical_two_level_gate`](../../formalization/weighted/TwoLevelPhysicalGates.lean):

```lean
theorem exists_physical_two_level_gate (p q : ℕ)
    (hq : 17 ≤ q) (hpq : 10*q+30 ≤ p) :
    ∃ c : ℝ, PhysicalTwoLevelGate p q c
```

This is a proved subcase of the physical-domain problem in
`NOV26_OPEN_DEPTH_GATES`. The arbitrary-depth, designated-tuning, marked
prime-end, and optimal-width clauses of that obligation remain open.

### Exact geometric statement

Put \(n=qp\), \(x_j=f_c^j(0)\), \(d=x_n<0\), and \(\rho=2^{-p}\).
Define the sources as the central components of **complete polynomial
pullbacks**:

\[
V_1=\operatorname{cc}_0\bigl((f_c^p)^{-1}B(0,\rho)\bigr),\qquad
V_2=\operatorname{cc}_0\bigl((f_c^n)^{-1}B(0,23|d|/20)\bigr).
\]

The theorem supplies all of the following in the same dynamical plane.

1. The parameter satisfies \(-2\le c\le-2+20\,4^{-p}\), the first
   critical return is positive and at most \(14\,4^{-p}\), and the
   original polynomial satisfies the exact signed relation
   \(x_{6n}+x_{3n}=0\).
2. Both sources contain zero, are open and connected, and have compact
   closures. The literal restricted polynomial maps are proper and map
   onto the displayed target disks. Every target has exactly two distinct
   preimages in its source except the actual critical value, which has
   exactly one. These are proved cardinalities of the complete fibers.
3. The prescribed collars are quantitative:
   \(\overline{V_1}\subset B(0,\rho/2)\) and
   \(\overline{V_2}\subset B(0,11|d|/10)\). Every point of
   \(\overline{V_2}\) has distance strictly greater than \(|d|/20\)
   from every point outside its target disk.
4. For every \(0\le j\le q\), the **whole phase image**
   \(f_c^{jp}(V_2)\) lies in \(V_1\). For \(1\le j<q\), it misses
   the inner target. Thus the inner map is a first return under the
   induced \(p\)-return map. Separately, every \(1\le j<p\) and every
   \(|z|\le\rho\) satisfy \(|f_c^j(z)|>\rho\), so the outer
   restriction has no premature return in the original polynomial clock.
5. The entire closed physical disk
   \[
   \left\{z:\left|z+\frac34d\right|\le\frac{133}{2000}|d|\right\}
   \subset V_2.
   \]
   Its center uses the signed scale \(d<0\); its radius uses \(|d|\).
6. Write \(H(z)=f_c^n(dz)/d\). For every
   \(s\in[63/1000,33/500]\), there is a point \(z\) on
   \(|z+3/4|=s\), with \(dz\in V_2\), such that
   \(\operatorname{Re}H(z)=0\), \(\operatorname{Im}H(z)>0\), and
   \(H^2(z),H^3(z)\) are real. Moreover,
   \[
   -999/1000< H^3(z)<-977/1000,
   \qquad H^3(z)<-H^4(0).
   \]
   The statement is a witness on every radius, not a continuous selection
   of an arc or a KKL Wave assertion. The positive imaginary sign is in
   the displayed signed normalized coordinate.

## Evidence

Initial research baseline: `665e5f942d6b39902272fe6d8ca2dee6fbca8a6f`.
The final branch incorporates main through
`fe12f2a86cab3be5d610fcf37781c3ea5e8c3c64`.

### What is new, and what is inherited

The [written all-period audit](../../research/independent_audits/real_primitive_tip_family_all_p_20261116/NOTE.md),
Proof II, already contains the \(14\,4^{-p}\) outer window, a chart
reaching the monic parameter \(-2\), and complete outer-return remainder
bounds. Its equations (13)–(14) already use the monic normalization.
Those facts are inherited infrastructure; their new Lean interfaces are
not counted as new mathematics.

The [previous depth-two audit](../../research/independent_audits/tip_family_renormalization_depth_20261116/NOTE.md),
§5, already gives the fixed-inner-period perturbation and shooting route.
Its error contains
\(22(5^{6q}+5^{3q}-2)4^{-p}\), and it requires locating
period-dependent rational chart constants before obtaining a sufficiently
large outer period. The perturbation mechanism and the factor-five
recursion are therefore also inherited ideas.

The increment here is a **single explicit region with both periods
unbounded**, eliminating the period-dependent chart and stability
premises, and proving the complete moving normalization and physical
source/gate geometry throughout that region. The theorem does not ask for
a preselected parameter, tuned copy, reference neighborhood size,
transversality constant, normalized error, or physical domain. An expanded
search of the archive's research notes, papers and contributions found no
prior explicit uniform regime \(p\ge Cq\) with this complete second-return
and physical-gate package. This is an archive-relative novelty assessment,
not a claim of independently established literature-wide priority.

### Proof architecture

Let \(A_p(c)\) be the exact coefficient of \(z^2\) in \(f_c^p(z)\).
The literal monic outer map and its parameter are

\[
G_c(u)=A_p(c)f_c^p(u/A_p(c)),\qquad
\tau(c)=A_p(c)x_p(c).
\]

The proof has five substantive steps.

1. **A parameter interval for the actual outer map.** The complete
   inverse-branch shooting construction supplies an interval whose monic
   parameter covers the full reference \(q\)-return chart near \(-2\).
   It gives \(-A_p4^{-p}>3/20\), the first itinerary, and
   \[
   |G_c(u)-(u^2+\tau(c))|\le128\,4^{-p},\qquad |u|\le12/5.
   \]
   A complete even divided difference proves that the only collisions of
   this literal map on the entire disk are \(u=v\) and \(u=-v\).
2. **Uniform reference margins and actual shooting.** On the whole
   reference chart, its return scale lies between \(7\,4^{-q}\) and
   \(12\,4^{-q}\). The two endpoint signed relations have opposite
   margins larger than \(4^{-q}/10000\). The explicit inequality
   \[
   128\,4^{-p}5^{6q}\le10^{-8}4^{-q}
   \]
   follows from the stated period separation. It transfers the endpoint
   signs to \(A_p(c)(x_{6qp}(c)+x_{3qp}(c))\). An intermediate-value
   argument selects a zero of this actual original-polynomial relation.
3. **The changing critical normalization.** Put
   \(D=G_c^q(0)=A_p(c)d>0\). The proof controls both the input change
   from the reference scale to \(Dz\) and the output division by \(D\).
   It establishes, for every \(|z|\le23/20\),
   \[
   \left|\frac{G_c^q(Dz)}D-(1-\kappa_q(\tau(c))z^2)\right|
   \le\frac1{500000},
   \quad
   \kappa_q(\tau(c))\in[17903/10000,17904/10000].
   \]
   The left map is proved exactly equal to \(f_c^{qp}(dz)/d\).
   The coefficient in the displayed interval belongs to the reference
   comparison quadratic; it is not asserted to be the exact quadratic
   coefficient of the physical second return.
4. **Whole-domain fibers and phase control.** Every intermediate
   \(G_c\)-phase of the second input disk remains within \(1/5\) of its
   reference critical phase. The latter has absolute value at least
   \(7/5\) at every noncentral time. This excludes antipodal intermediate
   collisions and gives exact signed fibers of the complete second
   return. It also gives the quantitative noncentral exclusion and the
   nesting of every complex phase in the same outer source.
5. **The physical components and closed gate.** The approximation gives
   a whole-circle barrier at radius \(11/10\) against target radius
   \(23/20\). Properness and openness of the original polynomial give
   surjectivity of the selected component. Exact signed fibers and
   symmetry exhaust every small-image point in the barrier, placing the
   whole closed gate disk in that component. Signed affine transport
   identifies it with the full physical pullback component. The archived
   crest-persistence theorem then applies to the actual normalized map,
   with all of its hypotheses supplied by the new uniform construction.

No polynomial truncation, sampled-circle test, floating-point sign
predicate, or unproved tuning identification is used in these Lean proofs.

### Lean modules and validation

| Module | Role |
|---|---|
| `TwoLevelOuterChart` | Literal monic chart and complete outer error/collision bounds |
| `TwoLevelReference` | Whole-reference-chart return, sign and phase margins |
| `TwoLevelPerturbation` | Full complex iteration and moving-scale normalization |
| `TwoLevelConjugacy` | Exact identities in the original quadratic dynamics |
| `TwoLevelCollisions` | Complete second-return fibers through every phase |
| `TwoLevelSelection` | Unconditional original parameter selection in the uniform region |
| `TwoLevelOuterDomain` | Actual outer source, collar, fibers, first return and phase entry |
| `TwoLevelGateDomain` | Central component, quantitative inner collar and closed gate |
| `TwoLevelPhysicalGate` | Sign-correct physical component, map, fibers and disk |
| `TwoLevelPhysicalGates` | Combined existential theorem and full phase nesting |

Local validation with the repository's Lean 4.32.0 toolchain:

```sh
cd formalization/weighted
lake build TwoLevelPhysicalGates
cd ../..
python code/contribute.py check
```

The combined theorem and all ten modules compile locally. A targeted audit
using the repository's `audit_command` and `Lean.collectAxioms` checked
**422 compiled declarations**, including **372 theorem declarations** and
**56 private declarations**. The exact union of transitive axiom dependencies
is `{propext, Classical.choice, Quot.sound}`. Counts include Lean-generated
declarations. No additional axiom or proof escape occurs.

Every source module and public theorem is registered with the contribution
tooling under the `DEPTH` route. The unchanged weighted Lean CI compiles the
whole registered project and audits every compiled declaration; green checks
at the submitted PR head are required before the draft is marked ready.
See [PR #254](https://github.com/dovvnloading/loops-research-archive/pull/254)
for the committed development and CI record.

Five archived files have only their broad Mathlib import headers replaced
by explicit imports: `NearTwoInverse`, `LimitingCrestParameter`,
`LimitingCrestPerturbation`, `StationarySeparatorTransport`, and
`QuadraticCylinderCensus`. Their statements and proof bodies are unchanged.
This removes the unnecessary full-Mathlib dependency from the new proof's
local build chain; it is not a mathematical contribution.

## Dependencies

Ledger dependency: `NOV26_DEPTH3` supplies the problem's finite-depth
context, not an unproved assumption in the main Lean theorem.

Mathematical infrastructure comes from the archived all-period and
fixed-inner-period arguments cited above, and the compiled
`NearTwoShooting`, `CriticalReturnRelationStability`,
`LimitingCrestQuadraticReturn`, `QuadraticCrestDividedDifference`,
`LimitingCrestPersistence`, `ThreeReturnDomain`, `ThreeReturnDegree`, and
`ThreeReturnParent` developments. Standard topology, complex arithmetic,
and polynomial properness come through Mathlib and those existing proofs.

The [all-depth audit](../../research/independent_audits/tip_family_all_depths_20261116/NOTE.md),
§§1 and 3, distinguishes prescribed physical domains from optimal
polynomial-like modulus. Its cited Lyubich–Yampolsky complex bounds and
Douady–Hubbard theory are background here, not new axioms or substitutes
for the displayed disk estimates. The new theorem does not invoke a
straightening or KKL identification.

## Boundary

`NOV26_OPEN_DEPTH_GATES` remains **open**. This packet proves the stated
uniform two-level physical-domain subcase, not its full ledger statement.
In particular:

- The periods obey \(q\ge17\) and \(p\ge10q+30\). The theorem covers neither
  all pairs of large periods nor arbitrary finite depth; the condition
  is not claimed optimal.
- The parameter is existential. Uniqueness, a canonical tuning label,
  complete kneading/primitive identification, and equality with a
  previously designated tuned parameter are not proved.
- The sources are proved open, connected, compactly contained, proper,
  and to have exact one/two-point fibers. A separate formal
  simply-connected/Jordan-source, connected-filled-Julia, or straightening
  theorem is not included. These labels must not be silently added.
- The whole closed disk and per-radius crest witnesses are physical.
  Continuous witness selection, terminal three-return geometry, complete
  terminal cut order, marked slit prime ends, KKL Wave realization,
  optimal widths, and width transport remain outside this result.
- The uniform collars and gate sizes are relative to the actual return
  scales; no positive absolute physical radius independent of the
  periods is claimed.
- No H1–H4 conclusion, new MLC/JLC conclusion, or literature-wide novelty
  priority is asserted.

## Attribution

The written archive already supplies the outer monic normalization and
fixed-inner-period perturbation method. This packet's contribution is the
explicit simultaneous period region and complete second-normalization,
parameter-selection and physical-gate theorem described above. The proof
uses the existing Lean archive and Mathlib without changing their
mathematical statements.

Developed with OpenAI ChatGPT GPT-6 Astra Pro, with separate AI reviews of
parameter dynamics, physical domains, novelty relative to the archive,
and transitive proof dependencies. These reviews are not human peer review;
`human_review: none` remains accurate.
