# Kernel-checked real period-27 quadratic center: IVT, MVT, and exact minimal period

**2026-11-05 · status:** A genuine mathlib formalization of the **real one-dimensional polynomial** analytic bridge, building on existing source-locked rational interval certificates. This closes the original *real center* existence, uniqueness, calculus-derivative and minimal-period gap noted in [the earlier rational arithmetic audit](period27_rational_interval_soundness_20261105.md); it does not close any global MLC gate.

## Exact mathematical statement

For the real quadratic map \(f_c(x)=x^2+c\), write \(P_j(c)=f_c^j(0)\). Fix the exact signed integer

\[
K=-607890580437450502081459824019535455703.
\]

The pinned Lean 4.32.0 + mathlib 4.32.0 kernel now proves

\[
\boxed{
\exists!\,c\in\left(K/2^{128},(K+1)/2^{128}\right)
:\quad P_{27}(c)=0\ \land\forall j\in\{1,\ldots,26\},\ P_j(c)\ne0.
}
\]

Thus the critical point has **minimal period exactly 27** under the *actual real quadratic polynomial*. This result is restricted to one unique parameter **inside the stated bracket**; it does not assert uniqueness of period-27 parameters globally or locate a parabolic component root.

## Proof dependency chain and Lean statement inventory

The source certificates are [Period27Dyadic.lean](../../Period27Dyadic.lean), [Period27IntervalSound.lean](../../Period27IntervalSound.lean), [Period27RationalTrace.lean](../../Period27RationalTrace.lean) and [Period27RationalDerivative.lean](../../Period27RationalDerivative.lean). They establish the exact dyadic bounds and prove universal enclosure correctness for rational arithmetic, along with a strict negative derivative-recurrence enclosure on the whole input interval.

**[Period27RealCenter.lean](../../formalization/weighted/Period27RealCenter.lean):** Defines the exact signed-fraction value in \(\mathbb R\), proves fraction addition/multiplication/squaring commute with real evaluation, and proves the entire rational joint orbit/derivative recurrence commutes with the corresponding real recurrence for **every** iteration count. Its theorem `hasDerivAt_polynomial` proves

\[
P'_j(c)=D_j(c),\qquad
D_0(c)=0,\qquad D_{j+1}(c)=2P_j(c)D_j(c)+1
\]

for every natural \(j\) and real \(c\), using ordinary calculus rather than an unverified algebraic-derivative label. The exact source rational endpoints then have the corresponding real signs \(P_{27}(K/2^{128})>0>P_{27}((K+1)/2^{128})\). By continuity and mathlib's intermediate-value theorem, `exists_real_period27_root` constructs a **real** root strictly between them.

**[Period27RealUniqueness.lean](../../formalization/weighted/Period27RealUniqueness.lean):** Proves the equivalence between integer cross-multiplied enclosure and real inequalities for every positive-denominator exact fraction. The existing *uniform*, negative integer upper bound on the period-27 derivative gives a **single fixed real number** \(M<0\) satisfying \(D_{27}(q)\le M\) for **all rational** \(q\) inside the parameter bracket. The reusable `continuous_cap_of_rationals` lemma uses rational density, closed intervals and continuity to extend the *same bound* to **all real** parameters, including irrational points and the bracket endpoints:

\[
\forall c\in[K/2^{128},(K+1)/2^{128}],\qquad
P'_{27}(c)=D_{27}(c)\le M<0.
\]

Crucially, this is **not** the invalid inference that a limit of arbitrary strictly negative rational values must remain strictly negative. The strict negative margin \(M<0\) is preserved by first proving the uniform non-strict bound \(D_{27}(c)\le M\). Mathlib's mean-value/strict-antitonicity machinery proves `exists_unique_period27_center_in_dyadic_bracket`.

**[Period27RealExactPeriod.lean](../../formalization/weighted/Period27RealExactPeriod.lean):** Proves that the arbitrary-horizon source rational **orbit** enclosures extend to every real parameter in the full bracket: `real_orbit_bounds`. Its finite kernel calculation `all_first_26_orbit_bounds_strict` checks all 26 pre-return enclosures have **strictly nonzero sign**. The theorem `real_no_early_critical_return` then proves \(P_j(c)\ne0\) for *all real bracket parameters* and all \(1\le j<27\). The final `exact_real_quadratic_period27` theorem identifies \(P_j(c)\) with the repo's already-defined **physical self-map iteration**, and proves uniqueness of the parameter with exact minimal critical period 27.

All of these modules are actual Lean theorem scripts checked by the kernel; the finite arithmetic is recomputed rather than accepted as untrusted output. The main theorems' `#print axioms` reports only Lean's standard `propext`, `Classical.choice` and `Quot.sound`, with **no `sorryAx` or added mathematical axioms**.

## What is—and is not—proved

**Proved in Lean:** arithmetic soundness of the particular exact certificates, calculus identity for the real polynomial recurrence, exact real IVT existence, uniform strictly negative real derivative, real uniqueness inside the dyadic bracket, and absence of all 26 early returns.

**Not proved in this increment:** the real restrictive interval geometry \(I_9\Subset I_3\), holomorphic degree-two quadratic-like restrictions and their complex-domain topology, component-root identification, external-ray landing, prime ends, complete sheet/coset transport, and the Kahn–Lyubich state used by the global reduction. Existing independent source-level and Python certificates for some of these properties remain separate and should not be mistaken for Lean theorems.

In particular this center is **superattracting**, so its ambient filled Julia set has nonempty interior: it **does not satisfy Paper 2's \(K(f)=J(f)\) hypothesis**. The ledger's `H1_MARKED_CONSTRUCTION`, `H2_CALIBRATION`, `H3_COERCIVITY`, `H4_RIGIDITY`, universal protected-tower closure, and **Mandelbrot Local Connectivity** all remain open. No statuses or count in the source-locked 465-entry ledger change.

This is a completed **real-analytic formal verification subproblem** and a reliable testbed for future source-compatible geometric formalizations, not a proof of a new case of MLC.

## Reproduce

The three new modules live in the independent pinned mathlib workspace:

```bash
cd formalization/weighted
lake exe cache get
lake build Period27RealCenter Period27RealUniqueness Period27RealExactPeriod
lake build
```

The workflow [weighted-lean.yml](../../.github/workflows/weighted-lean.yml) checks the entire library and rejects `sorry`, `admit`, and new `axiom` declarations in the audited mathlib modules. For the final source SHA, inspect that SHA's green Actions run, including the kernel diagnostics. Mathematical interpretation must still be reviewed independently of successful compilation.

**AI assistance disclosure:** OpenAI GPT-6 materially assisted in proof design, Lean 4/mathlib code and tactics, debugging against the pinned GitHub Actions compiler, and this audit. The proof checker validates the encoded statements; AI-generated text is not a scholarly primary source, and a complex-dynamics specialist has not endorsed the missing geometric applications.
