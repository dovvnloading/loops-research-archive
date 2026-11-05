# Kernel-checked rational interval soundness and the period-27 algebraic recurrence

**2026-11-05. Scope: an actual partial closure of [Issue #15](https://github.com/dovvnloading/loops-research-archive/issues/15).** The original Lean modules computed outward-rounded integer intervals but did **not** formally prove that those operations enclosed the exact values. This increment develops a generic, mathematical proof for arbitrary rational inputs represented by signed integer numerator and positive integer denominator.

It does **not** assert that a real root of the period-27 polynomial has been constructed in Lean, or that the MLC analytic and Kahn–Lyubich geometry gates have been closed. The real intermediate-value and mean-value theorems are not imported or formalized here.

## 1. Why the new distinction is substantive

The original certificate at resolution \(2^{-144}\) checked

\[
P_{27}(K2^{-128})\in[4251281,4252485]2^{-144},
\]

\[
P_{27}((K+1)2^{-128})\in[-8835097,-8833684]2^{-144},
\qquad K=-607890580437450502081459824019535455703.
\]

Those assertions were rigorous *provided* the elementary outward interval operations were sound, but the Lean kernel checked only the output of the algorithm. Now the grid bounds and rational orbit representations are linked by an actual theorem.

The proof uses no floating-point values, no external computations inside theorem proofs, no `native_decide`, no `sorry` or `admit`, and no new axioms. It builds with the repository-pinned **Lean 4.32.0** toolchain. Axiom reports distinguish standard foundational dependencies from proof holes.

## 2. Generic outward signed-interval arithmetic

[Period27IntervalSound.lean](../../Period27IntervalSound.lean) proves:

- **Floor/ceiling rounding:** for every integer \(n\) and positive integer scale \(S\),
  \[
  \left\lfloor\frac nS\right\rfloor S\le n
  \le \left\lceil\frac nS\right\rceil S,
  \qquad
  \left\lceil\frac nS\right\rceil
  =-\left\lfloor-\frac nS\right\rfloor.
  \]
- **Signed squaring:** for all integers \(\ell\le x\le u\),
  \[
    \bigl(\ell\le0\le u\ ?\ 0:\min(\ell^2,u^2)\bigr)
       \le x^2\le \max(\ell^2,u^2).
  \]
  The zero-crossing case is handled explicitly.
- **Signed four-corner products:** for any \(\ell_1\le x\le u_1\) and \(\ell_2\le y\le u_2\), the exact product \(xy\) is between the minimum and maximum of the four corner products. No nonnegativity assumption is made on either interval.
- **Rounded grid primitives:** the implemented `mulBoundsAt` and `squareBoundsAt` enclose every integer-grid input under the appropriate \(S\)-scaled comparisons.
- **Arbitrary rational arithmetic:** encode the precise rational value \(n/d\) with \(d>0\) by
  \[
  {\rm FractionEnclosed}(S,[\ell,u],n,d)
  \iff
  d>0,\quad \ell d\le nS\le ud.
  \]
  Lean then proves closure under `addBounds`, `doubleBounds`, `mulBoundsAt`, and the zero-crossing-aware `squareBoundsAt`—with **arbitrary positive denominators**, not only on-grid inputs.

The rational theorems are important because the exact orbit of a quadratic map generally leaves the fixed dyadic grid immediately; merely proving grid arithmetic would not certify the real polynomial evaluation.

These are universally quantified theorems about signed integers and exact rational representations. They are not copied tables of the period-27 orbit.

## 3. Soundness of the actual quadratic recurrence for any iteration count

[Period27RationalTrace.lean](../../Period27RationalTrace.lean) defines an exact rational fraction \(\operatorname{ExactFraction}(n,d)\) with \(d>0\). Its exact recursion is

\[
x_0=0,\qquad x_{j+1}=x_j^2+c,
\]

using exact integer numerator/denominator operations. The corresponding interval recursion matches the one used in [Period27Dyadic.lean](../../Period27Dyadic.lean).

The theorem **`pointAfterAt_encloses_all_rational_orbits`** is an induction over **every** natural number \(j\). It proves that for any rational \(c\) in a parameter interval, any rational initial \(x\) in a starting interval, and any iterate count, the integer interval program still encloses the exact rational orbit.

This is an end-to-end semantic connection between the generic arithmetic rules and the concrete quadratic iteration. It was not present in the initial numeric-only certificate.

Specializing it to the original exact dyadic endpoints gives two additional actual rational-dynamics theorems:

\[
\boxed{
P_{27}(K/2^{128})>0,\qquad
P_{27}((K+1)/2^{128})<0.
}
\]

The inequalities refer to the exact numerator of the rational function value with a **provably positive denominator**, not simply to the signs displayed by a rounded interval algorithm. The endpoint rational is represented by numerator \(K2^{16}\) or \((K+1)2^{16}\) and denominator \(2^{144}\).

## 4. Uniform parameter-derivative recurrence

[Period27RationalDerivative.lean](../../Period27RationalDerivative.lean) simultaneously propagates exact rational pairs \((x_j,d_j)\) by

\[
x_{j+1}=x_j^2+c,\qquad
d_{j+1}=2x_jd_j+1,\qquad
(x_0,d_0)=(0,0),
\]

and propagates their rounded interval counterparts. The theorem **`joint_rational_trace_enclosed`** proves the signed enclosure semantics for any finite horizon, every rational parameter in the interval and every suitably enclosed initial state.

The kernel's independent interval computation makes its 27th derivative-enclosure upper bound strictly negative. Consequently the theorem **`all_rational_bracket_parameter_derivatives_are_negative`** says that, for *every rational parameter* in the entire \(2^{-128}\) bracket, the corresponding exact **algebraic derivative recurrence** has a negative numerator.

This is a more mathematically meaningful statement than the former bare interval-program inequality. It remains distinct from having a formal Mathlib proof that \(d_{27}(c)=\frac{d}{dc}P_{27}(c)\) as a derivative of a *real* polynomial.

## 5. Precise remaining Issue #15 tasks

The present formalization establishes universal signed rounding, true rational interval semantics, rational polynomial-orbit endpoint signs and a rational parameter-derivative recurrence.

**Still not kernel-formalized in this package:**

1. The continuous real-variable embedding and the general passage from rational interval bounds to all real parameters in the bracket.
2. The analytic derivative identity \(\frac{d}{dc}P_j(c)=d_j(c)\), the real IVT, and the strict monotonicity/uniqueness argument from its negative derivative.
3. A theorem **`exists_unique_period27_center_in_dyadic_bracket`** quantifying over real \(c\), with exact period 27, without assuming the desired existence/uniqueness statement.
4. The complex proper polynomial-like restriction, actual parameter component identification, root-ray landing, prime-end and KL sheet/coset transport, and all global MLC analytic gates.

In particular, a polynomial can have endpoint values of opposite sign without there being a **rational** parameter root. The result above must not be misstated as a rational-root theorem. The existence of a unique **real** root follows mathematically from the classical IVT/MVT plus the newly formalized bounds and is an appropriate next Mathlib-backed formalization target.

The quotient-ring and signed-dyadic soundness methods here may also be useful for certified complex interval calculations, where the earlier Rouché argument still uses written classical theorems.

## 6. Reproduce

From the repository root, under the pinned Lean 4.32.0 toolchain:

    lake build Period27IntervalSound Period27RationalTrace Period27RationalDerivative
    python research/independent_audits/verify_real_nested_3_9.py

The usual `lake build` now includes these modules as default targets, and GitHub Research validation rejects proof placeholders in them. The existing \(2^{-224}\) independent Python verifier and previously merged Lean `Period27Dyadic` / `Period27Kneading` modules remain unchanged.

**Attribution and disclosure:** Interval arithmetic and basic order theory are classical mathematics, not novel propositions in themselves. OpenAI GPT-6 assisted with formal proof construction, counterchecking, CI diagnosis and writing under the archive steward's direction. These are kernel-checked internal mathematical statements, not unaffiliated specialist peer review. The released paper PDFs, source-locked 465-entry ledger, and MLC status are unchanged.
