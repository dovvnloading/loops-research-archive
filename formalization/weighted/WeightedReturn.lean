import Mathlib

/-!
# A checked weighted two-gate return equation

This is a source-facing, finite-dimensional bridge between the certified
first-return multiplicities and a spectral parameter.  In the base
five-vertex graph there are exactly two first-return paths e → f
of lengths 2 and 3 and one f → e path of length 2.  The weighted
return operator is therefore

  H(t) = [[0, t^(-2)+t^(-3)],
          [t^(-2), 0]].

For any real t ≠ 0 and any natural delay n, we show that H(t) has
an eigenvector (e,f) with f ≠ 0 and eigenvalue t^n exactly when

  t^(2*n+5) = t+1.

In particular, for t>0 satisfying this polynomial, we exhibit a
strictly positive eigenvector. No general Perron theorem, analytic
renormalization theorem, or MLC hypothesis is imported.

The proof is pinned to Lean 4.32.0 and mathlib v4.32.0.
-/

namespace LoopsSpectral

noncomputable section

/-- The source-typed base first-return operator, with *negative*
return-length powers. Row-source matrix action is on the right. -/
def weightedReturn (t : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (((t ^ 2)⁻¹ + (t ^ 3)⁻¹) * v.2,
    (t ^ 2)⁻¹ * v.1)

/-- The eigenproblem for the weighted first-return matrix. -/
def WeightedEigen (n : ℕ) (t e f : ℝ) : Prop :=
  weightedReturn t (e, f) = (t ^ n * e, t ^ n * f)

/-- Clearing denominators in the *two specific* weighted equations
gives these two polynomial equations. -/
def ClearedEigen (n : ℕ) (t e f : ℝ) : Prop :=
  t ^ (n + 3) * e = (t + 1) * f ∧
  t ^ (n + 2) * f = e

private theorem pow_product (n : ℕ) (t : ℝ) :
    t ^ (n + 3) * t ^ (n + 2) = t ^ (2 * n + 5) := by
  rw [← pow_add]
  congr 1
  omega

private theorem pow_mul_three (n : ℕ) (t e : ℝ) :
    t ^ (n + 3) * e = (t ^ n * e) * t ^ 3 := by
  rw [pow_add]
  ring

private theorem pow_mul_two (n : ℕ) (t f : ℝ) :
    t ^ (n + 2) * f = (t ^ n * f) * t ^ 2 := by
  rw [pow_add]
  ring

private theorem inv_weight_three (t f : ℝ) (ht : t ≠ 0) :
    (((t ^ 2)⁻¹ + (t ^ 3)⁻¹) * f) * t ^ 3 = (t + 1) * f := by
  field_simp [ht]

private theorem inv_weight_two (t e : ℝ) (ht : t ≠ 0) :
    ((t ^ 2)⁻¹ * e) * t ^ 2 = e := by
  field_simp [ht]

/-- Exact equivalence between the negative-power weighted eigenproblem
and the cleared-denominator equations for t ≠ 0. -/
theorem weighted_iff_cleared (n : ℕ) (t e f : ℝ) (ht : t ≠ 0) :
    WeightedEigen n t e f ↔ ClearedEigen n t e f := by
  have hp2 := pow_mul_two n t f
  have hp3 := pow_mul_three n t e
  constructor
  · intro h
    have h1 : ((t ^ 2)⁻¹ + (t ^ 3)⁻¹) * f = t ^ n * e := by
      have hfst := congrArg Prod.fst h
      simpa [WeightedEigen, weightedReturn] using hfst
    have h2 : (t ^ 2)⁻¹ * e = t ^ n * f := by
      have hsnd := congrArg Prod.snd h
      simpa [WeightedEigen, weightedReturn] using hsnd
    change t ^ (n + 3) * e = (t + 1) * f ∧ t ^ (n + 2) * f = e
    constructor
    · calc
        t ^ (n + 3) * e = (t ^ n * e) * t ^ 3 := hp3
        _ = (((t ^ 2)⁻¹ + (t ^ 3)⁻¹) * f) * t ^ 3 := by rw [h1]
        _ = (t + 1) * f := inv_weight_three t f ht
    · calc
        t ^ (n + 2) * f = (t ^ n * f) * t ^ 2 := hp2
        _ = ((t ^ 2)⁻¹ * e) * t ^ 2 := by rw [h2]
        _ = e := inv_weight_two t e ht
  · intro h
    obtain ⟨h1, h2⟩ := h
    change weightedReturn t (e, f) = (t ^ n * e, t ^ n * f)
    apply Prod.ext
    · change ((t ^ 2)⁻¹ + (t ^ 3)⁻¹) * f = t ^ n * e
      apply (mul_right_cancel₀ (pow_ne_zero 3 ht))
      calc
        (((t ^ 2)⁻¹ + (t ^ 3)⁻¹) * f) * t ^ 3 =
            (t + 1) * f := inv_weight_three t f ht
        _ = t ^ (n + 3) * e := h1.symm
        _ = (t ^ n * e) * t ^ 3 := hp3
    · change (t ^ 2)⁻¹ * e = t ^ n * f
      apply (mul_right_cancel₀ (pow_ne_zero 2 ht))
      calc
        ((t ^ 2)⁻¹ * e) * t ^ 2 = e := inv_weight_two t e ht
        _ = t ^ (n + 2) * f := h2.symm
        _ = (t ^ n * f) * t ^ 2 := hp2

/-- Division-free elimination: the two gate equations have a solution
with nonzero f exactly when the scalar polynomial holds. -/
theorem cleared_eigen_iff_polynomial (n : ℕ) (t : ℝ) :
    (∃ e f : ℝ, f ≠ 0 ∧ ClearedEigen n t e f) ↔
      t ^ (2 * n + 5) = t + 1 := by
  constructor
  · rintro ⟨e, f, hf, h1, h2⟩
    have eq : t ^ (2 * n + 5) * f = (t + 1) * f := by
      calc
        t ^ (2 * n + 5) * f =
            (t ^ (n + 3) * t ^ (n + 2)) * f := by
              rw [pow_product n t]
        _ = t ^ (n + 3) * (t ^ (n + 2) * f) := by ring
        _ = t ^ (n + 3) * e := by rw [h2]
        _ = (t + 1) * f := h1
    exact mul_right_cancel₀ hf eq
  · intro hp
    refine ⟨t ^ (n + 2), 1, one_ne_zero, ?_, ?_⟩
    · calc
        t ^ (n + 3) * t ^ (n + 2) = t ^ (2 * n + 5) := pow_product n t
        _ = t + 1 := hp
        _ = (t + 1) * 1 := by ring
    · simp

/-- Main spectral-consistency theorem:
the **negative-weight** first-return matrix has a nonzero gate
eigenvector with eigenvalue t^n iff the exact polynomial holds. -/
theorem weighted_eigen_iff_polynomial (n : ℕ) (t : ℝ) (ht : t ≠ 0) :
    (∃ e f : ℝ, f ≠ 0 ∧ WeightedEigen n t e f) ↔
      t ^ (2 * n + 5) = t + 1 := by
  constructor
  · rintro ⟨e, f, hf, he⟩
    apply (cleared_eigen_iff_polynomial n t).mp
    exact ⟨e, f, hf, (weighted_iff_cleared n t e f ht).mp he⟩
  · intro hp
    obtain ⟨e, f, hf, he⟩ :=
      (cleared_eigen_iff_polynomial n t).mpr hp
    exact ⟨e, f, hf, (weighted_iff_cleared n t e f ht).mpr he⟩

/-- The polynomial has a *strictly positive* gate eigenvector for
any positive root: choose e=t^(n+2), f=1. -/
theorem positive_gate_eigenvector (n : ℕ) (t : ℝ)
    (ht : 0 < t) (hp : t ^ (2 * n + 5) = t + 1) :
    ∃ e f : ℝ, 0 < e ∧ 0 < f ∧ WeightedEigen n t e f := by
  have hnz : t ≠ 0 := ne_of_gt ht
  refine ⟨t ^ (n + 2), 1, pow_pos ht _, by norm_num, ?_⟩
  apply (weighted_iff_cleared n t (t ^ (n + 2)) 1 hnz).mpr
  constructor
  · calc
      t ^ (n + 3) * t ^ (n + 2) = t ^ (2 * n + 5) := pow_product n t
      _ = t + 1 := hp
      _ = (t + 1) * 1 := by ring
  · simp


/-- The alternative operator using *positive* return-length powers.
    This is the literal weighting under investigation, not a claim
    about the intended asymptotics of the source paper. -/
def printedPositiveReturn (t : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  ((t ^ 2 + t ^ 3) * v.2, t ^ 2 * v.1)

def PrintedPositiveEigen (n : ℕ) (t e f : ℝ) : Prop :=
  printedPositiveReturn t (e, f) = (t ^ n * e, t ^ n * f)

/-- A nonzero-gate eigenvector for the positive-power operator would
    force the *different* scalar equation t^(2n)=t^4(t+1). -/
theorem printed_positive_eigen_scalar (n : ℕ) (t e f : ℝ)
    (hf : f ≠ 0) (h : PrintedPositiveEigen n t e f) :
    t ^ (2 * n) = t ^ 4 * (t + 1) := by
  have h1 : (t ^ 2 + t ^ 3) * f = t ^ n * e := by
    have hfst := congrArg Prod.fst h
    simpa [PrintedPositiveEigen, printedPositiveReturn] using hfst
  have h2 : t ^ 2 * e = t ^ n * f := by
    have hsnd := congrArg Prod.snd h
    simpa [PrintedPositiveEigen, printedPositiveReturn] using hsnd
  have hp : t ^ n * t ^ n = t ^ (2 * n) := by
    rw [← pow_add]
    congr 1
    omega
  have heq : t ^ (2 * n) * f = (t ^ 4 * (t + 1)) * f := by
    calc
      t ^ (2 * n) * f = (t ^ n * t ^ n) * f := by rw [hp]
      _ = t ^ n * (t ^ n * f) := by ring
      _ = t ^ n * (t ^ 2 * e) := by rw [← h2]
      _ = t ^ 2 * (t ^ n * e) := by ring
      _ = t ^ 2 * ((t ^ 2 + t ^ 3) * f) := by rw [← h1]
      _ = (t ^ 4 * (t + 1)) * f := by ring
  exact mul_right_cancel₀ hf heq

/-- The literal positive-power scalar equation and the actual clone
    polynomial cannot both hold for a real t>1. -/
theorem printed_positive_scalar_incompatible (n : ℕ) (t : ℝ)
    (ht : 1 < t)
    (hcorrect : t ^ (2 * n + 5) = t + 1)
    (hprinted : t ^ (2 * n) = t ^ 4 * (t + 1)) : False := by
  have hp : t ^ (2 * n) * t ^ 5 = t ^ (2 * n + 5) := by
    rw [← pow_add]
  have heq : t ^ 9 * (t + 1) = t + 1 := by
    calc
      t ^ 9 * (t + 1) = (t ^ 4 * (t + 1)) * t ^ 5 := by ring
      _ = t ^ (2 * n) * t ^ 5 := by rw [hprinted]
      _ = t ^ (2 * n + 5) := hp
      _ = t + 1 := hcorrect
  have hnonzero : t + 1 ≠ 0 := by linarith
  have hmul : t ^ 9 * (t + 1) = (1 : ℝ) * (t + 1) := by
    simpa only [one_mul] using heq
  have hnine : t ^ 9 = 1 := mul_right_cancel₀ hnonzero hmul
  have hgt : 1 < t ^ 9 := one_lt_pow₀ ht (by norm_num)
  linarith

/-- Formal countercheck for the printed positive-power definition:
    at any t>1 satisfying the actual finite-clone equation, it has
    *no* eigenvector with eigenvalue t^n and nonzero second coordinate. -/
theorem no_printed_positive_eigen_at_clone_root (n : ℕ) (t : ℝ)
    (ht : 1 < t)
    (hcorrect : t ^ (2 * n + 5) = t + 1) :
    ¬ ∃ e f : ℝ, f ≠ 0 ∧ PrintedPositiveEigen n t e f := by
  rintro ⟨e, f, hf, he⟩
  exact printed_positive_scalar_incompatible n t ht hcorrect
    (printed_positive_eigen_scalar n t e f hf he)


end

end LoopsSpectral
