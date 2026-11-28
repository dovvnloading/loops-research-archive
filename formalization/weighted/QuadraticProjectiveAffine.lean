import QuadraticProjectiveAlgebra

/-!
# Affine comparison for the critical-orbit projective jet

The four-point observable has an exact formula on an affine orbit.  This
classical comparison supplies the reference term for the nonlinear
quadratic-family obstruction; it is not a novelty claim on its own.
-/

noncomputable section

namespace LoopsQuadraticProjective

/-- An affine map written using its fixed point and multiplier. -/
def affineMap (p q z : ℂ) : ℂ := p + q * (z - p)

/-- A general orbit of the affine map with fixed point `p` and multiplier `q`. -/
def affineMark (p u q : ℂ) (n : ℕ) : ℂ := p + u * q ^ n

theorem affineMark_succ (p u q : ℂ) (n : ℕ) :
    affineMark p u q (n + 1) = affineMap p q (affineMark p u q n) := by
  simp only [affineMark, affineMap, pow_succ]
  ring

/-- Four consecutive geometric marks have no nonlinear finite curvature term. -/
theorem crossRatio_affine_geometric (p u t : ℂ)
    (hu : u ≠ 0) (ht : t ≠ 0) (ht₁ : t ≠ 1) :
    crossRatio (p + u) (p + u * t) (p + u * t ^ 2) (p + u * t ^ 3) =
      -t⁻¹ - 1 - t := by
  have hd₁ : p + u * t - (p + u) = u * (t - 1) := by ring
  have hd₂ : p + u * t ^ 3 - (p + u * t ^ 2) = u * t ^ 2 * (t - 1) := by ring
  unfold crossRatio
  rw [hd₁, hd₂]
  field_simp [hu, ht, sub_ne_zero.mpr ht₁]
  ring

/-- Exact all-clock formula for a nondegenerate affine orbit. -/
theorem crossRatio_affine_clock (p u q : ℂ) (k : ℕ)
    (hu : u ≠ 0) (hq : q ≠ 0) (hk : q ^ k ≠ 1) :
    crossRatio (affineMark p u q 0) (affineMark p u q k)
      (affineMark p u q (2 * k)) (affineMark p u q (3 * k)) =
      -(q ^ k)⁻¹ - 1 - q ^ k := by
  have h₂ : q ^ (2 * k) = (q ^ k) ^ 2 := by rw [Nat.mul_comm, pow_mul]
  have h₃ : q ^ (3 * k) = (q ^ k) ^ 3 := by rw [Nat.mul_comm, pow_mul]
  simpa only [affineMark, pow_zero, mul_one, h₂, h₃] using
    crossRatio_affine_geometric p u (q ^ k) hu (pow_ne_zero _ hq) hk

/-- A fractional linear map, restricted to points where its denominator is nonzero. -/
def fractionalMap (A B C D z : ℂ) : ℂ := (A * z + B) / (C * z + D)

theorem fractionalMap_sub (A B C D x y : ℂ)
    (hx : C * x + D ≠ 0) (hy : C * y + D ≠ 0) :
    fractionalMap A B C D x - fractionalMap A B C D y =
      (A * D - B * C) * (x - y) / ((C * x + D) * (C * y + D)) := by
  unfold fractionalMap
  rw [div_sub_div _ _ hx hy]
  congr 1
  ring

/-- Projective changes preserve the ordered four-point observable. -/
theorem crossRatio_fractionalMap (A B C D x₀ x₁ x₂ x₃ : ℂ)
    (hdet : A * D - B * C ≠ 0)
    (h₀ : C * x₀ + D ≠ 0) (h₁ : C * x₁ + D ≠ 0)
    (h₂ : C * x₂ + D ≠ 0) (h₃ : C * x₃ + D ≠ 0)
    (h₁₀ : x₁ ≠ x₀) (h₃₂ : x₃ ≠ x₂) :
    crossRatio (fractionalMap A B C D x₀) (fractionalMap A B C D x₁)
      (fractionalMap A B C D x₂) (fractionalMap A B C D x₃) =
      crossRatio x₀ x₁ x₂ x₃ := by
  unfold crossRatio
  rw [fractionalMap_sub A B C D x₃ x₀ h₃ h₀,
    fractionalMap_sub A B C D x₁ x₂ h₁ h₂,
    fractionalMap_sub A B C D x₁ x₀ h₁ h₀,
    fractionalMap_sub A B C D x₃ x₂ h₃ h₂]
  field_simp [hdet, h₀, h₁, h₂, h₃, sub_ne_zero.mpr h₁₀, sub_ne_zero.mpr h₃₂]

theorem affine_clock_pair_ne (p u q : ℂ) (k : ℕ)
    (hu : u ≠ 0) (hq : q ≠ 0) (hk : q ^ k ≠ 1) :
    affineMark p u q k ≠ affineMark p u q 0 ∧
      affineMark p u q (3 * k) ≠ affineMark p u q (2 * k) := by
  have ht : q ^ k ≠ 0 := pow_ne_zero _ hq
  have h₂ : q ^ (2 * k) = (q ^ k) ^ 2 := by rw [Nat.mul_comm, pow_mul]
  have h₃ : q ^ (3 * k) = (q ^ k) ^ 3 := by rw [Nat.mul_comm, pow_mul]
  simp only [affineMark, pow_zero, mul_one, h₂, h₃]
  constructor
  · intro h
    apply (mul_ne_zero hu (sub_ne_zero.mpr hk))
    linear_combination h
  · intro h
    apply (mul_ne_zero (mul_ne_zero hu (pow_ne_zero 2 ht)) (sub_ne_zero.mpr hk))
    linear_combination h

/-- The multiplier formula persists after any nondegenerate projective change. -/
theorem crossRatio_fractional_affine_clock (A B C D p u q : ℂ) (k : ℕ)
    (hdet : A * D - B * C ≠ 0)
    (hu : u ≠ 0) (hq : q ≠ 0) (hk : q ^ k ≠ 1)
    (h₀ : C * affineMark p u q 0 + D ≠ 0)
    (h₁ : C * affineMark p u q k + D ≠ 0)
    (h₂ : C * affineMark p u q (2 * k) + D ≠ 0)
    (h₃ : C * affineMark p u q (3 * k) + D ≠ 0) :
    crossRatio (fractionalMap A B C D (affineMark p u q 0))
      (fractionalMap A B C D (affineMark p u q k))
      (fractionalMap A B C D (affineMark p u q (2 * k)))
      (fractionalMap A B C D (affineMark p u q (3 * k))) =
      -(q ^ k)⁻¹ - 1 - q ^ k := by
  obtain ⟨h₁₀, h₃₂⟩ := affine_clock_pair_ne p u q k hu hq hk
  rw [crossRatio_fractionalMap A B C D _ _ _ _ hdet h₀ h₁ h₂ h₃ h₁₀ h₃₂]
  exact crossRatio_affine_clock p u q k hu hq hk

end LoopsQuadraticProjective
