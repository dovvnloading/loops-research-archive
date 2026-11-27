import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Distinguishable small signed critical excursions

The positive excursions point along distinct rays with a common positive
real coordinate at their markers. Each marker belongs to just its own
positive excursion and to none of the negative excursions. This concerns
the image sets themselves, independently of path parametrization.
-/

namespace LoopsCriticalRayGeometry

open Set

noncomputable section

/-- A small marker with positive real part and index-dependent slope. -/
def marker (r : ℝ) {n : ℕ} (i : Fin n) : ℂ :=
  ((r / ((n : ℝ) + 1) : ℝ) : ℂ) * (1 + (i.val : ℂ) * Complex.I)

/-- One out-and-back excursion from the origin to its marker. -/
def excursion (r : ℝ) {n : ℕ} (i : Fin n) (t : unitInterval) : ℂ :=
  ((4 * (t : ℝ) * (1 - (t : ℝ)) : ℝ) : ℂ) * marker r i

/-- The common midpoint used by every excursion. -/
def midpoint : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

theorem marker_re (r : ℝ) {n : ℕ} (i : Fin n) :
    (marker r i).re = r / ((n : ℝ) + 1) := by
  unfold marker
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  simp

theorem marker_im (r : ℝ) {n : ℕ} (i : Fin n) :
    (marker r i).im = r / ((n : ℝ) + 1) * (i.val : ℝ) := by
  unfold marker
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  simp

theorem marker_ne_zero {r : ℝ} (hr : 0 < r) {n : ℕ} (i : Fin n) :
    marker r i ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  rw [marker_re] at hh
  have hp : 0 < r / ((n : ℝ) + 1) := by positivity
  simpa using (ne_of_gt hp) hh

theorem excursion_continuous (r : ℝ) {n : ℕ} (i : Fin n) :
    Continuous (excursion r i) := by
  unfold excursion
  fun_prop

@[simp] theorem excursion_zero (r : ℝ) {n : ℕ} (i : Fin n) :
    excursion r i 0 = 0 := by
  simp [excursion]

@[simp] theorem excursion_one (r : ℝ) {n : ℕ} (i : Fin n) :
    excursion r i 1 = 0 := by
  simp [excursion]

@[simp] theorem excursion_midpoint (r : ℝ) {n : ℕ} (i : Fin n) :
    excursion r i midpoint = marker r i := by
  norm_num [excursion, midpoint]

theorem excursion_eq_zero_iff {r : ℝ} (hr : 0 < r) {n : ℕ}
    (i : Fin n) (t : unitInterval) :
    excursion r i t = 0 ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    have hb : (4 * (t : ℝ) * (1 - (t : ℝ))) = 0 := by
      exact_mod_cast (mul_eq_zero.mp h).resolve_right (marker_ne_zero hr i)
    rcases mul_eq_zero.mp hb with ht | ht
    · have hz : (t : ℝ) = 0 := (mul_eq_zero.mp ht).resolve_left (by norm_num)
      exact Or.inl (Subtype.ext hz)
    · exact Or.inr (Subtype.ext (sub_eq_zero.mp ht).symm)
  · rintro (rfl | rfl) <;> simp

private theorem bump_nonneg (t : unitInterval) :
    0 ≤ 4 * (t : ℝ) * (1 - (t : ℝ)) := by
  have ht0 := t.property.1
  have ht1 := t.property.2
  positivity

private theorem bump_le_one (t : unitInterval) :
    4 * (t : ℝ) * (1 - (t : ℝ)) ≤ 1 := by
  nlinarith [sq_nonneg (2 * (t : ℝ) - 1)]

theorem marker_norm_le {r : ℝ} (hr : 0 < r) {n : ℕ} (i : Fin n) :
    ‖marker r i‖ ≤ r := by
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have ha : 0 ≤ r / ((n : ℝ) + 1) := by positivity
  have hi : 0 ≤ (i.val : ℝ) := by positivity
  have hin : (i.val : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.le_of_lt i.isLt)
  calc
    ‖marker r i‖ ≤ |(marker r i).re| + |(marker r i).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = r / ((n : ℝ) + 1) * (1 + (i.val : ℝ)) := by
      rw [marker_re, marker_im, abs_of_nonneg ha, abs_of_nonneg (mul_nonneg ha hi)]
      ring
    _ ≤ r / ((n : ℝ) + 1) * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) ha
    _ = r := div_mul_cancel₀ r (ne_of_gt hden)

theorem excursion_norm_le {r : ℝ} (hr : 0 < r) {n : ℕ}
    (i : Fin n) (t : unitInterval) : ‖excursion r i t‖ ≤ r := by
  have hnonneg := bump_nonneg t
  calc
    ‖excursion r i t‖ = (4 * (t : ℝ) * (1 - (t : ℝ))) * ‖marker r i‖ := by
      rw [excursion, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ ≤ 1 * ‖marker r i‖ := mul_le_mul_of_nonneg_right (bump_le_one t) (norm_nonneg _)
    _ ≤ r := by simpa using marker_norm_le hr i

theorem neg_excursion_norm_le {r : ℝ} (hr : 0 < r) {n : ℕ}
    (i : Fin n) (t : unitInterval) : ‖-(excursion r i t)‖ ≤ r := by
  simpa only [norm_neg] using excursion_norm_le hr i t

/-- A positive marker occurs in a positive excursion precisely at the
matching index. The statement is about ranges, hence unparametrized traces. -/
theorem marker_mem_excursion_range_iff {r : ℝ} (hr : 0 < r)
    {n : ℕ} (i j : Fin n) :
    marker r j ∈ range (excursion r i) ↔ i = j := by
  constructor
  · rintro ⟨t, ht⟩
    have ha : r / ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
    have hre := congrArg Complex.re ht
    have him := congrArg Complex.im ht
    simp only [excursion, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, marker_re] at hre
    have hb : 4 * (t : ℝ) * (1 - (t : ℝ)) = 1 := by
      apply mul_right_cancel₀ ha
      simpa only [one_mul] using hre
    simp only [excursion, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, marker_im] at him
    rw [hb, one_mul] at him
    have hij : (i.val : ℝ) = (j.val : ℝ) := mul_left_cancel₀ ha him
    apply Fin.ext
    exact_mod_cast hij
  · rintro rfl
    exact ⟨midpoint, excursion_midpoint r i⟩

/-- No positive marker lies in any negative excursion. -/
theorem marker_not_mem_neg_excursion_range {r : ℝ} (hr : 0 < r)
    {n : ℕ} (i j : Fin n) :
    marker r j ∉ range (fun t => -(excursion r i t)) := by
  rintro ⟨t, ht⟩
  have hre := congrArg Complex.re ht
  simp only [Complex.neg_re, excursion, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, marker_re] at hre
  have ha : 0 < r / ((n : ℝ) + 1) := by positivity
  have hn := mul_nonneg (bump_nonneg t) ha.le
  linarith

end

end LoopsCriticalRayGeometry
