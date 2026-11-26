import ParabolicComplexPullback
import ParabolicSegment
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Exact physical fibers at the quadratic Chebyshev parameter

The map is the archive's actual complex quadratic at c = -2.
The Joukowski map is not a freely chosen finite symbolic projection.
Classical identities are used to expose a genuine obstruction to a
single-valued future-compatible boundary address.
-/
namespace LoopsChebyshev
open Function Set
open scoped ComplexConjugate
open LoopsParabolic

noncomputable section

def J (w : ℂ) : ℂ := w + w⁻¹

def BoundedOrbit (z : ℂ) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, ‖(cquad (-2))^[n] z‖ ≤ B

def UnitAddress (w : ℂ) : Prop := ‖w‖ = 1

theorem pair_step {w v : ℂ} (h : w * v = 1) :
    cquad (-2) (w + v) = w^2 + v^2 := by
  norm_num [cquad]
  linear_combination 2 * h

theorem pair_iterate {w v : ℂ} (h : w * v = 1) (n : ℕ) :
    (cquad (-2))^[n] (w + v) = w^(2^n) + v^(2^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    have hp : w^(2^n) * v^(2^n) = 1 := by rw [← mul_pow, h, one_pow]
    rw [pair_step hp]
    simp only [pow_succ (2 : ℕ) n, pow_mul]

theorem joukowski_step {w : ℂ} (hw : w ≠ 0) :
    cquad (-2) (J w) = J (w^2) := by
  unfold J
  rw [pair_step (mul_inv_cancel₀ hw), inv_pow]

theorem joukowski_iterate {w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    (cquad (-2))^[n] (J w) = J (w^(2^n)) := by
  unfold J
  rw [pair_iterate (mul_inv_cancel₀ hw), inv_pow]

/-- All complex points, not just points in a selected symbolic carrier. -/
theorem reciprocal_pair_exists (z : ℂ) :
    ∃ w v : ℂ, w*v = 1 ∧ w+v = z := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (z^2-4) (n := 2) (by decide)
  refine ⟨(z+s)/2, (z-s)/2, ?_, by ring⟩
  linear_combination -(1/4 : ℂ) * hs

theorem reciprocal_eq_inv {w v : ℂ} (h : w*v = 1) : v = w⁻¹ := by
  have hw : w ≠ 0 := by intro hz; simp [hz] at h
  apply mul_left_cancel₀ hw
  rw [h, mul_inv_cancel₀ hw]

theorem joukowski_surjective : Surjective J := by
  intro z
  obtain ⟨w,v,h,hz⟩ := reciprocal_pair_exists z
  have hw : w ≠ 0 := by intro he; simp [he] at h
  exact ⟨w, by simpa only [J, ← reciprocal_eq_inv h] using hz⟩

/-- The only ambiguity for nonzero addresses is inversion. -/
theorem joukowski_fiber {w v : ℂ} (hw : w ≠ 0) (hv : v ≠ 0) :
    J w = J v ↔ w = v ∨ w = v⁻¹ := by
  constructor
  · intro he
    have hf : (w-v)*(w*v-1) = 0 := by
      calc
        (w-v)*(w*v-1) = w*v*(J w-J v) := by
          unfold J
          field_simp [hw,hv] <;> ring
        _ = 0 := by rw [he, sub_self, mul_zero]
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (reciprocal_eq_inv (by simpa [mul_comm] using sub_eq_zero.mp h))
  · rintro (rfl | rfl)
    · rfl
    · simp [J, add_comm]

theorem unit_nonzero {w : ℂ} (h : UnitAddress w) : w ≠ 0 := by
  intro he
  simp [UnitAddress, he] at h

theorem unit_inv {w : ℂ} (h : UnitAddress w) : UnitAddress w⁻¹ := by
  simp [UnitAddress, norm_inv, h]

theorem unit_square {w : ℂ} (h : UnitAddress w) : UnitAddress (w^2) := by
  simp [UnitAddress, norm_pow, h]

private theorem pair_norm_product {w v : ℂ} (h : w*v = 1) :
    ‖w‖ * ‖v‖ = 1 := by
  simpa only [norm_mul, norm_one] using congrArg (fun z : ℂ => ‖z‖) h

private theorem growth (r : ℝ) (hr : 1 < r) (n : ℕ) :
    r ≤ r^(2^n) ∧ 1+(n:ℝ)*(r-1) ≤ r^(2^n) := by
  induction n with
  | zero => simp; linarith
  | succ n ih =>
    rw [pow_succ (2 : ℕ) n, pow_mul]
    push_cast
    constructor <;> nlinarith [sq_nonneg (r^(2^n)-1)]

/-- Every non-unit reciprocal lift on the exterior side escapes, with
a lower bound valid at every iterate (not just a sampled orbit). -/
theorem exterior_lower_bound {w v : ℂ} (h : w*v=1) (hw : 1 < ‖w‖) (n : ℕ) :
    ‖w‖^(2^n) - 1 ≤ ‖(cquad (-2))^[n] (w+v)‖ := by
  have hp := pair_norm_product h
  have hv : ‖v‖ ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ ‖w‖-1 by linarith) (norm_nonneg v)]
  have hpow : ‖v‖^(2^n) ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg v) hv (2^n)
  have ht := norm_sub_le (w^(2^n)+v^(2^n)) (v^(2^n))
  rw [add_sub_cancel_right, norm_pow, norm_pow] at ht
  rw [pair_iterate h]
  linarith

theorem exterior_unbounded {w v : ℂ} (h : w*v=1) (hw : 1 < ‖w‖) :
    ¬ BoundedOrbit (w+v) := by
  rintro ⟨B,hB⟩
  obtain ⟨n,hn⟩ := exists_nat_gt (B / (‖w‖-1))
  have hmul := (div_lt_iff₀ (sub_pos.mpr hw)).mp hn
  have hg := (growth ‖w‖ hw n).2
  have hl := exterior_lower_bound h hw n
  linarith [hB n]

theorem unit_bounded {w : ℂ} (hw : UnitAddress w) :
    ∀ n : ℕ, ‖(cquad (-2))^[n] (J w)‖ ≤ 2 := by
  intro n
  rw [joukowski_iterate (unit_nonzero hw)]
  have hp : ‖w^(2^n)‖ = 1 := by simp [norm_pow, hw]
  calc
    ‖J (w^(2^n))‖ ≤ ‖w^(2^n)‖ + ‖(w^(2^n))⁻¹‖ := norm_add_le _ _
    _ = 2 := by rw [norm_inv, hp]; norm_num

/-- An exact equivalence, with neither connectedness nor a priori bounds assumed. -/
theorem bounded_iff_unit_image (z : ℂ) :
    BoundedOrbit z ↔ ∃ w : ℂ, UnitAddress w ∧ J w = z := by
  constructor
  · intro hb
    obtain ⟨w,v,h,hz⟩ := reciprocal_pair_exists z
    have hp := pair_norm_product h
    have hw : ‖w‖ ≤ 1 := by
      by_contra! hgt
      exact exterior_unbounded h hgt (hz.symm ▸ hb)
    have hv : ‖v‖ ≤ 1 := by
      by_contra! hgt
      have h' : v*w=1 := by simpa [mul_comm] using h
      exact exterior_unbounded h' hgt ((add_comm v w ▸ hz).symm ▸ hb)
    have he : ‖w‖ = 1 := by
      have hm := mul_le_mul_of_nonneg_left hv (norm_nonneg w)
      linarith
    exact ⟨w,he,by simpa only [J, ← reciprocal_eq_inv h] using hz⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨2, unit_bounded hw⟩

theorem unit_inv_eq_conj {w : ℂ} (hw : UnitAddress w) : w⁻¹ = conj w := by
  have h : w * conj w = 1 := by
    rw [Complex.mul_conj', hw]
    norm_num
  exact (reciprocal_eq_inv h).symm

theorem unit_image_realSegment {w : ℂ} (hw : UnitAddress w) :
    J w ∈ realSegment 2 := by
  rw [J, unit_inv_eq_conj hw, Complex.add_conj]
  refine ⟨2*w.re, ?_, rfl⟩
  have h := Complex.abs_re_le_norm w
  rw [hw, abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem realSegment_invariant {z : ℂ} (hz : z ∈ realSegment 2) :
    cquad (-2) z ∈ realSegment 2 := by
  obtain ⟨x,hx,rfl⟩ := hz
  refine ⟨x^2-2, ?_, ?_⟩
  · exact ⟨by nlinarith [sq_nonneg x], by nlinarith [sq_le_sq' hx.1 hx.2]⟩
  · norm_num [cquad]

/-- The filled bounded-orbit set of the actual polynomial is exactly [-2,2]. -/
theorem bounded_iff_realSegment (z : ℂ) :
    BoundedOrbit z ↔ z ∈ realSegment 2 := by
  constructor
  · intro hb
    obtain ⟨w,hw,rfl⟩ := (bounded_iff_unit_image z).mp hb
    exact unit_image_realSegment hw
  · intro hz
    have hm : ∀ n : ℕ, (cquad (-2))^[n] z ∈ realSegment 2 := by
      intro n
      induction n with
      | zero => exact hz
      | succ n ih => rw [iterate_succ_apply']; exact realSegment_invariant ih
    refine ⟨2, fun n => ?_⟩
    obtain ⟨x,hx,he⟩ := hm n
    rw [← he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact hx

/-- A fixed planar point may have no fixed boundary address.
Consequently no single-valued equivariant section exists, even without
continuity or any regularity assumption. -/
theorem no_equivariant_unit_section :
    ¬ ∃ s : ℂ → ℂ,
      (∀ z ∈ realSegment 2, UnitAddress (s z) ∧ J (s z) = z) ∧
      (∀ z ∈ realSegment 2, s (cquad (-2) z) = (s z)^2) := by
  rintro ⟨s,hsec,heq⟩
  have hm : (-1 : ℂ) ∈ realSegment 2 := by
    exact ⟨-1, ⟨by norm_num, by norm_num⟩, by norm_num⟩
  have hf : cquad (-2) (-1) = -1 := by norm_num [cquad]
  have h := heq (-1) hm
  rw [hf] at h
  obtain ⟨hu,hj⟩ := hsec (-1) hm
  have hfactor : s (-1) * (s (-1)-1) = 0 := by linear_combination -h
  have hone : s (-1) = 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (unit_nonzero hu))
  rw [hone] at hj
  norm_num [J] at hj

end
end LoopsChebyshev
