import TwoLevelOuterChart

/-!
# Literal coordinates for two successive returns

The second critical scale is allowed to be negative in the original
quadratic coordinate.  All identities retain that sign; radii use its
absolute value.  These are coordinate identities for the actual polynomial.
-/

namespace TwoLevelConjugacy

open Set Function
open LimitingCrestQuadraticReturn TwoLevelOuterChart

noncomputable section

theorem iterate_real (c x : ℝ) (n : ℕ) :
    ((quadraticMap c)^[n]) (x : ℂ) =
      (((fun t : ℝ => t^2+c)^[n]) x : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih]
    simp only [quadraticMap, Complex.ofReal_add, Complex.ofReal_pow]

theorem iterate_zero (c : ℝ) (n : ℕ) :
    ((quadraticMap c)^[n]) (0 : ℂ) = (criticalValue c n : ℂ) :=
  iterate_real c 0 n

theorem outerMap_continuous (c : ℝ) (p : ℕ) :
    Continuous (outerMap c p) := by
  have hf : Continuous (quadraticMap c) := by unfold quadraticMap; fun_prop
  exact continuous_const.mul ((hf.iterate p).comp (continuous_id.div_const _))

theorem outerMap_real (c x : ℝ) (p : ℕ) :
    (outerMap c p (x : ℂ)).im = 0 := by
  unfold outerMap
  rw [← Complex.ofReal_div, iterate_real]
  simp

theorem outerMap_iterate_scale (c : ℝ) (p : ℕ)
    (hA : returnCoefficient p c ≠ 0) (m : ℕ) (z : ℂ) :
    ((outerMap c p)^[m]) z =
      (returnCoefficient p c : ℂ) *
        ((quadraticMap c)^[m*p]) (z/(returnCoefficient p c : ℂ)) := by
  have hAC : (returnCoefficient p c : ℂ) ≠ 0 := by exact_mod_cast hA
  induction m with
  | zero => simp [hAC]
  | succ m ih =>
    rw [iterate_succ_apply', ih]
    unfold outerMap
    rw [mul_div_cancel_left₀ _ hAC,
      show (m+1)*p = p+m*p by ring, iterate_add_apply]

theorem outerMap_iterate_zero (c : ℝ) (p q : ℕ)
    (hA : returnCoefficient p c ≠ 0) :
    ((outerMap c p)^[q]) 0 =
      ((returnCoefficient p c * criticalValue c (q*p) : ℝ) : ℂ) := by
  rw [outerMap_iterate_scale c p hA, zero_div, iterate_zero]
  push_cast
  rfl

def secondScale (c : ℝ) (p q : ℕ) : ℝ :=
  returnCoefficient p c * criticalValue c (q*p)

theorem secondScale_eq_re (c : ℝ) (p q : ℕ)
    (hA : returnCoefficient p c ≠ 0) :
    secondScale c p q = (((outerMap c p)^[q]) 0).re := by
  rw [outerMap_iterate_zero c p q hA]
  rfl

theorem secondScale_positive_iff (c : ℝ) (p q : ℕ)
    (hA : returnCoefficient p c < 0) :
    0 < secondScale c p q ↔ criticalValue c (q*p) < 0 := by
  unfold secondScale
  constructor
  · intro h
    rcases mul_pos_iff.mp h with hp | hn
    · linarith [hp.1]
    · exact hn.2
  · exact fun h => mul_pos_of_neg_of_neg hA h

theorem second_normalization_eq (c : ℝ) (p q : ℕ)
    (hA : returnCoefficient p c ≠ 0)
    (hD : secondScale c p q ≠ 0) (z : ℂ) :
    ((outerMap c p)^[q]) ((secondScale c p q : ℂ)*z) /
        (secondScale c p q : ℂ) = normalizedReturn c (q*p) z := by
  have hd : criticalValue c (q*p) ≠ 0 := by
    intro hz
    apply hD
    simp [secondScale, hz]
  have hAC : (returnCoefficient p c : ℂ) ≠ 0 := by exact_mod_cast hA
  have hdC : (criticalValue c (q*p) : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [outerMap_iterate_scale c p hA]
  have hin : (secondScale c p q : ℂ)*z/(returnCoefficient p c : ℂ) =
      (criticalValue c (q*p) : ℂ)*z := by
    unfold secondScale
    push_cast
    field_simp
  rw [hin]
  unfold normalizedReturn secondScale
  push_cast
  field_simp

theorem signed_relation_scale (c : ℝ) (p q : ℕ)
    (hA : returnCoefficient p c ≠ 0) :
    (((outerMap c p)^[6*q]) 0).re + (((outerMap c p)^[3*q]) 0).re =
      returnCoefficient p c *
        (criticalValue c (6*(q*p))+criticalValue c (3*(q*p))) := by
  rw [outerMap_iterate_zero c p (6*q) hA,
    outerMap_iterate_zero c p (3*q) hA]
  simp only [Complex.ofReal_re]
  rw [Nat.mul_assoc, Nat.mul_assoc]
  ring

theorem normalizedReturn_continuous (c : ℝ) (n : ℕ) :
    Continuous (normalizedReturn c n) := by
  have hf : Continuous (quadraticMap c) := by unfold quadraticMap; fun_prop
  exact ((hf.iterate n).comp (continuous_const.mul continuous_id)).div_const _

theorem normalizedReturn_real (c x : ℝ) (n : ℕ) :
    (normalizedReturn c n (x : ℂ)).im = 0 := by
  unfold normalizedReturn
  rw [← Complex.ofReal_mul, iterate_real]
  simp

theorem normalizedReturn_imaginary (c x : ℝ) (n : ℕ) (hn : 0 < n) :
    (normalizedReturn c n ((x : ℂ)*Complex.I)).im = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let d := criticalValue c (m+1)
  have hfirst : quadraticMap c ((d : ℂ)*((x : ℂ)*Complex.I)) =
      ((c-(d*x)^2 : ℝ) : ℂ) := by
    simp [quadraticMap, mul_pow, Complex.I_sq] <;> ring
  unfold normalizedReturn
  change (((quadraticMap c)^[m+1]) ((d : ℂ)*((x : ℂ)*Complex.I)) /
    (d : ℂ)).im = 0
  rw [iterate_succ_apply, hfirst, iterate_real]
  simp

end
end TwoLevelConjugacy
