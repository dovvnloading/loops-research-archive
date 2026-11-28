import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic

/-!
# Rectangular exhaustion of the upper half-plane

These measure-theoretic lemmas convert finite rectangular Green identities
to an integral on the full upper half-plane.
-/

namespace SlitEnergyExhaustion

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

def radius (n : ℕ) : ℝ := (n : ℝ) + 1

def box (n : ℕ) : Set (ℝ × ℝ) :=
  Icc (-radius n) (radius n) ×ˢ Icc (radius n)⁻¹ (radius n)

theorem radius_pos (n : ℕ) : 0 < radius n := by
  unfold radius
  positivity

theorem one_le_radius (n : ℕ) : 1 ≤ radius n := by
  unfold radius
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

theorem radius_tendsto_atTop : Tendsto radius atTop atTop := by
  exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

theorem inv_radius_tendsto_zero :
    Tendsto (fun n : ℕ => (radius n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp radius_tendsto_atTop

theorem radius_mono : Monotone radius := by
  intro n m hnm
  unfold radius
  have h : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  linarith

theorem box_measurable (n : ℕ) : MeasurableSet (box n) :=
  measurableSet_Icc.prod measurableSet_Icc

theorem box_mono : Monotone box := by
  intro n m hnm p hp
  have hr := radius_mono hnm
  exact ⟨⟨(neg_le_neg hr).trans hp.1.1, hp.1.2.trans hr⟩,
    ⟨(inv_anti₀ (radius_pos n) hr).trans hp.2.1, hp.2.2.trans hr⟩⟩

theorem iUnion_box : (⋃ n : ℕ, box n) = {p : ℝ × ℝ | 0 < p.2} := by
  ext p
  constructor
  · intro hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp hp
    exact (inv_pos.mpr (radius_pos n)).trans_le hn.2.1
  · intro hp
    obtain ⟨n, hn⟩ := (radius_tendsto_atTop.eventually_ge_atTop
      (max |p.1| (max p.2 p.2⁻¹))).exists
    have hx : |p.1| ≤ radius n := (le_max_left _ _).trans hn
    have hy : p.2 ≤ radius n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
    have hiy : p.2⁻¹ ≤ radius n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
    exact mem_iUnion.mpr ⟨n, ⟨abs_le.mp hx,
      ⟨(inv_le_comm₀ (radius_pos n) hp).mpr hiy, hy⟩⟩⟩

theorem tendsto_integral_box {E : ℝ × ℝ → ℝ} (hE : Integrable E) :
    Tendsto (fun n : ℕ => ∫ p in box n, E p) atTop
      (𝓝 (∫ p in {p : ℝ × ℝ | 0 < p.2}, E p)) := by
  simpa only [iUnion_box] using
    tendsto_setIntegral_of_monotone box_measurable box_mono hE.integrableOn

theorem intervalIntegral_eq_integral_box {E : ℝ × ℝ → ℝ}
    (hE : Integrable E) (n : ℕ) :
    (∫ x in -radius n..radius n, ∫ y in (radius n)⁻¹..radius n, E (x, y)) =
      ∫ p in box n, E p := by
  have hr := radius_pos n
  have h1 := one_le_radius n
  have hi : (radius n)⁻¹ ≤ radius n :=
    (inv_le_one₀ hr).mpr h1 |>.trans h1
  have hneg : -radius n ≤ radius n := by linarith
  simp_rw [intervalIntegral.integral_of_le hneg,
    intervalIntegral.integral_of_le hi]
  rw [box, Measure.volume_eq_prod,
    setIntegral_prod E (by simpa only [← Measure.volume_eq_prod] using hE.integrableOn)]
  simp_rw [integral_Icc_eq_integral_Ioc]

theorem integrable_complex_pullback {f : ℂ → ℝ} (hf : Integrable f) :
    Integrable (fun p : ℝ × ℝ => f ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
  simpa only [Function.comp_def, Complex.measurableEquivRealProd_symm_apply,
    Complex.mk_eq_add_mul_I] using
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hf

theorem integral_upperHalfPlane_complex_pullback (f : ℂ → ℝ) :
    (∫ p in {p : ℝ × ℝ | 0 < p.2}, f ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) =
      ∫ z in {z : ℂ | 0 < z.im}, f z := by
  simpa only [Complex.measurableEquivRealProd_symm_apply, preimage_setOf_eq,
    Complex.mk_eq_add_mul_I, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add,
    add_zero] using
    Complex.volume_preserving_equiv_real_prod.symm.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding f {z : ℂ | 0 < z.im}

end
end SlitEnergyExhaustion
