import ActualPairableSource
import Mathlib.Analysis.Convex.PathConnected

/-! # Connectivity of the actual archived upper sheet -/

namespace ActualPairableSource

open Set Function Metric
open NearTwoTip LimitingCrestQuadraticReturn

noncomputable section

theorem slitTarget_isPathConnected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsPathConnected (slitTarget c p) := by
  let u : ℝ := (criticalValue c p+radius p)/2
  have hdu : criticalValue c p < u := by dsimp [u]; linarith [criticalValue_lt_radius hp hc]
  have huR : u < radius p := by dsimp [u]; linarith [criticalValue_lt_radius hp hc]
  have hu0 : 0 < u := lt_trans hc.2.1 hdu
  have huBall : (u : ℂ) ∈ ball 0 (radius p) := by
    simpa only [mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu0] using huR
  have hstar : StarConvex ℝ (u : ℂ) (slitTarget c p) := by
    intro z hz a b ha hb hab
    refine ⟨(convex_ball (0 : ℂ) (radius p)) huBall hz.1 ha hb hab,?_⟩
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simp only [hb0,ha1,one_smul,zero_smul,add_zero]
      exact Or.inl hdu
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    rcases hz.2 with hzre | hzim
    · apply Or.inl
      simp only [Complex.add_re,Complex.smul_re,Complex.ofReal_re,smul_eq_mul]
      have h1 := mul_nonneg ha (le_of_lt (sub_pos.mpr hdu))
      have h2 := mul_pos hbpos (sub_pos.mpr hzre)
      nlinarith
    · apply Or.inr
      simpa only [Complex.add_im,Complex.smul_im,Complex.ofReal_im,smul_eq_mul,mul_zero,zero_add]
        using mul_ne_zero hb0 hzim
  exact hstar.isPathConnected ⟨huBall,Or.inl hdu⟩

theorem upperSource_isPathConnected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsPathConnected (upperSource c p) := by
  have ht : IsPathConnected (conformalChart hp hc).homeomorph.target := by
    rw [conformalChart_target]
    exact slitTarget_isPathConnected hp hc
  have hi := ht.image' (conformalChart hp hc).homeomorph.symm.continuousOn
  simpa only [OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.symm_image_target_eq_source,conformalChart_source] using hi

theorem upperSource_isConnected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsConnected (upperSource c p) :=
  (upperSource_isPathConnected hp hc).isConnected

end
end ActualPairableSource
