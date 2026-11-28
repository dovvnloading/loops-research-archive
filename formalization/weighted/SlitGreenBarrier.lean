import SlitJoukowski

/-!
# A maximum-modulus barrier with continuous boundary modulus

The exterior coordinate can have different phases on the two banks of
the slit. Only its modulus is extended to the slit. The first theorem
proves exactly the maximum principle needed for that situation.
-/

namespace SlitGreenBarrier

open Set Function Filter Topology Metric Bornology
open LoopsParabolic SlitJoukowski

noncomputable section

theorem norm_boundary_bound (D : Set ℂ) (hD : IsOpen D) (hb : IsBounded D)
    (f : ℂ → ℂ) (N : ℂ → ℝ) (hN : Continuous N)
    (hnorm : ∀ z ∈ D, N z = ‖f z‖) (hd : DifferentiableOn ℂ f D)
    (C : ℝ) (hboundary : ∀ z ∈ frontier D, N z ≤ C)
    {z : ℂ} (hz : z ∈ closure D) : N z ≤ C := by
  by_cases hne : D.Nonempty
  · have hc : IsCompact (closure D) := hb.isCompact_closure
    obtain ⟨w, hw, hmax⟩ := hc.exists_isMaxOn hne.closure hN.continuousOn
    have hwbound : N w ≤ C := by
      by_cases hwin : w ∈ D
      · have hnot : D ≠ univ := by
          intro h
          exact hc.ne_univ (by simpa [h])
        obtain ⟨a, ha, har⟩ :=
          exists_mem_frontier_infDist_compl_eq_dist hwin hnot
        have haw : a ≠ w := by
          intro h
          subst a
          exact ha.2 (by simpa only [hD.interior_eq] using hwin)
        have hr : 0 < dist a w := dist_pos.mpr haw
        have hball : ball w (dist a w) ⊆ D := by
          rw [dist_comm, ← har]
          exact ball_infDist_compl_subset
        have hm : IsMaxOn (norm ∘ f) (ball w (dist a w)) w := by
          intro v hv
          change ‖f v‖ ≤ ‖f w‖
          rw [← hnorm v (hball hv), ← hnorm w hwin]
          exact hmax (subset_closure (hball hv))
        have heq := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
          (convex_ball w (dist a w)).isPreconnected isOpen_ball
          (hd.mono hball) (mem_ball_self hr) hm
        have hconst : ball w (dist a w) ⊆ {v | N v = N w} := by
          intro v hv
          calc
            N v = ‖f v‖ := hnorm v (hball hv)
            _ = ‖f w‖ := heq hv
            _ = N w := (hnorm w hwin).symm
        have hclosed : IsClosed {v : ℂ | N v = N w} :=
          isClosed_eq hN continuous_const
        have hacl : a ∈ closure (ball w (dist a w)) := by
          rw [closure_ball w hr.ne']
          exact mem_closedBall.mpr le_rfl
        have hNa : N a = N w :=
          (hclosed.closure_subset_iff.mpr hconst) hacl
        exact hNa ▸ hboundary a ha
      · have hwfront : w ∈ frontier D :=
          ⟨hw, fun hi => hwin (interior_subset hi)⟩
        exact hboundary w hwfront
    exact (hmax hz).trans hwbound
  · have hzero : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hfalse : False := by simpa [hzero] using hz
    exact hfalse.elim

/-- A power comparison for the actual exterior coordinate.
The preimage exclusion is imposed on the original domain, while forward
invariance is imposed on the literal slit. Neither is inferred from a
model or from a real-orbit sample. -/
theorem slit_power_comparison {t : ℝ} (ht : 0 < t)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (U : Set ℂ) (hU : IsOpen U) (hb : IsBounded U)
    (hforward : MapsTo F (realSegment t) (realSegment t))
    (hinverse : ∀ z ∈ U, F z ∈ realSegment t → z ∈ realSegment t)
    (m n : ℕ)
    (hboundary : ∀ z ∈ frontier U,
      slitAmplitude t z ^ m ≤ slitAmplitude t (F z) ^ n)
    {z : ℂ} (hz : z ∈ U) :
    slitAmplitude t z ^ m ≤ slitAmplitude t (F z) ^ n := by
  let D : Set ℂ := U \ realSegment t
  let f : ℂ → ℂ := fun w => slitAddress t w ^ m / slitAddress t (F w) ^ n
  let N : ℂ → ℝ := fun w => slitAmplitude t w ^ m / slitAmplitude t (F w) ^ n
  have hD : IsOpen D := hU.inter (realSegment_compact t).isClosed.isOpen_compl
  have hbD : IsBounded D := hb.subset diff_subset
  have hpos (w : ℂ) : 0 < slitAmplitude t (F w) ^ n :=
    pow_pos (lt_of_lt_of_le zero_lt_one (slitAmplitude_ge_one t (F w))) n
  have hN : Continuous N := by
    exact ((slitAmplitude_continuous t).pow m).div
      (((slitAmplitude_continuous t).comp hF.continuous).pow n)
      (fun w => (hpos w).ne')
  have hnorm : ∀ w ∈ D, N w = ‖f w‖ := by
    intro w hw
    simp only [N, f, norm_div, norm_pow, norm_slitAddress]
  have hd : DifferentiableOn ℂ f D := by
    intro w hw
    have hout : F w ∉ realSegment t :=
      fun h => hw.2 (hinverse w hw.1 h)
    have ha := slitAddress_differentiableAt ht hw.2
    have hc := (slitAddress_differentiableAt ht hout).comp w (hF w)
    exact ((ha.pow m).div (hc.pow n)
      (pow_ne_zero n (slitAddress_ne_zero t (F w)))).differentiableWithinAt
  have hNb : ∀ w ∈ frontier D, N w ≤ 1 := by
    intro w hw
    by_cases hws : w ∈ realSegment t
    · have h₁ := (slitAmplitude_eq_one_iff ht w).mpr hws
      have h₂ := (slitAmplitude_eq_one_iff ht (F w)).mpr (hforward hws)
      simp only [N, h₁, h₂, one_pow, div_one, le_refl]
    · have hwU : w ∈ closure U := (closure_mono diff_subset) hw.1
      have hwnU : w ∉ U := by
        intro hu
        exact hw.2 (by
          rw [hD.interior_eq]
          exact ⟨hu, hws⟩)
      have hwfront : w ∈ frontier U :=
        ⟨hwU, fun hi => hwnU (interior_subset hi)⟩
      apply (div_le_iff₀ (hpos w)).mpr
      simpa only [one_mul] using hboundary w hwfront
  by_cases hzs : z ∈ realSegment t
  · have h₁ := (slitAmplitude_eq_one_iff ht z).mpr hzs
    have h₂ := (slitAmplitude_eq_one_iff ht (F z)).mpr (hforward hzs)
    simp only [h₁, h₂, one_pow, le_refl]
  · have h := norm_boundary_bound D hD hbD f N hN hnorm hd 1 hNb
      (subset_closure (show z ∈ D from ⟨hz, hzs⟩))
    have h' := (div_le_iff₀ (hpos z)).mp h
    simpa only [one_mul] using h'

private theorem norm_eq_of_frontier_ball {r : ℝ} {z : ℂ}
    (hz : z ∈ frontier (ball (0 : ℂ) r)) : ‖z‖ = r := by
  have hle : ‖z‖ ≤ r := by
    simpa only [mem_closedBall, dist_zero_right] using
      closure_ball_subset_closedBall hz.1
  have hnlt : ¬ ‖z‖ < r := by
    intro h
    exact hz.2 (by
      rw [isOpen_ball.interior_eq]
      simpa only [mem_ball, dist_zero_right] using h)
  exact le_antisymm hle (le_of_not_gt hnlt)

/-- The uniform seven-to-six power expansion from the quarter-radius
boundary barrier. -/
theorem slit_amplification {t : ℝ}
    (htlo : 117/1000 ≤ t) (hthi : t ≤ 119/1000)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hforward : MapsTo F (realSegment t) (realSegment t))
    (hinverse : ∀ z : ℂ, ‖z‖ < 1/6 →
      F z ∈ realSegment t → z ∈ realSegment t)
    (houter : ∀ z : ℂ, ‖z‖ = 1/6 → 1/4 ≤ ‖F z‖)
    {z : ℂ} (hz : ‖z‖ < 1/6) :
    slitAmplitude t z ^ 7 ≤ slitAmplitude t (F z) ^ 6 := by
  have ht : 0 < t := by linarith
  apply slit_power_comparison ht F hF (ball 0 (1/6)) isOpen_ball isBounded_ball
    hforward (fun w hw => hinverse w (by simpa only [mem_ball, dist_zero_right] using hw))
    7 6 ?_ (by simpa only [mem_ball, dist_zero_right] using hz)
  intro w hw
  have heq := norm_eq_of_frontier_ball hw
  have hu := slitAmplitude_upper htlo heq.le
  have hl := slitAmplitude_lower ht hthi (houter w heq)
  have hnonneg : 0 ≤ slitAmplitude t w := (by norm_num : (0 : ℝ) ≤ 1).trans
    (slitAmplitude_ge_one t w)
  calc
    slitAmplitude t w ^ 7 ≤ (16/5 : ℝ)^7 :=
      pow_le_pow_left₀ hnonneg hu 7
    _ ≤ (39/10 : ℝ)^6 := by norm_num
    _ ≤ slitAmplitude t (F w)^6 :=
      pow_le_pow_left₀ (by norm_num) hl 6

end
end SlitGreenBarrier
