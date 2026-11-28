import TwoLevelOuterDomain
import ActualParentMarks

/-!
# Exhaustion by the actual normalized child sources

The domain below is the literal central component of the complete physical
p-return pullback, expressed in units of the actual critical return value.
The growing disk is proved to lie in that component, rather than merely in
the polynomial inverse image.  No supplied collar or selected inverse branch
is used in the inclusion.
-/

namespace ActualChildSource

open Set Function Filter Metric
open LimitingCrestQuadraticReturn NearTwoShooting NearTwoTip
open scoped Topology

noncomputable section

/-- The canonical physical source, in the positive critical-return coordinate. -/
def normalizedSource (c : ℝ) (p : ℕ) : Set ℂ :=
  {z | (criticalValue c p : ℂ) * z ∈ TwoLevelOuterDomain.source c p}

/-- A radius tending to infinity inside that same source. -/
def innerRadius (c : ℝ) (p : ℕ) : ℝ :=
  Real.sqrt (ActualParentMarks.targetRadius c p) / 4

theorem innerRadius_pos {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    0 < innerRadius c p := by
  have hr : 0 < ActualParentMarks.targetRadius c p := by
    exact div_pos (by positivity) hc.2.1
  exact div_pos (Real.sqrt_pos.2 hr) (by norm_num)

private theorem targetRadius_small {p : ℕ} (hp : 17 ≤ p) :
    TwoLevelOuterDomain.targetRadius p ≤ 1/131072 := by
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hp
  norm_num at h
  exact h

/-- The complete p-return of the scaled growing disk lies in the original
physical target disk.  The displacement bound retains every nonlinear term. -/
theorem scaled_disk_image {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ innerRadius c p) :
    ‖((quadraticMap c)^[p]) ((criticalValue c p : ℂ) * z)‖ <
      TwoLevelOuterDomain.targetRadius p := by
  let d : ℝ := criticalValue c p
  let t : ℝ := TwoLevelOuterDomain.targetRadius p
  let R : ℝ := innerRadius c p
  let S : ℝ := (4 : ℝ)^p
  have hd : 0 < d := hc.2.1
  have ht : 0 < t := TwoLevelOuterDomain.targetRadius_pos p
  have hR : 0 < R := innerRadius_pos hc
  have hS : 0 < S := by dsimp [S]; positivity
  have hsmall : d ≤ 12*t^2 := by
    dsimp [d, t]
    rw [TwoLevelOuterDomain.targetRadius_sq]
    exact hc.2.2.1
  have hSt : S*t^2 = 1 := by
    dsimp [S, t]
    rw [TwoLevelOuterDomain.targetRadius_sq]
    simpa only [mul_comm] using TwoLevelPerturbation.scale_mul_power p
  have hSd : S*d ≤ 12 := by
    calc
      S*d ≤ S*(12*t^2) := mul_le_mul_of_nonneg_left hsmall hS.le
      _ = 12*(S*t^2) := by ring
      _ = 12 := by rw [hSt]; ring
  have hratio : 0 < t/d := div_pos ht hd
  have hRsq : R^2 = (t/d)/16 := by
    change (Real.sqrt (t/d)/4)^2 = (t/d)/16
    rw [div_pow, Real.sq_sqrt hratio.le]
    norm_num
  have hphysical_sq : (d*R)^2 = d*t/16 := by
    calc
      (d*R)^2 = d^2*R^2 := by ring
      _ = d^2*((t/d)/16) := by rw [hRsq]
      _ = d*t/16 := by field_simp [hd.ne']
  have hscale_eq : S*(d*R)^2 = S*d*t/16 := by
    rw [hphysical_sq]
    ring
  have hscale_le : S*(d*R)^2 ≤ 3*t/4 := by
    rw [hscale_eq]
    have h := mul_le_mul_of_nonneg_right hSd ht.le
    nlinarith only [h]
  have htSmall : t ≤ 1/131072 := targetRadius_small hp
  have hscale : S*(d*R)^2 ≤ 1 := by
    linarith only [hscale_le, htSmall]
  have he : p-1+1 = p := by omega
  have hinput : ‖(d : ℂ)*z‖ ≤ d*R := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    exact mul_le_mul_of_nonneg_left hz hd.le
  have herr := TwoLevelPerturbation.orbit_displacement c (p-1) (d*R)
    ((d : ℂ)*z) (mul_nonneg hd.le hR.le)
    (fun j hj => hc.2.2.2.2.2.2 j (by omega))
    (by simpa only [he] using hscale) hinput
  rw [he] at herr
  change ‖((quadraticMap c)^[p]) ((d : ℂ)*z)-(d : ℂ)‖ ≤
    S*(d*R)^2/3 at herr
  have hnorm := norm_le_norm_sub_add
    (((quadraticMap c)^[p]) ((d : ℂ)*z)) (d : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd] at hnorm
  have htSq := mul_le_mul_of_nonneg_right htSmall ht.le
  change ‖((quadraticMap c)^[p]) ((d : ℂ)*z)‖ < t
  nlinarith only [herr, hnorm, hscale_le, hsmall, htSq, ht]

/-- The disk belongs to the full anchored source component.  Connectedness
of its scaled image supplies the component identification. -/
theorem closedBall_subset_normalizedSource {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    closedBall (0 : ℂ) (innerRadius c p) ⊆ normalizedSource c p := by
  let e : ℂ → ℂ := fun z => (criticalValue c p : ℂ)*z
  have hconn : IsPreconnected (e '' closedBall (0 : ℂ) (innerRadius c p)) :=
    (convex_closedBall (0 : ℂ) (innerRadius c p)).isPreconnected.image e
      (continuous_const.mul continuous_id).continuousOn
  have hzero : (0 : ℂ) ∈ e '' closedBall (0 : ℂ) (innerRadius c p) := by
    refine ⟨0, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_zero]
      exact (innerRadius_pos hc).le
    · simp [e]
  have hsub : e '' closedBall (0 : ℂ) (innerRadius c p) ⊆
      ((quadraticMap c)^[p]) ⁻¹' ball 0 (TwoLevelOuterDomain.targetRadius p) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_preimage, mem_ball_zero_iff]
    exact scaled_disk_image hp hc (by simpa only [mem_closedBall_zero_iff] using hz)
  have hcomp := hconn.subset_connectedComponentIn hzero hsub
  intro z hz
  exact hcomp ⟨z, hz, rfl⟩

/-- Positive scaling recovers exactly the repository's physical source. -/
theorem scaled_normalizedSource {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    (fun z : ℂ => (criticalValue c p : ℂ)*z) '' normalizedSource c p =
      TwoLevelOuterDomain.source c p := by
  have hd : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hc.2.1.ne'
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    have he : (criticalValue c p : ℂ)*(z/(criticalValue c p : ℂ)) = z := by
      field_simp [hd]
    refine ⟨z/(criticalValue c p : ℂ), ?_, he⟩
    change (criticalValue c p : ℂ)*(z/(criticalValue c p : ℂ)) ∈
      TwoLevelOuterDomain.source c p
    rw [he]
    exact hz

/-- An explicit period-only lower bound, uniform over every actual tip.
The integer division keeps the estimate within natural powers. -/
theorem innerRadius_lower {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    (2 : ℝ)^(p/2)/16 ≤ innerRadius c p := by
  have hr : 0 < ActualParentMarks.targetRadius c p :=
    div_pos (by positivity) hc.2.1
  have hpow : ((2 : ℝ)^(p/2))^2 ≤ (2 : ℝ)^p := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hlower := ActualParentMarks.targetRadius_lower hc
  have hsq : ((2 : ℝ)^(p/2)/4)^2 ≤ ActualParentMarks.targetRadius c p := by
    rw [div_pow]
    norm_num
    nlinarith only [hpow, hlower, sq_nonneg ((2 : ℝ)^(p/2))]
  have hroot : (2 : ℝ)^(p/2)/4 ≤
      Real.sqrt (ActualParentMarks.targetRadius c p) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hr.le]
    exact hsq
  change (2 : ℝ)^(p/2)/16 ≤ Real.sqrt (ActualParentMarks.targetRadius c p)/4
  linarith only [hroot]

/-- Every choice of the actual signed tips has expanding source inradius. -/
theorem innerRadius_tendsto (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => innerRadius (c n) (n+17)) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  have hr := (Filter.tendsto_atTop.1 (ActualParentMarks.targetRadius_tendsto c hc))
    ((4*(max b 0+1))^2)
  filter_upwards [hr] with n hn
  have hs := Real.sqrt_le_sqrt hn
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 4*(max b 0+1))] at hs
  change b ≤ Real.sqrt (ActualParentMarks.targetRadius (c n) (n+17))/4
  linarith [le_max_left b 0]

/-- Every fixed disk is eventually contained in the canonical normalized
source, uniformly over all its points. -/
theorem eventually_closedBall_subset (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) (R : ℝ) :
    ∀ᶠ n : ℕ in atTop, closedBall (0 : ℂ) R ⊆ normalizedSource (c n) (n+17) := by
  filter_upwards [(Filter.tendsto_atTop.1 (innerRadius_tendsto c hc)) R] with n hn
  exact (closedBall_subset_closedBall hn).trans
    (closedBall_subset_normalizedSource (by omega) (hc n))

/-- Kernel exhaustion is proved for the actual source components, not for
independently chosen comparison disks. -/
theorem eventually_compact_subset (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) {K : Set ℂ} (hK : IsCompact K) :
    ∀ᶠ n : ℕ in atTop, K ⊆ normalizedSource (c n) (n+17) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hK.isBounded
  filter_upwards [eventually_closedBall_subset c hc R] with n hn
  exact hR.trans hn

end

end ActualChildSource
