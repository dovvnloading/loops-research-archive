import TwoLevelOuterChart
import TwoLevelPerturbation
import ThreeReturnDomain
import ThreeReturnDegree

/-!
# The actual outer domain containing the second-return phases

The source is the central component of a complete polynomial pullback.
A fixed ratio barrier gives compact containment before any shrinking.
The complete even divided difference identifies its fibers, and a whole
monic disk is shown to belong to this same physical component.
-/

namespace TwoLevelOuterDomain

open Set Function Metric Topology
open LimitingCrestQuadraticReturn NearTwoShooting TwoLevelOuterChart
open QuadraticCrestDividedDifference LoopsQuadraticCylinderCensus

noncomputable section

def targetRadius (p : ℕ) : ℝ := (1/2)^p

def source (c : ℝ) (p : ℕ) : Set ℂ :=
  connectedComponentIn (((quadraticMap c)^[p]) ⁻¹' ball 0 (targetRadius p)) 0

def sourceMap (c : ℝ) (p : ℕ) : source c p → ball (0 : ℂ) (targetRadius p) :=
  fun z => ⟨((quadraticMap c)^[p]) z,
    connectedComponentIn_subset _ 0 z.property⟩

theorem targetRadius_pos (p : ℕ) : 0 < targetRadius p := by
  unfold targetRadius
  positivity

theorem targetRadius_sq (p : ℕ) : (targetRadius p)^2 = scale p := by
  simp only [targetRadius, scale, ← pow_mul]
  rw [Nat.mul_comm p 2, pow_mul]
  norm_num

private theorem targetRadius_small {p : ℕ} (hp : 17 ≤ p) :
    targetRadius p ≤ 1/131072 := by
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hp
  norm_num at h
  exact h

private theorem small_scale_inside {p : ℕ} (hp : 17 ≤ p) :
    80*scale p < targetRadius p := by
  have hpos := targetRadius_pos p
  have hmul := mul_le_mul_of_nonneg_right (targetRadius_small hp) hpos.le
  have hs := targetRadius_sq p
  nlinarith only [hpos, hmul, hs]

private theorem coefficient_scale (p : ℕ) (hp : 0 < p) :
    (4 : ℝ)^(p-1)*scale p = 1/4 := by
  have he : p-1+1 = p := by omega
  have hpow : (4 : ℝ)^(p-1)*4 = (4 : ℝ)^p := by rw [← pow_succ, he]
  have hs := TwoLevelPerturbation.scale_mul_power p
  rw [← hpow] at hs
  nlinarith only [hs]

private theorem return_expansion (c : ℝ) (p : ℕ) (hp : 0 < p) (z : ℂ) :
    ((quadraticMap c)^[p]) z = (criticalValue c p : ℂ)+
      (returnCoefficient p c : ℂ)*z^2+quadraticRemainder c (p-1) z := by
  have he : p-1+1 = p := by omega
  simp only [quadraticRemainder, returnCoefficient, he]
  ring

theorem source_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hd : 0 < criticalValue c p) (hsmall : criticalValue c p ≤ 14*scale p) :
    (0 : ℂ) ∈ source c p := by
  apply mem_connectedComponentIn
  rw [mem_preimage, mem_ball_zero_iff, TwoLevelPerturbation.complex_criticalValue,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  have hs := small_scale_inside hp
  have hs0 := scale_pos p
  linarith

/-- The entire half-radius circle misses the complete pullback of the
outer target. The estimate includes all terms of the iterate. -/
theorem outer_barrier {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hd : 0 < criticalValue c p) (hsmall : criticalValue c p ≤ 14*scale p)
    (hlower : 3/20 < -returnCoefficient p c*scale p)
    {z : ℂ} (hz : ‖z‖ = targetRadius p/2) :
    targetRadius p < ‖((quadraticMap c)^[p]) z‖ := by
  have hp0 : 0 < p := by omega
  have he : p-1+1 = p := by omega
  have hA := coefficient_negative hlower
  have hr : 0 ≤ targetRadius p/2 :=
    div_nonneg (targetRadius_pos p).le (by norm_num)
  have hsq : (targetRadius p/2)^2 = scale p/4 := by
    nlinarith only [targetRadius_sq p]
  have hscale : (4 : ℝ)^(p-1+1)*(targetRadius p/2)^2 = 1/4 := by
    rw [he, hsq]
    have hs := TwoLevelPerturbation.scale_mul_power p
    nlinarith only [hs]
  have hE := complete_remainder_bound c (p-1) (targetRadius p/2) z hr
    (fun j hj => hcrit j (by omega)) (by rw [hscale]; norm_num) (le_of_eq hz)
  rw [hscale] at hE
  norm_num at hE
  have hlead : 3/80 < ‖(returnCoefficient p c : ℂ)*z^2‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg hA, hz, hsq]
    nlinarith only [hlower]
  have hid : (returnCoefficient p c : ℂ)*z^2 =
      ((quadraticMap c)^[p]) z-(criticalValue c p : ℂ)-
        quadraticRemainder c (p-1) z := by
    rw [return_expansion c p hp0 z]
    ring
  have ht := norm_sub_le
    (((quadraticMap c)^[p]) z-(criticalValue c p : ℂ))
    (quadraticRemainder c (p-1) z)
  rw [← hid] at ht
  have ht' := norm_sub_le (((quadraticMap c)^[p]) z) (criticalValue c p : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd] at ht'
  have hs := scale_small hp
  have hR := targetRadius_small hp
  linarith

/-- Complete physical-domain collision control, on a disk much larger
than the monic comparison disk. -/
theorem outer_collision_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hlower : 3/20 < -returnCoefficient p c*scale p)
    {z w : ℂ} (hz : ‖z‖ ≤ targetRadius p) (hw : ‖w‖ ≤ targetRadius p) :
    ((quadraticMap c)^[p]) z = ((quadraticMap c)^[p]) w ↔ z = w ∨ z = -w := by
  have he : p-1+1 = p := by omega
  have hscale : (4 : ℝ)^(p-1+1)*(targetRadius p)^2 = 1 := by
    rw [he, targetRadius_sq]
    nlinarith only [TwoLevelPerturbation.scale_mul_power p]
  have hE := evenSecant_error c (p-1) (targetRadius p) z w
    (targetRadius_pos p).le (fun j hj => hcrit j (by omega))
    (by rw [hscale]) hz hw
  rw [hscale] at hE
  have hD : evenSecant c (p-1) z w ≠ 0 := by
    intro hzero
    have hA := coefficient_negative hlower
    change ‖evenSecant c (p-1) z w-(returnCoefficient p c : ℂ)‖ ≤ _ at hE
    rw [hzero, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg hA] at hE
    have hm := mul_le_mul_of_nonneg_right hE (scale_pos p).le
    have hc := coefficient_scale p (by omega)
    nlinarith only [hm, hc, hlower]
  have hid := iterate_difference c (p-1) z w
  rw [he] at hid
  constructor
  · intro h
    have hprod : (z^2-w^2)*evenSecant c (p-1) z w = 0 := by
      rw [← hid, h, sub_self]
    have hzsq := (mul_eq_zero.mp hprod).resolve_right hD
    have hfact : (z-w)*(z+w) = 0 := by
      calc
        _ = z^2-w^2 := by ring
        _ = 0 := hzsq
    rcases mul_eq_zero.mp hfact with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  · intro h
    apply sub_eq_zero.mp
    rw [hid]
    rcases h with rfl | rfl <;> simp

theorem source_closure {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hd : 0 < criticalValue c p) (hsmall : criticalValue c p ≤ 14*scale p)
    (hlower : 3/20 < -returnCoefficient p c*scale p) :
    closure (source c p) ⊆ ball 0 (targetRadius p/2) ∧
      IsCompact (closure (source c p)) := by
  have hpoly : IsProperMap ((quadraticMap c)^[p]) := quadratic_iterate_proper (c : ℂ) p
  apply ThreeReturnDomain.component_closure_inside_barrier
    ((quadraticMap c)^[p]) hpoly.continuous (targetRadius p/2) (targetRadius p)
    (div_pos (targetRadius_pos p) (by norm_num))
  · have h0 := connectedComponentIn_subset _ 0 (source_zero hp hd hsmall)
    simpa [source] using h0
  · exact fun z hz => outer_barrier hp hcrit hd hsmall hlower hz

theorem source_open (c : ℝ) (p : ℕ) : IsOpen (source c p) :=
  (isOpen_ball.preimage (quadratic_iterate_proper (c : ℂ) p).continuous).connectedComponentIn

theorem source_connected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hd : 0 < criticalValue c p) (hsmall : criticalValue c p ≤ 14*scale p) :
    IsConnected (source c p) :=
  ⟨⟨0, source_zero hp hd hsmall⟩, isPreconnected_connectedComponentIn⟩

theorem sourceMap_proper (c : ℝ) (p : ℕ) : IsProperMap (sourceMap c p) :=
  ThreeReturnDomain.component_proper ((quadraticMap c)^[p])
    (quadratic_iterate_proper (c : ℂ) p) (ball 0 (targetRadius p)) 0 isOpen_ball

theorem source_image {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hd : 0 < criticalValue c p) (hsmall : criticalValue c p ≤ 14*scale p) :
    ((quadraticMap c)^[p]) '' source c p = ball 0 (targetRadius p) := by
  let f := (quadraticMap c)^[p]
  have hf : IsProperMap f := quadratic_iterate_proper (c : ℂ) p
  have h0 := connectedComponentIn_subset _ 0 (source_zero hp hd hsmall)
  exact localized_component_image f (f ⁻¹' ball 0 (targetRadius p))
    (ball 0 (targetRadius p)) (quadratic_iterate_open (c : ℂ) p) hf.isClosedMap
    (isOpen_ball.preimage hf.continuous)
    (convex_ball (0 : ℂ) (targetRadius p)).isPreconnected
    (fun _ hz => hz) (fun _ hz => hz.2) 0 h0

theorem source_symmetric {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hd : 0 < criticalValue c p) (hsmall : criticalValue c p ≤ 14*scale p) :
    ∀ z ∈ source c p, -z ∈ source c p := by
  have h0 := source_zero hp hd hsmall
  have hconn : IsPreconnected ((fun z : ℂ => -z) '' source c p) :=
    isPreconnected_connectedComponentIn.image _ continuous_neg.continuousOn
  have hhit : (0 : ℂ) ∈ (fun z : ℂ => -z) '' source c p := ⟨0, h0, neg_zero⟩
  have heven (z : ℂ) : ((quadraticMap c)^[p]) (-z) = ((quadraticMap c)^[p]) z := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show p ≠ 0 by omega)
    simp only [iterate_succ_apply, quadraticMap, neg_sq]
  have hsub : (fun z : ℂ => -z) '' source c p ⊆
      ((quadraticMap c)^[p]) ⁻¹' ball 0 (targetRadius p) := by
    rintro _ ⟨z, hz, rfl⟩
    change ((quadraticMap c)^[p]) (-z) ∈ ball 0 (targetRadius p)
    rw [heven]
    exact connectedComponentIn_subset _ 0 hz
  have h := hconn.subset_connectedComponentIn hhit hsub
  exact fun z hz => h ⟨z, hz, rfl⟩

theorem source_fiber_ncard {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hd : 0 < criticalValue c p) (hsmall : criticalValue c p ≤ 14*scale p)
    (hlower : 3/20 < -returnCoefficient p c*scale p)
    {y : ℂ} (hy : y ∈ ball 0 (targetRadius p)) :
    {z : ℂ | z ∈ source c p ∧ ((quadraticMap c)^[p]) z = y}.ncard =
      if y = (criticalValue c p : ℂ) then 1 else 2 := by
  have hcl := (source_closure hp hcrit hd hsmall hlower).1
  have hnorm {z : ℂ} (hz : z ∈ source c p) : ‖z‖ ≤ targetRadius p := by
    have hn : ‖z‖ < targetRadius p/2 := by simpa using hcl (subset_closure hz)
    linarith [targetRadius_pos p]
  have hi := source_image hp hd hsmall
  have h := ThreeReturnDegree.fiber_ncard ((quadraticMap c)^[p])
    (source c p) (ball 0 (targetRadius p)) (source_zero hp hd hsmall)
    (fun hz hw => outer_collision_iff hp hcrit hlower (hnorm hz) (hnorm hw))
    (source_symmetric hp hd hsmall) (by simpa only [SurjOn, hi] using (Subset.refl _)) hy
  simpa only [TwoLevelPerturbation.complex_criticalValue] using h

private theorem small_disk_image {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hd : 0 < criticalValue c p) (hsmall : criticalValue c p ≤ 14*scale p)
    {z : ℂ} (hz : ‖z‖ ≤ 16*scale p) :
    ‖((quadraticMap c)^[p]) z‖ ≤ 80*scale p := by
  have he : p-1+1 = p := by omega
  have hs := scale_small hp
  have hs0 := (scale_pos p).le
  have hscale : (4 : ℝ)^(p-1+1)*(16*scale p)^2 = 256*scale p := by
    rw [he]
    calc
      _ = 256*scale p*(scale p*(4 : ℝ)^p) := by ring
      _ = _ := by rw [TwoLevelPerturbation.scale_mul_power]; ring
  have hE := complete_remainder_bound c (p-1) (16*scale p) z (by positivity)
    (fun j hj => hcrit j (by omega)) (by rw [hscale]; linarith) hz
  rw [hscale] at hE
  have hA := TwoLevelPerturbation.coefficient_bound c (p-1)
    (fun j hj => hcrit j (by omega))
  have hlead : ‖(returnCoefficient p c : ℂ)*z^2‖ ≤ 64*scale p := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    change |quadraticCoefficient c (p-1)|*‖z‖^2 ≤ _
    calc
      _ ≤ (4 : ℝ)^(p-1)*(16*scale p)^2 :=
        mul_le_mul hA (pow_le_pow_left₀ (norm_nonneg z) hz 2)
          (sq_nonneg _) (by positivity)
      _ = 64*scale p := by
        calc
          _ = 256*scale p*((4 : ℝ)^(p-1)*scale p) := by ring
          _ = _ := by rw [coefficient_scale p (by omega)]; ring
  have ht := norm_add_le ((criticalValue c p : ℂ)+(returnCoefficient p c : ℂ)*z^2)
    (quadraticRemainder c (p-1) z)
  rw [← return_expansion c p (by omega) z] at ht
  have ht' := norm_add_le (criticalValue c p : ℂ) ((returnCoefficient p c : ℂ)*z^2)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd] at ht'
  have hsq := mul_le_mul_of_nonneg_right hs hs0
  nlinarith only [ht, ht', hlead, hE, hsmall, hsq, hs0]

theorem source_contains_small_disk {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hd : 0 < criticalValue c p) (hsmall : criticalValue c p ≤ 14*scale p) :
    closedBall (0 : ℂ) (16*scale p) ⊆ source c p := by
  have hconn := (convex_closedBall (0 : ℂ) (16*scale p)).isPreconnected
  have hzero : (0 : ℂ) ∈ closedBall (0 : ℂ) (16*scale p) := by
    simp only [mem_closedBall, dist_self]
    exact mul_nonneg (by norm_num) (scale_pos p).le
  apply hconn.subset_connectedComponentIn hzero
  intro z hz
  rw [mem_preimage, mem_ball_zero_iff]
  exact (small_disk_image hp hcrit hd hsmall (by simpa using hz)).trans_lt
    (small_scale_inside hp)

/-- The whole monic comparison disk belongs to the already selected
physical source, so every controlled second-return phase uses the same
outer domain. -/
theorem monic_disk_in_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hd : 0 < criticalValue c p) (hsmall : criticalValue c p ≤ 14*scale p)
    (hlower : 3/20 < -returnCoefficient p c*scale p)
    {u : ℂ} (hu : ‖u‖ ≤ 12/5) :
    u/(returnCoefficient p c : ℂ) ∈ source c p := by
  apply source_contains_small_disk hp hcrit hd hsmall
  rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg (coefficient_negative hlower)]
  apply (div_le_iff₀ (neg_pos.mpr (coefficient_negative hlower))).mpr
  nlinarith only [hu, hlower]

end

end TwoLevelOuterDomain
