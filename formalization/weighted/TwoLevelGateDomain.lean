import ThreeReturnParent

/-!
# A complete physical central gate with either sign of the critical scale

This interface is used for the negative second-level scale.  The central
source is the connected component of the complete literal inverse image.
Its construction uses a whole-circle barrier and exact signed fibers.
-/

namespace TwoLevelGateDomain

open Set Function Metric
open LimitingCrestQuadraticReturn LimitingCrest LimitingCrestPerturbation
open ThreeReturnDomain ThreeReturnParent ThreeReturnDegree
open LoopsQuadraticCylinderCensus

noncomputable section

def gateDisk : Set ℂ := {z | ‖z+(3/4 : ℂ)‖ ≤ (133/2000 : ℝ)}

structure CentralGate (c : ℝ) (n : ℕ) : Prop where
  scale_ne : criticalValue c n ≠ 0
  zero_mem : (0 : ℂ) ∈ parentSource c n
  source_open : IsOpen (parentSource c n)
  source_connected : IsConnected (parentSource c n)
  compact_closure : IsCompact (closure (parentSource c n))
  closure_inside : closure (parentSource c n) ⊆ ball 0 (23/20)
  image_eq : normalizedReturn c n '' parentSource c n = ball 0 (23/20)
  proper : IsProperMap (parentMap c n)
  fiber_card : ∀ y ∈ ball (0 : ℂ) (23/20),
    {z : ℂ | z ∈ parentSource c n ∧ normalizedReturn c n z = y}.ncard =
      if y = 1 then 1 else 2
  full_gate_disk : gateDisk ⊆ parentSource c n

theorem approximation_barrier (F : ℂ → ℂ) {k : ℝ}
    (hk : k ∈ Icc (17903/10000 : ℝ) (17904/10000))
    (he : ∀ z : ℂ, ‖z‖ ≤ 23/20 → ‖F z-complexMap k z‖ ≤ 1/500000)
    {z : ℂ} (hz : ‖z‖ = 23/20) : 23/20 < ‖F z‖ := by
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hn : ‖(k : ℂ)*z^2‖ = k*(23/20)^2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk0, hz]
  have htri : ‖(k : ℂ)*z^2‖ ≤ ‖complexMap k z‖+1 := by
    have hh := norm_sub_le (1 : ℂ) (complexMap k z)
    have hid : (1 : ℂ)-complexMap k z = (k : ℂ)*z^2 := by
      unfold complexMap
      ring
    rw [hid] at hh
    norm_num at hh
    linarith only [hh]
  have hdiff := norm_le_norm_sub_add (complexMap k z) (F z)
  rw [norm_sub_rev] at hdiff
  have herror := he z hz.le
  rw [hn] at htri
  nlinarith only [htri, hdiff, herror, hk.1]

theorem gateDisk_estimate (F : ℂ → ℂ) {k : ℝ}
    (hk : k ∈ Icc (17903/10000 : ℝ) (17904/10000))
    (he : ∀ z : ℂ, ‖z‖ ≤ 23/20 → ‖F z-complexMap k z‖ ≤ 1/500000)
    {z : ℂ} (hz : z ∈ gateDisk) : ‖z‖ < 23/20 ∧ ‖F z‖ < 7/20 := by
  have hzd : ‖z+(3/4 : ℂ)‖ ≤ (133/2000 : ℝ) := hz
  have hnorm : ‖z‖ ≤ (133/2000 : ℝ)+3/4 := by
    calc
      ‖z‖ = ‖(z+(3/4 : ℂ))-(3/4 : ℂ)‖ := by congr 1; ring
      _ ≤ ‖z+(3/4 : ℂ)‖+‖(3/4 : ℂ)‖ := norm_sub_le _ _
      _ ≤ (133/2000 : ℝ)+3/4 := by norm_num at *; linarith only [hzd]
  have hzR : ‖z‖ < 23/20 := by linarith only [hnorm]
  have hcenter : ‖complexMap k (-(3/4 : ℂ))‖ ≤ (1/100 : ℝ) := by
    rw [show (-(3/4 : ℂ)) = ((-3/4 : ℝ) : ℂ) by norm_num,
      complexMap_real, Complex.norm_real, Real.norm_eq_abs, abs_le]
    dsimp [realMap]
    constructor <;> nlinarith [hk.1, hk.2]
  have hdiff := quadratic_disk_lipschitz k
    (by linarith [hk.1]) (by linarith [hk.2]) z (-(3/4 : ℂ)) hzR.le
    (by norm_num)
  rw [sub_neg_eq_add] at hdiff
  have hnormQ := norm_le_norm_sub_add (complexMap k z) (complexMap k (-(3/4 : ℂ)))
  have hnormF := norm_le_norm_sub_add (F z) (complexMap k z)
  have herror := he z hzR.le
  exact ⟨hzR, by linarith only [hdiff, hzd, hcenter, hnormQ, hnormF, herror]⟩

theorem central_gate_of_estimates (c : ℝ) (n : ℕ) (hn : 0 < n)
    (hd : criticalValue c n ≠ 0) {k : ℝ}
    (hk : k ∈ Icc (17903/10000 : ℝ) (17904/10000))
    (he : ∀ z : ℂ, ‖z‖ ≤ 23/20 →
      ‖normalizedReturn c n z-complexMap k z‖ ≤ 1/500000)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 23/20 → ‖w‖ ≤ 23/20 →
      (normalizedReturn c n z = normalizedReturn c n w ↔ z = w ∨ z = -w)) :
    CentralGate c n := by
  let F := normalizedReturn c n
  have hproper := normalized_return_proper c n hd
  have hopen := normalized_return_open c n hd
  have hzero : ‖F 0‖ < 23/20 := by
    norm_num [F, normalized_return_zero c n hd]
  have h0 : (0 : ℂ) ∈ parentSource c n :=
    mem_connectedComponentIn (by simpa using hzero)
  obtain ⟨hinside, hcompact⟩ := component_closure_inside_barrier
    F hproper.continuous (23/20) (23/20) (by norm_num) hzero
    (fun z hz => approximation_barrier F hk he hz)
  change closure (parentSource c n) ⊆ ball 0 (23/20) at hinside
  have hnorm {z : ℂ} (hz : z ∈ parentSource c n) : ‖z‖ < 23/20 := by
    simpa using hinside (subset_closure hz)
  have honto : F '' parentSource c n = ball 0 (23/20) :=
    localized_component_image F (F ⁻¹' ball 0 (23/20)) (ball 0 (23/20))
      hopen hproper.isClosedMap (isOpen_ball.preimage hproper.continuous)
      (convex_ball (0 : ℂ) (23/20)).isPreconnected
      (fun _ hz => hz) (fun _ hz => hz.2) 0 (by simpa using hzero)
  have hsurj : SurjOn F (parentSource c n) (ball 0 (23/20)) := by
    simp only [SurjOn, honto, Subset.refl]
  have hsym := parent_source_symmetric c n hn hd
  have hexhaust {z : ℂ} (hz : ‖z‖ ≤ 23/20) (hfz : ‖F z‖ < 23/20) :
      z ∈ parentSource c n := by
    obtain ⟨w, hw, hwe⟩ := hsurj
      (show F z ∈ ball (0 : ℂ) (23/20) by simpa using hfz)
    rcases (hcollision (hnorm hw).le hz).mp hwe with heq | heq
    · exact heq ▸ hw
    · have hzw : z = -w := by rw [heq, neg_neg]
      rw [hzw]
      exact hsym w hw
  refine ⟨hd, h0, (isOpen_ball.preimage hproper.continuous).connectedComponentIn,
    ⟨⟨0, h0⟩, isPreconnected_connectedComponentIn⟩, hcompact, hinside, honto,
    component_proper F hproper (ball 0 (23/20)) 0 isOpen_ball, ?_, ?_⟩
  · intro y hy
    have hcard := fiber_ncard F (parentSource c n) (ball 0 (23/20)) h0
      (fun hz hw => hcollision (hnorm hz).le (hnorm hw).le) hsym hsurj hy
    simpa only [F, normalized_return_zero c n hd] using hcard
  · intro z hz
    have hb := gateDisk_estimate F hk he hz
    exact hexhaust hb.1.le (hb.2.trans (by norm_num))

end
end TwoLevelGateDomain
