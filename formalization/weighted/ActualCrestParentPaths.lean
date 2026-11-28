import ActualCrestPaths
import CircularCrestEnergy

/-!
# The actual full circular parent before its first restriction

The full parent meets the target slit only at its right real endpoint.
It meets the longer source slit at both real endpoints.  Consequently
the full circle, parametrized from angle zero to two pi, is a simple
proper loop in the target slit complement before restriction creates
its two semicircle children.  These are statements about literal sets
and curves, without an ideal-boundary marking assertion.
-/

namespace ActualCrestParentPaths

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open GlobalCrestEstimates GlobalCrestClassification GlobalCrestPhysical
open ActualCrestPaths ThreeReturnParent

noncomputable section

def parentCircle (s : ℝ) : Set ℂ := {z | ‖z+(3/4 : ℂ)‖ = s}

def parentPath (s t : ℝ) : ℂ := CircularCrestEnergy.point (-3/4) s t

def physicalSlitTarget (c : ℝ) (p : ℕ) : Set ℂ :=
  (fun z : ℂ => (criticalValue c p : ℂ)*z) '' slitTarget c p

def physicalSlitSource (c : ℝ) (p : ℕ) : Set ℂ :=
  (fun z : ℂ => (criticalValue c p : ℂ)*z) '' slitSource c p

def physicalTargetSlit (c : ℝ) (p : ℕ) : Set ℂ :=
  (fun z : ℂ => (criticalValue c p : ℂ)*z) '' targetSlit c p

def physicalSourceSlit (c : ℝ) (p : ℕ) : Set ℂ :=
  (fun z : ℂ => (criticalValue c p : ℂ)*z) '' sourceSlit

theorem actual_second_critical_sharp {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    (((normalizedReturn c p)^[2]) 0).re ∈ Ioo (-4/5 : ℝ) (-39/50) := by
  have he : ((normalizedReturn c p)^[2]) 0 = normalizedReturn c p 1 := by
    change normalizedReturn c p (normalizedReturn c p 0) = _
    rw [normalized_return_zero c p hc.2.1.ne']
  have hr := (Complex.abs_re_le_norm
    (normalizedReturn c p 1-complexMap (kappa p c) 1)).trans
      (actual_return_error_small hp hc (show ‖(1 : ℂ)‖ ≤ 3/2 by norm_num))
  norm_num [complexMap] at hr
  rw [he]
  have hk := hc.2.2.2.1
  constructor <;> linarith [hk.1,hk.2,(abs_le.mp hr).1,(abs_le.mp hr).2]

theorem parent_endpoint_order {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Icc (1/16 : ℝ) (parentOuter p)) :
    -1 < wEndpoint s ∧
    wEndpoint s < (((normalizedReturn c p)^[2]) 0).re ∧
    (((normalizedReturn c p)^[2]) 0).re < qEndpoint s ∧ qEndpoint s < 1 := by
  have hb := actual_second_critical_sharp hp hc
  have hsU := hs.2.trans (parentOuter_bounds hp).2
  dsimp only [qEndpoint,wEndpoint]
  exact ⟨by linarith,by linarith [hs.1,hb.1],by linarith [hs.1,hb.2],by linarith⟩

theorem q_mem_parentCircle {s : ℝ} (hs : 0 ≤ s) :
    (qEndpoint s : ℂ) ∈ parentCircle s := by
  change ‖(qEndpoint s : ℂ)+(3/4 : ℂ)‖ = s
  have he : (qEndpoint s : ℂ)+(3/4 : ℂ) = (s : ℂ) := by
    dsimp only [qEndpoint]
    push_cast
    ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs]

theorem w_mem_parentCircle {s : ℝ} (hs : 0 ≤ s) :
    (wEndpoint s : ℂ) ∈ parentCircle s := by
  change ‖(wEndpoint s : ℂ)+(3/4 : ℂ)‖ = s
  have he : (wEndpoint s : ℂ)+(3/4 : ℂ) = -(s : ℂ) := by
    dsimp only [wEndpoint]
    push_cast
    ring
  rw [he,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs]

theorem parentCircle_real_contacts {s : ℝ} {z : ℂ} (hz : z ∈ parentCircle s) :
    z.im = 0 ↔ z = (qEndpoint s : ℂ) ∨ z = (wEndpoint s : ℂ) := by
  constructor
  · intro hi
    have he : z+(3/4 : ℂ) = ((z.re+3/4 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hi]
    have ha : |z.re+3/4| = s := by
      change ‖z+(3/4 : ℂ)‖ = s at hz
      simpa only [he,Complex.norm_real,Real.norm_eq_abs] using hz
    rcases le_total 0 (z.re+3/4) with h | h
    · rw [abs_of_nonneg h] at ha
      left
      apply Complex.ext
      · simp only [Complex.ofReal_re,qEndpoint]
        linarith
      · simpa only [Complex.ofReal_im] using hi
    · rw [abs_of_nonpos h] at ha
      right
      apply Complex.ext
      · simp only [Complex.ofReal_re,wEndpoint]
        linarith
      · simpa only [Complex.ofReal_im] using hi
  · rintro (rfl | rfl) <;> simp

/-- The parent has one target-slit contact, even though it has two
source-slit contacts. Both facts use the literal actual critical cut. -/
theorem parentCircle_inter_targetSlit {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Icc (1/16 : ℝ) (parentOuter p)) :
    parentCircle s ∩ targetSlit c p = {(qEndpoint s : ℂ)} := by
  have ho := parent_endpoint_order hp hc hs
  ext z
  constructor
  · rintro ⟨hz,ht⟩
    rcases (parentCircle_real_contacts hz).mp ht.1 with h | h
    · exact h
    · rw [h] at ht
      have hb := ht.2.1
      simp only [Complex.ofReal_re] at hb
      linarith [ho.2.1]
  · intro hz
    have he : z = (qEndpoint s : ℂ) := hz
    rw [he]
    exact ⟨q_mem_parentCircle (by linarith [hs.1]),rfl,ho.2.2.1.le,ho.2.2.2.le⟩

theorem parentCircle_inter_sourceSlit {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Icc (1/16 : ℝ) (parentOuter p)) :
    parentCircle s ∩ sourceSlit = {(qEndpoint s : ℂ),(wEndpoint s : ℂ)} := by
  have ho := parent_endpoint_order hp hc hs
  have hqw : wEndpoint s < qEndpoint s := ho.2.1.trans ho.2.2.1
  ext z
  constructor
  · rintro ⟨hz,ht⟩
    simpa only [mem_insert_iff,mem_singleton_iff] using (parentCircle_real_contacts hz).mp ht.1
  · intro hz
    rcases (show z = (qEndpoint s : ℂ) ∨ z = (wEndpoint s : ℂ) by simpa using hz)
      with rfl | rfl
    · exact ⟨q_mem_parentCircle (by linarith [hs.1]),rfl,
        (ho.1.trans hqw).le,ho.2.2.2.le⟩
    · exact ⟨w_mem_parentCircle (by linarith [hs.1]),rfl,
        ho.1.le,(hqw.trans ho.2.2.2).le⟩

theorem parentCircle_in_full_disk {p : ℕ} (hp : 17 ≤ p) {s : ℝ}
    (hs : s ∈ Icc (1/16 : ℝ) (parentOuter p)) :
    parentCircle s ⊆ fullParentDisk := by
  intro z hz
  change ‖z+(3/4 : ℂ)‖ ≤ 1/8
  rw [show ‖z+(3/4 : ℂ)‖ = s from hz]
  exact hs.2.trans (parentOuter_bounds hp).2

theorem parentCircle_in_target_disk {p : ℕ} (hp : 17 ≤ p) {s : ℝ}
    (hs : s ∈ Icc (1/16 : ℝ) (parentOuter p)) :
    parentCircle s ⊆ Metric.ball (0 : ℂ) (23/20) := by
  intro z hz
  have hd := parentCircle_in_full_disk hp hs hz
  have hn := norm_le_norm_sub_add z (-(3/4 : ℂ))
  norm_num [sub_neg_eq_add] at hn
  change ‖z+(3/4 : ℂ)‖ ≤ 1/8 at hd
  simp only [Metric.mem_ball,dist_zero_right]
  linarith

theorem parentPath_continuous (s : ℝ) : Continuous (parentPath s) :=
  (CircularCrestEnergy.point_continuous _).comp (continuous_const.prodMk continuous_id)

theorem parentPath_mem_circle {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    parentPath s t ∈ parentCircle s := by
  change ‖parentPath s t+(3/4 : ℂ)‖ = s
  have he : parentPath s t+(3/4 : ℂ) = Complex.polarCoord.symm (s,t) := by
    unfold parentPath CircularCrestEnergy.point
    ring
  rw [he,Complex.norm_polarCoord_symm,abs_of_nonneg hs]

theorem parentPath_zero (s : ℝ) : parentPath s 0 = (qEndpoint s : ℂ) := by
  simp [parentPath,CircularCrestEnergy.point,Complex.polarCoord_symm_apply,qEndpoint]
  ring

theorem parentPath_two_pi (s : ℝ) : parentPath s (2*Real.pi) = (qEndpoint s : ℂ) := by
  simp [parentPath,CircularCrestEnergy.point,Complex.polarCoord_symm_apply,qEndpoint]
  ring

theorem parentPath_open_ne_q {s t : ℝ} (hs : 0 < s)
    (ht : t ∈ Ioo (0 : ℝ) (2*Real.pi)) : parentPath s t ≠ (qEndpoint s : ℂ) := by
  intro he
  have hr := congrArg Complex.re he
  simp only [parentPath,CircularCrestEnergy.point,Complex.polarCoord_symm_apply,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,qEndpoint] at hr
  norm_num at hr
  have hc : Real.cos t = 1 := by nlinarith
  have ht0 := (Real.cos_eq_one_iff_of_lt_of_lt
    (show -(2*Real.pi) < t by linarith [ht.1,Real.pi_pos]) ht.2).mp hc
  linarith [ht.1]

/-- Every open point of the full parent is in the actual target slit
complement; its two Euclidean endpoints coincide at q on the slit. -/
theorem parentPath_open_mem_target {p : ℕ} (hp : 17 ≤ p) {c s t : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Icc (1/16 : ℝ) (parentOuter p))
    (ht : t ∈ Ioo (0 : ℝ) (2*Real.pi)) : parentPath s t ∈ slitTarget c p := by
  have hr := parentPath_mem_circle (show 0 ≤ s by linarith [hs.1]) t
  refine ⟨parentCircle_in_target_disk hp hs hr,?_⟩
  intro hslit
  have he : parentPath s t ∈ ({(qEndpoint s : ℂ)} : Set ℂ) := by
    rw [← parentCircle_inter_targetSlit hp hc hs]
    exact ⟨hr,hslit⟩
  exact parentPath_open_ne_q (by linarith [hs.1]) ht he

theorem parentPath_mem_parent {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Icc (1/16 : ℝ) (parentOuter p)) (t : ℝ) :
    parentPath s t ∈ parentSource c p :=
  fullParentDisk_subset_parent hp hc
    (parentCircle_in_full_disk hp hs (parentPath_mem_circle (by linarith [hs.1]) t))

/-- The open parent loop is simple. Its closing endpoint is the only
identification when the closed angular interval is used. -/
theorem parentPath_injOn {s : ℝ} (hs : 0 < s) :
    InjOn (parentPath s) (Ioo (0 : ℝ) (2*Real.pi)) := by
  intro t ht u hu he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [parentPath,CircularCrestEnergy.point,Complex.polarCoord_symm_apply,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at hre
  simp only [parentPath,CircularCrestEnergy.point,Complex.polarCoord_symm_apply,
    Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,zero_mul,mul_one,add_zero,zero_add] at him
  have hcos : Real.cos t = Real.cos u := by nlinarith
  have hsin : Real.sin t = Real.sin u := by nlinarith
  have hdiff : Real.cos (t-u) = 1 := by
    rw [Real.cos_sub,hcos,hsin]
    nlinarith only [Real.sin_sq_add_cos_sq u]
  have hd := (Real.cos_eq_one_iff_of_lt_of_lt
    (show -(2*Real.pi) < t-u by linarith [ht.1,hu.2])
    (show t-u < 2*Real.pi by linarith [ht.2,hu.1])).mp hdiff
  linarith

theorem scaled_parentPath_eq (c : ℝ) (p : ℕ) (s t : ℝ) :
    (criticalValue c p : ℂ)*parentPath s t =
      CircularCrestEnergy.point (-((3*criticalValue c p/4 : ℝ) : ℂ))
        (criticalValue c p*s) t := by
  simp only [parentPath,CircularCrestEnergy.point,Complex.polarCoord_symm_apply]
  push_cast
  ring

theorem physical_parentPath_open_mem_target {p : ℕ} (hp : 17 ≤ p) {c ρ t : ℝ}
    (hc : ActualTip p c)
    (hρ : ρ ∈ Icc (criticalValue c p/16) (criticalValue c p*parentOuter p))
    (ht : t ∈ Ioo (0 : ℝ) (2*Real.pi)) :
    CircularCrestEnergy.point (-((3*criticalValue c p/4 : ℝ) : ℂ)) ρ t ∈
      physicalSlitTarget c p := by
  have hd := hc.2.1
  have hs : ρ/criticalValue c p ∈ Icc (1/16 : ℝ) (parentOuter p) := by
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith [hρ.1]
    · apply (div_le_iff₀ hd).mpr
      linarith [hρ.2]
  have he := scaled_parentPath_eq c p (ρ/criticalValue c p) t
  have hmul : criticalValue c p*(ρ/criticalValue c p) = ρ := by field_simp
  rw [hmul] at he
  exact ⟨parentPath (ρ/criticalValue c p) t,
    parentPath_open_mem_target hp hc hs ht,he⟩

theorem parentPath_endpoint_targetSlit {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Icc (1/16 : ℝ) (parentOuter p)) :
    parentPath s 0 ∈ targetSlit c p ∧
      parentPath s (2*Real.pi) ∈ targetSlit c p := by
  have ho := parent_endpoint_order hp hc hs
  rw [parentPath_zero,parentPath_two_pi]
  exact ⟨⟨rfl,ho.2.2.1.le,ho.2.2.2.le⟩,⟨rfl,ho.2.2.1.le,ho.2.2.2.le⟩⟩

theorem physical_parentPath_endpoint_targetSlit {p : ℕ} (hp : 17 ≤ p) {c ρ : ℝ}
    (hc : ActualTip p c)
    (hρ : ρ ∈ Icc (criticalValue c p/16) (criticalValue c p*parentOuter p)) :
    CircularCrestEnergy.point (-((3*criticalValue c p/4 : ℝ) : ℂ)) ρ 0 ∈
      physicalTargetSlit c p ∧
    CircularCrestEnergy.point (-((3*criticalValue c p/4 : ℝ) : ℂ)) ρ (2*Real.pi) ∈
      physicalTargetSlit c p := by
  have hd := hc.2.1
  have hs : ρ/criticalValue c p ∈ Icc (1/16 : ℝ) (parentOuter p) := by
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith [hρ.1]
    · apply (div_le_iff₀ hd).mpr
      linarith [hρ.2]
  have hmul : criticalValue c p*(ρ/criticalValue c p) = ρ := by field_simp
  have he (t : ℝ) := scaled_parentPath_eq c p (ρ/criticalValue c p) t
  simp only [hmul] at he
  have hm := parentPath_endpoint_targetSlit hp hc hs
  exact ⟨⟨parentPath (ρ/criticalValue c p) 0,hm.1,he 0⟩,
    ⟨parentPath (ρ/criticalValue c p) (2*Real.pi),hm.2,he _⟩⟩

/-- The scaled target slit is the actual critical-return interval. -/
theorem physicalTargetSlit_eq {p : ℕ} (_hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    physicalTargetSlit c p =
      {z : ℂ | z.im = 0 ∧ z.re ∈ Icc (criticalValue c (2*p)) (criticalValue c p)} := by
  have hd := hc.2.1
  have hscale := normalized_iterate_scale c p hd.ne' 2 0
  rw [mul_zero,quadratic_iterate_zero] at hscale
  have hcrit := congrArg Complex.re hscale
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hcrit
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    change z.im = 0 ∧ _ at hz
    simp only [mem_setOf_eq,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,hz.1,mul_zero,zero_mul,add_zero,sub_zero]
    exact ⟨trivial,by nlinarith [hz.2.1],by nlinarith [hz.2.2]⟩
  · rintro ⟨hi,hl,hu⟩
    refine ⟨((w.re/criticalValue c p : ℝ) : ℂ),⟨rfl,?_,?_⟩,?_⟩
    · apply (le_div_iff₀ hd).mpr
      nlinarith
    · apply (div_le_iff₀ hd).mpr
      simpa only [one_mul] using hu
    · apply Complex.ext
      · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
        field_simp
      · simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,
          zero_mul,add_zero] using hi.symm

/-- The small normalized target is contained in the archive's actual
physical target slit domain at its original outer radius. -/
theorem physicalSlitTarget_subset_literal {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    physicalSlitTarget c p ⊆ Metric.ball 0 (archivedTargetRadius p) \
      {z : ℂ | z.im = 0 ∧ z.re ∈ Icc (criticalValue c (2*p)) (criticalValue c p)} := by
  rintro w ⟨z,hz,rfl⟩
  have hd := hc.2.1
  have hn : ‖z‖ < 23/20 := by simpa using hz.1
  refine ⟨?_,?_⟩
  · simp only [Metric.mem_ball,dist_zero_right,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hd]
    exact (mul_lt_mul_of_pos_left hn hd).trans (actual_parent_scale_bound hp hc)
  · intro hw
    have hm : (criticalValue c p : ℂ)*z ∈ physicalTargetSlit c p := by
      rw [physicalTargetSlit_eq hp hc]
      exact hw
    obtain ⟨v,hv,he⟩ := hm
    have hdc : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hvz : v = z := mul_left_cancel₀ hdc he
    exact hz.2 (hvz ▸ hv)

theorem physicalSourceSlit_eq {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    physicalSourceSlit c p =
      {z : ℂ | z.im = 0 ∧ z.re ∈ Icc (-criticalValue c p) (criticalValue c p)} := by
  have hd := hc.2.1
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    change z.im = 0 ∧ _ at hz
    simp only [mem_setOf_eq,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,hz.1,mul_zero,zero_mul,add_zero,sub_zero]
    exact ⟨trivial,by nlinarith [hz.2.1],by nlinarith [hz.2.2]⟩
  · rintro ⟨hi,hl,hu⟩
    refine ⟨((w.re/criticalValue c p : ℝ) : ℂ),⟨rfl,?_,?_⟩,?_⟩
    · apply (le_div_iff₀ hd).mpr
      simpa only [neg_one_mul] using hl
    · apply (div_le_iff₀ hd).mpr
      simpa only [one_mul] using hu
    · apply Complex.ext
      · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
        field_simp
      · simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,
          zero_mul,add_zero] using hi.symm

theorem physicalSlitSource_subset_literal {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    physicalSlitSource c p ⊆ archivedParentSource c p \
      {z : ℂ | z.im = 0 ∧ z.re ∈ Icc (-criticalValue c p) (criticalValue c p)} := by
  rintro w ⟨z,hz,rfl⟩
  have hd := hc.2.1
  refine ⟨?_,?_⟩
  · apply physical_parent_subset_archived c p hd (actual_parent_restriction hp hc)
      (actual_parent_scale_bound hp hc)
    exact ⟨z,hz.1,rfl⟩
  · intro hw
    have hm : (criticalValue c p : ℂ)*z ∈ physicalSourceSlit c p := by
      rw [physicalSourceSlit_eq hc]
      exact hw
    obtain ⟨v,hv,he⟩ := hm
    have hdc : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hvz : v = z := mul_left_cancel₀ hdc he
    exact hz.2 (hvz ▸ hv)

end
end ActualCrestParentPaths
