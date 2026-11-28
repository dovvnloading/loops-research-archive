import ActualCrestLargeDisk
import LimitingCrestArcGates

/-!
# Complete actual crest support at every period from seventeen onward

The centered-disk recursion is propagated for the literal polynomial
return with an explicit perturbation allowance.  It gives one effective
period threshold, not a compactness-dependent eventual threshold.

The private real center enclosures below reuse the arithmetic argument of
`LimitingCrestArcGates`.  The new content is the perturbed complete-support
propagation and its specialization to every actual signed-tip parameter.
-/

namespace ActualCrestQuantitativeSupport

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter

noncomputable section

private theorem step_sq {κ x a b l u : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000))
    (hx : a ≤ x^2 ∧ x^2 ≤ b) (ha : 0 ≤ a)
    (hl : l ≤ 1-(17904/10000)*b) (hu : 1-(17903/10000)*a ≤ u) :
    realMap κ x ∈ Icc l u := by
  have hlow := mul_le_mul hk.1 hx.1 ha (by linarith [hk.1])
  have hupp := mul_le_mul hk.2 hx.2 (sq_nonneg x) (by norm_num)
  dsimp [realMap]
  constructor <;> linarith

private theorem step_pos {κ x a b l u : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000))
    (hx : x ∈ Icc a b) (ha : 0 ≤ a)
    (hl : l ≤ 1-(17904/10000)*b^2) (hu : 1-(17903/10000)*a^2 ≤ u) :
    realMap κ x ∈ Icc l u :=
  step_sq hk ⟨pow_le_pow_left₀ ha hx.1 2,
    pow_le_pow_left₀ (ha.trans hx.1) hx.2 2⟩ (sq_nonneg a) hl hu

private theorem step_neg {κ x a b l u : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000))
    (hx : x ∈ Icc a b) (hb : b ≤ 0)
    (hl : l ≤ 1-(17904/10000)*a^2) (hu : 1-(17903/10000)*b^2 ≤ u) :
    realMap κ x ∈ Icc l u := by
  have hs : b^2 ≤ x^2 ∧ x^2 ≤ a^2 := by
    constructor
    · simpa only [neg_sq] using
        pow_le_pow_left₀ (neg_nonneg.mpr hb) (neg_le_neg hx.2) 2
    · simpa only [neg_sq] using
        pow_le_pow_left₀ (neg_nonneg.mpr (hx.2.trans hb)) (neg_le_neg hx.1) 2
  exact step_sq hk hs (sq_nonneg b) hl hu

private theorem center_bounds {κ : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000)) :
    realOrbit κ (-3/4) 1 ∈ Icc (-71/10000) (-7043/1000000) ∧
    realOrbit κ (-3/4) 2 ∈ Icc (999909/1000000) (999912/1000000) ∧
    realOrbit κ (-3/4) 3 ∈ Icc (-790085/1000000) (-789974/1000000) ∧
    realOrbit κ (-3/4) 4 ∈ Icc (-117630/1000000) (-117252/1000000) := by
  have h0 : (-3/4 : ℝ) ∈ Icc (-3/4) (-3/4) := ⟨le_rfl,le_rfl⟩
  have h1 : realOrbit κ (-3/4) 1 ∈ Icc (-71/10000) (-7043/1000000) :=
    step_neg hk h0 (by norm_num) (by norm_num) (by norm_num)
  have h2 : realOrbit κ (-3/4) 2 ∈ Icc (999909/1000000) (999912/1000000) :=
    step_neg hk h1 (by norm_num) (by norm_num) (by norm_num)
  have h3 : realOrbit κ (-3/4) 3 ∈ Icc (-790085/1000000) (-789974/1000000) :=
    step_pos hk h2 (by norm_num) (by norm_num) (by norm_num)
  have h4 : realOrbit κ (-3/4) 4 ∈ Icc (-117630/1000000) (-117252/1000000) :=
    step_neg hk h3 (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h1,h2,h3,h4⟩

private theorem disk_consequences {z : ℂ} {a r A : ℝ}
    (hz : ‖z-(a:ℂ)‖ ≤ r) (ha : |a| ≤ A) :
    ‖z‖ ≤ r+A ∧ a-r ≤ z.re ∧ z.re ≤ a+r := by
  have hre := (Complex.abs_re_le_norm (z-(a:ℂ))).trans hz
  have hre' : |z.re-a| ≤ r := by simpa using hre
  have hnorm : ‖z‖ ≤ r+A := by
    calc
      ‖z‖ = ‖(z-(a:ℂ))+(a:ℂ)‖ := by congr 1; ring
      _ ≤ ‖z-(a:ℂ)‖+‖(a:ℂ)‖ := norm_add_le _ _
      _ ≤ r+A := by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using add_le_add hz ha
  exact ⟨hnorm,by linarith [(abs_le.mp hre').1],by linarith [(abs_le.mp hre').2]⟩

private theorem perturbed_disk_step {κ a r A : ℝ} {z : ℂ}
    (H : ℂ → ℂ) (hk : κ ∈ parameterInterval)
    (hr : 0 ≤ r) (ha : |a| ≤ A) (hz : ‖z-(a:ℂ)‖ ≤ r)
    (hsmall : r+A ≤ 2)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 2 →
      ‖H w-complexMap κ w‖ ≤ (1/1000000 : ℝ)) :
    ‖H z-(realMap κ a : ℂ)‖ ≤ 1/1000000+(9/5 : ℝ)*r*(r+2*A) := by
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have hA : 0 ≤ A := (abs_nonneg a).trans ha
  have hid : complexMap κ z-(realMap κ a : ℂ) =
      -(κ:ℂ)*(z-(a:ℂ))*(z+(a:ℂ)) := by
    simp only [complexMap,realMap,Complex.ofReal_sub,Complex.ofReal_one,
      Complex.ofReal_mul,Complex.ofReal_pow]
    ring
  have hsum : ‖z+(a:ℂ)‖ ≤ r+2*A := by
    calc
      ‖z+(a:ℂ)‖ = ‖(z-(a:ℂ))+((a:ℂ)+(a:ℂ))‖ := by congr 1; ring
      _ ≤ ‖z-(a:ℂ)‖+(‖(a:ℂ)‖+‖(a:ℂ)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ r+2*A := by simp only [Complex.norm_real,Real.norm_eq_abs]; linarith
  have hdiff : ‖complexMap κ z-(realMap κ a : ℂ)‖ ≤ κ*r*(r+2*A) := by
    rw [hid,norm_mul,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hk0]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hz hk0) hsum (norm_nonneg _)
      (mul_nonneg hk0 hr)
  have hK : κ*r*(r+2*A) ≤ (9/5 : ℝ)*r*(r+2*A) := by
    have hkU : κ ≤ (9/5 : ℝ) := by linarith [hk.2]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hkU hr) (by positivity)
  have herr := hclose z ((disk_consequences hz ha).1.trans hsmall)
  have htri : ‖H z-(realMap κ a : ℂ)‖ ≤
      ‖H z-complexMap κ z‖+‖complexMap κ z-(realMap κ a : ℂ)‖ := by
    simpa only [dist_eq_norm] using
      dist_triangle (H z) (complexMap κ z) (realMap κ a : ℂ)
  linarith only [htri,herr,hdiff,hK]

set_option maxHeartbeats 800000 in
/-- An explicit perturbation tolerance preserves all four complete
supports and their second- and third-image half-plane gates. Intermediate
domain containment is proved at each step of the recursion. -/
theorem perturbed_complete_support {κ : ℝ} (hk : κ ∈ parameterInterval)
    (H : ℂ → ℂ)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 2 →
      ‖H w-complexMap κ w‖ ≤ (1/1000000 : ℝ))
    {z : ℂ} (hz : z ∈ initialDisk) :
    (∀ m ≤ 4, ‖(H^[m]) z‖ ≤ (23/20 : ℝ)) ∧
      0 < ((H^[2]) z).re ∧ ((H^[3]) z).re < 0 := by
  obtain ⟨c1,c2,c3,c4⟩ := center_bounds hk
  have a0 : |(-3/4 : ℝ)| ≤ 3/4 := by norm_num
  have a1 : |realOrbit κ (-3/4) 1| ≤ (8/1000 : ℝ) := by
    rw [abs_le]; constructor <;> linarith [c1.1,c1.2]
  have a2 : |realOrbit κ (-3/4) 2| ≤ (1 : ℝ) := by
    rw [abs_le]; constructor <;> linarith [c2.1,c2.2]
  have a3 : |realOrbit κ (-3/4) 3| ≤ (8/10 : ℝ) := by
    rw [abs_le]; constructor <;> linarith [c3.1,c3.2]
  have a4 : |realOrbit κ (-3/4) 4| ≤ (15/100 : ℝ) := by
    rw [abs_le]; constructor <;> linarith [c4.1,c4.2]
  have d0 : ‖z-((-3/4 : ℝ):ℂ)‖ ≤ (133/2000 : ℝ) := by
    rw [show z-((-3/4 : ℝ):ℂ) = z+(3/4 : ℂ) by push_cast <;> ring]
    exact hz
  have d1 : ‖(H^[1]) z-(realOrbit κ (-3/4) 1 : ℂ)‖ ≤ (19/100 : ℝ) := by
    have h := perturbed_disk_step H hk (by norm_num) a0 d0 (by norm_num) hclose
    change ‖H z-(realMap κ (-3/4):ℂ)‖ ≤ _
    linarith only [h]
  have d2 : ‖(H^[2]) z-(realOrbit κ (-3/4) 2 : ℂ)‖ ≤ (71/1000 : ℝ) := by
    have h := perturbed_disk_step H hk (by norm_num) a1 d1 (by norm_num) hclose
    change ‖H ((H^[1]) z)-(realMap κ (realOrbit κ (-3/4) 1):ℂ)‖ ≤ _
    linarith only [h]
  have d3 : ‖(H^[3]) z-(realOrbit κ (-3/4) 3 : ℂ)‖ ≤ (265/1000 : ℝ) := by
    have h := perturbed_disk_step H hk (by norm_num) a2 d2 (by norm_num) hclose
    change ‖H ((H^[2]) z)-(realMap κ (realOrbit κ (-3/4) 2):ℂ)‖ ≤ _
    linarith only [h]
  have d4 : ‖(H^[4]) z-(realOrbit κ (-3/4) 4 : ℂ)‖ ≤ (89/100 : ℝ) := by
    have h := perturbed_disk_step H hk (by norm_num) a3 d3 (by norm_num) hclose
    change ‖H ((H^[3]) z)-(realMap κ (realOrbit κ (-3/4) 3):ℂ)‖ ≤ _
    linarith only [h]
  have b0 := disk_consequences d0 a0
  have b1 := disk_consequences d1 a1
  have b2 := disk_consequences d2 a2
  have b3 := disk_consequences d3 a3
  have b4 := disk_consequences d4 a4
  refine ⟨?_,by linarith [b2.2.1,c2.1],by linarith [b3.2.2,c3.2]⟩
  intro m hm
  interval_cases m
  · exact b0.1.trans (by norm_num)
  · exact b1.1.trans (by norm_num)
  · exact b2.1.trans (by norm_num)
  · exact b3.1.trans (by norm_num)
  · exact b4.1.trans (by norm_num)

/-- The complete actual crest support is certified at every period
`p ≥ 17`, for every admissible signed-tip parameter. -/
theorem actual_complete_support_all_periods {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    ∀ z ∈ initialDisk,
      (∀ m ≤ 4, ‖((normalizedReturn c p)^[m]) z‖ ≤ (23/20 : ℝ)) ∧
        0 < (((normalizedReturn c p)^[2]) z).re ∧
        (((normalizedReturn c p)^[3]) z).re < 0 := by
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale,one_div_pow,mul_one_div] using hc.2.2.1
  have hε : 216/(4 : ℝ)^p ≤ (1/1000000 : ℝ) := by
    have hpower := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hp
    have hpos : 0 < (4 : ℝ)^p := by positivity
    apply (div_le_iff₀ hpos).mpr
    norm_num at hpower
    linarith only [hpower]
  intro z hz
  apply perturbed_complete_support hc.2.2.2.1 (normalizedReturn c p) ?_ hz
  intro w hw
  exact (ActualCrestLargeDisk.normalized_return_error_two c p hp
    hc.2.2.2.2.2.2 hc.2.1 hsmall w hw).trans hε

end
end ActualCrestQuantitativeSupport

