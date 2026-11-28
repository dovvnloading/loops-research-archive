import ActualCrestPaths

/-!
# Quantitative whole-disk survival at every admissible period

The earlier actual-support theorem transfers strict model inequalities by
compactness and therefore gives an unspecified eventual period threshold.
Here four explicit disks close under the literal normalized return at each
period `p ≥ 17`.  Their radii absorb a uniform map error of `1/5000`, far
larger than the actual error.  This yields numerical distance from every
support boundary and removes the eventual qualifier from `StrictSupport`.

The scalar center bounds and the quadratic disk factorization below are
the elementary estimates used in `LimitingCrestArcGates`; the new estimate
propagates the full perturbed map through all four disks, quantitatively.
-/

namespace UniformCrestSupport

open Set Function LimitingCrest LimitingCrestQuadraticReturn
open LoopsLimitingCrestParameter NearTwoTip GlobalCrestEstimates

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

private theorem quadratic_disk_step {κ a r A : ℝ} {z : ℂ}
    (hk : 0 ≤ κ) (hr : 0 ≤ r) (ha : |a| ≤ A) (hz : ‖z-(a:ℂ)‖ ≤ r) :
    ‖complexMap κ z-(realMap κ a : ℂ)‖ ≤ κ*r*(r+2*A) := by
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
  rw [hid,norm_mul,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hk]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hz hk) hsum (norm_nonneg _)
    (mul_nonneg hk hr)

/-- A complete disk propagates under the actual perturbed map.  Its
comparison center is the next quadratic center; the map error is paid
anew in the output radius, so no iterate approximation is assumed. -/
private theorem perturbed_disk_step {κ a r A ε : ℝ} {z : ℂ} {H : ℂ → ℂ}
    (hk : 0 ≤ κ) (hr : 0 ≤ r) (ha : |a| ≤ A) (hz : ‖z-(a:ℂ)‖ ≤ r)
    (hRA : r+A ≤ 3/2)
    (herr : ∀ w : ℂ, ‖w‖ ≤ 3/2 → ‖H w-complexMap κ w‖ ≤ ε) :
    ‖H z-(realMap κ a : ℂ)‖ ≤ ε+κ*r*(r+2*A) := by
  have hnorm := (disk_consequences hz ha).1.trans hRA
  calc
    ‖H z-(realMap κ a : ℂ)‖ ≤
        ‖H z-complexMap κ z‖+‖complexMap κ z-(realMap κ a : ℂ)‖ :=
      by simpa only [dist_eq_norm] using
        dist_triangle (H z) (complexMap κ z) (realMap κ a : ℂ)
    _ ≤ ε+κ*r*(r+2*A) :=
      add_le_add (herr z hnorm) (quadratic_disk_step hk hr ha hz)

set_option maxHeartbeats 800000 in
/-- The full closed crest disk has four-stage survival under any map
within `1/5000` of the appropriate quadratic model on the radius-`3/2`
disk.  Every bound is uniform on the whole disk, including its boundary. -/
theorem whole_support_bounds_of_error {κ : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000)) {H : ℂ → ℂ}
    (herr : ∀ w : ℂ, ‖w‖ ≤ 3/2 →
      ‖H w-complexMap κ w‖ ≤ 1/5000) {z : ℂ} (hz : z ∈ initialDisk) :
    (∀ m : ℕ, m ≤ 4 → ‖H^[m] z‖ ≤ (267/250 : ℝ)) ∧
      (931909/1000000 : ℝ) ≤ (H^[2] z).re ∧
      (H^[3] z).re ≤ (-537974/1000000 : ℝ) := by
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  obtain ⟨c1,c2,c3,c4⟩ := center_bounds hk
  have a0 : |(-3/4 : ℝ)| ≤ 3/4 := by norm_num
  have a1 : |realOrbit κ (-3/4) 1| ≤ 71/10000 := by
    rw [abs_le]; constructor <;> linarith [c1.1,c1.2]
  have a2 : |realOrbit κ (-3/4) 2| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [c2.1,c2.2]
  have a3 : |realOrbit κ (-3/4) 3| ≤ 791/1000 := by
    rw [abs_le]; constructor <;> linarith [c3.1,c3.2]
  have a4 : |realOrbit κ (-3/4) 4| ≤ 119/1000 := by
    rw [abs_le]; constructor <;> linarith [c4.1,c4.2]
  have d0 : ‖z-((-3/4 : ℝ):ℂ)‖ ≤ (133/2000 : ℝ) := by
    rw [show z-((-3/4 : ℝ):ℂ) = z+(3/4 : ℂ) by push_cast <;> ring]
    exact hz
  have d1 : ‖H^[1] z-(realOrbit κ (-3/4) 1 : ℂ)‖ ≤ (187/1000 : ℝ) := by
    have h := perturbed_disk_step hk0 (by norm_num) a0 d0 (by norm_num) herr
    have hK := mul_le_mul_of_nonneg_right hk.2
      (by norm_num : (0 : ℝ) ≤ (133/2000)*((133/2000)+2*(3/4)))
    change ‖H z-(realMap κ (-3/4):ℂ)‖ ≤ _
    nlinarith only [h,hK]
  have d2 : ‖H^[2] z-(realOrbit κ (-3/4) 2 : ℂ)‖ ≤ (68/1000 : ℝ) := by
    have h := perturbed_disk_step hk0 (by norm_num) a1 d1 (by norm_num) herr
    have hK := mul_le_mul_of_nonneg_right hk.2
      (by norm_num : (0 : ℝ) ≤ (187/1000)*((187/1000)+2*(71/10000)))
    change ‖H (H^[1] z)-(realMap κ (realOrbit κ (-3/4) 1):ℂ)‖ ≤ _
    nlinarith only [h,hK]
  have d3 : ‖H^[3] z-(realOrbit κ (-3/4) 3 : ℂ)‖ ≤ (252/1000 : ℝ) := by
    have h := perturbed_disk_step hk0 (by norm_num) a2 d2 (by norm_num) herr
    have hK := mul_le_mul_of_nonneg_right hk.2
      (by norm_num : (0 : ℝ) ≤ (68/1000)*((68/1000)+2*1))
    change ‖H (H^[2] z)-(realMap κ (realOrbit κ (-3/4) 2):ℂ)‖ ≤ _
    nlinarith only [h,hK]
  have d4 : ‖H^[4] z-(realOrbit κ (-3/4) 4 : ℂ)‖ ≤ (83/100 : ℝ) := by
    have h := perturbed_disk_step hk0 (by norm_num) a3 d3 (by norm_num) herr
    have hK := mul_le_mul_of_nonneg_right hk.2
      (by norm_num : (0 : ℝ) ≤ (252/1000)*((252/1000)+2*(791/1000)))
    change ‖H (H^[3] z)-(realMap κ (realOrbit κ (-3/4) 3):ℂ)‖ ≤ _
    nlinarith only [h,hK]
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

/-- Quantified full-support bounds for every actual signed tip from
period 17 onward.  The actual polynomial, at its own parameter, is used
at every stage; there is no limiting-parameter or support premise. -/
theorem actual_support_quantitative {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ initialDisk) :
    (∀ m : ℕ, m ≤ 4 → ‖(normalizedReturn c p)^[m] z‖ ≤ (267/250 : ℝ)) ∧
      (931909/1000000 : ℝ) ≤ (((normalizedReturn c p)^[2]) z).re ∧
      (((normalizedReturn c p)^[3]) z).re ≤ (-537974/1000000 : ℝ) := by
  apply whole_support_bounds_of_error hc.2.2.2.1 _ hz
  intro w hw
  exact (actual_return_error_small hp hc hw).trans (by norm_num)

/-- The strict support hypothesis required by the actual proper-path
and modulus construction holds at every admissible period `p ≥ 17`. -/
theorem actual_strict_support {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ActualCrestPaths.StrictSupport c p := by
  intro z hz
  have h := actual_support_quantitative hp hc hz
  refine ⟨fun m hm => (h.1 m hm).trans_lt (by norm_num),?_,?_⟩
  · linarith [h.2.1]
  · linarith [h.2.2]

/-- There is a uniform gap of at least `41/500` from the comparison
circle at each of the five phases, including the complete fourth image. -/
theorem actual_support_radius_margin {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ initialDisk) {m : ℕ} (hm : m ≤ 4) :
    (41/500 : ℝ) ≤ 23/20-‖(normalizedReturn c p)^[m] z‖ := by
  have h := (actual_support_quantitative hp hc hz).1 m hm
  linarith

end
end UniformCrestSupport
