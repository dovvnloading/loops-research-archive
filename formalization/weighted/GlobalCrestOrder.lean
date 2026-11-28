import GlobalCrestCrossing
import GlobalCrestEstimates

/-!
# Global radial rigidity of the actual crest

The entire original parent radius interval has the same three-stage sign
itinerary. Complete actual divided differences therefore exclude every
collision of the terminal coordinate, including outside the old endpoint
window. No order or injectivity hypothesis is imposed on that coordinate.
-/

namespace GlobalCrestOrder

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open GlobalCrestCrossing GlobalCrestEstimates

noncomputable section

theorem family_point_negative {p : ℕ} {c : ℝ} (F : Family p c) (s : Radius) :
    (F.point s).re ≤ -(5/8 : ℝ) := by
  have h := (Complex.abs_re_le_norm (F.point s+(3/4 : ℂ)))
  rw [F.point_radius] at h
  have hu := (abs_le.mp h).2
  norm_num [Complex.add_re] at hu
  linarith [s.property.2]

/-- The first image of every full-parent crossing lies in the radius 2/5
disk; the whole input circle has the same bound. -/
theorem first_image_small {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z+(3/4 : ℂ)‖ ≤ 1/8) :
    ‖normalizedReturn c p z‖ < 2/5 := by
  let k := kappa p c
  have hk := hc.2.2.2.1
  change k ∈ LoopsLimitingCrestParameter.parameterInterval at hk
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hkmax : k ≤ 9/5 := by linarith [hk.2]
  have hzn : ‖z‖ ≤ 7/8 := by
    calc
      ‖z‖ = ‖(z+(3/4 : ℂ))-(3/4 : ℂ)‖ := by congr 1; ring
      _ ≤ ‖z+(3/4 : ℂ)‖+‖(3/4 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 7/8 := by norm_num at *; linarith
  have he := actual_return_error_small hp hc (hzn.trans (by norm_num))
  have hcenter : |1-k*(9/16 : ℝ)| ≤ 1/100 := by
    rw [abs_le]
    constructor <;> linarith [hk.1,hk.2]
  have hsum : ‖z-(3/4 : ℂ)‖ ≤ 13/8 := by
    calc
      _ ≤ ‖z‖+‖(3/4 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 13/8 := by norm_num; linarith
  have hid : complexMap k z = ((1-k*(9/16 : ℝ) : ℝ) : ℂ) -
      (k : ℂ)*(z+(3/4 : ℂ))*(z-(3/4 : ℂ)) := by
    unfold complexMap
    push_cast
    ring
  have hquad : ‖complexMap k z‖ ≤ 1/100+(9/5 : ℝ)*(1/8)*(13/8) := by
    rw [hid]
    calc
      _ ≤ ‖((1-k*(9/16 : ℝ) : ℝ) : ℂ)‖+
          ‖(k : ℂ)*(z+(3/4 : ℂ))*(z-(3/4 : ℂ))‖ := norm_sub_le _ _
      _ = |1-k*(9/16 : ℝ)|+k*‖z+(3/4 : ℂ)‖*‖z-(3/4 : ℂ)‖ := by
        rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
          Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hk0]
      _ ≤ 1/100+(9/5 : ℝ)*(1/8)*(13/8) := by
        apply add_le_add hcenter
        exact mul_le_mul (mul_le_mul hkmax hz (norm_nonneg _) (by norm_num))
          hsum (norm_nonneg _) (by norm_num)
  have htri := norm_le_norm_sub_add (normalizedReturn c p z) (complexMap k z)
  change ‖normalizedReturn c p z-complexMap k z‖ ≤ _ at he
  linarith

/-- The second image is genuinely positive real on every parent radius.
Its upper bound exceeds the old approximation disk, so the enlarged
actual-return control is essential here. -/
theorem second_image_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) (s : Radius) :
    (99/100 : ℝ) < (((normalizedReturn c p)^[2]) (F.point s)).re ∧
      (((normalizedReturn c p)^[2]) (F.point s)).re < 13/10 ∧
      ‖((normalizedReturn c p)^[2]) (F.point s)‖ < 13/10 := by
  let w := normalizedReturn c p (F.point s)
  have hw : ‖w‖ < 2/5 := first_image_small hp hc (by
    rw [F.point_radius]
    exact s.property.2)
  have hwre : w.re = 0 := F.crossing s
  have he := actual_return_error_small hp hc
    (show ‖w‖ ≤ 3/2 by linarith)
  have hre := (Complex.abs_re_le_norm
    (normalizedReturn c p w-complexMap (kappa p c) w)).trans he
  have hq : (complexMap (kappa p c) w).re = 1+kappa p c*w.im^2 := by
    simp [complexMap,pow_two,Complex.mul_re,hwre]
  rw [Complex.sub_re,hq] at hre
  have him : |w.im| ≤ 2/5 := (Complex.abs_im_le_norm w).trans hw.le
  have him2 : w.im^2 ≤ (2/5 : ℝ)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg w.im) him 2
    simpa only [sq_abs] using h
  have hk := hc.2.2.2.1
  have hkp : 0 ≤ kappa p c := by linarith [hk.1]
  have hprod := mul_le_mul (show kappa p c ≤ (9/5 : ℝ) by linarith [hk.2])
    him2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 9/5)
  have hprod0 := mul_nonneg hkp (sq_nonneg w.im)
  have hlow : (99/100 : ℝ) < (normalizedReturn c p w).re := by
    linarith [(abs_le.mp hre).1]
  have hhigh : (normalizedReturn c p w).re < (13/10 : ℝ) := by
    linarith [(abs_le.mp hre).2]
  have hreal : (normalizedReturn c p w).im = 0 := F.second_real (by omega) s
  have heq : normalizedReturn c p w = ((normalizedReturn c p w).re : ℂ) := by
    apply Complex.ext <;> simp [hreal]
  refine ⟨hlow,hhigh,?_⟩
  change ‖normalizedReturn c p w‖ < 13/10
  rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith :
    0 < (normalizedReturn c p w).re)]
  exact hhigh

/-- Every actual terminal collision on the complete parent interval
forces equality of radii. Three exact signed-fiber arguments, with
different sign exclusions at the three stages, remove all alternatives. -/
theorem actual_terminal_injective {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    InjOn (terminal F) (Icc (1/16 : ℝ) (1/8)) := by
  intro s hs t ht he
  let ss : Radius := ⟨s,hs⟩
  let tt : Radius := ⟨t,ht⟩
  let H := normalizedReturn c p
  have hthree : (H^[3]) (F.point ss) = (H^[3]) (F.point tt) := by
    apply Complex.ext
    · simpa only [terminal,point,radiusProjection_eq hs,radiusProjection_eq ht] using he
    · exact (F.third_real (by omega) ss).trans (F.third_real (by omega) tt).symm
  have hbs := second_image_bounds hp hc F ss
  have hbt := second_image_bounds hp hc F tt
  have htwo : (H^[2]) (F.point ss) = (H^[2]) (F.point tt) := by
    have h := (actual_return_collision_iff hp hc
      (hbs.2.2.le.trans (by norm_num)) (hbt.2.2.le.trans (by norm_num))).mp hthree
    rcases h with h | h
    · exact h
    · have he' := congrArg Complex.re h
      simp only [Complex.neg_re] at he'
      exact (by linarith [hbs.1,hbt.1] : False).elim
  have hsone : ‖H (F.point ss)‖ ≤ 3/2 :=
    (first_image_small hp hc (by rw [F.point_radius]; exact hs.2)).le.trans (by norm_num)
  have htone : ‖H (F.point tt)‖ ≤ 3/2 :=
    (first_image_small hp hc (by rw [F.point_radius]; exact ht.2)).le.trans (by norm_num)
  have hone : H (F.point ss) = H (F.point tt) := by
    have h := (actual_return_collision_iff hp hc hsone htone).mp htwo
    rcases h with h | h
    · exact h
    · have he' := congrArg Complex.im h
      simp only [Complex.neg_im] at he'
      have hss : 0 < (H (F.point ss)).im := F.positive ss
      have htt : 0 < (H (F.point tt)).im := F.positive tt
      exact (by linarith only [he',hss,htt] : False).elim
  have hpoints : F.point ss = F.point tt := by
    have h := (actual_return_collision_iff hp hc
      ((F.point_parent_disk ss).trans (by norm_num))
      ((F.point_parent_disk tt).trans (by norm_num))).mp hone
    rcases h with h | h
    · exact h
    · have he' := congrArg Complex.re h
      simp only [Complex.neg_re] at he'
      exact (by linarith [family_point_negative F ss,family_point_negative F tt] : False).elim
  exact congrArg Subtype.val (F.point_injective hpoints)

end
end GlobalCrestOrder
