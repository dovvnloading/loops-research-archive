import ActualCrestCrossingWindow

/-!
# Actual angular crossings on the complete parent radius interval

The radial window contains the entire parent at every return period.
The angular window expands to keep the crossing branch at all those radii.  All crossings concern the literal normalized
return at an actual signed-tip parameter.
-/

namespace GlobalCrestCrossing

open Set Function LimitingCrest NearTwoTip NearTwoShooting
open LimitingCrestQuadraticReturn QuadraticCrestCrossing
open LoopsLimitingCrestParameter
noncomputable section

/-- A fixed interval containing the entire parent radius range at every period. -/
abbrev Radius := Icc (1/16 : ℝ) (1/8)

private theorem small_angle_sqrt_bounds {u : ℝ}
    (hu : u ∈ Icc (-1/10 : ℝ) (1/10)) :
    (99/100 : ℝ) ≤ Real.sqrt (1-u^2) ∧ Real.sqrt (1-u^2) ≤ 1 := by
  have hu2 : u^2 ≤ (1/10 : ℝ)^2 := sq_le_sq' (show -(1/10 : ℝ) ≤ u by linarith [hu.1]) hu.2
  have hnonneg : 0 ≤ 1-u^2 := by nlinarith
  have hsquare := Real.sq_sqrt hnonneg
  have hroot := Real.sqrt_nonneg (1-u^2)
  constructor
  · by_contra h
    have hprod : 0 < (99/100-Real.sqrt (1-u^2))*(99/100+Real.sqrt (1-u^2)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith only [hsquare, hu2, hprod]
  · by_contra h
    have hprod : 0 < (Real.sqrt (1-u^2)-1)*(Real.sqrt (1-u^2)+1) :=
      mul_pos (by linarith) (by linarith)
    nlinarith only [hsquare, hprod, sq_nonneg u]

private theorem small_angle_sqrt_lipschitz {u v : ℝ}
    (hu : u ∈ Icc (-1/10 : ℝ) (1/10))
    (hv : v ∈ Icc (-1/10 : ℝ) (1/10)) :
    |Real.sqrt (1-u^2)-Real.sqrt (1-v^2)| ≤ |u-v| := by
  let U := Real.sqrt (1-u^2)
  let V := Real.sqrt (1-v^2)
  have hU := small_angle_sqrt_bounds hu
  have hV := small_angle_sqrt_bounds hv
  change 99/100 ≤ U ∧ U ≤ 1 at hU
  change 99/100 ≤ V ∧ V ≤ 1 at hV
  have hu2 : u^2 ≤ (1/10 : ℝ)^2 := sq_le_sq' (show -(1/10 : ℝ) ≤ u by linarith [hu.1]) hu.2
  have hv2 : v^2 ≤ (1/10 : ℝ)^2 := sq_le_sq' (show -(1/10 : ℝ) ≤ v by linarith [hv.1]) hv.2
  have hUsq : U^2 = 1-u^2 := Real.sq_sqrt (by nlinarith)
  have hVsq : V^2 = 1-v^2 := Real.sq_sqrt (by nlinarith)
  have hprod : (U-V)*(U+V) = -(u-v)*(u+v) := by nlinarith
  have habs := congrArg abs hprod
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (show 0 ≤ U+V by linarith)] at habs
  have hsum : |u+v| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  calc
    |U-V| = |U-V| *1 := by ring
    _ ≤ |U-V| *(U+V) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = |u-v| *|u+v| := habs
    _ ≤ |u-v| *1 := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = |u-v| := by ring

/-- The upper-circle parametrization has an explicit angular Lipschitz
bound on the fixed angular interval used for the full parent. -/
theorem circlePoint_angle_bound (s : ℝ) {u v : ℝ}
    (hu : u ∈ Icc (-1/10 : ℝ) (1/10))
    (hv : v ∈ Icc (-1/10 : ℝ) (1/10)) :
    ‖circlePoint s u-circlePoint s v‖ ≤ 2*|s| *|u-v| := by
  have hid : circlePoint s u-circlePoint s v =
      ((s*(u-v) : ℝ) : ℂ) +
        ((s*(Real.sqrt (1-u^2)-Real.sqrt (1-v^2)) : ℝ) : ℂ)*Complex.I := by
    unfold circlePoint
    push_cast
    ring
  rw [hid]
  calc
    ‖((s*(u-v) : ℝ) : ℂ) +
        ((s*(Real.sqrt (1-u^2)-Real.sqrt (1-v^2)) : ℝ) : ℂ)*Complex.I‖ ≤
        ‖((s*(u-v) : ℝ) : ℂ)‖ +
          ‖((s*(Real.sqrt (1-u^2)-Real.sqrt (1-v^2)) : ℝ) : ℂ)*Complex.I‖ := norm_add_le _ _
    _ = |s| *|u-v| + |s| *|Real.sqrt (1-u^2)-Real.sqrt (1-v^2)| := by
      rw [norm_mul, Complex.norm_I, mul_one]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    _ ≤ |s| *|u-v| + |s| *|u-v| :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (small_angle_sqrt_lipschitz hu hv)
        (abs_nonneg s))
    _ = 2*|s| *|u-v| := by ring


/-- Continuity of the literal normalized return in the complex variable. -/
theorem normalizedReturn_continuous (c : ℝ) (p : ℕ) :
    Continuous (normalizedReturn c p) := by
  have hf : Continuous (quadraticMap c) := by unfold quadraticMap; fun_prop
  exact ((hf.iterate p).comp (continuous_const.mul continuous_id)).div_const _

private theorem iterate_real (c t : ℝ) (n : ℕ) :
    ((quadraticMap c)^[n]) (t : ℂ) =
      (((fun x : ℝ => x^2+c)^[n]) t : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply',ih]
    simp [quadraticMap]

/-- Real inputs have real normalized images. -/
theorem normalizedReturn_real (c t : ℝ) (p : ℕ) :
    (normalizedReturn c p (t : ℂ)).im = 0 := by
  unfold normalizedReturn
  rw [← Complex.ofReal_mul,iterate_real]
  simp

/-- A nonzero return sends the imaginary axis to the real axis. -/
theorem normalizedReturn_imaginary (c t : ℝ) (p : ℕ) (hp : 0 < p) :
    (normalizedReturn c p ((t : ℂ)*Complex.I)).im = 0 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  let d := criticalValue c (n+1)
  have hfirst : quadraticMap c ((d : ℂ)*((t : ℂ)*Complex.I)) =
      ((c-(d*t)^2 : ℝ) : ℂ) := by
    simp [quadraticMap,mul_pow,Complex.I_sq] <;> ring
  unfold normalizedReturn
  change (((quadraticMap c)^[n+1]) ((d : ℂ)*((t : ℂ)*Complex.I))/(d : ℂ)).im = 0
  rw [iterate_succ_apply,hfirst,iterate_real]
  simp

private theorem parent_window {s : ℝ} (hs : s ∈ Radius) :
    s ∈ Icc (1/16 : ℝ) (1/8) := ⟨hs.1, by linarith [hs.2]⟩

/-- The complete upper semicircle stays inside the certified map disk. -/
theorem circlePoint_full_disk {s u : ℝ} (hs : s ∈ Radius)
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    ‖circlePoint s u‖ ≤ 23/20 := by
  have hr := circle_radius (show 0 ≤ s by linarith [hs.1]) hu
  calc
    ‖circlePoint s u‖ = ‖(circlePoint s u + (3/4 : ℂ)) - (3/4 : ℂ)‖ := by
      congr 1; ring
    _ ≤ ‖circlePoint s u + (3/4 : ℂ)‖ + ‖(3/4 : ℂ)‖ := norm_sub_le _ _
    _ = s+3/4 := by rw [hr]; norm_num
    _ ≤ 23/20 := by linarith [hs.2]

/-- The enlarged crossing rectangle stays inside the certified map disk. -/
theorem circlePoint_disk {s u : ℝ} (hs : s ∈ Radius)
    (hu : u ∈ Icc (-1/10 : ℝ) (1/10)) :
    ‖circlePoint s u‖ ≤ 23/20 :=
  circlePoint_full_disk hs (by constructor <;> linarith [hu.1,hu.2])

/-- Both angular walls retain a strict margin on the entire parent radius interval. -/
theorem crossing_endpoint_margins {κ s : ℝ} (hk : κ ∈ parameterInterval)
    (hs : s ∈ Radius) :
    crossing κ s (-1/10) < -1/2000 ∧
      1/2000 < crossing κ s (1/10) := by
  have hsl := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/16) hs.1 2
  have hsu := pow_le_pow_left₀ (by linarith [hs.1] : 0 ≤ s) hs.2 2
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  let a := 9/16-(3/2)*s*(-1/10)+s^2*(2*(-1/10 : ℝ)^2-1)
  let b := 9/16-(3/2)*s*(1/10)+s^2*(2*(1/10 : ℝ)^2-1)
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hss : s^2 ≤ s/8 := by
    nlinarith only [mul_nonneg hs0 (sub_nonneg.mpr hs.2)]
  have ha : (559/1000 : ℝ) ≤ a := by dsimp [a]; nlinarith [hs.1]
  have hb : b ≤ (558/1000 : ℝ) := by dsimp [b]; nlinarith [hs.1]
  have hb0 : 0 ≤ b := by dsimp [b]; nlinarith [hs.2]
  have hpa := mul_le_mul hk.1 ha (by norm_num) hk0
  have hpb := mul_le_mul hk.2 hb hb0 (by norm_num)
  change 1-κ*a < -1/2000 ∧ 1/2000 < 1-κ*b
  constructor <;> nlinarith only [hpa,hpb]

private theorem model_crossing_exists {κ s : ℝ} (hk : κ ∈ parameterInterval)
    (hs : s ∈ Radius) :
    ∃ u : ℝ, u ∈ Ioo (-1/10 : ℝ) (1/10) ∧ crossing κ s u = 0 := by
  have hcont : Continuous (crossing κ s) := by unfold crossing; fun_prop
  obtain ⟨hl,hr⟩ := crossing_endpoint_margins hk hs
  obtain ⟨u,hu,hz⟩ := intermediate_value_Icc
    (by norm_num : (-1/10 : ℝ) ≤ 1/10) hcont.continuousOn
    (show (0 : ℝ) ∈ Icc (crossing κ s (-1/10)) (crossing κ s (1/10)) by
      constructor <;> linarith)
  refine ⟨u,⟨?_,?_⟩,hz⟩
  · by_contra h
    have he : u = -1/10 := by linarith [hu.1]
    rw [he] at hz
    linarith
  · by_contra h
    have he : u = 1/10 := by linarith [hu.2]
    rw [he] at hz
    linarith

/-- The same algebraic model branch remains the small crossing throughout
the window; the formula is not a separately selected limit. -/
theorem crossingCos_spec {κ s : ℝ} (hk : κ ∈ parameterInterval)
    (hs : s ∈ Radius) :
    crossingCos κ s ∈ Ioo (-1/10 : ℝ) (1/10) ∧
      crossing κ s (crossingCos κ s) = 0 := by
  obtain ⟨u,hu,hz⟩ := model_crossing_exists hk hs
  have hk0 : κ ≠ 0 := by linarith [hk.1]
  have hs0 : s ≠ 0 := by linarith [hs.1]
  have hsu : s*u ≤ (1/8 : ℝ)*(1/10) :=
    (mul_le_mul_of_nonneg_left hu.2.le (by linarith [hs.1])).trans
      (mul_le_mul_of_nonneg_right hs.2 (by norm_num))
  have hpos : 0 ≤ (3/2 : ℝ)-4*s*u := by nlinarith
  have heq : 8/κ+8*s^2-9/4 = (3/2-4*s*u)^2 := by
    dsimp [crossing] at hz
    field_simp [hk0]
    nlinarith [hz]
  have hformula : crossingCos κ s = u := by
    unfold crossingCos
    rw [heq,Real.sqrt_sq_eq_abs,abs_of_nonneg hpos]
    field_simp [hs0]
    ring
  rw [hformula]
  exact ⟨hu,hz⟩

/-- The model circle crossing is exactly the radical terminal branch. -/
theorem radialPoint_eq_circlePoint {κ s : ℝ} (hk : κ ∈ parameterInterval)
    (hs : s ∈ Radius) :
    radialPoint κ s = circlePoint s (crossingCos κ s) := by
  have hspec := crossingCos_spec hk hs
  apply LimitingCrest.radialPoint_eq_circlePoint hk (parent_window hs)
    (show crossingCos κ s ∈ Icc (-1 : ℝ) 1 by
      constructor <;> linarith [hspec.1.1,hspec.1.2])
  rw [crossingCos_radial_coordinate (show s ≠ 0 by linarith [hs.1])]
  field_simp [show s ≠ 0 by linarith [hs.1]]
  <;> ring

private theorem actual_small {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    criticalValue c p ≤ 12/(4 : ℝ)^p := by
  simpa only [scale,one_div_pow,mul_one_div] using hc.2.2.1

private theorem actual_band {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    c ∈ Icc (-2 : ℝ) 0 := by
  have hb := parameter_band hp hc.1
  exact ⟨hb.1,by linarith [hb.2]⟩

private theorem actual_close {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20) :
    ‖normalizedReturn c p z-complexMap (kappa p c) z‖ ≤ 1/500000 := by
  have he := normalized_return_error c p (by omega) hc.2.2.2.2.2.2
    hc.2.1 (actual_small hc) z hz
  change ‖normalizedReturn c p z-complexMap (kappa p c) z‖ ≤ _ at he
  apply he.trans
  apply (div_le_iff₀ (show (0 : ℝ) < 4^p by positivity)).mpr
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hp
  norm_num at hpow
  linarith

/-- Every radius has an actual crossing strictly between the angular walls. -/
theorem actual_crossing_exists {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Radius) :
    ∃ u : ℝ, u ∈ Ioo (-1/10 : ℝ) (1/10) ∧
      (normalizedReturn c p (circlePoint s u)).re = 0 := by
  let H := normalizedReturn c p
  have hf : Continuous (quadraticMap c) := by unfold quadraticMap; fun_prop
  have hH : Continuous H :=
    ((hf.iterate p).comp (continuous_const.mul continuous_id)).div_const _
  have hcirc : Continuous (circlePoint s) := by unfold circlePoint; fun_prop
  have hcont : Continuous (fun u : ℝ => (H (circlePoint s u)).re) :=
    Complex.continuous_re.comp (hH.comp hcirc)
  have hqre (u : ℝ) (hu : u ∈ Icc (-1/10 : ℝ) (1/10)) :
      (complexMap (kappa p c) (circlePoint s u)).re = crossing (kappa p c) s u := by
    rw [circle_image _ _ (show u ∈ Icc (-1 : ℝ) 1 by
      constructor <;> linarith [hu.1,hu.2])]
    simp
  have herr (u : ℝ) (hu : u ∈ Icc (-1/10 : ℝ) (1/10)) :
      |(H (circlePoint s u)).re-crossing (kappa p c) s u| ≤ 1/500000 := by
    have h := (Complex.abs_re_le_norm
      (H (circlePoint s u)-complexMap (kappa p c) (circlePoint s u))).trans
        (actual_close hp hc (circlePoint_disk hs hu))
    simpa only [Complex.sub_re,hqre u hu] using h
  have hlE := (abs_le.mp (herr (-1/10) (by constructor <;> norm_num))).2
  have hrE := (abs_le.mp (herr (1/10) (by constructor <;> norm_num))).1
  obtain ⟨hl,hr⟩ := crossing_endpoint_margins hc.2.2.2.1 hs
  have hleft : (H (circlePoint s (-1/10))).re < 0 := by linarith
  have hright : 0 < (H (circlePoint s (1/10))).re := by linarith
  obtain ⟨u,hu,hz⟩ := intermediate_value_Icc
    (by norm_num : (-1/10 : ℝ) ≤ 1/10) hcont.continuousOn
    (show (0 : ℝ) ∈ Icc ((H (circlePoint s (-1/10))).re)
      ((H (circlePoint s (1/10))).re) from ⟨hleft.le,hright.le⟩)
  refine ⟨u,⟨?_,?_⟩,hz⟩
  · by_contra h
    have he : u = -1/10 := by linarith [hu.1]
    rw [he] at hz
    linarith
  · by_contra h
    have he : u = 1/10 := by linarith [hu.2]
    rw [he] at hz
    linarith

private theorem circlePoint_square_angle_bound {s u v : ℝ} (hs : s ∈ Radius)
    (hu : u ∈ Icc (-1/10 : ℝ) (1/10))
    (hv : v ∈ Icc (-1/10 : ℝ) (1/10)) :
    ‖(circlePoint s u)^2-(circlePoint s v)^2‖ ≤ |u-v| := by
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hd := circlePoint_angle_bound s hu hv
  rw [abs_of_nonneg hs0] at hd
  have hz := circlePoint_disk hs hu
  have hw := circlePoint_disk hs hv
  have hsum : ‖circlePoint s u+circlePoint s v‖ ≤ (23/10 : ℝ) :=
    (norm_add_le _ _).trans (by linarith)
  rw [sq_sub_sq,norm_mul,mul_comm]
  calc
    ‖circlePoint s u-circlePoint s v‖*‖circlePoint s u+circlePoint s v‖ ≤
        (2*s*|u-v|)*(23/10) := mul_le_mul hd hsum (norm_nonneg _) (by positivity)
    _ ≤ |u-v| := by
      nlinarith only [mul_le_mul_of_nonneg_right hs.2 (abs_nonneg (u-v)),abs_nonneg (u-v)]

/-- Quantitative angular ordering holds up to and beyond the terminal endpoint. -/
theorem actual_crossing_growth {p : ℕ} (hp : 17 ≤ p) {c s u v : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Radius)
    (hu : u ∈ Icc (-1/10 : ℝ) (1/10))
    (hv : v ∈ Icc (-1/10 : ℝ) (1/10)) (huv : u ≤ v) :
    (v-u)/20 ≤ (normalizedReturn c p (circlePoint s v)).re-
      (normalizedReturn c p (circlePoint s u)).re := by
  have hu1 : u ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hu.1,hu.2]
  have hv1 : v ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hv.1,hv.2]
  have hg := crossing_global_growth hc.2.2.2.1 (parent_window hs) hu1 hv1 huv
  have he := QuadraticCrestDividedDifference.normalized_remainder_difference c p
    (by omega) (actual_band hp hc) hc.2.1 (actual_small hc)
    (circlePoint_disk hs hv) (circlePoint_disk hs hu)
  change ‖(normalizedReturn c p (circlePoint s v)-complexMap (kappa p c) (circlePoint s v))-
    (normalizedReturn c p (circlePoint s u)-complexMap (kappa p c) (circlePoint s u))‖ ≤ _ at he
  have hb := circlePoint_square_angle_bound hs hv hu
  rw [abs_of_nonneg (sub_nonneg.mpr huv)] at hb
  have hRe := (Complex.abs_re_le_norm
    ((normalizedReturn c p (circlePoint s v)-complexMap (kappa p c) (circlePoint s v))-
      (normalizedReturn c p (circlePoint s u)-complexMap (kappa p c) (circlePoint s u)))).trans
    (he.trans (mul_le_mul_of_nonneg_left hb (by norm_num)))
  have hqv : (complexMap (kappa p c) (circlePoint s v)).re = crossing (kappa p c) s v := by
    rw [circle_image _ _ hv1]; simp
  have hqu : (complexMap (kappa p c) (circlePoint s u)).re = crossing (kappa p c) s u := by
    rw [circle_image _ _ hu1]; simp
  simp only [Complex.sub_re,hqv,hqu] at hRe
  linarith [(abs_le.mp hRe).1]

/-- The actual angular crossing is unique on the entire closed small-angle interval. -/
theorem actual_crossing_unique {p : ℕ} (hp : 17 ≤ p) {c s u v : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Radius)
    (hu : u ∈ Icc (-1/10 : ℝ) (1/10))
    (hv : v ∈ Icc (-1/10 : ℝ) (1/10))
    (huz : (normalizedReturn c p (circlePoint s u)).re = 0)
    (hvz : (normalizedReturn c p (circlePoint s v)).re = 0) : u = v := by
  rcases le_total u v with h | h
  · have hg := actual_crossing_growth hp hc hs hu hv h
    rw [huz,hvz] at hg
    linarith
  · have hg := actual_crossing_growth hp hc hs hv hu h
    rw [huz,hvz] at hg
    linarith

/-- Every actual upper-semicircle crossing lies strictly between the small
walls.  Uniform map error and global model ordering exclude additional roots. -/
theorem actual_full_crossing_small {p : ℕ} (hp : 17 ≤ p) {c s u : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Radius) (hu : u ∈ Icc (-1 : ℝ) 1)
    (hzero : (normalizedReturn c p (circlePoint s u)).re = 0) :
    u ∈ Ioo (-1/10 : ℝ) (1/10) := by
  have he := (Complex.abs_re_le_norm
    (normalizedReturn c p (circlePoint s u)-complexMap (kappa p c) (circlePoint s u))).trans
    (actual_close hp hc (circlePoint_full_disk hs hu))
  have hq : (complexMap (kappa p c) (circlePoint s u)).re = crossing (kappa p c) s u := by
    rw [circle_image _ _ hu]; simp
  simp only [Complex.sub_re,hzero,hq,zero_sub,abs_neg] at he
  obtain ⟨hl,hr⟩ := crossing_endpoint_margins hc.2.2.2.1 hs
  constructor
  · by_contra h
    have hle : u ≤ -1/10 := le_of_not_gt h
    have hg := crossing_global_growth hc.2.2.2.1 (parent_window hs) hu
      (show (-1/10 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hle
    linarith [(abs_le.mp he).1]
  · by_contra h
    have hle : (1/10 : ℝ) ≤ u := le_of_not_gt h
    have hg := crossing_global_growth hc.2.2.2.1 (parent_window hs)
      (show (1/10 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hu hle
    linarith [(abs_le.mp he).2]

/-- No other crossing is hidden elsewhere on the full upper semicircle. -/
theorem actual_full_crossing_unique {p : ℕ} (hp : 17 ≤ p) {c s u v : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Radius)
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1)
    (huz : (normalizedReturn c p (circlePoint s u)).re = 0)
    (hvz : (normalizedReturn c p (circlePoint s v)).re = 0) : u = v := by
  have hu' := actual_full_crossing_small hp hc hs hu huz
  have hv' := actual_full_crossing_small hp hc hs hv hvz
  exact actual_crossing_unique hp hc hs ⟨hu'.1.le,hu'.2.le⟩
    ⟨hv'.1.le,hv'.2.le⟩ huz hvz

/-- Every circle in the whole parent range has exactly one upper-semicircle
crossing; it is not merely a selected local root. -/
theorem existsUnique_actual_full_crossing {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Radius) :
    ∃! u : ℝ, u ∈ Icc (-1 : ℝ) 1 ∧
      (normalizedReturn c p (circlePoint s u)).re = 0 := by
  obtain ⟨u,hu,hz⟩ := actual_crossing_exists hp hc hs
  have hu1 : u ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hu.1,hu.2]
  refine ⟨u,⟨hu1,hz⟩,?_⟩
  intro v hv
  exact actual_full_crossing_unique hp hc hs hv.1 hu1 hv.2 hz

private theorem height_lower {κ s u : ℝ} (hk : κ ∈ parameterInterval)
    (hs : s ∈ Radius) (hu : u ∈ Icc (-1/10 : ℝ) (1/10)) :
    (1/10 : ℝ) ≤ height κ s u := by
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  have hu2 := sq_le_sq' (show -(1/10 : ℝ) ≤ u by linarith [hu.1]) hu.2
  have hnonneg : 0 ≤ 1-u^2 := by nlinarith
  have hroot := Real.sqrt_nonneg (1-u^2)
  have hsquare := Real.sq_sqrt hnonneg
  have hrl : (9/10 : ℝ) ≤ Real.sqrt (1-u^2) := by
    nlinarith only [hu2,hroot,hsquare]
  have hsu := mul_le_mul_of_nonneg_left hu.2 hs0
  have hal : (7/10 : ℝ) ≤ 3/4-s*u := by nlinarith only [hsu,hs.2]
  have ha0 : 0 ≤ 3/4-s*u := by linarith
  have hyl := mul_le_mul hs.1 hrl (by norm_num) hs0
  have hkl := mul_le_mul hk.1 hal (by norm_num) hk0
  have hlow := mul_le_mul hkl hyl (by norm_num) (mul_nonneg hk0 ha0)
  unfold height
  nlinarith only [hlow]

/-- The first actual image stays on the positive imaginary side. -/
theorem actual_first_image_positive {p : ℕ} (hp : 17 ≤ p) {c s u : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Radius)
    (hu : u ∈ Icc (-1/10 : ℝ) (1/10)) :
    0 < (normalizedReturn c p (circlePoint s u)).im := by
  have he := (Complex.abs_im_le_norm
    (normalizedReturn c p (circlePoint s u)-complexMap (kappa p c) (circlePoint s u))).trans
    (actual_close hp hc (circlePoint_disk hs hu))
  have hq : (complexMap (kappa p c) (circlePoint s u)).im = height (kappa p c) s u := by
    rw [circle_image _ _ (show u ∈ Icc (-1 : ℝ) 1 by
      constructor <;> linarith [hu.1,hu.2])]
    simp
  simp only [Complex.sub_im,hq] at he
  have hlo := height_lower hc.2.2.2.1 hs hu
  linarith [(abs_le.mp he).1]

/-- A coherent selection of the actual crossings on the entire parent radius interval. -/
structure Family (p : ℕ) (c : ℝ) where
  angle : Radius → ℝ
  lipschitz : LipschitzWith 100 angle
  angle_mem : ∀ s : Radius, angle s ∈ Ioo (-1/10 : ℝ) (1/10)
  crossing : ∀ s : Radius, (normalizedReturn c p (circlePoint s (angle s))).re = 0
  positive : ∀ s : Radius, 0 < (normalizedReturn c p (circlePoint s (angle s))).im

/-- Each actual signed tip has one Lipschitz angular selection on the full window. -/
theorem exists_family {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    Nonempty (Family p c) := by
  have hex (s : Radius) := actual_crossing_exists hp hc s.property
  choose a ha hz using hex
  have ham (s : Radius) : a s ∈ Icc (-1/10 : ℝ) (1/10) :=
    ⟨(ha s).1.le,(ha s).2.le⟩
  have hordered (s t : Radius) (hst : a s ≤ a t) :
      a t-a s ≤ 100*|(s : ℝ)-(t : ℝ)| := by
    have hg := actual_crossing_growth hp hc s.property (ham s) (ham t) hst
    rw [hz s] at hg
    have hb := QuadraticCrestDividedDifference.normalized_return_norm_sub_le c p
      (by omega) (actual_band hp hc) hc.2.1 (actual_small hc) hc.2.2.2.1
      (circlePoint_disk s.property (ham t)) (circlePoint_disk t.property (ham t))
    have ha1 : a t ∈ Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [(ha t).1,(ha t).2]
    rw [circlePoint_radius_distance (s : ℝ) (t : ℝ) ha1] at hb
    have hr := (Complex.abs_re_le_norm
      (normalizedReturn c p (circlePoint s (a t))-
       normalizedReturn c p (circlePoint t (a t)))).trans hb
    simp only [Complex.sub_re,hz t,sub_zero] at hr
    linarith [(abs_le.mp hr).2]
  have hbound (s t : Radius) : |a s-a t| ≤ 100*|(s : ℝ)-(t : ℝ)| := by
    rcases le_total (a s) (a t) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      linarith [hordered s t h]
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      have hb := hordered t s h
      rw [abs_sub_comm (t : ℝ) (s : ℝ)] at hb
      exact hb
  exact ⟨⟨a,LipschitzWith.of_dist_le_mul (fun s t => by
    simpa only [Real.dist_eq,Subtype.dist_eq,NNReal.coe_ofNat] using hbound s t),
    ha,hz,fun s => actual_first_image_positive hp hc s.property (ham s)⟩⟩

/-- Uniform angular error from the same limiting quadratic on the entire parent radius interval. -/
theorem actual_tip_angle_error {p : ℕ} (hp : 17 ≤ p) {c k₀ s u : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0)
    (hs : s ∈ Radius) (hu : u ∈ Icc (-1/10 : ℝ) (1/10))
    (hzero : (normalizedReturn c p (circlePoint s u)).re = 0) :
    |u-crossingCos k₀ s| ≤ 236460*scale p := by
  have hmap := ActualCrestLimit.actual_tip_limit_map_error hp hc hk₀ hroot
    (circlePoint_disk hs hu)
  have hreal := (Complex.abs_re_le_norm
    (normalizedReturn c p (circlePoint s u)-complexMap k₀ (circlePoint s u))).trans hmap
  have hu1 : u ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hu.1,hu.2]
  have hq : (complexMap k₀ (circlePoint s u)).re = crossing k₀ s u := by
    rw [circle_image k₀ s hu1]; simp
  simp only [Complex.sub_re,hzero,hq,zero_sub,abs_neg] at hreal
  have hspec := crossingCos_spec hk₀ hs
  have hv : crossingCos k₀ s ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hspec.1.1,hspec.1.2]
  rcases le_total u (crossingCos k₀ s) with hle | hle
  · have hg := crossing_global_growth hk₀ (parent_window hs) hu1 hv hle
    rw [hspec.2] at hg
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith only [hg,(abs_le.mp hreal).1]
  · have hg := crossing_global_growth hk₀ (parent_window hs) hv hu1 hle
    rw [hspec.2] at hg
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith only [hg,(abs_le.mp hreal).2]

/-- The actual crossing point approaches the radical model branch uniformly. -/
theorem actual_tip_point_error {p : ℕ} (hp : 17 ≤ p) {c k₀ s u : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0)
    (hs : s ∈ Radius) (hu : u ∈ Icc (-1/10 : ℝ) (1/10))
    (hzero : (normalizedReturn c p (circlePoint s u)).re = 0) :
    ‖circlePoint s u-radialPoint k₀ s‖ ≤ 60000*scale p := by
  rw [radialPoint_eq_circlePoint hk₀ hs]
  have hspec := (crossingCos_spec hk₀ hs).1
  have hv : crossingCos k₀ s ∈ Icc (-1/10 : ℝ) (1/10) := ⟨hspec.1.le,hspec.2.le⟩
  have hang := actual_tip_angle_error hp hc hk₀ hroot hs hu hzero
  have hcircle := circlePoint_angle_bound s hu hv
  rw [abs_of_pos (by linarith [hs.1] : 0 < s)] at hcircle
  have hm := mul_le_mul (show 2*s ≤ (1/4 : ℝ) by linarith [hs.2]) hang
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/4)
  nlinarith only [hcircle,hm,scale_pos p]

/-- The actual circle point chosen by one coherent angular family. -/
def Family.point {p : ℕ} {c : ℝ} (F : Family p c) (s : Radius) : ℂ :=
  circlePoint s (F.angle s)

theorem Family.point_lipschitz {p : ℕ} {c : ℝ} (F : Family p c) :
    LipschitzWith 26 F.point := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have ham (r : Radius) : F.angle r ∈ Icc (-1/10 : ℝ) (1/10) :=
    ⟨(F.angle_mem r).1.le,(F.angle_mem r).2.le⟩
  have ha1 (r : Radius) : F.angle r ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [(F.angle_mem r).1,(F.angle_mem r).2]
  have hangle : |F.angle s-F.angle t| ≤ 100*|(s : ℝ)-(t : ℝ)| := by
    simpa only [Real.dist_eq,Subtype.dist_eq,NNReal.coe_ofNat] using F.lipschitz.dist_le_mul s t
  have hcircle := circlePoint_angle_bound (t : ℝ) (ham s) (ham t)
  have ht0 : 0 ≤ (t : ℝ) := by linarith [t.property.1]
  have ht : 2*|(t : ℝ)| ≤ (1/4 : ℝ) := by
    rw [abs_of_nonneg ht0]
    linarith [t.property.2]
  have hangle2 := mul_le_mul ht hangle (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/4)
  have htri : ‖F.point s-F.point t‖ ≤
      ‖circlePoint s (F.angle s)-circlePoint t (F.angle s)‖+
        ‖circlePoint t (F.angle s)-circlePoint t (F.angle t)‖ := by
    simpa only [Family.point,dist_eq_norm] using
      dist_triangle (circlePoint s (F.angle s)) (circlePoint t (F.angle s))
        (circlePoint t (F.angle t))
  rw [circlePoint_radius_distance (s : ℝ) (t : ℝ) (ha1 s)] at htri
  rw [dist_eq_norm,NNReal.coe_ofNat,Subtype.dist_eq,Real.dist_eq]
  nlinarith only [htri,hcircle,hangle2,abs_nonneg ((s : ℝ)-(t : ℝ))]

theorem Family.point_continuous {p : ℕ} {c : ℝ} (F : Family p c) :
    Continuous F.point := F.point_lipschitz.continuous

theorem Family.point_radius {p : ℕ} {c : ℝ} (F : Family p c) (s : Radius) :
    ‖F.point s+(3/4 : ℂ)‖ = (s : ℝ) := by
  apply circle_radius (by linarith [s.property.1])
  constructor <;> linarith [(F.angle_mem s).1,(F.angle_mem s).2]

theorem Family.point_injective {p : ℕ} {c : ℝ} (F : Family p c) :
    Injective F.point := by
  intro s t h
  apply Subtype.ext
  have hn := congrArg (fun z : ℂ => ‖z+(3/4 : ℂ)‖) h
  simpa only [F.point_radius] using hn

theorem Family.point_disk {p : ℕ} {c : ℝ} (F : Family p c) (s : Radius) :
    ‖F.point s‖ ≤ 23/20 :=
  circlePoint_disk s.property ⟨(F.angle_mem s).1.le,(F.angle_mem s).2.le⟩

theorem Family.point_error {p : ℕ} (hp : 17 ≤ p) {c k₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0)
    (F : Family p c) (s : Radius) :
    ‖F.point s-radialPoint k₀ s‖ ≤ 60000*scale p :=
  actual_tip_point_error hp hc hk₀ hroot s.property
    ⟨(F.angle_mem s).1.le,(F.angle_mem s).2.le⟩ (F.crossing s)

theorem Family.second_real {p : ℕ} (hp : 0 < p) {c : ℝ}
    (F : Family p c) (s : Radius) :
    (((normalizedReturn c p)^[2]) (F.point s)).im = 0 := by
  have hid : normalizedReturn c p (F.point s) =
      ((normalizedReturn c p (F.point s)).im : ℂ)*Complex.I := by
    apply Complex.ext
    · simpa only [Family.point,Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,
        Complex.ofReal_im,Complex.I_im,zero_mul,sub_zero] using F.crossing s
    · simp
  change (normalizedReturn c p (normalizedReturn c p (F.point s))).im = 0
  rw [hid]
  exact normalizedReturn_imaginary c _ p hp

theorem Family.third_real {p : ℕ} (hp : 0 < p) {c : ℝ}
    (F : Family p c) (s : Radius) :
    (((normalizedReturn c p)^[3]) (F.point s)).im = 0 := by
  have hid : ((normalizedReturn c p)^[2]) (F.point s) =
      ((((normalizedReturn c p)^[2]) (F.point s)).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using F.second_real hp s
  change (normalizedReturn c p (((normalizedReturn c p)^[2]) (F.point s))).im = 0
  rw [hid]
  exact normalizedReturn_real c _ p

/-- The full circular parent is contained in the fixed disk of radius 7/8. -/
theorem Family.point_parent_disk {p : ℕ} {c : ℝ} (F : Family p c) (s : Radius) :
    ‖F.point s‖ ≤ 7/8 := by
  calc
    ‖F.point s‖ = ‖(F.point s+(3/4 : ℂ))-(3/4 : ℂ)‖ := by congr 1; ring
    _ ≤ ‖F.point s+(3/4 : ℂ)‖+‖(3/4 : ℂ)‖ := norm_sub_le _ _
    _ = (s : ℝ)+3/4 := by rw [F.point_radius]; norm_num
    _ ≤ 7/8 := by linarith [s.property.2]

def radiusProjection (s : ℝ) : Radius :=
  projIcc (1/16 : ℝ) (1/8) (by norm_num) s

theorem radiusProjection_eq {s : ℝ} (hs : s ∈ Radius) :
    radiusProjection s = ⟨s, hs⟩ := projIcc_of_mem (by norm_num) hs

def realAngle {p : ℕ} {c : ℝ} (F : Family p c) (s : ℝ) : ℝ :=
  F.angle (radiusProjection s)

def point {p : ℕ} {c : ℝ} (F : Family p c) (s : ℝ) : ℂ :=
  F.point (radiusProjection s)

def terminal {p : ℕ} {c : ℝ} (F : Family p c) (s : ℝ) : ℝ :=
  (((normalizedReturn c p)^[3]) (point F s)).re

theorem realAngle_continuous {p : ℕ} {c : ℝ} (F : Family p c) :
    Continuous (realAngle F) :=
  F.lipschitz.continuous.comp (continuous_projIcc (h := by norm_num))

theorem terminal_continuous {p : ℕ} {c : ℝ} (F : Family p c) :
    Continuous (terminal F) :=
  Complex.continuous_re.comp
    ((normalizedReturn_continuous c p).iterate 3 |>.comp
      (F.point_continuous.comp (continuous_projIcc (h := by norm_num))))

/-- The globally selected branch restricts to the archived endpoint window;
uniqueness excludes changing the actual crossing when changing its domain. -/
def Family.restrict {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c)
    (F : Family p c) : ActualCrestCrossingWindow.Family p c where
  angle := fun s => F.angle ⟨s,⟨s.property.1,by linarith [s.property.2]⟩⟩
  lipschitz := LipschitzWith.of_dist_le_mul (fun s t => by
    simpa only [Subtype.dist_eq, NNReal.coe_ofNat] using
      F.lipschitz.dist_le_mul
        ⟨s,⟨s.property.1,by linarith [s.property.2]⟩⟩
        ⟨t,⟨t.property.1,by linarith [t.property.2]⟩⟩)
  angle_mem := fun s =>
    ActualCrestCrossingWindow.actual_full_crossing_small hp hc s.property
      (by constructor <;> linarith [(F.angle_mem
        ⟨s,⟨s.property.1,by linarith [s.property.2]⟩⟩).1,
        (F.angle_mem ⟨s,⟨s.property.1,by linarith [s.property.2]⟩⟩).2])
      (F.crossing ⟨s,⟨s.property.1,by linarith [s.property.2]⟩⟩)
  crossing := fun s => F.crossing ⟨s,⟨s.property.1,by linarith [s.property.2]⟩⟩
  positive := fun s => F.positive ⟨s,⟨s.property.1,by linarith [s.property.2]⟩⟩

end
end GlobalCrestCrossing
