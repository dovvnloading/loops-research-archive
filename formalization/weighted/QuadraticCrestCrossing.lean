import LimitingCrestModelGates
import QuadraticCrestDividedDifference
import Mathlib.Tactic.FieldSimp

/-!
# A continuous crossing curve for the literal normalized return

Two-point control of the actual return gives quantitative angular
monotonicity.  The crossing on every selected radius is consequently
unique and varies continuously with that radius.
-/

namespace QuadraticCrestCrossing

open Set Function LimitingCrest
noncomputable section

private theorem small_angle_sqrt_bounds {u : ℝ}
    (hu : u ∈ Icc (-1/100 : ℝ) (1/100)) :
    (99/100 : ℝ) ≤ Real.sqrt (1-u^2) ∧ Real.sqrt (1-u^2) ≤ 1 := by
  have hu2 : u^2 ≤ (1/100 : ℝ)^2 := sq_le_sq' (show -(1/100 : ℝ) ≤ u by linarith [hu.1]) hu.2
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
    (hu : u ∈ Icc (-1/100 : ℝ) (1/100))
    (hv : v ∈ Icc (-1/100 : ℝ) (1/100)) :
    |Real.sqrt (1-u^2)-Real.sqrt (1-v^2)| ≤ |u-v| := by
  let U := Real.sqrt (1-u^2)
  let V := Real.sqrt (1-v^2)
  have hU := small_angle_sqrt_bounds hu
  have hV := small_angle_sqrt_bounds hv
  change 99/100 ≤ U ∧ U ≤ 1 at hU
  change 99/100 ≤ V ∧ V ≤ 1 at hV
  have hu2 : u^2 ≤ (1/100 : ℝ)^2 := sq_le_sq' (show -(1/100 : ℝ) ≤ u by linarith [hu.1]) hu.2
  have hv2 : v^2 ≤ (1/100 : ℝ)^2 := sq_le_sq' (show -(1/100 : ℝ) ≤ v by linarith [hv.1]) hv.2
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
bound on the fixed small angular interval. -/
theorem circlePoint_angle_bound (s : ℝ) {u v : ℝ}
    (hu : u ∈ Icc (-1/100 : ℝ) (1/100))
    (hv : v ∈ Icc (-1/100 : ℝ) (1/100)) :
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

/-- With angle fixed, the circle parametrization preserves radial distance. -/
theorem circlePoint_radius_distance (s t : ℝ) {u : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    ‖circlePoint s u-circlePoint t u‖ = |s-t| := by
  have hid : circlePoint s u-circlePoint t u =
      ((s-t : ℝ) : ℂ)*(circlePoint 1 u + (3/4 : ℂ)) := by
    unfold circlePoint
    push_cast
    ring
  rw [hid, norm_mul, circle_radius (by norm_num) hu, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- Every point of the chosen circle rectangle lies in the actual-return
approximation disk. -/
theorem circlePoint_disk {s u : ℝ}
    (hs : s ∈ Icc (63/1000 : ℝ) (33/500))
    (hu : u ∈ Icc (-1/100 : ℝ) (1/100)) :
    ‖circlePoint s u‖ ≤ 23/20 := by
  have hu1 : u ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hu.1, hu.2]
  have hr := circle_radius (show 0 ≤ s by linarith [hs.1]) hu1
  calc
    ‖circlePoint s u‖ = ‖(circlePoint s u + (3/4 : ℂ)) - (3/4 : ℂ)‖ := by congr 1; ring
    _ ≤ ‖circlePoint s u + (3/4 : ℂ)‖ + ‖(3/4 : ℂ)‖ := norm_sub_le _ _
    _ = s+3/4 := by rw [hr]; norm_num
    _ ≤ 23/20 := by linarith [hs.2]

theorem circlePoint_square_angle_bound {s u v : ℝ}
    (hs : s ∈ Icc (63/1000 : ℝ) (33/500))
    (hu : u ∈ Icc (-1/100 : ℝ) (1/100))
    (hv : v ∈ Icc (-1/100 : ℝ) (1/100)) :
    ‖(circlePoint s u)^2-(circlePoint s v)^2‖ ≤ |u-v| := by
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hd := circlePoint_angle_bound s hu hv
  rw [abs_of_nonneg hs0] at hd
  have hz := circlePoint_disk hs hu
  have hw := circlePoint_disk hs hv
  have hsum : ‖circlePoint s u+circlePoint s v‖ ≤ (23/10 : ℝ) :=
    (norm_add_le _ _).trans (by linarith)
  rw [sq_sub_sq, norm_mul, mul_comm]
  calc
    ‖circlePoint s u-circlePoint s v‖*‖circlePoint s u+circlePoint s v‖ ≤
        (2*s*|u-v|)*(23/10) := mul_le_mul hd hsum (norm_nonneg _) (by positivity)
    _ ≤ |u-v| := by nlinarith only [mul_le_mul_of_nonneg_right hs.2 (abs_nonneg (u-v)), abs_nonneg (u-v)]


/-- The actual normalized return is strictly ordered in the angular
variable, with a uniform quantitative lower bound. -/
theorem actual_crossing_growth (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < LimitingCrestQuadraticReturn.criticalValue c p)
    (hsmall : LimitingCrestQuadraticReturn.criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -LimitingCrestQuadraticReturn.quadraticCoefficient c (p-1)*
      LimitingCrestQuadraticReturn.criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000))
    {s u v : ℝ} (hs : s ∈ Icc (63/1000 : ℝ) (33/500))
    (hu : u ∈ Icc (-1/100 : ℝ) (1/100))
    (hv : v ∈ Icc (-1/100 : ℝ) (1/100)) (huv : u ≤ v) :
    (v-u)/20 ≤
      (LimitingCrestQuadraticReturn.normalizedReturn c p (circlePoint s v)).re -
      (LimitingCrestQuadraticReturn.normalizedReturn c p (circlePoint s u)).re := by
  let κ := -LimitingCrestQuadraticReturn.quadraticCoefficient c (p-1)*
    LimitingCrestQuadraticReturn.criticalValue c p
  let H := LimitingCrestQuadraticReturn.normalizedReturn c p
  have hu1 : u ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hu.1, hu.2]
  have hv1 : v ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hv.1, hv.2]
  have hs1 : s ∈ Icc (1/16 : ℝ) (1/8) := by constructor <;> linarith [hs.1, hs.2]
  have hg := crossing_global_growth hk hs1 hu1 hv1 huv
  have he := QuadraticCrestDividedDifference.normalized_remainder_difference c p hp hc hd
    hsmall (circlePoint_disk hs hv) (circlePoint_disk hs hu)
  change ‖(H (circlePoint s v)-complexMap κ (circlePoint s v)) -
    (H (circlePoint s u)-complexMap κ (circlePoint s u))‖ ≤ _ at he
  have hb := circlePoint_square_angle_bound hs hv hu
  rw [abs_of_nonneg (sub_nonneg.mpr huv)] at hb
  have hRe := (Complex.abs_re_le_norm
    ((H (circlePoint s v)-complexMap κ (circlePoint s v)) -
      (H (circlePoint s u)-complexMap κ (circlePoint s u)))).trans
    (he.trans (mul_le_mul_of_nonneg_left hb (by norm_num)))
  have hqv : (complexMap κ (circlePoint s v)).re = crossing κ s v := by
    rw [circle_image κ s hv1]; simp
  have hqu : (complexMap κ (circlePoint s u)).re = crossing κ s u := by
    rw [circle_image κ s hu1]; simp
  simp only [Complex.sub_re, hqv, hqu] at hRe
  have hlo := (abs_le.mp hRe).1
  change (v-u)/20 ≤ (H (circlePoint s v)).re-(H (circlePoint s u)).re
  change (v-u)/10 ≤ crossing κ s v-crossing κ s u at hg
  linarith

/-- There is exactly one actual crossing in the complete selected angular
interval, including its boundary. -/
theorem actual_crossing_unique (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < LimitingCrestQuadraticReturn.criticalValue c p)
    (hsmall : LimitingCrestQuadraticReturn.criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -LimitingCrestQuadraticReturn.quadraticCoefficient c (p-1)*
      LimitingCrestQuadraticReturn.criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000))
    {s u v : ℝ} (hs : s ∈ Icc (63/1000 : ℝ) (33/500))
    (hu : u ∈ Icc (-1/100 : ℝ) (1/100))
    (hv : v ∈ Icc (-1/100 : ℝ) (1/100))
    (huz : (LimitingCrestQuadraticReturn.normalizedReturn c p (circlePoint s u)).re = 0)
    (hvz : (LimitingCrestQuadraticReturn.normalizedReturn c p (circlePoint s v)).re = 0) :
    u = v := by
  rcases le_total u v with h | h
  · have hg := actual_crossing_growth c p hp hc hd hsmall hk hs hu hv h
    rw [huz, hvz] at hg
    linarith
  · have hg := actual_crossing_growth c p hp hc hd hsmall hk hs hv hu h
    rw [huz, hvz] at hg
    linarith

/-- The selected radial interval, with its ordinary induced metric. -/
abbrev CrestRadius := Icc (63/1000 : ℝ) (33/500)

private theorem selected_angle_estimate
    (H : ℂ → ℂ) (a : CrestRadius → ℝ)
    (ha : ∀ s : CrestRadius, a s ∈ Icc (-1/100 : ℝ) (1/100))
    (hz : ∀ s : CrestRadius, (H (circlePoint s (a s))).re = 0)
    (hg : ∀ (s : CrestRadius) {u v : ℝ},
      u ∈ Icc (-1/100 : ℝ) (1/100) → v ∈ Icc (-1/100 : ℝ) (1/100) →
      u ≤ v → (v-u)/20 ≤ (H (circlePoint s v)).re-(H (circlePoint s u)).re)
    (hlip : ∀ {z w : ℂ}, ‖z‖ ≤ 23/20 → ‖w‖ ≤ 23/20 →
      ‖H z-H w‖ ≤ 5*‖z-w‖) :
    ∀ s t : CrestRadius, |a s-a t| ≤ 100*|(s : ℝ)-(t : ℝ)| := by
  have hordered (s t : CrestRadius) (hst : a s ≤ a t) :
      a t-a s ≤ 100*|(s : ℝ)-(t : ℝ)| := by
    have hgrowth := hg s (ha s) (ha t) hst
    rw [hz s] at hgrowth
    have hbound := hlip (circlePoint_disk s.property (ha t))
      (circlePoint_disk t.property (ha t))
    have ha1 : a t ∈ Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [(ha t).1, (ha t).2]
    rw [circlePoint_radius_distance (s : ℝ) (t : ℝ) ha1] at hbound
    have hreal := (Complex.abs_re_le_norm
      (H (circlePoint s (a t))-H (circlePoint t (a t)))).trans hbound
    simp only [Complex.sub_re, hz t, sub_zero] at hreal
    linarith [(abs_le.mp hreal).2]
  intro s t
  rcases le_total (a s) (a t) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [hordered s t h]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hb := hordered t s h
    rw [abs_sub_comm (t : ℝ) (s : ℝ)] at hb
    exact hb

/-- The unique actual crossing angle is a globally Lipschitz function
of radius throughout the selected interval. -/
theorem exists_lipschitz_actual_angle (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < LimitingCrestQuadraticReturn.criticalValue c p)
    (hsmall : LimitingCrestQuadraticReturn.criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -LimitingCrestQuadraticReturn.quadraticCoefficient c (p-1)*
      LimitingCrestQuadraticReturn.criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000)) :
    ∃ a : CrestRadius → ℝ, LipschitzWith 100 a ∧
      ∀ s : CrestRadius, a s ∈ Ioo (-1/100 : ℝ) (1/100) ∧
        (LimitingCrestQuadraticReturn.normalizedReturn c p (circlePoint s (a s))).re = 0 := by
  have hex (s : CrestRadius) : ∃ u : ℝ,
      u ∈ Ioo (-1/100 : ℝ) (1/100) ∧
      (LimitingCrestQuadraticReturn.normalizedReturn c p (circlePoint s u)).re = 0 := by
    obtain ⟨u, hu, _, hz, _⟩ := LimitingCrestQuadraticReturn.actual_quadratic_return_corridor
      c p hp hc hd hsmall hk s.property
    exact ⟨u, hu, hz⟩
  choose a ha using hex
  have hang := selected_angle_estimate (LimitingCrestQuadraticReturn.normalizedReturn c p) a
    (fun s => ⟨(ha s).1.1.le, (ha s).1.2.le⟩) (fun s => (ha s).2)
    (fun s {u v} hu hv huv => actual_crossing_growth c p hp hc hd hsmall hk s.property hu hv huv)
    (fun {z w} hz hw => QuadraticCrestDividedDifference.normalized_return_norm_sub_le
      c p hp hc hd hsmall hk hz hw)
  refine ⟨a, LipschitzWith.of_dist_le_mul (fun s t => ?_), ha⟩
  simpa only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_ofNat] using hang s t


/-- A single injective Lipschitz curve selects the actual return crossing
on every radius.  Its second and third images and the moving terminal
cut inequalities hold simultaneously along the whole curve. -/
theorem exists_lipschitz_actual_curve (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < LimitingCrestQuadraticReturn.criticalValue c p)
    (hsmall : LimitingCrestQuadraticReturn.criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -LimitingCrestQuadraticReturn.quadraticCoefficient c (p-1)*
      LimitingCrestQuadraticReturn.criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000)) :
    ∃ γ : CrestRadius → ℂ, LipschitzWith 15 γ ∧ Injective γ ∧ Continuous γ ∧
      ∀ s : CrestRadius, ‖γ s+(3/4 : ℂ)‖ = (s : ℝ) ∧
        (LimitingCrestQuadraticReturn.normalizedReturn c p (γ s)).re = 0 ∧
        0 < (LimitingCrestQuadraticReturn.normalizedReturn c p (γ s)).im ∧
        (((LimitingCrestQuadraticReturn.normalizedReturn c p)^[2]) (γ s)).im = 0 ∧
        (((LimitingCrestQuadraticReturn.normalizedReturn c p)^[3]) (γ s)).im = 0 ∧
        (-999/1000 : ℝ) < (((LimitingCrestQuadraticReturn.normalizedReturn c p)^[3]) (γ s)).re ∧
        (((LimitingCrestQuadraticReturn.normalizedReturn c p)^[3]) (γ s)).re < -977/1000 ∧
        (((LimitingCrestQuadraticReturn.normalizedReturn c p)^[3]) (γ s)).re <
          -(((LimitingCrestQuadraticReturn.normalizedReturn c p)^[4]) 0).re := by
  obtain ⟨a, hLip, ha⟩ := exists_lipschitz_actual_angle c p hp hc hd hsmall hk
  let γ : CrestRadius → ℂ := fun s => circlePoint s (a s)
  have ha0 (s : CrestRadius) : a s ∈ Icc (-1/100 : ℝ) (1/100) :=
    ⟨(ha s).1.1.le, (ha s).1.2.le⟩
  have ha1 (s : CrestRadius) : a s ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [(ha s).1.1, (ha s).1.2]
  have hrad (s : CrestRadius) : ‖γ s+(3/4 : ℂ)‖ = (s : ℝ) :=
    circle_radius (by linarith [s.property.1]) (ha1 s)
  have hγ : LipschitzWith 15 γ := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have hangle : |a s-a t| ≤ 100*|(s : ℝ)-(t : ℝ)| := by
      simpa only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_ofNat] using hLip.dist_le_mul s t
    have hcircle := circlePoint_angle_bound (t : ℝ) (ha0 s) (ha0 t)
    have ht0 : 0 ≤ (t : ℝ) := by linarith [t.property.1]
    have ht : 2*|(t : ℝ)| ≤ (33/250 : ℝ) := by
      rw [abs_of_nonneg ht0]
      linarith [t.property.2]
    have hangle2 := mul_le_mul ht hangle (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 33/250)
    have htri : ‖γ s-γ t‖ ≤
        ‖circlePoint s (a s)-circlePoint t (a s)‖ +
          ‖circlePoint t (a s)-circlePoint t (a t)‖ := by
      simpa only [γ, dist_eq_norm] using
        dist_triangle (circlePoint s (a s)) (circlePoint t (a s)) (circlePoint t (a t))
    rw [circlePoint_radius_distance (s : ℝ) (t : ℝ) (ha1 s)] at htri
    rw [dist_eq_norm, NNReal.coe_ofNat, Subtype.dist_eq, Real.dist_eq]
    nlinarith only [htri, hcircle, hangle2, abs_nonneg ((s : ℝ)-(t : ℝ))]
  have hinj : Injective γ := by
    intro s t h
    apply Subtype.ext
    have hr := congrArg (fun z : ℂ => ‖z+(3/4 : ℂ)‖) h
    simpa only [hrad] using hr
  refine ⟨γ, hγ, hinj, hγ.continuous, ?_⟩
  intro s
  obtain ⟨u, hu, hr, hz, hpos, htwo, hthree, hlo, hhi, hcut⟩ :=
    LimitingCrestQuadraticReturn.actual_quadratic_return_corridor c p hp hc hd hsmall hk s.property
  have hueq : u = a s := actual_crossing_unique c p hp hc hd hsmall hk s.property
    ⟨hu.1.le, hu.2.le⟩ (ha0 s) hz (ha s).2
  subst u
  exact ⟨hr, hz, hpos, htwo, hthree, hlo, hhi, hcut⟩


open LimitingCrestQuadraticReturn

/-- The entire upper semicircle, including both real endpoints, remains
inside the disk on which the complete return error is controlled. -/
theorem circlePoint_full_disk {s u : ℝ}
    (hs : s ∈ Icc (63/1000 : ℝ) (33/500))
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    ‖circlePoint s u‖ ≤ 23/20 := by
  have hr := circle_radius (show 0 ≤ s by linarith [hs.1]) hu
  calc
    ‖circlePoint s u‖ = ‖(circlePoint s u + (3/4 : ℂ)) - (3/4 : ℂ)‖ := by congr 1; ring
    _ ≤ ‖circlePoint s u + (3/4 : ℂ)‖ + ‖(3/4 : ℂ)‖ := norm_sub_le _ _
    _ = s+3/4 := by rw [hr]; norm_num
    _ ≤ 23/20 := by linarith [hs.2]

private theorem real_critical_orbit_bound (c : ℝ)
    (hc : c ∈ Icc (-2 : ℝ) 0) (j : ℕ) : |criticalValue c j| ≤ 2 := by
  have hmap : MapsTo (fun t : ℝ => t^2+c) (Icc c (-c)) (Icc c (-c)) := by
    intro t ht
    have hsq : t^2 ≤ (-c)^2 :=
      sq_le_sq' (show -(-c) ≤ t by linarith [ht.1]) ht.2
    have hprod : c*(c+2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc.2 (by linarith [hc.1])
    constructor
    · nlinarith only [sq_nonneg t]
    · nlinarith only [hsq, hprod]
  have hzero : (0 : ℝ) ∈ Icc c (-c) := by constructor <;> linarith [hc.2]
  have hcrit : criticalValue c j ∈ Icc c (-c) := hmap.iterate j hzero
  rw [abs_le]
  constructor <;> linarith [hc.1, hcrit.1, hcrit.2]

/-- Every actual crossing on the entire upper semicircle belongs to the
small angular window.  No secondary crossing is hidden near either end. -/
theorem actual_crossing_localization (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0) (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1)*criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000))
    {s u : ℝ} (hs : s ∈ Icc (63/1000 : ℝ) (33/500))
    (hu : u ∈ Icc (-1 : ℝ) 1)
    (hz : (normalizedReturn c p (circlePoint s u)).re = 0) :
    u ∈ Ioo (-1/100 : ℝ) (1/100) := by
  let κ := -quadraticCoefficient c (p-1)*criticalValue c p
  have he := normalized_return_error c p hp
    (fun j _ => real_critical_orbit_bound c hc j) hd hsmall (circlePoint s u)
    (circlePoint_full_disk hs hu)
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hp
  norm_num at hpow
  have herr : (24 : ℝ)/4^p < 1/2000 := by
    apply (div_lt_iff₀ (show (0 : ℝ) < 4^p by positivity)).mpr
    linarith
  have hmodel : (complexMap κ (circlePoint s u)).re = crossing κ s u := by
    rw [circle_image κ s hu]
    simp
  have hreal := (Complex.abs_re_le_norm
    (normalizedReturn c p (circlePoint s u)-complexMap κ (circlePoint s u))).trans_lt
    (he.trans_lt herr)
  have hsmallroot : |crossing κ s u| < (1/2000 : ℝ) := by
    simpa only [Complex.sub_re, hz, hmodel, zero_sub, abs_neg] using hreal
  have hs1 : s ∈ Icc (1/16 : ℝ) (1/8) := by constructor <;> linarith [hs.1, hs.2]
  have hmono := (crossing_global_strictMono hk hs1).monotoneOn
  have hwalls := crossing_endpoint_margins hk hs
  change crossing κ s (-1/100) < -1/2000 ∧ 1/2000 < crossing κ s (1/100) at hwalls
  constructor
  · by_contra h
    have hle : u ≤ (-1/100 : ℝ) := by linarith
    have hcmp := hmono hu (show (-1/100 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hle
    change crossing κ s u ≤ crossing κ s (-1/100) at hcmp
    linarith [(abs_lt.mp hsmallroot).1, hwalls.1]
  · by_contra h
    have hle : (1/100 : ℝ) ≤ u := by linarith
    have hcmp := hmono (show (1/100 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hu hle
    change crossing κ s (1/100) ≤ crossing κ s u at hcmp
    linarith [(abs_lt.mp hsmallroot).2, hwalls.2]

/-- The actual crossing is unique on the whole upper semicircle. -/
theorem actual_crossing_global_unique (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0) (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1)*criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000))
    {s u v : ℝ} (hs : s ∈ Icc (63/1000 : ℝ) (33/500))
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1)
    (huz : (normalizedReturn c p (circlePoint s u)).re = 0)
    (hvz : (normalizedReturn c p (circlePoint s v)).re = 0) : u = v := by
  have hul := actual_crossing_localization c p hp hc hd hsmall hk hs hu huz
  have hvl := actual_crossing_localization c p hp hc hd hsmall hk hs hv hvz
  exact actual_crossing_unique c p hp hc hd hsmall hk hs
    ⟨hul.1.le, hul.2.le⟩ ⟨hvl.1.le, hvl.2.le⟩ huz hvz

/-- Every selected radius has exactly one crossing on its complete upper
semicircle, and the Lipschitz curve constructed above selects that point. -/
theorem existsUnique_actual_full_crossing (c : ℝ) (p : ℕ) (hp : 13 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) 0) (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1)*criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000))
    {s : ℝ} (hs : s ∈ Icc (63/1000 : ℝ) (33/500)) :
    ∃! u : ℝ, u ∈ Icc (-1 : ℝ) 1 ∧
      (normalizedReturn c p (circlePoint s u)).re = 0 := by
  obtain ⟨u, hu, _, hz, _⟩ := actual_quadratic_return_corridor c p hp hc hd hsmall hk hs
  have hu1 : u ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hu.1, hu.2]
  refine ⟨u, ⟨hu1, hz⟩, ?_⟩
  intro v hv
  exact actual_crossing_global_unique c p hp hc hd hsmall hk hs hv.1 hu1 hv.2 hz

end
end QuadraticCrestCrossing
