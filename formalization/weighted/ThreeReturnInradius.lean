import UniformThreeReturnRenormalization

/-!
# A uniform disk inside the actual three-return source

The fixed central component contains the closed normalized disk of radius
1/40.  This is an inner nondegeneration estimate for the actual polynomial
domain, complementary to its previously proved outer containment.  The
small periods are rechecked by full nonlinear integer disk certificates;
the infinite tail uses the actual return approximation and its narrow
coefficient interval.  Scaling gives the literal physical inner disk.
-/

namespace ThreeReturnInradius

open Set Function Metric Topology
open LoopsFormal.Period27 LoopsFormal.DepthThree
open LoopsDepthThreeReal LoopsDepthThreeRemainder
open LimitingCrest LimitingCrestPerturbation LimitingCrestQuadraticReturn
open FiniteThreeReturnCertificates FiniteThreeReturnCollars
open NearTwoShooting NearTwoTip ThreeReturnEstimates
open ThreeReturnDomain ThreeReturnCollar UniformThreeReturn

noncomputable section

private def certificateRadius (S : Int) (p : Nat) (C : Bounds) : Ratio :=
  ⟨(collarD S p C).hi, 40*S⟩

private def certificateDeviation (S : Int) (p : Nat) (C : Bounds) : Int :=
  let rows := collarRows S p C
  let r := certificateRadius S p C
  upperProduct S (absHi (rowAt rows (3*p)).quadratic) (radiusSquaredUpper S r) +
    errorAt (errors S rows r (3*p)) (3*p)

private def InradiusCertificate (S : Int) (p : Nat) (C : Bounds) : Prop :=
  25 * (absHi (rowAt (collarRows S p C) (3*p)).orbit +
    certificateDeviation S p C) < 4 * (collarD S p C).lo

private instance (S : Int) (p : Nat) (C : Bounds) :
    Decidable (InradiusCertificate S p C) := by
  unfold InradiusCertificate
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
private theorem finite_inradius_certificates :
    ((List.range 14).all fun i => decide
      (InradiusCertificate finiteScale (i+3) (parameterBox (i+3)))) = true := by
  decide +kernel

private theorem polynomial_eq_criticalValue (c : ℝ) (n : ℕ) :
    LoopsRealPeriod27.polynomial n c = criticalValue c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [polynomial_succ, ih]
    simp only [criticalValue, iterate_succ_apply']

private theorem orbit_eq_iterate (c : ℝ) (n : ℕ) (z : ℂ) :
    QuadraticEscape.orbit (c : ℂ) n z = ((quadraticMap c)^[n]) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [QuadraticEscape.orbit, ih, iterate_succ_apply']
    rfl

private theorem finite_disk_bound_of_certificate {S : Int} {p : ℕ} {C : Bounds}
    (hG : GeometryCertificate S p C) (hI : InradiusCertificate S p C)
    {c : ℝ} (hc : RealEnclosed S C c) {z : ℂ} (hz : ‖z‖ ≤ 1/40) :
    ‖threeReturn c p z‖ < 4/25 := by
  have hS : 0 < S := hG.1
  have hp : 0 < p := hG.2.1
  have hD : 0 < (collarD S p C).lo := hG.2.2.1
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hdlo : (0 : ℝ) < (collarD S p C).lo := by exact_mod_cast hD
  have hdrow := (trace_enclosed hS hc (3*p) p (by omega)).1
  have hden : RealEnclosed S (collarD S p C) (criticalValue c p) := by
    simpa only [polynomial_eq_criticalValue, collarD, collarRows] using hdrow
  have hdbox := (realEnclosed_iff hS _ _).mp hden
  have hd : 0 < criticalValue c p :=
    (div_pos hdlo hs).trans_le hdbox.1
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  let r := certificateRadius S p C
  let w : ℂ := (criticalValue c p : ℂ) * z
  have hr : r.den ≠ 0 := by
    change 40*S ≠ 0
    exact mul_ne_zero (by norm_num) hS.ne'
  have hw : ‖w‖ ≤ (r.num : ℝ)/(r.den : ℝ) := by
    dsimp only [w]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    calc
      criticalValue c p * ‖z‖ ≤ criticalValue c p * (1/40) :=
        mul_le_mul_of_nonneg_left hz hd.le
      _ ≤ ((collarD S p C).hi : ℝ)/(S : ℝ)*(1/40) :=
        mul_le_mul_of_nonneg_right hdbox.2 (by norm_num)
      _ = _ := by simp only [r, certificateRadius, Int.cast_mul, Int.cast_ofNat]; ring
  have hrow := trace_enclosed hS hc (3*p) (3*p) le_rfl
  have hx := abs_enclosed hS hrow.1
  have ha := abs_enclosed hS hrow.2.2
  have hA : 0 ≤ (absHi (rowAt (collarRows S p C) (3*p)).quadratic : ℝ)/(S : ℝ) :=
    (abs_nonneg _).trans ha
  have hr2 := radius_squared_sound hS r hr
  have hproduct := upperProduct_sound hS
    (absHi (rowAt (collarRows S p C) (3*p)).quadratic) (radiusSquaredUpper S r)
  have hlead : ‖(LoopsDepthThreeReal.quadraticCoefficient (3*p) c : ℂ)*w^2‖ ≤
      (upperProduct S (absHi (rowAt (collarRows S p C) (3*p)).quadratic)
        (radiusSquaredUpper S r) : ℝ)/(S : ℝ) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    apply le_trans _ hproduct
    exact (mul_le_mul_of_nonneg_right ha (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left
        ((pow_le_pow_left₀ (norm_nonneg _) hw 2).trans hr2) hA)
  have he := errors_sound hS hc (3*p) (3*p) le_rfl r hr w hw
    (3*p) (by omega) le_rfl
  have hid : QuadraticEscape.orbit (c : ℂ) (3*p) w =
      (LoopsRealPeriod27.polynomial (3*p) c : ℂ) +
        (LoopsDepthThreeReal.quadraticCoefficient (3*p) c : ℂ)*w^2 +
        remainder c (3*p) w := by
    rw [remainder]
    ring
  have hwhole : ‖QuadraticEscape.orbit (c : ℂ) (3*p) w‖ ≤
      ((absHi (rowAt (collarRows S p C) (3*p)).orbit +
        certificateDeviation S p C : Int) : ℝ)/(S : ℝ) := by
    have ht := norm_add_le
      ((LoopsRealPeriod27.polynomial (3*p) c : ℂ) +
        (LoopsDepthThreeReal.quadraticCoefficient (3*p) c : ℂ)*w^2)
      (remainder c (3*p) w)
    have ht' := norm_add_le (LoopsRealPeriod27.polynomial (3*p) c : ℂ)
      ((LoopsDepthThreeReal.quadraticCoefficient (3*p) c : ℂ)*w^2)
    rw [← hid] at ht
    simp only [Complex.norm_real, Real.norm_eq_abs] at ht'
    simp only [certificateDeviation, Int.cast_add, add_div]
    change ‖QuadraticEscape.orbit (c : ℂ) (3*p) w‖ ≤ _
    dsimp only [r] at hlead he
    linarith only [ht, ht', hx, hlead, he]
  have hscale : threeReturn c p z =
      QuadraticEscape.orbit (c : ℂ) (3*p) w / (criticalValue c p : ℂ) := by
    rw [eq_div_iff hdC, mul_comm]
    exact (normalized_iterate_scale c p hd.ne' 3 z).trans
      (orbit_eq_iterate c (3*p) w).symm
  have hnorm : ‖threeReturn c p z‖ ≤
      ((absHi (rowAt (collarRows S p C) (3*p)).orbit +
        certificateDeviation S p C : Int) : ℝ)/((collarD S p C).lo : ℝ) := by
    rw [hscale, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    calc
      _ ≤ (((absHi (rowAt (collarRows S p C) (3*p)).orbit +
            certificateDeviation S p C : Int) : ℝ)/(S : ℝ)) / criticalValue c p :=
        div_le_div_of_nonneg_right hwhole hd.le
      _ ≤ (((absHi (rowAt (collarRows S p C) (3*p)).orbit +
            certificateDeviation S p C : Int) : ℝ)/(S : ℝ)) /
          (((collarD S p C).lo : ℝ)/(S : ℝ)) :=
        div_le_div_of_nonneg_left ((norm_nonneg _).trans hwhole)
          (div_pos hdlo hs) hdbox.1
      _ = _ := by field_simp
  apply hnorm.trans_lt
  apply (div_lt_iff₀ hdlo).mpr
  have hcast : 25 * (((absHi (rowAt (collarRows S p C) (3*p)).orbit +
      certificateDeviation S p C : Int) : ℝ)) < 4 * ((collarD S p C).lo : ℝ) := by
    exact_mod_cast hI
  linarith only [hcast]

/-- All finite selected parameters map the entire closed disk of radius
1/40 strictly inside radius 4/25 under the actual normalized three-return.
The full nonlinear remainder is checked, not merely its quadratic part. -/
theorem finite_three_return_inner_bound {p : ℕ} (hp3 : 3 ≤ p) (hp16 : p ≤ 16)
    {c : ℝ} (hc : CertifiedParameter p c) {z : ℂ} (hz : ‖z‖ ≤ 1/40) :
    ‖threeReturn c p z‖ < 4/25 := by
  have hmem : p-3 ∈ List.range 14 := List.mem_range.mpr (by omega)
  have h := List.all_eq_true.mp finite_inradius_certificates (p-3) hmem
  have he : p-3+3 = p := by omega
  have hi : InradiusCertificate finiteScale p (parameterBox p) := by
    simpa only [he, decide_eq_true_eq] using h
  exact finite_disk_bound_of_certificate (finite_certificates hp3 hp16).2 hi hc.1 hz

private theorem model_third_critical_bound {k : ℝ}
    (hk : k ∈ LoopsLimitingCrestParameter.parameterInterval) :
    ‖((complexMap k)^[3]) 0‖ ≤ 1/8 := by
  have hklo : (179/100 : ℝ) ≤ k := by
    have h := hk.1
    change 17903/10000 ≤ k at h
    linarith only [h]
  have hkhi : k ≤ (1791/1000 : ℝ) := by
    have h := hk.2
    change k ≤ 17904/10000 at h
    linarith only [h]
  have hk0 : 0 ≤ k := by linarith only [hklo]
  have hkm : 0 ≤ k-1 := by linarith only [hklo]
  have hlo := mul_le_mul hklo
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 79/100)
      (show (79/100 : ℝ) ≤ k-1 by linarith only [hklo]) 2)
    (by norm_num : (0 : ℝ) ≤ (79/100)^2) hk0
  have hhi := mul_le_mul hkhi
    (pow_le_pow_left₀ hkm
      (show k-1 ≤ (791/1000 : ℝ) by linarith only [hkhi]) 2)
    (sq_nonneg (k-1)) (by norm_num : (0 : ℝ) ≤ 1791/1000)
  have he : ((complexMap k)^[3]) 0 = ((1-k*(k-1)^2 : ℝ) : ℂ) := by
    norm_num [iterate_succ_apply', complexMap]
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
  norm_num at hlo hhi
  constructor <;> linarith only [hlo, hhi]

private theorem approximate_quadratic_difference (F : ℂ → ℂ)
    {k ε : ℝ} (hk0 : 0 ≤ k) (hk2 : k ≤ 2)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 → ‖F w-complexMap k w‖ ≤ ε)
    {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    ‖F z-F w‖ ≤ 2*ε+5*‖z-w‖ := by
  have h1 := hclose z hz
  have h2 := hclose w hw
  have hq := quadratic_disk_lipschitz k hk0 hk2 z w hz hw
  have ht := norm_sub_le (F z-complexMap k z) (F w-complexMap k w)
  have hs : F z-F w = (F z-complexMap k z)-(F w-complexMap k w) +
      (complexMap k z-complexMap k w) := by ring
  rw [hs]
  exact (norm_add_le _ _).trans (by dsimp only [complexMap] at *; linarith)

/-- The same explicit inner disk works throughout the analytic tail.
The proof compares complete actual iterates and uses their already proved
phase confinement on the full outer disk. -/
theorem actual_three_return_inner_bound {p : ℕ} (hp : 17 ≤ p)
    {c : ℝ} (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 1/40) :
    ‖threeReturn c p z‖ < 4/25 := by
  let k := kappa p c
  let ε : ℝ := 24/(4 : ℝ)^p
  let F := normalizedReturn c p
  have hk := hc.2.2.2.1
  have hk0 : 0 ≤ k := by
    have h := hk.1
    change 17903/10000 ≤ k at h
    linarith only [h]
  have hk18 : k ≤ 9/5 := by
    have h := hk.2
    change k ≤ 17904/10000 at h
    linarith only [h]
  have hk2 : k ≤ 2 := by linarith only [hk18]
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  have hclose : ∀ w : ℂ, ‖w‖ ≤ 23/20 → ‖F w-complexMap k w‖ ≤ ε :=
    normalized_return_error c p (by omega) hc.2.2.2.2.2.2 hc.2.1 hsmall
  have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hεmax : ε ≤ 1/500000 := by
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
      (show 13 ≤ p by omega)
    norm_num at hpow
    dsimp only [ε]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4^p)).mpr
    linarith only [hpow]
  have hcritical := iterate_perturbation_up_to_four F (complexMap k) 0 ε
    hε0 hεmax hclose (quadratic_disk_lipschitz k hk0 hk2)
    (fun n _ => quadratic_critical_orbit_unit k hk0 hk2 n) 3 (by omega)
  have hmodel := model_third_critical_bound hk
  have h0 : ‖(F^[3]) 0‖ ≤ 1/8+31*ε := by
    have ht := norm_le_norm_sub_add ((F^[3]) 0) (((complexMap k)^[3]) 0)
    have he := hcritical.1
    norm_num only [errorCoefficient, mul_zero, add_zero, one_mul] at he
    linarith only [ht, he, hmodel]
  have hzouter : ‖z‖ ≤ outerRadius := hz.trans (by norm_num [outerRadius])
  have hzdisk : ‖z‖ ≤ 23/20 := hz.trans (by norm_num)
  have hzphase := (actual_phase_bounds hp hc hzouter).2.2.2
  have h0phase := (actual_phase_bounds hp hc
    (show ‖(0 : ℂ)‖ ≤ outerRadius by norm_num [outerRadius])).2.2.2
  have hfirst : ‖F z-F 0‖ ≤ 2*ε+(9/5 : ℝ)*(1/40)^2 := by
    have hq : ‖complexMap k z-complexMap k 0‖ ≤ (9/5 : ℝ)*(1/40)^2 := by
      have he : complexMap k z-complexMap k 0 = -(k : ℂ)*z^2 := by
        simp only [complexMap, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, mul_zero, sub_zero]
        ring
      rw [he, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hk0, norm_pow]
      exact mul_le_mul hk18 (pow_le_pow_left₀ (norm_nonneg _) hz 2)
        (sq_nonneg _) (by norm_num)
    have ht1 : ‖F z-F 0‖ ≤ ‖F z-complexMap k z‖+
        ‖complexMap k z-complexMap k 0‖+‖F 0-complexMap k 0‖ := by
      have ht := norm_sub_le (F z-complexMap k z) (F 0-complexMap k 0)
      have he : F z-F 0 = (F z-complexMap k z)-(F 0-complexMap k 0)+
          (complexMap k z-complexMap k 0) := by ring
      rw [he]
      have ht' := norm_add_le ((F z-complexMap k z)-(F 0-complexMap k 0))
        (complexMap k z-complexMap k 0)
      linarith only [ht, ht']
    exact ht1.trans (by linarith only [hclose z hzdisk,
      hclose 0 (by norm_num), hq])
  have hsecond : ‖(F^[2]) z-(F^[2]) 0‖ ≤
      12*ε+5*((9/5 : ℝ)*(1/40)^2) := by
    have h := approximate_quadratic_difference F hk0 hk2 hclose
      (hzphase 1 (by omega)).le (h0phase 1 (by omega)).le
    change ‖F (F z)-F (F 0)‖ ≤ 2*ε+5*‖F z-F 0‖ at h
    change ‖F (F z)-F (F 0)‖ ≤ _
    linarith only [h, hfirst]
  have hthird : ‖(F^[3]) z-(F^[3]) 0‖ ≤
      62*ε+25*((9/5 : ℝ)*(1/40)^2) := by
    have h := approximate_quadratic_difference F hk0 hk2 hclose
      (hzphase 2 (by omega)).le (h0phase 2 (by omega)).le
    change ‖F ((F^[2]) z)-F ((F^[2]) 0)‖ ≤
      2*ε+5*‖(F^[2]) z-(F^[2]) 0‖ at h
    rw [iterate_succ_apply', iterate_succ_apply']
    linarith only [h, hsecond]
  have ht := norm_le_norm_sub_add ((F^[3]) z) ((F^[3]) 0)
  change ‖(F^[3]) z‖ < 4/25
  linarith only [ht, hthird, h0, hεmax]

/-- All selected periods have the same strict whole-disk image bound.
The target radius 1/6 exceeds this bound by exactly 1/150. -/
theorem selected_three_return_inner_bound {p : ℕ} (hp : 3 ≤ p)
    {c : ℝ} (hc : SelectedParameter p c) {z : ℂ} (hz : ‖z‖ ≤ 1/40) :
    ‖threeReturn c p z‖ < 4/25 := by
  rcases hc with ⟨hp16, hc⟩ | ⟨hp17, hc⟩
  · exact finite_three_return_inner_bound hp hp16 hc hz
  · exact actual_three_return_inner_bound hp17 hc hz

/-- The whole closed central disk belongs to the actual selected source
component, because it is connected, contains zero, and stays in the full
polynomial pullback.  No supplied source-domain hypothesis is used. -/
theorem selected_closedBall_subset_source {p : ℕ} (hp : 3 ≤ p)
    {c : ℝ} (hc : SelectedParameter p c) :
    closedBall (0 : ℂ) (1/40) ⊆ source c p := by
  apply (convex_closedBall (0 : ℂ) (1/40)).isPreconnected.subset_connectedComponentIn
  · norm_num
  · intro z hz
    have h := selected_three_return_inner_bound hp hc
      (show ‖z‖ ≤ 1/40 by simpa using hz)
    change threeReturn c p z ∈ ball 0 (1/6)
    rw [mem_ball_zero_iff]
    linarith only [h]

/-- In physical coordinates the same theorem contains a closed disk of
radius d/40, where d is the actual positive critical p-return value. -/
theorem selected_physical_closedBall_subset {p : ℕ} (hp : 3 ≤ p)
    {c : ℝ} (hc : SelectedParameter p c) :
    closedBall (0 : ℂ) (criticalValue c p / 40) ⊆ physicalSource c p := by
  have hd := (selected_critical_data hp hc).1
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  intro z hz
  have hzn : ‖z‖ ≤ criticalValue c p / 40 := by simpa using hz
  refine ⟨z/(criticalValue c p : ℂ), selected_closedBall_subset_source hp hc ?_, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    linarith only [hzn]
  · change (criticalValue c p : ℂ)*(z/(criticalValue c p : ℂ)) = z
    field_simp [hdC]

/-- The full physical inner disk maps a distance greater than d/150
inside the target circle under the literal physical 3p iterate. -/
theorem selected_physical_inner_image_margin {p : ℕ} (hp : 3 ≤ p)
    {c : ℝ} (hc : SelectedParameter p c) {z : ℂ}
    (hz : ‖z‖ ≤ criticalValue c p/40) :
    ‖((quadraticMap c)^[3*p]) z‖ + criticalValue c p/150 <
      criticalValue c p/6 := by
  have hd := (selected_critical_data hp hc).1
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  let w : ℂ := z/(criticalValue c p : ℂ)
  have hw : ‖w‖ ≤ 1/40 := by
    dsimp only [w]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    linarith only [hz]
  have hbound := selected_three_return_inner_bound hp hc hw
  have he : (criticalValue c p : ℂ)*w = z := by
    dsimp only [w]
    field_simp [hdC]
  have hscale := normalized_iterate_scale c p hd.ne' 3 w
  rw [he] at hscale
  rw [← hscale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  change criticalValue c p * ‖threeReturn c p w‖ + criticalValue c p/150 < _
  have hmul := mul_lt_mul_of_pos_left hbound hd
  linarith only [hmul]

/-- Both sides of the actual physical size estimate hold simultaneously.
Thus the previous outer bound is accompanied by a positive uniform inner
radius in the same critical-return coordinate. -/
theorem selected_physical_disk_sandwich {p : ℕ} (hp : 3 ≤ p)
    {c : ℝ} (hc : SelectedParameter p c) :
    closedBall (0 : ℂ) (criticalValue c p/40) ⊆ physicalSource c p ∧
      closure (physicalSource c p) ⊆ ball 0 (3*criticalValue c p/20) :=
  ⟨selected_physical_closedBall_subset hp hc,
    (selected_canonical_collar hp hc).physical_closure_inside⟩

/-- Every p at least three has a complete actual physical realization
with the additional uniform inner-disk estimate. -/
theorem exists_physical_renormalization_with_inradius (p : ℕ) (hp : 3 ≤ p) :
    ∃ c : ℝ, UniformThreeReturnRenormalization.PhysicalRenormalization c p ∧
      closedBall (0 : ℂ) (criticalValue c p/40) ⊆ physicalSource c p := by
  obtain ⟨c, hc⟩ := exists_selected_parameter p hp
  exact ⟨c, UniformThreeReturnRenormalization.selected_physical_renormalization hp hc,
    selected_physical_closedBall_subset hp hc⟩

end
end ThreeReturnInradius
