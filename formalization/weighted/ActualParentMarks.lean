import ActualCrestLimit
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# The actual four marked parent cuts and expanding target disks

The cuts are literal critical-orbit values of the constructed quadratic
parameters, divided by their positive first-return value. Their limiting
configuration is ordered with a uniform gap. No source-domain or
immersion-marking assertion is used here.
-/

namespace ActualParentMarks

open Set Function Filter
open NearTwoTip NearTwoShooting LimitingCrest LimitingCrestPerturbation
open LimitingCrestQuadraticReturn LoopsLimitingCrestParameter
open CriticalReturnRelationStability ActualCrestLimit
open scoped Topology

noncomputable section

/-- A literal normalized critical return, retaining the physical index
`j*p` rather than replacing it with `j`. -/
def normalizedCut (c : ℝ) (p j : ℕ) : ℝ :=
  criticalValue c (j*p) / criticalValue c p

/-- Slit left tip, two parent electrode cuts, and slit right tip. -/
def actualCuts (c : ℝ) (p : ℕ) : Fin 4 → ℝ :=
  ![normalizedCut c p 2, normalizedCut c p 5, normalizedCut c p 3, 1]

def limitCuts (k : ℝ) : Fin 4 → ℝ :=
  ![criticalOrbit k 2, criticalOrbit k 5, criticalOrbit k 3, 1]

/-- The actual target disk radius after positive scaling by `x_p`. -/
def targetRadius (c : ℝ) (p : ℕ) : ℝ :=
  (1/2 : ℝ)^p / criticalValue c p

private theorem actual_iterate_real (c t : ℝ) (n : ℕ) :
    ((quadraticMap c)^[n]) (t : ℂ) =
      (((fun x : ℝ => x^2+c)^[n]) t : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih]
    simp only [quadraticMap, Complex.ofReal_add, Complex.ofReal_pow]

private theorem model_iterate_real (k : ℝ) (n : ℕ) :
    ((complexMap k)^[n]) 0 = (criticalOrbit k n : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    simp only [criticalOrbit, Q, complexMap]
    push_cast
    rfl

/-- Exact scaling identifies the cut with the normalized polynomial
iterate; this is not a model assignment of cut values. -/
theorem normalizedCut_eq_re (c : ℝ) (p j : ℕ) (hd : criticalValue c p ≠ 0) :
    normalizedCut c p j = (((normalizedReturn c p)^[j]) 0).re := by
  have hs := normalized_iterate_scale c p hd j (0 : ℂ)
  simp only [mul_zero] at hs
  have hc : ((quadraticMap c)^[j*p]) (0 : ℂ) =
      (criticalValue c (j*p) : ℂ) := actual_iterate_real c 0 (j*p)
  rw [hc] at hs
  have hr := congrArg Complex.re hs
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
  unfold normalizedCut
  apply (div_eq_iff hd).mpr
  simpa only [mul_comm] using hr.symm

private theorem errorCoefficient_le (j : ℕ) (hj : j ≤ 6) :
    errorCoefficient j ≤ 3906 := by
  interval_cases j <;> norm_num [errorCoefficient]

/-- Every relevant physical normalized critical cut converges with an
explicit exponentially small error. -/
theorem normalizedCut_error {p j : ℕ} (hp : 17 ≤ p) (hj : j ≤ 6)
    {c k : ℝ} (hc : ActualTip p c) (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) :
    |normalizedCut c p j-criticalOrbit k j| ≤
      errorCoefficient j * (23646*scale p) := by
  let ε : ℝ := 23646*scale p
  have hscale : 0 < scale p := scale_pos p
  have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
  have hεmax : ε ≤ 1/100000 := by
    dsimp [ε]
    nlinarith [scale_small hp]
  have hk0 : 0 ≤ k := by linarith [hk.1]
  have hk2 : k ≤ 2 := by linarith [hk.2]
  have hiter := iterate_perturbation_up_to_six
    (normalizedReturn c p) (complexMap k) 0 ε hε0 hεmax
    (fun z hz => actual_tip_limit_map_error hp hc hk hroot hz)
    (quadratic_disk_lipschitz k hk0 hk2)
    (fun m _ => quadratic_critical_orbit_unit k hk0 hk2 m)
  have hr := (Complex.abs_re_le_norm
    (((normalizedReturn c p)^[j]) 0-((complexMap k)^[j]) 0)).trans (hiter j hj).1
  rw [model_iterate_real] at hr
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  rw [normalizedCut_eq_re c p j hc.2.1.ne']
  exact hr

theorem normalizedCut_error_uniform {p j : ℕ} (hp : 17 ≤ p) (hj : j ≤ 6)
    {c k : ℝ} (hc : ActualTip p c) (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) :
    |normalizedCut c p j-criticalOrbit k j| ≤ 3906*23646*scale p := by
  have hscale : 0 < scale p := scale_pos p
  refine (normalizedCut_error hp hj hc hk hroot).trans ?_
  have h := mul_le_mul_of_nonneg_right (errorCoefficient_le j hj)
    (show 0 ≤ 23646*scale p by positivity)
  simpa only [mul_assoc] using h

theorem actualCuts_error {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0)
    (i : Fin 4) :
    |actualCuts c p i-limitCuts k i| ≤ 3906*23646*scale p := by
  have hscale : 0 < scale p := scale_pos p
  fin_cases i
  · exact normalizedCut_error_uniform hp (by norm_num : 2 ≤ 6) hc hk hroot
  · exact normalizedCut_error_uniform hp (by norm_num : 5 ≤ 6) hc hk hroot
  · exact normalizedCut_error_uniform hp (by norm_num : 3 ≤ 6) hc hk hroot
  · change |(1 : ℝ)-1| ≤ _
    norm_num only [sub_self, abs_zero]
    positivity

theorem actualCuts_error_lt {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0)
    (i : Fin 4) : |actualCuts c p i-limitCuts k i| < 1/100 := by
  have he := actualCuts_error hp hc hk hroot i
  nlinarith [scale_small hp]

/-- Coarse rational boxes suffice to separate all marked cuts. -/
theorem limit_cut_boxes {k : ℝ} (hk : k ∈ parameterInterval) :
    -(4/5 : ℝ) < criticalOrbit k 2 ∧ criticalOrbit k 2 < -(79/100 : ℝ) ∧
    -(3/4 : ℝ) < criticalOrbit k 5 ∧ criticalOrbit k 5 < -(2/3 : ℝ) ∧
    -(119/1000 : ℝ) < criticalOrbit k 3 ∧ criticalOrbit k 3 < -(118/1000 : ℝ) := by
  have hb := parameter_orbit_bounds hk
  have hklo : (179/100 : ℝ) ≤ k := by linarith [hk.1]
  have hkhi : k ≤ (9/5 : ℝ) := by linarith [hk.2]
  have h4lo : (97/100 : ℝ) < criticalOrbit k 4 := by linarith [hb.2.2.1]
  have h4hi : criticalOrbit k 4 < (49/50 : ℝ) := by linarith [hb.2.2.2]
  have hslo : (97/100 : ℝ)^2 < (criticalOrbit k 4)^2 := by nlinarith
  have hshi : (criticalOrbit k 4)^2 < (49/50 : ℝ)^2 := by nlinarith
  have hplo : (179/100 : ℝ)*(97/100)^2 < k*(criticalOrbit k 4)^2 := by
    calc
      (179/100 : ℝ)*(97/100)^2 < (179/100 : ℝ)*(criticalOrbit k 4)^2 :=
        mul_lt_mul_of_pos_left hslo (by norm_num)
      _ ≤ k*(criticalOrbit k 4)^2 := mul_le_mul_of_nonneg_right hklo (sq_nonneg _)
  have hphi : k*(criticalOrbit k 4)^2 < (9/5 : ℝ)*(49/50)^2 := by
    calc
      k*(criticalOrbit k 4)^2 ≤ (9/5 : ℝ)*(criticalOrbit k 4)^2 :=
        mul_le_mul_of_nonneg_right hkhi (sq_nonneg _)
      _ < (9/5 : ℝ)*(49/50)^2 := mul_lt_mul_of_pos_left hshi (by norm_num)
  have h2 : criticalOrbit k 2 = 1-k := by norm_num [criticalOrbit, Q]
  have h5 : criticalOrbit k 5 = 1-k*(criticalOrbit k 4)^2 := rfl
  refine ⟨?_, ?_, ?_, ?_, hb.1, hb.2.1⟩
  · rw [h2]; linarith [hk.2]
  · rw [h2]; linarith [hk.1]
  · rw [h5]; nlinarith
  · rw [h5]; nlinarith

theorem limitCuts_gap {k : ℝ} (hk : k ∈ parameterInterval)
    {i j : Fin 4} (hij : i < j) :
    (1/25 : ℝ) < limitCuts k j-limitCuts k i := by
  obtain ⟨h2l,h2u,h5l,h5u,h3l,h3u⟩ := limit_cut_boxes hk
  fin_cases i <;> fin_cases j
  all_goals norm_num at hij
  all_goals norm_num [limitCuts]
  all_goals linarith

theorem limitCuts_strictMono {k : ℝ} (hk : k ∈ parameterInterval) :
    StrictMono (limitCuts k) := by
  intro i j hij
  have hg := limitCuts_gap hk hij
  linarith

theorem limitCuts_separated {k : ℝ} (hk : k ∈ parameterInterval)
    {i j : Fin 4} (hij : i ≠ j) :
    (1/25 : ℝ) < |limitCuts k i-limitCuts k j| := by
  rcases lt_or_gt_of_ne hij with hij | hij
  · simpa only [abs_sub_comm] using
      (limitCuts_gap hk hij).trans_le (le_abs_self (limitCuts k j-limitCuts k i))
  · exact (limitCuts_gap hk hij).trans_le (le_abs_self _)

/-- Even at the first constructed period, the actual cuts are strictly
ordered with a fixed positive separation. -/
theorem actualCuts_gap {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0)
    {i j : Fin 4} (hij : i < j) :
    (1/50 : ℝ) < actualCuts c p j-actualCuts c p i := by
  have hi := abs_lt.mp (actualCuts_error_lt hp hc hk hroot i)
  have hj := abs_lt.mp (actualCuts_error_lt hp hc hk hroot j)
  have hg := limitCuts_gap hk hij
  linarith

theorem actualCuts_strictMono {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    StrictMono (actualCuts c p) := by
  intro i j hij
  have hg := actualCuts_gap hp hc hk hroot hij
  linarith

theorem actualCuts_separated {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0)
    {i j : Fin 4} (hij : i ≠ j) :
    (1/50 : ℝ) < |actualCuts c p i-actualCuts c p j| := by
  rcases lt_or_gt_of_ne hij with hij | hij
  · simpa only [abs_sub_comm] using
      (actualCuts_gap hp hc hk hroot hij).trans_le
        (le_abs_self (actualCuts c p j-actualCuts c p i))
  · exact (actualCuts_gap hp hc hk hroot hij).trans_le (le_abs_self _)

private theorem scaled_error_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ => C*scale (n+17)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (1/4 : ℝ)^n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [scale, pow_add, mul_zero, zero_mul] using
    (hbase.mul_const ((1/4 : ℝ)^17)).const_mul C

/-- All four literal orbit marks converge, for every sequence of actual
tips satisfying the already constructed signed shooting conditions. -/
theorem actualCuts_tendsto {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) (i : Fin 4) :
    Tendsto (fun n => actualCuts (c n) (n+17) i) atTop (𝓝 (limitCuts k i)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (tendsto_order.mp (scaled_error_tendsto_zero (3906*23646))).2 ε hε
  filter_upwards [he] with n hn
  rw [Real.dist_eq]
  exact (actualCuts_error (by omega) (hc n) hk hroot i).trans_lt hn

/-- The actual target radius has an explicit exponentially growing
lower bound in the same normalization as the four cuts. -/
theorem targetRadius_lower {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    (2 : ℝ)^p/12 ≤ targetRadius c p := by
  unfold targetRadius
  apply (le_div_iff₀ hc.2.1).mpr
  calc
    ((2 : ℝ)^p/12)*criticalValue c p ≤ ((2 : ℝ)^p/12)*(12*scale p) :=
      mul_le_mul_of_nonneg_left hc.2.2.1 (by positivity)
    _ = (2 : ℝ)^p*(1/4 : ℝ)^p := by unfold scale; ring
    _ = (2*(1/4) : ℝ)^p := (mul_pow _ _ _).symm
    _ = (1/2 : ℝ)^p := by norm_num

theorem targetRadius_tendsto (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => targetRadius (c n) (n+17)) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ)^(n+17)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 17)
  exact tendsto_atTop_mono (fun n => targetRadius_lower (hc n))
    (hpow.atTop_div_const (by norm_num : (0 : ℝ) < 12))

/-- A genuine family of quadratic parameters, ordered physical marks,
their limiting configuration, and expanding target disks are produced
together. No cut or radius convergence is assumed. -/
theorem exists_converging_actual_parent_marks :
    ∃ k : ℝ, k ∈ parameterInterval ∧ relation k = 0 ∧
      ∃ c : ℕ → ℝ, (∀ n, ActualTip (n+17) (c n)) ∧
        StrictMono (limitCuts k) ∧
        (∀ n, StrictMono (actualCuts (c n) (n+17))) ∧
        (∀ i : Fin 4, Tendsto (fun n => actualCuts (c n) (n+17) i)
          atTop (𝓝 (limitCuts k i))) ∧
        Tendsto (fun n => targetRadius (c n) (n+17)) atTop atTop := by
  classical
  obtain ⟨k,⟨hk,hroot⟩,_⟩ := exists_unique_limiting_parameter
  have hex (n : ℕ) := exists_actual_tip (n+17) (by omega)
  choose c hc using hex
  exact ⟨k,hk,hroot,c,hc,limitCuts_strictMono hk,
    (fun n => actualCuts_strictMono (by omega) (hc n) hk hroot),
    (fun i => actualCuts_tendsto hk hroot c hc i), targetRadius_tendsto c hc⟩

end
end ActualParentMarks
