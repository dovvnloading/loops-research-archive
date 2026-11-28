import ActualPairablePorts

/-!
# Convergence of the actual pairable source ports

The unique actual positive fixed cut has a quantitative error from the
positive fixed point of the limiting quadratic.  Together with the
literal critical-orbit estimates, this gives convergence of all four
return-image electrodes for every sequence of actual signed tips.
-/

namespace ActualPairablePortLimit

open Set Function Filter
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open ActualPairablePorts ActualParentMarks LoopsLimitingCrestParameter
open scoped Topology

noncomputable section

def limitingAlpha (k : ℝ) (hk : k ∈ parameterInterval) : ℝ :=
  Classical.choose (positive_fixed_point hk)

theorem limitingAlpha_pos {k : ℝ} (hk : k ∈ parameterInterval) : 0 < limitingAlpha k hk :=
  (Classical.choose_spec (positive_fixed_point hk)).1.1

theorem limitingAlpha_fixed {k : ℝ} (hk : k ∈ parameterInterval) :
    realMap k (limitingAlpha k hk) = limitingAlpha k hk :=
  (Classical.choose_spec (positive_fixed_point hk)).1.2

theorem limitingAlpha_unique {k : ℝ} (hk : k ∈ parameterInterval) {a : ℝ}
    (ha : 0 < a) (hfix : realMap k a = a) : a = limitingAlpha k hk :=
  (Classical.choose_spec (positive_fixed_point hk)).2 a ⟨ha,hfix⟩

theorem limitingAlpha_bounds {k : ℝ} (hk : k ∈ parameterInterval) :
    limitingAlpha k hk ∈ Ioo (518/1000 : ℝ) (519/1000) :=
  positive_fixed_point_bracket hk (limitingAlpha_pos hk) (limitingAlpha_fixed hk)

/-- The actual fixed cut converges at the complete-map error scale.
The denominator gain is at least one on the whole positive branch. -/
theorem normalizedAlpha_error {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    |normalizedAlpha hp hc-limitingAlpha k hk| ≤ 23646*scale p := by
  have ha := normalizedAlpha_bounds hp hc
  have ha0 : 0 < normalizedAlpha hp hc := by linarith [ha.1]
  have hk0 : 0 < k := by have h:=hk.1; change 17903/10000 ≤ k at h; linarith
  have herr := ActualCrestLimit.actual_tip_limit_map_error hp hc hk hroot
    (z := (normalizedAlpha hp hc : ℂ)) (by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha0]
      linarith [ha.2])
  have hre := (Complex.abs_re_le_norm
    (normalizedReturn c p (normalizedAlpha hp hc : ℂ)-complexMap k (normalizedAlpha hp hc : ℂ))).trans herr
  rw [normalizedAlpha_fixed hp hc,complexMap_real] at hre
  simp only [Complex.sub_re,Complex.ofReal_re] at hre
  have hfix := limitingAlpha_fixed hk
  have hfactor : 1 ≤ k*(normalizedAlpha hp hc+limitingAlpha k hk)+1 := by
    have hm := mul_nonneg hk0.le (add_nonneg ha0.le (limitingAlpha_pos hk).le)
    linarith
  have he : (normalizedAlpha hp hc-limitingAlpha k hk)*
      (k*(normalizedAlpha hp hc+limitingAlpha k hk)+1) =
      normalizedAlpha hp hc-realMap k (normalizedAlpha hp hc) := by
    dsimp [realMap] at hfix ⊢
    nlinarith
  calc
    |normalizedAlpha hp hc-limitingAlpha k hk| ≤
        |normalizedAlpha hp hc-limitingAlpha k hk| * (k*(normalizedAlpha hp hc+limitingAlpha k hk)+1) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)
    _ = |normalizedAlpha hp hc-realMap k (normalizedAlpha hp hc)| := by
      rw [← he,abs_mul,abs_of_nonneg (by linarith : 0 ≤ k*(normalizedAlpha hp hc+limitingAlpha k hk)+1)]
    _ ≤ 23646*scale p := hre

private theorem scaled_error_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ => C*scale (n+17)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (1/4 : ℝ)^n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [scale,pow_add,mul_zero,zero_mul] using
    (hbase.mul_const ((1/4 : ℝ)^17)).const_mul C

theorem normalizedAlpha_tendsto {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => normalizedAlpha (by omega : 17 ≤ n+17) (hc n)) atTop
      (𝓝 (limitingAlpha k hk)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (tendsto_order.mp (scaled_error_tendsto_zero 23646)).2 ε hε
  filter_upwards [he] with n hn
  rw [Real.dist_eq]
  exact (normalizedAlpha_error (by omega) (hc n) hk hroot).trans_lt hn

theorem normalizedCut_tendsto {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n))
    {j : ℕ} (hj : j ≤ 6) :
    Tendsto (fun n => normalizedCut (c n) (n+17) j) atTop (𝓝 (criticalOrbit k j)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (tendsto_order.mp (scaled_error_tendsto_zero (3906*23646))).2 ε hε
  filter_upwards [he] with n hn
  rw [Real.dist_eq]
  exact (normalizedCut_error_uniform (by omega) hj (hc n) hk hroot).trans_lt hn

def normalizedImageCuts {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : Fin 4 → ℝ :=
  ![normalizedCut c p 5,normalizedCut c p 3,normalizedCut c p 6,normalizedAlpha hp hc]

def physicalImageCuts {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : Fin 4 → ℝ :=
  ![cut c p 5,cut c p 3,cut c p 6,alpha hp hc]

theorem physicalImageCuts_div {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c)
    (i : Fin 4) : physicalImageCuts hp hc i/criticalValue c p = normalizedImageCuts hp hc i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · dsimp [physicalImageCuts,normalizedImageCuts,alpha]
    field_simp [hc.2.1.ne']

theorem normalizedImageCuts_mem_Ioo {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c)
    (i : Fin 4) : normalizedImageCuts hp hc i ∈ Ioo (-1 : ℝ) 1 := by
  obtain ⟨h2,h3,h4,h5,h6⟩ := normalized_cut_boxes hp hc
  have ha := normalizedAlpha_bounds hp hc
  fin_cases i <;> dsimp [normalizedImageCuts] <;> constructor <;>
    linarith [h3.1,h3.2,h5.1,h5.2,h6.1,h6.2,ha.1,ha.2]

theorem physicalImageCuts_lt_criticalValue {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (i : Fin 4) : physicalImageCuts hp hc i < criticalValue c p := by
  have h := (normalizedImageCuts_mem_Ioo hp hc i).2
  rw [← physicalImageCuts_div hp hc i] at h
  exact (div_lt_one hc.2.1).mp h

def limitingImageCuts (k : ℝ) (hk : k ∈ parameterInterval) : Fin 4 → ℝ :=
  ![criticalOrbit k 5,criticalOrbit k 3,criticalOrbit k 6,limitingAlpha k hk]

def limitingSourcePorts (k : ℝ) (hk : k ∈ parameterInterval) : Fin 4 → ℝ :=
  ![-criticalOrbit k 4,criticalOrbit k 2,criticalOrbit k 5,-limitingAlpha k hk]

theorem normalizedImageCuts_tendsto {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)) (i : Fin 4) :
    Tendsto (fun n => normalizedImageCuts (by omega : 17 ≤ n+17) (hc n) i) atTop
      (𝓝 (limitingImageCuts k hk i)) := by
  fin_cases i
  · exact normalizedCut_tendsto hk hroot c hc (by norm_num : 5 ≤ 6)
  · exact normalizedCut_tendsto hk hroot c hc (by norm_num : 3 ≤ 6)
  · exact normalizedCut_tendsto hk hroot c hc (by norm_num : 6 ≤ 6)
  · exact normalizedAlpha_tendsto hk hroot c hc

theorem normalizedImageCuts_tendsto_function {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => normalizedImageCuts (by omega : 17 ≤ n+17) (hc n)) atTop
      (𝓝 (limitingImageCuts k hk)) :=
  tendsto_pi_nhds.mpr (normalizedImageCuts_tendsto hk hroot c hc)

theorem limiting_image_order {k : ℝ} (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    criticalOrbit k 5 < criticalOrbit k 3 ∧ criticalOrbit k 3 < criticalOrbit k 6 ∧
      criticalOrbit k 6 < limitingAlpha k hk ∧ limitingAlpha k hk < 1 := by
  obtain ⟨_,_,h5l,h5u,h3l,h3u⟩ := limit_cut_boxes hk
  have ha := limitingAlpha_bounds hk
  change criticalOrbit k 6+criticalOrbit k 3=0 at hroot
  refine ⟨?_,?_,?_,?_⟩ <;> linarith [ha.1,ha.2]

theorem limiting_source_order {k : ℝ} (hk : k ∈ parameterInterval) :
    -1 < -criticalOrbit k 4 ∧ -criticalOrbit k 4 < criticalOrbit k 2 ∧
      criticalOrbit k 2 < criticalOrbit k 5 ∧ criticalOrbit k 5 < -limitingAlpha k hk ∧
      -limitingAlpha k hk < 0 := by
  obtain ⟨h2l,h2u,h5l,h5u,h3l,h3u⟩ := limit_cut_boxes hk
  have h4 := parameter_orbit_bounds hk
  have ha := limitingAlpha_bounds hk
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith [h4.2.2.1,h4.2.2.2,ha.1,ha.2]

theorem limitingImageCuts_strictMono {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) : StrictMono (limitingImageCuts k hk) := by
  obtain ⟨h01,h12,h23,_⟩ := limiting_image_order hk hroot
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals norm_num at hij
  all_goals norm_num [limitingImageCuts]
  all_goals linarith

theorem limitingSourcePorts_strictMono {k : ℝ} (hk : k ∈ parameterInterval) :
    StrictMono (limitingSourcePorts k hk) := by
  obtain ⟨_,h01,h12,h23,_⟩ := limiting_source_order hk
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals norm_num at hij
  all_goals norm_num [limitingSourcePorts]
  all_goals linarith

theorem limitingImageCuts_lt_one {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (i : Fin 4) : limitingImageCuts k hk i < 1 := by
  obtain ⟨h01,h12,h23,h3⟩ := limiting_image_order hk hroot
  fin_cases i <;> dsimp [limitingImageCuts] <;> linarith

/-- The limiting square-root image electrodes are a single positive
scale of the physical limiting source ports. -/
theorem sqrt_limitingImageCuts_eq {k : ℝ} (hk : k ∈ parameterInterval) (i : Fin 4) :
    -Real.sqrt (1-limitingImageCuts k hk i) = Real.sqrt k * limitingSourcePorts k hk i := by
  have hk0 : 0 ≤ k := by have h:=hk.1; change 17903/10000 ≤ k at h; linarith
  have h4 := parameter_orbit_bounds hk
  obtain ⟨h2l,h2u,h5l,h5u,_,_⟩ := limit_cut_boxes hk
  have ha := limitingAlpha_pos hk
  have hfix := limitingAlpha_fixed hk
  fin_cases i
  · change -Real.sqrt (1-criticalOrbit k 5) = Real.sqrt k * -criticalOrbit k 4
    have he : 1-criticalOrbit k 5 = k*(criticalOrbit k 4)^2 := by rw [criticalOrbit,Q]; ring
    rw [he,Real.sqrt_mul hk0,Real.sqrt_sq_eq_abs,abs_of_pos (by linarith [h4.2.2.1])]
    ring
  · change -Real.sqrt (1-criticalOrbit k 3) = Real.sqrt k * criticalOrbit k 2
    have he : 1-criticalOrbit k 3 = k*(criticalOrbit k 2)^2 := by rw [criticalOrbit,Q]; ring
    rw [he,Real.sqrt_mul hk0,Real.sqrt_sq_eq_abs,abs_of_neg (by linarith)]
    ring
  · change -Real.sqrt (1-criticalOrbit k 6) = Real.sqrt k * criticalOrbit k 5
    have he : 1-criticalOrbit k 6 = k*(criticalOrbit k 5)^2 := by rw [criticalOrbit,Q]; ring
    rw [he,Real.sqrt_mul hk0,Real.sqrt_sq_eq_abs,abs_of_neg (by linarith)]
    ring
  · change -Real.sqrt (1-limitingAlpha k hk) = Real.sqrt k * -limitingAlpha k hk
    have he : 1-limitingAlpha k hk = k*(limitingAlpha k hk)^2 := by
      dsimp [realMap] at hfix
      linarith
    rw [he,Real.sqrt_mul hk0,Real.sqrt_sq_eq_abs,abs_of_pos ha]
    ring

end
end ActualPairablePortLimit
