import ActualCrestLimit
import LimitingCrestArcGates
import CrestIterateLimit

/-!
# Entire-support geometry of the actual normalized returns

Uniform convergence is used on the full closed input disk. Compactness
transfers the model's strict second- and third-image half-plane gates.
The exact divided difference then excludes every additional collision
on the corresponding actual supports and on the selected fourfold image.
-/

namespace ActualCrestSupport

open Set Function Filter
open scoped Topology
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter QuadraticCrestDividedDifference

noncomputable section

private theorem initialDisk_compact : IsCompact initialDisk := by
  have he : initialDisk = Metric.closedBall (-(3/4 : ℂ)) (133/2000 : ℝ) := by
    ext z
    simp only [initialDisk, mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm,
      sub_neg_eq_add]
  rw [he]
  exact isCompact_closedBall _ _

private instance : CompactSpace initialDisk :=
  isCompact_iff_compactSpace.mp initialDisk_compact

private instance : Nonempty initialDisk :=
  ⟨⟨-(3/4 : ℂ), by simp [initialDisk]; norm_num⟩⟩

private theorem scaled_error_zero (C : ℝ) :
    Tendsto (fun n : ℕ => C*scale (n+17)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (1/4 : ℝ)^n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [scale, pow_add, mul_zero, zero_mul] using
    (hbase.mul_const ((1/4 : ℝ)^17)).const_mul C

private theorem map_convergence {k₀ : ℝ} (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    TendstoUniformlyOn (fun n => normalizedReturn (c n) (n+17))
      (complexMap k₀) atTop {z : ℂ | ‖z‖ ≤ 23/20} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he : ∀ᶠ n : ℕ in atTop, 23646*scale (n+17) < ε :=
    (tendsto_order.mp (scaled_error_zero 23646)).2 ε hε
  filter_upwards [he] with n hn
  intro z hz
  rw [dist_comm, dist_eq_norm]
  exact (ActualCrestLimit.actual_tip_limit_map_error (by omega) (hc n)
    hk₀ hroot hz).trans_lt hn

/-- All four iterates converge uniformly on the entire closed input
disk, and their actual intermediate images stay in the approximation disk. -/
theorem actual_support_iterates_tendsto {k₀ : ℝ} (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    ∀ m ≤ 4,
      TendstoUniformly
        (fun n (z : initialDisk) => ((normalizedReturn (c n) (n+17))^[m]) z)
        (fun z : initialDisk => ((complexMap k₀)^[m]) z) atTop ∧
      ∀ᶠ n in atTop, ∀ z : initialDisk,
        ‖((normalizedReturn (c n) (n+17))^[m]) z‖ ≤ 23/20 := by
  have hz : Continuous (fun z : initialDisk => (z : ℂ)) := continuous_subtype_val
  have hQ : Continuous (complexMap k₀) := by unfold complexMap; fun_prop
  have hR (m : ℕ) (hm : m ≤ 4) (z : initialDisk) :
      ‖((complexMap k₀)^[m]) z‖ < 23/20 :=
    (whole_support_bounds hk₀ z.property).1 m hm
  have hZ : TendstoUniformly (fun (_ : ℕ) (z : initialDisk) => (z : ℂ))
      (fun z : initialDisk => (z : ℂ)) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    exact Eventually.of_forall (fun _ z => by simpa only [dist_self] using hε)
  have hlip (v w : ℂ) (hv : ‖v‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
      ‖complexMap k₀ v-complexMap k₀ w‖ ≤ 5*‖v-w‖ :=
    LimitingCrestPerturbation.quadratic_disk_lipschitz k₀
      (by linarith [hk₀.1]) (by linarith [hk₀.2]) v w hv hw
  exact CrestIterateLimit.finite_iterates_uniformly 4 hz hQ hR hZ
    (map_convergence hk₀ hroot c hc) hlip

set_option maxHeartbeats 800000 in
/-- Complete-support bounds for every choice of actual signed-tip
parameters. The second and third images have uniform strict real signs
at all sufficiently large periods; no sampling or selected-curve premise
is used. -/
theorem actual_support_bounds (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    ∀ᶠ n in atTop, ∀ z ∈ initialDisk,
      (∀ m ≤ 4, ‖((normalizedReturn (c n) (n+17))^[m]) z‖ ≤ 23/20) ∧
        0 < (((normalizedReturn (c n) (n+17))^[2]) z).re ∧
        (((normalizedReturn (c n) (n+17))^[3]) z).re < 0 := by
  obtain ⟨k₀, ⟨hk₀, hroot⟩, _⟩ := exists_unique_limiting_parameter
  have hi := actual_support_iterates_tendsto hk₀ hroot c hc
  have hQ : Continuous (complexMap k₀) := by unfold complexMap; fun_prop
  have h2 : Continuous (fun z : initialDisk => (((complexMap k₀)^[2]) z).re) :=
    Complex.continuous_re.comp ((hQ.iterate 2).comp continuous_subtype_val)
  have h3 : Continuous (fun z : initialDisk => (((complexMap k₀)^[3]) z).re) :=
    Complex.continuous_re.comp ((hQ.iterate 3).comp continuous_subtype_val)
  obtain ⟨z₂, _, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty h2.continuousOn
  obtain ⟨z₃, _, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty h3.continuousOn
  let ε := min (((complexMap k₀)^[2]) z₂).re (-(((complexMap k₀)^[3]) z₃).re)
  have hε : 0 < ε := lt_min
    (whole_support_bounds hk₀ z₂.property).2.1
    (neg_pos.mpr (whole_support_bounds hk₀ z₃.property).2.2)
  have hnorm : ∀ᶠ n in atTop, ∀ m ≤ 4, ∀ z : initialDisk,
      ‖((normalizedReturn (c n) (n+17))^[m]) z‖ ≤ 23/20 := by
    have hall : ∀ᶠ n in atTop, ∀ m ∈ Finset.range 5, ∀ z : initialDisk,
        ‖((normalizedReturn (c n) (n+17))^[m]) z‖ ≤ 23/20 :=
      (eventually_all_finset (Finset.range 5)).mpr
        (fun m hm => (hi m (by have := Finset.mem_range.mp hm; omega)).2)
    filter_upwards [hall] with n hn
    intro m hm z
    exact hn m (Finset.mem_range.mpr (by omega)) z
  filter_upwards [hnorm,
    Metric.tendstoUniformly_iff.mp (hi 2 (by norm_num)).1 ε hε,
    Metric.tendstoUniformly_iff.mp (hi 3 (by norm_num)).1 ε hε] with n hn hn₂ hn₃
  intro z hz
  let zz : initialDisk := ⟨z, hz⟩
  refine ⟨fun m hm => hn m hm zz, ?_, ?_⟩
  · have he := hn₂ zz
    rw [dist_eq_norm] at he
    have hre := (Complex.re_le_norm
      (((complexMap k₀)^[2]) z - ((normalizedReturn (c n) (n+17))^[2]) z)).trans_lt he
    simp only [Complex.sub_re] at hre
    have hlow := hmin (mem_univ zz)
    dsimp only [mem_setOf_eq, zz] at hlow
    have hεlow : ε ≤ (((complexMap k₀)^[2]) z₂).re := min_le_left _ _
    linarith only [hre, hlow, hεlow]
  · have he := hn₃ zz
    rw [dist_eq_norm, norm_sub_rev] at he
    have hre := (Complex.re_le_norm
      (((normalizedReturn (c n) (n+17))^[3]) z - ((complexMap k₀)^[3]) z)).trans_lt he
    simp only [Complex.sub_re] at hre
    have hupp := hmax (mem_univ zz)
    dsimp only [mem_setOf_eq, zz] at hupp
    have hεupp : ε ≤ -(((complexMap k₀)^[3]) z₃).re := min_le_right _ _
    linarith only [hre, hupp, hεupp]

private theorem initialDisk_negative_re {z : ℂ} (hz : z ∈ initialDisk) : z.re < 0 := by
  have h := (Complex.re_le_norm (z+(3/4 : ℂ))).trans hz
  norm_num at h
  linarith

private theorem actual_half_disk_injective {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    InjOn (normalizedReturn c p) {z : ℂ | ‖z‖ ≤ 23/20 ∧ z.re < 0} ∧
      InjOn (normalizedReturn c p) {z : ℂ | ‖z‖ ≤ 23/20 ∧ 0 < z.re} := by
  have hband := parameter_band hp hc.1
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  have hcol {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20)
      (he : normalizedReturn c p z = normalizedReturn c p w) : z = w ∨ z = -w :=
    (normalized_return_collision_iff c p (by omega)
      ⟨hband.1, by linarith [hband.2]⟩ hc.2.1 hsmall hc.2.2.2.1 hz hw).mp he
  constructor
  · intro z hz w hw he
    rcases hcol hz.1 hw.1 he with h | h
    · exact h
    · have hr := congrArg Complex.re h
      simp only [Complex.neg_re] at hr
      exact (by linarith [hz.2, hw.2] : False).elim
  · intro z hz w hw he
    rcases hcol hz.1 hw.1 he with h | h
    · exact h
    · have hr := congrArg Complex.re h
      simp only [Complex.neg_re] at hr
      exact (by linarith [hz.2, hw.2] : False).elim

/-- The literal high-degree normalized polynomial return is injective
on the entire input disk and on the entire second and third image supports. -/
theorem actual_complete_support_injective (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    ∀ᶠ n in atTop,
      InjOn (normalizedReturn (c n) (n+17)) initialDisk ∧
        InjOn (normalizedReturn (c n) (n+17))
          ((normalizedReturn (c n) (n+17))^[2] '' initialDisk) ∧
        InjOn (normalizedReturn (c n) (n+17))
          ((normalizedReturn (c n) (n+17))^[3] '' initialDisk) := by
  filter_upwards [actual_support_bounds c hc] with n hn
  have hinj := actual_half_disk_injective (by omega) (hc n)
  refine ⟨hinj.1.mono ?_, hinj.2.mono ?_, hinj.1.mono ?_⟩
  · intro z hz
    exact ⟨by simpa using (hn z hz).1 0 (by norm_num), initialDisk_negative_re hz⟩
  · rintro z ⟨w, hw, rfl⟩
    exact ⟨(hn w hw).1 2 (by norm_num), (hn w hw).2.1⟩
  · rintro z ⟨w, hw, rfl⟩
    exact ⟨(hn w hw).1 3 (by norm_num), (hn w hw).2.2⟩

/-- All four actual pushes are injective on the complete input support
whose first image lies on the selected positive-real side. The criterion
uses the actual return, not the limiting model's sign. -/
theorem actual_selected_side_fourfold_injective (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    ∀ᶠ n in atTop,
      InjOn ((normalizedReturn (c n) (n+17))^[4])
        {z : ℂ | z ∈ initialDisk ∧ 0 < (normalizedReturn (c n) (n+17) z).re} := by
  filter_upwards [actual_support_bounds c hc, actual_complete_support_injective c hc]
    with n hn hd
  have hp := (actual_half_disk_injective (by omega) (hc n)).2
  intro z hz w hw he
  have h3 : (normalizedReturn (c n) (n+17))^[3] z =
      (normalizedReturn (c n) (n+17))^[3] w :=
    hd.2.2 ⟨z, hz.1, rfl⟩ ⟨w, hw.1, rfl⟩ he
  have h2 : (normalizedReturn (c n) (n+17))^[2] z =
      (normalizedReturn (c n) (n+17))^[2] w :=
    hd.2.1 ⟨z, hz.1, rfl⟩ ⟨w, hw.1, rfl⟩ h3
  have h1 : normalizedReturn (c n) (n+17) z = normalizedReturn (c n) (n+17) w :=
    hp ⟨by simpa using (hn z hz.1).1 1 (by norm_num), hz.2⟩
      ⟨by simpa using (hn w hw.1).1 1 (by norm_num), hw.2⟩ h2
  exact hd.1 hz.1 hw.1 h1

/-- One period threshold works for all admissible actual signed-tip
parameters, simultaneously. Arbitrary parameter selection cannot postpone
the complete support bounds or the selected-side fourfold injectivity. -/
theorem eventually_all_actual_tips_support :
    ∀ᶠ n : ℕ in atTop, ∀ c : ℝ, ActualTip (n+17) c →
      (∀ z ∈ initialDisk,
        (∀ m ≤ 4, ‖((normalizedReturn c (n+17))^[m]) z‖ ≤ 23/20) ∧
          0 < (((normalizedReturn c (n+17))^[2]) z).re ∧
          (((normalizedReturn c (n+17))^[3]) z).re < 0) ∧
      InjOn ((normalizedReturn c (n+17))^[4])
        {z : ℂ | z ∈ initialDisk ∧ 0 < (normalizedReturn c (n+17) z).re} := by
  classical
  let P : ℕ → ℝ → Prop := fun n c =>
    (∀ z ∈ initialDisk,
      (∀ m ≤ 4, ‖((normalizedReturn c (n+17))^[m]) z‖ ≤ 23/20) ∧
        0 < (((normalizedReturn c (n+17))^[2]) z).re ∧
        (((normalizedReturn c (n+17))^[3]) z).re < 0) ∧
    InjOn ((normalizedReturn c (n+17))^[4])
      {z : ℂ | z ∈ initialDisk ∧ 0 < (normalizedReturn c (n+17) z).re}
  have hselect : ∀ n : ℕ, ∃ c : ℝ, ActualTip (n+17) c ∧
      ((∃ d : ℝ, ActualTip (n+17) d ∧ ¬ P n d) → ¬ P n c) := by
    intro n
    by_cases h : ∃ d : ℝ, ActualTip (n+17) d ∧ ¬ P n d
    · obtain ⟨c, hc, hbad⟩ := h
      exact ⟨c, hc, fun _ => hbad⟩
    · obtain ⟨c, hc⟩ := exists_actual_tip (n+17) (by omega)
      exact ⟨c, hc, fun hh => (h hh).elim⟩
  choose c hc hbad using hselect
  filter_upwards [actual_support_bounds c hc, actual_selected_side_fourfold_injective c hc]
    with n hn hi
  intro d hd
  change P n d
  by_contra h
  exact hbad n ⟨d, hd, h⟩ ⟨hn, hi⟩

end
end ActualCrestSupport
