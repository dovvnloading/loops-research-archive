import ChildSlitCompression
import SlitWaveLimit

/-!
# Complete child-supremum convergence on moving source components

This adapts the archived whole-family cutoff argument to two disjoint
intervals on the same slit bank. The homotopies remain in the moving
source. All geometric compression, mark motion and escape estimates
apply before the supremum is taken; no optimizer is used.
-/

namespace ChildSlitLimit

open Set Filter MeasureTheory Metric
open MarkedSlitTransport SlitWaveModulus SlitWaveEscape
open ChildSlitModel ChildSlitTransport
open scoped ENNReal NNReal Topology

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem trace_preconnected (γ : Curve) : IsPreconnected (trace γ) :=
  isPreconnected_range γ.continuous

def endpointRadius (M : ChildMarking) : ℝ :=
  |M.left| + |M.firstLo| + |M.firstHi| + |M.right| + 1

theorem endpointRadius_pos (M : ChildMarking) : 0 < endpointRadius M := by
  dsimp [endpointRadius]
  positivity

theorem first_end_norm_le {M : ChildMarking} {D : Set ℂ} {γ : Curve}
    (hγ : ChildLeaf M D γ) : ‖γ initial‖ ≤ endpointRadius M := by
  have hγre : ‖γ initial‖ = |(γ initial).re| := by
    have he : γ initial = ((γ initial).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hγ.first_end.1
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    simp
  rw [hγre]
  apply abs_le.mpr
  have ha := hγ.first_end.2.1
  have hb := hγ.first_end.2.2
  have hfa := neg_abs_le M.firstLo
  have hsb := le_abs_self M.firstHi
  constructor <;> dsimp [endpointRadius] <;>
    linarith [abs_nonneg M.left, abs_nonneg M.firstLo,
      abs_nonneg M.firstHi, abs_nonneg M.right]

/-- A common admissible density controls every discarded leaf, including
leaves with infinite arclength. No measurability of the discarded
leaf subfamily is assumed or needed for this modulus upper bound. -/
theorem discarded_modulus_le {M : ChildMarking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ChildWave M D Γ) {N : ℕ} (hN : 0 < N) :
    modulus (traces (Γ \ boundedCurves (dyadicRadius (endpointRadius M) N))) ≤
      ENNReal.ofReal (3 * Real.pi / (N : ℝ)) := by
  obtain ⟨ρ, hρ, harea, hlength⟩ := exists_escape_density (endpointRadius_pos M) hN
  have ha : Admissible (traces (Γ \ boundedCurves (dyadicRadius (endpointRadius M) N))) ρ := by
    refine ⟨hρ, ?_⟩
    rintro _ ⟨γ, ⟨hγ, hb⟩, rfl⟩
    apply hlength (trace γ) (trace_preconnected γ)
    · exact ⟨γ initial, ⟨initial, rfl⟩, first_end_norm_le (hΓ.leaf γ hγ)⟩
    · change ¬ ∀ t : Parameter, ‖γ t‖ ≤ dyadicRadius (endpointRadius M) N at hb
      push_neg at hb
      obtain ⟨t, ht⟩ := hb
      exact ⟨γ t, ⟨t, rfl⟩, ht.le⟩
  exact (modulus_le_area ha).trans_eq harea

theorem traces_decompose (Γ : Set Curve) (R : ℝ) :
    traces Γ = traces (Γ ∩ boundedCurves R) ∪ traces (Γ \ boundedCurves R) := by
  unfold traces
  rw [← image_union, inter_union_diff]

/-- Quantitative exhaustion of the modulus of any complete child
lamination, uniformly over the lamination. -/
theorem lamination_cutoff {M : ChildMarking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ChildWave M D Γ) {N : ℕ} (hN : 0 < N) :
    modulus (traces Γ) ≤
      modulus (traces (Γ ∩ boundedCurves (dyadicRadius (endpointRadius M) N))) +
        ENNReal.ofReal (3 * Real.pi / (N : ℝ)) := by
  rw [traces_decompose Γ (dyadicRadius (endpointRadius M) N)]
  exact (modulus_union_le _ _).trans
    (add_le_add le_rfl (discarded_modulus_le hΓ hN))

/-- The whole limiting supremum is approximated by complete bounded
laminations. The entire Wave is compressed, so no measurable selection
of a retained subfamily is assumed. -/
theorem width_cutoff (M : ChildMarking) {N : ℕ} (hN : 0 < N) :
    width M univ ≤
      width M (closedBall (0 : ℂ) (2*(dyadicRadius (endpointRadius M) N+1))) +
        ENNReal.ofReal (3 * Real.pi / (N : ℝ)) := by
  let R := dyadicRadius (endpointRadius M) N
  have hRpos : 0 < R := dyadicRadius_pos (endpointRadius_pos M) N
  have hbase : endpointRadius M ≤ R := by
    have hpow : (1 : ℝ) ≤ 2^N := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    simpa only [R, dyadicRadius, one_mul] using
      mul_le_mul_of_nonneg_right hpow (endpointRadius_pos M).le
  have hl : |M.left| ≤ R := by
    apply le_trans _ hbase
    dsimp [endpointRadius]
    linarith [abs_nonneg M.firstLo, abs_nonneg M.firstHi, abs_nonneg M.right]
  have hr : |M.right| ≤ R := by
    apply le_trans _ hbase
    dsimp [endpointRadius]
    linarith [abs_nonneg M.left, abs_nonneg M.firstLo, abs_nonneg M.firstHi]
  apply iSup₂_le
  intro Γ hΓ
  obtain ⟨Δ, hΔ, hretain⟩ := ChildSlitCompression.exists_compressed_wave M hΓ R hRpos hl hr
  exact (lamination_cutoff hΓ hN).trans
    (add_le_add ((modulus_mono hretain).trans (modulus_le_width hΔ)) le_rfl)

def distortion (E r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1-E/r)⁻¹)^2 * (1+E/r)^2)

private theorem distortion_eq {E r : ℝ} {L K : ℝ≥0}
    (hL : (L : ℝ) = 1+E/r) (hK : (K : ℝ) = (1-E/r)⁻¹) :
    distortion E r = (K : ℝ≥0∞)^2 * (L : ℝ≥0∞)^2 := by
  rw [distortion, ← hL, ← hK, ENNReal.ofReal_mul (sq_nonneg _)]
  have he (x : ℝ≥0) : ENNReal.ofReal ((x : ℝ)^2) = (x : ℝ≥0∞)^2 := by
    calc
      ENNReal.ofReal ((x : ℝ)^2) = ENNReal.ofReal (x : ℝ)^2 :=
        ENNReal.ofReal_pow x.property 2
      _ = (x : ℝ≥0∞)^2 := congrArg (fun t : ℝ≥0∞ => t^(2 : ℕ))
        (ENNReal.ofReal_coe_nnreal (p := x))
  rw [he K, he L]

/-- Upper semicontinuity follows by transporting every actual leaf into
the limiting plane slit.  Only the explicitly constructed finite-mark
motion appears in the assumptions. -/
theorem width_small_marks_upper (M A : ChildMarking) {r : ℝ}
    (hr : 0 < r)
    (hsep : ∀ i j, i ≠ j → r ≤ |markCoords M i-markCoords M j|)
    (hsmall : cutError (markCoords M) (markCoords A) < r) (D : Set ℂ) :
    width A D ≤ distortion (cutError (markCoords M) (markCoords A)) r * width M univ := by
  let E := cutError (markCoords M) (markCoords A)
  let h := cutOrderIso (markCoords M) (markCoords A) hr hsmall
  have hE0 : 0 ≤ E := cutError_nonneg _ _
  let L : ℝ≥0 := ⟨1+E/r, add_nonneg zero_le_one (div_nonneg hE0 hr.le)⟩
  let K : ℝ≥0 := ⟨(1-E/r)⁻¹, inv_nonneg.mpr
    (sub_nonneg.mpr ((div_lt_one hr).2 hsmall).le)⟩
  have hL : LipschitzWith L (horizontal h) :=
    cutHorizontal_lipschitz _ _ hr hsmall
  have hK : LipschitzWith K (horizontal h).symm :=
    cutHorizontal_inverse_lipschitz _ _ hr hsmall
  have hL0 : L ≠ 0 := by
    apply ne_of_gt
    change 0 < 1+E/r
    exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hE0 hr.le)
  have hK0 : K ≠ 0 := by
    apply ne_of_gt
    change 0 < (1-E/r)⁻¹
    exact inv_pos.mpr (sub_pos.mpr ((div_lt_one hr).2 hsmall))
  have hmap : M.map h = A :=
    marking_map_eq (cutOrderIso_marks _ _ hr hsmall hsep)
  have hw := width_map_le_mul_width M h hL hK hL0 hK0 (D := univ) (E := D) (subset_univ _)
  rw [hmap] at hw
  rw [distortion_eq (L := L) (K := K) rfl rfl]
  exact hw

/-- The lower comparison retains all bounded leaves and then transports
their entire traces.  The disk margin comes from a proved displacement
bound for the explicit finite-mark map. -/
theorem width_small_marks_lower (M A : ChildMarking) {r R B : ℝ}
    (hr : 0 < r)
    (hsep : ∀ i j, i ≠ j → r ≤ |markCoords M i-markCoords M j|)
    (hsmall : cutError (markCoords M) (markCoords A) < r)
    (hR : R + cutError (markCoords M) (markCoords A) < B) :
    width M (closedBall (0 : ℂ) R) ≤
      distortion (cutError (markCoords M) (markCoords A)) r * width A (ball (0 : ℂ) B) := by
  let E := cutError (markCoords M) (markCoords A)
  let h := cutOrderIso (markCoords M) (markCoords A) hr hsmall
  have hE0 : 0 ≤ E := cutError_nonneg _ _
  let L : ℝ≥0 := ⟨1+E/r, add_nonneg zero_le_one (div_nonneg hE0 hr.le)⟩
  let K : ℝ≥0 := ⟨(1-E/r)⁻¹, inv_nonneg.mpr
    (sub_nonneg.mpr ((div_lt_one hr).2 hsmall).le)⟩
  have hL : LipschitzWith L (horizontal h) :=
    cutHorizontal_lipschitz _ _ hr hsmall
  have hK : LipschitzWith K (horizontal h).symm :=
    cutHorizontal_inverse_lipschitz _ _ hr hsmall
  have hL0 : L ≠ 0 := by
    apply ne_of_gt
    change 0 < 1+E/r
    exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hE0 hr.le)
  have hK0 : K ≠ 0 := by
    apply ne_of_gt
    change 0 < (1-E/r)⁻¹
    exact inv_pos.mpr (sub_pos.mpr ((div_lt_one hr).2 hsmall))
  have hmap : M.map h = A :=
    marking_map_eq (cutOrderIso_marks _ _ hr hsmall hsep)
  have hDE : horizontal h '' closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) B := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_ball, dist_zero_right]
    have hzR : ‖z‖ ≤ R := by simpa using hz
    have hdisp := cutHorizontal_displacement (markCoords M) (markCoords A) hr hsmall z
    have htri : ‖horizontal h z‖ ≤ ‖horizontal h z-z‖ + ‖z‖ := by
      simpa only [dist_eq_norm, sub_zero] using dist_triangle (horizontal h z) z (0 : ℂ)
    linarith
  have hw := width_le_mul_width M h hL hK hL0 hK0 hDE
  rw [hmap] at hw
  rw [distortion_eq (L := L) (K := K) rfl rfl]
  exact hw

theorem width_tendsto_of_source_exhaustion (M : ChildMarking) (A : ℕ → ChildMarking)
    (R : ℕ → ℝ) (D : ℕ → Set ℂ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j, i ≠ j → r ≤ |markCoords M i-markCoords M j|)
    (hmarks : ∀ i, Tendsto (fun n => markCoords (A n) i) atTop (𝓝 (markCoords M i)))
    (hR : Tendsto R atTop atTop)
    (hsource : ∀ n, ball (0 : ℂ) (R n) ⊆ D n) :
    Tendsto (fun n => width (A n) (D n)) atTop (𝓝 (width M univ)) := by
  let E : ℕ → ℝ := fun n => cutError (markCoords M) (markCoords (A n))
  have hE : Tendsto E atTop (𝓝 0) := by
    have hi (i : Fin 6) :
        Tendsto (fun n => |markCoords (A n) i-markCoords M i|) atTop (𝓝 0) := by
      simpa using ((hmarks i).sub_const (markCoords M i)).abs
    simpa [E, cutError] using tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hs : ∀ᶠ n in atTop, E n < r := (tendsto_order.mp hE).2 r hr
  have hC : Tendsto (fun n => distortion (E n) r) atTop (𝓝 1) := by
    have hf : Tendsto (fun n => E n/r) atTop (𝓝 0) := by
      simpa using hE.div_const r
    have hi : Tendsto (fun n => (1-E n/r)⁻¹) atTop (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.sub hf).inv₀ (by norm_num : (1 : ℝ)-0 ≠ 0)
    have hp : Tendsto (fun n => 1+E n/r) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add hf
    simpa [distortion, Function.comp_def] using ENNReal.continuous_ofReal.tendsto (1 : ℝ) |>.comp
      (by simpa using (hi.pow 2).mul (hp.pow 2))
  let e : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (3*Real.pi/(j+1 : ℕ))
  have he : Tendsto e atTop (𝓝 0) := by
    have hnat : Tendsto (fun j : ℕ => (j+1 : ℝ)) atTop atTop :=
      by simpa [Function.comp_def] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    have hd : Tendsto (fun j : ℕ => 3*Real.pi/(j+1 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnat
    simpa [e, Function.comp_def] using ENNReal.continuous_ofReal.tendsto (0 : ℝ) |>.comp hd
  apply SlitWaveLimit.tendsto_of_uniform_cutoff hC he
  · filter_upwards [hs] with n hn
    exact width_small_marks_upper M (A n) hr hsep hn _
  · intro j
    let B := 2*(dyadicRadius (endpointRadius M) (j+1)+1)
    filter_upwards [hs, (tendsto_order.mp hE).2 1 (by norm_num),
      hR.eventually_gt_atTop (B+1)] with n hn hEn hRn
    have hfit : B+E n < R n := by linarith
    have hl := width_small_marks_lower M (A n) hr hsep hn hfit
    have hdomain := width_mono (A n) (hsource n)
    exact (width_cutoff M (Nat.succ_pos j)).trans
      (add_le_add (hl.trans (mul_le_mul_left' hdomain _)) le_rfl)

end
end ChildSlitLimit
