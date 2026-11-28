import SlitWaveModulus
import SlitWaveEscape
import MarkedSlitCompression
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Exhaustion of the complete marked parent supremum

The supremum is over all Borel simple laminations in the selected marked
relative class.  Truncation is by the entire trace of each leaf.  Thus no
chosen circular witness, optimizing lamination, or compactness of a space
of optimizers is used.
-/

namespace SlitWaveLimit

open Set Filter MeasureTheory Metric
open MarkedSlitTransport SlitWaveModulus SlitWaveEscape
open scoped ENNReal NNReal Topology

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def width (M : Marking) (D : Set ℂ) : ℝ≥0∞ :=
  ⨆ (Γ : Set Curve) (_ : ParentWave M D Γ), modulus (traces Γ)

theorem modulus_le_width {M : Marking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ParentWave M D Γ) : modulus (traces Γ) ≤ width M D :=
  le_iSup₂_of_le Γ hΓ le_rfl

theorem width_mono (M : Marking) {D E : Set ℂ} (hDE : D ⊆ E) :
    width M D ≤ width M E := by
  apply iSup₂_le
  intro Γ hΓ
  exact modulus_le_width (hΓ.mono hDE)

theorem traces_map (h : ℝ ≃o ℝ) (Γ : Set Curve) :
    traces (mapCurve h '' Γ) = transportFamily (horizontal h) (traces Γ) := by
  ext S
  constructor
  · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    exact ⟨trace γ, ⟨γ, hγ, rfl⟩, (trace_mapCurve h γ).symm⟩
  · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    exact ⟨mapCurve h γ, ⟨γ, hγ, rfl⟩, trace_mapCurve h γ⟩

/-- This inequality transports every lamination in the supremum.
Neither the existence nor the choice of an optimizer is required. -/
theorem width_le_mul_width (M : Marking) {D E : Set ℂ} (h : ℝ ≃o ℝ)
    {L K : ℝ≥0} (hL : LipschitzWith L (horizontal h))
    (hK : LipschitzWith K (horizontal h).symm)
    (hL0 : L ≠ 0) (hK0 : K ≠ 0) (hDE : horizontal h '' D ⊆ E) :
    width M D ≤ ((K : ℝ≥0∞)^2 * (L : ℝ≥0∞)^2) * width (M.map h) E := by
  apply iSup₂_le
  intro Γ hΓ
  have hm := modulus_le_mul_transport (horizontal h) hL hK hL0 hK0 (traces Γ)
  rw [← traces_map] at hm
  exact hm.trans (mul_le_mul_left' (modulus_le_width ((hΓ.map h).mono hDE)) _)

theorem trace_preconnected (γ : Curve) : IsPreconnected (trace γ) :=
  isPreconnected_range γ.continuous

def endpointRadius (M : Marking) : ℝ :=
  |M.left| + |M.first| + |M.second| + |M.right| + 1

theorem endpointRadius_pos (M : Marking) : 0 < endpointRadius M := by
  dsimp [endpointRadius]
  positivity

theorem first_end_norm_le {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) : ‖γ initial‖ ≤ endpointRadius M := by
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
  have hfa := neg_abs_le M.first
  have hsb := le_abs_self M.second
  constructor <;> dsimp [endpointRadius] <;>
    linarith [abs_nonneg M.left, abs_nonneg M.first,
      abs_nonneg M.second, abs_nonneg M.right]

/-- A common admissible density controls every discarded leaf, including
leaves with infinite arclength. No measurability of the discarded
leaf subfamily is assumed or needed for this modulus upper bound. -/
theorem discarded_modulus_le {M : Marking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ParentWave M D Γ) {N : ℕ} (hN : 0 < N) :
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

/-- Quantitative exhaustion of the modulus of any complete parent
lamination, uniformly over the lamination. -/
theorem lamination_cutoff {M : Marking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ParentWave M D Γ) {N : ℕ} (hN : 0 < N) :
    modulus (traces Γ) ≤
      modulus (traces (Γ ∩ boundedCurves (dyadicRadius (endpointRadius M) N))) +
        ENNReal.ofReal (3 * Real.pi / (N : ℝ)) := by
  rw [traces_decompose Γ (dyadicRadius (endpointRadius M) N)]
  exact (modulus_union_le _ _).trans
    (add_le_add le_rfl (discarded_modulus_le hΓ hN))

/-- The whole limiting supremum is approximated by complete bounded
laminations. The entire Wave is compressed, so no measurable selection
of a retained subfamily is assumed. -/
theorem width_cutoff (M : Marking) {N : ℕ} (hN : 0 < N) :
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
    linarith [abs_nonneg M.first, abs_nonneg M.second, abs_nonneg M.right]
  have hr : |M.right| ≤ R := by
    apply le_trans _ hbase
    dsimp [endpointRadius]
    linarith [abs_nonneg M.left, abs_nonneg M.first, abs_nonneg M.second]
  apply iSup₂_le
  intro Γ hΓ
  obtain ⟨Δ, hΔ, hretain⟩ := exists_compressed_wave M hΓ R hRpos hl hr
  exact (lamination_cutoff hΓ hN).trans
    (add_le_add ((modulus_mono hretain).trans (modulus_le_width hΔ)) le_rfl)

/-- A varying multiplicative error tending to one, together with a
uniform exhaustion error tending to zero, forces convergence in the
extended nonnegative reals.  Finiteness and optimizer attainment are not
needed for this limit passage. -/
theorem tendsto_of_uniform_cutoff {P : ℕ → ℝ≥0∞} {Pinf : ℝ≥0∞}
    {C e : ℕ → ℝ≥0∞} (hC : Tendsto C atTop (𝓝 1))
    (he : Tendsto e atTop (𝓝 0))
    (hupper : ∀ᶠ n in atTop, P n ≤ C n * Pinf)
    (hlower : ∀ j : ℕ, ∀ᶠ n in atTop, Pinf ≤ C n * P n + e j) :
    Tendsto P atTop (𝓝 Pinf) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have he' : Tendsto (fun j => a + e j) atTop (𝓝 a) := by
      simpa using tendsto_const_nhds.add he
    obtain ⟨j, hj⟩ := ((tendsto_order.mp he').2 Pinf ha).exists
    have hCa : Tendsto (fun n => C n * a + e j) atTop (𝓝 (a + e j)) := by
      simpa using (ENNReal.Tendsto.mul_const hC (Or.inl one_ne_zero)).add_const (e j)
    filter_upwards [hlower j, (tendsto_order.mp hCa).2 Pinf hj] with n hn hlt
    by_contra hn'
    have hna : P n ≤ a := not_lt.mp hn'
    exact (not_lt_of_ge (hn.trans (add_le_add (mul_le_mul_left' hna _) le_rfl))) hlt
  · intro b hb
    have hCp : Tendsto (fun n => C n * Pinf) atTop (𝓝 Pinf) := by
      simpa using ENNReal.Tendsto.mul_const hC (Or.inl one_ne_zero)
    filter_upwards [hupper, (tendsto_order.mp hCp).2 b hb] with n hn hlt
    exact hn.trans_lt hlt

def markCoords (M : Marking) : Fin 4 → ℝ :=
  ![M.left, M.first, M.second, M.right]

private theorem marking_ext {M A : Marking}
    (hl : M.left = A.left) (ha : M.first = A.first)
    (hb : M.second = A.second) (hr : M.right = A.right) : M = A := by
  cases M
  cases A
  simp_all

theorem marking_map_eq {M A : Marking} {h : ℝ ≃o ℝ}
    (hh : ∀ i, h (markCoords M i) = markCoords A i) : M.map h = A := by
  apply marking_ext
  · exact hh 0
  · exact hh 1
  · exact hh 2
  · exact hh 3

theorem marking_map_symm (M : Marking) (h : ℝ ≃o ℝ) :
    (M.map h).map h.symm = M := by
  apply marking_ext <;> simp [Marking.map]

private theorem width_map_le_mul_width (M : Marking) (h : ℝ ≃o ℝ)
    {L K : ℝ≥0} (hL : LipschitzWith L (horizontal h))
    (hK : LipschitzWith K (horizontal h).symm)
    (hL0 : L ≠ 0) (hK0 : K ≠ 0) (D : Set ℂ) :
    width (M.map h) D ≤ ((K : ℝ≥0∞)^2*(L : ℝ≥0∞)^2)*width M univ := by
  have hK' : LipschitzWith K (horizontal h.symm) := by
    rw [horizontal_symm h]
    exact hK
  have hL' : LipschitzWith L (horizontal h.symm).symm := by
    rw [horizontal_symm h, Homeomorph.symm_symm]
    exact hL
  have hw := width_le_mul_width (M.map h) h.symm hK' hL' hK0 hL0
    (D := D) (E := univ) (subset_univ _)
  rw [marking_map_symm M h] at hw
  simpa only [mul_comm] using hw

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
theorem width_small_marks_upper (M A : Marking) {r : ℝ}
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
  have hw := width_map_le_mul_width M h hL hK hL0 hK0 D
  rw [hmap] at hw
  rw [distortion_eq (L := L) (K := K) rfl rfl]
  exact hw

/-- The lower comparison retains all bounded leaves and then transports
their entire traces.  The disk margin comes from a proved displacement
bound for the explicit finite-mark map. -/
theorem width_small_marks_lower (M A : Marking) {r R B : ℝ}
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

/-- Convergence of the complete marked parent optimum under convergence
of all four inner marks and exhaustion of the outer disks.  The modulus,
the full Borel leaf class, the transport, and the escaping-family error
have all been defined and proved above. -/
theorem width_tendsto_of_mark_convergence (M : Marking) (A : ℕ → Marking)
    (R : ℕ → ℝ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j, i ≠ j → r ≤ |markCoords M i-markCoords M j|)
    (hmarks : ∀ i, Tendsto (fun n => markCoords (A n) i) atTop (𝓝 (markCoords M i)))
    (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => width (A n) (ball (0 : ℂ) (R n))) atTop (𝓝 (width M univ)) := by
  let E : ℕ → ℝ := fun n => cutError (markCoords M) (markCoords (A n))
  have hE : Tendsto E atTop (𝓝 0) := by
    have hi (i : Fin 4) :
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
  apply tendsto_of_uniform_cutoff hC he
  · filter_upwards [hs] with n hn
    exact width_small_marks_upper M (A n) hr hsep hn _
  · intro j
    let B := 2*(dyadicRadius (endpointRadius M) (j+1)+1)
    filter_upwards [hs, (tendsto_order.mp hE).2 1 (by norm_num),
      hR.eventually_gt_atTop (B+1)] with n hn hEn hRn
    have hfit : B+E n < R n := by linarith
    have hl := width_small_marks_lower M (A n) hr hsep hn hfit
    exact (width_cutoff M (Nat.succ_pos j)).trans (add_le_add hl le_rfl)

end
end SlitWaveLimit
