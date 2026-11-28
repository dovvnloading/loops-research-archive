import SlitDiskMarking
import SlitLocalReflection
import SlitCubicUpperBound
import SlitCubicBoundaryRange

/-!
# The actual finite-disk parent calibration

The cubic potential in squared Cayley coordinates calibrates every
continuous simple parent in the disk. The density is the actual conformal
pullback of the full-plane cubic density, so its area is bounded by the
exact transformed period ratio.
-/

namespace SlitDiskUpperBound

open Set Filter MeasureTheory MarkedSlitTransport
open SlitCubicCalibration SlitCubicBoundary SlitCubicBoundaryRange
open SlitPotentialReflection SlitPotentialLength SlitDiskMarking
open scoped Topology ENNReal
noncomputable section

theorem disk_eq_ball (R : ℝ) : SlitDiskCayley.disk R = Metric.ball (0 : ℂ) R := by
  ext z
  simp only [SlitDiskCayley.disk, mem_setOf_eq, Metric.mem_ball, dist_zero_right]

theorem norm_fold (z : ℂ) : ‖fold z‖ = ‖z‖ := by
  simpa using norm_fold_sub_real z 0

theorem fold_mem_disk {R : ℝ} {z : ℂ} (hz : z ∈ SlitDiskCayley.disk R) :
    fold z ∈ SlitDiskCayley.disk R := by
  simpa only [SlitDiskCayley.disk, mem_setOf_eq, norm_fold] using hz

private theorem fold_eq_conj {z : ℂ} (hz : z.im ≤ 0) : fold z = starRingEnd ℂ z := by
  apply Complex.ext
  · rfl
  · simp only [fold_im, Complex.conj_im, abs_of_nonpos hz]

private theorem map_im_nonneg {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ SlitDiskCayley.disk R) (him : 0 ≤ z.im) :
    0 ≤ (SlitDiskCayley.map R z).im := by
  rcases him.eq_or_lt with him | him
  · have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him.symm]
    rw [he, SlitDiskCayley.map_ofReal]
    simp
  · exact (SlitDiskCayley.map_im_pos hR hz him).le

theorem map_fold {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ SlitDiskCayley.disk R) :
    SlitDiskCayley.map R (fold z) = fold (SlitDiskCayley.map R z) := by
  by_cases him : 0 ≤ z.im
  · rw [fold_eq_self him, fold_eq_self (map_im_nonneg hR hz him)]
  · have him' := (lt_of_not_ge him).le
    have hconj : starRingEnd ℂ z ∈ SlitDiskCayley.disk R := by
      simpa only [SlitDiskCayley.disk, mem_setOf_eq, Complex.norm_conj] using hz
    have hmi := map_im_nonneg hR hconj (by simpa only [Complex.conj_im] using neg_nonneg.mpr him')
    rw [SlitDiskCayley.map_conj, Complex.conj_im] at hmi
    rw [fold_eq_conj him', SlitDiskCayley.map_conj, fold_eq_conj (neg_nonneg.mp hmi)]

private theorem ends_mem_disk {R : ℝ} (M : Marking) (hleft : -R < M.left)
    (hright : M.right < R) {z : ℂ} (hz : M.ends z) : z ∈ SlitDiskCayley.disk R := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz.1]
  rw [he]
  exact SlitDiskCayley.ofReal_mem_disk
    ⟨(hleft.trans M.left_lt_first).trans hz.2.1,
      hz.2.2.trans (M.second_lt_right.trans hright)⟩

theorem trace_subset_disk {R : ℝ} {M : Marking} (hleft : -R < M.left)
    (hright : M.right < R) {γ : Curve} (hγ : ParentLeaf M (SlitDiskCayley.disk R) γ) :
    trace γ ⊆ SlitDiskCayley.disk R := by
  rintro z ⟨t, rfl⟩
  by_cases ht0 : t = initial
  · rw [ht0]
    exact ends_mem_disk M hleft hright hγ.first_end
  by_cases ht1 : t = terminal
  · rw [ht1]
    exact ends_mem_disk M hleft hright hγ.last_end
  apply hγ.inside t
  constructor
  · exact lt_of_le_of_ne t.property.1 (by intro he; exact ht0 (Subtype.ext he.symm))
  · exact lt_of_le_of_ne t.property.2 (by intro he; exact ht1 (Subtype.ext he))

private theorem trace_ne_pole {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) {p : ℝ} (hpl : M.left ≤ p) (hpr : p ≤ M.right)
    (hpe : p ≤ M.first ∨ M.second ≤ p) {z : ℂ} (hz : z ∈ trace γ) : z ≠ (p : ℂ) := by
  rintro rfl
  obtain ⟨t, ht⟩ := hz
  by_cases ht0 : t = initial
  · rw [ht0] at ht
    have h1 := hγ.first_end.2.1
    have h2 := hγ.first_end.2.2
    rw [ht] at h1 h2
    simp only [Complex.ofReal_re] at h1 h2
    rcases hpe with h | h <;> linarith
  by_cases ht1 : t = terminal
  · rw [ht1] at ht
    have h1 := hγ.last_end.2.1
    have h2 := hγ.last_end.2.2
    rw [ht] at h1 h2
    simp only [Complex.ofReal_re] at h1 h2
    rcases hpe with h | h <;> linarith
  have hti : t ∈ parameterInterior := by
    constructor
    · exact lt_of_le_of_ne t.property.1 (by intro he; exact ht0 (Subtype.ext he.symm))
    · exact lt_of_le_of_ne t.property.2 (by intro he; exact ht1 (Subtype.ext he))
  apply hγ.avoids t hti
  rw [ht]
  exact ⟨rfl, hpl, hpr⟩

private theorem map_fold_ne_realMap {R : ℝ} (hR : 0 < R) {z : ℂ} {p : ℝ}
    (hz : z ∈ SlitDiskCayley.disk R) (hp : p ∈ Ioo (-R) R) (hne : z ≠ (p : ℂ)) :
    SlitDiskCayley.map R (fold z) ≠ (SlitDiskCayley.realMap R p : ℂ) := by
  intro he
  have hm : SlitDiskCayley.map R (fold z) = SlitDiskCayley.map R (p : ℂ) :=
    he.trans (SlitDiskCayley.map_ofReal R p).symm
  have hf := SlitDiskCayley.map_injOn hR (fold_mem_disk hz) (SlitDiskCayley.ofReal_mem_disk hp) hm
  apply hne
  have hn : ‖z - (p : ℂ)‖ = 0 := by rw [← norm_fold_sub_real, hf, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem trace_map_fold_ne_poles {R : ℝ} (hR : 0 < R) {M : Marking}
    (hleft : -R < M.left) (hright : M.right < R) {γ : Curve}
    (hγ : ParentLeaf M (SlitDiskCayley.disk R) γ) {z : ℂ} (hz : z ∈ trace γ) :
    SlitDiskCayley.map R (fold z) ≠ ((transformedMarking hR M hleft hright).left : ℂ) ∧
    SlitDiskCayley.map R (fold z) ≠ ((transformedMarking hR M hleft hright).first : ℂ) ∧
    SlitDiskCayley.map R (fold z) ≠ ((transformedMarking hR M hleft hright).second : ℂ) := by
  have hzd := trace_subset_disk hleft hright hγ hz
  have hlr := M.left_lt_first.trans (M.first_lt_second.trans M.second_lt_right)
  exact ⟨map_fold_ne_realMap hR hzd (marking_left_mem_Ioo M hleft hright)
      (trace_ne_pole hγ le_rfl hlr.le (Or.inl M.left_lt_first.le) hz),
    map_fold_ne_realMap hR hzd (marking_first_mem_Ioo M hleft hright)
      (trace_ne_pole hγ M.left_lt_first.le (M.first_lt_second.trans M.second_lt_right).le
        (Or.inl le_rfl) hz),
    map_fold_ne_realMap hR hzd (marking_second_mem_Ioo M hleft hright)
      (trace_ne_pole hγ (M.left_lt_first.trans M.first_lt_second).le M.second_lt_right.le
        (Or.inr le_rfl) hz)⟩

def primitive (N : Marking) (R : ℝ) (z : ℂ) : ℂ :=
  tail N.left N.first N.second (SlitDiskCayley.map R z)

def primitiveDerivative (N : Marking) {R : ℝ} (hR : 0 < R) (z : ℂ) : ℂ :=
  -differential N.left N.first N.second (SlitDiskCayley.map R z) *
    (SlitDiskCayley.conformalChart hR).derivative z

def potential (N : Marking) (R : ℝ) (z : ℂ) : ℝ :=
  (primitive N R (fold z)).re / period N.left N.first N.second

def slope (N : Marking) {R : ℝ} (hR : 0 < R) (z : ℂ) : ℝ :=
  ‖primitiveDerivative N hR (fold z)‖ / period N.left N.first N.second

def density (N : Marking) {R : ℝ} (hR : 0 < R) : ℂ → ℝ≥0∞ :=
  (SlitDiskCayley.conformalChart hR).pullDensity (SlitCubicAdmissible.density N)

theorem primitive_continuousOn (N : Marking) {R : ℝ} (hR : 0 < R) :
    ContinuousOn (primitive N R) (SlitDiskCayley.disk R ∩ {z | 0 ≤ z.im}) := by
  apply (tail_continuousOn_closedUpper (realDensity_integrable N.left_lt_first N.first_lt_second)).comp
    ((SlitDiskCayley.map_differentiableOn hR).continuousOn.mono inter_subset_left)
  intro z hz
  exact map_im_nonneg hR hz.1 hz.2

theorem primitive_hasDerivAt (N : Marking) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ SlitDiskCayley.disk R) (him : 0 < z.im) :
    HasDerivAt (primitive N R) (primitiveDerivative N hR z) z := by
  exact (tail_hasDerivAt (realDensity_integrable N.left_lt_first N.first_lt_second)
    (SlitDiskCayley.map_im_pos hR hz him)).comp z
      ((SlitDiskCayley.conformalChart hR).hasDeriv z hz)

theorem primitiveDerivative_continuousAt (N : Marking) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ SlitDiskCayley.disk R) (him : 0 ≤ z.im)
    (ha : SlitDiskCayley.map R z ≠ (N.left : ℂ))
    (hb : SlitDiskCayley.map R z ≠ (N.first : ℂ))
    (hc : SlitDiskCayley.map R z ≠ (N.second : ℂ)) :
    ContinuousAt (primitiveDerivative N hR) z := by
  have hmap := (SlitDiskCayley.map_hasDerivAt hR hz).continuousAt
  have hderiv := (SlitDiskCayley.conformalChart hR).derivative_continuous.continuousAt
    ((SlitDiskCayley.disk_open R).mem_nhds hz)
  exact (((differential_continuousAt (map_im_nonneg hR hz him) ha hb hc).comp hmap).neg).mul hderiv

theorem derivative_norm_fold {R : ℝ} (hR : 0 < R) (z : ℂ) :
    ‖(SlitDiskCayley.conformalChart hR).derivative (fold z)‖ =
      ‖(SlitDiskCayley.conformalChart hR).derivative z‖ := by
  by_cases him : 0 ≤ z.im
  · rw [fold_eq_self him]
  · rw [fold_eq_conj (lt_of_not_ge him).le]
    have hc : (SlitDiskCayley.conformalChart hR).derivative (starRingEnd ℂ z) =
        starRingEnd ℂ ((SlitDiskCayley.conformalChart hR).derivative z) := by
      simp only [SlitDiskCayley.conformalChart_derivative]
      exact SlitDiskCayley.derivative_conj R z
    rw [hc, Complex.norm_conj]

theorem density_eq_half_slope (N : Marking) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ SlitDiskCayley.disk R) :
    density N hR z = (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (slope N hR z) := by
  unfold density CrestConformalModulus.ConformalChart.pullDensity
  rw [SlitDiskCayley.conformalChart_source, indicator_of_mem hz]
  simp only [SlitCubicAdmissible.density, SlitCubicAdmissible.slope,
    SlitDiskCayley.conformalChart_apply, CrestConformalModulus.ConformalChart.factor,
    slope, primitiveDerivative, norm_mul, norm_neg, derivative_norm_fold, map_fold hR hz]
  rw [mul_assoc, ← ENNReal.ofReal_mul
    (div_nonneg (norm_nonneg _) (period_pos N.left_lt_first N.first_lt_second).le)]
  congr 2
  ring

theorem potential_on_ends {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) {z : ℂ} (hz : M.ends z) :
    potential (transformedMarking hR M hleft hright) R z = 1 := by
  let N := transformedMarking hR M hleft hright
  have hx : z.re ∈ Ioo (-R) R :=
    ⟨(hleft.trans M.left_lt_first).trans hz.2.1,
      hz.2.2.trans (M.second_lt_right.trans hright)⟩
  have hb : N.first < SlitDiskCayley.realMap R z.re :=
    SlitDiskCayley.realMap_strictMonoOn hR (marking_first_mem_Ioo M hleft hright) hx hz.2.1
  have hc : SlitDiskCayley.realMap R z.re < N.second :=
    SlitDiskCayley.realMap_strictMonoOn hR hx (marking_second_mem_Ioo M hleft hright) hz.2.2
  have he : fold z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz.1]
  change potential N R z = 1
  unfold potential primitive
  rw [he, SlitDiskCayley.map_ofReal, tail_re_gap N.left_lt_first N.first_lt_second hb.le hc.le]
  exact div_self (period_pos N.left_lt_first N.first_lt_second).ne'

theorem potential_on_left {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) {z : ℂ}
    (hz : z ∈ SlitDiskCayley.disk R) (him : z.im = 0) (hre : z.re ≤ M.left) :
    potential (transformedMarking hR M hleft hright) R z = 0 := by
  let N := transformedMarking hR M hleft hright
  have hx : z.re ∈ Ioo (-R) R :=
    abs_lt.mp ((Complex.abs_re_le_norm z).trans_lt hz)
  have hx' : SlitDiskCayley.realMap R z.re ≤ N.left :=
    (SlitDiskCayley.realMap_strictMonoOn hR).monotoneOn hx
      (marking_left_mem_Ioo M hleft hright) hre
  have he : fold z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
  change potential N R z = 0
  unfold potential primitive
  rw [he, SlitDiskCayley.map_ofReal, tail_re_left N.left_lt_first N.first_lt_second hx', zero_div]

/-- Every literal parent in the finite disk has unit length in the
conformally pulled cubic metric. -/
theorem density_parent_length {R : ℝ} (hR : 0 < R) {M : Marking}
    (hleft : -R < M.left) (hright : M.right < R) {γ : Curve}
    (hγ : ParentLeaf M (SlitDiskCayley.disk R) γ) :
    1 ≤ SlitWaveModulus.lineLength (density (transformedMarking hR M hleft hright) hR) (trace γ) := by
  let N := transformedMarking hR M hleft hright
  have hB := period_pos N.left_lt_first N.first_lt_second
  have htrace := trace_subset_disk hleft hright hγ
  have hcont : ∀ z ∈ trace γ, ContinuousAt (primitiveDerivative N hR) (fold z) := by
    intro z hz
    obtain ⟨ha, hb, hc⟩ := trace_map_fold_ne_poles hR hleft hright hγ hz
    exact primitiveDerivative_continuousAt N hR (fold_mem_disk (htrace hz))
      (fold_im_nonneg z) ha hb hc
  have hg : ∀ z ∈ trace γ, ContinuousAt (slope N hR) z := by
    intro z hz
    exact (((hcont z hz).comp fold_continuous.continuousAt).norm).div_const _
  have hp : ∀ z ∈ trace γ, 0 < slope N hR z := by
    intro z hz
    obtain ⟨ha, hb, hc⟩ := trace_map_fold_ne_poles hR hleft hright hγ hz
    have hzd := fold_mem_disk (htrace hz)
    have hmi := map_im_nonneg hR hzd (fold_im_nonneg z)
    apply div_pos _ hB
    apply norm_pos_iff.mpr
    apply mul_ne_zero
    · exact neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (mul_ne_zero
        (upperRoot_ne_zero hmi ha) (upperRoot_ne_zero hmi hb)) (upperRoot_ne_zero hmi hc)))
    · exact (SlitDiskCayley.conformalChart hR).derivative_ne_zero _ hzd
  have hloc : LocalSlopeBound (potential N R) (slope N hR) (trace γ) := by
    exact SlitLocalReflection.localSlopeBound_fold_re_on (SlitDiskCayley.disk_open R)
      (fun z hz => fold_mem_disk (htrace hz)) (primitive_continuousOn N hR)
      (fun _ hz him => primitive_hasDerivAt N hR hz him) hcont hB
  obtain ⟨t, ht, him, hre⟩ := SlitLeftCrossing.parentLeaf_exists_left_real hγ
  have hlen := one_le_half_density_length_of_simple_excursion hγ.simple hg hp hloc
    (potential_on_ends hR M hleft hright hγ.first_end)
    (potential_on_ends hR M hleft hright hγ.last_end) ht
    (potential_on_left hR M hleft hright (htrace ⟨t, rfl⟩) him hre.le)
  apply hlen.trans_eq
  apply setLIntegral_congr_fun (trace_isCompact γ).measurableSet
  intro z hz
  exact (density_eq_half_slope N hR (htrace hz)).symm

theorem density_admissible {R : ℝ} (hR : 0 < R) {M : Marking}
    (hleft : -R < M.left) (hright : M.right < R) {Γ : Set Curve}
    (hΓ : ParentWave M (SlitDiskCayley.disk R) Γ) :
    SlitWaveModulus.Admissible (traces Γ) (density (transformedMarking hR M hleft hright) hR) := by
  refine ⟨(SlitDiskCayley.conformalChart hR).pullDensity_measurable
    (SlitCubicAdmissible.density_measurable _), ?_⟩
  rintro S ⟨γ, hγ, rfl⟩
  exact density_parent_length hR hleft hright (hΓ.leaf γ hγ)

theorem density_area_le (N : Marking) {R : ℝ} (hR : 0 < R) :
    SlitWaveModulus.area (density N hR) ≤
      ENNReal.ofReal (height N.left N.first N.second / (2 * period N.left N.first N.second)) := by
  have he := (SlitDiskCayley.conformalChart hR).area_pull (SlitCubicAdmissible.density N)
  calc
    _ = ∫⁻ z in (SlitDiskCayley.conformalChart hR).homeomorph.target,
        (SlitCubicAdmissible.density N z)^2 := he
    _ ≤ SlitWaveModulus.area (SlitCubicAdmissible.density N) := setLIntegral_le_lintegral _ _
    _ = _ := SlitCubicUpperBound.density_area_exact N

/-- The all-parent finite-disk supremum is bounded by the exact cubic
periods of the three squared-Cayley-transformed cuts. -/
theorem width_le_period_ratio {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) :
    SlitWaveLimit.width M (Metric.ball (0 : ℂ) R) ≤
      ENNReal.ofReal
        (height (SlitDiskCayley.realMap R M.left) (SlitDiskCayley.realMap R M.first)
          (SlitDiskCayley.realMap R M.second) /
        (2 * period (SlitDiskCayley.realMap R M.left) (SlitDiskCayley.realMap R M.first)
          (SlitDiskCayley.realMap R M.second))) := by
  rw [← disk_eq_ball]
  apply le_trans ?_ (density_area_le (transformedMarking hR M hleft hright) hR)
  apply iSup₂_le
  intro Γ hΓ
  exact SlitWaveModulus.modulus_le_area (density_admissible hR hleft hright hΓ)

end
end SlitDiskUpperBound
