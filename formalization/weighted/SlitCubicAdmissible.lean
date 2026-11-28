import SlitCubicBoundary
import SlitPotentialReflection
import SlitLeftCrossing
import SlitWaveLimit

/-!
# The actual cubic metric calibrates every marked parent

The differential, boundary values, reflected local slope, and forced
left crossing are assembled here for the archive's literal ParentLeaf.
No regularity of leaves and no extremizing foliation are assumed.
-/

namespace SlitCubicAdmissible

open Set Filter MeasureTheory MarkedSlitTransport SlitCubicCalibration
  SlitCubicBoundary SlitPotentialReflection SlitPotentialLength SlitWaveModulus
open scoped Topology ENNReal
noncomputable section

def potential (M : Marking) (z : ℂ) : ℝ :=
  (tail M.left M.first M.second (fold z)).re / period M.left M.first M.second

def slope (M : Marking) (z : ℂ) : ℝ :=
  ‖differential M.left M.first M.second (fold z)‖ / period M.left M.first M.second

def density (M : Marking) (z : ℂ) : ℝ≥0∞ := (2:ℝ≥0∞)⁻¹ * ENNReal.ofReal (slope M z)

theorem density_measurable (M : Marking) : Measurable (density M) := by
  exact measurable_const.mul
    (((differential_measurable M.left M.first M.second).comp
      fold_continuous.measurable).norm.div_const _).ennreal_ofReal

private theorem trace_ne_pole {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) {p : ℝ} (hpl : M.left ≤ p) (hpr : p ≤ M.right)
    (hpe : p ≤ M.first ∨ M.second ≤ p) {z : ℂ} (hz : z ∈ trace γ) : z ≠ (p:ℂ) := by
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
    · exact lt_of_le_of_ne t.property.1 (by intro h; exact ht0 (Subtype.ext h.symm))
    · exact lt_of_le_of_ne t.property.2 (by intro h; exact ht1 (Subtype.ext h))
  apply hγ.avoids t hti
  rw [ht]
  exact ⟨rfl,hpl,hpr⟩

private theorem fold_ne_real {z : ℂ} {p : ℝ} (h : z ≠ (p:ℂ)) : fold z ≠ (p:ℂ) := by
  intro he
  apply h
  have hn : ‖z-(p:ℂ)‖ = 0 := by rw [← norm_fold_sub_real,he,sub_self,norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

private theorem trace_fold_ne_poles {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) {z : ℂ} (hz : z ∈ trace γ) :
    fold z ≠ (M.left:ℂ) ∧ fold z ≠ (M.first:ℂ) ∧ fold z ≠ (M.second:ℂ) := by
  have hlr : M.left < M.right :=
    M.left_lt_first.trans (M.first_lt_second.trans M.second_lt_right)
  refine ⟨fold_ne_real (trace_ne_pole hγ le_rfl hlr.le (Or.inl M.left_lt_first.le) hz),
    fold_ne_real (trace_ne_pole hγ M.left_lt_first.le
      (M.first_lt_second.trans M.second_lt_right).le (Or.inl le_rfl) hz),
    fold_ne_real (trace_ne_pole hγ (M.left_lt_first.trans M.first_lt_second).le
      M.second_lt_right.le (Or.inr le_rfl) hz)⟩

theorem potential_on_ends {M : Marking} {z : ℂ} (hz : M.ends z) : potential M z = 1 := by
  have he : fold z = (z.re:ℂ) := by apply Complex.ext <;> simp [hz.1]
  unfold potential
  rw [he,tail_re_gap M.left_lt_first M.first_lt_second hz.2.1.le hz.2.2.le]
  exact div_self (period_pos M.left_lt_first M.first_lt_second).ne'

theorem potential_left {M : Marking} {z : ℂ} (hi : z.im = 0) (hr : z.re ≤ M.left) :
    potential M z = 0 := by
  have he : fold z = (z.re:ℂ) := by apply Complex.ext <;> simp [hi]
  unfold potential
  rw [he,tail_re_left M.left_lt_first M.first_lt_second hr,zero_div]

theorem density_parent_length {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) : 1 ≤ lineLength (density M) (trace γ) := by
  have hi := realDensity_integrable M.left_lt_first M.first_lt_second
  have hB := period_pos M.left_lt_first M.first_lt_second
  have hg : ∀ z ∈ trace γ, ContinuousAt (slope M) z := by
    intro z hz
    obtain ⟨ha,hb,hc⟩ := trace_fold_ne_poles hγ hz
    exact (((differential_continuousAt (fold_im_nonneg z) ha hb hc).comp
      fold_continuous.continuousAt).norm).div_const _
  have hp : ∀ z ∈ trace γ, 0 < slope M z := by
    intro z hz
    obtain ⟨ha,hb,hc⟩ := trace_fold_ne_poles hγ hz
    apply div_pos _ hB
    apply norm_pos_iff.mpr
    exact inv_ne_zero (mul_ne_zero (mul_ne_zero
      (upperRoot_ne_zero (fold_im_nonneg z) ha)
      (upperRoot_ne_zero (fold_im_nonneg z) hb))
      (upperRoot_ne_zero (fold_im_nonneg z) hc))
  have hloc : LocalSlopeBound (potential M) (slope M) (trace γ) := by
    have hh := localSlopeBound_fold_re (F := tail M.left M.first M.second)
      (F' := fun z => -differential M.left M.first M.second z)
      (tail_continuousOn_closedUpper hi)
      (fun z hz => tail_hasDerivAt hi hz)
      (S := trace γ) (by
        intro z hz
        obtain ⟨ha,hb,hc⟩ := trace_fold_ne_poles hγ hz
        exact (differential_continuousAt (fold_im_nonneg z) ha hb hc).neg) hB
    intro z hz L hL
    exact hh z hz L (by simpa only [slope,norm_neg] using hL)
  obtain ⟨t,ht,him,hre⟩ := SlitLeftCrossing.parentLeaf_exists_left_real hγ
  exact one_le_half_density_length_of_simple_excursion hγ.simple hg hp hloc
    (potential_on_ends hγ.first_end) (potential_on_ends hγ.last_end) ht
    (potential_left him hre.le)

/-- A single explicit metric works for every complete parent Wave. -/
theorem density_admissible {M : Marking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ParentWave M D Γ) : Admissible (traces Γ) (density M) := by
  refine ⟨density_measurable M,?_⟩
  rintro S ⟨γ,hγ,rfl⟩
  exact density_parent_length (hΓ.leaf γ hγ)

/-- The bound applies to the supremum over every Borel parent Wave. -/
theorem width_le_density_area (M : Marking) (D : Set ℂ) :
    SlitWaveLimit.width M D ≤ area (density M) := by
  apply iSup₂_le
  intro Γ hΓ
  exact modulus_le_area (density_admissible hΓ)

end
end SlitCubicAdmissible
