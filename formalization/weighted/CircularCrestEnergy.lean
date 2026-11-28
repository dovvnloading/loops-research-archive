import CollarMetricEnergy
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Group.Integral

/-!
# The metric problem for a variable-height circular foliation

The length constraint is the ordinary arclength integral along each
circular leaf. The density is any measurable extended nonnegative
function on the physical plane. Polar change of variables and
Cauchy--Schwarz evaluate the complete variational problem.
-/

namespace CircularCrestEnergy

open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal Classical

noncomputable section

def point (m : ℂ) (r t : ℝ) : ℂ :=
  m + Complex.polarCoord.symm (r,t)

theorem point_continuous (m : ℂ) : Continuous (fun p : ℝ × ℝ => point m p.1 p.2) := by
  simp only [point, Complex.polarCoord_symm_apply]
  fun_prop

def leafLength (m : ℂ) (r T : ℝ) (ρ : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t in Ioo 0 T, ρ (point m r t) * ENNReal.ofReal r

def Admissible (m : ℂ) (I : Set ℝ) (θ : ℝ → ℝ) (ρ : ℂ → ℝ≥0∞) : Prop :=
  Measurable ρ ∧ ∀ r ∈ I, 1 ≤ leafLength m r (θ r) ρ

def area (ρ : ℂ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ z : ℂ, (ρ z)^2

def modulus (m : ℂ) (I : Set ℝ) (θ : ℝ → ℝ) : ℝ≥0∞ :=
  ⨅ (ρ : ℂ → ℝ≥0∞) (_ : Admissible m I θ ρ), area ρ

theorem angular_energy_lower {m : ℂ} {r T : ℝ} (hr : 0 < r) (hT : 0 < T)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) (hlength : 1 ≤ leafLength m r T ρ) :
    ENNReal.ofReal (1/(r*T)) ≤
      ENNReal.ofReal r * ∫⁻ t in Ioo 0 T, (ρ (point m r t))^2 := by
  have hp : Measurable (fun t : ℝ => ρ (point m r t)) :=
    hρ.comp ((point_continuous m).comp (continuous_const.prodMk continuous_id)).measurable
  have hmass : (volume.restrict (Ioo (0 : ℝ) T)) univ = ENNReal.ofReal T := by simp
  have h := CollarMetricEnergy.reciprocal_mass_le_square_integral
    (μ := volume.restrict (Ioo (0 : ℝ) T))
    (f := fun t => ρ (point m r t) * ENNReal.ofReal r)
    (hp.mul measurable_const).aemeasurable
    (by rw [hmass]; exact (ENNReal.ofReal_pos.mpr hT).ne')
    (by rw [hmass]; exact ENNReal.ofReal_ne_top) hlength
  simp only [hmass, mul_pow] at h
  rw [lintegral_mul_const _ (hp.pow_const 2)] at h
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have he : ENNReal.ofReal (1/(r*T)) =
      (ENNReal.ofReal T)⁻¹ / ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_inv_of_pos hT, ← ENNReal.ofReal_div_of_pos hr]
    congr 1
    field_simp
  rw [he]
  apply (ENNReal.div_le_iff hr0 ENNReal.ofReal_ne_top).mpr
  simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using h

/-- The polar energy of any rectangular subregion is bounded by its
actual planar energy. The center is arbitrary and no outer-domain
replacement is used. -/
theorem polar_energy_le_area {m : ℂ} {I J : Set ℝ} (hI : MeasurableSet I)
    (hJ : MeasurableSet J) (hIp : I ⊆ Ioi 0) (hJp : J ⊆ Ioo (-Real.pi) Real.pi)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    (∫⁻ r in I, ENNReal.ofReal r * ∫⁻ t in J, (ρ (point m r t))^2) ≤ area ρ := by
  have hp : Measurable (fun p : ℝ × ℝ => (ρ (point m p.1 p.2))^2) :=
    (hρ.comp (point_continuous m).measurable).pow_const 2
  have hf : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * (ρ (point m p.1 p.2))^2) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul hp
  have he : (∫⁻ r in I, ENNReal.ofReal r * ∫⁻ t in J, (ρ (point m r t))^2) =
      ∫⁻ p : ℝ × ℝ in I ×ˢ J, ENNReal.ofReal p.1 * (ρ (point m p.1 p.2))^2 := by
    rw [volume_eq_prod, setLIntegral_prod _ hf.aemeasurable]
    apply lintegral_congr
    intro r
    exact (lintegral_const_mul _
      (hp.comp (measurable_const.prodMk measurable_id))).symm
  rw [he]
  calc
    _ ≤ ∫⁻ p : ℝ × ℝ in _root_.polarCoord.target,
        ENNReal.ofReal p.1 * (ρ (point m p.1 p.2))^2 :=
      lintegral_mono_set (fun _ hp => ⟨hIp hp.1, hJp hp.2⟩)
    _ = ∫⁻ z : ℂ, (ρ (m+z))^2 := by
      simpa only [point, smul_eq_mul] using
        Complex.lintegral_comp_polarCoord_symm (fun z => (ρ (m+z))^2)
    _ = area ρ := lintegral_add_left_eq_self (fun z : ℂ => (ρ z)^2) m

/-- Every density admissible for the entire circular family has at
least its stated radial energy. -/
theorem radial_integral_le_area {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    (hI : MeasurableSet I) (hIp : I ⊆ Ioi 0)
    (hθ : ∀ r ∈ I, 0 < θ r ∧ θ r ≤ Real.pi)
    {ρ : ℂ → ℝ≥0∞} (hρ : Admissible m I θ ρ) :
    (∫⁻ r in I, ENNReal.ofReal (1/(r*θ r))) ≤ area ρ := by
  have hslice : ∀ r ∈ I,
      ENNReal.ofReal (1/(r*θ r)) ≤
        ENNReal.ofReal r * ∫⁻ t in Ioo 0 Real.pi, (ρ (point m r t))^2 := by
    intro r hr
    exact (angular_energy_lower (hIp hr) (hθ r hr).1 hρ.1 (hρ.2 r hr)).trans
      (mul_le_mul_left' (lintegral_mono_set
        (Ioo_subset_Ioo le_rfl (hθ r hr).2)) _)
  calc
    _ ≤ ∫⁻ r in I, ENNReal.ofReal r *
        ∫⁻ t in Ioo 0 Real.pi, (ρ (point m r t))^2 := by
      apply setLIntegral_mono' hI
      exact hslice
    _ ≤ area ρ := polar_energy_le_area hI measurableSet_Ioo hIp
      (Ioo_subset_Ioo (neg_nonpos.mpr Real.pi_pos.le) le_rfl) hρ.1

theorem radial_integral_le_modulus {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    (hI : MeasurableSet I) (hIp : I ⊆ Ioi 0)
    (hθ : ∀ r ∈ I, 0 < θ r ∧ θ r ≤ Real.pi) :
    (∫⁻ r in I, ENNReal.ofReal (1/(r*θ r))) ≤ modulus m I θ := by
  apply le_iInf₂
  intro ρ hρ
  exact radial_integral_le_area hI hIp hθ hρ

def ribbon (m : ℂ) (I : Set ℝ) (θ : ℝ → ℝ) : Set ℂ :=
  {z | ‖z-m‖ ∈ I ∧ (z-m).arg ∈ Ioo 0 (θ ‖z-m‖)}

def extremalDensity (m : ℂ) (I : Set ℝ) (θ : ℝ → ℝ) : ℂ → ℝ≥0∞ :=
  (ribbon m I θ).indicator (fun z => ENNReal.ofReal (1/(‖z-m‖*θ ‖z-m‖)))

theorem ribbon_measurable {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    (hI : MeasurableSet I) (hθ : Measurable θ) : MeasurableSet (ribbon m I θ) := by
  have hn : Measurable (fun z : ℂ => ‖z-m‖) := (continuous_id.sub continuous_const).norm.measurable
  have ha : Measurable (fun z : ℂ => (z-m).arg) :=
    Complex.measurable_arg.comp (continuous_id.sub continuous_const).measurable
  exact (hI.preimage hn).inter
    ((measurableSet_lt measurable_const ha).inter (measurableSet_lt ha (hθ.comp hn)))

theorem extremalDensity_measurable {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    (hI : MeasurableSet I) (hθ : Measurable θ) : Measurable (extremalDensity m I θ) := by
  have hn : Measurable (fun z : ℂ => ‖z-m‖) := (continuous_id.sub continuous_const).norm.measurable
  exact (ENNReal.measurable_ofReal.comp (measurable_const.div (hn.mul (hθ.comp hn)))).indicator
    (ribbon_measurable hI hθ)

theorem point_coordinates (m : ℂ) {r t : ℝ} (hr : 0 < r)
    (ht : t ∈ Ioo (-Real.pi) Real.pi) :
    ‖point m r t-m‖ = r ∧ (point m r t-m).arg = t := by
  have h := Complex.polarCoord.right_inv (show (r,t) ∈ Complex.polarCoord.target from ⟨hr,ht⟩)
  rw [Complex.polarCoord_apply] at h
  have hnorm := congrArg Prod.fst h
  have harg := congrArg Prod.snd h
  simpa [point] using And.intro hnorm harg

theorem extremalDensity_point {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    {r t : ℝ} (hr : 0 < r) (ht : t ∈ Ioo (-Real.pi) Real.pi) :
    extremalDensity m I θ (point m r t) =
      if r ∈ I ∧ t ∈ Ioo 0 (θ r) then ENNReal.ofReal (1/(r*θ r)) else 0 := by
  obtain ⟨hn,ha⟩ := point_coordinates m hr ht
  simp only [extremalDensity, ribbon, indicator, mem_setOf_eq, hn, ha]

/-- The constructed density has unit metric length on every leaf,
not merely on almost every radius. -/
theorem extremalDensity_leafLength {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    {r : ℝ} (hrI : r ∈ I) (hr : 0 < r) (hθ : 0 < θ r ∧ θ r ≤ Real.pi) :
    leafLength m r (θ r) (extremalDensity m I θ) = 1 := by
  have hp (t : ℝ) (ht : t ∈ Ioo 0 (θ r)) :
      extremalDensity m I θ (point m r t) = ENNReal.ofReal (1/(r*θ r)) := by
    rw [extremalDensity_point hr
      ⟨(neg_lt_zero.mpr Real.pi_pos).trans ht.1,ht.2.trans_le hθ.2⟩]
    simp only [hrI,ht,and_self,if_true]
  have hT : 0 < θ r := hθ.1
  unfold leafLength
  calc
    _ = ∫⁻ _t in Ioo 0 (θ r), ENNReal.ofReal (1/(r*θ r)) * ENNReal.ofReal r := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp only
      rw [hp t ht]
    _ = ENNReal.ofReal ((1/(r*θ r))*r*(θ r)) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(r*θ r)),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (1/(r*θ r))*r)]
    _ = 1 := by
      have he : (1/(r*θ r))*r*(θ r) = (1 : ℝ) := by field_simp [hr.ne',hθ.1.ne']
      rw [he, ENNReal.ofReal_one]

theorem extremalDensity_admissible {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    (hI : MeasurableSet I) (hθm : Measurable θ) (hIp : I ⊆ Ioi 0)
    (hθ : ∀ r ∈ I, 0 < θ r ∧ θ r ≤ Real.pi) :
    Admissible m I θ (extremalDensity m I θ) := by
  refine ⟨extremalDensity_measurable hI hθm, ?_⟩
  intro r hr
  rw [extremalDensity_leafLength hr (hIp hr) (hθ r hr)]

private theorem density_slice_energy {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    (hθ : ∀ r ∈ I, 0 < θ r ∧ θ r ≤ Real.pi) {r : ℝ} (hr : 0 < r) :
    (∫⁻ t in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal r * (extremalDensity m I θ (point m r t))^2) =
      I.indicator (fun r => ENNReal.ofReal (1/(r*θ r))) r := by
  by_cases hrI : r ∈ I
  · rw [indicator_of_mem hrI]
    have ht := hθ r hrI
    have hT : 0 < θ r := ht.1
    let A := ENNReal.ofReal r * (ENNReal.ofReal (1/(r*θ r)))^2
    have he : (∫⁻ t in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * (extremalDensity m I θ (point m r t))^2) =
        ∫⁻ t in Ioo (-Real.pi) Real.pi,
          (Ioo (0 : ℝ) (θ r)).indicator (fun _ => A) t := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht'
      dsimp only
      rw [extremalDensity_point hr ht']
      by_cases htI : t ∈ Ioo 0 (θ r) <;> simp [hrI,htI,A]
    rw [he, setLIntegral_indicator measurableSet_Ioo,
      inter_eq_left.mpr (Ioo_subset_Ioo (neg_nonpos.mpr Real.pi_pos.le) ht.2)]
    simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
    dsimp [A]
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 1/(r*θ r)),
      ← ENNReal.ofReal_mul hr.le,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ r*(1/(r*θ r))^2)]
    congr 1
    field_simp [hr.ne',ht.1.ne']
    <;> ring
  · rw [indicator_of_notMem hrI]
    calc
      _ = ∫⁻ _t in Ioo (-Real.pi) Real.pi, (0 : ℝ≥0∞) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro t ht
        dsimp only
        rw [extremalDensity_point hr ht]
        simp [hrI]
      _ = 0 := by simp

theorem extremalDensity_area {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    (hI : MeasurableSet I) (hθm : Measurable θ) (hIp : I ⊆ Ioi 0)
    (hθ : ∀ r ∈ I, 0 < θ r ∧ θ r ≤ Real.pi) :
    area (extremalDensity m I θ) = ∫⁻ r in I, ENNReal.ofReal (1/(r*θ r)) := by
  let ρ := extremalDensity m I θ
  have hm : Measurable ρ := extremalDensity_measurable hI hθm
  have hf : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * (ρ (point m p.1 p.2))^2) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      ((hm.comp (point_continuous m).measurable).pow_const 2)
  calc
    area ρ = ∫⁻ z : ℂ, (ρ (m+z))^2 :=
      (lintegral_add_left_eq_self (fun z : ℂ => (ρ z)^2) m).symm
    _ = ∫⁻ p : ℝ × ℝ in _root_.polarCoord.target,
        ENNReal.ofReal p.1 * (ρ (point m p.1 p.2))^2 := by
      simpa only [point, smul_eq_mul] using
        (Complex.lintegral_comp_polarCoord_symm (fun z => (ρ (m+z))^2)).symm
    _ = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ t in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * (ρ (point m r t))^2 := by
      rw [_root_.polarCoord_target, volume_eq_prod, setLIntegral_prod _ hf.aemeasurable]
    _ = ∫⁻ r in Ioi (0 : ℝ), I.indicator (fun r => ENNReal.ofReal (1/(r*θ r))) r := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      exact density_slice_energy hθ hr
    _ = ∫⁻ r in I, ENNReal.ofReal (1/(r*θ r)) := by
      rw [setLIntegral_indicator hI, inter_eq_left.mpr hIp]

/-- Exact modulus of the complete specified circular foliation. This
does not replace it by all curves between the boundary rails. -/
theorem modulus_eq_radial_integral {m : ℂ} {I : Set ℝ} {θ : ℝ → ℝ}
    (hI : MeasurableSet I) (hθm : Measurable θ) (hIp : I ⊆ Ioi 0)
    (hθ : ∀ r ∈ I, 0 < θ r ∧ θ r ≤ Real.pi) :
    modulus m I θ = ∫⁻ r in I, ENNReal.ofReal (1/(r*θ r)) := by
  apply le_antisymm
  · have h : modulus m I θ ≤ area (extremalDensity m I θ) := by
      unfold modulus
      exact iInf₂_le _ (extremalDensity_admissible hI hθm hIp hθ)
    exact h.trans_eq (extremalDensity_area hI hθm hIp hθ)
  · exact radial_integral_le_modulus hI hIp hθ

end
end CircularCrestEnergy
