import SlitFourPointMetric
import SlitReflectedRectangleModulus

/-!
# Attained full-plane pairable optimum for four finite source ports

This supplies the genuine limiting-domain optimization problem. The
source and ambient domain are the whole plane, with a specified removed
real slit. The supremum still ranges over every pairable Borel parent
Wave, rather than only over the constructed reflected horizontals.
-/

namespace SlitFourPointPairable

open Set Function MarkedSlitTransport SlitWaveModulus
open SlitPairableWaves (PairableWave calibrationRegion)
open SlitFourPointChart
open scoped ENNReal
noncomputable section

def port (a b : ℝ) : Set ℂ := {z | z.im = 0 ∧ z.re ∈ Ioo a b}

def identityChart : CrestConformalModulus.ConformalChart where
  homeomorph := OpenPartialHomeomorph.refl ℂ
  derivative := fun _ => 1
  hasDeriv := fun z _ => hasDerivAt_id z
  derivative_continuous := continuous_const.continuousOn
  derivative_ne_zero := fun _ _ => one_ne_zero

def inverseData {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t) :
    SlitReflectedRectangleModulus.Data (width u v w t) (height u v w t) where
  toFun := closedInverse u v w t
  width_pos := SlitFourPointChart.width_pos huv hvw hwt
  height_pos := SlitFourPointChart.height_pos huv hvw hwt
  continuous := closedInverse_continuousOn huv hvw hwt
  injective := closedInverse_injOn huv hvw hwt
  upper := fun _ hz => closedInverse_mem_upper huv hvw hwt hz
  left_real := fun _ hy => (closedInverse_left_edge huv hvw hwt hy).1
  right_real := fun _ hy => (closedInverse_right_edge huv hvw hwt hy).1
  chart := inverseConformal huv hvw hwt
  chart_source := inverseConformal_source huv hvw hwt
  chart_target := by rw [inverseConformal_target]
  velocity := closedVelocity u v w t
  velocity_continuous := closedVelocity_continuousOn huv hvw hwt
  hasDeriv := fun _ hz => closedInverse_hasDerivAt huv hvw hwt hz
  interior_eq := fun _ hz => closedInverse_eq_inverseConformal huv hvw hwt hz
  derivative_eq := fun _ hz => inverseConformal_derivative huv hvw hwt hz

def family {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t) : Set Curve :=
  SlitReflectedRectangles.family (inverseData huv hvw hwt).toInverseData

theorem family_pairableWave {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t)
    (M : Marking) (T : Set ℂ) (hv : v ≤ M.left) (hw : M.first ≤ w) (ht : t ≤ M.second)
    (hT : ∀ z ∈ T, z.im = 0) (hleft : port u v ⊆ T) (hright : port w t ⊆ T) :
    PairableWave M univ univ T (port u v) (port w t) (family huv hvw hwt) := by
  apply SlitReflectedRectangles.family_pairableWave (inverseData huv hvw hwt).toInverseData M
    (fun _ _ => mem_univ _) (fun _ _ => mem_univ _) hT
  · intro y hy
    have hz := closedInverse_left_edge huv hvw hwt hy
    exact ⟨hz.2.2.trans_le hv,hleft hz,hz⟩
  · intro y hy
    have hz := closedInverse_right_edge huv hvw hwt hy
    exact ⟨⟨hz.1,hw.trans_lt hz.2.1,hz.2.2.trans_le ht⟩,hright hz,hz⟩

theorem region_ne_electrodes {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t)
    {T : Set ℂ} (huT : (u:ℂ) ∈ T) (hvT : (v:ℂ) ∈ T)
    (hwT : (w:ℂ) ∈ T) (htT : (t:ℂ) ∈ T) {z : ℂ}
    (hz : z ∈ calibrationRegion univ T (port u v) (port w t)) :
    z ≠ (u:ℂ) ∧ z ≠ (v:ℂ) ∧ z ≠ (w:ℂ) ∧ z ≠ (t:ℂ) := by
  have hz' := hz.2
  refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> subst z <;>
    rcases hz' with hn | hj | hj
  all_goals first
    | exact hn huT
    | exact hn hvT
    | exact hn hwT
    | exact hn htT
    | (simp only [port,mem_setOf_eq,Complex.ofReal_im,Complex.ofReal_re,true_and,mem_Ioo] at hj
       rcases hj with ⟨h0,h1⟩
       linarith)

theorem width_le_ratio {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t)
    (M : Marking) (T : Set ℂ) (huT : (u:ℂ) ∈ T) (hvT : (v:ℂ) ∈ T)
    (hwT : (w:ℂ) ∈ T) (htT : (t:ℂ) ∈ T) :
    SlitPairableWaves.width M univ univ T (port u v) (port w t) ≤
      ENNReal.ofReal (height u v w t/(2*width u v w t)) := by
  apply SlitFourPointMetric.pairable_width_le identityChart M univ univ T
    (port u v) (port w t) huv hvw hwt
  · exact fun _ _ => mem_univ _
  · exact fun _ hz => region_ne_electrodes huv hvw hwt huT hvT hwT htT hz
  · exact fun _ hz => hz
  · exact fun _ hz => hz

theorem family_modulus_lower {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t) :
    ENNReal.ofReal (height u v w t/(2*width u v w t)) ≤
      modulus (traces (family huv hvw hwt)) :=
  SlitReflectedRectangleModulus.family_modulus_lower (inverseData huv hvw hwt)

/-- The limiting full-plane two-port problem has an actual maximizing
Wave and the same sharp common-quadrilateral value. -/
theorem family_attains_width {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t)
    (M : Marking) (T : Set ℂ) (hv : v ≤ M.left) (hw : M.first ≤ w) (ht : t ≤ M.second)
    (hT : ∀ z ∈ T, z.im = 0) (hleft : port u v ⊆ T) (hright : port w t ⊆ T)
    (huT : (u:ℂ) ∈ T) (hvT : (v:ℂ) ∈ T) (hwT : (w:ℂ) ∈ T) (htT : (t:ℂ) ∈ T) :
    PairableWave M univ univ T (port u v) (port w t) (family huv hvw hwt) ∧
      modulus (traces (family huv hvw hwt)) =
        SlitPairableWaves.width M univ univ T (port u v) (port w t) ∧
      SlitPairableWaves.width M univ univ T (port u v) (port w t) =
        ENNReal.ofReal (height u v w t/(2*width u v w t)) := by
  have hfam := family_pairableWave huv hvw hwt M T hv hw ht hT hleft hright
  have hupper := width_le_ratio huv hvw hwt M T huT hvT hwT htT
  have hlower := family_modulus_lower huv hvw hwt
  have hmid := SlitPairableWaves.modulus_le_width hfam
  have heq : SlitPairableWaves.width M univ univ T (port u v) (port w t) =
      ENNReal.ofReal (height u v w t/(2*width u v w t)) :=
    le_antisymm hupper (hlower.trans hmid)
  exact ⟨hfam,le_antisymm hmid (heq.trans_le hlower),heq⟩

end
end SlitFourPointPairable
