import SlitFourPointChart
import SlitConformalCalibration

/-!
# The global four-electrode coordinate for a common pairable metric

The same fractional-linear map used by the actual rectangle chart is
conformal on the punctured physical plane. This permits one global area
change for the common reflected potential, including both children.
-/

namespace SlitFourPointMetric

open Set Function MarkedSlitTransport
open CrestConformalModulus SlitFourPointChart
noncomputable section

/-- The fractional-linear chart on its full punctured-plane domain. -/
def globalChart (u : ℝ) : ConformalChart where
  homeomorph := {
    toFun := SlitFourPointChart.map u
    invFun := SlitFourPointChart.inverse u
    source := {z | z ≠ (u:ℂ)}
    target := {z | z ≠ 0}
    map_source' := by
      intro z hz
      exact neg_ne_zero.mpr (inv_ne_zero (sub_ne_zero.mpr hz))
    map_target' := by
      intro z hz he
      apply hz
      apply inv_eq_zero.mp
      change (u:ℂ)-z⁻¹ = (u:ℂ) at he
      linear_combination -he
    left_inv' := fun z _ => inverse_map u z
    right_inv' := fun z _ => map_inverse u z
    open_source := isOpen_ne_fun continuous_id continuous_const
    open_target := isOpen_ne_fun continuous_id continuous_const
    continuousOn_toFun := fun z hz => (map_hasDerivAt u hz).continuousAt.continuousWithinAt
    continuousOn_invFun := fun z hz =>
      (inverse_hasDerivAt u hz).continuousAt.continuousWithinAt }
  derivative := fun z => ((z-(u:ℂ))^2)⁻¹
  hasDeriv := fun z hz => map_hasDerivAt u hz
  derivative_continuous := by
    apply ContinuousOn.inv₀
    · exact (continuous_id.sub continuous_const).pow 2 |>.continuousOn
    · intro z hz
      exact pow_ne_zero _ (sub_ne_zero.mpr hz)
  derivative_ne_zero := fun z hz => inv_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz))

@[simp] theorem globalChart_source (u : ℝ) :
    (globalChart u).homeomorph.source = {z | z ≠ (u:ℂ)} := rfl

@[simp] theorem globalChart_target (u : ℝ) :
    (globalChart u).homeomorph.target = {z | z ≠ 0} := rfl

@[simp] theorem globalChart_apply (u : ℝ) (z : ℂ) :
    (globalChart u).homeomorph z = SlitFourPointChart.map u z := rfl

@[simp] theorem globalChart_symm_apply (u : ℝ) (z : ℂ) :
    (globalChart u).homeomorph.symm z = SlitFourPointChart.inverse u z := rfl

def cubicMarking {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t) : Marking where
  left := realMap u v
  first := realMap u w
  second := realMap u t
  right := realMap u t+1
  left_lt_first := first_lt_second huv hvw
  first_lt_second := second_lt_third huv hvw hwt
  second_lt_right := lt_add_one _

theorem map_leftPort {u v : ℝ} {z : ℂ} (hi : z.im = 0)
    (hz : z.re ∈ Ioo u v) :
    (SlitFourPointChart.map u z).im = 0 ∧
      (SlitFourPointChart.map u z).re < realMap u v := by
  have he : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hi]
  rw [he,map_ofReal]
  exact ⟨rfl,realMap_strictMonoOn u hz.1 (hz.1.trans hz.2) hz.2⟩

theorem map_rightPort {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t)
    {z : ℂ} (hi : z.im = 0) (hz : z.re ∈ Ioo w t) :
    (cubicMarking huv hvw hwt).ends (SlitFourPointChart.map u z) := by
  have he : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hi]
  rw [he,map_ofReal]
  refine ⟨rfl,?_,?_⟩
  · exact realMap_strictMonoOn u (huv.trans hvw) ((huv.trans hvw).trans hz.1) hz.1
  · exact realMap_strictMonoOn u ((huv.trans hvw).trans hz.1)
      (huv.trans (hvw.trans hwt)) hz.2

theorem map_ne_pole {u x : ℝ} {z : ℂ} (hz : z ≠ (x:ℂ)) :
    SlitFourPointChart.map u z ≠ (realMap u x:ℂ) := by
  intro he
  apply hz
  apply map_injective u
  exact he.trans (map_ofReal u x).symm

theorem fold_ne_real {z : ℂ} {x : ℝ} (hz : z ≠ (x:ℂ)) :
    SlitPotentialReflection.fold z ≠ (x:ℂ) := by
  intro he
  apply hz
  have hn : ‖z-(x:ℂ)‖ = 0 := by
    rw [← SlitPotentialReflection.norm_fold_sub_real,he,sub_self,norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem map_regular {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t)
    {z : ℂ} (hv : z ≠ (v:ℂ)) (hw : z ≠ (w:ℂ)) (ht : z ≠ (t:ℂ)) :
    SlitFourPointChart.map u z ∈ SlitConformalCalibration.regular (cubicMarking huv hvw hwt) :=
  ⟨fold_ne_real (map_ne_pole hv),fold_ne_real (map_ne_pole hw),
    fold_ne_real (map_ne_pole ht)⟩

/-- A four-electrode upper bound in any proved global source coordinate.
All endpoint and exclusion hypotheses concern that coordinate's actual
values, rather than an extremal-length comparison supplied as a premise. -/
theorem pairable_width_le (C : ConformalChart) (M : Marking) (D V T J₀ J₁ : Set ℂ)
    {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t)
    (hsource : SlitPairableWaves.calibrationRegion V T J₀ J₁ ⊆ C.homeomorph.source)
    (hpoles : ∀ z ∈ SlitPairableWaves.calibrationRegion V T J₀ J₁,
      C.homeomorph z ≠ (u:ℂ) ∧ C.homeomorph z ≠ (v:ℂ) ∧
      C.homeomorph z ≠ (w:ℂ) ∧ C.homeomorph z ≠ (t:ℂ))
    (hleft : ∀ z ∈ J₀, (C.homeomorph z).im = 0 ∧ (C.homeomorph z).re ∈ Ioo u v)
    (hright : ∀ z ∈ J₁, (C.homeomorph z).im = 0 ∧ (C.homeomorph z).re ∈ Ioo w t) :
    SlitPairableWaves.width M D V T J₀ J₁ ≤ ENNReal.ofReal
      (SlitFourPointChart.height u v w t/(2*SlitFourPointChart.width u v w t)) := by
  apply SlitConformalCalibration.pairable_width_le_period_ratio
    (SlitConformalCalibration.compose C (globalChart u)) M (cubicMarking huv hvw hwt)
  · intro z hz
    exact ⟨hsource hz,(hpoles z hz).1⟩
  · intro z hz
    exact map_regular huv hvw hwt (hpoles z hz).2.1 (hpoles z hz).2.2.1
      (hpoles z hz).2.2.2
  · intro z hz
    have h := map_leftPort (hleft z hz).1 (hleft z hz).2
    exact ⟨h.1,h.2.le⟩
  · intro z hz
    exact map_rightPort huv hvw hwt (hright z hz).1 (hright z hz).2

end
end SlitFourPointMetric
