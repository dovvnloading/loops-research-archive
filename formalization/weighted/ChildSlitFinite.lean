import ChildSlitModel
import SlitWaveFinite

/-!
# One finite metric for every complete child Wave

The two child ending intervals have a positive gap. Every continuous
leaf therefore connects its first endpoint to a point at a fixed
positive distance. The existing connected-trace Hausdorff estimate
puts that amount of length inside a single bounded disk, even if the
leaf itself has infinite arclength or leaves every prescribed smaller
disk. A single bounded-support density controls all child laminations.
-/

namespace ChildSlitFinite

open Set Metric MeasureTheory
open MarkedSlitTransport SlitWaveModulus ChildSlitModel
open scoped ENNReal NNReal Topology

noncomputable section

def gap (M : ChildMarking) : ℝ := M.secondLo-M.firstHi

theorem gap_pos (M : ChildMarking) : 0 < gap M :=
  sub_pos.mpr M.firstHi_lt_secondLo

def endBound (M : ChildMarking) : ℝ := |M.firstLo|+|M.firstHi|+1

theorem endBound_pos (M : ChildMarking) : 0 < endBound M := by
  unfold endBound
  positivity

def outerRadius (M : ChildMarking) : ℝ := endBound M+gap M

theorem childLeaf_first_norm_le {M : ChildMarking} {D : Set ℂ} {γ : Curve}
    (hγ : ChildLeaf M D γ) : ‖γ initial‖ ≤ endBound M := by
  have he : γ initial = ((γ initial).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hγ.first_end.1
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  have hlo := hγ.first_end.2.1
  have hhi := hγ.first_end.2.2
  have hfirst := neg_abs_le M.firstLo
  have hsecond := le_abs_self M.firstHi
  constructor <;> unfold endBound <;>
    linarith [abs_nonneg M.firstLo, abs_nonneg M.firstHi]

theorem childLeaf_endpoint_distance {M : ChildMarking} {D : Set ℂ} {γ : Curve}
    (hγ : ChildLeaf M D γ) : gap M ≤ dist (γ initial) (γ terminal) := by
  have hfirst := hγ.first_end.2.2
  have hlast := hγ.last_end.2.1
  have hd := (le_abs_self ((γ terminal).re-(γ initial).re)).trans
    (by simpa only [Complex.sub_re] using
      Complex.abs_re_le_norm (γ terminal-γ initial))
  rw [dist_eq_norm, norm_sub_rev]
  unfold gap
  linarith

def childDensity (M : ChildMarking) : ℂ → ℝ≥0∞ :=
  (closedBall (0 : ℂ) (outerRadius M)).indicator
    (fun _ => ENNReal.ofReal (1/gap M))

theorem childDensity_measurable (M : ChildMarking) : Measurable (childDensity M) :=
  measurable_const.indicator isClosed_closedBall.measurableSet

theorem childDensity_length {M : ChildMarking} {D : Set ℂ} {γ : Curve}
    (hγ : ChildLeaf M D γ) : 1 ≤ lineLength (childDensity M) (trace γ) := by
  have hH := SlitWaveFinite.hausdorff_bounded_length (trace_isPreconnected γ)
    (show γ initial ∈ trace γ from ⟨initial,rfl⟩)
    (show γ terminal ∈ trace γ from ⟨terminal,rfl⟩)
    (childLeaf_first_norm_le hγ) (childLeaf_endpoint_distance hγ)
  have hδ := gap_pos M
  unfold lineLength childDensity
  rw [lintegral_indicator_const isClosed_closedBall.measurableSet,
    Measure.restrict_apply isClosed_closedBall.measurableSet,inter_comm]
  calc
    (1 : ℝ≥0∞) = ENNReal.ofReal (1/gap M)*ENNReal.ofReal (gap M) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1/gap M)]
      simp [hδ.ne']
    _ ≤ _ := mul_le_mul_left' hH _

theorem childDensity_admissible {M : ChildMarking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ChildWave M D Γ) : Admissible (traces Γ) (childDensity M) := by
  refine ⟨childDensity_measurable M,?_⟩
  rintro _ ⟨γ,hγ,rfl⟩
  exact childDensity_length (hΓ.leaf γ hγ)

theorem childDensity_area_ne_top (M : ChildMarking) : area (childDensity M) ≠ ⊤ := by
  have heq : (fun z : ℂ => childDensity M z ^ (2 : ℕ)) =
      (closedBall (0 : ℂ) (outerRadius M)).indicator
        (fun _ => ENNReal.ofReal (1/gap M) ^ (2 : ℕ)) := by
    funext z
    by_cases hz : z ∈ closedBall (0 : ℂ) (outerRadius M) <;> simp [childDensity,hz]
  unfold area
  rw [heq,lintegral_indicator_const isClosed_closedBall.measurableSet]
  exact ENNReal.mul_ne_top (by simp) measure_closedBall_lt_top.ne

theorem childWave_modulus_le {M : ChildMarking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ChildWave M D Γ) : modulus (traces Γ) ≤ area (childDensity M) :=
  modulus_le_area (childDensity_admissible hΓ)

/-- The complete child optimum is finite on every source domain,
including the whole plane. -/
theorem width_ne_top (M : ChildMarking) (D : Set ℂ) : width M D ≠ ⊤ := by
  have hbound : width M D ≤ area (childDensity M) := by
    apply iSup₂_le
    intro Γ hΓ
    exact childWave_modulus_le hΓ
  exact ne_top_of_le_ne_top (childDensity_area_ne_top M) hbound

end
end ChildSlitFinite
