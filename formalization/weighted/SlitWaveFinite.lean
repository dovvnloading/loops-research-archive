import SlitWaveModulus
import SlitWaveEscape
import MarkedSlitTransport

/-!
# A finite metric for the complete opposite-bank parent class

Every proper path joining the two opposite slit banks crosses the real
line outside the slit. Since both electrodes lie strictly inside the
slit, this forces a fixed positive amount of geometric length in a
single bounded disk. The resulting finite-area density is admissible
simultaneously for every parent Wave, including infinite-length leaves.
-/

namespace SlitWaveFinite

open Set Metric MeasureTheory
open MarkedSlitTransport SlitWaveModulus SlitWaveEscape
open scoped ENNReal NNReal Topology

noncomputable section

def clearance (M : Marking) : ℝ := min (M.first-M.left) (M.right-M.second)

theorem clearance_pos (M : Marking) : 0 < clearance M :=
  lt_min (sub_pos.mpr M.left_lt_first) (sub_pos.mpr M.second_lt_right)

def endBound (M : Marking) : ℝ := |M.first|+|M.second|+1

theorem endBound_pos (M : Marking) : 0 < endBound M := by
  unfold endBound
  positivity

def outerRadius (M : Marking) : ℝ := endBound M+clearance M

private theorem lower_point {γ : Curve} (hγ : LowerBank γ) :
    ∃ t ∈ parameterInterior, (γ t).im < 0 := by
  obtain ⟨ε,hε,hneg⟩ := hγ
  let x : ℝ := min (ε/2) (1/2)
  have hx0 : 0 < x := lt_min (by positivity) (by norm_num)
  have hx1 : x < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hxε : x < ε := (min_le_left _ _).trans_lt (by linarith)
  let t : Parameter := ⟨x, hx0.le, hx1.le⟩
  exact ⟨t, ⟨hx0,hx1⟩, hneg t hx0 hxε⟩

private theorem upper_point {γ : Curve} (hγ : UpperBank γ) :
    ∃ t ∈ parameterInterior, 0 < (γ t).im := by
  obtain ⟨ε,hε,hpos⟩ := hγ
  let x : ℝ := min (ε/2) (1/2)
  have hx0 : 0 < x := lt_min (by positivity) (by norm_num)
  have hx1 : x < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hxε : x < ε := (min_le_left _ _).trans_lt (by linarith)
  let t : Parameter := ⟨1-x, by constructor <;> linarith⟩
  have ht0 : (0 : ℝ) < t := by dsimp [t]; linarith
  have ht1 : (t : ℝ) < 1 := by dsimp [t]; linarith
  exact ⟨t, ⟨ht0,ht1⟩, hpos t (by dsimp [t]; linarith) ht1⟩

/-- Opposite accesses force an actual real crossing outside the slit.
No winding simplification or selected reference arc is used. -/
theorem parentLeaf_exists_exterior_real {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) :
    ∃ t ∈ parameterInterior, (γ t).im = 0 ∧
      ((γ t).re < M.left ∨ M.right < (γ t).re) := by
  obtain ⟨s,hs,hneg⟩ := lower_point hγ.lower
  obtain ⟨u,hu,hpos⟩ := upper_point hγ.upper
  have hpre : IsPreconnected parameterInterior := by
    change IsPreconnected (Ioo initial terminal)
    exact isPreconnected_Ioo
  obtain ⟨t,ht,hzero⟩ := hpre.intermediate_value hs hu
    (Complex.continuous_im.comp γ.continuous).continuousOn
    (show (0 : ℝ) ∈ Icc (γ s).im (γ u).im from
      ⟨hneg.le,hpos.le⟩)
  change (γ t).im = 0 at hzero
  refine ⟨t,ht,hzero,?_⟩
  by_cases hl : M.left ≤ (γ t).re
  · right
    by_contra hr
    exact hγ.avoids t ht ⟨hzero,hl,not_lt.mp hr⟩
  · exact Or.inl (lt_of_not_ge hl)

theorem parentLeaf_first_norm_le {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) : ‖γ initial‖ ≤ endBound M := by
  have he : γ initial = ((γ initial).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hγ.first_end.1
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  have hfirst := hγ.first_end.2.1
  have hsecond := hγ.first_end.2.2
  have hlo := neg_abs_le M.first
  have hhi := le_abs_self M.second
  constructor <;> unfold endBound <;>
    linarith [abs_nonneg M.first, abs_nonneg M.second]

/-- Each parent trace contains a point at a uniformly positive distance
from its first endpoint. -/
theorem parentLeaf_exists_distant_point {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) :
    ∃ b ∈ trace γ, clearance M ≤ dist (γ initial) b := by
  obtain ⟨t,ht,hzero,hout⟩ := parentLeaf_exists_exterior_real hγ
  refine ⟨γ t,⟨t,rfl⟩,?_⟩
  have hleft : clearance M ≤ M.first-M.left := min_le_left _ _
  have hright : clearance M ≤ M.right-M.second := min_le_right _ _
  have hfirst := hγ.first_end.2.1
  have hsecond := hγ.first_end.2.2
  rcases hout with hout | hout
  · have hd := (le_abs_self ((γ initial).re-(γ t).re)).trans
      (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (γ initial-γ t))
    rw [dist_eq_norm]
    linarith
  · have hd := (le_abs_self ((γ t).re-(γ initial).re)).trans
      (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (γ t-γ initial))
    rw [dist_eq_norm, norm_sub_rev]
    linarith

/-- A connected trace joining `a` to a point at distance at least `δ`
has at least `δ` units of Hausdorff length in a common bounded disk. -/
theorem hausdorff_bounded_length {S : Set ℂ} (hS : IsPreconnected S)
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) {R δ : ℝ}
    (haR : ‖a‖ ≤ R) (hfar : δ ≤ dist a b) :
    ENNReal.ofReal δ ≤ μH[1] (S ∩ closedBall (0 : ℂ) (R+δ)) := by
  have hradial : Ioo (0 : ℝ) δ ⊆
      (dist a) '' (S ∩ closedBall (0 : ℂ) (R+δ)) := by
    intro y hy
    obtain ⟨z,hz,hzy⟩ := hS.intermediate_value ha hb
      (LipschitzWith.dist_right a).continuous.continuousOn
      (show y ∈ Icc (dist a a) (dist a b) by simpa using ⟨hy.1.le,hy.2.le.trans hfar⟩)
    change dist a z = y at hzy
    refine ⟨z,⟨hz,?_⟩,hzy⟩
    rw [mem_closedBall,dist_zero_right]
    have htri := dist_triangle z a (0 : ℂ)
    rw [dist_zero_right,dist_zero_right,dist_comm z a,hzy] at htri
    linarith [hy.2]
  have hmono := measure_mono (μ := (μH[1] : Measure ℝ)) hradial
  have hlip := (LipschitzWith.dist_right a).hausdorffMeasure_image_le
    (d := 1) (by norm_num) (S ∩ closedBall (0 : ℂ) (R+δ))
  rw [hausdorffMeasure_real,Real.volume_Ioo,sub_zero] at hmono
  rw [hausdorffMeasure_real] at hlip
  simpa using hmono.trans hlip

/-- One finite-area metric is valid for every leaf of every parent Wave. -/
def parentDensity (M : Marking) : ℂ → ℝ≥0∞ :=
  (closedBall (0 : ℂ) (outerRadius M)).indicator
    (fun _ => ENNReal.ofReal (1/clearance M))

theorem parentDensity_measurable (M : Marking) : Measurable (parentDensity M) :=
  measurable_const.indicator isClosed_closedBall.measurableSet

theorem parentDensity_length {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) : 1 ≤ lineLength (parentDensity M) (trace γ) := by
  obtain ⟨b,hb,hfar⟩ := parentLeaf_exists_distant_point hγ
  have hH := hausdorff_bounded_length (trace_isPreconnected γ)
    (show γ initial ∈ trace γ from ⟨initial,rfl⟩) hb (parentLeaf_first_norm_le hγ) hfar
  have hδ := clearance_pos M
  unfold lineLength parentDensity
  rw [lintegral_indicator_const isClosed_closedBall.measurableSet,
    Measure.restrict_apply isClosed_closedBall.measurableSet,inter_comm]
  calc
    (1 : ℝ≥0∞) = ENNReal.ofReal (1/clearance M)*ENNReal.ofReal (clearance M) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1/clearance M)]
      simp [hδ.ne']
    _ ≤ _ := mul_le_mul_left' hH _

theorem parentDensity_admissible {M : Marking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ParentWave M D Γ) : Admissible (traces Γ) (parentDensity M) := by
  refine ⟨parentDensity_measurable M,?_⟩
  rintro _ ⟨γ,hγ,rfl⟩
  exact parentDensity_length (hΓ.leaf γ hγ)

/-- The common metric has finite planar energy, independently of the
lamination and of the outer domain. -/
theorem parentDensity_area_ne_top (M : Marking) : area (parentDensity M) ≠ ⊤ := by
  have heq : (fun z : ℂ => parentDensity M z ^ (2 : ℕ)) =
      (closedBall (0 : ℂ) (outerRadius M)).indicator
        (fun _ => ENNReal.ofReal (1/clearance M) ^ (2 : ℕ)) := by
    funext z
    by_cases hz : z ∈ closedBall (0 : ℂ) (outerRadius M) <;> simp [parentDensity,hz]
  unfold area
  rw [heq,lintegral_indicator_const isClosed_closedBall.measurableSet]
  exact ENNReal.mul_ne_top (by simp) measure_closedBall_lt_top.ne

theorem parentWave_modulus_le {M : Marking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ParentWave M D Γ) : modulus (traces Γ) ≤ area (parentDensity M) :=
  modulus_le_area (parentDensity_admissible hΓ)

end
end SlitWaveFinite
