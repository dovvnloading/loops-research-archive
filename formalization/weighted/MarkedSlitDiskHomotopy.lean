import MarkedSlitCompression
import Mathlib.Topology.Homotopy.Basic

/-!
# Reflection of the selected plane-slit class into the actual target disk

The class predicate used for geometric width is defined on the whole
plane minus the slit.  This file proves that, in a sufficiently large
target disk, its homotopies can be chosen inside that disk.  A coordinate
compression fixes the slit and decreases the Euclidean norm.  Its straight
interpolation with the identity preserves the slit complement, so a given
leaf can first be joined to its compressed image inside the target disk.
The entire original homotopy can then be compressed into the same disk.
-/

namespace MarkedSlitTransport

open Set Function MeasureTheory Metric
open scoped Topology NNReal ENNReal

noncomputable section

theorem softTail_le_self {x : ℝ} (hx : 0 ≤ x) : softTail x ≤ x := by
  apply (div_le_iff₀ (by linarith : 0 < 1+x)).2
  nlinarith [sq_nonneg x]

theorem compressCoord_abs_le {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |compressCoord R x| ≤ |x| := by
  by_cases hxlo : x ≤ -R
  · rw [compressCoord_of_le hR.le hxlo]
    have h0 := softTail_nonneg (by linarith : 0 ≤ -x-R)
    have h1 := softTail_le_self (by linarith : 0 ≤ -x-R)
    rw [abs_of_neg (by linarith : -R-softTail (-x-R) < 0),
      abs_of_neg (by linarith : x < 0)]
    linarith
  · by_cases hxhi : R ≤ x
    · rw [compressCoord_of_ge hR.le hxhi]
      have h0 := softTail_nonneg (by linarith : 0 ≤ x-R)
      have h1 := softTail_le_self (by linarith : 0 ≤ x-R)
      rw [abs_of_pos (by linarith : 0 < R+softTail (x-R)),
        abs_of_pos (by linarith : 0 < x)]
      linarith
    · rw [compressCoord_of_mem ⟨(lt_of_not_ge hxlo).le,(lt_of_not_ge hxhi).le⟩]

theorem compression_plane_norm_le {R : ℝ} (hR : 0 < R) (z : ℂ) :
    ‖(compressionCoordinate R hR).plane z‖ ≤ ‖z‖ := by
  have hre : (compressCoord R z.re)^2 ≤ z.re^2 := sq_le_sq.mpr (compressCoord_abs_le hR _)
  have him : (compressCoord R z.im)^2 ≤ z.im^2 := sq_le_sq.mpr (compressCoord_abs_le hR _)
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simpa only [CoordinateEmbedding.plane_re,
    CoordinateEmbedding.plane_im, compressionCoordinate, pow_two] using add_le_add hre him

/-- Every intermediate coordinate map is itself increasing and fixes zero. -/
def interpolateCoordinate (h : CoordinateEmbedding) (s : Parameter) : CoordinateEmbedding where
  toFun x := (1-(s : ℝ))*x+(s : ℝ)*h x
  continuous := (continuous_const.mul continuous_id).add (continuous_const.mul h.continuous)
  strictMono := by
    intro x y hxy
    have hs0 : 0 ≤ (s : ℝ) := s.property.1
    have hs1 : (s : ℝ) ≤ 1 := s.property.2
    by_cases hs : (s : ℝ) = 0
    · simpa [hs] using hxy
    · have hsp : 0 < (s : ℝ) := lt_of_le_of_ne hs0 (Ne.symm hs)
      have ha : 0 ≤ (1-(s : ℝ))*(y-x) :=
        mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hxy.le)
      have hb : 0 < (s : ℝ)*(h y-h x) := mul_pos hsp (sub_pos.mpr (h.strictMono hxy))
      nlinarith
  map_zero := by simp [h.map_zero]

def straightCompression (R : ℝ) (hR : 0 < R) (s : Parameter) (z : ℂ) : ℂ :=
  (1-(s : ℝ)) • z+(s : ℝ) • (compressionCoordinate R hR).plane z

theorem straightCompression_eq_plane {R : ℝ} (hR : 0 < R) (s : Parameter) (z : ℂ) :
    straightCompression R hR s z =
      (interpolateCoordinate (compressionCoordinate R hR) s).plane z := by
  apply Complex.ext <;>
    simp [straightCompression, CoordinateEmbedding.plane, interpolateCoordinate] <;> ring

theorem straightCompression_norm_le {R : ℝ} (hR : 0 < R) (s : Parameter) (z : ℂ) :
    ‖straightCompression R hR s z‖ ≤ ‖z‖ := by
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hs1 : 0 ≤ 1-(s : ℝ) := sub_nonneg.mpr s.property.2
  calc
    ‖straightCompression R hR s z‖ ≤
        ‖(1-(s : ℝ)) • z‖+‖(s : ℝ) • (compressionCoordinate R hR).plane z‖ :=
      norm_add_le _ _
    _ = (1-(s : ℝ))*‖z‖+(s : ℝ)*‖(compressionCoordinate R hR).plane z‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hs1, abs_of_nonneg hs0]
    _ ≤ (1-(s : ℝ))*‖z‖+(s : ℝ)*‖z‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (compression_plane_norm_le hR z) hs0)
    _ = ‖z‖ := by ring

theorem interpolation_marking_fixed (M : Marking) {h : CoordinateEmbedding}
    (hfix : M.coordinateMap h = M) (s : Parameter) :
    M.coordinateMap (interpolateCoordinate h s) = M := by
  have hl := congrArg Marking.left hfix
  have ha := congrArg Marking.first hfix
  have hb := congrArg Marking.second hfix
  have hr := congrArg Marking.right hfix
  change h M.left = M.left at hl
  change h M.first = M.first at ha
  change h M.second = M.second at hb
  change h M.right = M.right at hr
  ext <;> simp [Marking.coordinateMap, interpolateCoordinate, hl,ha,hb,hr] <;> ring

theorem straightCompression_avoids (M : Marking) {R : ℝ} (hR : 0 < R)
    (hl : |M.left| ≤ R) (hr : |M.right| ≤ R) (s : Parameter)
    {z : ℂ} (hz : z ∉ M.slit) : straightCompression R hR s z ∉ M.slit := by
  rw [straightCompression_eq_plane]
  have hfix := interpolation_marking_fixed M (compression_marking_fixed M hR hl hr) s
  rw [← hfix]
  exact ((interpolateCoordinate (compressionCoordinate R hR) s).plane_mem_slit_iff M z).not.mpr hz

theorem Marking.norm_le_of_ends (M : Marking) {R : ℝ}
    (hl : |M.left| ≤ R) (hr : |M.right| ≤ R) {z : ℂ} (hz : M.ends z) : ‖z‖ ≤ R := by
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [hz.1]
  rw [hzreal, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [(abs_le.mp hl).1, M.left_lt_first, hz.2.1]
  · linarith [(abs_le.mp hr).2, M.second_lt_right, hz.2.2]

/-- The full relative path condition used during a homotopy inside an
outer domain.  Simplicity is required of the original leaf and reference,
as usual for an arc class, but is not imposed on intermediate homotopies. -/
def RelativeSlitPath (M : Marking) (D : Set ℂ) (γ : Curve) (η : Curve) : Prop :=
  η initial = γ initial ∧ η terminal = γ terminal ∧
    ∀ t ∈ parameterInterior, η t ∈ D ∧ η t ∉ M.slit

def RelSlitHomotopyIn (M : Marking) (D : Set ℂ) (γ η : Curve) : Prop :=
  Nonempty (ContinuousMap.HomotopyWith γ η (RelativeSlitPath M D γ))

def LeftClassIn (M : Marking) (D : Set ℂ) (γ : Curve) : Prop :=
  ∃ η : Curve, LeftReference M.left η ∧ RelSlitHomotopyIn M D γ η

theorem RelSlitHomotopyIn.forget {M : Marking} {D : Set ℂ} {γ η : Curve}
    (h : RelSlitHomotopyIn M D γ η) : RelSlitHomotopy M γ η := by
  obtain ⟨F⟩ := h
  refine ⟨F.toHomotopy.toContinuousMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; exact F.map_zero_left t
  · intro t; exact F.map_one_left t
  · intro s; exact (F.prop s).1
  · intro s; exact (F.prop s).2.1
  · intro s t ht; exact ((F.prop s).2.2 t ht).2

theorem LeftClassIn.forget {M : Marking} {D : Set ℂ} {γ : Curve}
    (h : LeftClassIn M D γ) : LeftClass M γ := by
  obtain ⟨η,hη,hγη⟩ := h
  exact ⟨η,hη,hγη.forget⟩

theorem RelSlitHomotopyIn.coordinateMap {M : Marking} {D : Set ℂ} {γ η : Curve}
    (hγη : RelSlitHomotopyIn M D γ η) (h : CoordinateEmbedding) :
    RelSlitHomotopyIn (M.coordinateMap h) (h.plane '' D)
      (coordinateCurve h γ) (coordinateCurve h η) := by
  obtain ⟨F⟩ := hγη
  refine ⟨{
    toContinuousMap := h.plane.comp F.toHomotopy.toContinuousMap
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    change h.plane (F (initial,t)) = h.plane (γ t)
    exact congrArg h.plane (F.map_zero_left t)
  · intro t
    change h.plane (F (terminal,t)) = h.plane (η t)
    exact congrArg h.plane (F.map_one_left t)
  · intro s
    refine ⟨?_, ?_, ?_⟩
    · change h.plane (F (s,initial)) = h.plane (γ initial)
      exact congrArg h.plane (F.prop s).1
    · change h.plane (F (s,terminal)) = h.plane (γ terminal)
      exact congrArg h.plane (F.prop s).2.1
    · intro t ht
      exact ⟨⟨F (s,t), ((F.prop s).2.2 t ht).1, rfl⟩,
        (h.plane_mem_slit_iff M (F (s,t))).not.mpr ((F.prop s).2.2 t ht).2⟩

theorem LeftClassIn.coordinateMap {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : LeftClassIn M D γ) (h : CoordinateEmbedding) :
    LeftClassIn (M.coordinateMap h) (h.plane '' D) (coordinateCurve h γ) := by
  obtain ⟨η,hη,hγη⟩ := hγ
  exact ⟨coordinateCurve h η, hη.coordinateMap h, hγη.coordinateMap h⟩

/-- A plane-slit left class of a proper target-disk leaf has a literal
relative-endpoint homotopy inside that target disk.  This is the converse
direction needed to identify the finite physical arc class; it is not an
assumed class-preservation predicate. -/
theorem ParentLeaf.leftClassIn_ball {M : Marking} {B R : ℝ} {γ : Curve}
    (hγ : ParentLeaf M (ball (0 : ℂ) B) γ) (hR : 0 < R)
    (hl : |M.left| ≤ R) (hr : |M.right| ≤ R) (hB : 2*(R+1) < B) :
    LeftClassIn M (ball (0 : ℂ) B) γ := by
  let h := compressionCoordinate R hR
  have hm : M.coordinateMap h = M := compression_marking_fixed M hR hl hr
  have he0 : h.plane (γ initial) = γ initial :=
    compression_plane_fixed hR (M.norm_le_of_ends hl hr hγ.first_end)
  have he1 : h.plane (γ terminal) = γ terminal :=
    compression_plane_fixed hR (M.norm_le_of_ends hl hr hγ.last_end)
  obtain ⟨η,hη,F,h0,h1,hf0,hf1,havoid⟩ := hγ.left_class
  let P : Curve → Prop := RelativeSlitPath M (ball (0 : ℂ) B) γ
  let A : ContinuousMap.HomotopyWith γ (coordinateCurve h γ) P :=
    { toFun := fun p => straightCompression R hR p.1 (γ p.2)
      continuous_toFun :=
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (γ.continuous.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).smul
          (h.plane.continuous.comp (γ.continuous.comp continuous_snd)))
      map_zero_left := by intro t; simp [straightCompression]
      map_one_left := by intro t; simp [straightCompression, coordinateCurve, h]
      prop' := by
        intro s
        refine ⟨?_, ?_, ?_⟩
        · change (1-(s : ℝ)) • γ initial+(s : ℝ) • h.plane (γ initial) = γ initial
          rw [he0, ← add_smul]
          simp
        · change (1-(s : ℝ)) • γ terminal+(s : ℝ) • h.plane (γ terminal) = γ terminal
          rw [he1, ← add_smul]
          simp
        · intro t ht
          constructor
          · change straightCompression R hR s (γ t) ∈ ball (0 : ℂ) B
            rw [mem_ball, dist_zero_right]
            exact (straightCompression_norm_le hR s (γ t)).trans_lt
              (by simpa using hγ.inside t ht)
          · exact straightCompression_avoids M hR hl hr s (hγ.avoids t ht) }
  let C : ContinuousMap.HomotopyWith (coordinateCurve h γ) (coordinateCurve h η) P :=
    { toContinuousMap := h.plane.comp F
      map_zero_left := by intro t; change h.plane (F (initial,t)) = h.plane (γ t); rw [h0]
      map_one_left := by intro t; change h.plane (F (terminal,t)) = h.plane (η t); rw [h1]
      prop' := by
        intro s
        refine ⟨?_, ?_, ?_⟩
        · change h.plane (F (s,initial)) = γ initial
          rw [hf0, he0]
        · change h.plane (F (s,terminal)) = γ terminal
          rw [hf1, he1]
        · intro t ht
          constructor
          · change h.plane (F (s,t)) ∈ ball (0 : ℂ) B
            rw [mem_ball, dist_zero_right]
            exact (compression_plane_bound hR (F (s,t))).trans_lt hB
          · change h.plane (F (s,t)) ∉ M.slit
            rw [← hm]
            exact (h.plane_mem_slit_iff M (F (s,t))).not.mpr (havoid s t ht) }
  have hleft : h M.left = M.left := compressCoord_fixed hl
  have href := hη.coordinateMap h
  rw [hleft] at href
  exact ⟨coordinateCurve h η,href,⟨A.trans C⟩⟩

end
end MarkedSlitTransport
