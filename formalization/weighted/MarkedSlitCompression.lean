import MarkedSlitTransport

/-!
# Compression of a whole geometrically Borel Wave

A coordinatewise increasing embedding fixes a prescribed square and sends
the entire plane into a bounded square.  Applying it to a whole Wave
preserves its Borel geometric support and its complete marked homotopy
class.  Every curve already contained in the prescribed disk is literally
unchanged.  Thus modulus cutoff estimates never require a Borel
parametrization of the leaf space, or a Borel assertion about the discarded
leaf selection.
-/

namespace MarkedSlitTransport

open Set Function MeasureTheory Metric
open scoped Topology NNReal ENNReal

noncomputable section

def softTail (x : ℝ) : ℝ := x/(1+x)

theorem softTail_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ softTail x := by
  exact div_nonneg hx (by linarith)

theorem softTail_lt_one {x : ℝ} (hx : 0 ≤ x) : softTail x < 1 := by
  exact (div_lt_one (by linarith : 0 < 1+x)).2 (by linarith)

theorem softTail_strictMonoOn : StrictMonoOn softTail (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  change x/(1+x) < y/(1+y)
  apply (div_lt_div_iff₀ (by linarith [hx] : 0 < 1+x)
    (by linarith [hy] : 0 < 1+y)).2
  nlinarith

/-- The center interval is fixed.  Outside it, the two tails have length
strictly less than one.  The formula has no discontinuous case selection. -/
def compressCoord (R x : ℝ) : ℝ :=
  min R (max (-R) x) + softTail (max 0 (x-R)) - softTail (max 0 (-x-R))

theorem compressCoord_continuous (R : ℝ) : Continuous (compressCoord R) := by
  have hu : Continuous (fun x : ℝ => max 0 (x-R)) :=
    continuous_const.max (continuous_id.sub continuous_const)
  have hl : Continuous (fun x : ℝ => max 0 (-x-R)) :=
    continuous_const.max (continuous_id.neg.sub continuous_const)
  have hu' : Continuous (fun x : ℝ => softTail (max 0 (x-R))) := by
    exact hu.div (continuous_const.add hu) fun x => by
      have hx := le_max_left (0 : ℝ) (x-R)
      positivity
  have hl' : Continuous (fun x : ℝ => softTail (max 0 (-x-R))) := by
    exact hl.div (continuous_const.add hl) fun x => by
      have hx := le_max_left (0 : ℝ) (-x-R)
      positivity
  exact ((continuous_const.min (continuous_const.max continuous_id)).add hu').sub hl'

theorem compressCoord_of_le {R x : ℝ} (hR : 0 ≤ R) (hx : x ≤ -R) :
    compressCoord R x = -R-softTail (-x-R) := by
  have hxR : x-R ≤ 0 := by linarith
  have hnxR : 0 ≤ -x-R := by linarith
  simp [compressCoord, max_eq_left hx, min_eq_right (by linarith : -R ≤ R),
    max_eq_left hxR, max_eq_right hnxR, softTail]

theorem compressCoord_of_mem {R x : ℝ} (hx : x ∈ Icc (-R) R) :
    compressCoord R x = x := by
  have hxR : x-R ≤ 0 := by linarith [hx.2]
  have hnxR : -x-R ≤ 0 := by linarith [hx.1]
  simp [compressCoord, max_eq_right hx.1, min_eq_right hx.2,
    max_eq_left hxR, max_eq_left hnxR, softTail]

theorem compressCoord_of_ge {R x : ℝ} (hR : 0 ≤ R) (hx : R ≤ x) :
    compressCoord R x = R+softTail (x-R) := by
  have hxlo : -R ≤ x := by linarith
  have hxR : 0 ≤ x-R := by linarith
  have hnxR : -x-R ≤ 0 := by linarith
  simp [compressCoord, max_eq_right hxlo, min_eq_left hx,
    max_eq_right hxR, max_eq_left hnxR, softTail]

theorem compressCoord_fixed {R x : ℝ} (hx : |x| ≤ R) : compressCoord R x = x :=
  compressCoord_of_mem (abs_le.mp hx)

theorem compressCoord_strictMono {R : ℝ} (hR : 0 < R) :
    StrictMono (compressCoord R) := by
  intro x y hxy
  by_cases hylo : y ≤ -R
  · have hxlo : x ≤ -R := hxy.le.trans hylo
    rw [compressCoord_of_le hR.le hxlo, compressCoord_of_le hR.le hylo]
    have h := softTail_strictMonoOn
      (by change 0 ≤ -y-R; linarith) (by change 0 ≤ -x-R; linarith)
      (by linarith : -y-R < -x-R)
    linarith
  · have hylo' : -R < y := lt_of_not_ge hylo
    by_cases hxhi : R ≤ x
    · have hyhi : R ≤ y := hxhi.trans hxy.le
      rw [compressCoord_of_ge hR.le hxhi, compressCoord_of_ge hR.le hyhi]
      have h := softTail_strictMonoOn
        (by change 0 ≤ x-R; linarith) (by change 0 ≤ y-R; linarith)
        (by linarith : x-R < y-R)
      linarith
    · have hxhi' : x < R := lt_of_not_ge hxhi
      by_cases hxlo : x ≤ -R
      · rw [compressCoord_of_le hR.le hxlo]
        have hxnonneg := softTail_nonneg (by linarith : 0 ≤ -x-R)
        by_cases hyhi : R ≤ y
        · rw [compressCoord_of_ge hR.le hyhi]
          have hynonneg := softTail_nonneg (by linarith : 0 ≤ y-R)
          linarith
        · rw [compressCoord_of_mem ⟨hylo'.le,(lt_of_not_ge hyhi).le⟩]
          linarith
      · have hxlo' : -R < x := lt_of_not_ge hxlo
        rw [compressCoord_of_mem ⟨hxlo'.le,hxhi'.le⟩]
        by_cases hyhi : R ≤ y
        · rw [compressCoord_of_ge hR.le hyhi]
          have hynonneg := softTail_nonneg (by linarith : 0 ≤ y-R)
          linarith
        · rw [compressCoord_of_mem ⟨hylo'.le,(lt_of_not_ge hyhi).le⟩]
          exact hxy

theorem compressCoord_abs_lt {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |compressCoord R x| < R+1 := by
  by_cases hxlo : x ≤ -R
  · rw [compressCoord_of_le hR.le hxlo]
    have h0 := softTail_nonneg (by linarith : 0 ≤ -x-R)
    have h1 := softTail_lt_one (by linarith : 0 ≤ -x-R)
    rw [abs_of_neg (by linarith : -R-softTail (-x-R) < 0)]
    linarith
  · by_cases hxhi : R ≤ x
    · rw [compressCoord_of_ge hR.le hxhi]
      have h0 := softTail_nonneg (by linarith : 0 ≤ x-R)
      have h1 := softTail_lt_one (by linarith : 0 ≤ x-R)
      rw [abs_of_pos (by linarith : 0 < R+softTail (x-R))]
      linarith
    · rw [compressCoord_of_mem ⟨(lt_of_not_ge hxlo).le,(lt_of_not_ge hxhi).le⟩]
      exact (abs_le.mpr ⟨(lt_of_not_ge hxlo).le,(lt_of_not_ge hxhi).le⟩).trans_lt
        (by linarith)

/-- A continuous increasing coordinate embedding fixing zero.  Surjectivity
is deliberately absent: a compression maps the plane into a bounded open set. -/
structure CoordinateEmbedding where
  toFun : ℝ → ℝ
  continuous : Continuous toFun
  strictMono : StrictMono toFun
  map_zero : toFun 0 = 0

instance : CoeFun CoordinateEmbedding (fun _ => ℝ → ℝ) := ⟨CoordinateEmbedding.toFun⟩

def compressionCoordinate (R : ℝ) (hR : 0 < R) : CoordinateEmbedding where
  toFun := compressCoord R
  continuous := compressCoord_continuous R
  strictMono := compressCoord_strictMono hR
  map_zero := compressCoord_fixed (by simpa using hR.le)

def CoordinateEmbedding.plane (h : CoordinateEmbedding) : C(ℂ, ℂ) where
  toFun z := (h z.re : ℂ)+(h z.im : ℂ)*Complex.I
  continuous_toFun :=
    (Complex.continuous_ofReal.comp (h.continuous.comp Complex.continuous_re)).add
      ((Complex.continuous_ofReal.comp (h.continuous.comp Complex.continuous_im)).mul
        continuous_const)

@[simp] theorem CoordinateEmbedding.plane_re (h : CoordinateEmbedding) (z : ℂ) :
    (h.plane z).re = h z.re := by simp [CoordinateEmbedding.plane]

@[simp] theorem CoordinateEmbedding.plane_im (h : CoordinateEmbedding) (z : ℂ) :
    (h.plane z).im = h z.im := by simp [CoordinateEmbedding.plane]

theorem CoordinateEmbedding.plane_injective (h : CoordinateEmbedding) : Injective h.plane := by
  intro z w heq
  apply Complex.ext
  · exact h.strictMono.injective (by simpa using congrArg Complex.re heq)
  · exact h.strictMono.injective (by simpa using congrArg Complex.im heq)

def Marking.coordinateMap (M : Marking) (h : CoordinateEmbedding) : Marking where
  left := h M.left
  first := h M.first
  second := h M.second
  right := h M.right
  left_lt_first := h.strictMono M.left_lt_first
  first_lt_second := h.strictMono M.first_lt_second
  second_lt_right := h.strictMono M.second_lt_right

theorem CoordinateEmbedding.plane_mem_slit_iff (h : CoordinateEmbedding)
    (M : Marking) (z : ℂ) :
    h.plane z ∈ (M.coordinateMap h).slit ↔ z ∈ M.slit := by
  simp only [Marking.slit, Marking.coordinateMap, mem_setOf_eq, h.plane_re, h.plane_im]
  rw [← h.map_zero, h.strictMono.injective.eq_iff,
    h.strictMono.le_iff_le, h.strictMono.le_iff_le]
  rw [h.map_zero]

theorem CoordinateEmbedding.plane_ends_iff (h : CoordinateEmbedding)
    (M : Marking) (z : ℂ) :
    (M.coordinateMap h).ends (h.plane z) ↔ M.ends z := by
  simp only [Marking.ends, Marking.coordinateMap, h.plane_re, h.plane_im]
  rw [← h.map_zero, h.strictMono.injective.eq_iff,
    h.strictMono.lt_iff_lt, h.strictMono.lt_iff_lt]
  rw [h.map_zero]

def coordinateCurve (h : CoordinateEmbedding) (γ : Curve) : Curve := h.plane.comp γ

@[simp] theorem coordinateCurve_apply (h : CoordinateEmbedding) (γ : Curve) (t : Parameter) :
    coordinateCurve h γ t = h.plane (γ t) := rfl

theorem coordinateCurve_injective (h : CoordinateEmbedding) : Injective (coordinateCurve h) := by
  intro γ η heq
  ext t
  exact h.plane_injective (congrArg (fun f : Curve => f t) heq)

theorem interiorTrace_coordinateCurve (h : CoordinateEmbedding) (γ : Curve) :
    interiorTrace (coordinateCurve h γ) = h.plane '' interiorTrace γ := by
  rw [interiorTrace, interiorTrace, ← image_comp]
  rfl

theorem support_coordinateCurve (h : CoordinateEmbedding) (Γ : Set Curve) :
    support (coordinateCurve h '' Γ) = h.plane '' support Γ := by
  ext z
  simp only [support, mem_iUnion, mem_image]
  constructor
  · rintro ⟨_,⟨γ,hγ,rfl⟩,hz⟩
    rw [interiorTrace_coordinateCurve] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    exact ⟨w,⟨γ,hγ,hw⟩,rfl⟩
  · rintro ⟨w,⟨γ,hγ,hw⟩,rfl⟩
    refine ⟨coordinateCurve h γ,⟨γ,hγ,rfl⟩,?_⟩
    rw [interiorTrace_coordinateCurve]
    exact ⟨w,hw,rfl⟩

theorem Simple.coordinateMap {γ : Curve} (hγ : Simple γ) (h : CoordinateEmbedding) :
    Simple (coordinateCurve h γ) := by
  intro s hs t ht heq
  exact hγ hs ht (h.plane_injective heq)

theorem LeftReference.coordinateMap {left : ℝ} {γ : Curve}
    (hγ : LeftReference left γ) (h : CoordinateEmbedding) :
    LeftReference (h left) (coordinateCurve h γ) where
  simple := hγ.simple.coordinateMap h
  below t ht htm := by
    simpa [h.map_zero] using h.strictMono (hγ.below t ht htm)
  crossing_re := by simpa using h.strictMono hγ.crossing_re
  crossing_im := by simp [hγ.crossing_im, h.map_zero]
  above t htm ht := by
    simpa [h.map_zero] using h.strictMono (hγ.above t htm ht)

theorem RelSlitHomotopy.coordinateMap {M : Marking} {γ η : Curve}
    (hγη : RelSlitHomotopy M γ η) (h : CoordinateEmbedding) :
    RelSlitHomotopy (M.coordinateMap h) (coordinateCurve h γ) (coordinateCurve h η) := by
  obtain ⟨F,h0,h1,he0,he1,havoid⟩ := hγη
  refine ⟨h.plane.comp F, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; change h.plane (F (initial,t)) = h.plane (γ t); rw [h0]
  · intro t; change h.plane (F (terminal,t)) = h.plane (η t); rw [h1]
  · intro s; change h.plane (F (s,initial)) = h.plane (γ initial); rw [he0]
  · intro s; change h.plane (F (s,terminal)) = h.plane (γ terminal); rw [he1]
  · intro s t ht hmem
    exact havoid s t ht ((h.plane_mem_slit_iff M (F (s,t))).mp hmem)

theorem ParentLeaf.coordinateMap {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) (h : CoordinateEmbedding) :
    ParentLeaf (M.coordinateMap h) (h.plane '' D) (coordinateCurve h γ) where
  simple := hγ.simple.coordinateMap h
  first_end := (h.plane_ends_iff M _).mpr hγ.first_end
  last_end := (h.plane_ends_iff M _).mpr hγ.last_end
  lower := by
    obtain ⟨ε,hε,hg⟩ := hγ.lower
    exact ⟨ε,hε,fun t ht hte => by simpa [h.map_zero] using h.strictMono (hg t ht hte)⟩
  upper := by
    obtain ⟨ε,hε,hg⟩ := hγ.upper
    exact ⟨ε,hε,fun t hte ht => by simpa [h.map_zero] using h.strictMono (hg t hte ht)⟩
  inside t ht := ⟨γ t,hγ.inside t ht,rfl⟩
  avoids t ht hmem := hγ.avoids t ht ((h.plane_mem_slit_iff M _).mp hmem)
  left_class := by
    obtain ⟨η,hη,hγη⟩ := hγ.left_class
    exact ⟨coordinateCurve h η,hη.coordinateMap h,hγη.coordinateMap h⟩

theorem ParentWave.coordinateMap {M : Marking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ParentWave M D Γ) (h : CoordinateEmbedding) :
    ParentWave (M.coordinateMap h) (h.plane '' D) (coordinateCurve h '' Γ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [support_coordinateCurve]
    exact hΓ.borel.image_of_measurable_injOn h.plane.continuous.measurable
      h.plane_injective.injOn
  · rintro _ ⟨γ,hγ,rfl⟩
    exact (hΓ.leaf γ hγ).coordinateMap h
  · rintro _ ⟨γ,hγ,rfl⟩ _ ⟨η,hη,rfl⟩ hne
    have hne' : γ ≠ η := fun heq => hne (congrArg (coordinateCurve h) heq)
    rw [interiorTrace_coordinateCurve, interiorTrace_coordinateCurve]
    exact Set.disjoint_image_of_injective h.plane_injective
      (hΓ.disjoint γ hγ η hη hne')

theorem compression_plane_fixed {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    (compressionCoordinate R hR).plane z = z := by
  apply Complex.ext
  · rw [CoordinateEmbedding.plane_re]
    exact compressCoord_fixed ((Complex.abs_re_le_norm z).trans hz)
  · rw [CoordinateEmbedding.plane_im]
    exact compressCoord_fixed ((Complex.abs_im_le_norm z).trans hz)

theorem compression_plane_bound {R : ℝ} (hR : 0 < R) (z : ℂ) :
    ‖(compressionCoordinate R hR).plane z‖ ≤ 2*(R+1) := by
  have hre := compressCoord_abs_lt hR z.re
  have him := compressCoord_abs_lt hR z.im
  have htri := norm_add_le ((compressCoord R z.re : ℝ) : ℂ)
    (((compressCoord R z.im : ℝ) : ℂ)*Complex.I)
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at htri
  exact htri.trans (by linarith : |compressCoord R z.re|+|compressCoord R z.im| ≤ 2*(R+1))

theorem compression_marking_fixed (M : Marking) {R : ℝ} (hR : 0 < R)
    (hl : |M.left| ≤ R) (hr : |M.right| ≤ R) :
    M.coordinateMap (compressionCoordinate R hR) = M := by
  have hfirst : |M.first| ≤ R := abs_le.mpr ⟨by linarith [(abs_le.mp hl).1, M.left_lt_first],
    by linarith [(abs_le.mp hr).2, M.first_lt_second, M.second_lt_right]⟩
  have hsecond : |M.second| ≤ R := abs_le.mpr
    ⟨by linarith [(abs_le.mp hl).1, M.left_lt_first, M.first_lt_second],
      by linarith [(abs_le.mp hr).2, M.second_lt_right]⟩
  ext <;> apply compressCoord_fixed <;> assumption

/-- Compressing the entire geometric Borel Wave produces a bounded Wave
in the same marked class and retains every originally bounded trace
literally.  No Borel assertion about that selected leaf subset is used. -/
theorem exists_compressed_wave (M : Marking) {Γ : Set Curve}
    (hΓ : ParentWave M univ Γ) (R : ℝ) (hR : 0 < R)
    (hl : |M.left| ≤ R) (hr : |M.right| ≤ R) :
    ∃ Δ : Set Curve, ParentWave M (closedBall (0 : ℂ) (2*(R+1))) Δ ∧
      traces (Γ ∩ boundedCurves R) ⊆ traces Δ := by
  let h := compressionCoordinate R hR
  refine ⟨coordinateCurve h '' Γ, ?_, ?_⟩
  · have hw := hΓ.coordinateMap h
    rw [show M.coordinateMap h = M from compression_marking_fixed M hR hl hr] at hw
    apply hw.mono
    rintro _ ⟨z,_,rfl⟩
    simpa using compression_plane_bound hR z
  · rintro _ ⟨γ,⟨hγ,hbound⟩,rfl⟩
    refine ⟨coordinateCurve h γ,⟨γ,hγ,rfl⟩,?_⟩
    have heq : coordinateCurve h γ = γ := by
      ext t
      exact compression_plane_fixed hR (hbound t)
    rw [heq]

end
end MarkedSlitTransport
