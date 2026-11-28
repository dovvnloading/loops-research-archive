import ChildSlitTransport
import MarkedSlitCompression

/-!
# Whole child-Wave compression with source-contained homotopies

The coordinate compression is the existing one from the parent development.
Here it acts on both same-bank ending intervals and on the entire homotopy
inside the source. The image of a complete geometric Borel family remains
Borel and contains every originally bounded trace. No measurability of a
selected subfamily is assumed.
-/

namespace ChildSlitModel

open Set Function MeasureTheory Metric
open MarkedSlitTransport SlitWaveModulus
open scoped ENNReal NNReal Topology

noncomputable section

def ChildMarking.coordinateMap (M : ChildMarking) (h : CoordinateEmbedding) : ChildMarking where
  left := h M.left
  firstLo := h M.firstLo
  firstHi := h M.firstHi
  secondLo := h M.secondLo
  secondHi := h M.secondHi
  right := h M.right
  left_lt_firstLo := h.strictMono M.left_lt_firstLo
  firstLo_lt_firstHi := h.strictMono M.firstLo_lt_firstHi
  firstHi_lt_secondLo := h.strictMono M.firstHi_lt_secondLo
  secondLo_lt_secondHi := h.strictMono M.secondLo_lt_secondHi
  secondHi_lt_right := h.strictMono M.secondHi_lt_right

theorem coordinate_mem_child_slit_iff (h : CoordinateEmbedding)
    (M : ChildMarking) (z : ℂ) :
    h.plane z ∈ (M.coordinateMap h).slit ↔ z ∈ M.slit :=
  h.plane_mem_slit_iff M.base z

theorem coordinate_firstEnds_iff (h : CoordinateEmbedding)
    (M : ChildMarking) (z : ℂ) :
    (M.coordinateMap h).firstEnds (h.plane z) ↔ M.firstEnds z := by
  simp only [ChildMarking.firstEnds, ChildMarking.coordinateMap, h.plane_re, h.plane_im]
  rw [← h.map_zero, h.strictMono.injective.eq_iff,
    h.strictMono.lt_iff_lt, h.strictMono.lt_iff_lt]
  rw [h.map_zero]

theorem coordinate_secondEnds_iff (h : CoordinateEmbedding)
    (M : ChildMarking) (z : ℂ) :
    (M.coordinateMap h).secondEnds (h.plane z) ↔ M.secondEnds z := by
  simp only [ChildMarking.secondEnds, ChildMarking.coordinateMap, h.plane_re, h.plane_im]
  rw [← h.map_zero, h.strictMono.injective.eq_iff,
    h.strictMono.lt_iff_lt, h.strictMono.lt_iff_lt]
  rw [h.map_zero]

theorem UpperReference.coordinateMap {γ : Curve}
    (hγ : UpperReference γ) (h : CoordinateEmbedding) :
    UpperReference (coordinateCurve h γ) where
  simple := hγ.simple.coordinateMap h
  above t ht := by simpa [h.map_zero] using h.strictMono (hγ.above t ht)

theorem RelChildHomotopy.coordinateMap {M : ChildMarking} {D : Set ℂ} {γ η : Curve}
    (hγη : RelChildHomotopy M D γ η) (h : CoordinateEmbedding) :
    RelChildHomotopy (M.coordinateMap h) (h.plane '' D)
      (coordinateCurve h γ) (coordinateCurve h η) := by
  obtain ⟨F,h0,h1,he0,he1,hinside⟩ := hγη
  refine ⟨h.plane.comp F, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; change h.plane (F (initial,t)) = h.plane (γ t); rw [h0]
  · intro t; change h.plane (F (terminal,t)) = h.plane (η t); rw [h1]
  · intro s; change h.plane (F (s,initial)) = h.plane (γ initial); rw [he0]
  · intro s; change h.plane (F (s,terminal)) = h.plane (γ terminal); rw [he1]
  · intro s t ht
    exact ⟨⟨F (s,t),(hinside s t ht).1,rfl⟩,
      fun hm => (hinside s t ht).2 ((coordinate_mem_child_slit_iff h M _).mp hm)⟩

theorem ChildLeaf.coordinateMap {M : ChildMarking} {D : Set ℂ} {γ : Curve}
    (hγ : ChildLeaf M D γ) (h : CoordinateEmbedding) :
    ChildLeaf (M.coordinateMap h) (h.plane '' D) (coordinateCurve h γ) where
  simple := hγ.simple.coordinateMap h
  first_end := (coordinate_firstEnds_iff h M _).mpr hγ.first_end
  last_end := (coordinate_secondEnds_iff h M _).mpr hγ.last_end
  initial_upper := by
    obtain ⟨ε,hε,hg⟩ := hγ.initial_upper
    exact ⟨ε,hε,fun t ht hte => by simpa [h.map_zero] using h.strictMono (hg t ht hte)⟩
  terminal_upper := by
    obtain ⟨ε,hε,hg⟩ := hγ.terminal_upper
    exact ⟨ε,hε,fun t hte ht => by simpa [h.map_zero] using h.strictMono (hg t hte ht)⟩
  inside t ht := ⟨γ t,hγ.inside t ht,rfl⟩
  avoids t ht hm := hγ.avoids t ht ((coordinate_mem_child_slit_iff h M _).mp hm)
  upper_class := by
    obtain ⟨η,hη,hγη⟩ := hγ.upper_class
    exact ⟨coordinateCurve h η,hη.coordinateMap h,hγη.coordinateMap h⟩

theorem ChildWave.coordinateMap {M : ChildMarking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ChildWave M D Γ) (h : CoordinateEmbedding) :
    ChildWave (M.coordinateMap h) (h.plane '' D) (coordinateCurve h '' Γ) := by
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

end
end ChildSlitModel

namespace ChildSlitCompression

open Set Function MeasureTheory Metric
open MarkedSlitTransport SlitWaveModulus ChildSlitModel ChildSlitTransport
open scoped ENNReal NNReal Topology

noncomputable section

theorem compression_marking_fixed (M : ChildMarking) {R : ℝ} (hR : 0 < R)
    (hl : |M.left| ≤ R) (hr : |M.right| ≤ R) :
    M.coordinateMap (compressionCoordinate R hR) = M := by
  have hfl : |M.firstLo| ≤ R := abs_le.mpr
    ⟨by linarith [(abs_le.mp hl).1,M.left_lt_firstLo],
      by linarith [(abs_le.mp hr).2,M.firstLo_lt_firstHi,M.firstHi_lt_secondLo,
        M.secondLo_lt_secondHi,M.secondHi_lt_right]⟩
  have hfh : |M.firstHi| ≤ R := abs_le.mpr
    ⟨by linarith [(abs_le.mp hl).1,M.left_lt_firstLo,M.firstLo_lt_firstHi],
      by linarith [(abs_le.mp hr).2,M.firstHi_lt_secondLo,
        M.secondLo_lt_secondHi,M.secondHi_lt_right]⟩
  have hsl : |M.secondLo| ≤ R := abs_le.mpr
    ⟨by linarith [(abs_le.mp hl).1,M.left_lt_firstLo,M.firstLo_lt_firstHi,
        M.firstHi_lt_secondLo],
      by linarith [(abs_le.mp hr).2,M.secondLo_lt_secondHi,M.secondHi_lt_right]⟩
  have hsh : |M.secondHi| ≤ R := abs_le.mpr
    ⟨by linarith [(abs_le.mp hl).1,M.left_lt_firstLo,M.firstLo_lt_firstHi,
        M.firstHi_lt_secondLo,M.secondLo_lt_secondHi],
      by linarith [(abs_le.mp hr).2,M.secondHi_lt_right]⟩
  apply marking_ext <;> apply compressCoord_fixed <;> assumption

/-- Compress every leaf and every witnessing homotopy. All originally
bounded leaves are retained literally, while the entire output is a
valid Borel Wave in a bounded source. -/
theorem exists_compressed_wave (M : ChildMarking) {Γ : Set Curve}
    (hΓ : ChildWave M univ Γ) (R : ℝ) (hR : 0 < R)
    (hl : |M.left| ≤ R) (hr : |M.right| ≤ R) :
    ∃ Δ : Set Curve, ChildWave M (closedBall (0 : ℂ) (2*(R+1))) Δ ∧
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
end ChildSlitCompression
