import ChildSlitModel

/-!
# Whole-family transport of the same-bank child class

Increasing horizontal homeomorphisms transport all six physical cuts,
both upper accesses, and the entire fixed-endpoint homotopy. The Borel
geometric support and disjoint interiors are transported without choosing
or discarding leaves. Quantitative modulus comparison therefore applies
to the supremum of the complete marked family class.
-/

namespace ChildSlitModel

open Set Function MeasureTheory Metric
open MarkedSlitTransport SlitWaveModulus
open scoped ENNReal NNReal Topology

noncomputable section

def ChildMarking.map (M : ChildMarking) (h : ℝ ≃o ℝ) : ChildMarking where
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

theorem ChildMarking.base_map (M : ChildMarking) (h : ℝ ≃o ℝ) :
    (M.map h).base = M.base.map h := rfl

theorem horizontal_mem_child_slit_iff (M : ChildMarking) (h : ℝ ≃o ℝ) (z : ℂ) :
    horizontal h z ∈ (M.map h).slit ↔ z ∈ M.slit := by
  exact horizontal_mem_slit_iff M.base h z

theorem horizontal_firstEnds_iff (M : ChildMarking) (h : ℝ ≃o ℝ) (z : ℂ) :
    (M.map h).firstEnds (horizontal h z) ↔ M.firstEnds z := by
  simp [ChildMarking.firstEnds, ChildMarking.map]

theorem horizontal_secondEnds_iff (M : ChildMarking) (h : ℝ ≃o ℝ) (z : ℂ) :
    (M.map h).secondEnds (horizontal h z) ↔ M.secondEnds z := by
  simp [ChildMarking.secondEnds, ChildMarking.map]

theorem InitialUpperBank.map {γ : Curve} (hγ : InitialUpperBank γ) (h : ℝ ≃o ℝ) :
    InitialUpperBank (mapCurve h γ) := by
  obtain ⟨ε,hε,hγ⟩ := hγ
  exact ⟨ε,hε,fun t ht hte => by simpa using hγ t ht hte⟩

theorem UpperReference.map {γ : Curve} (hγ : UpperReference γ) (h : ℝ ≃o ℝ) :
    UpperReference (mapCurve h γ) where
  simple := hγ.simple.map h
  above t ht := by simpa using hγ.above t ht

theorem RelChildHomotopy.map {M : ChildMarking} {D : Set ℂ} {γ η : Curve}
    (hγη : RelChildHomotopy M D γ η) (h : ℝ ≃o ℝ) :
    RelChildHomotopy (M.map h) (horizontal h '' D) (mapCurve h γ) (mapCurve h η) := by
  obtain ⟨F,h0,h1,he0,he1,hF⟩ := hγη
  refine ⟨(toContinuousMap (horizontal h)).comp F, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    change horizontal h (F (initial,t)) = horizontal h (γ t)
    rw [h0]
  · intro t
    change horizontal h (F (terminal,t)) = horizontal h (η t)
    rw [h1]
  · intro s
    change horizontal h (F (s,initial)) = horizontal h (γ initial)
    rw [he0]
  · intro s
    change horizontal h (F (s,terminal)) = horizontal h (γ terminal)
    rw [he1]
  · intro s t ht
    refine ⟨⟨F (s,t),(hF s t ht).1,rfl⟩,?_⟩
    intro hmem
    exact (hF s t ht).2 ((horizontal_mem_child_slit_iff M h (F (s,t))).mp hmem)

theorem UpperClass.map {M : ChildMarking} {D : Set ℂ} {γ : Curve}
    (hγ : UpperClass M D γ) (h : ℝ ≃o ℝ) :
    UpperClass (M.map h) (horizontal h '' D) (mapCurve h γ) := by
  obtain ⟨η,hη,hγη⟩ := hγ
  exact ⟨mapCurve h η,hη.map h,hγη.map h⟩

theorem ChildLeaf.map {M : ChildMarking} {D : Set ℂ} {γ : Curve}
    (hγ : ChildLeaf M D γ) (h : ℝ ≃o ℝ) :
    ChildLeaf (M.map h) (horizontal h '' D) (mapCurve h γ) where
  simple := hγ.simple.map h
  first_end := (horizontal_firstEnds_iff M h _).mpr hγ.first_end
  last_end := (horizontal_secondEnds_iff M h _).mpr hγ.last_end
  initial_upper := hγ.initial_upper.map h
  terminal_upper := hγ.terminal_upper.map h
  inside t ht := ⟨γ t,hγ.inside t ht,rfl⟩
  avoids t ht hmem := hγ.avoids t ht ((horizontal_mem_child_slit_iff M h _).mp hmem)
  upper_class := hγ.upper_class.map h

theorem ChildWave.map {M : ChildMarking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ChildWave M D Γ) (h : ℝ ≃o ℝ) :
    ChildWave (M.map h) (horizontal h '' D) (mapCurve h '' Γ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [support_mapCurve]
    exact (horizontal h).measurableEmbedding.measurableSet_image.mpr hΓ.borel
  · rintro _ ⟨γ,hγ,rfl⟩
    exact (hΓ.leaf γ hγ).map h
  · rintro _ ⟨γ,hγ,rfl⟩ _ ⟨η,hη,rfl⟩ hne
    have hne' : γ ≠ η := fun heq => hne (congrArg (mapCurve h) heq)
    rw [interiorTrace_mapCurve, interiorTrace_mapCurve]
    exact Set.disjoint_image_of_injective (horizontal h).injective
      (hΓ.disjoint γ hγ η hη hne')

end
end ChildSlitModel

namespace ChildSlitTransport

open Set Function MeasureTheory Metric
open MarkedSlitTransport SlitWaveModulus ChildSlitModel
open scoped ENNReal NNReal Topology

noncomputable section

def markCoords (M : ChildMarking) : Fin 6 → ℝ :=
  ![M.left, M.firstLo, M.firstHi, M.secondLo, M.secondHi, M.right]

theorem marking_ext {M A : ChildMarking}
    (hl : M.left = A.left) (ha : M.firstLo = A.firstLo)
    (hb : M.firstHi = A.firstHi) (hc : M.secondLo = A.secondLo)
    (hd : M.secondHi = A.secondHi) (hr : M.right = A.right) : M = A := by
  cases M
  cases A
  simp_all

theorem marking_map_eq {M A : ChildMarking} {h : ℝ ≃o ℝ}
    (hh : ∀ i, h (markCoords M i) = markCoords A i) : M.map h = A := by
  apply marking_ext
  · exact hh 0
  · exact hh 1
  · exact hh 2
  · exact hh 3
  · exact hh 4
  · exact hh 5

theorem marking_map_symm (M : ChildMarking) (h : ℝ ≃o ℝ) :
    (M.map h).map h.symm = M := by
  apply marking_ext <;> simp [ChildMarking.map]

theorem traces_map (h : ℝ ≃o ℝ) (Γ : Set Curve) :
    traces (mapCurve h '' Γ) = transportFamily (horizontal h) (traces Γ) :=
  traces_mapCurve h Γ

/-- The forward comparison transports every complete child Wave. -/
theorem width_le_mul_width (M : ChildMarking) {D E : Set ℂ} (h : ℝ ≃o ℝ)
    {L K : ℝ≥0} (hL : LipschitzWith L (horizontal h))
    (hK : LipschitzWith K (horizontal h).symm)
    (hL0 : L ≠ 0) (hK0 : K ≠ 0) (hDE : horizontal h '' D ⊆ E) :
    width M D ≤ ((K : ℝ≥0∞)^2 * (L : ℝ≥0∞)^2) * width (M.map h) E := by
  apply iSup₂_le
  intro Γ hΓ
  have hm := modulus_le_mul_transport (horizontal h) hL hK hL0 hK0 (traces Γ)
  rw [← traces_map] at hm
  exact hm.trans (mul_le_mul_left' (modulus_le_width ((hΓ.map h).mono hDE)) _)

/-- The same argument applied to the inverse moves all target Waves
back, so the transport controls the full target supremum as well. -/
theorem width_map_le_mul_width (M : ChildMarking) (h : ℝ ≃o ℝ)
    {D E : Set ℂ} {L K : ℝ≥0} (hL : LipschitzWith L (horizontal h))
    (hK : LipschitzWith K (horizontal h).symm)
    (hL0 : L ≠ 0) (hK0 : K ≠ 0) (hED : (horizontal h).symm '' E ⊆ D) :
    width (M.map h) E ≤ ((K : ℝ≥0∞)^2 * (L : ℝ≥0∞)^2) * width M D := by
  have hK' : LipschitzWith K (horizontal h.symm) := by
    rw [horizontal_symm h]
    exact hK
  have hL' : LipschitzWith L (horizontal h.symm).symm := by
    rw [horizontal_symm h, Homeomorph.symm_symm]
    exact hL
  have himage : horizontal h.symm '' E ⊆ D := by
    simpa only [horizontal_symm] using hED
  have hw := width_le_mul_width (M.map h) h.symm hK' hL' hK0 hL0 himage
  rw [marking_map_symm M h] at hw
  simpa only [mul_comm] using hw

end
end ChildSlitTransport
