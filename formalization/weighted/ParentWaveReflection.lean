import SlitWaveLimit
import Mathlib.Topology.Path

/-!
# Reflection of complete upper crossing families

The construction below turns actual upper-half-plane arcs into the
repository's parent leaves by reflection and concatenation.
-/

namespace ParentWaveReflection

open Set Function MeasureTheory Metric
open MarkedSlitTransport SlitWaveModulus SlitWaveLimit
open scoped Topology ENNReal NNReal

noncomputable section

structure UpperLeaf (M : Marking) (γ : Curve) : Prop where
  injective : Injective γ
  first_end : M.ends (γ initial)
  last_real : (γ terminal).im = 0
  last_left : (γ terminal).re < M.left
  upper : ∀ t ∈ parameterInterior, 0 < (γ t).im

def curvePath (γ : Curve) : Path (γ initial) (γ terminal) where
  toContinuousMap := γ
  source' := rfl
  target' := rfl

theorem conj_eq_of_im_zero {z : ℂ} (hz : z.im = 0) : starRingEnd ℂ z = z := by
  apply Complex.ext <;> simp [hz]

def reflectedLoop {M : Marking} (γ : Curve) (hγ : UpperLeaf M γ) :
    Path (γ initial) (γ initial) :=
  (((curvePath γ).map Complex.continuous_conj).cast
    (conj_eq_of_im_zero hγ.first_end.1).symm
    (conj_eq_of_im_zero hγ.last_real).symm).trans (curvePath γ).symm

def reflectedCurve {M : Marking} (γ : Curve) (hγ : UpperLeaf M γ) : Curve :=
  (reflectedLoop γ hγ).toContinuousMap

theorem reflectedCurve_initial {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ) :
    reflectedCurve γ hγ initial = γ initial :=
  (reflectedLoop γ hγ).source

theorem reflectedCurve_terminal {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ) :
    reflectedCurve γ hγ terminal = γ initial :=
  (reflectedLoop γ hγ).target

theorem reflectedCurve_left {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ)
    (t : Parameter) (ht : (t : ℝ) ≤ 1/2) :
    reflectedCurve γ hγ t = starRingEnd ℂ (γ ⟨2*(t : ℝ), by
      constructor
      · exact mul_nonneg (by norm_num) t.2.1
      · linarith⟩) := by
  change reflectedLoop γ hγ t = _
  rw [reflectedLoop, Path.trans_apply, dif_pos ht]
  rfl

theorem reflectedCurve_right {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ)
    (t : Parameter) (ht : 1/2 < (t : ℝ)) :
    reflectedCurve γ hγ t = γ ⟨2-2*(t : ℝ), by
      constructor
      · linarith [t.2.2]
      · linarith⟩ := by
  change reflectedLoop γ hγ t = _
  rw [reflectedLoop, Path.trans_apply, dif_neg (not_le.mpr ht)]
  change γ _ = γ _
  congr 1
  apply Subtype.ext
  simp only [unitInterval.symm, sub_sub]
  ring

theorem reflectedCurve_middle {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ) :
    reflectedCurve γ hγ middle = γ terminal := by
  rw [reflectedCurve_left hγ middle (by norm_num [middle])]
  have he : (⟨2*(middle : ℝ), by norm_num [middle]⟩ : Parameter) = terminal := by
    apply Subtype.ext
    norm_num [middle, terminal]
  rw [he]
  exact conj_eq_of_im_zero hγ.last_real

theorem reflectedCurve_below {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ)
    (t : Parameter) (ht0 : 0 < (t : ℝ)) (ht : (t : ℝ) < 1/2) :
    (reflectedCurve γ hγ t).im < 0 := by
  rw [reflectedCurve_left hγ t ht.le]
  simp only [Complex.conj_im]
  have h := hγ.upper ⟨2*(t : ℝ), by constructor <;> linarith⟩
    (by constructor <;> change _ < _ <;> linarith)
  linarith

theorem reflectedCurve_above {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ)
    (t : Parameter) (ht : 1/2 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    0 < (reflectedCurve γ hγ t).im := by
  rw [reflectedCurve_right hγ t ht]
  apply hγ.upper
  constructor <;> change _ < _ <;> linarith

private theorem reflectedCurve_left_im_nonpos {M : Marking} {γ : Curve}
    (hγ : UpperLeaf M γ) (t : Parameter) (ht0 : 0 < (t : ℝ))
    (ht : (t : ℝ) ≤ 1/2) : (reflectedCurve γ hγ t).im ≤ 0 := by
  rcases ht.eq_or_lt with ht | ht
  · have he : t = middle := Subtype.ext (by simpa [middle] using ht)
    rw [he, reflectedCurve_middle hγ, hγ.last_real]
  · exact (reflectedCurve_below hγ t ht0 ht).le

theorem reflectedCurve_simple {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ) :
    Simple (reflectedCurve γ hγ) := by
  intro t ht u hu heq
  by_cases htL : (t : ℝ) ≤ 1/2
  · by_cases huL : (u : ℝ) ≤ 1/2
    · rw [reflectedCurve_left hγ t htL, reflectedCurve_left hγ u huL] at heq
      have htu := hγ.injective (Complex.conjLIE.injective heq)
      apply Subtype.ext
      have hh := congrArg (fun x : Parameter => (x : ℝ)) htu
      dsimp at hh
      linarith
    · have him := congrArg Complex.im heq
      have ha := reflectedCurve_left_im_nonpos hγ t ht.1 htL
      have hb := reflectedCurve_above hγ u (lt_of_not_ge huL) hu.2
      linarith
  · by_cases huL : (u : ℝ) ≤ 1/2
    · have him := congrArg Complex.im heq
      have ha := reflectedCurve_above hγ t (lt_of_not_ge htL) ht.2
      have hb := reflectedCurve_left_im_nonpos hγ u hu.1 huL
      linarith
    · rw [reflectedCurve_right hγ t (lt_of_not_ge htL),
        reflectedCurve_right hγ u (lt_of_not_ge huL)] at heq
      have htu := hγ.injective heq
      apply Subtype.ext
      have hh := congrArg (fun x : Parameter => (x : ℝ)) htu
      dsimp at hh
      linarith

theorem reflectedCurve_reference {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ) :
    LeftReference M.left (reflectedCurve γ hγ) where
  simple := reflectedCurve_simple hγ
  below := reflectedCurve_below hγ
  crossing_re := by rw [reflectedCurve_middle hγ]; exact hγ.last_left
  crossing_im := by rw [reflectedCurve_middle hγ]; exact hγ.last_real
  above := reflectedCurve_above hγ

theorem reflectedCurve_avoids {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ)
    (t : Parameter) (ht : t ∈ parameterInterior) :
    reflectedCurve γ hγ t ∉ M.slit := by
  intro hmem
  rcases lt_trichotomy (t : ℝ) (1/2) with h | h | h
  · have him := reflectedCurve_below hγ t ht.1 h
    exact (ne_of_lt him) hmem.1
  · have he : t = middle := Subtype.ext (by simpa [middle] using h)
    rw [he, reflectedCurve_middle hγ] at hmem
    exact (not_le_of_gt hγ.last_left) hmem.2.1
  · have him := reflectedCurve_above hγ t h ht.2
    exact (ne_of_gt him) hmem.1

theorem reflectedCurve_parentLeaf {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ) :
    ParentLeaf M univ (reflectedCurve γ hγ) where
  simple := reflectedCurve_simple hγ
  first_end := by rw [reflectedCurve_initial hγ]; exact hγ.first_end
  last_end := by rw [reflectedCurve_terminal hγ]; exact hγ.first_end
  lower := ⟨1/2, by norm_num, reflectedCurve_below hγ⟩
  upper := ⟨1/2, by norm_num, fun t ht ht1 =>
    reflectedCurve_above hγ t (by linarith) ht1⟩
  inside := fun _ _ => mem_univ _
  avoids := reflectedCurve_avoids hγ
  left_class := by
    refine ⟨reflectedCurve γ hγ, reflectedCurve_reference hγ, ?_⟩
    refine ⟨(reflectedCurve γ hγ).comp ContinuousMap.snd,
      (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), ?_⟩
    exact fun _ t ht => reflectedCurve_avoids hγ t ht

theorem reflectedCurve_trace {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ) :
    trace (reflectedCurve γ hγ) = (starRingEnd ℂ) '' trace γ ∪ trace γ := by
  change Set.range (reflectedLoop γ hγ) = _
  rw [reflectedLoop, Path.trans_range, Path.symm_range]
  change Set.range ((starRingEnd ℂ) ∘ γ) ∪ Set.range γ = _
  rw [Set.range_comp]
  rfl

private theorem parameter_mem_interior_of_ne_ends (t : Parameter)
    (ht0 : t ≠ initial) (ht1 : t ≠ terminal) : t ∈ parameterInterior := by
  constructor
  · exact lt_of_le_of_ne t.2.1 (fun he => ht0 (Subtype.ext he.symm))
  · exact lt_of_le_of_ne t.2.2 (fun he => ht1 (Subtype.ext he))

theorem UpperLeaf.trace_end_iff {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ)
    {z : ℂ} (hz : z ∈ trace γ) : M.ends z ↔ z = γ initial := by
  constructor
  · rintro hend
    obtain ⟨t, rfl⟩ := hz
    by_cases ht0 : t = initial
    · rw [ht0]
    by_cases ht1 : t = terminal
    · rw [ht1] at hend
      exact False.elim (by linarith [hend.2.1, hγ.last_left, M.left_lt_first])
    · have hi := hγ.upper t (parameter_mem_interior_of_ne_ends t ht0 ht1)
      exact False.elim (by linarith [hend.1])
  · rintro rfl
    exact hγ.first_end

theorem UpperLeaf.trace_im_nonneg {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ)
    {z : ℂ} (hz : z ∈ trace γ) : 0 ≤ z.im := by
  obtain ⟨t,rfl⟩ := hz
  by_cases ht0 : t = initial
  · rw [ht0,hγ.first_end.1]
  by_cases ht1 : t = terminal
  · rw [ht1,hγ.last_real]
  exact (hγ.upper t (parameter_mem_interior_of_ne_ends t ht0 ht1)).le

private def upperFold (z : ℂ) : ℂ := ⟨z.re,|z.im|⟩

private theorem upperFold_eq_of_nonneg {z : ℂ} (hz : 0 ≤ z.im) : upperFold z = z := by
  apply Complex.ext
  · rfl
  · exact abs_of_nonneg hz

private theorem upperFold_conj_of_nonneg {z : ℂ} (hz : 0 ≤ z.im) :
    upperFold (starRingEnd ℂ z) = z := by
  apply Complex.ext
  · rfl
  · simp only [upperFold,Complex.conj_im,abs_neg,abs_of_nonneg hz]

private theorem reflectedCurve_fold_trace {M : Marking} {γ : Curve}
    (hγ : UpperLeaf M γ) {z : ℂ} (hz : z ∈ trace (reflectedCurve γ hγ)) :
    upperFold z ∈ trace γ := by
  rw [reflectedCurve_trace] at hz
  rcases hz with ⟨w,hw,rfl⟩ | hz
  · rw [upperFold_conj_of_nonneg (hγ.trace_im_nonneg hw)]
    exact hw
  · rw [upperFold_eq_of_nonneg (hγ.trace_im_nonneg hz)]
    exact hz

theorem reflectedCurve_interiorTrace {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ) :
    interiorTrace (reflectedCurve γ hγ) =
      ((starRingEnd ℂ) '' trace γ ∪ trace γ) \ {z | M.ends z} := by
  ext z
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← reflectedCurve_trace hγ]
      exact ⟨t,rfl⟩
    · intro he
      exact reflectedCurve_avoids hγ t ht
        ⟨he.1, (M.left_lt_first.trans he.2.1).le,
          (he.2.2.trans M.second_lt_right).le⟩
  · rintro ⟨hz,hn⟩
    rw [← reflectedCurve_trace hγ] at hz
    obtain ⟨t,rfl⟩ := hz
    refine ⟨t,parameter_mem_interior_of_ne_ends t ?_ ?_,rfl⟩
    · intro he
      rw [he,reflectedCurve_initial hγ] at hn
      exact hn hγ.first_end
    · intro he
      rw [he,reflectedCurve_terminal hγ] at hn
      exact hn hγ.first_end

def upperSupport (Γ : Set Curve) : Set ℂ := ⋃ γ ∈ Γ, trace γ

structure UpperWave (M : Marking) (Γ : Set Curve) : Prop where
  borel : MeasurableSet (upperSupport Γ)
  leaf : ∀ γ ∈ Γ, UpperLeaf M γ
  disjoint : ∀ γ ∈ Γ, ∀ η ∈ Γ, γ ≠ η → Disjoint (trace γ) (trace η)

def reflectedFamily {M : Marking} {Γ : Set Curve} (hΓ : UpperWave M Γ) : Set Curve :=
  {η | ∃ (γ : Curve) (hγ : γ ∈ Γ), η = reflectedCurve γ (hΓ.leaf γ hγ)}

theorem reflectedFamily_support {M : Marking} {Γ : Set Curve} (hΓ : UpperWave M Γ) :
    MarkedSlitTransport.support (reflectedFamily hΓ) =
      ((starRingEnd ℂ) '' upperSupport Γ ∪ upperSupport Γ) \ {z | M.ends z} := by
  ext z
  simp only [MarkedSlitTransport.support, reflectedFamily, mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨η,⟨γ,hγ,rfl⟩,hz⟩
    rw [reflectedCurve_interiorTrace] at hz
    refine ⟨?_,hz.2⟩
    rcases hz.1 with ⟨w,hw,rfl⟩ | hz
    · exact Or.inl ⟨w,by simp only [upperSupport,mem_iUnion]; exact ⟨γ,hγ,hw⟩,rfl⟩
    · exact Or.inr (by simp only [upperSupport,mem_iUnion]; exact ⟨γ,hγ,hz⟩)
  · rintro ⟨hz,hn⟩
    rcases hz with ⟨w,hw,rfl⟩ | hz
    · simp only [upperSupport,mem_iUnion] at hw
      obtain ⟨γ,hγ,hw⟩ := hw
      refine ⟨reflectedCurve γ (hΓ.leaf γ hγ),⟨γ,hγ,rfl⟩,?_⟩
      rw [reflectedCurve_interiorTrace]
      exact ⟨Or.inl ⟨w,hw,rfl⟩,hn⟩
    · simp only [upperSupport,mem_iUnion] at hz
      obtain ⟨γ,hγ,hz⟩ := hz
      refine ⟨reflectedCurve γ (hΓ.leaf γ hγ),⟨γ,hγ,rfl⟩,?_⟩
      rw [reflectedCurve_interiorTrace]
      exact ⟨Or.inr hz,hn⟩

theorem reflectedFamily_parentWave {M : Marking} {Γ : Set Curve} (hΓ : UpperWave M Γ) :
    ParentWave M univ (reflectedFamily hΓ) where
  borel := by
    rw [reflectedFamily_support]
    apply MeasurableSet.diff
    · exact ((Complex.conjLIE.toHomeomorph.measurableEmbedding.measurableSet_image).mpr
        hΓ.borel).union hΓ.borel
    · change MeasurableSet ({z : ℂ | z.im = 0} ∩
        ({z : ℂ | M.first < z.re} ∩ {z : ℂ | z.re < M.second}))
      exact (isClosed_eq Complex.continuous_im continuous_const).measurableSet.inter
        ((isOpen_lt continuous_const Complex.continuous_re).measurableSet.inter
          (isOpen_lt Complex.continuous_re continuous_const).measurableSet)
  leaf := by
    rintro η ⟨γ,hγ,rfl⟩
    exact reflectedCurve_parentLeaf (hΓ.leaf γ hγ)
  disjoint := by
    rintro ξ ⟨γ,hγ,rfl⟩ ζ ⟨η,hη,rfl⟩ hne
    have hγη : γ ≠ η := by
      intro he
      subst η
      exact hne rfl
    apply Set.disjoint_left.mpr
    intro z hzγ hzη
    have h1 := reflectedCurve_fold_trace (hΓ.leaf γ hγ)
      (interiorTrace_subset_trace _ hzγ)
    have h2 := reflectedCurve_fold_trace (hΓ.leaf η hη)
      (interiorTrace_subset_trace _ hzη)
    exact (Set.disjoint_left.mp (hΓ.disjoint γ hγ η hη hγη)) h1 h2

end

end ParentWaveReflection
