import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel

/-!
# Complete simple parent arcs and horizontal marked-slit transport

The curves in this file are arbitrary continuous simple proper arcs.  No
finite-length, smoothness, bounded-turning, or graph assumption is made.
The two physical endpoints may coincide: they lie on opposite accesses to
the slit.  The selected relative class is specified by an actual homotopy
to a path crossing the real line once, to the left of the slit.  Its
transport is proved by composing that homotopy with an explicit plane
homeomorphism, rather than postulating invariance of a class predicate.

The family model imposes the geometric Borel-support condition on arbitrary
families of parametrized arcs with pairwise-disjoint interiors.  No Borel
parametrization of the leaf space is required.  Horizontal transport acts
on the entire geometric support by a plane homeomorphism.
-/

namespace MarkedSlitTransport

open Set Function MeasureTheory Metric
open scoped Topology NNReal ENNReal

noncomputable section

abbrev Parameter := Set.Icc (0 : ℝ) 1
abbrev Curve := C(Parameter, ℂ)

instance curveMeasurableSpace : MeasurableSpace Curve := borel Curve
instance curveBorelSpace : BorelSpace Curve := ⟨rfl⟩

def initial : Parameter := ⟨0, by norm_num⟩
def terminal : Parameter := ⟨1, by norm_num⟩
def middle : Parameter := ⟨1/2, by norm_num⟩

def parameterInterior : Set Parameter := {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1}

def trace (γ : Curve) : Set ℂ := Set.range γ

def interiorTrace (γ : Curve) : Set ℂ := γ '' parameterInterior

theorem interiorTrace_subset_trace (γ : Curve) : interiorTrace γ ⊆ trace γ := by
  rintro z ⟨t, _, rfl⟩
  exact ⟨t, rfl⟩

theorem trace_isCompact (γ : Curve) : IsCompact (trace γ) :=
  isCompact_range γ.continuous

theorem trace_isPreconnected (γ : Curve) : IsPreconnected (trace γ) := by
  simpa only [trace, image_univ] using
    isPreconnected_univ.image γ γ.continuous.continuousOn

theorem parameterInterior_isOpen : IsOpen parameterInterior := by
  exact (isOpen_lt continuous_const continuous_subtype_val).inter
    (isOpen_lt continuous_subtype_val continuous_const)

/-- The four ordered physical cuts needed by the complete parent base.
The open ending atoms are the two banks over `(first, second)`. -/
@[ext] structure Marking where
  left : ℝ
  first : ℝ
  second : ℝ
  right : ℝ
  left_lt_first : left < first
  first_lt_second : first < second
  second_lt_right : second < right

def Marking.slit (M : Marking) : Set ℂ :=
  {z | z.im = 0 ∧ M.left ≤ z.re ∧ z.re ≤ M.right}

def Marking.ends (M : Marking) (z : ℂ) : Prop :=
  z.im = 0 ∧ M.first < z.re ∧ z.re < M.second

def Simple (γ : Curve) : Prop := InjOn γ parameterInterior

def LowerBank (γ : Curve) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ t : Parameter,
    0 < (t : ℝ) → (t : ℝ) < ε → (γ t).im < 0

def UpperBank (γ : Curve) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ t : Parameter,
    1-ε < (t : ℝ) → (t : ℝ) < 1 → 0 < (γ t).im

/-- A concrete simple reference arc for the left relative class.  It is
strictly below the slit until the midpoint, crosses to its left, and is
strictly above the slit thereafter.  The endpoints are supplied by the
relative homotopy. -/
structure LeftReference (left : ℝ) (γ : Curve) : Prop where
  simple : Simple γ
  below : ∀ t : Parameter, 0 < (t : ℝ) → (t : ℝ) < 1/2 → (γ t).im < 0
  crossing_re : (γ middle).re < left
  crossing_im : (γ middle).im = 0
  above : ∀ t : Parameter, 1/2 < (t : ℝ) → (t : ℝ) < 1 → 0 < (γ t).im

/-- A literal relative-endpoint homotopy in the plane minus the slit.
Every intermediate path has its complete open interval off the slit. -/
def RelSlitHomotopy (M : Marking) (γ η : Curve) : Prop :=
  ∃ F : C(Parameter × Parameter, ℂ),
    (∀ t, F (initial,t) = γ t) ∧
    (∀ t, F (terminal,t) = η t) ∧
    (∀ s, F (s,initial) = γ initial) ∧
    (∀ s, F (s,terminal) = γ terminal) ∧
    ∀ s t, t ∈ parameterInterior → F (s,t) ∉ M.slit

def LeftClass (M : Marking) (γ : Curve) : Prop :=
  ∃ η : Curve, LeftReference M.left η ∧ RelSlitHomotopy M γ η

/-- An oriented parent leaf.  Orientation always runs from the lower
ending atom to the upper ending atom; this loses no unoriented trace. -/
structure ParentLeaf (M : Marking) (D : Set ℂ) (γ : Curve) : Prop where
  simple : Simple γ
  first_end : M.ends (γ initial)
  last_end : M.ends (γ terminal)
  lower : LowerBank γ
  upper : UpperBank γ
  inside : ∀ t ∈ parameterInterior, γ t ∈ D
  avoids : ∀ t ∈ parameterInterior, γ t ∉ M.slit
  left_class : LeftClass M γ

theorem ParentLeaf.mono {M : Marking} {D E : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) (hDE : D ⊆ E) : ParentLeaf M E γ :=
  { hγ with inside := fun t ht => hDE (hγ.inside t ht) }

def support (Γ : Set Curve) : Set ℂ := ⋃ γ ∈ Γ, interiorTrace γ

/-- A family of all such simple arcs with disjoint interiors and Borel
geometric support.  The set of parametrized leaves need not be Borel.
There is no optimizer, transverse measure, or regular foliation hypothesis. -/
structure ParentWave (M : Marking) (D : Set ℂ) (Γ : Set Curve) : Prop where
  borel : MeasurableSet (support Γ)
  leaf : ∀ γ ∈ Γ, ParentLeaf M D γ
  disjoint : ∀ γ ∈ Γ, ∀ η ∈ Γ, γ ≠ η →
    Disjoint (interiorTrace γ) (interiorTrace η)

def traces (Γ : Set Curve) : Set (Set ℂ) := trace '' Γ

theorem support_eq_evaluation_image (Γ : Set Curve) :
    support Γ = (fun p : Curve × Parameter => p.1 p.2) '' (Γ ×ˢ parameterInterior) := by
  ext z
  simp only [support, mem_iUnion, interiorTrace, mem_image, mem_prod]
  constructor
  · rintro ⟨γ, hγ, t, ht, rfl⟩
    exact ⟨(γ,t), ⟨hγ,ht⟩, rfl⟩
  · rintro ⟨⟨γ,t⟩, ⟨hγ,ht⟩, rfl⟩
    exact ⟨γ,hγ,t,ht,rfl⟩

/-- The Borel support condition is a theorem for this full Borel leaf
model.  It follows from joint evaluation and disjoint simple interiors. -/
theorem measurableSet_support_of_borel_family {M : Marking} {D : Set ℂ} {Γ : Set Curve}
    (hB : MeasurableSet Γ) (hleaf : ∀ γ ∈ Γ, ParentLeaf M D γ)
    (hdisjoint : ∀ γ ∈ Γ, ∀ η ∈ Γ, γ ≠ η →
      Disjoint (interiorTrace γ) (interiorTrace η)) : MeasurableSet (support Γ) := by
  rw [support_eq_evaluation_image]
  apply (hB.prod parameterInterior_isOpen.measurableSet).image_of_measurable_injOn
    continuous_eval.measurable
  rintro ⟨γ,t⟩ ⟨hγ,ht⟩ ⟨η,u⟩ ⟨hη,hu⟩ heq
  have hγη : γ = η := by
    by_contra hne
    have hd := hdisjoint γ hγ η hη hne
    exact (Set.disjoint_left.mp hd) ⟨t,ht,rfl⟩ ⟨u,hu,heq.symm⟩
  subst η
  have htu := (hleaf γ hγ).simple ht hu heq
  exact Prod.ext rfl htu

theorem ParentWave.measurableSet_support {M : Marking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ParentWave M D Γ) : MeasurableSet (support Γ) := hΓ.borel

/-- A horizontal map preserves imaginary parts exactly. -/
def horizontal (h : ℝ ≃o ℝ) : ℂ ≃ₜ ℂ :=
  Complex.equivRealProdCLM.toHomeomorph.trans
    ((h.toHomeomorph.prodCongr (Homeomorph.refl ℝ)).trans
      Complex.equivRealProdCLM.toHomeomorph.symm)

@[simp] theorem horizontal_re (h : ℝ ≃o ℝ) (z : ℂ) :
    (horizontal h z).re = h z.re := by
  simp [horizontal, Complex.equivRealProdCLM_symm_apply]

@[simp] theorem horizontal_im (h : ℝ ≃o ℝ) (z : ℂ) :
    (horizontal h z).im = z.im := by
  simp [horizontal, Complex.equivRealProdCLM_symm_apply]

theorem horizontal_symm (h : ℝ ≃o ℝ) :
    horizontal h.symm = (horizontal h).symm := by
  ext z <;> simp [horizontal, Complex.equivRealProdCLM_symm_apply]

def Marking.map (M : Marking) (h : ℝ ≃o ℝ) : Marking where
  left := h M.left
  first := h M.first
  second := h M.second
  right := h M.right
  left_lt_first := h.strictMono M.left_lt_first
  first_lt_second := h.strictMono M.first_lt_second
  second_lt_right := h.strictMono M.second_lt_right

theorem horizontal_mem_slit_iff (M : Marking) (h : ℝ ≃o ℝ) (z : ℂ) :
    horizontal h z ∈ (M.map h).slit ↔ z ∈ M.slit := by
  simp [Marking.slit, Marking.map]

theorem horizontal_ends_iff (M : Marking) (h : ℝ ≃o ℝ) (z : ℂ) :
    (M.map h).ends (horizontal h z) ↔ M.ends z := by
  simp [Marking.ends, Marking.map]

/-- Postcomposition is a homeomorphism of the complete curve space. -/
def curveHomeomorph (h : ℝ ≃o ℝ) : Curve ≃ₜ Curve :=
  Homeomorph.arrowCongr (Homeomorph.refl Parameter) (horizontal h)

def mapCurve (h : ℝ ≃o ℝ) (γ : Curve) : Curve := curveHomeomorph h γ

@[simp] theorem mapCurve_apply (h : ℝ ≃o ℝ) (γ : Curve) (t : Parameter) :
    mapCurve h γ t = horizontal h (γ t) := rfl

theorem trace_mapCurve (h : ℝ ≃o ℝ) (γ : Curve) :
    trace (mapCurve h γ) = horizontal h '' trace γ := by
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨γ t,⟨t,rfl⟩,rfl⟩
  · rintro ⟨_,⟨t,rfl⟩,rfl⟩
    exact ⟨t,rfl⟩

theorem interiorTrace_mapCurve (h : ℝ ≃o ℝ) (γ : Curve) :
    interiorTrace (mapCurve h γ) = horizontal h '' interiorTrace γ := by
  rw [interiorTrace, interiorTrace, ← image_comp]
  rfl

theorem support_mapCurve (h : ℝ ≃o ℝ) (Γ : Set Curve) :
    support (mapCurve h '' Γ) = horizontal h '' support Γ := by
  ext z
  simp only [support, mem_iUnion, mem_image]
  constructor
  · rintro ⟨_,⟨γ,hγ,rfl⟩,hz⟩
    rw [interiorTrace_mapCurve] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    exact ⟨w,⟨γ,hγ,hw⟩,rfl⟩
  · rintro ⟨w,⟨γ,hγ,hw⟩,rfl⟩
    refine ⟨mapCurve h γ,⟨γ,hγ,rfl⟩,?_⟩
    rw [interiorTrace_mapCurve]
    exact ⟨w,hw,rfl⟩

theorem traces_mapCurve (h : ℝ ≃o ℝ) (Γ : Set Curve) :
    traces (mapCurve h '' Γ) = (fun S : Set ℂ => horizontal h '' S) '' traces Γ := by
  ext S
  simp only [traces, mem_image]
  constructor
  · rintro ⟨_,⟨γ,hγ,rfl⟩,rfl⟩
    exact ⟨trace γ,⟨γ,hγ,rfl⟩,(trace_mapCurve h γ).symm⟩
  · rintro ⟨_,⟨γ,hγ,rfl⟩,rfl⟩
    exact ⟨mapCurve h γ,⟨γ,hγ,rfl⟩,trace_mapCurve h γ⟩

theorem Simple.map {γ : Curve} (hγ : Simple γ) (h : ℝ ≃o ℝ) :
    Simple (mapCurve h γ) := by
  intro s hs t ht heq
  exact hγ hs ht ((horizontal h).injective heq)

theorem LowerBank.map {γ : Curve} (hγ : LowerBank γ) (h : ℝ ≃o ℝ) :
    LowerBank (mapCurve h γ) := by
  obtain ⟨ε,hε,hγ⟩ := hγ
  exact ⟨ε,hε,fun t ht hte => by simpa using hγ t ht hte⟩

theorem UpperBank.map {γ : Curve} (hγ : UpperBank γ) (h : ℝ ≃o ℝ) :
    UpperBank (mapCurve h γ) := by
  obtain ⟨ε,hε,hγ⟩ := hγ
  exact ⟨ε,hε,fun t hte ht => by simpa using hγ t hte ht⟩

theorem LeftReference.map {left : ℝ} {γ : Curve}
    (hγ : LeftReference left γ) (h : ℝ ≃o ℝ) :
    LeftReference (h left) (mapCurve h γ) where
  simple := hγ.simple.map h
  below t ht htm := by simpa using hγ.below t ht htm
  crossing_re := by simpa using h.strictMono hγ.crossing_re
  crossing_im := by simpa using hγ.crossing_im
  above t htm ht := by simpa using hγ.above t htm ht

/-- The whole relative homotopy, including its fixed endpoints, is
transported.  No assertion about class transport is an input. -/
theorem RelSlitHomotopy.map {M : Marking} {γ η : Curve}
    (hγη : RelSlitHomotopy M γ η) (h : ℝ ≃o ℝ) :
    RelSlitHomotopy (M.map h) (mapCurve h γ) (mapCurve h η) := by
  obtain ⟨F,h0,h1,he0,he1,havoid⟩ := hγη
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
  · intro s t ht hmem
    exact havoid s t ht ((horizontal_mem_slit_iff M h (F (s,t))).mp hmem)

theorem LeftClass.map {M : Marking} {γ : Curve}
    (hγ : LeftClass M γ) (h : ℝ ≃o ℝ) : LeftClass (M.map h) (mapCurve h γ) := by
  obtain ⟨η,hη,hγη⟩ := hγ
  exact ⟨mapCurve h η,hη.map h,hγη.map h⟩

theorem ParentLeaf.map {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) (h : ℝ ≃o ℝ) :
    ParentLeaf (M.map h) (horizontal h '' D) (mapCurve h γ) where
  simple := hγ.simple.map h
  first_end := (horizontal_ends_iff M h _).mpr hγ.first_end
  last_end := (horizontal_ends_iff M h _).mpr hγ.last_end
  lower := hγ.lower.map h
  upper := hγ.upper.map h
  inside t ht := ⟨γ t,hγ.inside t ht,rfl⟩
  avoids t ht hmem := hγ.avoids t ht ((horizontal_mem_slit_iff M h _).mp hmem)
  left_class := hγ.left_class.map h

/-- Every member of the original Borel lamination is transported, with
no transverse selection and no restriction on how a leaf wanders. -/
theorem ParentWave.map {M : Marking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ParentWave M D Γ) (h : ℝ ≃o ℝ) :
    ParentWave (M.map h) (horizontal h '' D) (mapCurve h '' Γ) := by
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

def boundedCurves (R : ℝ) : Set Curve := {γ | ∀ t : Parameter, ‖γ t‖ ≤ R}

theorem boundedCurves_isClosed (R : ℝ) : IsClosed (boundedCurves R) := by
  have heq : boundedCurves R = ⋂ t : Parameter, {γ : Curve | ‖γ t‖ ≤ R} := by
    ext γ
    simp [boundedCurves]
  rw [heq]
  exact isClosed_iInter fun t => isClosed_le (continuous_eval_const t).norm continuous_const

theorem mem_boundedCurves_iff_trace {R : ℝ} {γ : Curve} :
    γ ∈ boundedCurves R ↔ trace γ ⊆ closedBall (0 : ℂ) R := by
  simp only [boundedCurves, mem_setOf_eq, trace, range_subset_iff, mem_closedBall,
    dist_zero_right]

theorem ParentWave.restrict_of_borel_support {M : Marking} {D : Set ℂ} {Γ E : Set Curve}
    (hΓ : ParentWave M D Γ) (hE : MeasurableSet (support (Γ ∩ E))) :
    ParentWave M D (Γ ∩ E) where
  borel := hE
  leaf γ hγ := hΓ.leaf γ hγ.1
  disjoint γ hγ η hη hne := hΓ.disjoint γ hγ.1 η hη.1 hne

theorem ParentWave.mono {M : Marking} {D E : Set ℂ} {Γ : Set Curve}
    (hΓ : ParentWave M D Γ) (hDE : D ⊆ E) : ParentWave M E Γ where
  borel := hΓ.borel
  leaf γ hγ := (hΓ.leaf γ hγ).mono hDE
  disjoint := hΓ.disjoint

/-! ## An explicit small horizontal motion of finitely many marks -/

/-- A triangular hat, of fixed radius `r`, centered at `a`. -/
def hat (a r x : ℝ) : ℝ := max 0 (1-|x-a|/r)

theorem hat_nonneg (a r x : ℝ) : 0 ≤ hat a r x := le_max_left _ _

theorem hat_le_one {r : ℝ} (hr : 0 < r) (a x : ℝ) : hat a r x ≤ 1 := by
  apply max_le (by norm_num)
  have h : 0 ≤ |x-a|/r := div_nonneg (abs_nonneg _) hr.le
  linarith

@[simp] theorem hat_center (a r : ℝ) : hat a r a = 1 := by simp [hat]

theorem hat_eq_zero {a r x : ℝ} (hr : 0 < r) (hx : r ≤ |x-a|) :
    hat a r x = 0 := by
  apply max_eq_left
  have h : (1 : ℝ) ≤ |x-a|/r := (le_div_iff₀ hr).2 (by simpa using hx)
  linarith

theorem hat_difference {r : ℝ} (hr : 0 < r) (a x y : ℝ) :
    |hat a r x-hat a r y| ≤ |x-y|/r := by
  have hm := (LipschitzWith.id.const_max (0 : ℝ)).dist_le_mul
    (1-|x-a|/r) (1-|y-a|/r)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hm
  change |hat a r x-hat a r y| ≤ _ at hm
  have heq : (1-|x-a|/r)-(1-|y-a|/r) = (|y-a|-|x-a|)/r := by ring
  rw [heq, abs_div, abs_of_pos hr] at hm
  have habs : abs (abs (y-a)-abs (x-a)) ≤ |x-y| := by
    simpa only [sub_sub_sub_cancel_right, abs_sub_comm] using
      abs_abs_sub_abs_le_abs_sub (y-a) (x-a)
  exact hm.trans (div_le_div_of_nonneg_right habs hr.le)

def cutError {n : ℕ} (a b : Fin n → ℝ) : ℝ := ∑ i, |b i-a i|

def cutDisplacement {n : ℕ} (a b : Fin n → ℝ) (r x : ℝ) : ℝ :=
  ∑ i, (b i-a i)*hat (a i) r x

def cutMap {n : ℕ} (a b : Fin n → ℝ) (r x : ℝ) : ℝ :=
  x+cutDisplacement a b r x

theorem cutError_nonneg {n : ℕ} (a b : Fin n → ℝ) : 0 ≤ cutError a b :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem cutDisplacement_bound {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (x : ℝ) : |cutDisplacement a b r x| ≤ cutError a b := by
  calc
    |∑ i, (b i-a i)*hat (a i) r x| ≤
        ∑ i, |(b i-a i)*hat (a i) r x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |b i-a i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hat_nonneg _ _ _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hat_le_one hr _ _)

theorem cutDisplacement_difference {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (x y : ℝ) :
    |cutDisplacement a b r x-cutDisplacement a b r y| ≤
      (cutError a b/r)*|x-y| := by
  have heq : cutDisplacement a b r x-cutDisplacement a b r y =
      ∑ i, (b i-a i)*(hat (a i) r x-hat (a i) r y) := by
    simp only [cutDisplacement, Finset.sum_sub_distrib, mul_sub]
  rw [heq]
  calc
    |∑ i, (b i-a i)*(hat (a i) r x-hat (a i) r y)| ≤
        ∑ i, |(b i-a i)*(hat (a i) r x-hat (a i) r y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |b i-a i| * (|x-y|/r) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hat_difference hr _ _ _) (abs_nonneg _)
    _ = (cutError a b/r)*|x-y| := by
      rw [← Finset.sum_mul]
      simp only [cutError]
      ring

theorem cutDisplacement_lipschitz {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) :
    LipschitzWith ⟨cutError a b/r, div_nonneg (cutError_nonneg _ _) hr.le⟩
      (cutDisplacement a b r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |cutDisplacement a b r x-cutDisplacement a b r y| ≤
    (cutError a b/r)*|x-y|
  exact cutDisplacement_difference a b hr x y

theorem cutMap_continuous {n : ℕ} (a b : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    Continuous (cutMap a b r) :=
  continuous_id.add (cutDisplacement_lipschitz a b hr).continuous

theorem cutMap_strictMono {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hsmall : cutError a b < r) : StrictMono (cutMap a b r) := by
  intro x y hxy
  have hε : cutError a b/r < 1 := (div_lt_one hr).2 hsmall
  have hdiff := cutDisplacement_difference a b hr y x
  rw [abs_of_pos (sub_pos.mpr hxy)] at hdiff
  have hlo := (abs_le.mp hdiff).1
  have hprod : 0 < (1-cutError a b/r)*(y-x) :=
    mul_pos (sub_pos.mpr hε) (sub_pos.mpr hxy)
  dsimp only [cutMap]
  nlinarith

theorem cutMap_surjective {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) : Surjective (cutMap a b r) := by
  intro y
  let E := cutError a b
  have hE : 0 ≤ E := cutError_nonneg a b
  have hlo := (abs_le.mp (cutDisplacement_bound a b hr (y-E))).2
  have hhi := (abs_le.mp (cutDisplacement_bound a b hr (y+E))).1
  have hy : y ∈ Icc (cutMap a b r (y-E)) (cutMap a b r (y+E)) := by
    constructor <;> dsimp [cutMap, E] at * <;> linarith
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (by linarith : y-E ≤ y+E)
    (cutMap_continuous a b hr).continuousOn hy
  exact ⟨x,hx⟩

/-- The finite-cut map is a global increasing homeomorphism, constructed
from an explicit bounded Lipschitz perturbation of the identity. -/
def cutOrderIso {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hsmall : cutError a b < r) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (cutMap a b r)
    (cutMap_strictMono a b hr hsmall) (cutMap_surjective a b hr)

@[simp] theorem cutOrderIso_apply {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hsmall : cutError a b < r) (x : ℝ) :
    cutOrderIso a b hr hsmall x = cutMap a b r x := rfl

theorem cutMap_marks {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hsep : ∀ i j, i ≠ j → r ≤ |a i-a j|) (j : Fin n) :
    cutMap a b r (a j) = b j := by
  classical
  unfold cutMap cutDisplacement
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [hat_eq_zero hr (hsep j i (Ne.symm hij)), mul_zero]
  · simp

theorem cutOrderIso_marks {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hsmall : cutError a b < r)
    (hsep : ∀ i j, i ≠ j → r ≤ |a i-a j|) (j : Fin n) :
    cutOrderIso a b hr hsmall (a j) = b j := cutMap_marks a b hr hsep j

theorem cutHorizontal_displacement {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hsmall : cutError a b < r) (z : ℂ) :
    ‖horizontal (cutOrderIso a b hr hsmall) z-z‖ ≤ cutError a b := by
  have heq : horizontal (cutOrderIso a b hr hsmall) z-z =
      (cutDisplacement a b r z.re : ℂ) := by
    apply Complex.ext <;> simp [cutMap]
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  exact cutDisplacement_bound a b hr z.re

theorem cutHorizontal_difference {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hsmall : cutError a b < r) (z w : ℂ) :
    ‖(horizontal (cutOrderIso a b hr hsmall) z-z)-
        (horizontal (cutOrderIso a b hr hsmall) w-w)‖ ≤
      (cutError a b/r)*‖z-w‖ := by
  have heq : (horizontal (cutOrderIso a b hr hsmall) z-z)-
        (horizontal (cutOrderIso a b hr hsmall) w-w) =
      ((cutDisplacement a b r z.re-cutDisplacement a b r w.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [cutMap] <;> ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  exact (cutDisplacement_difference a b hr z.re w.re).trans
    (mul_le_mul_of_nonneg_left (by simpa using Complex.abs_re_le_norm (z-w))
      (div_nonneg (cutError_nonneg _ _) hr.le))

theorem cutHorizontal_lipschitz {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hsmall : cutError a b < r) :
    LipschitzWith ⟨1+cutError a b/r, by have := cutError_nonneg a b; positivity⟩
      (horizontal (cutOrderIso a b hr hsmall)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, dist_eq_norm]
  have heq : horizontal (cutOrderIso a b hr hsmall) z-
      horizontal (cutOrderIso a b hr hsmall) w =
      (z-w)+((horizontal (cutOrderIso a b hr hsmall) z-z)-
        (horizontal (cutOrderIso a b hr hsmall) w-w)) := by abel
  rw [heq]
  calc
    ‖(z-w)+((horizontal (cutOrderIso a b hr hsmall) z-z)-
        (horizontal (cutOrderIso a b hr hsmall) w-w))‖ ≤
      ‖z-w‖+‖(horizontal (cutOrderIso a b hr hsmall) z-z)-
        (horizontal (cutOrderIso a b hr hsmall) w-w)‖ := norm_add_le _ _
    _ ≤ ‖z-w‖+(cutError a b/r)*‖z-w‖ :=
      add_le_add le_rfl (cutHorizontal_difference a b hr hsmall z w)
    _ = (1+cutError a b/r)*‖z-w‖ := by ring

theorem cutHorizontal_lower {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hsmall : cutError a b < r) (z w : ℂ) :
    (1-cutError a b/r)*‖z-w‖ ≤
      ‖horizontal (cutOrderIso a b hr hsmall) z-
        horizontal (cutOrderIso a b hr hsmall) w‖ := by
  have heq : z-w =
      (horizontal (cutOrderIso a b hr hsmall) z-
        horizontal (cutOrderIso a b hr hsmall) w)-
      ((horizontal (cutOrderIso a b hr hsmall) z-z)-
        (horizontal (cutOrderIso a b hr hsmall) w-w)) := by abel
  have htri := norm_sub_le
    (horizontal (cutOrderIso a b hr hsmall) z-horizontal (cutOrderIso a b hr hsmall) w)
    ((horizontal (cutOrderIso a b hr hsmall) z-z)-
      (horizontal (cutOrderIso a b hr hsmall) w-w))
  rw [← heq] at htri
  have hdiff := cutHorizontal_difference a b hr hsmall z w
  nlinarith

theorem cutHorizontal_inverse_lipschitz {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hsmall : cutError a b < r) :
    LipschitzWith ⟨(1-cutError a b/r)⁻¹, inv_nonneg.mpr
      (sub_nonneg.mpr ((div_lt_one hr).2 hsmall).le)⟩
      (horizontal (cutOrderIso a b hr hsmall)).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(horizontal (cutOrderIso a b hr hsmall)).symm z-
      (horizontal (cutOrderIso a b hr hsmall)).symm w‖ ≤
    (1-cutError a b/r)⁻¹*‖z-w‖
  have hε : 0 < 1-cutError a b/r := sub_pos.mpr ((div_lt_one hr).2 hsmall)
  have h := cutHorizontal_lower a b hr hsmall
    ((horizontal (cutOrderIso a b hr hsmall)).symm z)
    ((horizontal (cutOrderIso a b hr hsmall)).symm w)
  simp only [Homeomorph.apply_symm_apply] at h
  simpa only [div_eq_inv_mul] using (le_div_iff₀ hε).mpr (by simpa [mul_comm] using h)

/-- An explicit finite-mark transport with quantitative displacement and
two-sided Lipschitz constants.  The only smallness is the sum of actual
mark displacements divided by their fixed separation radius. -/
theorem exists_horizontal_cut_transport {n : ℕ} (a b : Fin n → ℝ) {r : ℝ}
    (hr : 0 < r) (hsep : ∀ i j, i ≠ j → r ≤ |a i-a j|)
    (hsmall : cutError a b < r) :
    ∃ h : ℝ ≃o ℝ,
      (∀ i, h (a i) = b i) ∧
      (∀ z : ℂ, ‖horizontal h z-z‖ ≤ cutError a b) ∧
      LipschitzWith ⟨1+cutError a b/r, by have := cutError_nonneg a b; positivity⟩
        (horizontal h) ∧
      LipschitzWith ⟨(1-cutError a b/r)⁻¹, inv_nonneg.mpr
        (sub_nonneg.mpr ((div_lt_one hr).2 hsmall).le)⟩ (horizontal h).symm := by
  exact ⟨cutOrderIso a b hr hsmall, cutOrderIso_marks a b hr hsmall hsep,
    cutHorizontal_displacement a b hr hsmall, cutHorizontal_lipschitz a b hr hsmall,
    cutHorizontal_inverse_lipschitz a b hr hsmall⟩

end
end MarkedSlitTransport
