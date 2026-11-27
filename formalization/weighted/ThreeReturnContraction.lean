import ThreeReturnCovering
import Mathlib.Topology.Homotopy.Contractible

/-!
# Contraction across the unique branch fiber

The punctured covering lifts radial contractions toward the critical
value.  Closedness and the singleton critical fiber extend this lift
continuously across both the critical point and the final contraction
time.  No planar uniformization theorem is used.
-/

namespace ThreeReturnContraction

open Set Function Filter Metric
open scoped Topology

noncomputable section

private theorem continuousAt_of_closed_singleton_fiber
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (hf : IsClosedMap f) (x₀ : X)
    (hsingle : ∀ x, f x = f x₀ → x = x₀)
    (g : Z → X) (z : Z) (hz : g z = x₀)
    (hcomp : ContinuousAt (f ∘ g) z) : ContinuousAt g z := by
  have hpre : f ⁻¹' {f x₀} = {x₀} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨hsingle x, fun he => congrArg f he⟩
  have hle : Filter.comap f (𝓝 (f x₀)) ≤ 𝓝 x₀ := by
    simpa only [hpre, nhdsSet_singleton] using hf.comap_nhds_le (y := f x₀)
  have hcomp' : Tendsto (f ∘ g) (𝓝 z) (𝓝 (f x₀)) := by
    simpa only [ContinuousAt, Function.comp_apply, hz] using hcomp
  have hg : Tendsto g (𝓝 z) (Filter.comap f (𝓝 (f x₀))) :=
    tendsto_comap_iff.mpr hcomp'
  simpa only [ContinuousAt, hz] using hg.mono_right hle

private def blend (t : ℝ) (a y : ℂ) : ℂ := (1-t) • y + t • a

private theorem blend_zero (a y : ℂ) : blend 0 a y = y := by simp [blend]
private theorem blend_one (a y : ℂ) : blend 1 a y = a := by simp [blend]
private theorem blend_self (t : ℝ) (a : ℂ) : blend t a a = a := by
  rw [blend, ← add_smul]
  simp

private theorem blend_mem {V : Set ℂ} (hV : Convex ℝ V)
    {a y : ℂ} (ha : a ∈ V) (hy : y ∈ V) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    blend t a y ∈ V :=
  hV hy ha (sub_nonneg.mpr ht1) ht0 (by ring)

private theorem blend_ne {a y : ℂ} {t : ℝ} (ht : t < 1) (hy : y ≠ a) :
    blend t a y ≠ a := by
  intro he
  have hzero : (1-t) • (y-a) = 0 := by
    calc
      (1-t) • (y-a) = blend t a y-a := by
        simp only [blend, sub_smul, one_smul, smul_sub]
        abel
      _ = 0 := sub_eq_zero.mpr he
  have ht0 : (1-t : ℝ) ≠ 0 := by linarith
  exact hy (sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left ht0))

/-- A closed map to a convex plane domain with a singleton branch
fiber and a covering elsewhere has a contractible source. -/
theorem contractible_of_punctured_cover
    {X : Type*} [TopologicalSpace X] (V : Set ℂ) (hV : Convex ℝ V)
    (f : C(X, V)) (x₀ : X) (hf : IsClosedMap f)
    (hsingle : ∀ x, f x = f x₀ → x = x₀)
    (hcover : IsCoveringMap
      ({v : V | (v : ℂ) ≠ (f x₀ : ℂ)}.restrictPreimage f)) :
    ContractibleSpace X := by
  classical
  let S : Set V := {v | (v : ℂ) ≠ (f x₀ : ℂ)}
  let E : Set X := f ⁻¹' S
  let π : E → S := S.restrictPreimage f
  have hc : IsCoveringMap π := hcover
  let A : Set (unitInterval × X) :=
    {q | (q.1 : ℝ) < 1 ∧ (f q.2 : ℂ) ≠ (f x₀ : ℂ)}
  have hA : IsOpen A :=
    (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).inter
      (isOpen_ne.preimage
        (continuous_subtype_val.comp (f.continuous.comp continuous_snd)))
  have hmul (s : unitInterval) (q : A) :
      0 ≤ (s : ℝ) * (q.val.1 : ℝ) ∧ (s : ℝ) * (q.val.1 : ℝ) < 1 := by
    refine ⟨mul_nonneg s.property.1 q.val.1.property.1, ?_⟩
    exact (mul_le_of_le_one_left q.val.1.property.1 s.property.2).trans_lt q.property.1
  let B : C(unitInterval × X, V) :=
    ⟨fun q => ⟨blend (q.1 : ℝ) (f x₀ : ℂ) (f q.2 : ℂ),
      blend_mem hV (f x₀).property (f q.2).property q.1.property.1 q.1.property.2⟩,
      by dsimp [blend]; fun_prop⟩
  let H : C(unitInterval × A, S) :=
    ⟨fun sq => ⟨⟨blend ((sq.1 : ℝ) * (sq.2.val.1 : ℝ))
        (f x₀ : ℂ) (f sq.2.val.2 : ℂ),
      blend_mem hV (f x₀).property (f sq.2.val.2).property
        (hmul sq.1 sq.2).1 (hmul sq.1 sq.2).2.le⟩,
      blend_ne (hmul sq.1 sq.2).2 sq.2.property.2⟩,
      by dsimp [blend]; fun_prop⟩
  let initial : C(A, E) :=
    ⟨fun q => ⟨q.val.2, q.property.2⟩, by fun_prop⟩
  have hstart (q : A) : H (0, q) = π (initial q) := by
    apply Subtype.ext
    apply Subtype.ext
    change blend ((0 : ℝ) * (q.val.1 : ℝ)) (f x₀ : ℂ) (f q.val.2 : ℂ) = _
    simp only [zero_mul, blend_zero]
    rfl
  let L : C(unitInterval × A, E) := hc.liftHomotopy H initial hstart
  let g : C(A, X) :=
    ⟨fun q => (L (1, q) : X),
      continuous_subtype_val.comp (L.continuous.comp (continuous_const.prodMk continuous_id))⟩
  have hglift (q : A) : f (g q) = B q.val := by
    have h := congrFun (hc.liftHomotopy_lifts H initial hstart) (1, q)
    apply Subtype.ext
    have h' := congrArg (fun v : S => ((v : V) : ℂ)) h
    change (f (g q) : ℂ) =
      blend ((1 : ℝ) * (q.val.1 : ℝ)) (f x₀ : ℂ) (f q.val.2 : ℂ) at h'
    change (f (g q) : ℂ) = blend (q.val.1 : ℝ) (f x₀ : ℂ) (f q.val.2 : ℂ)
    simpa only [one_mul] using h'
  let K : unitInterval × X → X := fun q => if h : q ∈ A then g ⟨q, h⟩ else x₀
  have hKOn : ContinuousOn K A := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : A.restrict K = g := by
      funext q
      simp only [Set.restrict, K, dif_pos q.property]
    rw [heq]
    exact g.continuous
  have hKlift (q : unitInterval × X) : f (K q) = B q := by
    by_cases hq : q ∈ A
    · exact (by simpa only [K, dif_pos hq] using hglift ⟨q, hq⟩)
    · rw [show K q = x₀ by simp only [K, dif_neg hq]]
      apply Subtype.ext
      change (f x₀ : ℂ) = blend (q.1 : ℝ) (f x₀ : ℂ) (f q.2 : ℂ)
      by_cases ht : (q.1 : ℝ) < 1
      · have hy : (f q.2 : ℂ) = (f x₀ : ℂ) := by
          by_contra hy
          exact hq ⟨ht, hy⟩
        rw [hy, blend_self]
      · have ht1 : (q.1 : ℝ) = 1 := le_antisymm q.1.property.2 (le_of_not_gt ht)
        rw [ht1, blend_one]
  have hKcomp : Continuous (f ∘ K) := by
    have heq : f ∘ K = B := funext hKlift
    rw [heq]
    exact B.continuous
  have hK : Continuous K := by
    rw [continuous_iff_continuousAt]
    intro q
    by_cases hq : q ∈ A
    · exact hKOn.continuousAt (hA.mem_nhds hq)
    · exact continuousAt_of_closed_singleton_fiber f hf x₀ hsingle K q
        (by simp only [K, dif_neg hq]) hKcomp.continuousAt
  have hKzero (x : X) : K (0, x) = x := by
    by_cases hx : (f x : ℂ) = (f x₀ : ℂ)
    · have hxeq : x = x₀ := hsingle x (Subtype.ext hx)
      have hn : (0, x) ∉ A := fun h => h.2 hx
      change (if h : (0, x) ∈ A then g ⟨(0, x), h⟩ else x₀) = x
      rw [dif_neg hn]
      exact hxeq.symm
    · have hmem : (0, x) ∈ A := ⟨by norm_num, hx⟩
      let q : A := ⟨(0, x), hmem⟩
      have hconst : ∀ s t : unitInterval, π (L (s, q)) = π (L (t, q)) := by
        intro s t
        have hs := congrFun (hc.liftHomotopy_lifts H initial hstart) (s, q)
        have ht := congrFun (hc.liftHomotopy_lifts H initial hstart) (t, q)
        change π (L (s, q)) = H (s, q) at hs
        change π (L (t, q)) = H (t, q) at ht
        rw [hs, ht]
        apply Subtype.ext
        apply Subtype.ext
        change blend ((s : ℝ) * 0) (f x₀ : ℂ) (f x : ℂ) =
          blend ((t : ℝ) * 0) (f x₀ : ℂ) (f x : ℂ)
        simp only [mul_zero]
      have hsame : L (1, q) = L (0, q) := hc.const_of_comp
        (L.continuous.comp (continuous_id.prodMk continuous_const)) hconst 1 0
      have hinit : L (0, q) = initial q := hc.liftHomotopy_zero H initial hstart q
      change (if h : (0, x) ∈ A then g ⟨(0, x), h⟩ else x₀) = x
      rw [dif_pos hmem]
      exact congrArg Subtype.val (hsame.trans hinit)
  have hKone (x : X) : K (1, x) = x₀ := by
    have hn : (1, x) ∉ A := by
      intro h
      have ht := h.1
      norm_num at ht
    simp only [K, dif_neg hn]
  apply (contractible_iff_id_nullhomotopic X).mpr
  refine ⟨x₀, ⟨?_⟩⟩
  exact {
    toFun := K
    continuous_toFun := hK
    map_zero_left := hKzero
    map_one_left := hKone }

open LimitingCrestQuadraticReturn ThreeReturnDomain ThreeReturnDegree
open ThreeReturnCovering ThreeReturnEstimates NearTwoTip

/-- The boundary and collision certificates give a proper canonical
restriction with exactly two local sheets at every regular target. -/
theorem source_two_sheet_cover_of_bounds (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : criticalValue c p ≠ 0)
    (hzero : ‖threeReturn c p 0‖ < 1/6)
    (hbarrier : ∀ z : ℂ, ‖z‖ = 3/20 → 1/6 < ‖threeReturn c p z‖)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 1/6 → ‖w‖ ≤ 1/6 →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w)) :
    ∃ hm : MapsTo (threeReturn c p) (source c p) (ball 0 (1/6)),
      IsProperMap (MapsTo.restrict (threeReturn c p) (source c p) (ball 0 (1/6)) hm) ∧
      IsCoveringMapOn
        (MapsTo.restrict (threeReturn c p) (source c p) (ball 0 (1/6)) hm)
        {v : ball (0 : ℂ) (1/6) | (v : ℂ) ≠ threeReturn c p 0} ∧
      (∀ v : ball (0 : ℂ) (1/6), (v : ℂ) ≠ threeReturn c p 0 →
        IsEvenlyCovered
          (MapsTo.restrict (threeReturn c p) (source c p) (ball 0 (1/6)) hm) v (Fin 2)) ∧
      IsCoveringMap
        ({v : ball (0 : ℂ) (1/6) | (v : ℂ) ≠ threeReturn c p 0}.restrictPreimage
          (MapsTo.restrict (threeReturn c p) (source c p) (ball 0 (1/6)) hm)) := by
  have hproper := threeReturn_proper c p hd
  have hcl := component_closure_inside_barrier (threeReturn c p) hproper.continuous
    (3/20) (1/6) (by norm_num) hzero hbarrier
  have hnorm : ∀ z ∈ source c p, ‖z‖ ≤ 1/6 := by
    intro z hz
    have h : ‖z‖ < 3/20 := by simpa using hcl.1 (subset_closure hz)
    linarith
  have hW : IsOpen (source c p) :=
    (isOpen_ball.preimage hproper.continuous).connectedComponentIn
  have hm : MapsTo (threeReturn c p) (source c p) (ball 0 (1/6)) :=
    connectedComponentIn_subset _ _
  have hrest : IsProperMap
      (MapsTo.restrict (threeReturn c p) (source c p) (ball 0 (1/6)) hm) :=
    component_proper (threeReturn c p) hproper (ball 0 (1/6)) 0 isOpen_ball
  have hcoll : ∀ {z w : ℂ}, z ∈ source c p → w ∈ source c p →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w) := by
    intro z w hz hw
    exact hcollision (hnorm z hz) (hnorm w hw)
  have honto : SurjOn (threeReturn c p) (source c p) (ball 0 (1/6)) := by
    intro y hy
    exact (source_image c p hd hzero).symm ▸ hy
  exact ⟨hm, hrest, signed_two_sheet_cover (threeReturn c p) (source c p)
    (ball 0 (1/6)) hW isOpen_ball hm hproper.continuous (threeReturn_open c p hd)
    hrest hcoll (source_symmetric c p hp hzero) honto⟩

/-- The same boundary and collision certificates that define the
canonical collar also prove that its complete source is contractible. -/
theorem source_contractible_of_bounds (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : criticalValue c p ≠ 0)
    (hzero : ‖threeReturn c p 0‖ < 1/6)
    (hbarrier : ∀ z : ℂ, ‖z‖ = 3/20 → 1/6 < ‖threeReturn c p z‖)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 1/6 → ‖w‖ ≤ 1/6 →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w)) :
    ContractibleSpace (source c p) := by
  have hproper := threeReturn_proper c p hd
  have hopen := threeReturn_open c p hd
  have hcl := component_closure_inside_barrier (threeReturn c p) hproper.continuous
    (3/20) (1/6) (by norm_num) hzero hbarrier
  have hnorm : ∀ z ∈ source c p, ‖z‖ ≤ 1/6 := by
    intro z hz
    have h : ‖z‖ < 3/20 := by simpa using hcl.1 (subset_closure hz)
    linarith
  have h0 : (0 : ℂ) ∈ source c p := mem_connectedComponentIn (by simpa using hzero)
  have hW : IsOpen (source c p) :=
    (isOpen_ball.preimage hproper.continuous).connectedComponentIn
  have hm : MapsTo (threeReturn c p) (source c p) (ball 0 (1/6)) :=
    connectedComponentIn_subset _ _
  have hrest : IsProperMap
      (MapsTo.restrict (threeReturn c p) (source c p) (ball 0 (1/6)) hm) :=
    component_proper (threeReturn c p) hproper (ball 0 (1/6)) 0 isOpen_ball
  have hcoll : ∀ {z w : ℂ}, z ∈ source c p → w ∈ source c p →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w) := by
    intro z w hz hw
    exact hcollision (hnorm z hz) (hnorm w hw)
  have hsym := source_symmetric c p hp hzero
  have honto : SurjOn (threeReturn c p) (source c p) (ball 0 (1/6)) := by
    intro y hy
    exact (source_image c p hd hzero).symm ▸ hy
  have hcover := (signed_two_sheet_cover (threeReturn c p) (source c p)
    (ball 0 (1/6)) hW isOpen_ball hm hproper.continuous hopen hrest hcoll hsym honto).2.2
  let f : C(source c p, ball (0 : ℂ) (1/6)) :=
    ⟨MapsTo.restrict (threeReturn c p) (source c p) (ball 0 (1/6)) hm, hrest.continuous⟩
  let x₀ : source c p := ⟨0, h0⟩
  apply contractible_of_punctured_cover (ball 0 (1/6)) (convex_ball _ _) f x₀
    hrest.isClosedMap ?_ hcover
  intro x hx
  apply Subtype.ext
  have he : threeReturn c p x = threeReturn c p 0 := congrArg Subtype.val hx
  simpa using (hcoll x.property h0).mp he

/-- Actual analytic-tail parameters have a contractible canonical source. -/
theorem actual_source_contractible {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ContractibleSpace (source c p) := by
  apply source_contractible_of_bounds c p (by omega) hc.2.1.ne'
    (actual_critical_value_bound hp hc)
  · intro z hz
    have h := actual_annular_barrier hp hc (by simpa [innerRadius] using hz.ge)
      (show ‖z‖ ≤ outerRadius by rw [hz]; norm_num [outerRadius])
    change 1/6 + 1/500 < ‖threeReturn c p z‖ at h
    linarith
  · exact fun hz hw => actual_three_return_collision_iff hp hc hz hw

/-- Simple connectivity is a theorem about the actual selected domain. -/
theorem actual_source_simplyConnected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsSimplyConnected (source c p) := by
  letI := actual_source_contractible hp hc
  change SimplyConnectedSpace (source c p)
  infer_instance

end

end ThreeReturnContraction
