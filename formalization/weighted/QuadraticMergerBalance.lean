import QuadraticRamificationCensus

/-!
# Critical-charge balance for actual quadratic component mergers

Under target enlargement, old components can merge either when critical
values are admitted or when previously separated inverse sheets become
connected without a new critical value. The exact balance retains the
archive's independently defined reflection debt. No interpretation of
that debt as a topological hole count is assumed.
-/

namespace LoopsQuadraticMergerBalance

open Set Function Classical
open LoopsQuadraticCylinderCensus LoopsQuadraticCylinderRamification
open LoopsQuadraticComponentFiberDegree LoopsQuadraticEnlargementDegree
open LoopsQuadraticRamificationCensus
open LoopsQuadraticLocalRamification
open scoped BigOperators

noncomputable section

/-- A representative of a nonempty geometric component. The value on
the empty set is unused in the component theorems. -/
def componentAnchor (D : Set ℂ) : ℂ :=
  if h : D.Nonempty then h.choose else 0

theorem componentAnchor_mem (D : Set ℂ) (hD : D.Nonempty) :
    componentAnchor D ∈ D := by
  simp only [componentAnchor, dif_pos hD]
  exact hD.choose_spec

/-- Reflection debt attached to an actual planar component rather
than to a separately supplied component label or representative. -/
def componentDebt (c : ℂ) (n : ℕ) (U D : Set ℂ) : ℕ :=
  componentReflectionDebt c U n (componentAnchor D)

/-- The new target charge counts distinct postcritical values in the
newly admitted region, retaining each full local fiber deficit. -/
def newCriticalCharge (c : ℂ) (n : ℕ) (U V : Set ℂ) (x : ℂ) : ℕ :=
  ∑ z ∈ postcriticalTargets c (V \ U) n, componentFiberDefect c V z n x

/-- Reflection debt is constant on an actual open pullback component. -/
theorem componentReflectionDebt_eq_of_mem (c : ℂ) (V : Set ℂ)
    (hVo : IsOpen V) (n : ℕ) (x a : ℂ)
    (hx : (quad c)^[n] x ∈ V)
    (ha : a ∈ connectedComponentIn ((quad c)^[n] ⁻¹' V) x) :
    componentReflectionDebt c V n a = componentReflectionDebt c V n x := by
  induction n generalizing x a with
  | zero => rfl
  | succ n ih =>
    have hx' : (quad c)^[n] (quad c x) ∈ V := by
      simpa only [Function.iterate_succ_apply] using hx
    have htail : quad c a ∈
        connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x) := by
      have he := quadratic_prefix_component_image c n 1 V hVo x hx
      simp only [Function.iterate_one] at he
      rw [← he]
      exact ⟨a, ha, rfl⟩
    have he := connectedComponentIn_eq ha
    have ht := connectedComponentIn_eq htail
    have hd := ih (quad c x) (quad c a) hx' htail
    simp only [componentReflectionDebt, ← he, ← ht, hd]

/-- The set-valued debt agrees with every valid component anchor. -/
theorem componentDebt_eq (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (x : ℂ) (hx : (quad c)^[n] x ∈ V) :
    componentDebt c n V (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) =
      componentReflectionDebt c V n x := by
  unfold componentDebt
  exact componentReflectionDebt_eq_of_mem c V hVo n x _ hx
    (componentAnchor_mem _ ⟨x, mem_connectedComponentIn hx⟩)

/-- Every census entry has a valid representative, and is exactly the
old pullback component through that representative. -/
theorem mergerCensus_componentAnchor (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (x y : ℂ) (hy : y ∈ U) (D : Set ℂ)
    (hD : D ∈ mergerCensus c n U V x y) :
    (quad c)^[n] (componentAnchor D) ∈ U ∧
      D = connectedComponentIn ((quad c)^[n] ⁻¹' U) (componentAnchor D) := by
  obtain ⟨a, _, haU, he⟩ :=
    (mem_mergerCensus c n U V hUV hUo hUc x y hy D).mp hD
  have hn : D.Nonempty := by
    rw [he]
    exact ⟨a, mem_connectedComponentIn haU⟩
  have ha : componentAnchor D ∈ connectedComponentIn ((quad c)^[n] ⁻¹' U) a := by
    rw [← he]
    exact componentAnchor_mem D hn
  exact ⟨connectedComponentIn_subset ((quad c)^[n] ⁻¹' U) a ha,
    he.trans (connectedComponentIn_eq ha)⟩

/-- The postcritical inventory partitions exactly into retained and
newly admitted target values, even if several orbit times coincide. -/
theorem postcriticalTargets_enlargement_partition (c : ℂ) (n : ℕ)
    (U V : Set ℂ) (hUV : U ⊆ V) :
    postcriticalTargets c V n =
      postcriticalTargets c U n ∪ postcriticalTargets c (V \ U) n := by
  ext z
  simp only [Finset.mem_union, mem_postcriticalTargets, mem_diff]
  constructor
  · rintro ⟨hzV, hz⟩
    by_cases hzU : z ∈ U
    · exact Or.inl ⟨hzU, hz⟩
    · exact Or.inr ⟨⟨hzV, hzU⟩, hz⟩
  · rintro (h | h)
    · exact ⟨hUV h.1, h.2⟩
    · exact ⟨h.1.1, h.2⟩

/-- Aggregate target deficit separates into retained and new charge. -/
theorem postcritical_defect_split (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (x : ℂ) :
    (∑ z ∈ postcriticalTargets c V n, componentFiberDefect c V z n x) =
      (∑ z ∈ postcriticalTargets c U n, componentFiberDefect c V z n x) +
        newCriticalCharge c n U V x := by
  rw [postcriticalTargets_enlargement_partition c n U V hUV]
  apply Finset.sum_union
  apply Finset.disjoint_left.mpr
  intro z hzU hzN
  exact ((mem_postcriticalTargets c (V \ U) n z).mp hzN).1.2
    ((mem_postcriticalTargets c U n z).mp hzU).1

/-- The exact merger count balances new actual critical-fiber charge
against the change in reflection debt. All components are the genuine
connected components of the quadratic iterate's inverse images. -/
theorem merger_balance (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (x y : ℂ) (hx : (quad c)^[n] x ∈ V) (hy : y ∈ U)
    (hreg : ∀ k < n, (quad c)^[k] c ≠ y) :
    (mergerCensus c n U V x y).card +
        (∑ D ∈ mergerCensus c n U V x y, componentDebt c n U D) =
      1 + componentReflectionDebt c V n x + newCriticalCharge c n U V x := by
  let C := mergerCensus c n U V x y
  let A := postcriticalTargets c U n
  have hpoint (D : Set ℂ) (hD : D ∈ C) :
      (∑ z ∈ A, ((localFiber c n D y).card - (localFiber c n D z).card)) +
        componentDebt c n U D + 1 = (localFiber c n D y).card := by
    obtain ⟨haU, heD⟩ := mergerCensus_componentAnchor c n U V hUV hUo hUc x y hy D hD
    have hdeg := quadratic_component_regular_degree c U hUo hUc n
      (componentAnchor D) haU y hy hreg
    rw [← heD] at hdeg
    have he := component_actual_deficit_accounting c U hUo hUc A n
      (componentAnchor D) haU
      (fun z hz => ((mem_postcriticalTargets c U n z).mp hz).1)
      (fun k hk hv => (mem_postcriticalTargets c U n _).mpr ⟨hv, k, hk, rfl⟩)
    rw [← heD, ← hdeg] at he
    exact he
  have hsum := Finset.sum_congr rfl hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hsum
  have htranspose :
      (∑ D ∈ C, ∑ z ∈ A,
        ((localFiber c n D y).card - (localFiber c n D z).card)) =
      ∑ z ∈ A, componentFiberDefect c V z n x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z hz
    exact mergerCensus_defect_conservation c n U V hUV hUo hUc hVo hVc
      x y z hx hy ((mem_postcriticalTargets c U n z).mp hz).1 hreg
  rw [htranspose] at hsum
  have hdegree := mergerCensus_degree_conservation c n U V hUV hVo hVc x y hx hy hreg
  have hbudget := aggregate_defect_debt_eq_degree c V (postcriticalTargets c V n) n x
    (fun k hk hv => (mem_postcriticalTargets c V n _).mpr ⟨hv, k, hk, rfl⟩)
  rw [postcritical_defect_split c n U V hUV x] at hbudget
  change (∑ D ∈ C, (localFiber c n D y).card) =
    2 ^ componentReflectionRank c V n x at hdegree
  change (∑ z ∈ A, componentFiberDefect c V z n x) +
    newCriticalCharge c n U V x + componentReflectionDebt c V n x + 1 =
      2 ^ componentReflectionRank c V n x at hbudget
  change C.card + (∑ D ∈ C, componentDebt c n U D) = _
  omega

/-- Every nonempty open target contains a value outside the complete
finite postcritical inventory of a prescribed iterate. -/
theorem regular_target_exists (c : ℂ) (n : ℕ) (U : Set ℂ)
    (hUo : IsOpen U) (hUn : U.Nonempty) :
    ∃ y ∈ U, ∀ k < n, (quad c)^[k] c ≠ y := by
  obtain ⟨a, ha⟩ := hUn
  have hUi : U.Infinite := infinite_of_mem_nhds a (hUo.mem_nhds ha)
  obtain ⟨y, hy, hyN⟩ := hUi.exists_notMem_finset (postcriticalTargets c univ n)
  refine ⟨y, hy, ?_⟩
  intro k hk he
  exact hyN ((mem_postcriticalTargets c univ n y).mpr ⟨mem_univ y, k, hk, he⟩)

/-- The geometric merger balance is independent of the target used
to enumerate the census. That anchor may itself be postcritical. -/
theorem merger_balance_any_anchor (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hUV : U ⊆ V) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (x y : ℂ) (hx : (quad c)^[n] x ∈ V) (hy : y ∈ U) :
    (mergerCensus c n U V x y).card +
        (∑ D ∈ mergerCensus c n U V x y, componentDebt c n U D) =
      1 + componentReflectionDebt c V n x + newCriticalCharge c n U V x := by
  obtain ⟨z, hz, hreg⟩ := regular_target_exists c n U hUo ⟨y, hy⟩
  have he := merger_balance c n U V hUV hUo hUc hVo hVc x z hx hz hreg
  rw [← mergerCensus_independent c n U V hUV hUo hUc x y z hy hz] at he
  exact he

/-- New target charge is exactly the local-order excess of the actual
derivative-critical points in the newly admitted part of the enlarged
component. No regular comparison target is needed for this identity. -/
theorem newCriticalCharge_eq_new_ramification (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (x : ℂ) (hx : (quad c)^[n] x ∈ V) :
    newCriticalCharge c n U V x =
      ∑ z ∈ criticalPoints c n
        (connectedComponentIn ((quad c)^[n] ⁻¹' V) x \ ((quad c)^[n] ⁻¹' U)),
        (localMultiplicity c z n - 1) := by
  let B := connectedComponentIn ((quad c)^[n] ⁻¹' V) x
  let E := B \ ((quad c)^[n] ⁻¹' U)
  have hm : MapsTo ((quad c)^[n]) E (V \ U) := by
    intro z hz
    exact ⟨connectedComponentIn_subset ((quad c)^[n] ⁻¹' V) x hz.1, hz.2⟩
  change newCriticalCharge c n U V x =
    ∑ z ∈ criticalPoints c n E, (localMultiplicity c z n - 1)
  rw [criticalPoints_ramification_sum c (V \ U) E n hm]
  unfold newCriticalCharge
  apply Finset.sum_congr rfl
  intro y hy
  have hyVU := ((mem_postcriticalTargets c (V \ U) n y).mp hy).1
  have hF : localFiber c n E y = localFiber c n B y := by
    ext z
    simp only [mem_localFiber]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨hzB, hzy⟩
      refine ⟨⟨hzB, ?_⟩, hzy⟩
      change (quad c)^[n] z ∉ U
      rw [hzy]
      exact hyVU.2
  rw [hF]
  exact quadratic_component_defect_eq_ramification_sum c V hVo hVc y hyVU.1 n x hx

/-- Vanishing new charge is exactly absence of a new actual critical
source point in the selected enlarged component. Postcritical values
whose critical inverse points lie elsewhere contribute nothing. -/
theorem newCriticalCharge_eq_zero_iff_no_new_critical
    (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (x : ℂ) (hx : (quad c)^[n] x ∈ V) :
    newCriticalCharge c n U V x = 0 ↔
      criticalPoints c n
        (connectedComponentIn ((quad c)^[n] ⁻¹' V) x \ ((quad c)^[n] ⁻¹' U)) = ∅ := by
  rw [newCriticalCharge_eq_new_ramification c n U V hVo hVc x hx]
  let E := connectedComponentIn ((quad c)^[n] ⁻¹' V) x \ ((quad c)^[n] ⁻¹' U)
  change (∑ z ∈ criticalPoints c n E, (localMultiplicity c z n - 1)) = 0 ↔
    criticalPoints c n E = ∅
  constructor
  · intro he
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hle : localMultiplicity c z n - 1 ≤
        ∑ w ∈ criticalPoints c n E, (localMultiplicity c w n - 1) :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hz
    have hne := ((mem_criticalPoints_iff_multiplicity c n E z).mp hz).2
    have hp : 0 < localMultiplicity c z n := pow_pos (by norm_num) _
    omega
  · intro he
    simp only [he, Finset.sum_empty]

/-- An equivalent analytic form tests the actual complex derivative
on the newly admitted part of the selected component. -/
theorem newCriticalCharge_eq_zero_iff_deriv
    (c : ℂ) (n : ℕ) (U V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (x : ℂ) (hx : (quad c)^[n] x ∈ V) :
    newCriticalCharge c n U V x = 0 ↔
      ∀ z ∈ connectedComponentIn ((quad c)^[n] ⁻¹' V) x,
        (quad c)^[n] z ∉ U → deriv ((quad c)^[n]) z ≠ 0 := by
  rw [newCriticalCharge_eq_zero_iff_no_new_critical c n U V hVo hVc x hx]
  constructor
  · intro he z hzB hzU hd
    have hz := (mem_criticalPoints_iff_deriv c n
      (connectedComponentIn ((quad c)^[n] ⁻¹' V) x \ ((quad c)^[n] ⁻¹' U)) z).mpr
      ⟨⟨hzB, hzU⟩, hd⟩
    simpa only [he, Finset.notMem_empty] using hz
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hzE, hd⟩ := (mem_criticalPoints_iff_deriv c n
      (connectedComponentIn ((quad c)^[n] ⁻¹' V) x \ ((quad c)^[n] ⁻¹' U)) z).mp hz
    exact h z hzE.1 hzE.2 hd

end
end LoopsQuadraticMergerBalance
