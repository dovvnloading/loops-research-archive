import QuadraticLocalRamification

/-!
# The actual critical-point budget of a quadratic pullback component

The finite census consists of the actual points that encounter zero before
the terminal iterate. Each point is counted once, even when its orbit
encounters zero several times. Its contribution is its exact local order
minus one.
-/

namespace LoopsQuadraticRamificationCensus

open Set Function Classical
open LoopsQuadraticCylinderCensus LoopsQuadraticCriticalFiberCensus
open LoopsQuadraticCylinderRamification LoopsQuadraticComponentFiberDegree
open LoopsQuadraticEnlargementDegree LoopsQuadraticLocalRamification
open LoopsQuadraticTransversality
open scoped BigOperators

noncomputable section

/-- The actual critical points of the iterate retained in a planar set. -/
def criticalPoints (c : ℂ) (n : ℕ) (C : Set ℂ) : Finset ℂ :=
  (Finset.range n).biUnion (fun k => localFiber c k C 0)

theorem mem_criticalPoints (c : ℂ) (n : ℕ) (C : Set ℂ) (z : ℂ) :
    z ∈ criticalPoints c n C ↔ z ∈ C ∧ ∃ k < n, (quad c)^[k] z = 0 := by
  simp only [criticalPoints, Finset.mem_biUnion, Finset.mem_range, mem_localFiber]
  constructor
  · rintro ⟨k, hk, hz, he⟩
    exact ⟨hz, k, hk, he⟩
  · rintro ⟨hz, k, hk, he⟩
    exact ⟨k, hk, hz, he⟩

/-- Criticality is exactly nontriviality of the proved local order. -/
theorem mem_criticalPoints_iff_multiplicity (c : ℂ) (n : ℕ)
    (C : Set ℂ) (z : ℂ) :
    z ∈ criticalPoints c n C ↔ z ∈ C ∧ localMultiplicity c z n ≠ 1 := by
  rw [mem_criticalPoints]
  constructor
  · rintro ⟨hz, k, hk, he⟩
    exact ⟨hz, fun h => ((localMultiplicity_eq_one_iff c z n).mp h k hk) he⟩
  · rintro ⟨hz, hmult⟩
    refine ⟨hz, ?_⟩
    by_contra hn
    apply hmult
    apply (localMultiplicity_eq_one_iff c z n).mpr
    intro k hk he
    exact hn ⟨k, hk, he⟩

/-- Nonvanishing of the actual complex derivative is equivalent to
avoiding the quadratic critical point at every earlier orbit position. -/
theorem quadratic_iterate_deriv_ne_zero_iff (c z : ℂ) (n : ℕ) :
    deriv ((quad c)^[n]) z ≠ 0 ↔ ∀ k < n, (quad c)^[k] z ≠ 0 := by
  have hm : returnMultiplier c z n ≠ 0 ↔
      ∀ k < n, returnOrbit c z k ≠ 0 := by
    induction n with
    | zero => simp [returnMultiplier]
    | succ n ih =>
      rw [returnMultiplier, mul_ne_zero_iff, mul_ne_zero_iff, ih]
      constructor
      · rintro ⟨⟨_, hlast⟩, hprev⟩ k hk
        by_cases he : k = n
        · simpa only [he] using hlast
        · exact hprev k (by omega)
      · intro h
        exact ⟨⟨by norm_num, h n (by omega)⟩, fun k hk => h k (by omega)⟩
  have hd : deriv ((quad c)^[n]) z = returnMultiplier c z n := by
    simpa only [returnOrbit_eq_iterate] using (returnMultiplier_hasDerivAt c z n).deriv
  rw [hd, hm]
  simp only [returnOrbit_eq_iterate]

/-- The finite orbital census is literally the zero set of the actual
complex derivative on the specified planar set. -/
theorem mem_criticalPoints_iff_deriv (c : ℂ) (n : ℕ) (C : Set ℂ) (z : ℂ) :
    z ∈ criticalPoints c n C ↔ z ∈ C ∧ deriv ((quad c)^[n]) z = 0 := by
  rw [mem_criticalPoints]
  constructor
  · rintro ⟨hz, k, hk, he⟩
    refine ⟨hz, ?_⟩
    by_contra hne
    exact ((quadratic_iterate_deriv_ne_zero_iff c z n).mp hne k hk) he
  · rintro ⟨hz, hd⟩
    refine ⟨hz, ?_⟩
    by_contra hn
    have hne : deriv ((quad c)^[n]) z ≠ 0 :=
      (quadratic_iterate_deriv_ne_zero_iff c z n).mpr
        (fun k hk he => hn ⟨k, hk, he⟩)
    exact hne hd

/-- Distinct postcritical target values retained by the open target. -/
def postcriticalTargets (c : ℂ) (V : Set ℂ) (n : ℕ) : Finset ℂ :=
  ((Finset.range n).image (fun k => (quad c)^[k] c)).filter (fun y => y ∈ V)

theorem mem_postcriticalTargets (c : ℂ) (V : Set ℂ) (n : ℕ) (y : ℂ) :
    y ∈ postcriticalTargets c V n ↔ y ∈ V ∧ ∃ k < n, (quad c)^[k] c = y := by
  simp only [postcriticalTargets, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  tauto

/-- An encounter with zero fixes the remaining critical-value itinerary. -/
theorem iterate_after_critical (c z : ℂ) (n k : ℕ)
    (hk : k < n) (hz : (quad c)^[k] z = 0) :
    (quad c)^[n] z = (quad c)^[n-(k+1)] c := by
  have hs : (quad c)^[k+1] z = c := by
    rw [Function.iterate_succ_apply', hz]
    simp [quad]
  calc
    (quad c)^[n] z = (quad c)^[n-(k+1)+(k+1)] z :=
      congrArg (fun j : ℕ => (quad c)^[j] z) (by omega)
    _ = (quad c)^[n-(k+1)] ((quad c)^[k+1] z) := Function.iterate_add_apply _ _ _ _
    _ = (quad c)^[n-(k+1)] c := by rw [hs]

/-- The intrinsic critical census is exactly the ramified part of the
finite union of inverse fibers over the distinct postcritical targets. -/
theorem criticalPoints_eq_postcritical_filter (c : ℂ) (V C : Set ℂ) (n : ℕ)
    (hm : MapsTo ((quad c)^[n]) C V) :
    criticalPoints c n C =
      ((postcriticalTargets c V n).biUnion (fun y => localFiber c n C y)).filter
        (fun z => localMultiplicity c z n ≠ 1) := by
  ext z
  rw [Finset.mem_filter, mem_criticalPoints_iff_multiplicity]
  constructor
  · rintro ⟨hz, hmult⟩
    have hcrit := (mem_criticalPoints c n C z).mp
      ((mem_criticalPoints_iff_multiplicity c n C z).mpr ⟨hz, hmult⟩)
    obtain ⟨k, hk, he⟩ := hcrit.2
    have htarget : (quad c)^[n] z ∈ postcriticalTargets c V n :=
      (mem_postcriticalTargets c V n _).mpr
        ⟨hm hz, n-(k+1), by omega, (iterate_after_critical c z n k hk he).symm⟩
    exact ⟨Finset.mem_biUnion.mpr
      ⟨(quad c)^[n] z, htarget, (mem_localFiber c n C _ z).mpr ⟨hz, rfl⟩⟩, hmult⟩
  · rintro ⟨hF, hmult⟩
    obtain ⟨y, _, hy⟩ := Finset.mem_biUnion.mp hF
    exact ⟨((mem_localFiber c n C y z).mp hy).1, hmult⟩

/-- Regrouping the critical locus by actual target values counts every
critical point once; repeated values and repeated encounters cause no
duplication. -/
theorem criticalPoints_ramification_sum (c : ℂ) (V C : Set ℂ) (n : ℕ)
    (hm : MapsTo ((quad c)^[n]) C V) :
    (∑ z ∈ criticalPoints c n C, (localMultiplicity c z n - 1)) =
      ∑ y ∈ postcriticalTargets c V n,
        ∑ z ∈ localFiber c n C y, (localMultiplicity c z n - 1) := by
  let A := postcriticalTargets c V n
  let F := A.biUnion (fun y => localFiber c n C y)
  have hdisj : Set.PairwiseDisjoint (↑A) (fun y => localFiber c n C y) := by
    intro y hy w hw hne
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact hne (((mem_localFiber c n C y z).mp hz).2.symm.trans
      ((mem_localFiber c n C w z).mp hz').2)
  have hsub : criticalPoints c n C ⊆ F := by
    rw [criticalPoints_eq_postcritical_filter c V C n hm]
    exact Finset.filter_subset _ _
  have hzero : ∀ z ∈ F, z ∉ criticalPoints c n C →
      localMultiplicity c z n - 1 = 0 := by
    intro z hz hn
    have hmult : localMultiplicity c z n = 1 := by
      by_contra hne
      apply hn
      rw [criticalPoints_eq_postcritical_filter c V C n hm]
      exact Finset.mem_filter.mpr ⟨hz, hne⟩
    rw [hmult]
  calc
    (∑ z ∈ criticalPoints c n C, (localMultiplicity c z n - 1)) =
        ∑ z ∈ F, (localMultiplicity c z n - 1) := Finset.sum_subset hsub hzero
    _ = ∑ y ∈ A, ∑ z ∈ localFiber c n C y, (localMultiplicity c z n - 1) :=
      Finset.sum_biUnion hdisj

/-- Exact ramification budget for every actual connected open pullback
component, including targets with holes. The correction term is the
previously defined missing critical charge, not an assumed zero. -/
theorem quadratic_component_critical_budget (c : ℂ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (n : ℕ) (x : ℂ)
    (hx : (quad c)^[n] x ∈ V) :
    (∑ z ∈ criticalPoints c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) x),
      (localMultiplicity c z n - 1)) +
        componentReflectionDebt c V n x + 1 = 2 ^ componentReflectionRank c V n x := by
  let C := connectedComponentIn ((quad c)^[n] ⁻¹' V) x
  let A := postcriticalTargets c V n
  have hm : MapsTo ((quad c)^[n]) C V := connectedComponentIn_subset _ _
  have hA : ∀ k < n, (quad c)^[k] c ∈ V → (quad c)^[k] c ∈ A := by
    intro k hk hv
    exact (mem_postcriticalTargets c V n _).mpr ⟨hv, k, hk, rfl⟩
  have hs : (∑ y ∈ A, componentFiberDefect c V y n x) =
      ∑ y ∈ A, ∑ z ∈ localFiber c n C y, (localMultiplicity c z n - 1) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact quadratic_component_defect_eq_ramification_sum c V hVo hVc y
      ((mem_postcriticalTargets c V n y).mp hy).1 n x hx
  have he := aggregate_defect_debt_eq_degree c V A n x hA
  rw [hs, ← criticalPoints_ramification_sum c V C n hm] at he
  exact he

/-- The actual number of critical points is bounded by the exact
ramification budget, with repeated encounters contributing extra weight. -/
theorem quadratic_component_critical_count_bound (c : ℂ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (n : ℕ) (x : ℂ)
    (hx : (quad c)^[n] x ∈ V) :
    (criticalPoints c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) x)).card +
      componentReflectionDebt c V n x + 1 ≤ 2 ^ componentReflectionRank c V n x := by
  let C := connectedComponentIn ((quad c)^[n] ⁻¹' V) x
  have hle : (criticalPoints c n C).card ≤
      ∑ z ∈ criticalPoints c n C, (localMultiplicity c z n - 1) := by
    calc
      (criticalPoints c n C).card = ∑ z ∈ criticalPoints c n C, (1 : ℕ) := by simp
      _ ≤ ∑ z ∈ criticalPoints c n C, (localMultiplicity c z n - 1) := by
        apply Finset.sum_le_sum
        intro z hz
        have hne := ((mem_criticalPoints_iff_multiplicity c n C z).mp hz).2
        have hp : 0 < localMultiplicity c z n := by
          exact pow_pos (by norm_num) _
        omega
  have he := quadratic_component_critical_budget c V hVo hVc n x hx
  change (∑ z ∈ criticalPoints c n C, (localMultiplicity c z n - 1)) +
    componentReflectionDebt c V n x + 1 = 2 ^ componentReflectionRank c V n x at he
  change (criticalPoints c n C).card + componentReflectionDebt c V n x + 1 ≤ _
  omega

/-- The whole plane has both inverse sheets at every finite stage. -/
theorem componentReflectionRank_univ (c : ℂ) (n : ℕ) (x : ℂ) :
    componentReflectionRank c univ n x = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp [componentReflectionRank, ih, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]

/-- Every critical value is retained when the target is the whole plane,
so there is no missing critical charge in the global formula. -/
theorem componentReflectionDebt_univ (c : ℂ) (n : ℕ) (x : ℂ) :
    componentReflectionDebt c univ n x = 0 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp [componentReflectionDebt, ih, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ]

/-- Global ramification of the actual quadratic iterate is exactly
degree minus one, for every parameter and horizon, including repeated
critical returns. The finite set has no duplicate critical points. -/
theorem quadratic_global_ramification_budget (c : ℂ) (n : ℕ) :
    (∑ z ∈ criticalPoints c n univ, (localMultiplicity c z n - 1)) + 1 = 2^n := by
  have h := quadratic_component_critical_budget c univ isOpen_univ
    isPreconnected_univ n 0 (mem_univ _)
  simpa [componentReflectionRank_univ, componentReflectionDebt_univ,
    connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ] using h

end
end LoopsQuadraticRamificationCensus
