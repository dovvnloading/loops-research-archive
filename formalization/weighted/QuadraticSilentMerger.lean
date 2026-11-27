import QuadraticMergerBalance
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Maximal component mergers with no new critical values

For every complex quadratic parameter and every depth, the complement
of the finite postcritical set has one connected full pullback. Any
simply connected old target inside that complement has exactly `2^n`
univalent pullback components, all of which merge into that one
component. The entire merger is recorded by reflection debt.
-/

namespace LoopsQuadraticSilentMerger

open Set Function Classical Metric
open LoopsQuadraticCylinderCensus LoopsQuadraticCriticalFiberCensus
open LoopsQuadraticCylinderRamification LoopsQuadraticComponentFiberDegree
open LoopsQuadraticEnlargementDegree
open LoopsQuadraticRamificationCensus LoopsQuadraticMergerBalance

noncomputable section

/-- Distinct postcritical targets through the specified depth. -/
def finitePostcritical (c : ℂ) (n : ℕ) : Finset ℂ :=
  (Finset.range n).image (fun k => (quad c)^[k] c)

/-- The enlarged target omits all postcritical targets at that depth. -/
def criticalFreeTarget (c : ℂ) (n : ℕ) : Set ℂ :=
  (↑(finitePostcritical c n) : Set ℂ)ᶜ

private theorem complex_rank_gt_one : 1 < Module.rank ℝ ℂ := by
  rw [Complex.rank_real_complex]
  norm_num

theorem mem_finitePostcritical (c : ℂ) (n : ℕ) (y : ℂ) :
    y ∈ finitePostcritical c n ↔ ∃ k < n, (quad c)^[k] c = y := by
  simp only [finitePostcritical, Finset.mem_image, Finset.mem_range]

theorem criticalFreeTarget_open (c : ℂ) (n : ℕ) :
    IsOpen (criticalFreeTarget c n) :=
  (finitePostcritical c n).finite_toSet.isClosed.isOpen_compl

theorem criticalFreeTarget_path_connected (c : ℂ) (n : ℕ) :
    IsPathConnected (criticalFreeTarget c n) :=
  (finitePostcritical c n).finite_toSet.countable.isPathConnected_compl_of_one_lt_rank
    complex_rank_gt_one

/-- Neither the old target nor the enlarged target can contain a
postcritical value when both lie in this complement. -/
theorem criticalFreeTarget_postcritical_avoided (c : ℂ) (n k : ℕ) (hk : k < n) :
    (quad c)^[k] c ∉ criticalFreeTarget c n := by
  intro h
  exact h ((mem_finitePostcritical c n ((quad c)^[k] c)).mpr ⟨k, hk, rfl⟩)

/-- The new critical charge is zero for every old target, with no
connectedness or containment assumptions on that old target. -/
theorem silent_newCriticalCharge_zero (c : ℂ) (n : ℕ) (U : Set ℂ) (x : ℂ) :
    newCriticalCharge c n U (criticalFreeTarget c n) x = 0 := by
  have he : postcriticalTargets c (criticalFreeTarget c n \ U) n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨⟨hzV, _⟩, k, hk, he⟩ :=
      (mem_postcriticalTargets c (criticalFreeTarget c n \ U) n z).mp hz
    exact criticalFreeTarget_postcritical_avoided c n k hk (he.symm ▸ hzV)
  simp only [newCriticalCharge, he, Finset.sum_empty]

/-- The exceptional source set is finite, using the actual polynomial
fiber census rather than an assumed topological covering. -/
theorem finitePostcritical_preimage_finite (c : ℂ) (n : ℕ) :
    ((quad c)^[n] ⁻¹' (↑(finitePostcritical c n) : Set ℂ)).Finite := by
  apply (finitePostcritical c n).finite_toSet.preimage'
  intro y _
  have he : (quad c)^[n] ⁻¹' ({y} : Set ℂ) =
      (↑(globalFiber c n y) : Set ℂ) := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, Finset.mem_coe, mem_globalFiber]
  rw [he]
  exact (globalFiber c n y).finite_toSet

/-- Removing the finitely many exceptional inverse points leaves a
path connected actual source, at every parameter and every depth. -/
theorem criticalFree_pullback_path_connected (c : ℂ) (n : ℕ) :
    IsPathConnected ((quad c)^[n] ⁻¹' criticalFreeTarget c n) := by
  change IsPathConnected (((quad c)^[n] ⁻¹'
    (↑(finitePostcritical c n) : Set ℂ))ᶜ)
  exact (finitePostcritical_preimage_finite c n).countable.isPathConnected_compl_of_one_lt_rank
    complex_rank_gt_one

/-- There is just one actual enlarged pullback component. -/
theorem criticalFree_component (c : ℂ) (n : ℕ) (x : ℂ)
    (hx : (quad c)^[n] x ∈ criticalFreeTarget c n) :
    connectedComponentIn ((quad c)^[n] ⁻¹' criticalFreeTarget c n) x =
      (quad c)^[n] ⁻¹' criticalFreeTarget c n := by
  exact Subset.antisymm
    (connectedComponentIn_subset ((quad c)^[n] ⁻¹' criticalFreeTarget c n) x)
    ((criticalFree_pullback_path_connected c n).isConnected.isPreconnected
      |>.subset_connectedComponentIn hx Subset.rfl)

/-- Every fiber over the enlarged target is the complete global
fiber, because the whole pullback is connected. -/
theorem criticalFree_fiber_eq_global (c : ℂ) (n : ℕ) (x y : ℂ)
    (hx : (quad c)^[n] x ∈ criticalFreeTarget c n)
    (hy : y ∈ criticalFreeTarget c n) :
    localFiber c n
      (connectedComponentIn ((quad c)^[n] ⁻¹' criticalFreeTarget c n) x) y =
        globalFiber c n y := by
  rw [criticalFree_component c n x hx]
  ext z
  simp only [mem_localFiber, mem_globalFiber]
  constructor
  · exact fun h => h.2
  · intro hz
    refine ⟨?_, hz⟩
    change (quad c)^[n] z ∈ criticalFreeTarget c n
    rw [hz]
    exact hy

/-- The enlarged source has the full degree `2^n` even though no
postcritical target is present. Its intrinsic reflection rank is n. -/
theorem criticalFree_rank (c : ℂ) (n : ℕ) (x : ℂ)
    (hx : (quad c)^[n] x ∈ criticalFreeTarget c n) :
    componentReflectionRank c (criticalFreeTarget c n) n x = n := by
  let y := (quad c)^[n] x
  have hy : y ∈ criticalFreeTarget c n := hx
  have hreg : ∀ k < n, (quad c)^[k] c ≠ y := by
    intro k hk he
    exact criticalFreeTarget_postcritical_avoided c n k hk (he.symm ▸ hy)
  have he := quadratic_component_regular_degree c (criticalFreeTarget c n)
    (criticalFreeTarget_open c n)
    (criticalFreeTarget_path_connected c n).isConnected.isPreconnected
    n x hx y hy hreg
  rw [criticalFree_fiber_eq_global c n x y hx hy,
    (globalFiber_full_card_iff c y n).mpr hreg] at he
  exact Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) he.symm

/-- All enlarged degree beyond one is missing critical charge.
The value is the maximal possible debt `2^n - 1`. -/
theorem criticalFree_debt (c : ℂ) (n : ℕ) (x : ℂ)
    (hx : (quad c)^[n] x ∈ criticalFreeTarget c n) :
    componentReflectionDebt c (criticalFreeTarget c n) n x = 2^n-1 := by
  have he := aggregate_defect_debt_eq_degree c (criticalFreeTarget c n) ∅ n x
    (fun k hk hv => (criticalFreeTarget_postcritical_avoided c n k hk hv).elim)
  rw [criticalFree_rank c n x hx] at he
  simp only [Finset.sum_empty, zero_add] at he
  omega

/-- Every old component over a simply connected target contained in
the critical-free target is genuinely univalent. -/
theorem old_component_univalent (c : ℂ) (n : ℕ) (U : Set ℂ)
    (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hUV : U ⊆ criticalFreeTarget c n) (a : ℂ) (ha : (quad c)^[n] a ∈ U) :
    InjOn ((quad c)^[n]) (connectedComponentIn ((quad c)^[n] ⁻¹' U) a) := by
  exact (quadratic_iterate_univalent_component c n U hUo hUc
    (fun k hk hv => criticalFreeTarget_postcritical_avoided c n k hk (hUV hv)) a ha).1

theorem old_component_rank_zero (c : ℂ) (n : ℕ) (U : Set ℂ)
    (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hUV : U ⊆ criticalFreeTarget c n) (a : ℂ) (ha : (quad c)^[n] a ∈ U) :
    componentReflectionRank c U n a = 0 := by
  let y := (quad c)^[n] a
  have hy : y ∈ U := ha
  have hpre := hUc.isPathConnected.isConnected.isPreconnected
  have hreg : ∀ k < n, (quad c)^[k] c ≠ y := by
    intro k hk he
    exact criticalFreeTarget_postcritical_avoided c n k hk (he.symm ▸ hUV hy)
  have hc := (quadratic_component_univalent_iff_regular_card_one
    c U hUo hpre n a ha y hy hreg).mp
      (old_component_univalent c n U hUo hUc hUV a ha)
  have he := quadratic_component_regular_degree c U hUo hpre n a ha y hy hreg
  have hp : (2 : ℕ) ^ componentReflectionRank c U n a = 2^0 := by
    simpa using he.symm.trans hc
  exact Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) hp

/-- Each actual old component has zero reflection debt. -/
theorem old_component_debt_zero (c : ℂ) (n : ℕ) (U : Set ℂ)
    (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hUV : U ⊆ criticalFreeTarget c n) (a : ℂ) (ha : (quad c)^[n] a ∈ U) :
    componentReflectionDebt c U n a = 0 := by
  have he := aggregate_defect_debt_eq_degree c U ∅ n a
    (fun k hk hv => (criticalFreeTarget_postcritical_avoided c n k hk (hUV hv)).elim)
  rw [old_component_rank_zero c n U hUo hUc hUV a ha] at he
  simp only [Finset.sum_empty, zero_add, pow_zero] at he
  omega

/-- Exactly `2^n` distinct actual old components merge into the one
enlarged component. This holds for every complex parameter, not just
the monomial parameter or a disconnected-filled-set regime. -/
theorem silent_merger_count (c : ℂ) (n : ℕ) (U : Set ℂ)
    (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hUV : U ⊆ criticalFreeTarget c n) (x y : ℂ)
    (hx : (quad c)^[n] x ∈ criticalFreeTarget c n) (hy : y ∈ U) :
    (mergerCensus c n U (criticalFreeTarget c n) x y).card = 2^n := by
  have hreg : ∀ k < n, (quad c)^[k] c ≠ y := by
    intro k hk he
    exact criticalFreeTarget_postcritical_avoided c n k hk (he.symm ▸ hUV hy)
  have he := mergerCensus_uniform_rank_count c n U (criticalFreeTarget c n)
    hUV hUo hUc.isPathConnected.isConnected.isPreconnected
    (criticalFreeTarget_open c n)
    (criticalFreeTarget_path_connected c n).isConnected.isPreconnected
    x y hx hy hreg 0 (fun a _ ha => old_component_rank_zero c n U hUo hUc hUV a ha)
  simpa only [pow_zero, Nat.mul_one, criticalFree_rank c n x hx] using he

/-- At every retained target point, the selected old component misses
exactly `2^n - 1` inverse points that lie in its enlarged component.
This is a pointwise obstruction at every fiber, not only a count of
the merged geometric components. -/
theorem silent_missing_fiber_count (c : ℂ) (n : ℕ) (U : Set ℂ)
    (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hUV : U ⊆ criticalFreeTarget c n) (x t : ℂ)
    (hx : (quad c)^[n] x ∈ U) (ht : t ∈ U) :
    (localFiber c n
        (connectedComponentIn ((quad c)^[n] ⁻¹' criticalFreeTarget c n) x) t \
      localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' U) x) t).card = 2^n-1 := by
  have hreg : ∀ k < n, (quad c)^[k] c ≠ t := by
    intro k hk he
    exact criticalFreeTarget_postcritical_avoided c n k hk (he.symm ▸ hUV ht)
  have hAB : connectedComponentIn ((quad c)^[n] ⁻¹' U) x ⊆
      connectedComponentIn ((quad c)^[n] ⁻¹' criticalFreeTarget c n) x :=
    connectedComponentIn_mono x (preimage_mono hUV)
  have hsub :
      localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' U) x) t ⊆
        localFiber c n
          (connectedComponentIn ((quad c)^[n] ⁻¹' criticalFreeTarget c n) x) t := by
    intro z hz
    obtain ⟨hzA, hzt⟩ := (mem_localFiber c n _ t z).mp hz
    exact (mem_localFiber c n _ t z).mpr ⟨hAB hzA, hzt⟩
  have hbig := quadratic_component_regular_degree c (criticalFreeTarget c n)
    (criticalFreeTarget_open c n)
    (criticalFreeTarget_path_connected c n).isConnected.isPreconnected
    n x (hUV hx) t (hUV ht) hreg
  rw [criticalFree_rank c n x (hUV hx)] at hbig
  have hsmall := quadratic_component_regular_degree c U hUo
    hUc.isPathConnected.isConnected.isPreconnected n x hx t ht hreg
  rw [old_component_rank_zero c n U hUo hUc hUV x hx] at hsmall
  rw [Finset.card_sdiff_of_subset hsub, hbig, hsmall, pow_zero]

/-- At every positive depth the retained-component square fails to
be Cartesian. Excluding every postcritical target does not prevent
component mergers when the enlarged target has holes. -/
theorem silent_merger_not_cartesian (c : ℂ) (n : ℕ) (hn : 0 < n)
    (U : Set ℂ) (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hUV : U ⊆ criticalFreeTarget c n) (x : ℂ) (hx : (quad c)^[n] x ∈ U) :
    connectedComponentIn ((quad c)^[n] ⁻¹' criticalFreeTarget c n) x ∩
        ((quad c)^[n] ⁻¹' U) ≠ connectedComponentIn ((quad c)^[n] ⁻¹' U) x := by
  let y := (quad c)^[n] x
  have hy : y ∈ U := hx
  have hreg : ∀ k < n, (quad c)^[k] c ≠ y := by
    intro k hk he
    exact criticalFreeTarget_postcritical_avoided c n k hk (he.symm ▸ hUV hy)
  intro hcart
  have he := (quadratic_enlargement_rank_eq_iff_no_merger c n
    U (criticalFreeTarget c n) hUV hUo hUc.isPathConnected.isConnected.isPreconnected
    (criticalFreeTarget_open c n)
    (criticalFreeTarget_path_connected c n).isConnected.isPreconnected
    x hx y hy hreg).mpr hcart
  rw [old_component_rank_zero c n U hUo hUc hUV x hx,
    criticalFree_rank c n x (hUV hx)] at he
  omega

/-- Every actual quadratic admits a bounded simply connected old
target realizing the maximal merger at every depth. The old pieces
are univalent, the enlarged target omits all postcritical values,
and its missing charge accounts for the complete merger. -/
theorem every_quadratic_silent_merger (c : ℂ) (n : ℕ) :
    ∃ (x y : ℂ) (r : ℝ), 0 < r ∧
      ball y r ⊆ criticalFreeTarget c n ∧ (quad c)^[n] x = y ∧
      (mergerCensus c n (ball y r) (criticalFreeTarget c n) x y).card = 2^n ∧
      componentReflectionDebt c (criticalFreeTarget c n) n x = 2^n-1 ∧
      (∀ a : ℂ, (quad c)^[n] a ∈ ball y r →
        InjOn ((quad c)^[n]) (connectedComponentIn ((quad c)^[n] ⁻¹' ball y r) a) ∧
          componentReflectionDebt c (ball y r) n a = 0) ∧
      (0 < n →
        connectedComponentIn ((quad c)^[n] ⁻¹' criticalFreeTarget c n) x ∩
            ((quad c)^[n] ⁻¹' ball y r) ≠
          connectedComponentIn ((quad c)^[n] ⁻¹' ball y r) x) := by
  obtain ⟨y, hy⟩ := (criticalFreeTarget_path_connected c n).nonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (criticalFreeTarget_open c n) y hy
  obtain ⟨x, hxy⟩ := quadratic_iterate_surjective c n y
  have hyball : y ∈ ball y r := mem_ball_self hr
  have hx : (quad c)^[n] x ∈ criticalFreeTarget c n := hxy.symm ▸ hy
  have hxball : (quad c)^[n] x ∈ ball y r := hxy.symm ▸ hyball
  have hsimply : IsSimplyConnected (ball y r) := by
    letI : ContractibleSpace (ball y r) := Metric.contractibleSpace_ball hr
    exact inferInstance
  refine ⟨x, y, r, hr, hball, hxy,
    silent_merger_count c n (ball y r) isOpen_ball hsimply hball x y hx hyball,
    criticalFree_debt c n x hx, ?_, ?_⟩
  · intro a ha
    exact ⟨old_component_univalent c n (ball y r) isOpen_ball hsimply hball a ha,
      old_component_debt_zero c n (ball y r) isOpen_ball hsimply hball a ha⟩
  · intro hn
    exact silent_merger_not_cartesian c n hn (ball y r) isOpen_ball hsimply hball x hxball

end
end LoopsQuadraticSilentMerger
