import QuadraticSilentMerger
import QuadraticInverseOpen

/-!
# Maximal silent mergers inside relatively compact targets

The maximal merger does not require an unbounded enlarged target. Finite
paths join a complete regular quadratic inverse fiber inside the full
critical-free source. A connected neighborhood of their compact target
image retains the whole fiber while its compact closure still avoids
every postcritical value. A smaller disk then exhibits the complete
merger inside two relatively compact actual targets.
-/

namespace LoopsQuadraticCompactMerger

open Set Function Classical Metric
open LoopsQuadraticCylinderCensus LoopsQuadraticCriticalFiberCensus
open LoopsQuadraticCylinderRamification LoopsQuadraticComponentFiberDegree
open LoopsQuadraticEnlargementDegree LoopsQuadraticMergerBalance
open LoopsQuadraticSilentMerger LoopsQuadraticInverseOpen
open LoopsQuadraticRamificationCensus

noncomputable section

/-- A finite family in a path connected planar set is contained in
a compact preconnected subset through any prescribed anchor. Only
finitely many actual path ranges are used. -/
theorem finite_compact_connected_hull (S : Set ℂ) (hS : IsPathConnected S)
    (x : ℂ) (hx : x ∈ S) (F : Finset ℂ) (hF : (↑F : Set ℂ) ⊆ S) :
    ∃ K : Set ℂ, IsCompact K ∧ IsPreconnected K ∧ x ∈ K ∧
      (↑F : Set ℂ) ⊆ K ∧ K ⊆ S := by
  classical
  revert hF
  induction F using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨{x}, isCompact_singleton, isPreconnected_singleton,
      mem_singleton x, ?_, singleton_subset_iff.mpr hx⟩
    simp
  | @insert a F ha ih =>
    intro hF
    have hFS : (↑F : Set ℂ) ⊆ S := by
      intro z hz
      exact hF (Finset.mem_insert_of_mem hz)
    obtain ⟨K, hK, hKconn, hxK, hFK, hKS⟩ := ih hFS
    have haS : a ∈ S := hF (Finset.mem_insert_self a F)
    let joined := hS.joinedIn x hx a haS
    let p : Path x a := joined.somePath
    have hpS : range p ⊆ S := by
      rintro z ⟨t, rfl⟩
      exact joined.somePath_mem t
    have hxP : x ∈ range p := ⟨0, p.source⟩
    have haP : a ∈ range p := ⟨1, p.target⟩
    refine ⟨K ∪ range p, hK.union (isCompact_range p.continuous),
      hKconn.union x hxK hxP (isConnected_range p.continuous).isPreconnected,
      Or.inl hxK, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Or.inr haP
      · exact Or.inl (hFK hz)
    · intro z hz
      exact hz.elim hKS hpS

/-- Any prescribed regular target and inverse anchor admit a connected
open target with compact closure in the postcritical-free region, whose
selected component still contains the entire global inverse fiber. -/
theorem compact_full_fiber_target (c : ℂ) (n : ℕ) (x y : ℂ)
    (hy : y ∈ criticalFreeTarget c n) (hxy : (quad c)^[n] x = y) :
    ∃ W : Set ℂ, IsOpen W ∧ IsPreconnected W ∧ y ∈ W ∧
      IsCompact (closure W) ∧ closure W ⊆ criticalFreeTarget c n ∧
      localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' W) x) y =
        globalFiber c n y := by
  let f := (quad c)^[n]
  let S := f ⁻¹' criticalFreeTarget c n
  have hxS : x ∈ S := by
    change (quad c)^[n] x ∈ criticalFreeTarget c n
    rw [hxy]
    exact hy
  have hFS : (↑(globalFiber c n y) : Set ℂ) ⊆ S := by
    intro z hz
    have hzy := (mem_globalFiber c n y z).mp hz
    change (quad c)^[n] z ∈ criticalFreeTarget c n
    rw [hzy]
    exact hy
  obtain ⟨K, hK, hKconn, hxK, hFK, hKS⟩ :=
    finite_compact_connected_hull S (criticalFree_pullback_path_connected c n)
      x hxS (globalFiber c n y) hFS
  have hf : Continuous f := (quadratic_iterate_proper c n).continuous
  have hKimage : IsCompact (f '' K) := hK.image hf
  have hKimageConn : IsPreconnected (f '' K) := hKconn.image f hf.continuousOn
  have hyImage : y ∈ f '' K := ⟨x, hxK, hxy⟩
  have hImageSub : f '' K ⊆ criticalFreeTarget c n := by
    rintro z ⟨a, ha, rfl⟩
    exact hKS ha
  obtain ⟨W, hWo, hWconn, hImageW, hWcompact, hWcl⟩ :=
    connected_precompact_target_neighborhood (f '' K) (criticalFreeTarget c n)
      hKimage hKimageConn y hyImage (criticalFreeTarget_open c n) hImageSub
  have hKpre : K ⊆ f ⁻¹' W := by
    intro z hz
    exact hImageW ⟨z, hz, rfl⟩
  have hKB : K ⊆ connectedComponentIn (f ⁻¹' W) x :=
    hKconn.subset_connectedComponentIn hxK hKpre
  refine ⟨W, hWo, hWconn, hImageW hyImage, hWcompact, hWcl, ?_⟩
  ext z
  simp only [mem_localFiber, mem_globalFiber]
  constructor
  · exact fun h => h.2
  · intro hz
    exact ⟨hKB (hFK ((mem_globalFiber c n y z).mpr hz)), hz⟩

/-- A compactly contained enlarged target can have the full intrinsic
rank and maximal reflection debt while omitting every postcritical
value. The equality of a complete regular fiber supplies the rank. -/
theorem compact_full_degree_target (c : ℂ) (n : ℕ) (x y : ℂ)
    (hy : y ∈ criticalFreeTarget c n) (hxy : (quad c)^[n] x = y) :
    ∃ W : Set ℂ, IsOpen W ∧ IsPreconnected W ∧ y ∈ W ∧
      IsCompact (closure W) ∧ closure W ⊆ criticalFreeTarget c n ∧
      componentReflectionRank c W n x = n ∧
      componentReflectionDebt c W n x = 2^n-1 := by
  obtain ⟨W, hWo, hWconn, hyW, hWcompact, hWcl, hFiber⟩ :=
    compact_full_fiber_target c n x y hy hxy
  have hWV : W ⊆ criticalFreeTarget c n := subset_closure.trans hWcl
  have hxW : (quad c)^[n] x ∈ W := hxy.symm ▸ hyW
  have hreg : ∀ k < n, (quad c)^[k] c ≠ y := by
    intro k hk he
    exact criticalFreeTarget_postcritical_avoided c n k hk (he.symm ▸ hy)
  have hdegree := quadratic_component_regular_degree c W hWo hWconn n x hxW y hyW hreg
  rw [hFiber, (globalFiber_full_card_iff c y n).mpr hreg] at hdegree
  have hrank : componentReflectionRank c W n x = n :=
    Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) hdegree.symm
  have hbudget := aggregate_defect_debt_eq_degree c W ∅ n x
    (fun k hk hv => (criticalFreeTarget_postcritical_avoided c n k hk (hWV hv)).elim)
  rw [hrank] at hbudget
  simp only [Finset.sum_empty, zero_add] at hbudget
  exact ⟨W, hWo, hWconn, hyW, hWcompact, hWcl, hrank, by omega⟩

/-- Full rank of a critical-free enlarged component forces the maximum
number of merged old univalent components over every simply connected
retained target. The enlarged target may be relatively compact. -/
theorem full_rank_silent_merger_count (c : ℂ) (n : ℕ) (U W : Set ℂ)
    (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hWo : IsOpen W) (hWc : IsPreconnected W)
    (hUW : U ⊆ W) (hWV : W ⊆ criticalFreeTarget c n)
    (x y : ℂ) (hxW : (quad c)^[n] x ∈ W) (hy : y ∈ U)
    (hrank : componentReflectionRank c W n x = n) :
    (mergerCensus c n U W x y).card = 2^n := by
  have hUV := hUW.trans hWV
  have hreg : ∀ k < n, (quad c)^[k] c ≠ y := by
    intro k hk he
    exact criticalFreeTarget_postcritical_avoided c n k hk (he.symm ▸ hUV hy)
  have hcount := mergerCensus_uniform_rank_count c n U W hUW hUo
    hUc.isPathConnected.isConnected.isPreconnected hWo hWc x y hxW hy hreg 0
    (fun a _ ha => old_component_rank_zero c n U hUo hUc hUV a ha)
  simpa only [pow_zero, Nat.mul_one, hrank] using hcount

/-- The maximal component merger omits exactly degree minus one
actual inverse points from the selected old component at every
retained target point, even for a relatively compact enlargement. -/
theorem full_rank_silent_missing_fiber (c : ℂ) (n : ℕ) (U W : Set ℂ)
    (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hWo : IsOpen W) (hWc : IsPreconnected W)
    (hUW : U ⊆ W) (hWV : W ⊆ criticalFreeTarget c n)
    (x t : ℂ) (hx : (quad c)^[n] x ∈ U) (ht : t ∈ U)
    (hrank : componentReflectionRank c W n x = n) :
    (localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' W) x) t \
      localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' U) x) t).card = 2^n-1 := by
  have hUV := hUW.trans hWV
  have hreg : ∀ k < n, (quad c)^[k] c ≠ t := by
    intro k hk he
    exact criticalFreeTarget_postcritical_avoided c n k hk (he.symm ▸ hUV ht)
  have hAB : connectedComponentIn ((quad c)^[n] ⁻¹' U) x ⊆
      connectedComponentIn ((quad c)^[n] ⁻¹' W) x :=
    connectedComponentIn_mono x (preimage_mono hUW)
  have hsub : localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' U) x) t ⊆
      localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' W) x) t := by
    intro z hz
    obtain ⟨hzA, hzt⟩ := (mem_localFiber c n _ t z).mp hz
    exact (mem_localFiber c n _ t z).mpr ⟨hAB hzA, hzt⟩
  have hbig := quadratic_component_regular_degree c W hWo hWc n x (hUW hx) t
    (hUW ht) hreg
  rw [hrank] at hbig
  have hsmall := quadratic_component_regular_degree c U hUo
    hUc.isPathConnected.isConnected.isPreconnected n x hx t ht hreg
  rw [old_component_rank_zero c n U hUo hUc hUV x hx] at hsmall
  rw [Finset.card_sdiff_of_subset hsub, hbig, hsmall, pow_zero]

private theorem new_charge_zero_of_critical_free (c : ℂ) (n : ℕ) (U W : Set ℂ)
    (hWV : W ⊆ criticalFreeTarget c n) (x : ℂ) :
    newCriticalCharge c n U W x = 0 := by
  have he : postcriticalTargets c (W \ U) n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨⟨hzW, _⟩, k, hk, he⟩ := (mem_postcriticalTargets c (W \ U) n z).mp hz
    exact criticalFreeTarget_postcritical_avoided c n k hk (he.symm ▸ hWV hzW)
  simp only [newCriticalCharge, he, Finset.sum_empty]

/-- Every parameter and depth admit relatively compact old and enlarged
open targets with the maximal silent component merger. The old target
is a disk compactly contained in the enlarged target, whose compact
closure omits every postcritical target. Every retained fiber has the
maximal defect, and positive depth defeats the Cartesian condition. -/
theorem every_quadratic_compact_silent_merger (c : ℂ) (n : ℕ) :
    ∃ (x y : ℂ) (r : ℝ) (W : Set ℂ),
      0 < r ∧ IsOpen W ∧ IsPreconnected W ∧
      IsCompact (closure W) ∧ closure W ⊆ criticalFreeTarget c n ∧
      IsCompact (closure (ball y r)) ∧ closure (ball y r) ⊆ W ∧
      (quad c)^[n] x = y ∧
      (mergerCensus c n (ball y r) W x y).card = 2^n ∧
      componentReflectionDebt c W n x = 2^n-1 ∧
      newCriticalCharge c n (ball y r) W x = 0 ∧
      (∀ a : ℂ, (quad c)^[n] a ∈ ball y r →
        InjOn ((quad c)^[n]) (connectedComponentIn ((quad c)^[n] ⁻¹' ball y r) a) ∧
          componentReflectionDebt c (ball y r) n a = 0) ∧
      (∀ t ∈ ball y r,
        (localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' W) x) t \
          localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' ball y r) x) t).card =
            2^n-1) ∧
      (0 < n →
        connectedComponentIn ((quad c)^[n] ⁻¹' W) x ∩
            ((quad c)^[n] ⁻¹' ball y r) ≠
          connectedComponentIn ((quad c)^[n] ⁻¹' ball y r) x) := by
  obtain ⟨y, hy⟩ := (criticalFreeTarget_path_connected c n).nonempty
  obtain ⟨x, hxy⟩ := quadratic_iterate_surjective c n y
  obtain ⟨W, hWo, hWc, hyW, hWcompact, hWcl, hrank, hdebt⟩ :=
    compact_full_degree_target c n x y hy hxy
  obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp hWo y hyW
  let r := s / 2
  have hr : 0 < r := half_pos hs
  have hUcl : closure (ball y r) ⊆ W :=
    closure_ball_subset_closedBall.trans
      ((closedBall_subset_ball (half_lt_self hs)).trans hball)
  have hUcompact : IsCompact (closure (ball y r)) :=
    (isCompact_closedBall y r).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have hUW : ball y r ⊆ W := subset_closure.trans hUcl
  have hWV : W ⊆ criticalFreeTarget c n := subset_closure.trans hWcl
  have hUV := hUW.trans hWV
  have hyU : y ∈ ball y r := mem_ball_self hr
  have hxU : (quad c)^[n] x ∈ ball y r := hxy.symm ▸ hyU
  have hxW : (quad c)^[n] x ∈ W := hUW hxU
  have hsimply : IsSimplyConnected (ball y r) := by
    letI : ContractibleSpace (ball y r) := Metric.contractibleSpace_ball hr
    exact inferInstance
  refine ⟨x, y, r, W, hr, hWo, hWc, hWcompact, hWcl, hUcompact, hUcl, hxy,
    full_rank_silent_merger_count c n (ball y r) W isOpen_ball hsimply hWo hWc
      hUW hWV x y hxW hyU hrank,
    hdebt, new_charge_zero_of_critical_free c n (ball y r) W hWV x, ?_, ?_, ?_⟩
  · intro a ha
    exact ⟨old_component_univalent c n (ball y r) isOpen_ball hsimply hUV a ha,
      old_component_debt_zero c n (ball y r) isOpen_ball hsimply hUV a ha⟩
  · intro t ht
    exact full_rank_silent_missing_fiber c n (ball y r) W isOpen_ball hsimply hWo hWc
      hUW hWV x t hxU ht hrank
  · intro hn hcart
    have hreg : ∀ k < n, (quad c)^[k] c ≠ y := by
      intro k hk he
      exact criticalFreeTarget_postcritical_avoided c n k hk (he.symm ▸ hy)
    have he := (quadratic_enlargement_rank_eq_iff_no_merger c n (ball y r) W
      hUW isOpen_ball hsimply.isPathConnected.isConnected.isPreconnected hWo hWc
      x hxU y hyU hreg).mpr hcart
    rw [old_component_rank_zero c n (ball y r) isOpen_ball hsimply hUV x hxU,
      hrank] at he
    omega

end
end LoopsQuadraticCompactMerger
