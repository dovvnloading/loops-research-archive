import QuadraticCylinderRamification

/-!
# Actual quadratic component fiber degrees

A connected pullback component has either disjoint signed inverse
sheets or a reflection-invariant sheet. No simple connectivity of
the target is assumed.
-/

namespace LoopsQuadraticComponentFiberDegree

open Set Function Classical
open LoopsQuadraticCylinderCensus LoopsQuadraticCriticalFiberCensus
open LoopsQuadraticCylinderRamification LoopsStationarySeparatorTransport

noncomputable section

/-- A single reflected pair forces the entire component to be
reflection invariant. -/
theorem even_component_reflection_of_pair (F : ℂ → ℂ) (V : Set ℂ)
    (heven : ∀ z, F (-z) = F z) (x a : ℂ)
    (ha : a ∈ connectedComponentIn (F ⁻¹' V) x)
    (hna : -a ∈ connectedComponentIn (F ⁻¹' V) x) :
    ∀ z ∈ connectedComponentIn (F ⁻¹' V) x,
      -z ∈ connectedComponentIn (F ⁻¹' V) x := by
  let C := connectedComponentIn (F ⁻¹' V) x
  have hconn : IsPreconnected ((fun w : ℂ => -w) '' C) :=
    isPreconnected_connectedComponentIn.image _ continuous_neg.continuousOn
  have hhit : -a ∈ (fun w : ℂ => -w) '' C := ⟨a, ha, rfl⟩
  have hsub : (fun w : ℂ => -w) '' C ⊆ F ⁻¹' V := by
    rintro _ ⟨w, hw, rfl⟩
    change F (-w) ∈ V
    rw [heven]
    exact connectedComponentIn_subset (F ⁻¹' V) x hw
  have h := hconn.subset_connectedComponentIn hhit hsub
  rw [← connectedComponentIn_eq hna] at h
  intro z hz
  exact h ⟨z, hz, rfl⟩

theorem quadratic_eq_or_neg (c a b : ℂ) (h : quad c a = quad c b) :
    a = b ∨ a = -b := by
  change a^2+c = b^2+c at h
  have hp : (a-b)*(a+b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hp with hp | hp
  · exact Or.inl (sub_eq_zero.mp hp)
  · exact Or.inr (by linear_combination hp)

/-- Outside the invariant case the first quadratic step is
globally injective on the actual pullback component. -/
theorem quadratic_component_nonsymmetric_inj (c : ℂ) (n : ℕ)
    (V : Set ℂ) (x : ℂ)
    (hn : ¬ (∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
      -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x)) :
    InjOn (quad c) (connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) := by
  intro a ha b hb he
  rcases quadratic_eq_or_neg c a b he with hab | hab
  · exact hab
  · exfalso
    apply hn
    have hna : -b ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x := hab ▸ ha
    exact even_component_reflection_of_pair ((quad c)^[n+1]) V
      (quadratic_positive_iterate_even c (n+1) (by omega)) x b hb hna

/-- Exact first-step transport of the actual finite localized fiber,
with no univalence or simple connectivity assumption. -/
theorem quadratic_component_fiber_image (c : ℂ) (n : ℕ)
    (V : Set ℂ) (hVo : IsOpen V) (x y : ℂ)
    (hx : (quad c)^[n+1] x ∈ V) :
    (localFiber c (n+1) (connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) y).image
      (quad c) =
    localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y := by
  classical
  let f := quad c
  let C := connectedComponentIn (f^[n+1] ⁻¹' V) x
  let D := connectedComponentIn (f^[n] ⁻¹' V) (f x)
  have hfirst : f '' C = D := by
    simpa only [Function.iterate_one] using
      quadratic_prefix_component_image c n 1 V hVo x hx
  change (localFiber c (n+1) C y).image f = localFiber c n D y
  ext w
  simp only [Finset.mem_image, mem_localFiber]
  constructor
  · rintro ⟨z, ⟨hz, hzy⟩, rfl⟩
    have hw' : f z ∈ f '' C := ⟨z, hz, rfl⟩
    have hw : f z ∈ D := hfirst ▸ hw'
    exact ⟨hw, by simpa only [Function.iterate_succ_apply] using hzy⟩
  · rintro ⟨hw, hwy⟩
    have hw' : w ∈ f '' C := hfirst.symm ▸ hw
    obtain ⟨z, hz, rfl⟩ := hw'
    exact ⟨z, ⟨hz, by simpa only [Function.iterate_succ_apply] using hwy⟩, rfl⟩

/-- A non-reflection-invariant component preserves the entire
tail fiber cardinality, even for a critical target. -/
theorem quadratic_component_nonsymmetric_count (c : ℂ) (n : ℕ)
    (V : Set ℂ) (hVo : IsOpen V) (x y : ℂ)
    (hx : (quad c)^[n+1] x ∈ V)
    (hn : ¬ (∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
      -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x)) :
    (localFiber c (n+1) (connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) y).card =
    (localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y).card := by
  classical
  let C := connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x
  let A := localFiber c (n+1) C y
  have hi := quadratic_component_nonsymmetric_inj c n V x hn
  have hAi : InjOn (quad c) (↑A : Set ℂ) := by
    intro a ha b hb hab
    exact hi ((mem_localFiber c (n+1) C y a).mp ha).1
      ((mem_localFiber c (n+1) C y b).mp hb).1 hab
  have he := Finset.card_image_of_injOn hAi
  simpa only [A, C, quadratic_component_fiber_image c n V hVo x y hx] using he.symm

/-- The invariant case doubles the actual tail fiber, with exactly
one lost point if the tail contains the critical value over y. -/
theorem quadratic_component_symmetric_count (c : ℂ) (n : ℕ)
    (V : Set ℂ) (hVo : IsOpen V) (x y : ℂ)
    (hx : (quad c)^[n+1] x ∈ V)
    (hs : ∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
      -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) :
    (localFiber c (n+1) (connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x) y).card +
      (if c ∈ localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y
        then 1 else 0) =
    2 * (localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x)) y).card := by
  classical
  let f := quad c
  let C := connectedComponentIn (f^[n+1] ⁻¹' V) x
  let D := connectedComponentIn (f^[n] ⁻¹' V) (f x)
  let B := localFiber c n D y
  have hfirst : f '' C = D := by
    simpa only [Function.iterate_one] using
      quadratic_prefix_component_image c n 1 V hVo x hx
  have hposmem (w : ℂ) : fiberRoot c w ∈ C ↔ w ∈ D := by
    constructor
    · intro hw
      rw [← hfirst]
      exact ⟨fiberRoot c w, hw, fiberRoot_spec c w⟩
    · intro hw
      have hw' : w ∈ f '' C := hfirst.symm ▸ hw
      obtain ⟨a, ha, haw⟩ := hw'
      have he : f a = f (fiberRoot c w) :=
        haw.trans (fiberRoot_spec c w).symm
      rcases quadratic_eq_or_neg c a (fiberRoot c w) he with h | h
      · exact h ▸ ha
      · have h' : -a ∈ C := hs a ha
        rw [h, neg_neg] at h'
        exact h'
  have hnegmem (w : ℂ) : -fiberRoot c w ∈ C ↔ w ∈ D := by
    constructor
    · intro hw
      have h : -(-fiberRoot c w) ∈ C := hs _ hw
      rw [neg_neg] at h
      exact (hposmem w).mp h
    · intro hw
      exact hs _ ((hposmem w).mpr hw)
  have hpos : (globalFiber c n y).filter (fun w => fiberRoot c w ∈ C) = B := by
    ext w
    simp only [B, Finset.mem_filter, mem_globalFiber, mem_localFiber, hposmem]
    exact and_comm
  have hneg : ((globalFiber c n y).erase c).filter (fun w => -fiberRoot c w ∈ C) =
      B.erase c := by
    ext w
    simp only [B, Finset.mem_filter, Finset.mem_erase, mem_globalFiber,
      mem_localFiber, hnegmem]
    tauto
  change (localFiber c (n+1) C y).card + (if c ∈ B then 1 else 0) = 2 * B.card
  rw [localFiber_signed_count, hpos, hneg]
  by_cases hc : c ∈ B
  · rw [if_pos hc, Finset.card_erase_of_mem hc]
    have hp : 0 < B.card := Finset.card_pos.mpr ⟨c, hc⟩
    omega
  · rw [if_neg hc, Finset.erase_eq_of_notMem hc]
    omega

/-- Count the reflection-invariant steps along the actual forward
component itinerary, independently of the choice of target fiber. -/
def componentReflectionRank (c : ℂ) (V : Set ℂ) : ℕ → ℂ → ℕ
  | 0, _ => 0
  | n+1, x => componentReflectionRank c V n (quad c x) +
      (if ∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
        -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x then 1 else 0)

/-- The local distinct-point deficit is accumulated only at invariant
steps. The loss is propagated through exactly those earlier steps
which double the fiber. -/
def componentFiberDefect (c : ℂ) (V : Set ℂ) (y : ℂ) : ℕ → ℂ → ℕ
  | 0, _ => 0
  | n+1, x =>
      if ∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
        -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x then
        2 * componentFiberDefect c V y n (quad c x) +
          (if c ∈ localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V)
            (quad c x)) y then 1 else 0)
      else componentFiberDefect c V y n (quad c x)

theorem componentReflectionRank_le (c : ℂ) (V : Set ℂ) (n : ℕ) (x : ℂ) :
    componentReflectionRank c V n x ≤ n := by
  induction n generalizing x with
  | zero => simp [componentReflectionRank]
  | succ n ih =>
    have ht := ih (quad c x)
    by_cases hs : ∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
        -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x
    · simp only [componentReflectionRank, if_pos hs]
      omega
    · simp only [componentReflectionRank, if_neg hs]
      omega

/-- The exact component census at every depth and every target point,
including postcritical values and targets with holes. -/
theorem quadratic_component_fiber_card_exact (c : ℂ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (y : ℂ) (hy : y ∈ V)
    (n : ℕ) (x : ℂ) (hx : (quad c)^[n] x ∈ V) :
    (localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) y).card +
      componentFiberDefect c V y n x = 2 ^ componentReflectionRank c V n x := by
  induction n generalizing x with
  | zero =>
    have hxV : x ∈ V := by simpa using hx
    have hsub : V ⊆ connectedComponentIn V x :=
      hVc.subset_connectedComponentIn hxV Subset.rfl
    have hmem : y ∈ connectedComponentIn ((quad c)^[0] ⁻¹' V) x := by
      simpa using hsub hy
    have hf : localFiber c 0 (connectedComponentIn ((quad c)^[0] ⁻¹' V) x) y = {y} := by
      ext z
      simp only [mem_localFiber, Function.iterate_zero, id_eq, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · intro h
        subst z
        exact ⟨hmem, rfl⟩
    rw [hf]
    simp [componentFiberDefect, componentReflectionRank]
  | succ n ih =>
    have hxD : (quad c)^[n] (quad c x) ∈ V := by
      simpa only [Function.iterate_succ_apply] using hx
    have ht := ih (quad c x) hxD
    by_cases hs : ∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
        -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x
    · have he := quadratic_component_symmetric_count c n V hVo x y hx hs
      simp only [componentFiberDefect, componentReflectionRank, if_pos hs, pow_succ]
      omega
    · have he := quadratic_component_nonsymmetric_count c n V hVo x y hx hs
      simp only [componentFiberDefect, componentReflectionRank, if_neg hs, Nat.add_zero]
      omega

theorem componentFiberDefect_zero_of_regular (c : ℂ) (V : Set ℂ) (y : ℂ)
    (n : ℕ) (x : ℂ) (hreg : ∀ k < n, (quad c)^[k] c ≠ y) :
    componentFiberDefect c V y n x = 0 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have ht := ih (quad c x) (fun k hk => hreg k (by omega))
    have hc : c ∉ localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V)
        (quad c x)) y := by
      intro h
      exact hreg n (by omega) ((mem_localFiber c n _ y c).mp h).2
    by_cases hs : ∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
        -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x
    · rw [componentFiberDefect, if_pos hs, ht, if_neg hc] <;> omega
    · rw [componentFiberDefect, if_neg hs, ht]

/-- All regular fibers in a given actual component have the same
cardinality, a power of two with exponent bounded by the depth. -/
theorem quadratic_component_regular_degree (c : ℂ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (n : ℕ) (x : ℂ)
    (hx : (quad c)^[n] x ∈ V) :
    ∀ y ∈ V, (∀ k < n, (quad c)^[k] c ≠ y) →
      (localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) y).card =
        2 ^ componentReflectionRank c V n x := by
  intro y hy hreg
  have he := quadratic_component_fiber_card_exact c V hVo hVc y hy n x hx
  rw [componentFiberDefect_zero_of_regular c V y n x hreg, Nat.add_zero] at he
  exact he

/-- Vanishing reflection rank forces univalence on the complete
connected component, not merely on one regular fiber. -/
theorem quadratic_component_rank_zero_inj (c : ℂ) (V : Set ℂ) (hVo : IsOpen V)
    (n : ℕ) (x : ℂ) (hx : (quad c)^[n] x ∈ V)
    (hr : componentReflectionRank c V n x = 0) :
    InjOn ((quad c)^[n]) (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) := by
  induction n generalizing x with
  | zero =>
    intro a ha b hb hab
    simpa using hab
  | succ n ih =>
    have hxD : (quad c)^[n] (quad c x) ∈ V := by
      simpa only [Function.iterate_succ_apply] using hx
    by_cases hs : ∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
        -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x
    · simp only [componentReflectionRank, if_pos hs] at hr
      omega
    · have ht : componentReflectionRank c V n (quad c x) = 0 := by
        simpa only [componentReflectionRank, if_neg hs, Nat.add_zero] using hr
      have hi := ih (quad c x) hxD ht
      have hfirst : quad c '' connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x =
          connectedComponentIn ((quad c)^[n] ⁻¹' V) (quad c x) := by
        simpa only [Function.iterate_one] using
          quadratic_prefix_component_image c n 1 V hVo x hx
      intro a ha b hb hab
      apply quadratic_component_nonsymmetric_inj c n V x hs ha hb
      apply hi
      · rw [← hfirst]
        exact ⟨a, ha, rfl⟩
      · rw [← hfirst]
        exact ⟨b, hb, rfl⟩
      · simpa only [Function.iterate_succ_apply] using hab

/-- One regular point suffices to test univalence, even for a
connected open target with nontrivial fundamental group. -/
theorem quadratic_component_univalent_iff_regular_card_one
    (c : ℂ) (V : Set ℂ) (hVo : IsOpen V) (hVc : IsPreconnected V)
    (n : ℕ) (x : ℂ) (hx : (quad c)^[n] x ∈ V)
    (y : ℂ) (hy : y ∈ V) (hreg : ∀ k < n, (quad c)^[k] c ≠ y) :
    InjOn ((quad c)^[n]) (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) ↔
      (localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) y).card = 1 := by
  let C := connectedComponentIn ((quad c)^[n] ⁻¹' V) x
  constructor
  · intro hi
    have he := quadratic_global_component_image c n V hVo hVc x hx
    have hh : y ∈ (quad c)^[n] '' C := he.symm ▸ hy
    obtain ⟨a, ha, hay⟩ := hh
    have hf : localFiber c n C y = {a} := by
      ext z
      simp only [mem_localFiber, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, hzy⟩
        exact hi hz ha (hzy.trans hay.symm)
      · intro h
        subst z
        exact ⟨ha, hay⟩
    change (localFiber c n C y).card = 1
    rw [hf]
    simp
  · intro hc
    have he := quadratic_component_regular_degree c V hVo hVc n x hx y hy hreg
    have hp : 2 ^ componentReflectionRank c V n x = 1 := he.symm.trans hc
    have hr : componentReflectionRank c V n x = 0 := by
      by_contra hn
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [hk, pow_succ] at hp
      have hpos : 0 < (2 : ℕ)^k := by positivity
      omega
    exact quadratic_component_rank_zero_inj c V hVo n x hx hr

/-- Proper open localizations inherit the same regular-fiber test.
The localization need not contain all global components. -/
theorem quadratic_localized_univalent_iff_regular_card_one
    (c : ℂ) (n : ℕ) (S V : Set ℂ)
    (hS : IsOpen S) (hVo : IsOpen V) (hVc : IsPreconnected V)
    (hm : MapsTo ((quad c)^[n]) S V)
    (hp : IsProperMap (fun z : S => (⟨(quad c)^[n] z, hm z.property⟩ : V)))
    (x : ℂ) (hx : x ∈ S) (y : ℂ) (hy : y ∈ V)
    (hreg : ∀ k < n, (quad c)^[k] c ≠ y) :
    InjOn ((quad c)^[n]) (connectedComponentIn S x) ↔
      (localFiber c n (connectedComponentIn S x) y).card = 1 := by
  have he := proper_localization_component_global ((quad c)^[n]) S V
    (quadratic_iterate_proper c n).continuous hS hVo hm hp x hx
  rw [he]
  exact quadratic_component_univalent_iff_regular_card_one c V hVo hVc n x
    (hm hx) y hy hreg


/-- Enlarging the target cannot destroy an invariant step in the
actual component itinerary. This needs neither openness nor regularity. -/
theorem componentReflectionRank_mono (c : ℂ) (U V : Set ℂ)
    (hUV : U ⊆ V) (n : ℕ) (x : ℂ) (hx : (quad c)^[n] x ∈ U) :
    componentReflectionRank c U n x ≤ componentReflectionRank c V n x := by
  induction n generalizing x with
  | zero => simp [componentReflectionRank]
  | succ n ih =>
    have hxD : (quad c)^[n] (quad c x) ∈ U := by
      simpa only [Function.iterate_succ_apply] using hx
    have ht := ih (quad c x) hxD
    by_cases hsU : ∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' U) x,
        -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' U) x
    · have hsub : connectedComponentIn ((quad c)^[n+1] ⁻¹' U) x ⊆
          connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x :=
        connectedComponentIn_mono x (preimage_mono hUV)
      have hxC : x ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' U) x :=
        mem_connectedComponentIn hx
      have hsV := even_component_reflection_of_pair ((quad c)^[n+1]) V
        (quadratic_positive_iterate_even c (n+1) (by omega)) x x
        (hsub hxC) (hsub (hsU x hxC))
      simp only [componentReflectionRank, if_pos hsU, if_pos hsV]
      omega
    · by_cases hsV : ∀ z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x,
          -z ∈ connectedComponentIn ((quad c)^[n+1] ⁻¹' V) x
      · simp only [componentReflectionRank, if_neg hsU, if_pos hsV]
        omega
      · simp only [componentReflectionRank, if_neg hsU, if_neg hsV]
        omega

/-- Exact selected-component enlargement test over any single target
point, including critical values. Equality of local inverse fibers
means that the enlarged component contains no other old component. -/
theorem quadratic_enlargement_no_merger_iff_fiber_eq (c : ℂ) (n : ℕ)
    (U V : Set ℂ) (hUV : U ⊆ V) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (x : ℂ) (hx : (quad c)^[n] x ∈ U) (y : ℂ) (hy : y ∈ U) :
    localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' U) x) y =
      localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) y ↔
    connectedComponentIn ((quad c)^[n] ⁻¹' V) x ∩ ((quad c)^[n] ⁻¹' U) =
      connectedComponentIn ((quad c)^[n] ⁻¹' U) x := by
  let f := (quad c)^[n]
  let A := connectedComponentIn (f ⁻¹' U) x
  let B := connectedComponentIn (f ⁻¹' V) x
  have hAB : A ⊆ B := connectedComponentIn_mono x (preimage_mono hUV)
  change localFiber c n A y = localFiber c n B y ↔ B ∩ f ⁻¹' U = A
  constructor
  · intro hF
    apply Subset.antisymm
    · intro z hz
      have hzU : f z ∈ U := hz.2
      let D := connectedComponentIn (f ⁻¹' U) z
      have him := quadratic_global_component_image c n U hUo hUc z hzU
      have hyD : y ∈ f '' D := him.symm ▸ hy
      obtain ⟨w, hw, hwy⟩ := hyD
      have hwB : w ∈ B := by
        have hm : D ⊆ connectedComponentIn (f ⁻¹' V) z :=
          connectedComponentIn_mono z (preimage_mono hUV)
        have he : B = connectedComponentIn (f ⁻¹' V) z := connectedComponentIn_eq hz.1
        exact he.symm ▸ hm hw
      have hwF : w ∈ localFiber c n B y :=
        (mem_localFiber c n B y w).mpr ⟨hwB, hwy⟩
      have hwF' : w ∈ localFiber c n A y := hF.symm ▸ hwF
      have hwA : w ∈ A := ((mem_localFiber c n A y w).mp hwF').1
      have hAw : A = connectedComponentIn (f ⁻¹' U) w := connectedComponentIn_eq hwA
      have hDw : D = connectedComponentIn (f ⁻¹' U) w := connectedComponentIn_eq hw
      change z ∈ A
      rw [hAw, ← hDw]
      exact mem_connectedComponentIn hzU
    · intro z hz
      exact ⟨hAB hz, connectedComponentIn_subset (f ⁻¹' U) x hz⟩
  · intro h
    ext z
    simp only [mem_localFiber]
    constructor
    · rintro ⟨hz, hzy⟩
      exact ⟨hAB hz, hzy⟩
    · rintro ⟨hz, hzy⟩
      have hzU : f z ∈ U := by
        change ((fun w : ℂ => w^2+c)^[n]) z ∈ U
        rw [hzy]
        exact hy
      have hz' : z ∈ B ∩ f ⁻¹' U := ⟨hz, hzU⟩
      exact ⟨h ▸ hz', hzy⟩

/-- At a regular target the no-merger test becomes a single numerical
equality of intrinsic reflection ranks. This works even when neither
target is simply connected and both contain other critical values. -/
theorem quadratic_enlargement_rank_eq_iff_no_merger (c : ℂ) (n : ℕ)
    (U V : Set ℂ) (hUV : U ⊆ V)
    (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hVo : IsOpen V) (hVc : IsPreconnected V)
    (x : ℂ) (hx : (quad c)^[n] x ∈ U) (y : ℂ) (hy : y ∈ U)
    (hreg : ∀ k < n, (quad c)^[k] c ≠ y) :
    componentReflectionRank c U n x = componentReflectionRank c V n x ↔
    connectedComponentIn ((quad c)^[n] ⁻¹' V) x ∩ ((quad c)^[n] ⁻¹' U) =
      connectedComponentIn ((quad c)^[n] ⁻¹' U) x := by
  have heU := quadratic_component_regular_degree c U hUo hUc n x hx y hy hreg
  have heV := quadratic_component_regular_degree c V hVo hVc n x (hUV hx) y (hUV hy) hreg
  have hAB : connectedComponentIn ((quad c)^[n] ⁻¹' U) x ⊆
      connectedComponentIn ((quad c)^[n] ⁻¹' V) x :=
    connectedComponentIn_mono x (preimage_mono hUV)
  have hsub : localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' U) x) y ⊆
      localFiber c n (connectedComponentIn ((quad c)^[n] ⁻¹' V) x) y := by
    intro z hz
    obtain ⟨hzU, hzy⟩ := (mem_localFiber c n _ y z).mp hz
    exact (mem_localFiber c n _ y z).mpr ⟨hAB hzU, hzy⟩
  rw [← quadratic_enlargement_no_merger_iff_fiber_eq c n U V hUV hUo hUc x hx y hy]
  constructor
  · intro hr
    apply Finset.eq_of_subset_of_card_le hsub
    rw [heU, heV, hr]
  · intro hF
    have hcard := congrArg Finset.card hF
    rw [heU, heV] at hcard
    exact Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) hcard


end
end LoopsQuadraticComponentFiberDegree
