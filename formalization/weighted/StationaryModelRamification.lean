import StationaryRamificationCensus

/-!
# Exact inverse-label loss for actual quadratic geometric models

We compare the archived exact physical and model censuses. Their
discrepancy is exactly the weighted list of postcritical points identified
with a different physical anchor. This also characterizes injectivity of
the projection on each complete inverse level, without a singleton target
fiber assumption.
-/

namespace LoopsStationaryModelRamification

open Set Function Classical
open LoopsStationaryFiberDynamics LoopsStationaryLightModel
open LoopsStationaryGeometricFibers
open LoopsQuadraticEscapeFullness LoopsStationaryRamificationCensus
open LoopsQuadraticCriticalFiberCensus
open scoped BigOperators

noncomputable section

/-- Every additional inverse step doubles an existing label loss. -/
theorem collapsedCriticalDefect_growth {X Y : Type*}
    (p : X → Y) (F : X → X) (v a : X) (n m : ℕ) :
    2^m * collapsedCriticalDefect p F v a n ≤
      collapsedCriticalDefect p F v a (n+m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, pow_succ]
    change 2^m * 2 * collapsedCriticalDefect p F v a n ≤
      2 * collapsedCriticalDefect p F v a (n+m) + _
    calc
      2^m * 2 * collapsedCriticalDefect p F v a n =
          2 * (2^m * collapsedCriticalDefect p F v a n) := by ring
      _ ≤ 2 * collapsedCriticalDefect p F v a (n+m) := Nat.mul_le_mul_left 2 ih
      _ ≤ _ := Nat.le_add_right _ _

/-- A false contact at time k forces 2^m lost labels at depth k+1+m. -/
theorem collapsedCriticalDefect_of_contact {X Y : Type*}
    (p : X → Y) (F : X → X) (v a : X) (k m : ℕ)
    (hp : p ((F^[k]) v) = p a) (hne : (F^[k]) v ≠ a) :
    2^m ≤ collapsedCriticalDefect p F v a (k+1+m) := by
  have hhit : p ((F^[k]) v) = p a ∧ (F^[k]) v ≠ a := ⟨hp, hne⟩
  have hone : 1 ≤ collapsedCriticalDefect p F v a (k+1) := by
    rw [collapsedCriticalDefect, if_pos hhit]
    omega
  calc
    2^m = 2^m * 1 := by omega
    _ ≤ 2^m * collapsedCriticalDefect p F v a (k+1) :=
      Nat.mul_le_mul_left _ hone
    _ ≤ _ := collapsedCriticalDefect_growth p F v a (k+1) m

/-- Complete invariance identifies the subtype and ambient inverse counts. -/
private theorem quadratic_filled_inverse_level (c : ℂ)
    (a : quadraticFilled c) (n : ℕ) :
    (((quadraticFilledMap c)^[n]) ⁻¹' {a}).Finite ∧
      (((quadraticFilledMap c)^[n]) ⁻¹' {a}).ncard =
        (globalFiber c n (a : ℂ)).card := by
  have hsem : Semiconj (Subtype.val : quadraticFilled c → ℂ)
      (quadraticFilledMap c) (fun z : ℂ => z^2+c) := fun _ => rfl
  have himage : (Subtype.val : quadraticFilled c → ℂ) ''
      (((quadraticFilledMap c)^[n]) ⁻¹' {a}) =
      (↑(globalFiber c n (a : ℂ)) : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply (mem_globalFiber c n (a : ℂ) (x : ℂ)).mpr
      change ((quadraticFilledMap c)^[n]) x = a at hx
      rw [← hsem.iterate_right n x, hx]
    · intro hz
      have he := (mem_globalFiber c n (a : ℂ) z).mp hz
      have hzK : z ∈ quadraticFilled c := by
        apply (quadratic_filled_iterate_mem_iff c z n).mp
        rw [he]
        exact a.property
      refine ⟨⟨z, hzK⟩, ?_, rfl⟩
      apply Subtype.ext
      rw [hsem.iterate_right n]
      exact he
  have hc := Set.ncard_image_of_injective
    (((quadraticFilledMap c)^[n]) ⁻¹' {a})
    (Subtype.coe_injective : Injective (Subtype.val : quadraticFilled c → ℂ))
  rw [himage, Set.ncard_coe_finset] at hc
  have hfinim : ((Subtype.val : quadraticFilled c → ℂ) ''
      (((quadraticFilledMap c)^[n]) ⁻¹' {a})).Finite := by
    rw [himage]
    exact Finset.finite_toSet _
  exact ⟨hfinim.of_finite_image Subtype.coe_injective.injOn, hc.symm⟩

private theorem filled_critical_defect (c : ℂ) (o a : quadraticFilled c)
    (ho : (o : ℂ) = 0) (n : ℕ) :
    modelCriticalDefect (quadraticFilledMap c) (quadraticFilledMap c o) a n =
      criticalFiberDefect c (a : ℂ) n := by
  have hsem : Semiconj (Subtype.val : quadraticFilled c → ℂ)
      (quadraticFilledMap c) (fun z : ℂ => z^2+c) := fun _ => rfl
  have hv : ((quadraticFilledMap c o : quadraticFilled c) : ℂ) = c := by
    change (o : ℂ)^2+c = c
    rw [ho]
    ring
  have heq (k : ℕ) : ((quadraticFilledMap c)^[k]) (quadraticFilledMap c o) = a ↔
      ((fun z : ℂ => z^2+c)^[k]) c = (a : ℂ) := by
    rw [Subtype.ext_iff, hsem.iterate_right k, hv]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [modelCriticalDefect, criticalFiberDefect, ih]
    by_cases h : ((quadraticFilledMap c)^[n]) (quadraticFilledMap c o) = a
    · rw [if_pos h, if_pos ((heq n).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((heq n).mpr hh))]

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

private theorem model_census_from_archive
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (hKi : interior (quadraticFilled c) = ∅)
    (o : quadraticFilled c) (ho : (o : ℂ) = 0) (y : Y) (n : ℕ) :
    ((G^[n]) ⁻¹' {y}).ncard + modelCriticalDefect G (G (p o)) y n = 2^n := by
  have h0 : (0 : ℂ) ∈ quadraticFilled c := ho ▸ o.property
  obtain ⟨M, hM, hcard, _⟩ := quadratic_filled_light_model_all_target_census
    c p G hp hsurj hs hf hlight hKi h0 n y
  have ho' : (⟨0,h0⟩ : quadraticFilled c) = o := Subtype.ext ho.symm
  have hset : ((G^[n]) ⁻¹' {y}) = (↑M : Set Y) := by
    ext z
    exact (hM z).symm
  rw [ho'] at hcard
  rw [hset, Set.ncard_coe_finset]
  exact hcard

/-- Exact loss in actual complex predecessor points after projection. -/
theorem quadratic_filled_quotient_loss
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (hKi : interior (quadraticFilled c) = ∅)
    (o : quadraticFilled c) (ho : (o : ℂ) = 0)
    (a : quadraticFilled c) (n : ℕ) :
    (globalFiber c n (a : ℂ)).card = ((G^[n]) ⁻¹' {p a}).ncard +
      collapsedCriticalDefect p (quadraticFilledMap c) (quadraticFilledMap c o) a n := by
  have hphysical := globalFiber_card_exact c (a : ℂ) n
  have hmodel := model_census_from_archive c p G hp hsurj hs hf hlight hKi o ho (p a) n
  rw [← hs o, semiconj_modelCriticalDefect p (quadraticFilledMap c) G hs,
    filled_critical_defect c o a ho n] at hmodel
  omega

/-- Sharp finite-horizon replacement for a singleton-anchor premise. -/
theorem quadratic_filled_inverse_labels_iff
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (hKi : interior (quadraticFilled c) = ∅)
    (o : quadraticFilled c) (ho : (o : ℂ) = 0)
    (a : quadraticFilled c) (n : ℕ) :
    InjOn p (((quadraticFilledMap c)^[n]) ⁻¹' {a}) ↔
      ∀ k < n, p (((quadraticFilledMap c)^[k]) (quadraticFilledMap c o)) = p a →
        ((quadraticFilledMap c)^[k]) (quadraticFilledMap c o) = a := by
  have hproj := model_iterate_preimage_projection p (quadraticFilledMap c) G hs
    (quadratic_filled_light_fiber_image c p G hp hsurj hs hf hlight) a n
  have hfinite := (quadratic_filled_inverse_level c a n).1
  have hiff : InjOn p (((quadraticFilledMap c)^[n]) ⁻¹' {a}) ↔
      (((quadraticFilledMap c)^[n]) ⁻¹' {a}).ncard = ((G^[n]) ⁻¹' {p a}).ncard := by
    constructor
    · intro hi
      have he := hi.ncard_image
      rw [← hproj] at he
      exact he.symm
    · intro he
      apply Set.injOn_of_ncard_image_eq _ hfinite
      rw [← hproj]
      exact he.symm
  rw [hiff, (quadratic_filled_inverse_level c a n).2,
    ← collapsedCriticalDefect_zero_iff p (quadraticFilledMap c) (quadraticFilledMap c o) a n]
  have he := quadratic_filled_quotient_loss c p G hp hsurj hs hf hlight hKi o ho a n
  omega

/-- One false postcritical contact forces exponentially many lost labels. -/
theorem quadratic_filled_quotient_loss_lower_bound
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (hKi : interior (quadraticFilled c) = ∅)
    (o : quadraticFilled c) (ho : (o : ℂ) = 0)
    (a : quadraticFilled c) (k m : ℕ)
    (hcontact : p (((quadraticFilledMap c)^[k]) (quadraticFilledMap c o)) = p a)
    (hne : ((quadraticFilledMap c)^[k]) (quadraticFilledMap c o) ≠ a) :
    ((G^[k+1+m]) ⁻¹' {p a}).ncard + 2^m ≤
      (globalFiber c (k+1+m) (a : ℂ)).card := by
  have he := quadratic_filled_quotient_loss
    c p G hp hsurj hs hf hlight hKi o ho a (k+1+m)
  have hl := collapsedCriticalDefect_of_contact p (quadraticFilledMap c)
    (quadraticFilledMap c o) a k m hcontact hne
  omega

end

end LoopsStationaryModelRamification
