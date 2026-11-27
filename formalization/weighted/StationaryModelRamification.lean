import StationaryCriticalFiber
import StationaryRamificationCensus

/-!
# Exact inverse-label loss for actual quadratic geometric models

The census is exact at every model target, without assuming a singleton
physical fiber. Its discrepancy from the actual polynomial inverse level
is exactly the weighted list of postcritical points identified with a
different physical anchor. This also characterizes injectivity of the
projection on each complete inverse level.
-/

namespace LoopsStationaryModelRamification

open Set Function Classical
open LoopsStationaryFiberDynamics LoopsStationaryLightModel
open LoopsStationaryGeometricFibers
open LoopsStationaryCriticalFiber LoopsStationaryRamificationCensus
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
  have hone : 1 ≤ collapsedCriticalDefect p F v a (k+1) := by
    simp only [collapsedCriticalDefect, hp, hne, and_self, if_true]
    omega
  calc
    2^m = 2^m * 1 := by omega
    _ ≤ 2^m * collapsedCriticalDefect p F v a (k+1) :=
      Nat.mul_le_mul_left _ hone
    _ ≤ _ := collapsedCriticalDefect_growth p F v a (k+1) m

/-- Complete invariance identifies the subtype and ambient inverse counts. -/
theorem quadratic_filled_inverse_ncard (c : ℂ)
    (a : quadraticFilled c) (n : ℕ) :
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
  exact hc.symm

/-- The actual filled quadratic has the required one-step point census. -/
theorem quadratic_filled_predecessor_census (c : ℂ)
    (o : quadraticFilled c) (ho : (o : ℂ) = 0) (a : quadraticFilled c) :
    ((quadraticFilledMap c) ⁻¹' {a}).Finite ∧
      ((quadraticFilledMap c) ⁻¹' {a}).ncard +
        (if a = quadraticFilledMap c o then 1 else 0) = 2 := by
  refine ⟨quadratic_restricted_fiber_finite c (quadraticFilled c)
    (quadraticFilledMap c) (fun _ => rfl) a, ?_⟩
  have hv : ((quadraticFilledMap c o : quadraticFilled c) : ℂ) = c := by
    change (o : ℂ)^2+c = c
    rw [ho]
    ring
  have ha : a = quadraticFilledMap c o ↔ (a : ℂ) = c := by
    rw [Subtype.ext_iff, hv]
  simp only [ha]
  have hc := quadratic_filled_inverse_ncard c a 1
  simp only [Function.iterate_one] at hc
  rw [hc]
  simpa [criticalFiberDefect, eq_comm] using globalFiber_card_exact c (a : ℂ) 1

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]

/-- Exact all-depth census for every geometric model target; critical
identification and finite degree are derived from the physical map. -/
theorem quadratic_filled_model_census_exact
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (hKi : interior (quadraticFilled c) = ∅)
    (o : quadraticFilled c) (ho : (o : ℂ) = 0) (y : Y) (n : ℕ) :
    ((G^[n]) ⁻¹' {y}).Finite ∧
      ((G^[n]) ⁻¹' {y}).ncard + criticalDefect G (G (p o)) y n = 2^n := by
  have hc := quadratic_filled_model_predecessor_census
    c p G hp hsurj hs hf hlight hKi o ho
  exact ⟨iterate_fiber_finite G (fun z => (hc z).1) y n,
    iterate_fiber_ncard_exact G (fun z => (hc z).1) (G (p o))
      (fun z => (hc z).2) y n⟩

/-- Weighted physical postcritical contacts give the entire model count. -/
theorem quadratic_filled_model_census_sum
    (c : ℂ) (p : quadraticFilled c → Y) (G : Y → Y)
    (hp : Continuous p) (hsurj : Surjective p)
    (hs : Semiconj p (quadraticFilledMap c) G)
    (hf : ∀ y : Y, IsPreconnected (p ⁻¹' {y}))
    (hlight : ∀ y : Y, IsTotallyDisconnected (G ⁻¹' {y}))
    (hKi : interior (quadraticFilled c) = ∅)
    (o : quadraticFilled c) (ho : (o : ℂ) = 0) (y : Y) (n : ℕ) :
    ((G^[n]) ⁻¹' {y}).ncard +
      (∑ k ∈ Finset.range n, 2^(n-1-k) *
        (if p (((quadraticFilledMap c)^[k]) (quadraticFilledMap c o)) = y
          then 1 else 0)) = 2^n := by
  have he := (quadratic_filled_model_census_exact
    c p G hp hsurj hs hf hlight hKi o ho y n).2
  rw [← hs o, criticalDefect_eq_sum] at he
  have hiter (k : ℕ) : G^[k] (p (quadraticFilledMap c o)) =
      p (((quadraticFilledMap c)^[k]) (quadraticFilledMap c o)) :=
    (hs.iterate_right k (quadraticFilledMap c o)).symm
  simpa only [hiter] using he

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
  have hF := quadratic_filled_predecessor_census c o ho
  have hG := quadratic_filled_model_predecessor_census
    c p G hp hsurj hs hf hlight hKi o ho
  have hGc (y : Y) : (G ⁻¹' {y}).ncard +
      (if y = p (quadraticFilledMap c o) then 1 else 0) = 2 := by
    rw [hs o]
    exact (hG y).2
  have he := semiconj_inverse_fiber_loss p (quadraticFilledMap c) G hs
    (quadraticFilledMap c o) a (fun x => (hF x).1) (fun y => (hG y).1)
    (fun x => by simpa using (hF x).2) hGc n
  rwa [quadratic_filled_inverse_ncard c a n] at he

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
  have hF := quadratic_filled_predecessor_census c o ho
  have hG := quadratic_filled_model_predecessor_census
    c p G hp hsurj hs hf hlight hKi o ho
  have hGc (y : Y) : (G ⁻¹' {y}).ncard +
      (if y = p (quadraticFilledMap c o) then 1 else 0) = 2 := by
    rw [hs o]
    exact (hG y).2
  have hproj := model_iterate_preimage_projection p (quadraticFilledMap c) G hs
    (quadratic_filled_light_fiber_image c p G hp hsurj hs hf hlight) a n
  have hfinite := iterate_fiber_finite (quadraticFilledMap c) (fun x => (hF x).1) a n
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
  exact hiff.trans (semiconj_inverse_fiber_card_eq_iff p (quadraticFilledMap c) G hs
    (quadraticFilledMap c o) a (fun x => (hF x).1) (fun y => (hG y).1)
    (fun x => by simpa using (hF x).2) hGc n)

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
