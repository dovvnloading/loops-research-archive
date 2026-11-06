import PhaseFuture27

/-!
# Exact nine-cycle rays and conditional quadratic renormalization fibers

The arithmetic is kernel-checked. Landing of dynamical rays, complex
polynomial-like domains, and Levin's geometric hypotheses are NOT
assumed to have been proved by Lean.
-/

namespace LoopsFormal.TipRayPortrait

def criticalValueLower : Fin 261632 := ⟨116791, by decide⟩
def criticalValueUpper : Fin 261632 := ⟨144841, by decide⟩

def forwardAngle (n : Nat) (a : Fin 261632) : Fin 261632 :=
  ⟨(2 ^ n * a.val) % 261632, Nat.mod_lt _ (by decide)⟩

/-- After nine doublings the two critical-value rays become the
    283/511 and 228/511 rays. -/
theorem critical_value_enters_period_nine :
    forwardAngle 9 criticalValueLower = ⟨144896, by decide⟩ ∧
    forwardAngle 9 criticalValueUpper = ⟨116736, by decide⟩ := by
  decide +kernel

/-- Side 0 follows the lower critical-value ray, regardless of angle
    order at later stages. Phase i represents the point x_(10+i). -/
def tailRay (i : Fin 9) (side : Fin 2) : Fin 511 :=
  ⟨((if side.val = 0 then 283 else 228) * 2 ^ i.val) % 511,
    Nat.mod_lt _ (by decide)⟩

/-- All eighteen explicit angle labels are distinct. -/
theorem eighteen_angles_distinct :
    Function.Injective (fun x : Fin 9 × Fin 2 => tailRay x.1 x.2) := by
  intro x y
  rcases x with ⟨i, side⟩
  rcases y with ⟨j, other⟩
  revert i side j other
  decide +kernel

/-- Every angle in the portrait has least positive doubling period nine. -/
theorem eighteen_angles_have_no_early_return :
    ∀ i : Fin 9, ∀ side : Fin 2, ∀ t : Fin 9,
      0 < t.val →
      (2 ^ t.val * (tailRay i side).val) % 511 ≠ (tailRay i side).val := by
  decide +kernel

theorem ambient_ninth_return_fixed (a : Fin 511) :
    (512 * a.val) % 511 = a.val := by
  have ha := a.isLt
  omega

/-- The positive endpoint x18 of the real I9 interval is landed by
    the distinct rays of angles 397/511 and 114/511. Landing itself
    is a separately attributed analytic theorem input. -/
theorem phase_eighteen_pair :
    tailRay ⟨8, by decide⟩ ⟨0, by decide⟩ = ⟨397, by decide⟩ ∧
    tailRay ⟨8, by decide⟩ ⟨1, by decide⟩ = ⟨114, by decide⟩ := by
  decide +kernel

def betweenEndpoints (x y u : Nat) : Bool :=
  decide (min x y < u) && decide (u < max x y)

def chordCrosses (i j : Fin 9) : Bool :=
  let a := (tailRay i ⟨0, by decide⟩).val
  let b := (tailRay i ⟨1, by decide⟩).val
  let c := (tailRay j ⟨0, by decide⟩).val
  let d := (tailRay j ⟨1, by decide⟩).val
  (betweenEndpoints a b c) != (betweenEndpoints a b d)

/-- Exact noncrossing condition for the nine rational-angle chords. -/
theorem nine_chords_pairwise_unlinked :
    ∀ i j : Fin 9, i ≠ j → chordCrosses i j = false := by
  decide +kernel

/-- Internal degree-two angles: doubling modulo any positive grid. -/
def innerDouble (q : Nat) (a : Fin q) : Fin q :=
  ⟨(2 * a.val) % q, Nat.mod_lt _ (by have h := a.isLt; omega)⟩

/-- Doubling has exactly one fixed circle angle, zero. -/
theorem innerDouble_fixed_is_zero (q : Nat) (a : Fin q)
    (h : innerDouble q a = a) : a.val = 0 := by
  have hh : (2 * a.val) % q = a.val := by
    have hv := congrArg Fin.val h
    simpa [innerDouble] using hv
  have ha := a.isLt
  by_cases hsmall : 2 * a.val < q
  · rw [Nat.mod_eq_of_lt hsmall] at hh
    omega
  · have hbig : q ≤ 2 * a.val := by omega
    have hsub : 2 * a.val - q < q := by omega
    rw [Nat.mod_eq_sub_mod hbig, Nat.mod_eq_of_lt hsub] at hh
    omega

def ambientReturn9 (a : Fin 511) : Fin 511 :=
  ⟨(512 * a.val) % 511, Nat.mod_lt _ (by decide)⟩

theorem ambientReturn9_fixed (a : Fin 511) : ambientReturn9 a = a := by
  apply Fin.ext
  exact ambient_ninth_return_fixed a

/-- Abstract semiconjugacy obstruction: a fixed ambient ray can map
    only to internal angle zero, if a valid angular map is defined. -/
theorem fixed_ray_maps_to_internal_zero {E : Type} (step : E → E)
    (q : Nat) (read : E → Fin q) (x : E)
    (hx : step x = x)
    (hsem : read (step x) = innerDouble q (read x)) :
    (read x).val = 0 := by
  have hf : innerDouble q (read x) = read x := by
    rw [hx] at hsem
    exact hsem.symm
  exact innerDouble_fixed_is_zero q (read x) hf

/-- Two fixed ambient rays necessarily have the same internal angle.
    This theorem is conditional on the angular semiconjugacy equations. -/
theorem two_fixed_rays_forced_to_one_internal_angle {E : Type}
    (step : E → E) (q : Nat) (read : E → Fin q) (x y : E)
    (hx : step x = x) (hy : step y = y)
    (hsemx : read (step x) = innerDouble q (read x))
    (hsemy : read (step y) = innerDouble q (read y)) :
    read x = read y := by
  apply Fin.ext
  calc
    (read x).val = 0 := fixed_ray_maps_to_internal_zero step q read x hx hsemx
    _ = (read y).val :=
      (fixed_ray_maps_to_internal_zero step q read y hy hsemy).symm

/-- The two explicit external rays at x18 are a forced fiber of ANY
    valid degree-two return-nine angular correspondence defined there.
    The existence of Levin's source-domain map remains an analytic gate. -/
theorem tip_phase_eighteen_forced_fiber (q : Nat) (read : Fin 511 → Fin q)
    (hleft : read (ambientReturn9 ⟨397, by decide⟩) =
      innerDouble q (read ⟨397, by decide⟩))
    (hright : read (ambientReturn9 ⟨114, by decide⟩) =
      innerDouble q (read ⟨114, by decide⟩)) :
    read ⟨397, by decide⟩ = read ⟨114, by decide⟩ := by
  exact two_fixed_rays_forced_to_one_internal_angle ambientReturn9 q read
    ⟨397, by decide⟩ ⟨114, by decide⟩
    (ambientReturn9_fixed _) (ambientReturn9_fixed _) hleft hright

#print axioms tip_phase_eighteen_forced_fiber
#print axioms eighteen_angles_distinct
#print axioms nine_chords_pairwise_unlinked

end LoopsFormal.TipRayPortrait
