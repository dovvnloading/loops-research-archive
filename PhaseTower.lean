import RealTwoScalePhase

/-!
# Lossless and lossy phase transport in nested return towers

This file separates three distinct objects that should not be conflated:
* an actual orbit of a self-map on a physical state space;
* the finite clock phase of a return of period `p`;
* a *marking* on phases that may or may not factor through a coarser clock.

Unlike a bare assertion that reduction modulo p is possible, the
factorization theorem is an if-and-only-if characterization of the precise
information lost. The no-go theorem proves that *no injective fine-phase
marking* can be represented by a strictly coarser clock without auxiliary
memory. The statements hold for arbitrary finite periods.

This is formal combinatorics/conditional dynamics. No holomorphic
realization, rays, sheet transport, quantitative KL estimate or MLC gate is
claimed.
-/

namespace LoopsFormal.PhaseTower

open LoopsFormal.Paper2

/-- A phase in a positive-period cyclic clock. -/
abbrev Phase (p : Nat) := Fin p

/-- Forget fine phase information, retaining only its residue mod p. -/
def project (p q : Nat) (hp : 0 < p) (i : Phase q) : Phase p :=
  ⟨i.val % p, Nat.mod_lt i.val hp⟩

/-- Every coarse phase occurs in any fine clock of at least its size. -/
theorem project_surjective (p q : Nat) (hp : 0 < p)
    (hle : p ≤ q) : Function.Surjective (project p q hp) := by
  intro a
  let b : Phase q := ⟨a.val, by have ha := a.isLt; omega⟩
  refine ⟨b, ?_⟩
  apply Fin.ext
  simpa [project, b] using (Nat.mod_eq_of_lt a.isLt)

/-- No collision occurs if the fine clock does not exceed the coarse one. -/
theorem project_injective_of_le (p q : Nat) (hp : 0 < p)
    (hle : q ≤ p) : Function.Injective (project p q hp) := by
  intro i j hij
  have hi : i.val < p := by have hi0 := i.isLt; omega
  have hj : j.val < p := by have hj0 := j.isLt; omega
  apply Fin.ext
  have h := congrArg Fin.val hij
  dsimp [project] at h
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
  exact h

/-- A strict clock reduction always collapses two different phases:
    phase 0 and phase p are indistinguishable modulo p. -/
theorem project_has_collision (p q : Nat) (hp : 0 < p)
    (hlt : p < q) :
    ∃ i j : Phase q, i ≠ j ∧ project p q hp i = project p q hp j := by
  let i : Phase q := ⟨0, by omega⟩
  let j : Phase q := ⟨p, hlt⟩
  refine ⟨i, j, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    dsimp [i, j] at hv
    omega
  · apply Fin.ext
    simp [project, i, j]

/-- A marking is realizable from a coarser phase *alone*. The output
    alphabet is completely arbitrary; no decidable equality is assumed. -/
def FactorsThrough {α : Type} (p q : Nat) (hp : 0 < p)
    (L : Phase q → α) : Prop :=
  ∃ g : Phase p → α, ∀ i, L i = g (project p q hp i)

/-- All fine phases identified by the quotient must carry the same mark. -/
def ConstantOnFibers {α : Type} (p q : Nat) (hp : 0 < p)
    (L : Phase q → α) : Prop :=
  ∀ i j, project p q hp i = project p q hp j → L i = L j

/-- Exact factorization criterion. For p <= q, being constant on quotient
    fibers is not merely necessary: it is sufficient. The proof constructs
    the coarse marking using the canonical representatives 0,...,p-1. -/
theorem factorsThrough_iff_constantOnFibers {α : Type}
    (p q : Nat) (hp : 0 < p) (hle : p ≤ q)
    (L : Phase q → α) :
    FactorsThrough p q hp L ↔ ConstantOnFibers p q hp L := by
  constructor
  · rintro ⟨g, hg⟩ i j hij
    calc
      L i = g (project p q hp i) := hg i
      _ = g (project p q hp j) := by rw [hij]
      _ = L j := (hg j).symm
  · intro h
    let pick : Phase p → Phase q :=
      fun a => ⟨a.val, by have ha := a.isLt; omega⟩
    have hsection : ∀ a : Phase p, project p q hp (pick a) = a := by
      intro a
      apply Fin.ext
      simpa [project, pick] using (Nat.mod_eq_of_lt a.isLt)
    refine ⟨fun a => L (pick a), ?_⟩
    intro i
    exact h i (pick (project p q hp i))
      (hsection (project p q hp i)).symm

/-- The factorized coarse marking is unique when the projection is onto. -/
theorem coarse_marking_unique {α : Type}
    (p q : Nat) (hp : 0 < p) (hle : p ≤ q)
    (L : Phase q → α) (g h : Phase p → α)
    (hg : ∀ i, L i = g (project p q hp i))
    (hh : ∀ i, L i = h (project p q hp i)) :
    g = h := by
  funext a
  obtain ⟨i, hi⟩ := project_surjective p q hp hle a
  calc
    g a = L i := by rw [← hi]; exact (hg i).symm
    _ = h a := by rw [← hi]; exact hh i

/-- Distinct fine-phase marks cannot be obtained from a smaller phase
    alphabet by any relabeling function whatsoever. -/
theorem injective_marking_never_factors {α : Type}
    (p q : Nat) (hp : 0 < p) (hlt : p < q)
    (L : Phase q → α) (hL : Function.Injective L) :
    ¬ FactorsThrough p q hp L := by
  intro hfact
  have hc := (factorsThrough_iff_constantOnFibers p q hp
    (Nat.le_of_lt hlt) L).mp hfact
  obtain ⟨i, j, hne, heq⟩ := project_has_collision p q hp hlt
  exact hne (hL (hc i j heq))

/-- If two phases lie in the same coarse fiber and have different
    labels, they give a concrete obstruction to factoring. -/
theorem two_marks_obstruct_factorization {α : Type}
    (p q : Nat) (hp : 0 < p) (L : Phase q → α)
    (i j : Phase q)
    (heq : project p q hp i = project p q hp j)
    (hneq : L i ≠ L j) :
    ¬ FactorsThrough p q hp L := by
  rintro ⟨g, hg⟩
  apply hneq
  calc
    L i = g (project p q hp i) := hg i
    _ = g (project p q hp j) := by rw [heq]
    _ = L j := (hg j).symm

/-- Reduction first modulo q and then modulo p agrees with reduction
    directly modulo p, provided p divides q. -/
theorem mod_mod_of_divisor (j p q : Nat)
    (hdiv : p ∣ q) : (j % q) % p = j % p := by
  have hz : q % p = 0 := Nat.mod_eq_zero_of_dvd hdiv
  calc
    (j % q) % p = ((j % q) + q * (j / q)) % p := by
      simp [Nat.add_mod, Nat.mul_mod, hz]
    _ = j % p := by rw [Nat.mod_add_div]

/-- Phase reduction composes along a tower of divisible periods. -/
theorem project_compose (p q r : Nat)
    (hp : 0 < p) (hq : 0 < q) (hdiv : p ∣ q)
    (i : Phase r) :
    project p q hp (project q r hq i) = project p r hp i := by
  apply Fin.ext
  exact mod_mod_of_divisor i.val p q hdiv

/-- A clock map commutes with phase projection at *every physical time*. -/
theorem project_of_time (p q j : Nat)
    (hp : 0 < p) (hq : 0 < q) (hdiv : p ∣ q) :
    project p q hp ⟨j % q, Nat.mod_lt j hq⟩ =
      (⟨j % p, Nat.mod_lt j hp⟩ : Phase p) := by
  apply Fin.ext
  exact mod_mod_of_divisor j p q hdiv

/-- Lossless quotienting is transitive: if the q-level marking already
    forgets down to p, then any r-level marking factoring via q also
    forgets down to p. The contrapositive can identify an indispensable
    intermediate memory layer. -/
theorem factorization_transitive {α : Type}
    (p q r : Nat) (hp : 0 < p) (hq : 0 < q)
    (hpq : p ∣ q) (L : Phase r → α)
    (hL : FactorsThrough q r hq L)
    (g : Phase q → α) (hg : FactorsThrough p q hp g)
    (hvia : ∀ i, L i = g (project q r hq i)) :
    FactorsThrough p r hp L := by
  obtain ⟨h, hh⟩ := hg
  refine ⟨h, ?_⟩
  intro i
  calc
    L i = g (project q r hq i) := hvia i
    _ = h (project p q hp (project q r hq i)) :=
      hh (project q r hq i)
    _ = h (project p r hp i) := by rw [project_compose p q r hp hq hpq i]

/-- A physical point of an inner restrictive set follows an actual
    outer orbit phase. This is inherited from the dynamical iterate
    identity; no symbolic phase-routing oracle is assumed. -/
theorem physical_outer_phase_route {α : Type}
    (f : α → α) (outer inner : α → Prop)
    (p : Nat) (hp : 0 < p)
    (hcontain : ∀ x, inner x → outer x)
    (hinvariant : ∀ y, outer y → outer (iterate f p y))
    (x : α) (hx : inner x) (j : Nat) :
    ∃ y, outer y ∧ iterate f j x = iterate f (j % p) y := by
  exact terminal_root_phase_route f outer p j hinvariant x
    (hcontain x hx)

/-- A three-level nested physical return yields *both* outer and middle
    phase routes with the correct physical iterate, with no relabeling
    axiom. This does not assert that the witnesses are unique, or that
    they describe accesses or sheets. -/
theorem physical_three_level_routes {α : Type}
    (f : α → α) (outer middle inner : α → Prop)
    (p q : Nat) (hp : 0 < p) (hq : 0 < q)
    (hinner : ∀ x, inner x → middle x)
    (hmiddle : ∀ x, middle x → outer x)
    (hinvOuter : ∀ x, outer x → outer (iterate f p x))
    (hinvMiddle : ∀ x, middle x → middle (iterate f q x))
    (x : α) (hx : inner x) (j : Nat) :
    (∃ y, outer y ∧ iterate f j x = iterate f (j % p) y) ∧
    (∃ z, middle z ∧ iterate f j x = iterate f (j % q) z) := by
  constructor
  · exact physical_outer_phase_route f outer inner p hp
      (fun y hy => hmiddle y (hinner y hy)) hinvOuter x hx j
  · exact physical_outer_phase_route f middle inner q hq
      hinner hinvMiddle x hx j

/-- If a proposed return to the base is disjoint from all nonzero
    images of the outer root, its time must be aligned modulo p. -/
theorem actual_return_requires_outer_alignment {α : Type}
    (f : α → α) (root base : α → Prop)
    (p time : Nat) (hp : 0 < p)
    (hinv : ∀ x, root x → root (iterate f p x))
    (hdisjoint : ∀ r, 0 < r → r < p →
      ∀ y, root y → ¬ base (iterate f r y))
    (x : α) (hx : root x)
    (hreturn : base (iterate f time x)) :
    time % p = 0 := by
  exact no_deep_root_return_without_phase_alignment
    f root base p time hp hinv hdisjoint ⟨x, hx, hreturn⟩

end LoopsFormal.PhaseTower
