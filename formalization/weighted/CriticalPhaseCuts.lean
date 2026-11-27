import Mathlib

/-!
# Continuous choices through arbitrary collisions

The regular set is where the two continuous branches are different.
Each relatively clopen phase choice on that open set extends continuously
across every collision, including accumulation points of collisions.
The extension and extraction operations are inverse to each other.
-/

namespace LoopsCriticalPhase

open Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A phase is allowed to change only through the omitted collision set. -/
structure PhaseCut (R : Set X) where
  carrier : Set X
  subset_regular : carrier ⊆ R
  open_true : IsOpen carrier
  open_false : IsOpen (R \ carrier)

@[ext]
theorem PhaseCut.ext {R : Set X} {S T : PhaseCut R}
    (h : S.carrier = T.carrier) : S = T := by
  cases S
  cases T
  cases h
  rfl

/-- Transport the phase data across an equality of regular loci. -/
def phaseCutCongr {R S : Set X} (h : R = S) : PhaseCut R ≃ PhaseCut S := by
  cases h
  exact Equiv.refl _

@[simp]
theorem phaseCutCongr_carrier {R S : Set X} (h : R = S) (P : PhaseCut R) :
    (phaseCutCongr h P).carrier = P.carrier := by
  cases h
  rfl

/-- The true phase selects the first branch. -/
noncomputable def phaseSelect (f g : X → Y) (S : Set X) : X → Y := by
  classical
  exact fun x => if x ∈ S then f x else g x

@[simp]
theorem phaseSelect_of_mem (f g : X → Y) (S : Set X) {x : X}
    (hx : x ∈ S) : phaseSelect f g S x = f x := by
  classical
  simp [phaseSelect, hx]

@[simp]
theorem phaseSelect_of_not_mem (f g : X → Y) (S : Set X) {x : X}
    (hx : x ∉ S) : phaseSelect f g S x = g x := by
  classical
  simp [phaseSelect, hx]

theorem phaseSelect_choice (f g : X → Y) (S : Set X) (x : X) :
    phaseSelect f g S x = f x ∨ phaseSelect f g S x = g x := by
  classical
  by_cases hx : x ∈ S
  · exact Or.inl (phaseSelect_of_mem f g S hx)
  · exact Or.inr (phaseSelect_of_not_mem f g S hx)

/-- No finiteness, isolation, or local finiteness of collisions is needed. -/
theorem continuous_phaseSelect (f g : X → Y) (S : Set X)
    (hf : Continuous f) (hg : Continuous g) (hS : IsOpen S)
    (hother : IsOpen ({x | f x ≠ g x} \ S)) :
    Continuous (phaseSelect f g S) := by
  classical
  have hclosure : closure S ⊆ ({x | f x ≠ g x} \ S)ᶜ :=
    closure_minimal (fun _ hx h => h.2 hx) hother.isClosed_compl
  have hboundary : ∀ x ∈ frontier S, f x = g x := by
    intro x hx
    by_contra hne
    have hxnot : x ∉ S := by
      simpa only [hS.interior_eq] using hx.2
    exact hclosure hx.1 ⟨hne, hxnot⟩
  change Continuous (fun x => if x ∈ S then f x else g x)
  exact Continuous.if hboundary hf hg

variable [T2Space Y]

/-- The first-branch locus is open in the whole parameter space after
removing the collision points. -/
theorem choice_true_open (f g h : X → Y)
    (hg : Continuous g) (hh : Continuous h)
    (hchoice : ∀ x, h x = f x ∨ h x = g x) :
    IsOpen {x | h x = f x ∧ f x ≠ g x} := by
  have heq : {x | h x = f x ∧ f x ≠ g x} = {x | h x ≠ g x} := by
    ext x
    constructor
    · rintro ⟨hxf, hfg⟩ hxg
      exact hfg (hxf.symm.trans hxg)
    · intro hxg
      have hxf : h x = f x := (hchoice x).resolve_right hxg
      exact ⟨hxf, fun hfg => hxg (hxf.trans hfg)⟩
  rw [heq]
  exact isOpen_ne hh hg

theorem choice_false_open (f g h : X → Y)
    (hf : Continuous f) (hh : Continuous h)
    (hchoice : ∀ x, h x = f x ∨ h x = g x) :
    IsOpen ({x | f x ≠ g x} \ {x | h x = f x ∧ f x ≠ g x}) := by
  have heq : ({x | f x ≠ g x} \ {x | h x = f x ∧ f x ≠ g x}) =
      {x | h x ≠ f x} := by
    ext x
    constructor
    · rintro ⟨hfg, hx⟩ hxf
      exact hx ⟨hxf, hfg⟩
    · intro hxf
      have hxg : h x = g x := (hchoice x).resolve_left hxf
      exact ⟨fun hfg => hxf (hxg.trans hfg.symm), fun hx => hxf hx.1⟩
  rw [heq]
  exact isOpen_ne hh hf

/-- Extracting the phase of a selection recovers exactly the chosen set. -/
theorem phaseSelect_region (f g : X → Y) (S : Set X)
    (hS : S ⊆ {x | f x ≠ g x}) :
    {x | phaseSelect f g S x = f x ∧ f x ≠ g x} = S := by
  classical
  ext x
  constructor
  · rintro ⟨heq, hne⟩
    by_contra hx
    rw [phaseSelect_of_not_mem f g S hx] at heq
    exact hne heq.symm
  · intro hx
    exact ⟨phaseSelect_of_mem f g S hx, hS hx⟩

/-- Every pointwise choice is recovered from its regular first-branch locus. -/
theorem phaseSelect_reconstruct (f g h : X → Y)
    (hchoice : ∀ x, h x = f x ∨ h x = g x) :
    phaseSelect f g {x | h x = f x ∧ f x ≠ g x} = h := by
  classical
  funext x
  by_cases hx : h x = f x ∧ f x ≠ g x
  · rw [phaseSelect_of_mem f g _ hx]
    exact hx.1.symm
  · rw [phaseSelect_of_not_mem f g _ hx]
    rcases hchoice x with hxf | hxg
    · by_cases hfg : f x = g x
      · exact hfg.symm.trans hxf.symm
      · exact False.elim (hx ⟨hxf, hfg⟩)
    · exact hxg.symm

/-- The continuous map selected by a phase cut. -/
noncomputable def phaseChoiceMap (f g : C(X, Y))
    (S : PhaseCut {x | f x ≠ g x}) : C(X, Y) where
  toFun := phaseSelect f g S.carrier
  continuous_toFun := continuous_phaseSelect f g S.carrier
    f.continuous g.continuous S.open_true S.open_false

/-- The unique regular phase carried by a continuous pointwise choice. -/
def phaseCutOfChoice (f g h : C(X, Y))
    (hchoice : ∀ x, h x = f x ∨ h x = g x) :
    PhaseCut {x | f x ≠ g x} where
  carrier := {x | h x = f x ∧ f x ≠ g x}
  subset_regular := fun _ hx => hx.2
  open_true := choice_true_open f g h g.continuous h.continuous hchoice
  open_false := choice_false_open f g h f.continuous h.continuous hchoice

/-- Complete classification, including arbitrary closed collision sets.
Neither connectedness of the regular set nor finiteness of its components
is a hypothesis. -/
noncomputable def phaseChoiceEquiv (f g : C(X, Y)) :
    {h : C(X, Y) // ∀ x, h x = f x ∨ h x = g x} ≃
      PhaseCut {x | f x ≠ g x} where
  toFun := fun h => phaseCutOfChoice f g h.1 h.2
  invFun := fun S => ⟨phaseChoiceMap f g S,
    fun x => phaseSelect_choice f g S.carrier x⟩
  left_inv := by
    intro h
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact congrFun (phaseSelect_reconstruct f g h.1 h.2) x
  right_inv := by
    intro S
    apply PhaseCut.ext
    exact phaseSelect_region f g S.carrier S.subset_regular

@[simp]
theorem phaseChoiceEquiv_carrier (f g : C(X, Y))
    (h : {h : C(X, Y) // ∀ x, h x = f x ∨ h x = g x}) :
    (phaseChoiceEquiv f g h).carrier = {x | h.1 x = f x ∧ f x ≠ g x} := rfl

@[simp]
theorem phaseChoiceEquiv_symm_apply (f g : C(X, Y))
    (S : PhaseCut {x | f x ≠ g x}) (x : X) :
    ((phaseChoiceEquiv f g).symm S).1 x = phaseSelect f g S.carrier x := rfl

end LoopsCriticalPhase
