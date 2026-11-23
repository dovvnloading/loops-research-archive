import Mathlib

/-!
# Paper 3: exact finite-packet closure and obstruction logic

This file extracts the checkable order-theoretic core of Paper 3,
"Protected planar carriers", especially:
* the filled-hull absorption/order-independence lemma (Section E),
* persistent packet-merger, escape and port-loss witnesses,
* the obstruction to a canonical least carrier,
* preservation of closure under intersections of fixed hulls.

The actual planar *full hull* is a closure operation, but identifying
these sets with full compact continua, proving component/prime-end
port survival, and proving connectedness of a limiting intersection
require topology beyond this module. No geometric or analytic premise
is silently inferred from the abstract finite certificates.
-/

namespace LoopsFormal.ProtectedCarriers

variable {α : Type*}

/-- The three exact laws of a hull/fill operation. In the planar
application, the hull fills bounded complementary components. -/
structure Fullifier (α : Type*) where
  hull : Set α → Set α
  extensive : ∀ S, S ⊆ hull S
  monotone : ∀ ⦃S T : Set α⦄, S ⊆ T → hull S ⊆ hull T
  idempotent : ∀ S, hull (hull S) = hull S

/-- Filling before adjoining a new packet piece gives exactly the
same result as first adjoining the piece and filling once. -/
theorem fill_absorption (F : Fullifier α) (A B : Set α) :
    F.hull (F.hull A ∪ B) = F.hull (A ∪ B) := by
  apply Set.Subset.antisymm
  · have h : F.hull A ∪ B ⊆ F.hull (A ∪ B) := by
      intro x hx
      rcases hx with hx | hx
      · exact (F.monotone (Set.subset_union_left)) hx
      · exact (F.extensive (A ∪ B)) (Or.inr hx)
    calc
      F.hull (F.hull A ∪ B) ⊆ F.hull (F.hull (A ∪ B)) :=
        F.monotone h
      _ = F.hull (A ∪ B) := F.idempotent _
  · apply F.monotone
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl ((F.extensive A) hx)
    · exact Or.inr hx

theorem fill_absorption_right (F : Fullifier α) (A B : Set α) :
    F.hull (A ∪ F.hull B) = F.hull (A ∪ B) := by
  calc
    F.hull (A ∪ F.hull B) =
        F.hull (F.hull B ∪ A) := by rw [Set.union_comm]
    _ = F.hull (B ∪ A) := fill_absorption F B A
    _ = F.hull (A ∪ B) := by rw [Set.union_comm]

/-- The simplest nontrivial order-independence certificate. -/
theorem two_piece_fill_order_independent (F : Fullifier α)
    (A B : Set α) :
    F.hull (F.hull A ∪ B) = F.hull (F.hull B ∪ A) := by
  calc
    F.hull (F.hull A ∪ B) = F.hull (A ∪ B) :=
      fill_absorption F A B
    _ = F.hull (B ∪ A) := by rw [Set.union_comm]
    _ = F.hull (F.hull B ∪ A) :=
      (fill_absorption F B A).symm

/-- The underlying union of all pieces of a fixed typed packet. -/
def packetUnion (pieces : List (Set α)) : Set α :=
  {x | ∃ S ∈ pieces, x ∈ S}

@[simp] theorem packetUnion_nil :
    packetUnion ([] : List (Set α)) = ∅ := by
  ext x
  simp [packetUnion]

theorem packetUnion_cons (S : Set α) (pieces : List (Set α)) :
    packetUnion (S :: pieces) = S ∪ packetUnion pieces := by
  ext x
  constructor
  · rintro ⟨T, hT, hx⟩
    rcases List.mem_cons.mp hT with h | h
    · subst T
      exact Or.inl hx
    · exact Or.inr ⟨T, h, hx⟩
  · rintro (hx | ⟨T, hT, hx⟩)
    · exact ⟨S, by simp, hx⟩
    · exact ⟨T, by simp [hT], hx⟩

/-- An incremental packet completion, intentionally filling after
each added piece, in the order determined by the list. -/
def complete (F : Fullifier α) : List (Set α) → Set α
  | [] => F.hull ∅
  | S :: rest => F.hull (complete F rest ∪ S)

/-- The full result is exactly the one-shot hull of all the pieces:
no hidden dependence on intermediate filling choices. -/
theorem complete_eq_hull_union (F : Fullifier α)
    (pieces : List (Set α)) :
    complete F pieces = F.hull (packetUnion pieces) := by
  induction pieces with
  | nil => simp only [complete, packetUnion_nil]
  | cons S rest ih =>
    calc
      complete F (S :: rest) =
          F.hull (F.hull (packetUnion rest) ∪ S) := by
            simp only [complete, ih]
      _ = F.hull (packetUnion rest ∪ S) :=
        fill_absorption F _ _
      _ = F.hull (packetUnion (S :: rest)) := by
        rw [packetUnion_cons, Set.union_comm S (packetUnion rest)]

/-- Reordering a fixed list of pieces cannot change their union. -/
theorem packetUnion_perm {xs ys : List (Set α)}
    (h : xs.Perm ys) : packetUnion xs = packetUnion ys := by
  ext x
  constructor
  · rintro ⟨S, hS, hx⟩
    exact ⟨S, (h.mem_iff).mp hS, hx⟩
  · rintro ⟨S, hS, hx⟩
    exact ⟨S, (h.mem_iff).mpr hS, hx⟩

/-- The source's fixed-assignment packet completion is independent
of every processing order, including lists with repeated pieces. -/
theorem complete_perm (F : Fullifier α)
    {xs ys : List (Set α)} (h : xs.Perm ys) :
    complete F xs = complete F ys := by
  rw [complete_eq_hull_union, complete_eq_hull_union,
    packetUnion_perm h]

/-- Full hulls form an intersection-closed family. This is only
a hull statement; connectedness of decreasing continua is separate. -/
theorem hull_intersection_fixed (F : Fullifier α) {ι : Type*}
    (S : ι → Set α) (hfixed : ∀ i, F.hull (S i) = S i) :
    F.hull (⋂ i, S i) = ⋂ i, S i := by
  apply Set.Subset.antisymm
  · intro x hx
    apply Set.mem_iInter.mpr
    intro i
    have hsubset : (⋂ j, S j) ⊆ S i := Set.iInter_subset _ i
    have h : x ∈ F.hull (S i) := (F.monotone hsubset) hx
    simpa only [hfixed i] using h
  · exact F.extensive _

/-! ## Persistent negative certificates -/

/-- A merger witness is a point already in two distinct completed
packets. Enlarging either packet cannot repair the merger. -/
theorem packet_merger_persists
    {A B A' B' : Set α}
    (hA : A ⊆ A') (hB : B ⊆ B')
    (hmerge : (A ∩ B).Nonempty) :
    (A' ∩ B').Nonempty := by
  rcases hmerge with ⟨x, hxA, hxB⟩
  exact ⟨x, hA hxA, hB hxB⟩

theorem enlarged_packets_cannot_be_disjoint
    {A B A' B' : Set α}
    (hA : A ⊆ A') (hB : B ⊆ B')
    (hmerge : (A ∩ B).Nonempty) :
    ¬ Disjoint A' B' := by
  intro hdisj
  obtain ⟨x, hxA, hxB⟩ :=
    packet_merger_persists hA hB hmerge
  exact (Set.disjoint_left.mp hdisj) hxA hxB

/-- A piece which has escaped a fixed localization U stays escaped
under every enlargement of the packet. -/
theorem localization_escape_persists
    {U A A' : Set α}
    (hA : A ⊆ A')
    (hescape : ∃ x ∈ A, x ∉ U) :
    ∃ x ∈ A', x ∉ U := by
  obtain ⟨x, hxA, hxU⟩ := hescape
  exact ⟨x, hA hxA, hxU⟩

/-- Every available port in a fixed inventory meets the forbidden set.
The inventory of candidate ports is intentionally frozen. -/
def NoSurvivingPort {P : Type*} (ports : P → Set α)
    (forbidden : Set α) : Prop :=
  ∀ p, ¬ Disjoint (ports p) forbidden

/-- Once all ports are blocked, enlarging the obstacle/forbidden
inventory can never restore a port from the same candidate family. -/
theorem no_surviving_port_persists
    {P : Type*} (ports : P → Set α)
    {Z Z' : Set α} (hZZ' : Z ⊆ Z')
    (hbad : NoSurvivingPort ports Z) :
    NoSurvivingPort ports Z' := by
  intro p hdisj
  apply hbad p
  apply Set.disjoint_left.mpr
  intro x hxP hxZ
  exact (Set.disjoint_left.mp hdisj) hxP (hZZ' hxZ)

/-! ## Least-carrier obstruction -/

/-- A least carrier is included in every admissible carrier containing
the same package; this is stronger than being a minimal carrier. -/
def IsLeastCarrier (Good : Set α → Prop) (package H : Set α) : Prop :=
  Good H ∧ package ⊆ H ∧
    ∀ C, Good C → package ⊆ C → H ⊆ C

/-- Two admissible carriers intersecting *only* in a forbidden
package disprove existence of a least carrier. This is the exact
order-theoretic step of Paper 3's upper/lower semicircle example. -/
theorem no_least_of_two_carriers
    (Good : Set α → Prop) (package A B : Set α)
    (hA : Good A) (hB : Good B)
    (hPA : package ⊆ A) (hPB : package ⊆ B)
    (hinter : A ∩ B = package) (hbad : ¬ Good package) :
    ¬ ∃ H, IsLeastCarrier Good package H := by
  rintro ⟨H, hgood, hPH, hmin⟩
  have hHA : H ⊆ A := hmin A hA hPA
  have hHB : H ⊆ B := hmin B hB hPB
  have hHP : H ⊆ package := by
    rw [← hinter]
    intro x hx
    exact ⟨hHA hx, hHB hx⟩
  have hEq : H = package := Set.Subset.antisymm hHP hPH
  rw [hEq] at hgood
  exact hbad hgood

/-- The four-vertex diamond is a *finite path-skeleton model*, not
a claim that finite discrete sets are plane continua. It isolates
the branching-choice obstruction used by the geometric example. -/
inductive DiamondVertex where
  | left | upper | right | lower
  deriving DecidableEq, Fintype, Repr

def diamondPackage : Set DiamondVertex :=
  fun v => v = .left ∨ v = .right

def diamondUpper : Set DiamondVertex :=
  fun v => v ≠ .lower

def diamondLower : Set DiamondVertex :=
  fun v => v ≠ .upper

/-- In the four-cycle graph a carrier connecting the two endpoints
must choose at least one intermediate vertex. -/
def DiamondConnects (C : Set DiamondVertex) : Prop :=
  DiamondVertex.left ∈ C ∧ DiamondVertex.right ∈ C ∧
    (DiamondVertex.upper ∈ C ∨ DiamondVertex.lower ∈ C)

/-- A machine-checked finite countermodel for "take the least
connected hull" on the two opposite vertices of a diamond graph. -/
theorem diamond_has_no_least_carrier :
    ¬ ∃ H : Set DiamondVertex,
        IsLeastCarrier DiamondConnects diamondPackage H := by
  apply no_least_of_two_carriers DiamondConnects diamondPackage
    diamondUpper diamondLower
  · change (DiamondVertex.left ≠ DiamondVertex.lower) ∧
      (DiamondVertex.right ≠ DiamondVertex.lower) ∧
      (DiamondVertex.upper ≠ DiamondVertex.lower ∨
        DiamondVertex.lower ≠ DiamondVertex.lower)
    decide
  · change (DiamondVertex.left ≠ DiamondVertex.upper) ∧
      (DiamondVertex.right ≠ DiamondVertex.upper) ∧
      (DiamondVertex.upper ≠ DiamondVertex.upper ∨
        DiamondVertex.lower ≠ DiamondVertex.upper)
    decide
  · intro v hv
    change v = DiamondVertex.left ∨ v = DiamondVertex.right at hv
    change v ≠ DiamondVertex.lower
    rcases hv with rfl | rfl <;> decide
  · intro v hv
    change v = DiamondVertex.left ∨ v = DiamondVertex.right at hv
    change v ≠ DiamondVertex.upper
    rcases hv with rfl | rfl <;> decide
  · ext v
    change (v ≠ DiamondVertex.lower ∧ v ≠ DiamondVertex.upper) ↔
      (v = DiamondVertex.left ∨ v = DiamondVertex.right)
    cases v <;> decide
  · intro h
    have hmid := h.2.2
    change
      (DiamondVertex.upper = DiamondVertex.left ∨
        DiamondVertex.upper = DiamondVertex.right) ∨
      (DiamondVertex.lower = DiamondVertex.left ∨
        DiamondVertex.lower = DiamondVertex.right) at hmid
    rcases hmid with (h | h) | (h | h) <;> cases h

#print axioms fill_absorption
#print axioms complete_perm
#print axioms hull_intersection_fixed
#print axioms no_surviving_port_persists
#print axioms diamond_has_no_least_carrier

end LoopsFormal.ProtectedCarriers
