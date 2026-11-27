import CriticalPhaseCuts
import Mathlib.Data.Fintype.Card

/-!
# Exact phase memory at critical encounters

Each nonempty connected regular excursion carries one independent Boolean
phase. The excursion sets are open in the original time space, not supplied
with a disconnected topology. Arbitrarily many accumulating critical times
are allowed: the equivalence below has no finiteness assumption on its index.

Combining this census with the physical return-lift classification counts
actual continuous lifts, including those that change deck phase at branch
value encounters. Anchoring one regular excursion removes precisely one bit.
-/

namespace LoopsCriticalPhase

open Set Function

noncomputable section

variable {X ι : Type*} [TopologicalSpace X]

/-- A phase is constant throughout a connected regular excursion. -/
theorem PhaseCut.constant_on_preconnected {R S : Set X} (P : PhaseCut R)
    (hS : IsPreconnected S) (hSR : S ⊆ R)
    {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    x ∈ P.carrier ↔ y ∈ P.carrier := by
  have hcover : S ⊆ P.carrier ∪ (R \ P.carrier) := by
    intro z hz
    by_cases hp : z ∈ P.carrier
    · exact Or.inl hp
    · exact Or.inr ⟨hSR hz, hp⟩
  constructor
  · intro hxp
    by_contra hyp
    obtain ⟨z, _, hzp, hzn⟩ := hS P.carrier (R \ P.carrier)
      P.open_true P.open_false hcover ⟨x, hx, hxp⟩ ⟨y, hy, hSR hy, hyp⟩
    exact hzn.2 hzp
  · intro hyp
    by_contra hxp
    obtain ⟨z, _, hzp, hzn⟩ := hS P.carrier (R \ P.carrier)
      P.open_true P.open_false hcover ⟨y, hy, hyp⟩ ⟨x, hx, hSR hx, hxp⟩
    exact hzn.2 hzp

/-- Every Boolean assignment to the actual open connected excursions
corresponds to exactly one phase cut, and the correspondence records the
phase at every point. Finiteness of the excursion inventory is not needed. -/
theorem phaseCut_excursion_equiv (R : Set X) (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i))
    (hconn : ∀ i, IsPreconnected (U i))
    (hne : ∀ i, (U i).Nonempty)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcover : R = ⋃ i, U i) :
    ∃ e : PhaseCut R ≃ (ι → Bool),
      ∀ P i x, x ∈ U i → (e P i = true ↔ x ∈ P.carrier) := by
  classical
  let point : ι → X := fun i => (hne i).choose
  have hp (i : ι) : point i ∈ U i := (hne i).choose_spec
  have hUR (i : ι) : U i ⊆ R := by
    rw [hcover]
    exact subset_iUnion U i
  have unique_cell {i j : ι} {x : X} (hi : x ∈ U i) (hj : x ∈ U j) : i = j := by
    by_contra hij
    exact Set.disjoint_left.mp (hdis hij) hi hj
  let selected : (ι → Bool) → Set X := fun s => ⋃ i, ⋃ (_ : s i = true), U i
  have hselected (s : ι → Bool) (x : X) :
      x ∈ selected s ↔ ∃ i, s i = true ∧ x ∈ U i := by
    simp only [selected, mem_iUnion, exists_prop]
  have hselected_open (s : ι → Bool) : IsOpen (selected s) :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => hopen i
  have hselected_sub (s : ι → Bool) : selected s ⊆ R := by
    intro x hx
    obtain ⟨i, _, hi⟩ := (hselected s x).mp hx
    exact hUR i hi
  have hselected_compl (s : ι → Bool) :
      R \ selected s = selected (fun i => !(s i)) := by
    ext x
    constructor
    · rintro ⟨hxR, hx⟩
      rw [hcover] at hxR
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxR
      have hn : s i ≠ true := fun hs => hx ((hselected s x).mpr ⟨i, hs, hi⟩)
      apply (hselected _ x).mpr
      refine ⟨i, ?_, hi⟩
      cases hs : s i with
      | false => simp [hs]
      | true => exact (hn hs).elim
    · intro hx
      obtain ⟨i, hs, hi⟩ := (hselected _ x).mp hx
      refine ⟨hUR i hi, ?_⟩
      intro hx'
      obtain ⟨j, ht, hj⟩ := (hselected s x).mp hx'
      have hij := unique_cell hi hj
      subst j
      simp [ht] at hs
  let decode : (ι → Bool) → PhaseCut R := fun s =>
    { carrier := selected s
      subset_regular := hselected_sub s
      open_true := hselected_open s
      open_false := by rw [hselected_compl]; exact hselected_open _ }
  let encode : PhaseCut R → (ι → Bool) := fun P i => decide (point i ∈ P.carrier)
  have hencode (P : PhaseCut R) (i : ι) :
      encode P i = true ↔ point i ∈ P.carrier := by simp [encode]
  have hdecode (s : ι → Bool) (i : ι) :
      point i ∈ (decode s).carrier ↔ s i = true := by
    change point i ∈ selected s ↔ s i = true
    constructor
    · intro h
      obtain ⟨j, hj, hpj⟩ := (hselected s (point i)).mp h
      have hji := unique_cell hpj (hp i)
      subst j
      exact hj
    · intro h
      exact (hselected s (point i)).mpr ⟨i, h, hp i⟩
  have left_inv : LeftInverse decode encode := by
    intro P
    apply PhaseCut.ext
    ext x
    change x ∈ selected (encode P) ↔ x ∈ P.carrier
    constructor
    · intro h
      obtain ⟨i, hi, hx⟩ := (hselected (encode P) x).mp h
      exact (P.constant_on_preconnected (hconn i) (hUR i) (hp i) hx).mp
        ((hencode P i).mp hi)
    · intro hx
      have hxR := P.subset_regular hx
      rw [hcover] at hxR
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxR
      apply (hselected (encode P) x).mpr
      refine ⟨i, (hencode P i).mpr ?_, hi⟩
      exact (P.constant_on_preconnected (hconn i) (hUR i) hi (hp i)).mp hx
  have right_inv : RightInverse decode encode := by
    intro s
    funext i
    cases hs : s i with
    | false =>
      have hm : point i ∉ (decode s).carrier := by rw [hdecode]; simp [hs]
      simp [encode, hm, hs]
    | true =>
      have hm : point i ∈ (decode s).carrier := (hdecode s i).mpr hs
      simp [encode, hm, hs]
  let e : PhaseCut R ≃ (ι → Bool) :=
    { toFun := encode, invFun := decode, left_inv := left_inv, right_inv := right_inv }
  refine ⟨e, ?_⟩
  intro P i x hx
  change encode P i = true ↔ x ∈ P.carrier
  exact (hencode P i).trans
    (P.constant_on_preconnected (hconn i) (hUR i) (hp i) hx)

/-- Exactly N nonempty connected regular excursions create 2^N possible
continuous phase choices; critical encounters do not erase earlier choices. -/
theorem phaseCut_excursion_count [Fintype ι] (R : Set X) (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i))
    (hconn : ∀ i, IsPreconnected (U i))
    (hne : ∀ i, (U i).Nonempty)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcover : R = ⋃ i, U i) :
    Nat.card (PhaseCut R) = 2 ^ Fintype.card ι := by
  classical
  obtain ⟨e, _⟩ := phaseCut_excursion_equiv R U hopen hconn hne hdis hcover
  letI : Fintype (PhaseCut R) := Fintype.ofEquiv (ι → Bool) e.symm
  calc
    Nat.card (PhaseCut R) = Fintype.card (ι → Bool) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr e
    _ = 2 ^ Fintype.card ι := by simp

/-- Fixing the phase at one regular time fixes its entire excursion and
leaves one independent bit on each of the other N excursions. In particular,
an anchored path may still have exponentially many full critical-crossing lifts. -/
theorem phaseCut_anchored_excursion_count (n : ℕ) (R : Set X)
    (U : Fin (n+1) → Set X)
    (hopen : ∀ i, IsOpen (U i))
    (hconn : ∀ i, IsPreconnected (U i))
    (hne : ∀ i, (U i).Nonempty)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcover : R = ⋃ i, U i) (x : X) (hx : x ∈ U 0) :
    Nat.card {P : PhaseCut R // x ∈ P.carrier} = 2 ^ n := by
  obtain ⟨e, he⟩ := phaseCut_excursion_equiv R U hopen hconn hne hdis hcover
  let E : {P : PhaseCut R // x ∈ P.carrier} ≃ (Fin n → Bool) :=
    { toFun := fun P i => e P.val i.succ
      invFun := fun s =>
        ⟨e.symm (Fin.cases true s), by
          apply (he (e.symm (Fin.cases true s)) 0 x hx).mp
          rw [e.apply_symm_apply]
          rfl⟩
      left_inv := by
        intro P
        apply Subtype.ext
        apply e.injective
        change e (e.symm (Fin.cases true (fun i => e P.val i.succ))) = e P.val
        rw [e.apply_symm_apply]
        funext i
        refine Fin.cases ?_ ?_ i
        · exact ((he P.val 0 x hx).mpr P.property).symm
        · intro j
          rfl
      right_inv := by
        intro s
        funext i
        change e (e.symm (Fin.cases true s)) i.succ = s i
        rw [e.apply_symm_apply]
        rfl }
  letI : Fintype {P : PhaseCut R // x ∈ P.carrier} :=
    Fintype.ofEquiv (Fin n → Bool) E.symm
  calc
    Nat.card {P : PhaseCut R // x ∈ P.carrier} = Fintype.card (Fin n → Bool) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr E
    _ = 2 ^ n := by simp

end

end LoopsCriticalPhase
