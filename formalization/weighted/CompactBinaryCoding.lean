import Mathlib

/-!
# Binary coding from a compact two-sheet splitting

Every binary sequence is realized by the iterated second-coordinate map
of a homeomorphism to two copies of a compact nonempty space. Compactness
is used on closed finite-prefix cylinders, so no diameter estimate or
uniqueness of the point with a given address is required.
-/

namespace LoopsCompactBinaryCoding

open Set Function

variable {X : Type*} [TopologicalSpace X]

/-- The actual map supplied by the second coordinate of the splitting. -/
def step (e : X ≃ₜ (Fin 2 × X)) (x : X) : X := (e x).2

/-- The label observed along every forward iterate. -/
def address (e : X ≃ₜ (Fin 2 × X)) (x : X) (n : ℕ) : Fin 2 :=
  (e ((step e)^[n] x)).1

/-- The one-sided binary shift. -/
def shift (a : ℕ → Fin 2) (n : ℕ) : Fin 2 := a (n+1)

theorem step_continuous (e : X ≃ₜ (Fin 2 × X)) : Continuous (step e) :=
  continuous_snd.comp e.continuous

/-- Reading all labels at once is continuous for the product topology. -/
theorem address_continuous (e : X ≃ₜ (Fin 2 × X)) : Continuous (address e) := by
  apply continuous_pi
  intro n
  exact continuous_fst.comp (e.continuous.comp ((step_continuous e).iterate n))

theorem address_zero (e : X ≃ₜ (Fin 2 × X)) (x : X) :
    address e x 0 = (e x).1 := rfl

theorem address_succ (e : X ≃ₜ (Fin 2 × X)) (x : X) (n : ℕ) :
    address e x (n+1) = address e (step e x) n := by
  simp only [address, Function.iterate_succ_apply]

/-- The coding intertwines the original step with the full binary shift. -/
theorem address_semiconj (e : X ≃ₜ (Fin 2 × X)) :
    Semiconj (address e) (step e) shift := by
  intro x
  funext n
  exact (address_succ e x n).symm

/-- A cylinder retains exactly the prescribed first `n` labels. -/
def prefixCylinder (e : X ≃ₜ (Fin 2 × X)) (a : ℕ → Fin 2) (n : ℕ) : Set X :=
  {x | ∀ k < n, address e x k = a k}

theorem prefixCylinder_closed (e : X ≃ₜ (Fin 2 × X))
    (a : ℕ → Fin 2) (n : ℕ) : IsClosed (prefixCylinder e a n) := by
  simp only [prefixCylinder, Set.setOf_forall]
  exact isClosed_iInter fun k => isClosed_iInter fun _ =>
    isClosed_eq ((continuous_apply k).comp (address_continuous e)) continuous_const

theorem prefixCylinder_antitone (e : X ≃ₜ (Fin 2 × X))
    (a : ℕ → Fin 2) : Antitone (prefixCylinder e a) := by
  intro m n hmn x hx k hk
  exact hx k (hk.trans_le hmn)

/-- Every finite binary word is realized by repeated actual inverse sections. -/
theorem prefixCylinder_nonempty [Nonempty X] (e : X ≃ₜ (Fin 2 × X))
    (a : ℕ → Fin 2) (n : ℕ) : (prefixCylinder e a n).Nonempty := by
  induction n generalizing a with
  | zero =>
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact ⟨x, fun k hk => False.elim (Nat.not_lt_zero k hk)⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih (shift a)
    refine ⟨e.symm (a 0, y), ?_⟩
    intro k hk
    cases k with
    | zero => simp [address]
    | succ k =>
      have hky : address e y k = a (k+1) := hy k (by omega)
      rw [address_succ]
      simpa [step] using hky

/-- Compactness turns all finite realizations into a realization of every
infinite binary address. No conclusion about individual fiber size is used. -/
theorem address_surjective [CompactSpace X] [Nonempty X]
    (e : X ≃ₜ (Fin 2 × X)) : Surjective (address e) := by
  intro a
  have hm := prefixCylinder_antitone e a
  have hd : Directed (· ⊇ ·) (prefixCylinder e a) := by
    intro m n
    exact ⟨max m n, hm (le_max_left m n), hm (le_max_right m n)⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (prefixCylinder e a) hd (prefixCylinder_nonempty e a)
    (fun n => (prefixCylinder_closed e a n).isCompact) (prefixCylinder_closed e a)
  refine ⟨x, funext fun n => ?_⟩
  exact (mem_iInter.mp hx (n+1)) n (Nat.lt_succ_self n)

/-- A connected component has one binary address, so the continuous coding
descends to the actual connected-component quotient. -/
def componentAddress (e : X ≃ₜ (Fin 2 × X)) :
    ConnectedComponents X → (ℕ → Fin 2) :=
  (address_continuous e).connectedComponentsLift

theorem componentAddress_continuous (e : X ≃ₜ (Fin 2 × X)) :
    Continuous (componentAddress e) :=
  (address_continuous e).connectedComponentsLift_continuous

theorem componentAddress_mk (e : X ≃ₜ (Fin 2 × X)) (x : X) :
    componentAddress e (ConnectedComponents.mk x) = address e x := rfl

/-- Every address is already realized at the level of actual components. -/
theorem componentAddress_surjective [CompactSpace X] [Nonempty X]
    (e : X ≃ₜ (Fin 2 × X)) : Surjective (componentAddress e) := by
  intro a
  obtain ⟨x, hx⟩ := address_surjective e a
  exact ⟨ConnectedComponents.mk x, hx⟩

/-- Distinct binary sequences select distinct actual components. This is
an explicit cardinal lower bound, stronger than uncountability alone. -/
theorem componentAddress_section [CompactSpace X] [Nonempty X]
    (e : X ≃ₜ (Fin 2 × X)) :
    ∃ s : (ℕ → Fin 2) ↪ ConnectedComponents X,
      ∀ a, componentAddress e (s a) = a := by
  let h := componentAddress_surjective e
  refine ⟨⟨surjInv h, injective_surjInv h⟩, ?_⟩
  intro a
  exact surjInv_eq h a

private theorem binary_sequences_uncountable : Uncountable (ℕ → Fin 2) := by
  apply uncountable_iff_forall_not_surjective.mpr
  intro f hf
  obtain ⟨n, hn⟩ := hf (fun k => if f k k = 0 then 1 else 0)
  have he := congrFun hn n
  by_cases h : f n n = 0
  · simp [h] at he
  · simp only [if_neg h] at he
    exact h he

/-- A compact nonempty two-sheet self-splitting has uncountably many
actual connected components. This does not identify any component with a point. -/
theorem component_uncountable [CompactSpace X] [Nonempty X]
    (e : X ≃ₜ (Fin 2 × X)) : Uncountable (ConnectedComponents X) := by
  letI : Uncountable (ℕ → Fin 2) := binary_sequences_uncountable
  exact (componentAddress_surjective e).uncountable

/-- The induced dynamics on actual components. -/
def componentStep (e : X ≃ₜ (Fin 2 × X)) : ConnectedComponents X → ConnectedComponents X :=
  (step_continuous e).connectedComponentsMap

/-- The component coding also intertwines its induced dynamics with the shift. -/
theorem componentAddress_semiconj (e : X ≃ₜ (Fin 2 × X)) :
    Semiconj (componentAddress e) (componentStep e) shift := by
  intro q
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
  exact address_semiconj e x

end LoopsCompactBinaryCoding
