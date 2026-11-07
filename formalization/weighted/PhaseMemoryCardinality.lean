import Mathlib
import PhaseMemoryGeneral

/-!
# Finite-cardinality consequence of the all-period clock-memory theorem

The core Lean theorem gives an *injection* of Fin k into an arbitrary
memory type if the augmented coarse clock preserves the full future of
one Boolean sensor. Mathlib's finite-cardinality API converts the
injection into the numeric sharp lower bound k ≤ card M.

This does not identify a physical complex-dynamical sheet system with
the finite symbolic clock.
-/

namespace LoopsFormal.PhaseMemory

open LoopsFormal.PhaseTower
open LoopsFormal.PhaseFuture

/-- For any positive p,k and any finite memory alphabet M, preserving
the future zero-sensor across a p*k-to-p quotient requires at least k
memory states. No augmented transition or total order on M is assumed. -/
theorem finite_memory_card_ge
    {M : Type} [Fintype M]
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (mem : Phase (p * k) → M)
    (hfuture : PreservesFuture
      (fun i : Phase (p * k) => (project p (p * k) hp i, mem i))
      (clockNext (p * k) (Nat.mul_pos hp hk))
      (zeroSensor (p * k))) :
    k ≤ Fintype.card M := by
  let r : Phase p := ⟨0, hp⟩
  have hinj : Function.Injective
      (fun a : Phase k => mem (fiber p k hp r a)) :=
    zeroSensor_future_requires_memory_everywhere p k hp hk mem hfuture r
  have hcard := Fintype.card_le_of_injective
    (fun a : Phase k => mem (fiber p k hp r a)) hinj
  simpa using hcard

/-- A strictly smaller finite alphabet is impossible, even if all
its memory labels depend arbitrarily on the fine phase. -/
theorem no_small_fin_memory
    (p k r : ℕ) (hp : 0 < p) (hk : 0 < k) (hr : r < k)
    (mem : Phase (p * k) → Phase r) :
    ¬ PreservesFuture
      (fun i : Phase (p * k) => (project p (p * k) hp i, mem i))
      (clockNext (p * k) (Nat.mul_pos hp hk))
      (zeroSensor (p * k)) := by
  intro hfuture
  have hcard := finite_memory_card_ge p k hp hk mem hfuture
  have hle : k ≤ r := by simpa using hcard
  omega

/-- The lower bound multiplies through a tower: reducing from
p*m*n phases straight to p phases requires at least m*n states. -/
theorem tower_memory_card_ge
    {M : Type} [Fintype M]
    (p m n : ℕ) (hp : 0 < p) (hm : 0 < m) (hn : 0 < n)
    (mem : Phase (p * (m * n)) → M)
    (hfuture : PreservesFuture
      (fun i : Phase (p * (m * n)) =>
        (project p (p * (m * n)) hp i, mem i))
      (clockNext (p * (m * n)) (Nat.mul_pos hp (Nat.mul_pos hm hn)))
      (zeroSensor (p * (m * n)))) :
    m * n ≤ Fintype.card M := by
  exact finite_memory_card_ge p (m * n) hp (Nat.mul_pos hm hn)
    mem hfuture

/-- The lower bound is attained by the explicit memory alphabet
Fin k, which in fact reconstructs *all* observables at all times. -/
theorem exactly_k_memory_states_suffice
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k) :
    ∃ mem : Phase (p * k) → Phase k,
      PreservesFuture
        (fun i : Phase (p * k) =>
          (project p (p * k) hp i, mem i))
        (clockNext (p * k) (Nat.mul_pos hp hk))
        (zeroSensor (p * k)) := by
  refine ⟨memoryDigit p k hp, ?_⟩
  intro i j hij
  have h : i = j := address_injective p k hp hij
  subst j
  exact futureEqual_refl _ _ i

#print axioms finite_memory_card_ge
#print axioms no_small_fin_memory
#print axioms tower_memory_card_ge
#print axioms exactly_k_memory_states_suffice

end LoopsFormal.PhaseMemory
