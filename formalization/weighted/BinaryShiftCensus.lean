import CompactBinaryCoding
import Mathlib.Data.Nat.Periodic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Periodic orbit census for the full one-sided binary shift

The fixed points of the n-fold shift are exactly repetitions of binary words
of length n. Every finite prefix has such a periodic extension, and every
positive length occurs as an exact least period.
-/

namespace LoopsBinaryShiftCensus

open Function LoopsCompactBinaryCoding Filter Topology

/-- Iterating the shift reads the same sequence at the translated index. -/
theorem shift_iterate_apply (a : ℕ → Fin 2) (n k : ℕ) :
    shift^[n] a k = a (k+n) := by
  induction n generalizing a k with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [shift, Nat.add_assoc]

/-- The finite word repeated indefinitely. -/
def repeatWord {n : ℕ} (hn : 0 < n) (w : Fin n → Fin 2) : ℕ → Fin 2 :=
  fun k => w ⟨k % n, Nat.mod_lt k hn⟩

theorem repeatWord_fixed {n : ℕ} (hn : 0 < n) (w : Fin n → Fin 2) :
    shift^[n] (repeatWord hn w) = repeatWord hn w := by
  funext k
  rw [shift_iterate_apply]
  simp only [repeatWord]
  congr 1
  exact Fin.ext (Nat.add_mod_right k n)

theorem repeatWord_prefix {n : ℕ} (hn : 0 < n) (w : Fin n → Fin 2)
    (k : Fin n) : repeatWord hn w k = w k := by
  simp [repeatWord, Nat.mod_eq_of_lt k.isLt]

/-- Restricting to the first n entries is an exact equivalence between
fixed points of the n-fold shift and words of length n. -/
def fixedWordEquiv (n : ℕ) (hn : 0 < n) :
    {a : ℕ → Fin 2 // shift^[n] a = a} ≃ (Fin n → Fin 2) where
  toFun a i := a.val i
  invFun w := ⟨repeatWord hn w, repeatWord_fixed hn w⟩
  left_inv a := by
    apply Subtype.ext
    funext k
    have hp : Periodic a.val n := by
      intro j
      simpa only [shift_iterate_apply] using congrFun a.property j
    exact hp.map_mod_nat k
  right_inv w := by
    funext k
    exact repeatWord_prefix hn w k

/-- The full binary shift has exactly 2^n points fixed by its n-th iterate. -/
theorem fixed_point_card (n : ℕ) (hn : 0 < n) :
    Nat.card {a : ℕ → Fin 2 // shift^[n] a = a} = 2^n := by
  rw [Nat.card_congr (fixedWordEquiv n hn), Nat.card_fun, Nat.card_fin, Nat.card_fin]

/-- Every prescribed finite prefix extends to a point fixed by the shift
iterate of the same positive length. -/
theorem periodic_extension (a : ℕ → Fin 2) (n : ℕ) (hn : 0 < n) :
    ∃ b : ℕ → Fin 2, shift^[n] b = b ∧ ∀ k < n, b k = a k := by
  refine ⟨repeatWord hn (fun i => a i), repeatWord_fixed hn _, ?_⟩
  intro k hk
  exact repeatWord_prefix hn (fun i => a i) ⟨k, hk⟩

/-- Repetition of successively longer prefixes converges to the original
address in the product topology. -/
theorem periodic_approximants_tendsto (a : ℕ → Fin 2) :
    Tendsto (fun n : ℕ => repeatWord (Nat.succ_pos n) (fun i => a i))
      atTop (𝓝 a) := by
  apply tendsto_pi_nhds.2
  intro k
  apply Filter.Tendsto.congr' (f₁ := fun _ : ℕ => a k) ?_ tendsto_const_nhds
  refine eventually_atTop.2 ⟨k, ?_⟩
  intro n hn
  exact (repeatWord_prefix (Nat.succ_pos n) (fun i => a i)
    ⟨k, by omega⟩).symm

/-- Periodic addresses are dense in the full binary sequence space. -/
theorem periodic_points_dense :
    Dense {a : ℕ → Fin 2 | ∃ n : ℕ, 0 < n ∧ shift^[n] a = a} := by
  intro a
  apply mem_closure_of_tendsto (periodic_approximants_tendsto a)
  exact Filter.Eventually.of_forall fun n =>
    ⟨n+1, Nat.succ_pos n, repeatWord_fixed (Nat.succ_pos n) _⟩

/-- One marked entry in each block supplies a point with least period n. -/
theorem exact_period_exists (n : ℕ) (hn : 0 < n) :
    ∃ a : ℕ → Fin 2, shift^[n] a = a ∧
      ∀ m, 0 < m → m < n → shift^[m] a ≠ a := by
  let w : Fin n → Fin 2 := fun i => if i.val = 0 then 1 else 0
  refine ⟨repeatWord hn w, repeatWord_fixed hn w, ?_⟩
  intro m hm hmn h
  have he := congrFun h 0
  rw [shift_iterate_apply] at he
  simp [repeatWord, w, Nat.mod_eq_of_lt hmn, Nat.ne_of_gt hm] at he

end LoopsBinaryShiftCensus
