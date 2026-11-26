import CompactBinaryCoding

/-!
# Exact periodic census and dense periodic addresses

The one-sided binary shift has exactly `2^n` points fixed by its positive
`n`-th iterate. Periodic addresses are dense in the product topology.
These statements will be transported to actual quadratic components by
the component conjugacy, rather than inferred from a surjective factor.
-/

namespace LoopsBinaryShiftPeriodic

open Set Function LoopsCompactBinaryCoding

/-- Iteration of the one-sided shift discards precisely the first `n` symbols. -/
theorem shift_iterate_apply (a : ℕ → Fin 2) (n k : ℕ) :
    (shift^[n] a) k = a (k+n) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (shift^[n] a) (k+1) = a (k+(n+1))
    rw [ih]
    congr 1
    omega

/-- A shift-periodic address is exactly an ordinary periodic function on naturals. -/
theorem shift_periodic_iff (a : ℕ → Fin 2) (n : ℕ) :
    IsPeriodicPt shift n a ↔ Periodic a n := by
  constructor
  · intro h k
    have he := congrFun h.eq k
    simpa only [shift_iterate_apply] using he
  · intro h
    apply funext
    intro k
    rw [shift_iterate_apply]
    exact h k

/-- Repeat a finite nonempty binary word indefinitely. -/
def repeatWord {n : ℕ} (hn : 0 < n) (w : Fin n → Fin 2) : ℕ → Fin 2 :=
  fun k => w ⟨k % n, Nat.mod_lt k hn⟩

theorem repeatWord_periodic {n : ℕ} (hn : 0 < n) (w : Fin n → Fin 2) :
    IsPeriodicPt shift n (repeatWord hn w) := by
  apply (shift_periodic_iff _ _).mpr
  intro k
  simp [repeatWord, Nat.add_mod_right]

theorem repeatWord_prefix {n : ℕ} (hn : 0 < n) (w : Fin n → Fin 2) (k : Fin n) :
    repeatWord hn w k = w k := by
  simp only [repeatWord, Nat.mod_eq_of_lt k.isLt]

/-- Restriction to one period and periodic extension are inverse equivalences. -/
def periodicWordEquiv (n : ℕ) (hn : 0 < n) :
    {a : ℕ → Fin 2 // IsPeriodicPt shift n a} ≃ (Fin n → Fin 2) where
  toFun a k := a.val k
  invFun w := ⟨repeatWord hn w, repeatWord_periodic hn w⟩
  left_inv a := by
    apply Subtype.ext
    funext k
    exact ((shift_periodic_iff a.val n).mp a.property).map_mod_nat k
  right_inv w := funext (repeatWord_prefix hn w)

/-- The exact count includes all periods dividing `n`; `n` must be positive. -/
theorem shift_periodic_card (n : ℕ) (hn : 0 < n) :
    Nat.card {a : ℕ → Fin 2 // IsPeriodicPt shift n a} = 2^n := by
  rw [Nat.card_congr (periodicWordEquiv n hn)]
  simp

/-- Every finite prefix has a periodic continuation of a specified longer length. -/
theorem periodic_extension (a : ℕ → Fin 2) (n : ℕ) (hn : 0 < n) :
    ∃ b : ℕ → Fin 2, IsPeriodicPt shift n b ∧ ∀ k < n, b k = a k := by
  refine ⟨repeatWord hn (fun k => a k), repeatWord_periodic hn _, ?_⟩
  intro k hk
  simpa using repeatWord_prefix hn (fun k : Fin n => a k) ⟨k,hk⟩

/-- A single marked symbol in each length-`n` block has minimal period `n`. -/
theorem shift_has_exact_period (n : ℕ) (hn : 0 < n) :
    ∃ a : ℕ → Fin 2, minimalPeriod shift a = n := by
  let w : Fin n → Fin 2 := fun k => if k.val = 0 then 1 else 0
  let a := repeatWord hn w
  have ha : IsPeriodicPt shift n a := repeatWord_periodic hn w
  refine ⟨a, Nat.le_antisymm (ha.minimalPeriod_le hn) ?_⟩
  by_contra hnot
  have hlt : minimalPeriod shift a < n := by omega
  have hpos : 0 < minimalPeriod shift a := ha.minimalPeriod_pos hn
  have he := congrFun (isPeriodicPt_minimalPeriod shift a).eq 0
  rw [shift_iterate_apply, zero_add] at he
  have hzero : a 0 = 1 := by simp [a, repeatWord, w]
  have hmark : a (minimalPeriod shift a) = 0 := by
    simp [a, repeatWord, w, Nat.mod_eq_of_lt hlt, Nat.ne_of_gt hpos]
  rw [hmark, hzero] at he
  exact (by decide : (0 : Fin 2) ≠ 1) he

/-- Periodic addresses meet every nonempty open subset of the full binary shift. -/
theorem shift_periodic_dense : Dense (periodicPts shift) := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨a, ha⟩ := hne
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU a ha
  let n := I.sup id + 1
  have hn : 0 < n := by dsimp [n]; omega
  obtain ⟨b, hb, hprefix⟩ := periodic_extension a n hn
  refine ⟨b, hsub ?_, mk_mem_periodicPts hn hb⟩
  intro k hk
  have hkn : k < n := by
    have := Finset.le_sup (f := id) hk
    dsimp [n]
    omega
  rw [hprefix k hkn]
  exact (hu k hk).2

end LoopsBinaryShiftPeriodic
