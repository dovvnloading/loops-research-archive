import PhaseTower

/-!
# Exact 3 -> 9 -> 27 phase addresses and the minimum retained clock data

The certified real quadratic model has physical return times 3 and 9 and
critical period 27. The exact *finite clock* 27 decomposes into three base-3
digits. This module constructs a reversible encoding, checks the complete
carry transition, and proves its conjugacy for every number of iterations.

The first digit is the period-3 phase, the first two digits together encode
the period-9 phase, and all three digits encode the period-27 phase.
Forgetting digits is not lossless for a marking that distinguishes them.
No parameter ray, prime end, holomorphic restriction, or MLC theorem is
asserted or imported.
-/

namespace LoopsFormal.PhaseTower

/-- Outer phase, middle refinement memory, and deepest refinement memory. -/
abbrev Address27 := Phase 3 × Phase 3 × Phase 3

/-- Natural order is outer phase + 3 * middle memory + 9 * deep memory. -/
def encode27 (j : Phase 27) : Address27 :=
  (⟨j.val % 3, by omega⟩,
   ⟨(j.val / 3) % 3, by omega⟩,
   ⟨j.val / 9, by have hj := j.isLt; omega⟩)

/-- Reconstruct the unique physical clock phase from the three digits. -/
def decode27 (a : Address27) : Phase 27 :=
  ⟨a.1.val + 3 * a.2.1.val + 9 * a.2.2.val, by
    have h0 := a.1.isLt
    have h1 := a.2.1.isLt
    have h2 := a.2.2.isLt
    omega⟩

/-- Every one of the 27 physical phases survives decoding after
    encoding. This finite theorem is checked by kernel reduction. -/
theorem decode_encode27 : ∀ j : Phase 27,
    decode27 (encode27 j) = j := by
  decide +kernel

/-- Every three-digit address also survives encoding after decoding. -/
theorem encode_decode27 : ∀ a : Address27,
    encode27 (decode27 a) = a := by
  intro a
  cases a with
  | mk x tail =>
    cases tail with
    | mk y z =>
      revert x y z
      decide +kernel

theorem encode27_injective : Function.Injective encode27 := by
  intro i j h
  calc
    i = decode27 (encode27 i) := (decode_encode27 i).symm
    _ = decode27 (encode27 j) := congrArg decode27 h
    _ = j := decode_encode27 j

theorem encode27_surjective : Function.Surjective encode27 := by
  intro a
  exact ⟨decode27 a, encode_decode27 a⟩

/-- The exact 9-phase residue is encoded by the first two digits. -/
def firstTwoDigits (a : Address27) : Phase 9 :=
  ⟨a.1.val + 3 * a.2.1.val, by
    have h0 := a.1.isLt
    have h1 := a.2.1.isLt
    omega⟩

/-- The first digit is the period-3 phase of the original 27-clock. -/
theorem first_digit_is_outer_phase : ∀ j : Phase 27,
    (encode27 j).1 = project 3 27 (by decide) j := by
  decide +kernel

/-- The first two digits retain exactly the period-9 phase. -/
theorem first_two_digits_are_middle_phase : ∀ j : Phase 27,
    firstTwoDigits (encode27 j) = project 9 27 (by decide) j := by
  decide +kernel

/-- Reducing the retained 9-phase again gives the outer 3-phase. -/
theorem first_two_digits_project_to_first (a : Address27) :
    project 3 9 (by decide) (firstTwoDigits a) = a.1 := by
  apply Fin.ext
  have h0 := a.1.isLt
  have h1 := a.2.1.isLt
  dsimp [project, firstTwoDigits]
  omega

/-- Physical clock successor, including wraparound. -/
def next27 (j : Phase 27) : Phase 27 :=
  ⟨(j.val + 1) % 27, by omega⟩

/-- Successor as a three-digit carry machine. The middle digit advances
    exactly when the outer digit wraps; the deep digit advances exactly
    when both lower digits wrap. -/
def carry27 (a : Address27) : Address27 :=
  (⟨(a.1.val + 1) % 3, by omega⟩,
   ⟨(a.2.1.val + (if a.1.val = 2 then 1 else 0)) % 3,
      by omega⟩,
   ⟨(a.2.2.val +
        (if a.1.val = 2 ∧ a.2.1.val = 2 then 1 else 0)) % 3,
      by omega⟩)

/-- Exhaustive 27-state kernel check of the claimed carry transition;
    it is not an assumed diagram of how the digits behave. -/
theorem carry_is_physical_successor : ∀ a : Address27,
    carry27 a = encode27 (next27 (decode27 a)) := by
  intro a
  cases a with
  | mk x tail =>
    cases tail with
    | mk y z =>
      revert x y z
      decide +kernel

/-- The phase encoding intertwines physical successor and exact carry. -/
theorem carry_conjugacy (j : Phase 27) :
    carry27 (encode27 j) = encode27 (next27 j) := by
  rw [carry_is_physical_successor, decode_encode27]

/-- The same intertwining holds at *all* times, not just a single step. -/
theorem carry_conjugacy_all_times (time : Nat) (j : Phase 27) :
    LoopsFormal.Paper2.iterate carry27 time (encode27 j) =
      encode27 (LoopsFormal.Paper2.iterate next27 time j) := by
  induction time with
  | zero => rfl
  | succ time ih =>
      change carry27
          (LoopsFormal.Paper2.iterate carry27 time (encode27 j)) =
        encode27 (next27 (LoopsFormal.Paper2.iterate next27 time j))
      rw [ih]
      exact carry_conjugacy (LoopsFormal.Paper2.iterate next27 time j)

/-- Explicit physical phase at arbitrary time. This theorem is general
    in the number of steps; no finite list of clock iterates is assumed. -/
theorem iterate_next27_mod (time : Nat) (j : Phase 27) :
    (LoopsFormal.Paper2.iterate next27 time j).val =
      (j.val + time) % 27 := by
  induction time with
  | zero =>
      change j.val = (j.val + 0) % 27
      simp [Nat.mod_eq_of_lt j.isLt]
  | succ time ih =>
      change ((LoopsFormal.Paper2.iterate next27 time j).val + 1) % 27 =
        (j.val + (time + 1)) % 27
      rw [ih, Nat.mod_add_mod]

/-- The physical clock returns after 27 steps. -/
theorem next27_returns (j : Phase 27) :
    LoopsFormal.Paper2.iterate next27 27 j = j := by
  apply Fin.ext
  rw [iterate_next27_mod]
  simpa using (Nat.mod_eq_of_lt j.isLt)

/-- No positive time strictly less than 27 returns a physical phase.
    This rules out a shorter phase period in the complete clock. -/
theorem next27_no_early_return (j : Phase 27) (time : Nat)
    (htpos : 0 < time) (htlt : time < 27) :
    LoopsFormal.Paper2.iterate next27 time j ≠ j := by
  intro heq
  have hval := congrArg Fin.val heq
  rw [iterate_next27_mod] at hval
  have hj := j.isLt
  omega

/-- Exact period 27 is preserved by the complete three-digit
    carry representation (both existence and minimality of the period). -/
theorem address_exact_period27 (a : Address27) :
    LoopsFormal.Paper2.iterate carry27 27 a = a ∧
    ∀ time, 0 < time → time < 27 →
      LoopsFormal.Paper2.iterate carry27 time a ≠ a := by
  constructor
  · calc
      LoopsFormal.Paper2.iterate carry27 27 a =
          LoopsFormal.Paper2.iterate carry27 27 (encode27 (decode27 a)) := by
            rw [encode_decode27]
      _ = encode27 (LoopsFormal.Paper2.iterate next27 27 (decode27 a)) :=
        carry_conjugacy_all_times 27 (decode27 a)
      _ = encode27 (decode27 a) := by rw [next27_returns]
      _ = a := encode_decode27 a
  · intro time htpos htlt heq
    have hc : encode27 (LoopsFormal.Paper2.iterate next27 time (decode27 a)) =
        encode27 (decode27 a) := by
      calc
        encode27 (LoopsFormal.Paper2.iterate next27 time (decode27 a)) =
            LoopsFormal.Paper2.iterate carry27 time (encode27 (decode27 a)) :=
              (carry_conjugacy_all_times time (decode27 a)).symm
        _ = LoopsFormal.Paper2.iterate carry27 time a := by rw [encode_decode27]
        _ = a := heq
        _ = encode27 (decode27 a) := (encode_decode27 a).symm
    exact next27_no_early_return (decode27 a) time htpos htlt
      (encode27_injective hc)

/-- Every injective nine-phase marking needs some information beyond
    the three-phase quotient: no relabeling on three phases recovers it. -/
theorem nine_to_three_cannot_preserve_distinct_marks {α : Type}
    (L : Phase 9 → α) (hL : Function.Injective L) :
    ¬ FactorsThrough 3 9 (by decide) L :=
  injective_marking_never_factors 3 9 (by decide) (by decide) L hL

/-- The same obstruction at the top step of the 27 -> 9 -> 3 tower. -/
theorem twentyseven_to_nine_cannot_preserve_distinct_marks {α : Type}
    (L : Phase 27 → α) (hL : Function.Injective L) :
    ¬ FactorsThrough 9 27 (by decide) L :=
  injective_marking_never_factors 9 27 (by decide) (by decide) L hL

/-- Projecting all the way from 27 to 3 loses even more information,
    regardless of how the nine-phase intermediate stage is organized. -/
theorem twentyseven_to_three_cannot_preserve_distinct_marks {α : Type}
    (L : Phase 27 → α) (hL : Function.Injective L) :
    ¬ FactorsThrough 3 27 (by decide) L :=
  injective_marking_never_factors 3 27 (by decide) (by decide) L hL

/-- The 27 -> 9 -> 3 phase projections commute, independent of whether
    those clocks arise from actual dynamical return sets. -/
theorem period27_projection_commutes (j : Phase 27) :
    project 3 9 (by decide) (project 9 27 (by decide) j) =
      project 3 27 (by decide) j := by
  exact project_compose 3 9 27 (by decide) (by decide)
    (by decide) j

#print axioms decode_encode27
#print axioms encode_decode27
#print axioms carry_is_physical_successor
#print axioms carry_conjugacy_all_times
#print axioms address_exact_period27

end LoopsFormal.PhaseTower
