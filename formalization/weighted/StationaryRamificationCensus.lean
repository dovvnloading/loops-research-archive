import QuadraticEscapeFullness

/-!
# Exact postcritical identification loss under a geometric quotient

The archive already supplies the exact model and physical inverse census.
The new comparison isolates precisely which critical-orbit contacts are
created by collapsing a nonsingleton geometric target fiber. Their actual
times and repetitions determine the full dyadic loss of predecessors.
-/

namespace LoopsStationaryRamificationCensus

open Set Function Classical
open LoopsQuadraticEscapeFullness
open scoped BigOperators

noncomputable section

variable {X Y : Type*}

/-- Extra critical-orbit contacts created by identifying points in a
quotient fiber; true physical hits at the chosen anchor are excluded. -/
def collapsedCriticalDefect (p : X → Y) (F : X → X) (v a : X) : ℕ → ℕ
  | 0 => 0
  | n+1 => 2*collapsedCriticalDefect p F v a n +
      (if p ((F^[n]) v) = p a ∧ (F^[n]) v ≠ a then 1 else 0)

/-- The complete loss is the dyadically weighted list of extra
postcritical contacts, retaining their actual times and repetitions. -/
theorem collapsedCriticalDefect_eq_sum (p : X → Y) (F : X → X)
    (v a : X) (n : ℕ) :
    collapsedCriticalDefect p F v a n =
      ∑ k ∈ Finset.range n,
        2^(n-1-k) *
          (if p ((F^[k]) v) = p a ∧ (F^[k]) v ≠ a then 1 else 0) := by
  induction n with
  | zero => simp [collapsedCriticalDefect]
  | succ n ih =>
    rw [collapsedCriticalDefect, ih, Finset.sum_range_succ, Finset.mul_sum]
    have hs : (∑ k ∈ Finset.range n,
        2 * (2^(n-1-k) *
          (if p ((F^[k]) v) = p a ∧ (F^[k]) v ≠ a then 1 else 0))) =
      ∑ k ∈ Finset.range n,
        2^(n+1-1-k) *
          (if p ((F^[k]) v) = p a ∧ (F^[k]) v ≠ a then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have he : n+1-1-k = (n-1-k)+1 := by omega
      rw [he, pow_succ]
      ring
    rw [hs]
    simp

/-- The model defect splits into the physical defect and exactly the
extra contacts with the whole geometric quotient fiber. -/
theorem semiconj_modelCriticalDefect (p : X → Y) (F : X → X) (G : Y → Y)
    (hs : Semiconj p F G) (v a : X) (n : ℕ) :
    modelCriticalDefect G (p v) (p a) n =
      modelCriticalDefect F v a n + collapsedCriticalDefect p F v a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [modelCriticalDefect, modelCriticalDefect, collapsedCriticalDefect, ih,
      ← hs.iterate_right n v]
    by_cases h : (F^[n]) v = a
    · simp [h]
      omega
    · by_cases hp : p ((F^[n]) v) = p a
      · simp [h, hp]
        omega
      · simp [h, hp]
        omega

theorem collapsedCriticalDefect_zero_iff (p : X → Y) (F : X → X)
    (v a : X) (n : ℕ) :
    collapsedCriticalDefect p F v a n = 0 ↔
      ∀ k < n, p ((F^[k]) v) = p a → (F^[k]) v = a := by
  induction n with
  | zero => simp [collapsedCriticalDefect]
  | succ n ih =>
    constructor
    · intro hd k hk hp
      have hprev : collapsedCriticalDefect p F v a n = 0 := by
        simp only [collapsedCriticalDefect] at hd
        omega
      by_cases he : k = n
      · subst k
        by_contra hn
        simp [collapsedCriticalDefect, hp, hn] at hd
      · exact ih.mp hprev k (by omega) hp
    · intro h
      have hp := ih.mpr (fun k hk => h k (by omega))
      have hn : ¬ (p ((F^[n]) v) = p a ∧ (F^[n]) v ≠ a) :=
        fun hh => hh.2 (h n (by omega) hh.1)
      simp [collapsedCriticalDefect, hp, hn]

end

end LoopsStationaryRamificationCensus
