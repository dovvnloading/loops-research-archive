import Mathlib

/-!
# Exact predecessor loss under a quadratic geometric quotient

A map with a single one-point predecessor fiber and two points in every
other predecessor fiber has an exact inverse census at every depth. Under
a semiconjugacy between two such systems, the discrepancy is precisely the
weighted list of extra critical-orbit contacts with the whole quotient
fiber. No singleton assumption is made on the quotient target fiber.
-/

namespace LoopsStationaryRamificationCensus

open Set Function Classical
open scoped BigOperators

noncomputable section

variable {X Y : Type*}

/-- Finite predecessor levels, constructed from the actual point fibers. -/
def inverseLevel (F : X → X) (hfinite : ∀ y, (F ⁻¹' {y}).Finite)
    (y : X) : ℕ → Finset X
  | 0 => {y}
  | n+1 => (inverseLevel F hfinite y n).biUnion (fun x => (hfinite x).toFinset)

theorem mem_inverseLevel (F : X → X)
    (hfinite : ∀ y, (F ⁻¹' {y}).Finite) (y x : X) (n : ℕ) :
    x ∈ inverseLevel F hfinite y n ↔ (F^[n]) x = y := by
  induction n generalizing x with
  | zero => simp [inverseLevel]
  | succ n ih =>
    simp only [inverseLevel, Finset.mem_biUnion, Set.Finite.mem_toFinset,
      Set.mem_preimage, Set.mem_singleton_iff, ih]
    constructor
    · rintro ⟨z, hz, hx⟩
      rw [Function.iterate_succ_apply, hx]
      exact hz
    · intro hx
      exact ⟨F x, by simpa only [Function.iterate_succ_apply] using hx, rfl⟩

theorem inverseLevel_coe (F : X → X)
    (hfinite : ∀ y, (F ⁻¹' {y}).Finite) (y : X) (n : ℕ) :
    (↑(inverseLevel F hfinite y n) : Set X) = (F^[n]) ⁻¹' {y} := by
  ext x
  exact mem_inverseLevel F hfinite y x n

theorem iterate_fiber_finite (F : X → X)
    (hfinite : ∀ y, (F ⁻¹' {y}).Finite) (y : X) (n : ℕ) :
    ((F^[n]) ⁻¹' {y}).Finite := by
  rw [← inverseLevel_coe F hfinite y n]
  exact Finset.finite_toSet _

private theorem inverseLevel_card_step (F : X → X)
    (hfinite : ∀ y, (F ⁻¹' {y}).Finite) (v : X)
    (hcard : ∀ y, (F ⁻¹' {y}).ncard + (if y = v then 1 else 0) = 2)
    (y : X) (n : ℕ) :
    (inverseLevel F hfinite y (n+1)).card +
      (if (F^[n]) v = y then 1 else 0) =
      2*(inverseLevel F hfinite y n).card := by
  have hdis : (↑(inverseLevel F hfinite y n) : Set X).PairwiseDisjoint
      (fun z => (hfinite z).toFinset) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    have h₁ : F x = a := by simpa only [Set.Finite.mem_toFinset,
      Set.mem_preimage, Set.mem_singleton_iff] using hxa
    have h₂ : F x = b := by simpa only [Set.Finite.mem_toFinset,
      Set.mem_preimage, Set.mem_singleton_iff] using hxb
    exact hab (h₁.symm.trans h₂)
  have hc (z : X) :
      (hfinite z).toFinset.card + (if z = v then 1 else 0) = 2 := by
    rw [← Set.ncard_eq_toFinset_card _ (hfinite z)]
    exact hcard z
  have hs := Finset.sum_congr (s₁ := inverseLevel F hfinite y n) rfl
    (fun z _ => hc z)
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_ite_eq', Finset.sum_const, nsmul_eq_mul] at hs
  rw [inverseLevel, Finset.card_biUnion hdis]
  rw [← mem_inverseLevel F hfinite y v n]
  by_cases hv : v ∈ inverseLevel F hfinite y n
  · simpa [hv, Nat.mul_comm] using hs
  · simpa [hv, Nat.mul_comm] using hs

/-- Each critical-value hit contributes one lost branch, then doubles
at every remaining inverse step. -/
def criticalDefect (F : X → X) (v y : X) : ℕ → ℕ
  | 0 => 0
  | n+1 => 2*criticalDefect F v y n + (if (F^[n]) v = y then 1 else 0)

/-- Exact all-depth distinct-point census for a one-critical-value
quadratic map. The one-step hypothesis is a count of actual point fibers. -/
theorem inverseLevel_card_exact (F : X → X)
    (hfinite : ∀ y, (F ⁻¹' {y}).Finite) (v : X)
    (hcard : ∀ y, (F ⁻¹' {y}).ncard + (if y = v then 1 else 0) = 2)
    (y : X) (n : ℕ) :
    (inverseLevel F hfinite y n).card + criticalDefect F v y n = 2^n := by
  induction n with
  | zero => simp [inverseLevel, criticalDefect]
  | succ n ih =>
    have h := inverseLevel_card_step F hfinite v hcard y n
    rw [criticalDefect, pow_succ (2 : ℕ) n]
    omega

/-- The same census without dependence on a chosen finite-set enumeration. -/
theorem iterate_fiber_ncard_exact (F : X → X)
    (hfinite : ∀ y, (F ⁻¹' {y}).Finite) (v : X)
    (hcard : ∀ y, (F ⁻¹' {y}).ncard + (if y = v then 1 else 0) = 2)
    (y : X) (n : ℕ) :
    ((F^[n]) ⁻¹' {y}).ncard + criticalDefect F v y n = 2^n := by
  rw [← inverseLevel_coe F hfinite y n, Set.ncard_coe_finset]
  exact inverseLevel_card_exact F hfinite v hcard y n

/-- Explicit weights retain repeated contacts, including a periodic
critical orbit. No distinctness of critical-value labels is assumed. -/
theorem criticalDefect_eq_sum (F : X → X) (v y : X) (n : ℕ) :
    criticalDefect F v y n =
      ∑ k ∈ Finset.range n,
        2^(n-1-k) * (if (F^[k]) v = y then 1 else 0) := by
  induction n with
  | zero => simp [criticalDefect]
  | succ n ih =>
    rw [criticalDefect, ih, Finset.sum_range_succ, Finset.mul_sum]
    have hs : (∑ k ∈ Finset.range n,
        2 * (2^(n-1-k) * (if (F^[k]) v = y then 1 else 0))) =
      ∑ k ∈ Finset.range n,
        2^(n+1-1-k) * (if (F^[k]) v = y then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have he : n+1-1-k = (n-1-k)+1 := by omega
      rw [he, pow_succ]
      ring
    rw [hs]
    simp

theorem criticalDefect_zero_iff (F : X → X) (v y : X) (n : ℕ) :
    criticalDefect F v y n = 0 ↔ ∀ k < n, (F^[k]) v ≠ y := by
  induction n with
  | zero => simp [criticalDefect]
  | succ n ih =>
    constructor
    · intro hd k hk
      have hp : criticalDefect F v y n = 0 := by
        simp only [criticalDefect] at hd
        omega
      by_cases he : k = n
      · subst k
        intro h
        simp [criticalDefect, h] at hd
      · exact ih.mp hp k (by omega)
    · intro h
      have hp := ih.mpr (fun k hk => h k (by omega))
      simp [criticalDefect, hp, h n (by omega)]

theorem iterate_fiber_full_card_iff (F : X → X)
    (hfinite : ∀ y, (F ⁻¹' {y}).Finite) (v : X)
    (hcard : ∀ y, (F ⁻¹' {y}).ncard + (if y = v then 1 else 0) = 2)
    (y : X) (n : ℕ) :
    ((F^[n]) ⁻¹' {y}).ncard = 2^n ↔ ∀ k < n, (F^[k]) v ≠ y := by
  rw [← criticalDefect_zero_iff F v y n]
  have he := iterate_fiber_ncard_exact F hfinite v hcard y n
  omega

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
theorem semiconj_criticalDefect (p : X → Y) (F : X → X) (G : Y → Y)
    (hs : Semiconj p F G) (v a : X) (n : ℕ) :
    criticalDefect G (p v) (p a) n =
      criticalDefect F v a n + collapsedCriticalDefect p F v a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [criticalDefect, criticalDefect, collapsedCriticalDefect, ih,
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

/-- Exact loss in distinct predecessors under a quadratic
semiconjugacy, including nonsingleton target fibers. -/
theorem semiconj_inverse_fiber_loss (p : X → Y) (F : X → X) (G : Y → Y)
    (hs : Semiconj p F G) (v a : X)
    (hFfinite : ∀ x, (F ⁻¹' {x}).Finite)
    (hGfinite : ∀ y, (G ⁻¹' {y}).Finite)
    (hFcard : ∀ x, (F ⁻¹' {x}).ncard + (if x = v then 1 else 0) = 2)
    (hGcard : ∀ y, (G ⁻¹' {y}).ncard + (if y = p v then 1 else 0) = 2)
    (n : ℕ) :
    ((F^[n]) ⁻¹' {a}).ncard =
      ((G^[n]) ⁻¹' {p a}).ncard + collapsedCriticalDefect p F v a n := by
  have hF := iterate_fiber_ncard_exact F hFfinite v hFcard a n
  have hG := iterate_fiber_ncard_exact G hGfinite (p v) hGcard (p a) n
  rw [semiconj_criticalDefect p F G hs v a n] at hG
  omega

/-- Equality of the predecessor census is equivalent to the absence
of extra critical-orbit contacts in the complete target fiber. -/
theorem semiconj_inverse_fiber_card_eq_iff (p : X → Y) (F : X → X) (G : Y → Y)
    (hs : Semiconj p F G) (v a : X)
    (hFfinite : ∀ x, (F ⁻¹' {x}).Finite)
    (hGfinite : ∀ y, (G ⁻¹' {y}).Finite)
    (hFcard : ∀ x, (F ⁻¹' {x}).ncard + (if x = v then 1 else 0) = 2)
    (hGcard : ∀ y, (G ⁻¹' {y}).ncard + (if y = p v then 1 else 0) = 2)
    (n : ℕ) :
    ((F^[n]) ⁻¹' {a}).ncard = ((G^[n]) ⁻¹' {p a}).ncard ↔
      ∀ k < n, p ((F^[k]) v) = p a → (F^[k]) v = a := by
  rw [← collapsedCriticalDefect_zero_iff p F v a n]
  have he := semiconj_inverse_fiber_loss p F G hs v a hFfinite hGfinite
    hFcard hGcard n
  omega

end

end LoopsStationaryRamificationCensus
