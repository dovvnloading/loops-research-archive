import StationaryPrefixCharge

/-!
# Finite stage-endpoint census

The written application is in
research/independent_audits/stationary_transport_attack_20261124/STAGE_ENDPOINT_CENSUS.md.
The component/phase injection and the degree caps are supplied by the
physical argument. This module verifies their finite consequences,
not the existence or physical landing of stationary paths.
-/

namespace LoopsStationaryEndpointVisits

open scoped BigOperators

/-- The records have an owner (a final component or an endpoint time)
and a critical phase. Distinct records with the same owner must have
distinct phases. This injection is the exact finite capacity argument. -/
theorem owner_phase_count {n k b : ℕ}
    (owner : Fin n → Fin k) (phase : Fin n → Fin b)
    (h : ∀ i j, owner i = owner j → phase i = phase j → i = j) :
    n ≤ k * b := by
  have hinj : Function.Injective (fun i => (owner i, phase i)) := by
    intro i j hij
    exact h i j (congrArg Prod.fst hij) (congrArg Prod.snd hij)
  have hc := Fintype.card_le_of_injective _ hinj
  simpa using hc

/-- A family of more than b distinct stage records cannot have a
single component owner if its phases are injective within each owner. -/
theorem more_than_b_distinct_components {n b : ℕ} {Q : Type*}
    (owner : Fin n → Q) (phase : Fin n → Fin b)
    (h : ∀ i j, owner i = owner j → phase i = phase j → i = j)
    (hn : b < n) :
    ∃ i j, owner i ≠ owner j := by
  classical
  by_contra hno
  have hinj : Function.Injective phase := by
    intro i j hij
    have ho : owner i = owner j := by
      by_contra hne
      exact hno ⟨i, j, hne⟩
    exact h i j ho hij
  have hc := Fintype.card_le_of_injective phase hinj
  have hnle : n ≤ b := by simpa using hc
  omega

/-- At the original horizon b+2, if at most b stages are
Julia-critical then at least three are not. -/
theorem original_horizon_residual (b good bad : ℕ)
    (hpartition : good + bad = b + 3) (hgood : good ≤ b) :
    3 ≤ bad := by
  omega

/-- The two original endpoint times and e interior endpoint times
can jointly account for at most b(2+e) critical stages. -/
theorem window_birth_budget {h b e : ℕ}
    (owner : Fin (h+1) → Fin (2+e)) (phase : Fin (h+1) → Fin b)
    (hinj : ∀ i j, owner i = owner j → phase i = phase j → i = j) :
    h+1 ≤ (2+e)*b := by
  exact owner_phase_count owner phase hinj

/-- The excess beyond the two original endpoint capacities must
be supplied by genuinely new endpoint times. -/
theorem excess_requires_births {h b e : ℕ}
    (hc : h+1 ≤ (2+e)*b) :
    h+1-2*b ≤ e*b := by
  rw [Nat.add_mul] at hc
  omega

/-- At horizon 2b, two unchanged endpoint times are insufficient. -/
theorem no_full_window_at_double_bound {b e : ℕ}
    (hc : 2*b+1 ≤ (2+e)*b) :
    0 < e := by
  by_contra he
  have hz : e = 0 := by omega
  subst e
  simp at hc
  omega

/-- Geometric prefix sum with an empty range allowed. -/
theorem degree_prefix_sum (h : ℕ) :
    (∑ j ∈ Finset.range h, (2 : ℝ)^j) = (2 : ℝ)^h - 1 := by
  cases h with
  | zero => norm_num
  | succ h => exact LoopsStationaryPrefixCharge.prefix_degree_sum h

/-- The prefix preimage degree is at most 2^j per critical target.
A suffix before the final stage has degree at most two, while the
empty suffix at the final stage has degree one. Summing the upper
charges (including duplicates only in the upper-bound direction)
gives the uniform bank degree bound. -/
theorem final_bank_degree_budget (h : ℕ) (b : ℝ) (c : ℕ → ℝ)
    (hp : ∀ j < h, c j ≤ 2*b*(2 : ℝ)^j)
    (hlast : c h ≤ b*(2 : ℝ)^h) :
    (∑ j ∈ Finset.range (h+1), c j) ≤ b*(3*(2 : ℝ)^h-2) := by
  have hs : (∑ j ∈ Finset.range h, c j) ≤
      ∑ j ∈ Finset.range h, 2*b*(2 : ℝ)^j := by
    apply Finset.sum_le_sum
    intro j hj
    exact hp j (Finset.mem_range.mp hj)
  have he : (∑ j ∈ Finset.range h, 2*b*(2 : ℝ)^j) =
      2*b*((2 : ℝ)^h-1) := by
    rw [← Finset.mul_sum, degree_prefix_sum]
  rw [he] at hs
  rw [Finset.sum_range_succ]
  linarith

/-- At least one interior endpoint must occur in a longer stationary
chain, independently of how the retained witnesses were chosen. -/
theorem at_least_one_birth {b e : ℕ}
    (owner : Fin (2*b+1) → Fin (2+e))
    (phase : Fin (2*b+1) → Fin b)
    (hinj : ∀ i j, owner i = owner j → phase i = phase j → i = j) :
    0 < e := by
  exact no_full_window_at_double_bound (owner_phase_count owner phase hinj)

end LoopsStationaryEndpointVisits
