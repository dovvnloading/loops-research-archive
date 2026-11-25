import Mathlib

/-!
# Finite endpoint-cover accounting for stationary exit transfer

Formalizes the finite real-valued inequality (4.4) and bank estimates of
research/independent_audits/stationary_transport_attack_20261124/VARIABLE_END_EXIT_TRANSFER.md.
The geometric input is the incidence-width estimate for every charged end.
No geometric exit existence, modulus additivity, covering degree census,
or MLC conclusion is asserted here.
-/

namespace LoopsStationaryEndpointCover

open scoped BigOperators

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- Width incident to an end, counting each occurring pair once. The
endpoints are oriented solely to represent the unordered pair. -/
def incidentLoad (u v : E → V) (x : E → ℝ) (j : V) : ℝ :=
  ∑ e, if j = u e ∨ j = v e then x e else 0

/-- Distinct ends are required to split the incidence into two endpoint
contributions. Self-returns are not eligible exits in the source theorem. -/
theorem incidentLoad_eq_split (u v : E → V) (x : E → ℝ)
    (hne : ∀ e, u e ≠ v e) (j : V) :
    incidentLoad u v x j =
      ∑ e, ((if j = u e then x e else 0) + (if j = v e then x e else 0)) := by
  unfold incidentLoad
  apply Finset.sum_congr rfl
  intro e _
  by_cases hu : j = u e
  · have hv : j ≠ v e := fun h => hne e (hu.symm.trans h)
    simp only [if_pos (show j = u e ∨ j = v e from Or.inl hu),
      if_pos hu, if_neg hv, add_zero]
  · by_cases hv : j = v e
    · simp only [if_pos (show j = u e ∨ j = v e from Or.inr hv),
        if_neg hu, if_pos hv, zero_add]
    · have hn : ¬ (j = u e ∨ j = v e) := fun h => h.elim hu hv
      simp only [if_neg hn, if_neg hu, if_neg hv, zero_add]

/-- Exact finite double-counting identity, independent of signs. -/
theorem weighted_load (u v : E → V) (x : E → ℝ) (a : V → ℝ)
    (hne : ∀ e, u e ≠ v e) :
    (∑ j, a j * incidentLoad u v x j) =
      ∑ e, (a (u e) + a (v e)) * x e := by
  calc
    (∑ j, a j * incidentLoad u v x j) =
        ∑ j, ∑ e, a j *
          ((if j = u e then x e else 0) + (if j = v e then x e else 0)) := by
            simp only [incidentLoad_eq_split u v x hne, Finset.mul_sum]
    _ = ∑ e, ∑ j, a j *
          ((if j = u e then x e else 0) + (if j = v e then x e else 0)) :=
      Finset.sum_comm
    _ = ∑ e, (a (u e) + a (v e)) * x e := by
      apply Finset.sum_congr rfl
      intro e _
      have single (k : V) :
          (∑ j, a j * (if j = k then x e else 0)) = a k * x e := by
        calc
          _ = ∑ j, if j = k then a j * x e else 0 := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : j = k <;> simp [hj]
          _ = _ := by simp
      rw [add_mul]
      simp only [mul_add, Finset.sum_add_distrib]
      rw [single (u e), single (v e)]

/-- Weak duality for every finite endpoint graph, not just certificate
instances. A zero coefficient requires no capacity inequality at that end:
its assigned real number is immaterial. -/
theorem fractional_cover (u v : E → V) (x : E → ℝ) (a L : V → ℝ)
    (hne : ∀ e, u e ≠ v e) (hx : ∀ e, 0 ≤ x e)
    (ha : ∀ j, 0 ≤ a j)
    (hcover : ∀ e, 1 ≤ a (u e) + a (v e))
    (hbudget : ∀ j, 0 < a j → incidentLoad u v x j ≤ L j) :
    (∑ e, x e) ≤ ∑ j, a j * L j := by
  calc
    (∑ e, x e) ≤ ∑ e, (a (u e) + a (v e)) * x e := by
      apply Finset.sum_le_sum
      intro e _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hcover e) (hx e)
    _ = ∑ j, a j * incidentLoad u v x j := (weighted_load u v x a hne).symm
    _ ≤ ∑ j, a j * L j := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : 0 < a j
      · exact mul_le_mul_of_nonneg_left (hbudget j hj) (ha j)
      · have hz : a j = 0 := le_antisymm (le_of_not_gt hj) (ha j)
        simp [hz]

/-- Total charge of a selected bank; values outside the bank are ignored. -/
def bankCharge (C : Finset V) (L : V → ℝ) : ℝ :=
  ∑ j, if j ∈ C then L j else 0

/-- Corollary 4.2(2): each exit need only touch some charged end. -/
theorem one_end_bank (u v : E → V) (x : E → ℝ) (L : V → ℝ)
    (C : Finset V) (hne : ∀ e, u e ≠ v e) (hx : ∀ e, 0 ≤ x e)
    (hhit : ∀ e, u e ∈ C ∨ v e ∈ C)
    (hbudget : ∀ j ∈ C, incidentLoad u v x j ≤ L j) :
    (∑ e, x e) ≤ bankCharge C L := by
  let a : V → ℝ := fun j => if j ∈ C then 1 else 0
  have ha : ∀ j, 0 ≤ a j := by
    intro j
    by_cases hj : j ∈ C <;> simp [a, hj]
  have hc : ∀ e, 1 ≤ a (u e) + a (v e) := by
    intro e
    by_cases hu : u e ∈ C <;> by_cases hv : v e ∈ C
    · norm_num [a, hu, hv]
    · norm_num [a, hu, hv]
    · norm_num [a, hu, hv]
    · exact False.elim ((hhit e).elim hu hv)
  have hb : ∀ j, 0 < a j → incidentLoad u v x j ≤ L j := by
    intro j hj
    by_cases hm : j ∈ C
    · exact hbudget j hm
    · simp [a, hm] at hj
  calc
    (∑ e, x e) ≤ ∑ j, a j * L j := fractional_cover u v x a L hne hx ha hc hb
    _ = bankCharge C L := by
      unfold bankCharge
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ C <;> simp [a, hj]

/-- Corollary 4.2(3): if both distinct ends are charged, the bank cost
is halved. -/
theorem two_end_bank (u v : E → V) (x : E → ℝ) (L : V → ℝ)
    (C : Finset V) (hne : ∀ e, u e ≠ v e) (hx : ∀ e, 0 ≤ x e)
    (hhit : ∀ e, u e ∈ C ∧ v e ∈ C)
    (hbudget : ∀ j ∈ C, incidentLoad u v x j ≤ L j) :
    (∑ e, x e) ≤ (1 / 2 : ℝ) * bankCharge C L := by
  let a : V → ℝ := fun j => if j ∈ C then 1 / 2 else 0
  have ha : ∀ j, 0 ≤ a j := by
    intro j
    by_cases hj : j ∈ C <;> norm_num [a, hj]
  have hc : ∀ e, 1 ≤ a (u e) + a (v e) := by
    intro e
    norm_num [a, (hhit e).1, (hhit e).2]
  have hb : ∀ j, 0 < a j → incidentLoad u v x j ≤ L j := by
    intro j hj
    by_cases hm : j ∈ C
    · exact hbudget j hm
    · simp [a, hm] at hj
  calc
    (∑ e, x e) ≤ ∑ j, a j * L j := fractional_cover u v x a L hne hx ha hc hb
    _ = (1 / 2 : ℝ) * bankCharge C L := by
      unfold bankCharge
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ C <;> simp [a, hj]

/-- The local width-to-degree bounds imply a total bank cost bound.
The actual peripheral degree census is a separate geometric input. -/
theorem bank_charge_le_degree (C : Finset V) (L d : V → ℝ) (R : ℝ)
    (hlocal : ∀ j ∈ C, L j ≤ d j * R) :
    bankCharge C L ≤ bankCharge C d * R := by
  unfold bankCharge
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j ∈ C
  · simpa [hj] using hlocal j hj
  · simp [hj]

/-- Conditional terminal degree budget (1.2), (5.5): instantiate D with
b * 2^m or 2*r after proving the actual degree budget. -/
theorem one_end_degree_budget (u v : E → V) (x : E → ℝ) (L d : V → ℝ)
    (C : Finset V) (R D : ℝ)
    (hne : ∀ e, u e ≠ v e) (hx : ∀ e, 0 ≤ x e)
    (hhit : ∀ e, u e ∈ C ∨ v e ∈ C)
    (hbudget : ∀ j ∈ C, incidentLoad u v x j ≤ L j)
    (hlocal : ∀ j ∈ C, L j ≤ d j * R)
    (hdegree : bankCharge C d ≤ D) (hR : 0 ≤ R) :
    (∑ e, x e) ≤ D * R := by
  calc
    (∑ e, x e) ≤ bankCharge C L := one_end_bank u v x L C hne hx hhit hbudget
    _ ≤ bankCharge C d * R := bank_charge_le_degree C L d R hlocal
    _ ≤ D * R := mul_le_mul_of_nonneg_right hdegree hR

/-- Both-end terminal degree budget with the factor of two saving. -/
theorem two_end_degree_budget (u v : E → V) (x : E → ℝ) (L d : V → ℝ)
    (C : Finset V) (R D : ℝ)
    (hne : ∀ e, u e ≠ v e) (hx : ∀ e, 0 ≤ x e)
    (hhit : ∀ e, u e ∈ C ∧ v e ∈ C)
    (hbudget : ∀ j ∈ C, incidentLoad u v x j ≤ L j)
    (hlocal : ∀ j ∈ C, L j ≤ d j * R)
    (hdegree : bankCharge C d ≤ D) (hR : 0 ≤ R) :
    (∑ e, x e) ≤ (1 / 2 : ℝ) * (D * R) := by
  have hcost : bankCharge C L ≤ D * R :=
    (bank_charge_le_degree C L d R hlocal).trans (mul_le_mul_of_nonneg_right hdegree hR)
  exact (two_end_bank u v x L C hne hx hhit hbudget).trans
    (mul_le_mul_of_nonneg_left hcost (by norm_num))

end

end LoopsStationaryEndpointCover
