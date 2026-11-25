import StationaryEndpointVisits

/-!
# Finite accounting for canonical continuation and oriented restrictions

The analytic and topological inputs are stated separately in
research/independent_audits/stationary_transport_attack_20261124/CANONICAL_LIFT_AND_DIRECTION.md.
These results check the finite crossing-indicator, occupancy and energy
algebra; they do not construct the physical lifts or protected access charts.
-/

namespace LoopsStationaryCanonicalLift

open scoped BigOperators

/-- Inside/outside indicators telescope along a finite transverse path. -/
theorem indicator_telescope (s : ℕ → ℤ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (s j - s (j+1))) = s 0 - s n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- A component's relative orientation multiplies its net crossing count. -/
theorem signed_component_crossings (s : ℕ → ℤ) (n : ℕ) (e : ℤ) :
    (∑ j ∈ Finset.range n, e*(s j-s (j+1))) = e*(s 0-s n) := by
  rw [← Finset.mul_sum, indicator_telescope]

/-- If at most one raw component contains the anchor and the total
oriented crossing count is +1, that component exists and has sign +1.
All other components can contribute pairs of canceling crossings. -/
theorem unique_positive_anchor {J : Type*} [Fintype J]
    (active : J → Prop) [DecidablePred active] (w : J → ℤ)
    (hunique : ∀ i j, active i → active j → i = j)
    (hsum : (∑ i, if active i then w i else 0) = 1) :
    ∃ i, active i ∧ w i = 1 ∧ ∀ j, active j → j = i := by
  classical
  have hex : ∃ i, active i := by
    by_contra hn
    have hz : ∀ i, ¬ active i := fun i hi => hn ⟨i, hi⟩
    simp [hz] at hsum
  obtain ⟨i, hi⟩ := hex
  have he : (∑ j, if active j then w j else 0) = w i := by
    calc
      _ = ∑ j, if j = i then w j else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = i
        · subst j
          simp [hi]
        · have hnot : ¬ active j := fun ha => hj (hunique j i ha hi)
          simp [hj, hnot]
      _ = _ := by simp
  exact ⟨i, hi, he.symm.trans hsum, fun j hj => hunique j i hj hi⟩

/-- A proper covering image cannot contain the complete image of a
saturating block. The actual interval containment is a geometric input. -/
theorem proper_image_excludes_saturation {A B : Type*}
    (p : A → B) (critical base : Set A)
    (hsat : p '' critical = Set.univ) (hproper : p '' base ≠ Set.univ) :
    ¬ critical ⊆ base := by
  intro hsub
  apply hproper
  ext y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    have hy : y ∈ p '' critical := by
      rw [hsat]
      exact Set.mem_univ y
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hsub hx, rfl⟩

/-- Linearized cyclic order: from the precritical side to a positive
anchor, every point in the intervening critical block is in the base. -/
theorem intervening_block_contained {A : Type*} [LinearOrder A]
    (s l r e t : A) (hsl : s < l) (hre : r < e) (het : e < t) :
    Set.Icc l r ⊆ Set.Ioo s t := by
  intro x hx
  exact ⟨lt_of_lt_of_le hsl hx.1, lt_trans (lt_of_le_of_lt hx.2 hre) het⟩

/-- If completeness at a later horizon implies every earlier
completeness predicate, the union of all prefix failures equals
the last-horizon failure. -/
theorem prefix_failures_eq_last {A : Type*} (complete : ℕ → A → Prop)
    (hmono : ∀ i j, i ≤ j → ∀ x, complete j x → complete i x)
    (h : ℕ) (x : A) :
    (∃ j ≤ h, ¬ complete j x) ↔ ¬ complete h x := by
  constructor
  · rintro ⟨j, hj, hf⟩ hh
    exact hf (hmono j h hj x hh)
  · intro hf
    exact ⟨h, le_rfl, hf⟩

/-- A fixed oriented endpoint side has only one original endpoint.
Each new endpoint time may account for at most b critical visits. -/
theorem one_side_visit_budget {h b e : ℕ}
    (owner : Fin (h+1) → Fin (1+e))
    (phase : Fin (h+1) → Fin b)
    (hinj : ∀ i j, owner i = owner j → phase i = phase j → i = j) :
    h+1 ≤ (1+e)*b :=
  LoopsStationaryEndpointVisits.owner_phase_count owner phase hinj

/-- The exact excess beyond the single original endpoint capacity. -/
theorem one_side_birth_excess {h b e : ℕ}
    (hc : h+1 ≤ (1+e)*b) :
    h+1-b ≤ e*b := by
  rw [Nat.add_mul, Nat.one_mul] at hc
  omega

/-- At horizon b the critical side cannot have had no new endpoint. -/
theorem one_side_birth_at_bound {b e : ℕ}
    (hc : b+1 ≤ (1+e)*b) : 0 < e := by
  by_contra he
  have hz : e = 0 := by omega
  subst e
  simp at hc

/-- Combining a single final vertical escape charge with the free
potential charge. The geometric width partition and the energy
transport are explicit premises. -/
theorem free_response_charge (b : ℕ) (W E G V S : ℝ)
    (hpartition : W ≤ E+G) (hescape : E ≤ (2 : ℝ)^b*V)
    (hgood : G ≤ ((2 : ℝ)^(b+1)-1)*S/4) :
    W ≤ (2 : ℝ)^b*V+((2 : ℝ)^(b+1)-1)*S/4 := by
  linarith

end LoopsStationaryCanonicalLift
