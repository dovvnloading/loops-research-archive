import QuadraticEnlargementDegree

/-!
# An arbitrarily late merger in the actual quadratic inverse image

The map is the literal complex polynomial z ↦ z².  Its inverse images
of 1 are separated over the right half-plane and joined over the whole
plane.  An increasing open connected target exhaustion can postpone
that single merger for any prescribed number of stages.

This is a sharpness example for eventual finite-fiber stabilization.
It rules out a bound on the stabilization stage from the iterate depth
and the size of the inverse fiber alone.  No native virtual-block
realization or marked-access identification is asserted.
-/

namespace LoopsQuadraticDelayedMerger

open Set Function
open LoopsQuadraticCylinderCensus LoopsQuadraticComponentFiberDegree
open LoopsQuadraticCylinderRamification

noncomputable section

def rightHalfPlane : Set ℂ := {z | 0 < z.re}

theorem rightHalfPlane_open : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem rightHalfPlane_connected : IsConnected rightHalfPlane := by
  have hc : Convex ℝ rightHalfPlane :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm
  exact hc.isConnected ⟨1, by norm_num [rightHalfPlane]⟩

/-- The two roots of the same regular target value lie in different
actual pullback components.  The separation is proved from the real
part of the square, with no branch or separation assumption. -/
theorem negative_one_not_in_positive_component :
    (-1 : ℂ) ∉ connectedComponentIn ((quad 0) ⁻¹' rightHalfPlane) 1 := by
  let C := connectedComponentIn ((quad 0) ⁻¹' rightHalfPlane) 1
  have hpos : (1 : ℂ) ∈ C := by
    apply mem_connectedComponentIn
    norm_num [rightHalfPlane, quad]
  have hnonzero : ∀ z ∈ C, z.re ≠ 0 := by
    intro z hz he
    have hs : 0 < (z ^ 2).re := by
      simpa only [Set.mem_preimage, rightHalfPlane, Set.mem_setOf_eq, quad,
        add_zero] using connectedComponentIn_subset ((quad 0) ⁻¹' rightHalfPlane) 1 hz
    rw [pow_two, Complex.mul_re, he] at hs
    nlinarith [sq_nonneg z.im]
  intro hneg
  have hp : 0 < (-1 : ℂ).re :=
    isPreconnected_connectedComponentIn.lt_of_ne
      Complex.continuous_re.continuousOn hnonzero
      ⟨1, hpos, by norm_num⟩ hneg
  norm_num at hp

/-- The component containing 1 has exactly one point over the
regular value 1, before the target crosses the critical value. -/
theorem rightHalfPlane_selected_fiber :
    localFiber 0 1 (connectedComponentIn ((quad 0) ⁻¹' rightHalfPlane) 1) 1 =
      {1} := by
  classical
  ext z
  simp only [mem_localFiber, Finset.mem_singleton, Function.iterate_one]
  constructor
  · rintro ⟨hz, he⟩
    have he' : quad 0 z = quad 0 1 := by simpa [quad] using he
    rcases quadratic_eq_or_neg 0 z 1 he' with h | h
    · exact h
    · subst z
      exact (negative_one_not_in_positive_component hz).elim
  · intro he
    subst z
    constructor
    · apply mem_connectedComponentIn
      norm_num [rightHalfPlane, quad]
    · norm_num [quad]

/-- Over the final target the same two regular inverse points lie
in one component. -/
theorem wholePlane_component :
    connectedComponentIn ((quad 0) ⁻¹' (univ : Set ℂ)) 1 = univ := by
  simp only [Set.preimage_univ, connectedComponentIn_univ,
    PreconnectedSpace.connectedComponent_eq_univ]

theorem wholePlane_selected_fiber :
    localFiber 0 1 (connectedComponentIn ((quad 0) ⁻¹' (univ : Set ℂ)) 1) 1 =
      {1, -1} := by
  classical
  rw [wholePlane_component]
  ext z
  simp only [mem_localFiber, Set.mem_univ, true_and, Function.iterate_one,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro he
    have he' : quad 0 z = quad 0 1 := by simpa [quad] using he
    exact quadratic_eq_or_neg 0 z 1 he'
  · rintro (he | he) <;> subst z <;> norm_num [quad]

def delayedTarget (N k : ℕ) : Set ℂ :=
  if k ≤ N then rightHalfPlane else univ

theorem delayedTarget_monotone (N : ℕ) : Monotone (delayedTarget N) := by
  intro i j hij
  by_cases hj : j ≤ N
  · have hi : i ≤ N := hij.trans hj
    simpa only [delayedTarget, if_pos hi, if_pos hj] using
      (Subset.rfl : rightHalfPlane ⊆ rightHalfPlane)
  · change delayedTarget N i ⊆ if j ≤ N then rightHalfPlane else univ
    rw [if_neg hj]
    exact subset_univ _

theorem delayedTarget_open_connected (N k : ℕ) :
    IsOpen (delayedTarget N k) ∧ IsConnected (delayedTarget N k) := by
  by_cases hk : k ≤ N
  · simpa only [delayedTarget, if_pos hk] using
      And.intro rightHalfPlane_open rightHalfPlane_connected
  · simpa only [delayedTarget, if_neg hk] using
      And.intro (isOpen_univ : IsOpen (univ : Set ℂ))
        (isConnected_univ : IsConnected (univ : Set ℂ))

theorem one_mem_delayedTarget (N k : ℕ) : (1 : ℂ) ∈ delayedTarget N k := by
  by_cases hk : k ≤ N
  · simp only [delayedTarget, if_pos hk]
    norm_num [rightHalfPlane]
  · simp only [delayedTarget, if_neg hk, Set.mem_univ]

theorem delayedTarget_union (N : ℕ) : (⋃ k, delayedTarget N k) = univ := by
  apply Subset.antisymm (subset_univ _)
  intro z _
  apply mem_iUnion.mpr
  refine ⟨N+1, ?_⟩
  simp [delayedTarget]

/-- The merger happens at precisely the prescribed stage N+1,
although the polynomial, iterate depth and regular fiber are fixed. -/
theorem delayed_merger_exact (N k : ℕ) :
    (-1 : ℂ) ∈ connectedComponentIn ((quad 0) ⁻¹' delayedTarget N k) 1 ↔ N < k := by
  by_cases hk : k ≤ N
  · simp only [delayedTarget, if_pos hk]
    exact iff_of_false negative_one_not_in_positive_component (by omega)
  · simp only [delayedTarget, if_neg hk, wholePlane_component, Set.mem_univ,
      true_iff]
    omega

/-- The selected regular-fiber census remains 1 for an arbitrarily
long plateau, then becomes 2.  An observed plateau is not a
certificate excluding future mergers. -/
theorem delayed_fiber_count (N k : ℕ) :
    (localFiber 0 1
      (connectedComponentIn ((quad 0) ⁻¹' delayedTarget N k) 1) 1).card =
        if k ≤ N then 1 else 2 := by
  by_cases hk : k ≤ N
  · simp only [delayedTarget, if_pos hk, rightHalfPlane_selected_fiber,
      Finset.card_singleton]
  · simp only [delayedTarget, if_neg hk, wholePlane_selected_fiber]
    norm_num

/-- Eventual capture of a fixed finite inverse fiber admits no stage
bound uniform over increasing connected open target exhaustions,
already for z² at depth one and the regular target point 1. -/
theorem no_uniform_two_point_stabilization_stage :
    ¬ ∃ B : ℕ, ∀ U : ℕ → Set ℂ,
      Monotone U →
      (∀ k, IsOpen (U k) ∧ IsConnected (U k)) →
      (1 : ℂ) ∈ U 0 → (⋃ k, U k) = univ →
      (-1 : ℂ) ∈ connectedComponentIn ((quad 0) ⁻¹' U B) 1 := by
  rintro ⟨B, hB⟩
  have h := hB (delayedTarget B) (delayedTarget_monotone B)
    (delayedTarget_open_connected B) (one_mem_delayedTarget B 0)
    (delayedTarget_union B)
  exact (Nat.lt_irrefl B) ((delayed_merger_exact B B).mp h)

end

end LoopsQuadraticDelayedMerger
