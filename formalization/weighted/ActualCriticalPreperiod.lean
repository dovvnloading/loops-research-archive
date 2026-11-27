import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import ActualFullCycle

/-!
# Exact entrance, orbit collisions, and finite critical-orbit census

A nonperiodic predecessor of a periodic point enters its cycle at the
next iterate.  The resulting portrait determines every equality in the
forward orbit and the size of the complete finite orbit.  The distinct
quadratic predecessors used below are the opposite signed tip points.

The predecessor argument extends the one already used in
`ParabolicTipPeriod.critical_preperiod_of_shot`; its application here is to
the actual near-minus-two family and its full physical return period.
-/

namespace ActualCriticalPreperiod

open Set Function

noncomputable section

/-- An exact first entrance into a cycle with the indicated least period. -/
structure ExactPortrait {α : Type*} (f : α → α) (x : α) (L N : ℕ) : Prop where
  period_pos : 0 < N
  entry_period : minimalPeriod f (f^[L] x) = N
  before_nonperiodic : ∀ m < L, f^[m] x ∉ periodicPts f

/-- A collision with a distinct periodic predecessor locates the first
periodic critical iterate exactly, without a finite collision assumption. -/
theorem portrait_of_collision {α : Type*} {f : α → α} {x u v : α} {L N : ℕ}
    (hN : 0 < N) (hperiod : minimalPeriod f v = N)
    (hlast : f^[L] x = u) (hne : u ≠ v) (himage : f u = f v) :
    ExactPortrait f x (L+1) N := by
  have hv : v ∈ periodicPts f := minimalPeriod_pos_iff_mem_periodicPts.mp
    (by simpa only [hperiod] using hN)
  have hper : IsPeriodicPt f N v := by
    simpa only [hperiod] using isPeriodicPt_minimalPeriod f v
  refine ⟨hN, ?_, ?_⟩
  · rw [iterate_succ_apply', hlast, himage, minimalPeriod_apply hv, hperiod]
  · intro m hm hmem
    obtain ⟨n, hn, hperiodic⟩ := mem_periodicPts.mp hmem
    have hu : IsPeriodicPt f n u := by
      have h := hperiodic.apply_iterate (L-m)
      change IsPeriodicPt f n (f^[L-m] (f^[m] x)) at h
      rwa [← iterate_add_apply, Nat.sub_add_cancel (by omega : m ≤ L), hlast] at h
    exact hne (hu.eq_of_apply_eq hper hn hN himage)

namespace ExactPortrait

variable {α : Type*} {f : α → α} {x : α} {L N : ℕ}

theorem entry_mem (h : ExactPortrait f x L N) : f^[L] x ∈ periodicPts f :=
  minimalPeriod_pos_iff_mem_periodicPts.mp (by rw [h.entry_period]; exact h.period_pos)

/-- Every point after first entrance has the same exact physical period. -/
theorem period_after (h : ExactPortrait f x L N) {m : ℕ} (hm : L ≤ m) :
    minimalPeriod f (f^[m] x) = N := by
  rw [← Nat.sub_add_cancel hm, iterate_add_apply,
    minimalPeriod_apply_iterate h.entry_mem, h.entry_period]

/-- The first entrance time separates all transient and periodic points. -/
theorem periodic_iff (h : ExactPortrait f x L N) (m : ℕ) :
    f^[m] x ∈ periodicPts f ↔ L ≤ m := by
  constructor
  · intro hm
    by_contra hn
    exact h.before_nonperiodic m (Nat.lt_of_not_ge hn) hm
  · intro hm
    apply minimalPeriod_pos_iff_mem_periodicPts.mp
    rw [h.period_after hm]
    exact h.period_pos

private theorem eq_after_iff (h : ExactPortrait f x L N) {i j : ℕ}
    (hi : L ≤ i) (hj : L ≤ j) :
    f^[i] x = f^[j] x ↔ (i-L)%N = (j-L)%N := by
  have hleft : f^[i] x = f^[(i-L)%N] (f^[L] x) := by
    rw [← h.entry_period, iterate_mod_minimalPeriod_eq,
      ← iterate_add_apply, Nat.sub_add_cancel hi]
  have hright : f^[j] x = f^[(j-L)%N] (f^[L] x) := by
    rw [← h.entry_period, iterate_mod_minimalPeriod_eq,
      ← iterate_add_apply, Nat.sub_add_cancel hj]
  rw [hleft, hright]
  exact iterate_eq_iterate_iff_of_lt_minimalPeriod
    (by rw [h.entry_period]; exact Nat.mod_lt _ h.period_pos)
    (by rw [h.entry_period]; exact Nat.mod_lt _ h.period_pos)

private theorem no_early_collision (h : ExactPortrait f x L N) {i j : ℕ}
    (hi : i < L) (hij : i < j) : f^[i] x ≠ f^[j] x := by
  intro heq
  have hper : IsPeriodicPt f (j-i) (f^[i] x) := by
    change f^[j-i] (f^[i] x) = f^[i] x
    rw [← iterate_add_apply, Nat.sub_add_cancel hij.le, heq]
  exact h.before_nonperiodic i hi (mk_mem_periodicPts (Nat.sub_pos_of_lt hij) hper)

/-- Complete classification of all forward-orbit collisions. -/
theorem orbit_eq_iff (h : ExactPortrait f x L N) (i j : ℕ) :
    f^[i] x = f^[j] x ↔
      i = j ∨ (L ≤ i ∧ L ≤ j ∧ (i-L)%N = (j-L)%N) := by
  by_cases heq : i = j
  · subst j
    simp
  by_cases hi : L ≤ i
  · by_cases hj : L ≤ j
    · simp only [heq, false_or, hi, hj, true_and]
      exact h.eq_after_iff hi hj
    · have hne := h.no_early_collision (Nat.lt_of_not_ge hj) (by omega : j < i)
      simp only [heq, false_or, hj, false_and, and_false, iff_false]
      exact Ne.symm hne
  · have hne : f^[i] x ≠ f^[j] x := by
      rcases lt_or_gt_of_ne heq with hij | hij
      · exact h.no_early_collision (Nat.lt_of_not_ge hi) hij
      · exact Ne.symm (h.no_early_collision (by omega) hij)
    simp only [heq, false_or, hi, false_and, iff_false]
    exact hne

/-- The complete transient tail and one whole cycle have no repeated points. -/
theorem injective_prefix (h : ExactPortrait f x L N) :
    Set.InjOn (fun i => f^[i] x) (Set.Iio (L+N)) := by
  intro i hi j hj heq
  rcases (h.orbit_eq_iff i j).mp heq with heq | ⟨hiL, hjL, hmod⟩
  · exact heq
  · have hiN : i-L < N := by change i < L+N at hi; omega
    have hjN : j-L < N := by change j < L+N at hj; omega
    rw [Nat.mod_eq_of_lt hiN, Nat.mod_eq_of_lt hjN] at hmod
    omega

/-- The infinite forward orbit is exactly this finite initial prefix. -/
theorem range_eq_prefix (h : ExactPortrait f x L N) :
    Set.range (fun i => f^[i] x) = (fun i => f^[i] x) '' Set.Iio (L+N) := by
  apply Set.Subset.antisymm
  · rintro y ⟨i, rfl⟩
    by_cases hi : i < L
    · exact ⟨i, by change i < L+N; omega, rfl⟩
    · let j := L+(i-L)%N
      have hj : j < L+N := by
        dsimp [j]
        exact Nat.add_lt_add_left (Nat.mod_lt _ h.period_pos) L
      refine ⟨j, hj, ?_⟩
      apply (h.orbit_eq_iff j i).mpr
      right
      refine ⟨by dsimp [j]; omega, by omega, ?_⟩
      simp [j]
  · exact Set.image_subset_range _ _

/-- Exact cardinality of the complete orbit, including its initial point. -/
theorem orbit_ncard (h : ExactPortrait f x L N) :
    (Set.range (fun i => f^[i] x)).ncard = L+N := by
  rw [h.range_eq_prefix, h.injective_prefix.ncard_image]
  have hs : Set.Iio (L+N) = (↑(Finset.range (L+N)) : Set ℕ) := by ext i; simp
  rw [hs, Set.ncard_coe_finset, Finset.card_range]

/-- The finite orbit statement includes the complete infinite-time range. -/
theorem orbit_finite (h : ExactPortrait f x L N) :
    (Set.range (fun i => f^[i] x)).Finite := by
  rw [h.range_eq_prefix]
  exact (Set.finite_Iio (L+N)).image _

/-- Removing the initial transient point removes exactly one orbit point. -/
theorem postcritical_ncard (h : ExactPortrait f x L N) (hL : 0 < L) :
    (Set.range (fun i => f^[i+1] x)).ncard = L+N-1 := by
  have hshift : ExactPortrait f (f x) (L-1) N := by
    refine ⟨h.period_pos, ?_, ?_⟩
    · rw [← iterate_succ_apply, show (L-1).succ = L by omega, h.entry_period]
    · intro m hm
      rw [← iterate_succ_apply]
      exact h.before_nonperiodic (m+1) (by omega)
  have hrange : (fun i => f^[i+1] x) = (fun i => f^[i] (f x)) := by
    funext i
    exact iterate_succ_apply f i x
  rw [hrange, hshift.orbit_ncard]
  omega

end ExactPortrait

open LimitingCrestQuadraticReturn ThreeReturnParent UniformThreeReturn ActualFullCycle

/-- The actual signed-tip critical point first enters its eventual cycle
at time 3p+1, and that cycle has exact period 3p for the original map. -/
theorem actual_critical_portrait {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c)
    (hfirst : ∀ r : ℕ, 0 < r → r < p →
      Disjoint (physicalParentSource c p)
        (((quadraticMap c)^[r]) '' physicalParentSource c p)) :
    ExactPortrait (quadraticMap c) 0 (3*p+1) (3*p) := by
  have hnegative := (selected_uniform_collar hp hc).third_return_negative
  have hne : ((quadraticMap c)^[3*p]) 0 ≠ -((quadraticMap c)^[3*p]) 0 := by
    intro heq
    have hr := congrArg Complex.re heq
    simp only [quadratic_iterate_zero, Complex.neg_re, Complex.ofReal_re] at hr
    linarith
  exact portrait_of_collision (by omega : 0 < 3*p)
    (actual_signed_tip_minimalPeriod hp hc hfirst) rfl hne
    (by simp only [quadraticMap, neg_sq])

/-- Every physical critical-orbit collision is determined by the exact
transient tail and the residue in the cycle of length 3p. -/
theorem actual_critical_orbit_eq_iff {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c)
    (hfirst : ∀ r : ℕ, 0 < r → r < p →
      Disjoint (physicalParentSource c p)
        (((quadraticMap c)^[r]) '' physicalParentSource c p)) (i j : ℕ) :
    ((quadraticMap c)^[i]) 0 = ((quadraticMap c)^[j]) 0 ↔
      i = j ∨ (3*p+1 ≤ i ∧ 3*p+1 ≤ j ∧
        (i-(3*p+1))%(3*p) = (j-(3*p+1))%(3*p)) :=
  (actual_critical_portrait hp hc hfirst).orbit_eq_iff i j

/-- The first 6p+1 critical-orbit points are all distinct. -/
theorem actual_critical_prefix_injective {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c)
    (hfirst : ∀ r : ℕ, 0 < r → r < p →
      Disjoint (physicalParentSource c p)
        (((quadraticMap c)^[r]) '' physicalParentSource c p)) :
    Set.InjOn (fun i => ((quadraticMap c)^[i]) 0) (Set.Iio (6*p+1)) := by
  simpa only [show 3*p+1+3*p = 6*p+1 by omega] using
    (actual_critical_portrait hp hc hfirst).injective_prefix

/-- Exact cardinality of the entire actual critical orbit, including zero. -/
theorem actual_critical_orbit_ncard {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c)
    (hfirst : ∀ r : ℕ, 0 < r → r < p →
      Disjoint (physicalParentSource c p)
        (((quadraticMap c)^[r]) '' physicalParentSource c p)) :
    (Set.range (fun i => ((quadraticMap c)^[i]) 0)).ncard = 6*p+1 := by
  rw [(actual_critical_portrait hp hc hfirst).orbit_ncard]
  omega

/-- The full postcritical set of the actual quadratic has exactly 6p points. -/
theorem actual_postcritical_ncard {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c)
    (hfirst : ∀ r : ℕ, 0 < r → r < p →
      Disjoint (physicalParentSource c p)
        (((quadraticMap c)^[r]) '' physicalParentSource c p)) :
    (Set.range (fun i => ((quadraticMap c)^[i+1]) 0)).ncard = 6*p := by
  rw [(actual_critical_portrait hp hc hfirst).postcritical_ncard (by omega)]
  omega

end
end ActualCriticalPreperiod
