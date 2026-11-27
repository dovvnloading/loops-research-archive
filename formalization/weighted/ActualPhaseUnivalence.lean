import ActualFullCycle

/-!
# The single critical phase of the actual physical cycle

The exact signed fibers of the complete return force the original
quadratic map to be injective on every positive intermediate phase.
Full phase separation then locates the unique critical phase at the
canonical source itself.  All sets are the complete physical domains.
-/

namespace ActualPhaseUnivalence

open Set Function
open LimitingCrestQuadraticReturn ThreeReturnDomain ThreeReturnCollar
open ThreeReturnPhysical ThreeReturnParent UniformThreeReturn ActualFullCycle
open LoopsStationarySeparatorTransport

noncomputable section

private theorem selected_physical_collision {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) {z w : ℂ}
    (hz : z ∈ physicalSource c p) (hw : w ∈ physicalSource c p) :
    ((quadraticMap c)^[3*p]) z = ((quadraticMap c)^[3*p]) w ↔
      z = w ∨ z = -w := by
  have hcan := selected_canonical_collar hp hc
  have hnorm {u : ℂ} (hu : u ∈ source c p) : ‖u‖ ≤ (1/6 : ℝ) := by
    have hn : ‖u‖ < (3/20 : ℝ) := by
      simpa using hcan.closure_inside (subset_closure hu)
    linarith
  exact physical_collision_iff c p hcan.scale_pos
    (fun hu hv => selected_collision_iff hp hc (hnorm hu) (hnorm hv)) hz hw

private theorem quadratic_deriv (c : ℝ) (z : ℂ) :
    deriv (quadraticMap c) z = 2*z := by
  have h : HasDerivAt (quadraticMap c) (2*z) z := by
    change HasDerivAt (fun w : ℂ => w^2 + (c : ℂ)) (2*z) z
    exact (((hasDerivAt_id z).pow 2).add_const (c : ℂ)).congr_deriv (by simp)
  exact h.deriv

/-- After the critical step, every complete canonical phase before
the return is mapped injectively by the original quadratic polynomial.
The argument uses the actual signed return fibers, without assuming
intermediate phase separation. -/
theorem actual_positive_phase_injOn {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) (i : ℕ) (hi : 0 < i) (hip : i < 3*p) :
    InjOn (quadraticMap c) (((quadraticMap c)^[i]) '' physicalSource c p) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ he
  have hlast : ((quadraticMap c)^[3*p]) a = ((quadraticMap c)^[3*p]) b := by
    have h := congrArg ((quadraticMap c)^[3*p-(i+1)]) he
    rw [← iterate_succ_apply' (quadraticMap c) i a,
      ← iterate_succ_apply' (quadraticMap c) i b,
      ← iterate_add_apply, ← iterate_add_apply,
      Nat.sub_add_cancel (by omega : i+1 ≤ 3*p)] at h
    exact h
  rcases (selected_physical_collision hp hc ha hb).mp hlast with hab | hab
  · exact congrArg ((quadraticMap c)^[i]) hab
  · rw [hab]
    exact quadratic_positive_iterate_even (c : ℂ) i hi b

/-- Every point of a positive physical phase has nonzero derivative
for the original quadratic map, once the actual first-return exclusion
on the parent has been supplied. -/
theorem actual_positive_phase_noncritical {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c)
    (hfirst : ∀ r : ℕ, 0 < r → r < p →
      Disjoint (physicalParentSource c p)
        (((quadraticMap c)^[r]) '' physicalParentSource c p))
    (i : ℕ) (hi : 0 < i) (hip : i < 3*p) {z : ℂ}
    (hz : z ∈ ((quadraticMap c)^[i]) '' physicalSource c p) :
    deriv (quadraticMap c) z ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro he
    apply disjoint_left.mp (actual_source_no_early_contact hp hc hfirst i hi hip)
      (physical_zero (selected_canonical_collar hp hc))
    simpa only [he] using hz
  rw [quadratic_deriv]
  exact mul_ne_zero (by norm_num) hz0

/-- Among all the actual 3p phase domains, the canonical phase zero
is exactly the one containing a critical point of the original map. -/
theorem actual_phase_critical_iff {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c)
    (hfirst : ∀ r : ℕ, 0 < r → r < p →
      Disjoint (physicalParentSource c p)
        (((quadraticMap c)^[r]) '' physicalParentSource c p))
    (i : ℕ) (hip : i < 3*p) :
    (∃ z ∈ ((quadraticMap c)^[i]) '' physicalSource c p,
      deriv (quadraticMap c) z = 0) ↔ i = 0 := by
  constructor
  · rintro ⟨z, hz, hd⟩
    by_contra hi
    exact actual_positive_phase_noncritical hp hc hfirst i (by omega) hip hz hd
  · rintro rfl
    refine ⟨0, ?_, ?_⟩
    · simpa only [iterate_zero, image_id] using
        physical_zero (selected_canonical_collar hp hc)
    · rw [quadratic_deriv]
      simp

end
end ActualPhaseUnivalence
