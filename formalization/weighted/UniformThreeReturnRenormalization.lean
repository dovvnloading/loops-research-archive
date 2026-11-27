import UniformThreeReturn
import FiniteFirstReturnBounds
import ThreeReturnParentTopology
import ThreeReturnRealization

/-!
# The complete uniform physical three-return realization

Every integer period at least three supplies an actual quadratic parameter,
a fixed physical collar, a proper holomorphic three-return with trapped
critical orbit, and an ambient proper degree-two p-return restriction.
Its target and three phases lie in the actual ambient source, and that
ambient source lies in the archive's original p-return component.
-/

namespace UniformThreeReturnRenormalization

open Set Function Metric Topology
open LimitingCrestQuadraticReturn ThreeReturnDomain ThreeReturnDegree
open ThreeReturnCollar ThreeReturnPhysical ThreeReturnParent
open ThreeReturnParentTopology ThreeReturnRealization UniformThreeReturn
open FiniteFirstReturnBounds NearTwoShooting NearTwoTip
open QuadraticCrestDividedDifference

noncomputable section

theorem selected_parent_collision {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) {z w : ℂ}
    (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    normalizedReturn c p z = normalizedReturn c p w ↔ z = w ∨ z = -w := by
  rcases hc with ⟨hp16, hc⟩ | ⟨hp17, hc⟩
  · exact finite_first_return_collision_iff hp hp16 hc hz hw
  · have hband := parameter_band hp17 hc.1
    have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
      simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
    exact normalized_return_collision_iff c p (by omega)
      ⟨hband.1, by linarith [hband.2]⟩ hc.2.1 hsmall hc.2.2.2.1 hz hw

theorem selected_parent_restriction {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) : ParentRestriction c p := by
  have hcanonical := selected_canonical_collar hp hc
  rcases hc with ⟨hp16, hc⟩ | ⟨hp17, hc⟩
  · apply parent_restriction_of_bounds c p (by omega) hcanonical
    · intro z hz
      have h := finite_first_return_sphere_barrier hp hp16 hc hz
      linarith
    · exact finite_first_return_collision_iff hp hp16 hc
    · exact fun _ hz => finite_parent_phase_control hp hp16 hc hz
  · exact actual_parent_restriction hp17 hc

theorem selected_parent_scale_bound {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    criticalValue c p * (23/20) < archivedTargetRadius p := by
  rcases hc with ⟨hp16, hc⟩ | ⟨hp17, hc⟩
  · exact finite_parent_scale_bound hp hp16 hc
  · exact actual_parent_scale_bound hp17 hc

/-- The entire closed physical target of the three-return already lies
inside the actual ambient p-return source. -/
theorem physical_target_closure_subset_parent (c : ℝ) (p : ℕ)
    (hd : 0 < criticalValue c p) (hparent : ParentRestriction c p) :
    closure (physicalTarget c p) ⊆ physicalParentSource c p := by
  let d := criticalValue c p
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hclosed : closure (physicalTarget c p) ⊆ closedBall (0 : ℂ) (d/6) :=
    isClosed_closedBall.closure_subset_iff.mpr ball_subset_closedBall
  intro z hz
  have hn : ‖z‖ ≤ d/6 := by simpa using hclosed hz
  refine ⟨z / (d : ℂ), hparent.target_closure_subset ?_, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    linarith
  · change (d : ℂ) * (z / (d : ℂ)) = z
    field_simp [hdC]

/-- A complete actual-polynomial realization of the fixed collar.
The capacity theorem concerns this literal physical source closure and
target; no modulus identification is added to the variational definition. -/
structure PhysicalRenormalization (c : ℝ) (p : ℕ) : Prop where
  collar : UniformCollar c p
  parent : ParentRestriction c p
  holomorphic : Differentiable ℂ ((quadraticMap c)^[3*p])
  proper : IsProperMap (physicalMap c p collar.toCanonicalCollar)
  source_contractible : ContractibleSpace (physicalSource c p)
  parent_contractible : ContractibleSpace (parentSource c p)
  physical_parent_contractible : ContractibleSpace (physicalParentSource c p)
  target_closure_in_parent : closure (physicalTarget c p) ⊆ physicalParentSource c p
  parent_in_archived_source : physicalParentSource c p ⊆ archivedParentSource c p
  phases_in_archived_source : ∀ n : ℕ, n ≤ 2 →
    ((quadraticMap c)^[n*p]) '' physicalSource c p ⊆ archivedParentSource c p
  physical_phase_disjoint :
    Disjoint (physicalSource c p) (((quadraticMap c)^[p]) '' physicalSource c p) ∧
    Disjoint (physicalSource c p) (((quadraticMap c)^[2*p]) '' physicalSource c p) ∧
    Disjoint (((quadraticMap c)^[p]) '' physicalSource c p)
      (((quadraticMap c)^[2*p]) '' physicalSource c p)
  critical_orbit_in_source : ∀ n : ℕ,
    ((quadraticMap c)^[(3*p)*n]) 0 ∈ physicalSource c p
  normalized_critical_tail : ∀ n : ℕ,
    ((threeReturn c p)^[n+2]) 0 = -threeReturn c p 0

/-- The finite certificates and analytic tail supply every hypothesis
of the actual physical and ambient realization, without domain shrinking. -/
theorem selected_physical_renormalization {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) : PhysicalRenormalization c p := by
  have hcollar := selected_uniform_collar hp hc
  have hcanonical := hcollar.toCanonicalCollar
  have hparent := selected_parent_restriction hp hc
  have hinside := physical_parent_subset_archived c p hcanonical.scale_pos hparent
    (selected_parent_scale_bound hp hc)
  have hp0 : 0 < p := by omega
  have hcollision := @selected_collision_iff p hp c hc
  refine {
    collar := hcollar
    parent := hparent
    holomorphic := physical_return_differentiable c p
    proper := physicalMap_proper hcanonical
    source_contractible := physical_source_contractible hcanonical hcollar.contractible_source
    parent_contractible := parent_contractible_of_bounds c p hp0 hcanonical.scale_pos.ne'
      hparent (selected_parent_collision hp hc)
    physical_parent_contractible := physical_parent_contractible_of_bounds c p hp0
      hcanonical.scale_pos.ne' hparent (selected_parent_collision hp hc)
    target_closure_in_parent := physical_target_closure_subset_parent c p hcanonical.scale_pos hparent
    parent_in_archived_source := hinside
    phases_in_archived_source := fun n hn => (hparent.physical_phase_subset n hn).trans hinside
    physical_phase_disjoint := physical_phases_disjoint c p hcanonical.scale_pos.ne' hcollar.phase_disjoint
    critical_orbit_in_source := physical_critical_orbit_trapped c p hp0 hcanonical
      hcollar.critical_relation hcollision
    normalized_critical_tail :=
      (critical_orbit_trapped c p hp0 hcanonical hcollar.critical_relation hcollision).2.2.2
  }

/-- For every integer period at least three there is an actual quadratic
parameter realizing the canonical physical collar, with reciprocal
variational capacity greater than 1/60, genuine ring topology, exact
two-sheet fibers, trapped critical orbit, and fixed ambient phase inclusion. -/
theorem exists_uniform_three_return (p : ℕ) (hp : 3 ≤ p) :
    ∃ c : ℝ, PhysicalRenormalization c p := by
  obtain ⟨c, hc⟩ := exists_selected_parameter p hp
  exact ⟨c, selected_physical_renormalization hp hc⟩

end
end UniformThreeReturnRenormalization
