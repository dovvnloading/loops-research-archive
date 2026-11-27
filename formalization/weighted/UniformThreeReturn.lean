import FiniteThreeReturnCollars
import ThreeReturnPhysical
import ThreeReturnContraction
import ThreeReturnFullness

/-!
# Uniform physical three-return collars for every period at least three

The finite exact certificates and the analytic tail meet at the same
actual-polynomial interface.  The final existence theorem has only the
integer period as input.  Its domains are canonical pullback components,
and its quantitative invariant is the literal planar variational capacity.
-/

namespace UniformThreeReturn

open Set Function Metric Topology
open LimitingCrestQuadraticReturn ThreeReturnDomain ThreeReturnDegree
open ThreeReturnEstimates ThreeReturnCollar ThreeReturnPhysical
open ThreeReturnContraction ThreeReturnFullness FiniteThreeReturnCollars NearTwoTip
open LoopsFormal.ProtectedCarriers
open scoped Classical

noncomputable section

/-- The finite archived parameter boxes and the rigorously constructed
analytic tail specify the selected actual parameters. -/
def SelectedParameter (p : ℕ) (c : ℝ) : Prop :=
  (p ≤ 16 ∧ CertifiedParameter p c) ∨ (17 ≤ p ∧ ActualTip p c)

theorem exists_selected_parameter (p : ℕ) (hp : 3 ≤ p) :
    ∃ c : ℝ, SelectedParameter p c := by
  by_cases hp16 : p ≤ 16
  · obtain ⟨c, hc⟩ := exists_finite_parameter p hp hp16
    exact ⟨c, Or.inl ⟨hp16, hc⟩⟩
  · have hp17 : 17 ≤ p := by omega
    obtain ⟨c, hc⟩ := exists_actual_tip p hp17
    exact ⟨c, Or.inr ⟨hp17, hc⟩⟩

theorem selected_critical_data {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    0 < criticalValue c p ∧
      criticalValue c (6*p) + criticalValue c (3*p) = 0 ∧
      criticalValue c (3*p) < 0 := by
  rcases hc with ⟨hp16, hc⟩ | ⟨_, hc⟩
  · have hsign := finite_critical_signs hp hp16 hc
    exact ⟨hsign.1, hc.2, hsign.2⟩
  · exact ⟨hc.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1⟩

theorem selected_critical_value_bound {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) : ‖threeReturn c p 0‖ < 1/6 := by
  rcases hc with ⟨hp16, hc⟩ | ⟨hp17, hc⟩
  · exact finite_critical_value_bound hp hp16 hc
  · exact actual_critical_value_bound hp17 hc

/-- The identical positive exclusion margin holds over the entire
closed radial band at every selected period, including all small periods. -/
theorem selected_annular_barrier {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) {z : ℂ}
    (hzlo : (3/20 : ℝ) ≤ ‖z‖) (hzhi : ‖z‖ ≤ 1/6) :
    1/6 + 1/500 < ‖threeReturn c p z‖ := by
  rcases hc with ⟨hp16, hc⟩ | ⟨hp17, hc⟩
  · exact finite_annular_barrier hp hp16 hc hzlo hzhi
  · exact actual_annular_barrier hp17 hc hzlo hzhi

theorem selected_boundary_barrier {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) (z : ℂ) (hz : ‖z‖ = 3/20) :
    1/6 < ‖threeReturn c p z‖ := by
  have h := selected_annular_barrier hp hc hz.ge (by rw [hz]; norm_num)
  linarith

theorem selected_collision_iff {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) {z w : ℂ}
    (hz : ‖z‖ ≤ 1/6) (hw : ‖w‖ ≤ 1/6) :
    threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w := by
  rcases hc with ⟨hp16, hc⟩ | ⟨hp17, hc⟩
  · exact finite_three_return_collision_iff hp hp16 hc hz hw
  · exact actual_three_return_collision_iff hp17 hc hz hw

theorem selected_canonical_collar {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) : CanonicalCollar c p :=
  canonical_collar_of_bounds c p (by omega) (selected_critical_data hp hc).1
    (selected_critical_value_bound hp hc) (selected_boundary_barrier hp hc)
    (selected_collision_iff hp hc)

theorem selected_phase_domains_disjoint {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    Disjoint (source c p) (normalizedReturn c p '' source c p) ∧
    Disjoint (source c p) ((normalizedReturn c p)^[2] '' source c p) ∧
    Disjoint (normalizedReturn c p '' source c p)
      ((normalizedReturn c p)^[2] '' source c p) := by
  have hcanonical := selected_canonical_collar hp hc
  rcases hc with ⟨hp16, hc⟩ | ⟨hp17, hc⟩
  · have hsub : source c p ⊆ ball (0 : ℂ) (1/6) := by
      intro z hz
      have hn : ‖z‖ < 3/20 := by simpa using hcanonical.closure_inside (subset_closure hz)
      rw [mem_ball_zero_iff]
      linarith
    have hz0 : ‖(0 : ℂ)‖ ≤ 1/6 := by norm_num
    have hphase := separated_phase_images (normalizedReturn c p)
      (criticalValue c (2*p)/criticalValue c p)
      (by simpa only [neg_div] using (finite_phase_bounds hp hp16 hc hz0).2.2)
      (fun z hz => ⟨(finite_phase_bounds hp hp16 hc hz).1,
        (finite_phase_bounds hp hp16 hc hz).2.1⟩)
    exact ⟨hphase.1.mono hsub (image_mono hsub),
      hphase.2.1.mono hsub (image_mono hsub),
      hphase.2.2.mono (image_mono hsub) (image_mono hsub)⟩
  · exact actual_phase_domains_disjoint hp17 hc

/-- The source contraction applies to the finite exact cases as well
as to every period in the analytic tail. -/
theorem selected_source_contractible {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) : ContractibleSpace (source c p) :=
  source_contractible_of_bounds c p (by omega) (selected_critical_data hp hc).1.ne'
    (selected_critical_value_bound hp hc) (selected_boundary_barrier hp hc)
    (selected_collision_iff hp hc)

theorem selected_source_simplyConnected {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) : IsSimplyConnected (source c p) := by
  letI := selected_source_contractible hp hc
  change SimplyConnectedSpace (source c p)
  infer_instance

/-- The actual restriction has two local sheets over each regular
target value, at every finite or analytic-tail period. -/
theorem selected_two_sheet_cover {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    IsCoveringMapOn (sourceMap c p)
        {v : ball (0 : ℂ) (1/6) | (v : ℂ) ≠ threeReturn c p 0} ∧
      (∀ v : ball (0 : ℂ) (1/6), (v : ℂ) ≠ threeReturn c p 0 →
        IsEvenlyCovered (sourceMap c p) v (Fin 2)) ∧
      IsCoveringMap
        ({v : ball (0 : ℂ) (1/6) | (v : ℂ) ≠ threeReturn c p 0}.restrictPreimage
          (sourceMap c p)) := by
  obtain ⟨_, _, hcover⟩ := source_two_sheet_cover_of_bounds c p (by omega)
    (selected_critical_data hp hc).1.ne' (selected_critical_value_bound hp hc)
    (selected_boundary_barrier hp hc) (selected_collision_iff hp hc)
  exact hcover

/-- Fullness, connected physical collar, and the two actual complementary
components hold uniformly over the complete selected family. -/
theorem selected_physical_collar_topology {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    planarFill (closure (source c p)) = closure (source c p) ∧
    IsConnected (physicalTarget c p \ closure (physicalSource c p)) ∧
    ∀ z ∈ (physicalTarget c p \ closure (physicalSource c p))ᶜ,
      connectedComponentIn (physicalTarget c p \ closure (physicalSource c p))ᶜ z =
        if z ∈ closure (physicalSource c p) then closure (physicalSource c p)
        else (physicalTarget c p)ᶜ :=
  physical_collar_topology_of_bounds c p (by omega) (selected_critical_data hp hc).1
    (selected_critical_value_bound hp hc) (selected_boundary_barrier hp hc)
    (selected_collision_iff hp hc)

/-- The literal physical collar is an open connected ring with exactly
two complementary components; this includes every small period. -/
theorem selected_physical_ring_domain {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    IsOpen (physicalTarget c p \ closure (physicalSource c p)) ∧
    IsConnected (physicalTarget c p \ closure (physicalSource c p)) ∧
    {C : Set ℂ | ∃ z ∈ (physicalTarget c p \ closure (physicalSource c p))ᶜ,
      connectedComponentIn (physicalTarget c p \ closure (physicalSource c p))ᶜ z = C}.ncard = 2 :=
  physical_ring_domain_of_bounds c p (by omega) (selected_critical_data hp hc).1
    (selected_critical_value_bound hp hc) (selected_boundary_barrier hp hc)
    (selected_collision_iff hp hc)

/-- All geometric and quantitative conclusions are bundled for the
actual selected parameter; the capacity fields are inherited unchanged. -/
structure UniformCollar (c : ℝ) (p : ℕ) : Prop extends CanonicalCollar c p where
  selected : SelectedParameter p c
  critical_relation : criticalValue c (6*p) + criticalValue c (3*p) = 0
  third_return_negative : criticalValue c (3*p) < 0
  contractible_source : ContractibleSpace (source c p)
  full_closure : planarFill (closure (source c p)) = closure (source c p)
  connected_collar : IsConnected (physicalTarget c p \ closure (physicalSource c p))
  open_collar : IsOpen (physicalTarget c p \ closure (physicalSource c p))
  complementary_component_count :
    {C : Set ℂ | ∃ z ∈ (physicalTarget c p \ closure (physicalSource c p))ᶜ,
      connectedComponentIn (physicalTarget c p \ closure (physicalSource c p))ᶜ z = C}.ncard = 2
  complement_components : ∀ z ∈ (physicalTarget c p \ closure (physicalSource c p))ᶜ,
    connectedComponentIn (physicalTarget c p \ closure (physicalSource c p))ᶜ z =
      if z ∈ closure (physicalSource c p) then closure (physicalSource c p)
      else (physicalTarget c p)ᶜ
  physical_fibers : ∀ y ∈ physicalTarget c p,
    {z : ℂ | z ∈ physicalSource c p ∧ ((quadraticMap c)^[3*p]) z = y}.ncard =
      if y = ((quadraticMap c)^[3*p]) 0 then 1 else 2
  phase_disjoint :
    Disjoint (source c p) (normalizedReturn c p '' source c p) ∧
    Disjoint (source c p) ((normalizedReturn c p)^[2] '' source c p) ∧
    Disjoint (normalizedReturn c p '' source c p)
      ((normalizedReturn c p)^[2] '' source c p)

theorem selected_uniform_collar {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) : UniformCollar c p := by
  have hcanonical := selected_canonical_collar hp hc
  have hdata := selected_critical_data hp hc
  have htop := selected_physical_collar_topology hp hc
  have hring := selected_physical_ring_domain hp hc
  refine ⟨hcanonical, hc, hdata.2.1, hdata.2.2,
    selected_source_contractible hp hc, htop.1, htop.2.1, hring.1, hring.2.2, htop.2.2, ?_,
    selected_phase_domains_disjoint hp hc⟩
  intro y hy
  apply physical_fiber_ncard c p (by omega) hcanonical ?_ hy
  intro z w hz hw
  have hnorm {u : ℂ} (hu : u ∈ source c p) : ‖u‖ ≤ 1/6 := by
    have h := hcanonical.closure_inside (subset_closure hu)
    have hn : ‖u‖ < 3/20 := by simpa using h
    linarith
  exact selected_collision_iff hp hc (hnorm hz) (hnorm hw)

/-- Every integer period at least three has a selected actual signed tip
with a canonical physical collar, exact two-sheet fibers, contractible
source, full closure, and the uniform reciprocal-capacity bound `>1/60`. -/
theorem exists_uniform_physical_collar (p : ℕ) (hp : 3 ≤ p) :
    ∃ c : ℝ, UniformCollar c p := by
  obtain ⟨c, hc⟩ := exists_selected_parameter p hp
  exact ⟨c, selected_uniform_collar hp hc⟩

end
end UniformThreeReturn
