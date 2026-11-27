import ThreeReturnFullness
import ThreeReturnRealization
import ActualFilledReturn

/-!
# No holes in the actual trapped three-return core

Maximum modulus on a hypothetical bounded complementary component
controls every entire return iterate.  Exact source-fiber exhaustion
then puts that component into the trapped set itself.  Thus fullness is
proved for the original trapped set, without replacing it by a hull.
-/

namespace ActualFilledReturnFullness

open Set Function Metric Bornology Topology
open LoopsFormal.ProtectedCarriers LoopsQuadraticCylinderCensus
open ThreeReturnFullness

noncomputable section

private theorem complementary_component_frontier {K : Set ℂ} (hK : IsClosed K)
    (z : ℂ) : frontier (connectedComponentIn Kᶜ z) ⊆ K := by
  intro w hw
  by_contra hwK
  have ho : IsOpen (connectedComponentIn Kᶜ z) :=
    hK.isOpen_compl.connectedComponentIn
  have hc := open_component_relative_closed Kᶜ hK.isOpen_compl z
  change w ∈ closure (connectedComponentIn Kᶜ z) ∧
    w ∉ interior (connectedComponentIn Kᶜ z) at hw
  exact hw.2 (ho.interior_eq.symm ▸ hc ⟨hw.1, hwK⟩)

/-- An entire return with complete source-fiber exhaustion cannot have
a bounded hole in its closed trapped core. -/
theorem entire_exhausted_core_full (H : ℂ → ℂ) (S K : Set ℂ) (r : ℝ)
    (hH : Differentiable ℂ H) (hK : IsClosed K)
    (hcore : K = {z | ∀ n : ℕ, (H^[n]) z ∈ S})
    (hS : S ⊆ ball 0 r)
    (hexhaust : ∀ z : ℂ, ‖z‖ ≤ r → ‖H z‖ < r → z ∈ S) :
    planarFill K = K := by
  apply Subset.antisymm _ (planarFill_extensive K)
  intro z hz
  change IsBounded (connectedComponentIn Kᶜ z) at hz
  by_contra hzK
  let U := connectedComponentIn Kᶜ z
  have hzU : z ∈ U := mem_connectedComponentIn hzK
  have hbound (n : ℕ) : ‖(H^[n]) z‖ < r := by
    obtain ⟨w, hw, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm hz
      ⟨z, hzU⟩ (hH.iterate n).diffContOnCl
    have hwK : w ∈ K := complementary_component_frontier hK z hw
    rw [hcore] at hwK
    have hwS : (H^[n]) w ∈ S := hwK n
    have hwbound : ‖(H^[n]) w‖ < r := by simpa using hS hwS
    exact (hmax (subset_closure hzU)).trans_lt hwbound
  apply hzK
  rw [hcore]
  intro n
  apply hexhaust _ (hbound n).le
  simpa only [iterate_succ_apply'] using hbound (n+1)

/-- A bounded plane set with connected exterior already equals its
filled hull.  This lets physical scaling preserve the same literal set. -/
theorem full_of_bounded_connected_complement {K : Set ℂ} (hK : IsBounded K)
    (hconn : IsConnected Kᶜ) : planarFill K = K := by
  apply Subset.antisymm _ (planarFill_extensive K)
  intro z hz
  change IsBounded (connectedComponentIn Kᶜ z) at hz
  by_contra hzK
  have hsub : Kᶜ ⊆ connectedComponentIn Kᶜ z :=
    hconn.isPreconnected.subset_connectedComponentIn hzK (Subset.refl _)
  have hb : IsBounded Kᶜ := hz.subset hsub
  exact NormedSpace.unbounded_univ ℝ ℂ (by simpa using hK.union hb)

open LimitingCrestQuadraticReturn NearTwoTip ThreeReturnDomain ThreeReturnDegree
open ThreeReturnCollar ThreeReturnRealization ActualFilledReturn

/-- The actual normalized nonescaping set is full.  The proof uses its
constructed compactness and complete fiber exhaustion at the same parameter. -/
theorem actual_normalizedCore_full {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    planarFill (normalizedCore c p) = normalizedCore c p := by
  have hcan := actual_canonical_collar hp hc
  have hF : Differentiable ℂ (normalizedReturn c p) :=
    fun z => (normalized_return_hasDerivAt c p (by omega) hc.2.1.ne' z).differentiableAt
  have hH : Differentiable ℂ (threeReturn c p) := by
    simpa [threeReturn, iterate_succ_apply', Function.comp_def] using hF.comp (hF.comp hF)
  apply entire_exhausted_core_full (threeReturn c p) (source c p)
    (normalizedCore c p) (1/6) hH (actual_normalizedCore_compact hp hc).isClosed rfl
  · intro z hz
    have hn : ‖z‖ < 3/20 := by simpa using hcan.closure_inside (subset_closure hz)
    rw [mem_ball_zero_iff]
    linarith
  · intro z hz hvalue
    exact canonical_source_exhaustion c p (by omega) hcan
      (actual_three_return_collision_iff hp hc) hz hvalue

/-- The actual normalized core has a connected exterior. -/
theorem actual_normalizedCore_exterior_connected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsConnected (normalizedCore c p)ᶜ :=
  full_bounded_complement_connected (actual_normalizedCore_compact hp hc).isBounded
    (actual_normalizedCore_full hp hc)

/-- The genuine physical scaling preserves the connected exterior. -/
theorem actual_physicalCore_exterior_connected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsConnected (physicalCore c p)ᶜ := by
  have hd : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hc.2.1.ne'
  let e := Homeomorph.mulLeft₀ (criticalValue c p : ℂ) hd
  have he : physicalCore c p = e '' normalizedCore c p := rfl
  rw [he, ← e.image_compl]
  exact (actual_normalizedCore_exterior_connected hp hc).image e e.continuous.continuousOn

/-- The physical filled core is full in the original quadratic plane. -/
theorem actual_physicalCore_full {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : planarFill (physicalCore c p) = physicalCore c p :=
  full_of_bounded_connected_complement (actual_physicalCore_compact hp hc).isBounded
    (actual_physicalCore_exterior_connected hp hc)

end
end ActualFilledReturnFullness
