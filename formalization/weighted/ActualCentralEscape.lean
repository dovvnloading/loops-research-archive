import ActualCentralSlit
import ComplexEscapeSequence
import SlitGreenBarrier

/-!
# Uniform complex escape for the actual central return

The seven-to-six inequality concerns the literal three-return polynomial on
its complete closed control disk. The critical orbit fixes the slit and its
exterior amplitude. The interval identification is a canonical-object bridge;
the new quantitative claim is the uniform complex amplification and its
finite escape certificate.
-/

namespace ActualCentralEscape

open Set Function Metric
open LimitingCrestQuadraticReturn NearTwoTip GlobalCrestSourceGates
open ActualThreeReturnNormalization ThreeReturnDomain ThreeReturnCollar
open ThreeReturnEstimates ActualCentralSlit LoopsParabolic
open SlitJoukowski ComplexEscapeSequence

noncomputable section

private theorem actual_threeReturn_differentiable (c : ℝ) (p : ℕ) :
    Differentiable ℂ (threeReturn c p) := by
  have hq : Differentiable ℂ (quadraticMap c) := by
    change Differentiable ℂ (fun z : ℂ => z^2 + (c : ℂ))
    exact (differentiable_id.pow 2).add_const (c : ℂ)
  have hm : Differentiable ℂ (fun z : ℂ => (criticalValue c p : ℂ) * z) := by
    fun_prop
  have hF : Differentiable ℂ (normalizedReturn c p) := by
    exact ((hq.iterate p).comp hm).div_const (criticalValue c p : ℂ)
  exact hF.iterate 3

private theorem source_norm_lt_control {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ source c p) :
    ‖z‖ < 1/6 := by
  have h := (actual_canonical_collar hp hc).closure_inside (subset_closure hz)
  have hn : ‖z‖ < 3/20 := by simpa only [mem_ball, dist_zero_right] using h
  linarith

/-- Native complex amplification, including the complete control circle.
The map, radius, and slit are all determined by the actual quadratic orbit. -/
theorem actual_amplification {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 1/6) :
    slitAmplitude (centralRadius c p) z ^ 7 ≤
      slitAmplitude (centralRadius c p) (threeReturn c p z) ^ 6 := by
  have ht := centralRadius_bounds hp hc
  have houter : ∀ w : ℂ, ‖w‖ = 1/6 → (1/4 : ℝ) ≤ ‖threeReturn c p w‖ := by
    intro w hw
    exact (actual_outer_circle_barrier hp hc
      (show ‖w‖ = outerRadius from hw)).le
  by_cases hstrict : ‖z‖ < 1/6
  · exact SlitGreenBarrier.slit_amplification ht.1 ht.2
      (threeReturn c p) (actual_threeReturn_differentiable c p)
      (slit_invariant hp hc)
      (fun w hw hmem => (inverse_slit_iff hp hc hw.le).mp hmem)
      houter hstrict
  · have heq : ‖z‖ = 1/6 := le_antisymm hz (le_of_not_gt hstrict)
    have hu := slitAmplitude_upper ht.1 hz
    have hl := slitAmplitude_lower (centralRadius_pos hp hc) ht.2 (houter z heq)
    have hnonneg : 0 ≤ slitAmplitude (centralRadius c p) z :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (slitAmplitude_ge_one _ _)
    calc
      slitAmplitude (centralRadius c p) z ^ 7 ≤ (16/5 : ℝ)^7 :=
        pow_le_pow_left₀ hnonneg hu 7
      _ ≤ (39/10 : ℝ)^6 := by norm_num
      _ ≤ slitAmplitude (centralRadius c p) (threeReturn c p z) ^ 6 :=
        pow_le_pow_left₀ (by norm_num) hl 6

/-- The exact exponential power law through every finite surviving orbit
segment. The hypothesis concerns the full literal complex iterates. -/
theorem actual_power_growth {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (N : ℕ)
    (hstay : ∀ n ≤ N, ‖((threeReturn c p)^[n]) z‖ ≤ 1/6) :
    slitAmplitude (centralRadius c p) z ^ (7^N) ≤
      slitAmplitude (centralRadius c p) (((threeReturn c p)^[N]) z) ^ (6^N) := by
  have h := finite_power_growth
    (fun n => slitAmplitude (centralRadius c p) (((threeReturn c p)^[n]) z)) N
    (fun n _ => (by norm_num : (0 : ℝ) ≤ 1).trans (slitAmplitude_ge_one _ _))
    (fun n hn => by
      simpa only [iterate_succ_apply'] using
        actual_amplification hp hc (hstay n (by omega)))
  simpa using h

/-- A fully explicit finite escape certificate, uniform in the unbounded
period range. No limiting orbit, straightening, or model dynamics is used. -/
theorem actual_finite_exponential_escape {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (N : ℕ)
    (hbudget : (16/5 : ℝ)^(6^N) <
      slitAmplitude (centralRadius c p) z ^ (7^N)) :
    ∃ n ≤ N, (1/6 : ℝ) < ‖((threeReturn c p)^[n]) z‖ := by
  by_contra! hstay
  have hg := actual_power_growth hp hc N hstay
  have hb := slitAmplitude_upper (centralRadius_bounds hp hc).1 (hstay N le_rfl)
  have hn : 0 ≤ slitAmplitude (centralRadius c p) (((threeReturn c p)^[N]) z) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (slitAmplitude_ge_one _ _)
  have hu := pow_le_pow_left₀ hn hb (6^N)
  exact (not_lt_of_ge (hg.trans hu)) hbudget

/-- Every point outside the actual central interval eventually exits the
complete control disk, even if it initially lies outside the selected source. -/
theorem actual_complex_escape {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ}
    (hz : z ∉ realSegment (centralRadius c p)) :
    ∃ n : ℕ, (1/6 : ℝ) < ‖((threeReturn c p)^[n]) z‖ := by
  by_contra! hstay
  have he := bounded_power_sequence_eq_one
    (fun n => slitAmplitude (centralRadius c p) (((threeReturn c p)^[n]) z))
    (16/5)
    (fun n => slitAmplitude_ge_one _ _)
    (fun n => slitAmplitude_upper (centralRadius_bounds hp hc).1 (hstay n))
    (fun n => by
      simpa only [iterate_succ_apply'] using actual_amplification hp hc (hstay n))
  have he0 : slitAmplitude (centralRadius c p) z = 1 := by simpa using he
  exact hz ((slitAmplitude_eq_one_iff (centralRadius_pos hp hc) z).mp he0)

/-- Surviving in the complete closed control disk is equivalent to lying
in the literal orbit interval. -/
theorem survives_control_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (z : ℂ) :
    (∀ n : ℕ, ‖((threeReturn c p)^[n]) z‖ ≤ 1/6) ↔
      z ∈ realSegment (centralRadius c p) := by
  constructor
  · intro hstay
    by_contra hz
    obtain ⟨n, hn⟩ := actual_complex_escape hp hc hz
    exact (not_lt_of_ge (hstay n)) hn
  · intro hz n
    exact (source_norm_lt_control hp hc (slit_orbit_in_source hp hc hz n)).le

/-- Identification with the filled set of the actual selected proper
restriction. This supplies the canonical-object link for the escape rate. -/
theorem filledSource_eq_slit {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    filledSource c p = realSegment (centralRadius c p) := by
  apply Set.Subset.antisymm
  · intro z hz
    change ∀ n : ℕ, ((threeReturn c p)^[n]) z ∈ source c p at hz
    apply (survives_control_iff hp hc z).mp
    intro n
    exact (source_norm_lt_control hp hc (hz n)).le
  · exact slit_subset_filledSource hp hc

end
end ActualCentralEscape
