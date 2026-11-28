import QuadraticExtremalMultiplier
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Regularized Jacobian partitions and the actual parameter Green potential

Every factor below is evaluated on the critical-value orbit of z ↦ z²+c.
The partition is a finite sum over suffixes, not an assumed invariant measure
or a topological-pressure identification. Its regularizer controls the exact
quadratic perturbation term before any infinite-time limit is taken.
-/

namespace QuadraticEscape

open Set
open scoped BigOperators

noncomputable section

/-- Finite renewal partition for the regularized geometric Jacobian. -/
def regularizedResponse (c : ℂ) (ε : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (2 * ‖orbit c n c‖ + ε) * regularizedResponse c ε n + 1

/-- The unregularized factor is the actual one-step complex derivative norm. -/
theorem regularized_factor_eq_deriv (c : ℂ) (ε : ℝ) (j : ℕ) :
    2 * ‖orbit c j c‖ + ε =
      ‖deriv (orbit c 1) (orbit c j c)‖ + ε := by
  rw [multiplier_eq_deriv]
  simp [multiplier, orbit, norm_mul, Complex.norm_two]

/-- Exact finite partition expansion, including its empty suffix. -/
theorem regularizedResponse_partition (c : ℂ) (ε : ℝ) (n : ℕ) :
    regularizedResponse c ε n =
      ∑ j ∈ Finset.range (n+1),
        ∏ k ∈ Finset.Ico j n, (2 * ‖orbit c k c‖ + ε) := by
  induction n with
  | zero => simp [regularizedResponse]
  | succ n ih =>
    calc
      regularizedResponse c ε (n+1) =
          (2 * ‖orbit c n c‖ + ε) *
            (∑ j ∈ Finset.range (n+1),
              ∏ k ∈ Finset.Ico j n, (2 * ‖orbit c k c‖ + ε)) + 1 := by
        rw [regularizedResponse, ih]
      _ = (∑ j ∈ Finset.range (n+1),
            (∏ k ∈ Finset.Ico j n, (2 * ‖orbit c k c‖ + ε)) *
              (2 * ‖orbit c n c‖ + ε)) + 1 := by
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (∑ j ∈ Finset.range (n+1),
            ∏ k ∈ Finset.Ico j (n+1), (2 * ‖orbit c k c‖ + ε)) + 1 := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        exact (Finset.prod_Ico_succ_top
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
          (fun k => 2 * ‖orbit c k c‖ + ε)).symm
      _ = ∑ j ∈ Finset.range ((n+1)+1),
            ∏ k ∈ Finset.Ico j (n+1), (2 * ‖orbit c k c‖ + ε) := by
        symm
        rw [Finset.sum_range_succ]
        simp

theorem regularizedResponse_nonneg (c : ℂ) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ regularizedResponse c ε n := by
  induction n with
  | zero => norm_num [regularizedResponse]
  | succ n ih =>
    rw [regularizedResponse]
    positivity

theorem regularizedResponse_one_le (c : ℂ) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    1 ≤ regularizedResponse c ε n := by
  cases n with
  | zero => norm_num [regularizedResponse]
  | succ n =>
    rw [regularizedResponse]
    have hm := mul_nonneg
      (show 0 ≤ 2 * ‖orbit c n c‖ + ε by positivity)
      (regularizedResponse_nonneg c hε n)
    linarith

/-- The partition controls both parameter motion and the moving critical
value. The quadratic error is bounded by the regularizer at every prefix. -/
theorem regularizedResponse_shadowing (c d : ℂ) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    (∀ j ≤ n, ‖d-c‖ * regularizedResponse c ε j ≤ ε) →
    ‖orbit d n d - orbit c n c‖ ≤ ‖d-c‖ * regularizedResponse c ε n := by
  induction n with
  | zero => intro _; simp [orbit, regularizedResponse]
  | succ n ih =>
    intro hscale
    have hp : ∀ j ≤ n, ‖d-c‖ * regularizedResponse c ε j ≤ ε :=
      fun j hj => hscale j (hj.trans (Nat.le_succ n))
    have hshadow := ih hp
    have hsmall : ‖orbit d n d - orbit c n c‖ ≤ ε :=
      hshadow.trans (hscale n (Nat.le_succ n))
    calc
      ‖orbit d (n+1) d - orbit c (n+1) c‖ ≤
          (2 * ‖orbit c n c‖ + ‖orbit d n d-orbit c n c‖) *
            ‖orbit d n d-orbit c n c‖ + ‖d-c‖ :=
        orbit_difference_step c d c d n
      _ ≤ (2 * ‖orbit c n c‖ + ε) *
          (‖d-c‖ * regularizedResponse c ε n) + ‖d-c‖ := by
        have hcoeff :
            2 * ‖orbit c n c‖ + ‖orbit d n d-orbit c n c‖ ≤
              2 * ‖orbit c n c‖ + ε := add_le_add le_rfl hsmall
        have hmul := mul_le_mul hcoeff hshadow (norm_nonneg _)
          (show 0 ≤ 2 * ‖orbit c n c‖ + ε by positivity)
        exact add_le_add hmul le_rfl
      _ = ‖d-c‖ * regularizedResponse c ε (n+1) := by
        rw [regularizedResponse]
        ring

/-- A finite, nonstationary thermodynamic certificate for a Green sublevel
disk around any actual bounded-critical-orbit parameter. -/
theorem regularizedResponse_green (c d : ℂ) {ε : ℝ}
    (hc : parameterEscape c = 0) (hε : 0 ≤ ε) (n : ℕ)
    (hscale : ∀ j ≤ n, ‖d-c‖ * regularizedResponse c ε j ≤ ε) :
    parameterEscape d ≤ weight n * (Real.log (2+ε) + Real.log (3+ε)) := by
  have hδ := hscale 0 (Nat.zero_le n)
  simp only [regularizedResponse, mul_one] at hδ
  have hc2 := parameter_norm_le_two c hc
  have hd : ‖d‖ ≤ 2+ε := by
    calc
      ‖d‖ = ‖(d-c)+c‖ := by rw [sub_add_cancel]
      _ ≤ ‖d-c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ 2+ε := by linarith only [hδ, hc2]
  have hshadow := regularizedResponse_shadowing c d hε n hscale
  have hdiff := hshadow.trans (hscale n le_rfl)
  have hb : ‖orbit c n c‖ ≤ 2 := bounded_orbit_norm_le_two c c hc2 hc n
  have hnorm : ‖orbit d n d‖ ≤ 2+ε := by
    calc
      ‖orbit d n d‖ = ‖(orbit d n d-orbit c n c)+orbit c n c‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖orbit d n d-orbit c n c‖ + ‖orbit c n c‖ := norm_add_le _ _
      _ ≤ 2+ε := by linarith only [hdiff, hb]
  have hl : logSize (orbit d n d) ≤ Real.log (2+ε) := by
    unfold logSize
    apply Real.log_le_log (size_pos _)
    exact max_le (by linarith) hnorm
  have hm := mul_le_mul_of_nonneg_left hl (weight_pos n).le
  have herr := (abs_le.mp (escape_error d d hd n)).1
  unfold approx at herr
  rw [show (1:ℝ)+(2+ε) = 3+ε by ring] at herr
  change escape d d ≤ _
  linarith only [hm, herr]

/-- A single upper bound for all prefix partitions certifies the entire disk. -/
theorem regularizedResponse_green_disk (c d : ℂ) {ε B : ℝ}
    (hc : parameterEscape c = 0) (hε : 0 ≤ ε) (n : ℕ)
    (hB : ∀ j ≤ n, regularizedResponse c ε j ≤ B)
    (hd : ‖d-c‖ * B ≤ ε) :
    parameterEscape d ≤ weight n * (Real.log (2+ε) + Real.log (3+ε)) := by
  apply regularizedResponse_green c d hc hε n
  intro j hj
  exact (mul_le_mul_of_nonneg_left (hB j hj) (norm_nonneg _)).trans hd

/-- Any larger actual Green value forces failure of a prefix partition
bound. This is a quadratic parameter-level obstruction, with no fibers
or abstract metric hypothesis in its statement. -/
theorem regularizedResponse_superlevel_obstruction (c d : ℂ) {ε : ℝ}
    (hc : parameterEscape c = 0) (hε : 0 ≤ ε) (n : ℕ)
    (hg : weight n * (Real.log (2+ε) + Real.log (3+ε)) < parameterEscape d) :
    ∃ j ≤ n, ε < ‖d-c‖ * regularizedResponse c ε j := by
  by_contra h
  push Not at h
  exact (not_le_of_gt hg) (regularizedResponse_green c d hc hε n h)


/-- Uniformly bounded regularized partitions certify an actual disk of
bounded critical orbits. The proof uses the full nonlinear family. -/
theorem bounded_regularizedResponse_zero_disk (c d : ℂ) {ε B : ℝ}
    (hc : parameterEscape c = 0) (hε : 0 ≤ ε)
    (hB : ∀ n, regularizedResponse c ε n ≤ B)
    (hd : ‖d-c‖ * B ≤ ε) :
    parameterEscape d = 0 := by
  apply (escape_zero_iff_bounded d d).mpr
  refine ⟨ε + 2, fun n => ?_⟩
  have hscale : ∀ j ≤ n, ‖d-c‖ * regularizedResponse c ε j ≤ ε :=
    fun j _ => (mul_le_mul_of_nonneg_left (hB j) (norm_nonneg _)).trans hd
  have hdiff := (regularizedResponse_shadowing c d hε n hscale).trans (hscale n le_rfl)
  have hc2 := parameter_norm_le_two c hc
  have hb := bounded_orbit_norm_le_two c c hc2 hc n
  calc
    ‖orbit d n d‖ = ‖(orbit d n d-orbit c n c)+orbit c n c‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖orbit d n d-orbit c n c‖ + ‖orbit c n c‖ := norm_add_le _ _
    _ ≤ ε + 2 := add_le_add hdiff hb

/-- A positive regularizer with a bounded all-time partition certifies
interiority in the actual zero-potential parameter locus. -/
theorem bounded_regularizedResponse_interior (c : ℂ) {ε B : ℝ}
    (hc : parameterEscape c = 0) (hε : 0 < ε)
    (hB : ∀ n, regularizedResponse c ε n ≤ B) :
    c ∈ interior {d : ℂ | parameterEscape d = 0} := by
  have hB1 : 1 ≤ B := by simpa only [regularizedResponse] using hB 0
  have hB0 : 0 < B := by linarith
  apply mem_interior_iff_mem_nhds.mpr
  apply Metric.mem_nhds_iff.mpr
  refine ⟨ε / B, div_pos hε hB0, ?_⟩
  intro d hd
  have hδ : ‖d-c‖ < ε / B := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hd
  exact bounded_regularizedResponse_zero_disk c d hc hε.le hB
    ((lt_div_iff₀ hB0).mp hδ).le

/-- At every actual boundary parameter, every positive regularizer has
unbounded finite renewal partitions. Zero potential and noninteriority
are the explicit boundary hypotheses. -/
theorem boundary_regularizedResponse_unbounded (c : ℂ) {ε : ℝ}
    (hc : parameterEscape c = 0)
    (hboundary : c ∉ interior {d : ℂ | parameterEscape d = 0})
    (hε : 0 < ε) (B : ℝ) :
    ∃ n, B < regularizedResponse c ε n := by
  by_contra h
  push Not at h
  exact hboundary (bounded_regularizedResponse_interior c hc hε h)

end
end QuadraticEscape
