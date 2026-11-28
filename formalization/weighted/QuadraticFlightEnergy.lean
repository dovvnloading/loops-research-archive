import QuadraticFlightJet
import QuadraticReciprocalFlight

/-!
# Small quadratic energy controls actual flight jets

Bounded complex partial sums and small square energy control the first
three nonlinear coefficients. No bound on total absolute variation is
used. These estimates connect the reciprocal shadowing mechanism to the
actual-polynomial jet obstruction.
-/

namespace QuadraticFlightEnergy

open QuadraticFlightJet Polynomial Filter
open LoopsQuadraticReciprocalFlight (energy)
open scoped Topology BigOperators

noncomputable section

def partialSum (a : ℕ → ℂ) (n : ℕ) : ℂ := ∑ j ∈ Finset.range n, a j

def squareSum (a : ℕ → ℂ) (n : ℕ) : ℂ := ∑ j ∈ Finset.range n, (a j)^2

def mixedSum (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n, (a j)^2 * partialSum a j

def cubeSum (a : ℕ → ℂ) (n : ℕ) : ℂ := ∑ j ∈ Finset.range n, (a j)^3

theorem partialSum_succ (a : ℕ → ℂ) (n : ℕ) :
    partialSum a (n+1) = partialSum a n + a n := by
  simp [partialSum, Finset.sum_range_succ]

theorem jet_a_eq_partialSum (a : ℕ → ℂ) (n : ℕ) :
    (flightJet a n).a = partialSum a n := by
  induction n with
  | zero => simp [flightJet, Jet.identity, partialSum]
  | succ n ih =>
    simpa only [flightJet, Jet.comp, Jet.kick, partialSum_succ] using
      congrArg (fun z : ℂ => z+a n) ih

/-- The second nonlinear coefficient differs from the square of the
total drift by precisely the signed quadratic energy. -/
theorem jet_b_eq (a : ℕ → ℂ) (n : ℕ) :
    (flightJet a n).b = (partialSum a n)^2 - squareSum a n := by
  induction n with
  | zero => simp [flightJet, Jet.identity, partialSum, squareSum]
  | succ n ih =>
    simp only [flightJet, Jet.comp, Jet.kick, add_zero]
    rw [ih, jet_a_eq_partialSum, partialSum_succ]
    simp only [squareSum, Finset.sum_range_succ]
    ring

/-- Exact summation-by-parts identity for the fourth-degree coefficient. -/
theorem jet_d_eq (a : ℕ → ℂ) (n : ℕ) :
    (flightJet a n).d = (partialSum a n)^3 -
      2*partialSum a n*squareSum a n - mixedSum a n + cubeSum a n := by
  induction n with
  | zero => simp [flightJet, Jet.identity, partialSum, squareSum, mixedSum, cubeSum]
  | succ n ih =>
    simp only [flightJet, Jet.comp, Jet.kick, zero_mul, mul_zero, add_zero]
    rw [ih, jet_a_eq_partialSum, jet_b_eq, partialSum_succ]
    simp only [squareSum, mixedSum, cubeSum, Finset.sum_range_succ]
    ring

theorem norm_squareSum_le_energy (a : ℕ → ℂ) (n : ℕ) :
    ‖squareSum a n‖ ≤ energy a n := by
  calc
    ‖squareSum a n‖ ≤ ∑ j ∈ Finset.range n, ‖(a j)^2‖ := norm_sum_le _ _
    _ = energy a n := by simp only [energy, norm_pow]

theorem coefficient_le_of_partialSums (a : ℕ → ℂ) (N : ℕ) (M : ℝ)
    (hpart : ∀ j ≤ N, ‖partialSum a j‖ ≤ M) (j : ℕ) (hj : j < N) :
    ‖a j‖ ≤ 2*M := by
  have he : a j = partialSum a (j+1) - partialSum a j := by
    rw [partialSum_succ]
    ring
  rw [he]
  calc
    ‖partialSum a (j+1) - partialSum a j‖ ≤
        ‖partialSum a (j+1)‖ + ‖partialSum a j‖ := norm_sub_le _ _
    _ ≤ M+M := add_le_add (hpart (j+1) (by omega)) (hpart j (by omega))
    _ = 2*M := by ring

theorem norm_mixedSum_le_energy (a : ℕ → ℂ) (N : ℕ) (M : ℝ)
    (hpart : ∀ j ≤ N, ‖partialSum a j‖ ≤ M) :
    ‖mixedSum a N‖ ≤ M*energy a N := by
  calc
    ‖mixedSum a N‖ ≤ ∑ j ∈ Finset.range N, ‖(a j)^2*partialSum a j‖ :=
      norm_sum_le _ _
    _ = ∑ j ∈ Finset.range N, ‖a j‖^2*‖partialSum a j‖ := by
      simp only [norm_mul, norm_pow]
    _ ≤ ∑ j ∈ Finset.range N, ‖a j‖^2*M := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hpart j (by
        have := Finset.mem_range.mp hj
        omega)) (sq_nonneg ‖a j‖)
    _ = M*energy a N := by
      simp only [energy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem norm_cubeSum_le_energy (a : ℕ → ℂ) (N : ℕ) (M : ℝ)
    (hpart : ∀ j ≤ N, ‖partialSum a j‖ ≤ M) :
    ‖cubeSum a N‖ ≤ (2*M)*energy a N := by
  calc
    ‖cubeSum a N‖ ≤ ∑ j ∈ Finset.range N, ‖(a j)^3‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, ‖a j‖^2*(2*M) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_pow]
      calc
        ‖a j‖^3 = ‖a j‖^2*‖a j‖ := by ring
        _ ≤ ‖a j‖^2*(2*M) := mul_le_mul_of_nonneg_left
          (coefficient_le_of_partialSums a N M hpart j (Finset.mem_range.mp hj))
          (sq_nonneg ‖a j‖)
    _ = (2*M)*energy a N := by
      simp only [energy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem jet_b_error_le_energy (a : ℕ → ℂ) (N : ℕ) :
    ‖(flightJet a N).b - (partialSum a N)^2‖ ≤ energy a N := by
  have he : (flightJet a N).b - (partialSum a N)^2 = -squareSum a N := by
    rw [jet_b_eq]
    ring
  rw [he, norm_neg]
  exact norm_squareSum_le_energy a N

/-- Uniform fourth-degree control from bounded partial drift and square
energy; the number of physical quadratic steps is unrestricted. -/
theorem jet_d_error_le_energy (a : ℕ → ℂ) (N : ℕ) (M : ℝ)
    (hpart : ∀ j ≤ N, ‖partialSum a j‖ ≤ M) :
    ‖(flightJet a N).d - (partialSum a N)^3‖ ≤ (5*M)*energy a N := by
  have hM : 0 ≤ M := (norm_nonneg (partialSum a 0)).trans (hpart 0 (by omega))
  have hprod : 2*‖partialSum a N‖*‖squareSum a N‖ ≤ (2*M)*energy a N := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hpart N le_rfl) (by norm_num))
      (norm_squareSum_le_energy a N) (norm_nonneg _) (by positivity)
  calc
    ‖(flightJet a N).d - (partialSum a N)^3‖ =
        ‖-(2*partialSum a N*squareSum a N) - mixedSum a N + cubeSum a N‖ := by
          congr 1
          rw [jet_d_eq]
          ring
    _ ≤ ‖-(2*partialSum a N*squareSum a N) - mixedSum a N‖ + ‖cubeSum a N‖ :=
      norm_add_le _ _
    _ ≤ (‖-(2*partialSum a N*squareSum a N)‖ + ‖mixedSum a N‖) + ‖cubeSum a N‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ = 2*‖partialSum a N‖*‖squareSum a N‖ + ‖mixedSum a N‖ + ‖cubeSum a N‖ := by
      simp only [norm_neg, norm_mul, Complex.norm_two]
    _ ≤ (2*M)*energy a N + M*energy a N + (2*M)*energy a N :=
      add_le_add (add_le_add hprod (norm_mixedSum_le_energy a N M hpart))
        (norm_cubeSum_le_energy a N M hpart)
    _ = (5*M)*energy a N := by ring

/-- A neutral flight has a flat fourth jet when its partial drift stays
bounded and its square energy vanishes. Absolute variation may diverge. -/
theorem flight_jet_tendsto_zero
    (a : ℕ → ℕ → ℂ) (N : ℕ → ℕ) (M : ℝ)
    (hpartial : ∀ n j, j ≤ N n → ‖partialSum (a n) j‖ ≤ M)
    (hsum : Tendsto (fun n => partialSum (a n) (N n)) atTop (𝓝 0))
    (henergy : Tendsto (fun n => energy (a n) (N n)) atTop (𝓝 0)) :
    Tendsto (fun n => (flightJet (a n) (N n)).a) atTop (𝓝 0) ∧
    Tendsto (fun n => (flightJet (a n) (N n)).b) atTop (𝓝 0) ∧
    Tendsto (fun n => (flightJet (a n) (N n)).d) atTop (𝓝 0) := by
  have hb : Tendsto
      (fun n => (flightJet (a n) (N n)).b - (partialSum (a n) (N n))^2)
      atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => jet_b_error_le_energy (a n) (N n)) henergy
  have hbound : Tendsto (fun n => (5*M)*energy (a n) (N n)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => 5*M) atTop (𝓝 (5*M)) := tendsto_const_nhds
    simpa using hconst.mul henergy
  have hd : Tendsto
      (fun n => (flightJet (a n) (N n)).d - (partialSum (a n) (N n))^3)
      atTop (𝓝 0) :=
    squeeze_zero_norm
      (fun n => jet_d_error_le_energy (a n) (N n) M (hpartial n)) hbound
  refine ⟨?_, ?_, ?_⟩
  · simpa only [jet_a_eq_partialSum] using hsum
  · simpa using hb.add (hsum.pow 2)
  · simpa using hd.add (hsum.pow 3)

end
end QuadraticFlightEnergy
