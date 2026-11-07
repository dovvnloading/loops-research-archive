import FullCloneEigenline

/-!
# Delay growth has NO uniform positive eigenvalue expansion factor

The full cloned graphs are primitive for every n; the leading root
t_n of t_n^(2n+5)=t_n+1 nevertheless tends to 1.

A direct Bernoulli inequality proves the explicit universal bound
(2n+4)*(t_n-1) ≤ 1. Thus no argument can extract a uniform
t_n≥1+ε from primitivity alone, regardless of the proven strict
per-n spectral gap. This is not yet an estimate on the second
eigenvalue or the quantitative mixing time.
-/

namespace LoopsSpectral

noncomputable section

/-- Bernoulli's inequality for positive shifts, proved by induction
without a transcendental estimate. -/
private theorem bernoulli_one_add (a : ℝ) (ha : 0 ≤ a) :
    ∀ m : ℕ, 1 + (m : ℝ) * a ≤ (1 + a) ^ m := by
  intro m
  induction m with
  | zero => norm_num
  | succ m ih =>
      have hmul : 0 ≤ 1 + a := by linarith
      calc
        1 + ((m + 1 : ℕ) : ℝ) * a =
            1 + (m : ℝ) * a + a := by
              push_cast
              ring
        _ ≤ (1 + (m : ℝ) * a) * (1 + a) := by
              have hnonneg : 0 ≤ (m : ℝ) * a * a :=
                mul_nonneg (mul_nonneg (Nat.cast_nonneg m) ha) ha
              nlinarith
        _ ≤ (1 + a) ^ m * (1 + a) := by
              exact mul_le_mul_of_nonneg_right ih hmul
        _ = (1 + a) ^ (m + 1) := by rw [pow_succ]

/-- An exact all-delay root bound. Even though t_n is a
strict dominant eigenvalue, its excess over 1 is at most
1/(2n+4). The multiplication form avoids division by zero. -/
theorem clone_root_excess_bound
    (n : ℕ) (t : ℝ) (ht : 1 < t)
    (hroot : t ^ (2 * n + 5) = t + 1) :
    ((2 * n + 4 : ℕ) : ℝ) * (t - 1) ≤ 1 := by
  have h := bernoulli_one_add (t - 1) (by linarith) (2 * n + 5)
  have hnat : ((2 * n + 5 : ℕ) : ℝ) =
      ((2 * n + 4 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [show 1 + (t - 1) = t by ring, hroot, hnat] at h
  nlinarith

/-- There cannot be any fixed ε>0 below every primitive clone's
dominant-root excess. This quantifies the nonuniformity for all
positive real tolerances, not just a finite list of delays. -/
theorem clone_root_can_approach_one (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ t : ℝ,
      1 < t ∧ t < 1 + ε ∧
      t ^ (2 * n + 5) = t + 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  obtain ⟨t, ht, _, hroot⟩ := finite_clone_root_exists n
  have hprod : ((2 * n + 4 : ℕ) : ℝ) * (t - 1) ≤ 1 :=
    clone_root_excess_bound n t ht hroot
  have hdiv : (1 / ε) * ε = 1 := by
    field_simp [ne_of_gt hε]
  have hnε : 1 < (n : ℝ) * ε := by
    calc
      (1 : ℝ) = (1 / ε) * ε := hdiv.symm
      _ < (n : ℝ) * ε := mul_lt_mul_of_pos_right hn hε
  have hcoeff : (n : ℝ) ≤ ((2 * n + 4 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * n + 4 by omega)
  have hcoefpos : 0 ≤ ((2 * n + 4 : ℕ) : ℝ) := by positivity
  have hbig : 1 < ((2 * n + 4 : ℕ) : ℝ) * ε :=
    lt_of_lt_of_le hnε (mul_le_mul_of_nonneg_right hcoeff (le_of_lt hε))
  have hlt : t - 1 < ε := by
    by_contra hnot
    have hle : ε ≤ t - 1 := le_of_not_gt hnot
    have hh : ((2 * n + 4 : ℕ) : ℝ) * ε ≤
        ((2 * n + 4 : ℕ) : ℝ) * (t - 1) :=
      mul_le_mul_of_nonneg_left hle hcoefpos
    linarith
  refine ⟨n, t, ht, ?_, hroot⟩
  linarith

#print axioms clone_root_excess_bound
#print axioms clone_root_can_approach_one

end

end LoopsSpectral
