import QuadraticCriticalTransversality

/-!
# Exact ramification and the equal-clock critical-window obstruction

For the actual complex quadratic family, not a symbolic degree word.
The local polynomial factorization records every encounter with zero.
The reached-domain obstruction uses only the actual inverse-section equation
and an open root domain containing zero.
-/

namespace QuadraticCriticalWindow
open Polynomial Set Function
open LoopsQuadraticTransversality
noncomputable section

/-- The number of critical encounters before the terminal iterate. -/
def criticalCount (c z : ℂ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if returnOrbit c z n = 0 then criticalCount c z n + 1
             else criticalCount c z n

/-- The actual iterate evaluated in the translated coordinate z + X. -/
def shiftedOrbit (c z : ℂ) : ℕ → ℂ[X]
  | 0 => C z + X
  | n + 1 => shiftedOrbit c z n ^ 2 + C c

/-- The residual polynomial after removing all powers of the local coordinate. -/
def localUnit (c z : ℂ) : ℕ → ℂ[X]
  | 0 => 1
  | n + 1 => if returnOrbit c z n = 0 then localUnit c z n ^ 2
             else localUnit c z n * (shiftedOrbit c z n + C (returnOrbit c z n))

theorem shiftedOrbit_eval (c z t : ℂ) (n : ℕ) :
    (shiftedOrbit c z n).eval t = returnOrbit c (z+t) n := by
  induction n with
  | zero => simp [shiftedOrbit, returnOrbit]
  | succ n ih => simp [shiftedOrbit, returnOrbit, ih]

theorem criticalCount_eq_zero_iff (c z : ℂ) (n : ℕ) :
    criticalCount c z n = 0 ↔ ∀ i < n, returnOrbit c z i ≠ 0 := by
  induction n with
  | zero => simp [criticalCount]
  | succ n ih =>
    by_cases h : returnOrbit c z n = 0
    · constructor
      · intro hz
        simp [criticalCount, h] at hz
      · intro hh
        exact False.elim (hh n (Nat.lt_succ_self n) h)
    · rw [criticalCount, if_neg h, ih]
      constructor
      · intro hh i hi
        by_cases hei : i = n
        · subst i
          exact h
        · exact hh i (by omega)
      · intro hh i hi
        exact hh i (by omega)

/-- No cancellations can increase the order of the residual polynomial. -/
theorem localUnit_eval_zero_ne (c z : ℂ) (n : ℕ) :
    (localUnit c z n).eval 0 ≠ 0 := by
  induction n with
  | zero => simp [localUnit]
  | succ n ih =>
    by_cases h : returnOrbit c z n = 0
    · simp only [localUnit, if_pos h, eval_pow]
      exact pow_ne_zero _ ih
    · simp only [localUnit, if_neg h, eval_mul, eval_add, eval_C,
        shiftedOrbit_eval, add_zero]
      apply mul_ne_zero ih
      rw [← two_mul]
      exact mul_ne_zero (by norm_num) h

/-- Exact order factorization, valid for every parameter, point and horizon. -/
theorem shiftedOrbit_factor (c z : ℂ) (n : ℕ) :
    shiftedOrbit c z n - C (returnOrbit c z n) =
      X ^ (2 ^ criticalCount c z n) * localUnit c z n := by
  induction n with
  | zero => simp [shiftedOrbit, returnOrbit, criticalCount, localUnit]
  | succ n ih =>
    have hd :
        shiftedOrbit c z (n+1) - C (returnOrbit c z (n+1)) =
          (shiftedOrbit c z n - C (returnOrbit c z n)) *
            (shiftedOrbit c z n + C (returnOrbit c z n)) := by
      simp only [shiftedOrbit, returnOrbit, map_add, map_pow]
      ring
    rw [hd, ih]
    by_cases h : returnOrbit c z n = 0
    · have hp : shiftedOrbit c z n =
          X ^ (2 ^ criticalCount c z n) * localUnit c z n := by
        simpa [h] using ih
      rw [criticalCount, localUnit, if_pos h, if_pos h, h, map_zero, add_zero, hp]
      rw [pow_succ (2 : ℕ), pow_mul]
      ring
    · rw [criticalCount, localUnit, if_neg h, if_neg h]
      ring

/-- Exact divisibility by the local coordinate, including the strict upper
bound: the exponent is not just a lower bound on multiplicity. -/
theorem shiftedOrbit_exact_order (c z : ℂ) (n : ℕ) :
    (X : ℂ[X]) ^ (2 ^ criticalCount c z n) ∣
      shiftedOrbit c z n - C (returnOrbit c z n) ∧
    ¬ (X : ℂ[X]) ^ (2 ^ criticalCount c z n + 1) ∣
      shiftedOrbit c z n - C (returnOrbit c z n) := by
  constructor
  · exact ⟨localUnit c z n, shiftedOrbit_factor c z n⟩
  · rintro ⟨Q, hQ⟩
    have hx : (X : ℂ[X]) ^ (2 ^ criticalCount c z n) ≠ 0 :=
      pow_ne_zero _ X_ne_zero
    have hc : localUnit c z n = X * Q := by
      apply mul_left_cancel₀ hx
      calc
        X ^ (2 ^ criticalCount c z n) * localUnit c z n =
            shiftedOrbit c z n - C (returnOrbit c z n) :=
          (shiftedOrbit_factor c z n).symm
        _ = X ^ (2 ^ criticalCount c z n + 1) * Q := hQ
        _ = X ^ (2 ^ criticalCount c z n) * (X * Q) := by
          rw [pow_succ, mul_assoc]
    have he := congrArg (fun p : ℂ[X] => p.eval 0) hc
    exact localUnit_eval_zero_ne c z n (by simpa using he)

/-- Pointwise form, with the actual iterated quadratic map on both sides. -/
theorem local_factorization (c z t : ℂ) (n : ℕ) :
    returnOrbit c (z+t) n - returnOrbit c z n =
      t ^ (2 ^ criticalCount c z n) * (localUnit c z n).eval t := by
  have h := congrArg (fun p : ℂ[X] => p.eval t) (shiftedOrbit_factor c z n)
  simpa only [eval_sub, eval_C, eval_mul, eval_pow, eval_X, shiftedOrbit_eval] using h

theorem orbit_add (c z : ℂ) (m n : ℕ) :
    returnOrbit c z (m+n) = returnOrbit c (returnOrbit c z n) m := by
  simp only [returnOrbit_eq_iterate, Function.iterate_add_apply]

/-- Evenness is exact at every positive time, with no geometric hypotheses. -/
theorem positive_iterate_even (c z : ℂ) (j : ℕ) (hj : 0 < j) :
    returnOrbit c z j = returnOrbit c (-z) j := by
  cases j with
  | zero => omega
  | succ j =>
    rw [orbit_add c z j 1, orbit_add c (-z) j 1]
    simp [returnOrbit, neg_sq]

/-- Every open complex domain containing the critical point contains a
nontrivial reflected pair. -/
theorem open_contains_reflected_pair (A : Set ℂ) (hA : IsOpen A)
    (h0 : (0 : ℂ) ∈ A) : ∃ t : ℂ, t ∈ A ∧ -t ∈ A ∧ t ≠ -t := by
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hA 0 h0
  let t : ℂ := ((ε / 2 : ℝ) : ℂ)
  have ht : t ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    change ‖((ε / 2 : ℝ) : ℂ)‖ < ε
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < ε / 2)]
    linarith
  have ht' : -t ∈ Metric.ball (0 : ℂ) ε := by
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using ht
  refine ⟨t, hb ht, hb ht', ?_⟩
  intro he
  have hr : (ε / 2 : ℝ) = -(ε / 2) := by
    simpa only [t, Complex.ofReal_re, Complex.neg_re] using congrArg Complex.re he
  linarith

/-- A reached domain which surjects onto an open critical root under the
residual clock has an actual pair of distinct points with the same
equal-clock projection. This does not assume that the reached domain
is itself open or that any hypothetical target is a cylinder. -/
theorem reached_projection_collision (c : ℂ) (N j : ℕ) (U A : Set ℂ)
    (hj : 0 < j) (hjN : j ≤ N) (hA : IsOpen A) (h0 : (0 : ℂ) ∈ A)
    (hsurj : SurjOn (fun z => returnOrbit c z (N-j)) U A) :
    ∃ u ∈ U, ∃ v ∈ U, u ≠ v ∧ returnOrbit c u N = returnOrbit c v N := by
  obtain ⟨t, ht, hnt, hne⟩ := open_contains_reflected_pair A hA h0
  obtain ⟨u, hu, hut⟩ := hsurj ht
  obtain ⟨v, hv, hvt⟩ := hsurj hnt
  have hclock (z : ℂ) : returnOrbit c z N =
      returnOrbit c (returnOrbit c z (N-j)) j :=
    (congrArg (returnOrbit c z) (show N = j + (N-j) by omega)).trans
      (orbit_add c z j (N-j))
  refine ⟨u, hu, v, hv, ?_, ?_⟩
  · intro he
    apply hne
    rw [← hut, ← hvt, he]
  · rw [hclock u, hclock v, hut, hvt]
    exact positive_iterate_even c t j hj

/-- Direct native formulation. Any N-step inverse section on the open
critical root, at every intermediate positive time j ≤ N, forces a
collision in every putative target containing its reached image. -/
theorem central_window_no_univalent_cylinder (c : ℂ) (N j : ℕ)
    (phi : ℂ → ℂ) (A T : Set ℂ) (hj : 0 < j) (hjN : j ≤ N)
    (hA : IsOpen A) (h0 : (0 : ℂ) ∈ A)
    (hsection : ∀ x ∈ A, returnOrbit c (phi x) N = x)
    (hcontain : ∀ x ∈ A, returnOrbit c (phi x) j ∈ T) :
    ¬ InjOn (fun z => returnOrbit c z N) T := by
  let U : Set ℂ := (fun x => returnOrbit c (phi x) j) '' A
  have hs : SurjOn (fun z => returnOrbit c z (N-j)) U A := by
    intro x hx
    refine ⟨returnOrbit c (phi x) j, ⟨x, hx, rfl⟩, ?_⟩
    have he := orbit_add c (phi x) (N-j) j
    rw [show N-j+j = N by omega, hsection x hx] at he
    exact he.symm
  obtain ⟨u, hu, v, hv, hne, he⟩ :=
    reached_projection_collision c N j U A hj hjN hA h0 hs
  have hUT : U ⊆ T := by
    rintro y ⟨x, hx, rfl⟩
    exact hcontain x hx
  intro hinj
  exact hne (hinj (hUT hu) (hUT hv) he)

end
end QuadraticCriticalWindow
