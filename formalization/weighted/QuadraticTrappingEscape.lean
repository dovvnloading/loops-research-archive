import QuadraticEscape
import QuadraticMultiplierIteration

/-!
# Return trapping implies zero actual quadratic escape

A bounded subsequence at positive-length return times forces the actual
escape potential to vanish. An invariant disk for a positive iterate
therefore consists of bounded-orbit points. In particular, a return disk
containing the critical point forces the actual parameter escape to vanish.
-/

namespace LoopsQuadraticTrappingEscape

open LoopsQuadraticTransversality

noncomputable section

/-- The escape development and critical-relation development use the same
actual spatial iterates, with their arguments in different positions. -/
theorem escapeOrbit_eq_returnOrbit (d z : ℂ) (m : ℕ) :
    QuadraticEscape.orbit d m z = returnOrbit d z m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (QuadraticEscape.orbit d m z)^2+d = (returnOrbit d z m)^2+d
    rw [ih]

private theorem escape_le_logSize_add (d z : ℂ) :
    QuadraticEscape.escape d z ≤
      QuadraticEscape.logSize z + Real.log (1+‖d‖) := by
  have he := (abs_le.mp
    (QuadraticEscape.escape_error d z (le_refl ‖d‖) 0)).1
  simp only [QuadraticEscape.approx, QuadraticEscape.weight,
    QuadraticEscape.orbit, pow_zero, one_mul] at he
  linarith only [he]

private theorem natCast_add_one_le_two_pow (m : ℕ) :
    (m : ℝ)+1 ≤ (2 : ℝ)^m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Nat.cast_succ, pow_succ]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith only [ih, hm]

/-- A bounded subsequence at every multiple of a positive return length
already forces zero escape. Intermediate iterates need not be estimated. -/
theorem escape_zero_of_bounded_return_subsequence (d z : ℂ)
    (p : ℕ) (hp : 0 < p) (r : ℝ)
    (hbound : ∀ k : ℕ, ‖returnOrbit d z (p*k)‖ ≤ r) :
    QuadraticEscape.escape d z = 0 := by
  let C : ℝ := Real.log (max 1 r) + Real.log (1+‖d‖)
  have hb (k : ℕ) :
      (2 : ℝ)^(p*k) * QuadraticEscape.escape d z ≤ C := by
    have hnorm : ‖QuadraticEscape.orbit d (p*k) z‖ ≤ r := by
      rw [escapeOrbit_eq_returnOrbit]
      exact hbound k
    have hlog : QuadraticEscape.logSize (QuadraticEscape.orbit d (p*k) z) ≤
        Real.log (max 1 r) := by
      unfold QuadraticEscape.logSize
      apply Real.log_le_log (QuadraticEscape.size_pos _)
      exact max_le_max le_rfl hnorm
    calc
      (2 : ℝ)^(p*k) * QuadraticEscape.escape d z =
          QuadraticEscape.escape d (QuadraticEscape.orbit d (p*k) z) :=
        (QuadraticEscape.escape_iterate d z (p*k)).symm
      _ ≤ QuadraticEscape.logSize (QuadraticEscape.orbit d (p*k) z) +
          Real.log (1+‖d‖) :=
        escape_le_logSize_add d (QuadraticEscape.orbit d (p*k) z)
      _ ≤ C := add_le_add hlog le_rfl
  apply le_antisymm _ (QuadraticEscape.escape_nonneg d z)
  by_contra hnot
  have he : 0 < QuadraticEscape.escape d z := lt_of_not_ge hnot
  obtain ⟨k, hk⟩ := exists_nat_gt (C / QuadraticEscape.escape d z)
  have hkC : C < (k : ℝ) * QuadraticEscape.escape d z :=
    (div_lt_iff₀ he).mp hk
  have hi : k ≤ p*k := by
    simpa only [one_mul] using Nat.mul_le_mul_right k (Nat.succ_le_of_lt hp)
  have hi' : (k : ℝ) ≤ ((p*k : ℕ) : ℝ) := by exact_mod_cast hi
  have hg := natCast_add_one_le_two_pow (p*k)
  have hkpow : (k : ℝ) ≤ (2 : ℝ)^(p*k) := by linarith only [hi', hg]
  have hmul := mul_le_mul_of_nonneg_right hkpow he.le
  exact (not_lt_of_ge (hmul.trans (hb k))) hkC

/-- Every point of a disk invariant under a positive quadratic iterate has
zero actual escape, even if the disk is not invariant under one step. -/
theorem escape_zero_of_return_disk (d z : ℂ) (p : ℕ) (hp : 0 < p)
    (r : ℝ) (hz : ‖z‖ ≤ r)
    (htrap : ∀ w : ℂ, ‖w‖ ≤ r → ‖returnOrbit d w p‖ ≤ r) :
    QuadraticEscape.escape d z = 0 := by
  apply escape_zero_of_bounded_return_subsequence d z p hp r
  intro k
  induction k with
  | zero => simpa only [Nat.mul_zero, returnOrbit] using hz
  | succ k ih =>
    rw [Nat.mul_succ, returnOrbit_add_steps]
    exact htrap (returnOrbit d z (p*k)) ih

/-- A positive-length invariant disk about the critical point puts the
actual parameter in the zero-escape locus. -/
theorem parameterEscape_zero_of_return_disk (d : ℂ) (p : ℕ) (hp : 0 < p)
    (r : ℝ) (hr : 0 ≤ r)
    (htrap : ∀ z : ℂ, ‖z‖ ≤ r → ‖returnOrbit d z p‖ ≤ r) :
    QuadraticEscape.parameterEscape d = 0 := by
  have hzero := escape_zero_of_return_disk d 0 p hp r
    (by simpa only [norm_zero] using hr) htrap
  rw [QuadraticEscape.parameterEscape_critical, hzero, mul_zero]

end
end LoopsQuadraticTrappingEscape
