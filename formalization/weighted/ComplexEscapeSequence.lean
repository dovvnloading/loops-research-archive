import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! Elementary finite accounting for the complex escape inequality.
This module makes no dynamical claim independently of its native use. -/

namespace ComplexEscapeSequence

private theorem step_mono {a b : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hs : a^7 ≤ b^6) : a ≤ b := by
  have ha0 : 0 ≤ a := by linarith
  apply (pow_le_pow_iff_left₀ ha0 hb (by norm_num : (6 : ℕ) ≠ 0)).mp
  calc
    a^6 = a^6 * 1 := by ring
    _ ≤ a^6 * a := mul_le_mul_of_nonneg_left ha (pow_nonneg ha0 6)
    _ = a^7 := by ring
    _ ≤ b^6 := hs

private theorem step_increment {a b : ℝ} (ha : 1 ≤ a)
    (hs : a^7 ≤ b^6) : a^6 + (a-1) ≤ b^6 := by
  have h6 : 1 ≤ a^6 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ha 6
  have hm := mul_le_mul_of_nonneg_right h6 (show 0 ≤ a-1 by linarith)
  nlinarith

theorem finite_power_budget (u : ℕ → ℝ) (N : ℕ)
    (hu : ∀ n ≤ N, 1 ≤ u n)
    (hs : ∀ n < N, (u n)^7 ≤ (u (n+1))^6) :
    (u 0)^6 + (N : ℝ)*(u 0-1) ≤ (u N)^6 := by
  have hm : ∀ n ≤ N, u 0 ≤ u n := by
    intro n
    induction n with
    | zero => intro _; exact le_rfl
    | succ n ih =>
      intro hn
      exact (ih (by omega)).trans (step_mono (hu n (by omega))
        (by linarith [hu (n+1) hn]) (hs n (by omega)))
  have hb : ∀ n ≤ N, (u 0)^6 + (n : ℝ)*(u 0-1) ≤ (u n)^6 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hp := ih (by omega)
      have hi := step_increment (hu n (by omega)) (hs n (by omega))
      have h0 := hm n (by omega)
      push_cast
      nlinarith
  exact hb N le_rfl

theorem bounded_power_sequence_eq_one (u : ℕ → ℝ) (B : ℝ)
    (hu : ∀ n, 1 ≤ u n) (hB : ∀ n, u n ≤ B)
    (hs : ∀ n, (u n)^7 ≤ (u (n+1))^6) : u 0 = 1 := by
  by_contra hne
  have hd : 0 < u 0-1 := by
    have hg : 1 < u 0 := lt_of_le_of_ne (hu 0) (Ne.symm hne)
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((B^6-(u 0)^6)/(u 0-1))
  have hb := finite_power_budget u N (fun n _ => hu n) (fun n _ => hs n)
  have hupper := pow_le_pow_left₀ (show 0 ≤ u N by linarith [hu N]) (hB N) 6
  have hg : B^6-(u 0)^6 < (N : ℝ)*(u 0-1) := (div_lt_iff₀ hd).mp hN
  linarith

theorem finite_escape_certificate (u : ℕ → ℝ) (B : ℝ) (N : ℕ)
    (hu : ∀ n ≤ N, 1 ≤ u n)
    (hs : ∀ n < N, (u n)^7 ≤ (u (n+1))^6)
    (hbudget : B^6-(u 0)^6 < (N : ℝ)*(u 0-1)) :
    ∃ n ≤ N, B < u n := by
  by_contra! hbound
  have hb := finite_power_budget u N hu hs
  have hp := pow_le_pow_left₀ (show 0 ≤ u N by linarith [hu N le_rfl])
    (hbound N le_rfl) 6
  linarith

/-- Exact exponential iteration of the native power inequality. -/
theorem finite_power_growth (u : ℕ → ℝ) (N : ℕ)
    (hu : ∀ n ≤ N, 0 ≤ u n)
    (hs : ∀ n < N, (u n)^7 ≤ (u (n+1))^6) :
    (u 0)^(7^N) ≤ (u N)^(6^N) := by
  have hb : ∀ n ≤ N, (u 0)^(7^n) ≤ (u n)^(6^n) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hp := pow_le_pow_left₀ (pow_nonneg (hu 0 (by omega)) (7^n))
        (ih (by omega)) 7
      have ht := pow_le_pow_left₀ (pow_nonneg (hu n (by omega)) 7)
        (hs n (by omega)) (6^n)
      calc
        (u 0)^(7^(n+1)) = ((u 0)^(7^n))^7 := by rw [pow_succ, pow_mul]
        _ ≤ ((u n)^(6^n))^7 := hp
        _ = ((u n)^7)^(6^n) := by simp only [← pow_mul, Nat.mul_comm]
        _ ≤ ((u (n+1))^6)^(6^n) := ht
        _ = (u (n+1))^(6^(n+1)) := by simp only [← pow_mul, pow_succ, Nat.mul_comm]
  exact hb N le_rfl

end ComplexEscapeSequence
