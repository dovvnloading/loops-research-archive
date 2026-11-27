import NearTwoInverse

/-!
# A uniform coefficient budget for the positive inverse orbit

Three certified initial inverse points and a telescoping tail account
bound the entire normalized derivative product, independently of period.
-/

namespace NearTwoInverse

open Set Function
open scoped BigOperators

noncomputable section

private theorem small_parameter_band {c : ℝ}
    (hc : c ∈ Icc (-2) (-2+1/10000)) : c ∈ Icc (-2) (-49/25) := by
  exact ⟨hc.1, by linarith [hc.2]⟩

theorem first_inverse_lower_bounds {c d : ℝ}
    (hc : c ∈ Icc (-2) (-2+1/10000)) (hd : d ∈ Icc 0 2) :
    707/500 ≤ back c 1 d ∧ 1847/1000 ≤ back c 2 d ∧
      1961/1000 ≤ back c 3 d := by
  have hband := small_parameter_band hc
  have h1 := B_sq (c := c) (x := d) (by linarith [hc.2]) hd.1
  have h1n := B_nonneg c d
  have h1b : 707/500 ≤ back c 1 d := by
    simpa only [back_succ, back_zero] using
      (show 707/500 ≤ B c d by nlinarith [hc.2, hd.1])
  have h2 := B_sq (c := c) (x := back c 1 d)
    (by linarith [hc.2]) (back_bounds hband hd 1).1
  have h2n := B_nonneg c (back c 1 d)
  have h2b : 1847/1000 ≤ back c 2 d := by
    rw [show 2 = 1+1 from rfl, back_succ]
    nlinarith [hc.2, h1b]
  have h3 := B_sq (c := c) (x := back c 2 d)
    (by linarith [hc.2]) (back_bounds hband hd 2).1
  have h3n := B_nonneg c (back c 2 d)
  have h3b : 1961/1000 ≤ back c 3 d := by
    rw [show 3 = 2+1 from rfl, back_succ]
    nlinarith [hc.2, h2b]
  exact ⟨h1b,h2b,h3b⟩

theorem inverse_tail_lower {c d : ℝ}
    (hc : c ∈ Icc (-2) (-2+1/10000)) (hd : d ∈ Icc 0 2) (n : ℕ) :
    1961/1000 ≤ back c (n+3) d := by
  induction n with
  | zero => exact (first_inverse_lower_bounds hc hd).2.2
  | succ n ih =>
    have hs := B_sq (c := c) (x := back c (n+3) d)
      (by linarith [hc.2]) (back_bounds (small_parameter_band hc) hd (n+3)).1
    have hn := B_nonneg c (back c (n+3) d)
    rw [show n+1+3 = (n+3)+1 by omega, back_succ]
    nlinarith [hc.2]

/-- The tail debt is charged once. The final deficit is retained, so
this inequality is stronger than a separate bound at each depth. -/
theorem inverse_tail_deficit_account {c d : ℝ}
    (hc : c ∈ Icc (-2) (-2+1/10000)) (hd : d ∈ Icc 0 2) (n : ℕ) :
    (29/10 : ℝ)*(∑ j ∈ Finset.range n, (2-back c (j+4) d)) +
      (2-back c (n+3) d) ≤ (2-back c 3 d)+(n : ℝ)*(c+2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hband := small_parameter_band hc
    have hnext := inverse_tail_lower hc hd (n+1)
    have hub := (back_bounds hband hd (n+4)).2
    have hs := B_sq (c := c) (x := back c (n+3) d)
      (by linarith [hc.2]) (back_bounds hband hd (n+3)).1
    rw [← back_succ] at hs
    have hsq : (back c (n+4) d)^2 = back c (n+3) d-c := by
      simpa only [show n+3+1 = n+4 by omega] using hs
    have hlo : 39/10 ≤ 2+back c (n+4) d := by
      have hnext' : 1961/1000 ≤ back c (n+4) d := by
        simpa only [show n+1+3=n+4 by omega] using hnext
      linarith
    have hmul := mul_le_mul_of_nonneg_right hlo
      (show 0 ≤ 2-back c (n+4) d by linarith)
    have hstep : (39/10 : ℝ)*(2-back c (n+4) d) ≤
        (2-back c (n+3) d)+(c+2) := by nlinarith
    rw [Finset.sum_range_succ]
    push_cast
    simp only [show n+1+3=n+4 by omega]
    nlinarith

private theorem product_ge_one_sub_deficits (a : ℕ → ℝ) (n : ℕ)
    (ha : ∀ j < n, a j ∈ Icc 0 1) :
    1-(∑ j ∈ Finset.range n, (1-a j)) ≤ ∏ j ∈ Finset.range n, a j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun j hj => ha j (by omega))
    have han := ha n (by omega)
    have hsum : 0 ≤ ∑ j ∈ Finset.range n, (1-a j) := by
      apply Finset.sum_nonneg
      intro j hj
      have hjn : j<n := Finset.mem_range.mp hj
      linarith [(ha j (by omega)).2]
    have hprod := mul_le_mul_of_nonneg_right hprev han.1
    have hgood := mul_nonneg hsum (show 0 ≤ 1-a n by linarith [han.2])
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    nlinarith

/-- A period-independent lower bound for the exact normalized product
along a positive inverse orbit, with its complete parameter debt. -/
theorem normalized_inverse_product_lower {c d : ℝ} (n : ℕ) (hn : 3 ≤ n)
    (hc : c ∈ Icc (-2) (-2+1/10000)) (hd : d ∈ Icc 0 2)
    (hbudget : (n : ℝ)*(c+2) ≤ 1/10000) :
    241/400 ≤ ∏ j ∈ Finset.range n, (back c (j+1) d/2) := by
  let k := n-3
  have hnk : n=k+3 := by dsimp [k]; omega
  have hband := small_parameter_band hc
  have hfirst := first_inverse_lower_bounds hc hd
  have htail := inverse_tail_deficit_account hc hd k
  have hlast := (back_bounds hband hd (k+3)).2
  have hkbudget : (k : ℝ)*(c+2) ≤ 1/10000 := by
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast (show k ≤ n by dsimp [k]; omega)
    have hmul := mul_le_mul_of_nonneg_right hkn (show 0 ≤ c+2 by linarith [hc.1])
    exact hmul.trans hbudget
  have htailbound : (∑ j ∈ Finset.range k, (2-back c (j+4) d)) ≤ 17/1000 := by
    nlinarith [hfirst.2.2]
  have hsum : (∑ j ∈ Finset.range n, (2-back c (j+1) d)) ≤ 159/200 := by
    rw [hnk, Nat.add_comm k 3, Finset.sum_range_add]
    norm_num [Finset.sum_range_succ] at *
    simp only [show ∀ j : ℕ, 3+j+1=j+4 by intro j; omega]
    linarith [hfirst.1,hfirst.2.1,hfirst.2.2]
  have hfac : ∀ j<n, back c (j+1) d/2 ∈ Icc (0 : ℝ) 1 := by
    intro j hj
    have h := back_bounds hband hd (j+1)
    constructor <;> linarith [h.1,h.2]
  have hp := product_ge_one_sub_deficits (fun j => back c (j+1) d/2) n hfac
  have hsum' : (∑ j ∈ Finset.range n, (1-back c (j+1) d/2)) =
      (∑ j ∈ Finset.range n, (2-back c (j+1) d))/2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum'] at hp
  linarith

/-- The exact normalized quadratic coefficient stays above 3/20.
The return-map application identifies the product with its genuine
coefficient; this estimate does not assume that identification. -/
theorem coefficient_product_lower {c d : ℝ} (n : ℕ) (hn : 3 ≤ n)
    (hc : c ∈ Icc (-2) (-2+1/10000)) (hd : d ∈ Icc 0 2)
    (hbudget : (n : ℝ)*(c+2) ≤ 1/10000) :
    3/20 < (-c)/8 * (∏ j ∈ Finset.range n, (back c (j+1) d/2)) := by
  have hp := normalized_inverse_product_lower n hn hc hd hbudget
  have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ (-c)/8 by linarith [hc.2])
  nlinarith [hc.2]

end

end NearTwoInverse
