import NearTwoProduct
import Mathlib.Tactic.FieldSimp

/-!
# Inverse-endpoint localization of a complete real return window

The hypotheses retain the two actual positive inverse orbits.  In particular,
the terminal return scale is not assumed to be exponentially small.  The
inverse secant identity first supplies a coarse contraction estimate; a second
product estimate recovers the sharp base-four scale.
-/

namespace GlobalInverseWindow

open Set Function Finset NearTwoInverse
open scoped BigOperators

noncomputable section

private theorem band {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000)) :
    c ∈ Icc (-2 : ℝ) (-49/25) :=
  ⟨hc.1, by linarith [hc.2]⟩

private theorem first_bounds {c x : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hx : x ∈ Icc (-3/2 : ℝ) 2) :
    B c x ∈ Icc (2/3 : ℝ) 2 := by
  have hs : (B c x)^2 = x-c := by
    unfold B
    exact Real.sq_sqrt (by linarith [hc.2,hx.1])
  have hn := B_nonneg c x
  constructor <;> nlinarith [hc.1,hc.2,hx.1,hx.2]

private theorem inverse_bounds {c x : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hx : x ∈ Icc (-3/2 : ℝ) 2) (n : ℕ) :
    back c (n+1) x ∈ Icc (2/3 : ℝ) 2 := by
  induction n with
  | zero => simpa only [back_succ,back_zero] using first_bounds hc hx
  | succ n ih =>
    rw [back_succ]
    exact first_bounds hc ⟨by linarith [ih.1],ih.2⟩

private theorem inverse_later_lower {c x : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hx : x ∈ Icc (-3/2 : ℝ) 2) (n : ℕ) :
    3/2 ≤ back c (n+2) x := by
  have hb := inverse_bounds hc hx n
  have hs := B_sq (c := c) (x := back c (n+1) x)
    (by linarith [hc.2]) (by linarith [hb.1])
  have hn := B_nonneg c (back c (n+1) x)
  rw [show n+2 = (n+1)+1 by omega, back_succ]
  nlinarith [hc.2,hb.1]

private theorem inverse_sq {c x : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hx : x ∈ Icc (-3/2 : ℝ) 2) (n : ℕ) :
    (back c (n+1) x)^2 = back c n x-c := by
  rw [back_succ]
  unfold B
  apply Real.sq_sqrt
  cases n with
  | zero => simpa only [back_zero] using (show 0 ≤ x-c by linarith [hc.2,hx.1])
  | succ n => have h := inverse_bounds hc hx n; linarith [h.1,hc.2]

private theorem inverse_secant {c x y : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hx : x ∈ Icc (-3/2 : ℝ) 2)
    (hy : y ∈ Icc (-3/2 : ℝ) 2) (n : ℕ) :
    (back c (n+1) x-back c (n+1) y) *
        (back c (n+1) x+back c (n+1) y) =
      back c n x-back c n y := by
  nlinarith only [inverse_sq hc hx n,inverse_sq hc hy n]

/-- An exact positive-inverse secant estimate on the entire terminal range,
including negative target endpoints. -/
theorem inverse_difference_bound {c x y : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hx : x ∈ Icc (-3/2 : ℝ) 2)
    (hy : y ∈ Icc (-3/2 : ℝ) 2) (hyx : y ≤ x) (n : ℕ) :
    back c (n+1) x-back c (n+1) y ≤
      (3/4 : ℝ)*(1/3)^n*(x-y) := by
  induction n with
  | zero =>
    have hnonneg : 0 ≤ back c 1 x-back c 1 y :=
      sub_nonneg.mpr (back_mono_initial c 1 hyx)
    have hx' := inverse_bounds hc hx 0
    have hy' := inverse_bounds hc hy 0
    have he := inverse_secant hc hx hy 0
    simp only [back_zero,pow_zero,mul_one] at he ⊢
    nlinarith [mul_nonneg hnonneg (show 0 ≤
      back c 1 x+back c 1 y-4/3 by linarith [hx'.1,hy'.1])]
  | succ n ih =>
    have hnonneg : 0 ≤ back c (n+2) x-back c (n+2) y :=
      sub_nonneg.mpr (back_mono_initial c (n+2) hyx)
    have hx' := inverse_later_lower hc hx n
    have hy' := inverse_later_lower hc hy n
    have he := inverse_secant hc hx hy (n+1)
    have hm := mul_nonneg hnonneg
      (show 0 ≤ back c (n+2) x+back c (n+2) y-3 by linarith)
    rw [pow_succ]
    nlinarith only [he,hm,ih]

/-- The coarse scale is a conclusion of the inverse endpoint equation. -/
theorem coarse_scale_bound {c d e : ℝ} {p : ℕ}
    (hp : 17 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hd : 0 < d) (hdu : d < 3/2)
    (he : e ∈ Icc (-d) d)
    (hid : back c (p-1) d-back c (p-1) e = d^2) :
    d ≤ (27/2 : ℝ)*(1/3)^p := by
  have hdb : d ∈ Icc (-3/2 : ℝ) 2 := ⟨by linarith,by linarith⟩
  have heb : e ∈ Icc (-3/2 : ℝ) 2 := ⟨by linarith [he.1],by linarith [he.2]⟩
  have h := inverse_difference_bound hc hdb heb he.2 (p-2)
  rw [show p-2+1=p-1 by omega,hid] at h
  have hpow : (1/3 : ℝ)^(p-2)=9*(1/3)^p := by
    have heq := pow_add (1/3 : ℝ) (p-2) 2
    rw [Nat.sub_add_cancel (by omega : 2 ≤ p)] at heq
    norm_num at heq
    linarith only [heq]
  rw [hpow] at h
  have hmul := mul_le_mul_of_nonneg_left (show d-e ≤ 2*d by linarith [he.1])
    (show 0 ≤ (3/4 : ℝ)*(9*(1/3)^p) by positivity)
  have hdd : d*d ≤ ((27/2 : ℝ)*(1/3)^p)*d := by nlinarith only [h,hmul]
  exact (mul_le_mul_right hd).mp hdd

private theorem coarse_budget (p : ℕ) (hp : 17 ≤ p) :
    (p : ℝ)*((27/2 : ℝ)*(1/3)^p) < 1/200 := by
  have bound : (p : ℝ)*((27/2 : ℝ)*(1/3)^p) ≤
      17*((27/2 : ℝ)*(1/3)^17) := by
    induction p, hp using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      have hn' : (17 : ℝ) ≤ n := by exact_mod_cast hn
      have hpow : 0 ≤ (27/2 : ℝ)*(1/3)^n := by positivity
      rw [pow_succ]
      push_cast
      have hstep : ((n : ℝ)+1)*((27/2 : ℝ)*((1/3)^n*(1/3))) ≤
          n*((27/2 : ℝ)*(1/3)^n) := by
        nlinarith [mul_nonneg hpow (show 0 ≤ 2*(n : ℝ)-1 by linarith)]
      exact hstep.trans ih
  have hconst : (17 : ℝ)*((27/2 : ℝ)*(1/3)^17)<1/200 := by norm_num
  exact bound.trans_lt hconst

private theorem product_difference_bound (a b : ℕ → ℝ) (n : ℕ)
    (ha : ∀ j < n, a j ∈ Icc (0 : ℝ) 1)
    (hb : ∀ j < n, b j ∈ Icc (0 : ℝ) (a j)) :
    (∏ j ∈ Finset.range n, a j)-(∏ j ∈ Finset.range n, b j) ≤
      ∑ j ∈ Finset.range n, (a j-b j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha' := ha n (by omega)
    have hb' := hb n (by omega)
    have hprev := ih (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))
    have hpa : (∏ j ∈ Finset.range n, a j) ≤ 1 := by
      exact Finset.prod_le_one (fun j hj => (ha j (Finset.mem_range.mp hj)).1)
        (fun j hj => (ha j (Finset.mem_range.mp hj)).2)
    have hsum : 0 ≤ ∑ j ∈ Finset.range n, (a j-b j) := by
      exact Finset.sum_nonneg (fun j hj => sub_nonneg.mpr
        (hb j (Finset.mem_range.mp hj)).2)
    have hmul := mul_le_mul_of_nonneg_right hprev hb'.1
    have hmul' := mul_le_mul_of_nonneg_right hpa (sub_nonneg.mpr hb'.2)
    have hsum' := mul_le_mul_of_nonneg_left (hb'.2.trans ha'.2) hsum
    rw [Finset.prod_range_succ,Finset.prod_range_succ,Finset.sum_range_succ]
    nlinarith only [hmul,hmul',hsum']

private theorem terminal_difference {c d : ℝ} (n : ℕ)
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hd : 0 < d) (hdu : d < 3/2) :
    back c (n+1) 0-back c (n+1) (-d) ≤ d := by
  have h := inverse_difference_bound hc
    (show (0 : ℝ) ∈ Icc (-3/2 : ℝ) 2 by norm_num)
    (show -d ∈ Icc (-3/2 : ℝ) 2 by constructor <;> linarith)
    (by linarith) n
  have hpow : (1/3 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hpow hd.le
  simp only [zero_sub,neg_neg] at h
  nlinarith only [h,hmul]

/-- The complete inverse product remains quantitatively nondegenerate even
at the negative endpoint, after deriving its small scale from the return. -/
theorem negative_endpoint_product {c d e : ℝ} {p : ℕ}
    (hp : 17 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hbudget : ((p-1 : ℕ) : ℝ)*(c+2) ≤ 1/10000)
    (hd : 0 < d) (hdu : d < 3/2)
    (he : e ∈ Icc (-d) d)
    (hid : back c (p-1) d-back c (p-1) e = d^2) :
    3/5 < ∏ j ∈ Finset.range (p-1), back c (j+1) (-d)/2 := by
  have hcoarse := coarse_scale_bound hp hc hd hdu he hid
  have hmul := mul_le_mul_of_nonneg_left hcoarse (show (0 : ℝ) ≤ p by positivity)
  have hpd : (p : ℝ)*d < 1/200 := hmul.trans_lt (coarse_budget p hp)
  have hn : ((p-1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hnd := mul_le_mul_of_nonneg_right hn hd.le
  have hbase := normalized_inverse_product_lower (p-1) (by omega) hc
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 2 by norm_num) hbudget
  have hdiff := product_difference_bound
    (fun j => back c (j+1) 0/2) (fun j => back c (j+1) (-d)/2) (p-1)
    (by
      intro j hj
      have h := back_bounds (band hc) (show (0 : ℝ) ∈ Icc (0 : ℝ) 2 by norm_num) (j+1)
      constructor <;> linarith [h.1,h.2])
    (by
      intro j hj
      have h := inverse_bounds hc
        (show -d ∈ Icc (-3/2 : ℝ) 2 by constructor <;> linarith) j
      have hle := back_mono_initial c (j+1) (show -d ≤ 0 by linarith)
      constructor <;> linarith [h.1])
  have hsum : (∑ j ∈ Finset.range (p-1),
      (back c (j+1) 0/2-back c (j+1) (-d)/2)) ≤ ((p-1 : ℕ) : ℝ)*d/2 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (p-1), d/2 := by
        apply Finset.sum_le_sum
        intro j hj
        linarith [terminal_difference j hc hd hdu]
      _ = _ := by simp; ring
  linarith only [hbase,hdiff,hsum,hpd,hnd]

/-- Exact secant conservation, with the full inverse-orbit product. -/
theorem inverse_difference_product {c x y : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hx : x ∈ Icc (-3/2 : ℝ) 2)
    (hy : y ∈ Icc (-3/2 : ℝ) 2) (n : ℕ) :
    (back c n x-back c n y) *
      (∏ j ∈ Finset.range n, (back c (j+1) x+back c (j+1) y)) = x-y := by
  induction n with
  | zero => simp only [back_zero,Finset.prod_range_zero,mul_one]
  | succ n ih =>
    have hs := inverse_secant hc hx hy n
    rw [Finset.prod_range_succ]
    calc
      _ = ((back c (n+1) x-back c (n+1) y) *
          (back c (n+1) x+back c (n+1) y)) *
          (∏ j ∈ Finset.range n, (back c (j+1) x+back c (j+1) y)) := by ring
      _ = _ := by rw [hs,ih]

/-- A global return-window endpoint equation forces the base-four scale.
The scale bound is not among the assumptions. -/
theorem return_scale_bound {c d e : ℝ} {p : ℕ}
    (hp : 17 ≤ p)
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hbudget : ((p-1 : ℕ) : ℝ)*(c+2) ≤ 1/10000)
    (hd : 0 < d) (hdu : d < 3/2)
    (he : e ∈ Icc (-d) d)
    (hid : back c (p-1) d-back c (p-1) e = d^2) :
    d < 14*(1/4 : ℝ)^p := by
  have hprod := negative_endpoint_product hp hc hbudget hd hdu he hid
  have hsec := inverse_difference_product hc
    (show d ∈ Icc (-3/2 : ℝ) 2 by constructor <;> linarith)
    (show e ∈ Icc (-3/2 : ℝ) 2 by constructor <;> linarith [he.1,he.2]) (p-1)
  rw [hid] at hsec
  have hpoint (j : ℕ) : 4*(back c (j+1) (-d)/2) ≤
      back c (j+1) d+back c (j+1) e := by
    have h1 := back_mono_initial c (j+1) (show -d ≤ d by linarith)
    have h2 := back_mono_initial c (j+1) he.1
    linarith only [h1,h2]
  have hcmp : (4 : ℝ)^(p-1) *
      (∏ j ∈ Finset.range (p-1), back c (j+1) (-d)/2) ≤
      ∏ j ∈ Finset.range (p-1), (back c (j+1) d+back c (j+1) e) := by
    calc
      _ = ∏ j ∈ Finset.range (p-1), 4*(back c (j+1) (-d)/2) := by
        rw [Finset.prod_mul_distrib]
        simp
      _ ≤ _ := by
        apply Finset.prod_le_prod
        · intro j hj
          have h := inverse_bounds hc
            (show -d ∈ Icc (-3/2 : ℝ) 2 by constructor <;> linarith) j
          have hb : 0 ≤ back c (j+1) (-d) := by linarith [h.1]
          positivity
        · intro j hj
          exact hpoint j
  have hstrict := mul_lt_mul_of_pos_left hprod (show (0 : ℝ) < 4^(p-1) by positivity)
  have hprodlo : (3/5 : ℝ)*4^(p-1) <
      ∏ j ∈ Finset.range (p-1), (back c (j+1) d+back c (j+1) e) := by
    nlinarith only [hstrict,hcmp]
  have hd2 : 0 < d^2 := sq_pos_of_pos hd
  have hm := mul_lt_mul_of_pos_left hprodlo hd2
  have heup : d-e ≤ 2*d := by linarith [he.1]
  have hsmall : d*((3/5 : ℝ)*4^(p-1)) < 2 := by
    have h : (d*((3/5 : ℝ)*4^(p-1)))*d < 2*d := by nlinarith only [hm,hsec,heup]
    exact (mul_lt_mul_right hd).mp h
  have hpower : (4 : ℝ)^p=4^(p-1)*4 := by
    rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have htotal : d*(4 : ℝ)^p < 40/3 := by rw [hpower]; nlinarith only [hsmall]
  have hpowpos : (0 : ℝ)<4^p := by positivity
  have hfinal : d < 14/(4 : ℝ)^p := (lt_div_iff₀ hpowpos).mpr (by linarith only [htotal])
  simpa only [one_div_pow,mul_one_div] using hfinal

end
end GlobalInverseWindow
