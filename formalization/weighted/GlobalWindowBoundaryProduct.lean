import GlobalInverseWindow
import NearTwoShooting

/-!
# The inverse product controlling the physical return boundary

The product is defined on the entire near-minus-two shooting rectangle,
before assuming that the return interval is invariant.  Its quantitative
positivity and joint Lipschitz estimate permit a contraction argument for
the boundary where the right endpoint returns to the left endpoint.
-/

namespace GlobalWindowBoundaryProduct

open Set Function Finset NearTwoInverse NearTwoShooting
open scoped BigOperators

noncomputable section

def endpointProduct (c : ℝ) (p : ℕ) (d : ℝ) : ℝ :=
  ∏ j ∈ Finset.range (p-1),
    (back c (j+1) d+back c (j+1) (-d))/4

theorem continuous_endpointProduct (p : ℕ) :
    Continuous (fun cd : ℝ × ℝ => endpointProduct cd.1 p cd.2) := by
  unfold endpointProduct
  apply continuous_finset_prod
  intro j hj
  exact ((continuous_back (j+1)).add
    ((continuous_back (j+1)).comp
      (continuous_fst.prodMk continuous_snd.neg))).div_const 4

private theorem small_band {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p)) :
    c ∈ Icc (-2 : ℝ) (-2+1/10000) := by
  have hq := scale_small hp
  exact ⟨hc.1,by linarith [hc.2]⟩

private theorem wide_band {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p)) :
    c ∈ Icc (-2 : ℝ) (-199/100) := by
  have hb := small_band hp hc
  exact ⟨hb.1,by linarith [hb.2]⟩

private theorem terminal_small {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) :
    d ∈ Icc (0 : ℝ) (1/100) := by
  have hq := scale_small hp
  exact ⟨hd.1,by linarith [hd.2]⟩

private theorem branch_bounds {c x : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-199/100))
    (hx : x ∈ Icc (-1/100 : ℝ) 2) :
    B c x ∈ Icc (1 : ℝ) 2 := by
  have hs : (B c x)^2=x-c := by
    unfold B
    exact Real.sq_sqrt (by linarith [hc.2,hx.1])
  have hn := B_nonneg c x
  constructor <;> nlinarith [hc.1,hc.2,hx.1,hx.2]

private theorem inverse_bounds {c x : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-199/100))
    (hx : x ∈ Icc (-1/100 : ℝ) 2) (n : ℕ) :
    back c n x ∈ Icc (-1/100 : ℝ) 2 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [back_succ]
    have hb := branch_bounds hc ih
    exact ⟨by linarith [hb.1],hb.2⟩

private theorem inverse_positive_bounds {c x : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-199/100))
    (hx : x ∈ Icc (-1/100 : ℝ) 2) (n : ℕ) :
    back c (n+1) x ∈ Icc (1 : ℝ) 2 := by
  rw [back_succ]
  exact branch_bounds hc (inverse_bounds hc hx n)

private theorem branch_joint_bound {c a x y : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-199/100))
    (ha : a ∈ Icc (-2 : ℝ) (-199/100))
    (hx : x ∈ Icc (-1/100 : ℝ) 2)
    (hy : y ∈ Icc (-1/100 : ℝ) 2) :
    2*|B c x-B a y| ≤ |x-y|+|c-a| := by
  have hA := branch_bounds hc hx
  have hB := branch_bounds ha hy
  have hsA : (B c x)^2=x-c := by
    unfold B
    exact Real.sq_sqrt (by linarith [hc.2,hx.1])
  have hsB : (B a y)^2=y-a := by
    unfold B
    exact Real.sq_sqrt (by linarith [ha.2,hy.1])
  have hid : (B c x-B a y)*(B c x+B a y)=(x-y)-(c-a) := by
    nlinarith only [hsA,hsB]
  have habs : |B c x-B a y|*(B c x+B a y)=|(x-y)-(c-a)| := by
    rw [← abs_of_nonneg (show 0 ≤ B c x+B a y by linarith [hA.1,hB.1]),
      ← abs_mul,hid]
  have htri := abs_sub (x-y) (c-a)
  have hmul := mul_le_mul_of_nonneg_left
    (show (2 : ℝ) ≤ B c x+B a y by linarith [hA.1,hB.1])
    (abs_nonneg (B c x-B a y))
  nlinarith only [habs,htri,hmul]

private theorem inverse_joint_bound {c a x y : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-199/100))
    (ha : a ∈ Icc (-2 : ℝ) (-199/100))
    (hx : x ∈ Icc (-1/100 : ℝ) 2)
    (hy : y ∈ Icc (-1/100 : ℝ) 2) (n : ℕ) :
    |back c n x-back a n y| ≤ |c-a|+|x-y| := by
  induction n with
  | zero =>
    simp only [back_zero]
    linarith only [abs_nonneg (c-a)]
  | succ n ih =>
    have h := branch_joint_bound hc ha
      (inverse_bounds hc hx n) (inverse_bounds ha hy n)
    rw [back_succ,back_succ]
    linarith only [h,ih,abs_nonneg (x-y)]

private theorem factor_bounds {c d : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-199/100))
    (hd : d ∈ Icc (0 : ℝ) (1/100)) (j : ℕ) :
    (back c (j+1) d+back c (j+1) (-d))/4 ∈ Icc (0 : ℝ) 1 := by
  have hpos := inverse_positive_bounds hc
    (show d ∈ Icc (-1/100 : ℝ) 2 by constructor <;> linarith [hd.1,hd.2]) j
  have hneg := inverse_positive_bounds hc
    (show -d ∈ Icc (-1/100 : ℝ) 2 by constructor <;> linarith [hd.1,hd.2]) j
  constructor <;> linarith [hpos.1,hpos.2,hneg.1,hneg.2]

private theorem factor_difference {c a d e : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-199/100))
    (ha : a ∈ Icc (-2 : ℝ) (-199/100))
    (hd : d ∈ Icc (0 : ℝ) (1/100))
    (he : e ∈ Icc (0 : ℝ) (1/100)) (j : ℕ) :
    |(back c (j+1) d+back c (j+1) (-d))/4-
      (back a (j+1) e+back a (j+1) (-e))/4| ≤
      (|c-a|+|d-e|)/2 := by
  have hpos := inverse_joint_bound hc ha
    (show d ∈ Icc (-1/100 : ℝ) 2 by constructor <;> linarith [hd.1,hd.2])
    (show e ∈ Icc (-1/100 : ℝ) 2 by constructor <;> linarith [he.1,he.2]) (j+1)
  have hneg := inverse_joint_bound hc ha
    (show -d ∈ Icc (-1/100 : ℝ) 2 by constructor <;> linarith [hd.1,hd.2])
    (show -e ∈ Icc (-1/100 : ℝ) 2 by constructor <;> linarith [he.1,he.2]) (j+1)
  have hnegabs : |(-d)-(-e)|=|d-e| := by
    rw [show (-d)-(-e)=-(d-e) by ring,abs_neg]
  rw [hnegabs] at hneg
  have htri := abs_add (back c (j+1) d-back a (j+1) e)
    (back c (j+1) (-d)-back a (j+1) (-e))
  have hid : (back c (j+1) d+back c (j+1) (-d))/4-
      (back a (j+1) e+back a (j+1) (-e))/4 =
      ((back c (j+1) d-back a (j+1) e)+
        (back c (j+1) (-d)-back a (j+1) (-e)))/4 := by ring
  rw [hid,abs_div]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ)<4)]
  linarith only [hpos,hneg,htri]

private theorem product_difference (a b : ℕ → ℝ) (n : ℕ)
    (ha : ∀ j < n, a j ∈ Icc (0 : ℝ) 1)
    (hb : ∀ j < n, b j ∈ Icc (0 : ℝ) 1) :
    |(∏ j ∈ Finset.range n, a j)-(∏ j ∈ Finset.range n, b j)| ≤
      ∑ j ∈ Finset.range n, |a j-b j| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha' := ha n (by omega)
    have hb' := hb n (by omega)
    have hprev := ih (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))
    have hpa0 : 0 ≤ ∏ j ∈ Finset.range n, a j :=
      Finset.prod_nonneg (fun j hj => (ha j (Finset.mem_range.mp hj)).1)
    have hpa1 : (∏ j ∈ Finset.range n, a j) ≤ 1 :=
      Finset.prod_le_one (fun j hj => (ha j (Finset.mem_range.mp hj)).1)
        (fun j hj => (ha j (Finset.mem_range.mp hj)).2)
    have hid : (∏ j ∈ Finset.range n, a j)*a n-
        (∏ j ∈ Finset.range n, b j)*b n =
        ((∏ j ∈ Finset.range n, a j)-(∏ j ∈ Finset.range n, b j))*b n+
          (∏ j ∈ Finset.range n, a j)*(a n-b n) := by ring
    have htri := abs_add
      (((∏ j ∈ Finset.range n, a j)-(∏ j ∈ Finset.range n, b j))*b n)
      ((∏ j ∈ Finset.range n, a j)*(a n-b n))
    rw [abs_mul,abs_mul,abs_of_nonneg hb'.1,abs_of_nonneg hpa0] at htri
    have hm1 := mul_le_mul_of_nonneg_left hb'.2
      (abs_nonneg ((∏ j ∈ Finset.range n, a j)-(∏ j ∈ Finset.range n, b j)))
    have hm2 := mul_le_mul_of_nonneg_right hpa1 (abs_nonneg (a n-b n))
    rw [Finset.prod_range_succ,Finset.prod_range_succ,hid,Finset.sum_range_succ]
    nlinarith only [htri,hm1,hm2,hprev]

private theorem endpointProduct_lipschitz_raw {c a d e : ℝ} (p : ℕ)
    (hc : c ∈ Icc (-2 : ℝ) (-199/100))
    (ha : a ∈ Icc (-2 : ℝ) (-199/100))
    (hd : d ∈ Icc (0 : ℝ) (1/100))
    (he : e ∈ Icc (0 : ℝ) (1/100)) :
    |endpointProduct c p d-endpointProduct a p e| ≤
      ((p-1 : ℕ) : ℝ)*(|c-a|+|d-e|)/2 := by
  have hprod := product_difference
    (fun j => (back c (j+1) d+back c (j+1) (-d))/4)
    (fun j => (back a (j+1) e+back a (j+1) (-e))/4) (p-1)
    (fun j _ => factor_bounds hc hd j) (fun j _ => factor_bounds ha he j)
  have hsum : (∑ j ∈ Finset.range (p-1),
      |(back c (j+1) d+back c (j+1) (-d))/4-
        (back a (j+1) e+back a (j+1) (-e))/4|) ≤
      ((p-1 : ℕ) : ℝ)*(|c-a|+|d-e|)/2 := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (p-1), (|c-a|+|d-e|)/2 := by
        exact Finset.sum_le_sum (fun j _ => factor_difference hc ha hd he j)
      _ = _ := by simp; ring
  exact hprod.trans hsum

/-- Joint product control before any return-invariance assumption. -/
theorem endpointProduct_lipschitz {p : ℕ} (hp : 17 ≤ p) {c a d e : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p))
    (ha : a ∈ Icc (-2 : ℝ) (-2+20*scale p))
    (hd : d ∈ Icc (0 : ℝ) (14*scale p))
    (he : e ∈ Icc (0 : ℝ) (14*scale p)) :
    |endpointProduct c p d-endpointProduct a p e| ≤
      2*(p : ℝ)*(|c-a|+|d-e|) := by
  have h := endpointProduct_lipschitz_raw p (wide_band hp hc) (wide_band hp ha)
    (terminal_small hp hd) (terminal_small hp he)
  have hn : ((p-1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hmul := mul_le_mul_of_nonneg_right hn
    (show 0 ≤ |c-a|+|d-e| by positivity)
  have hp0 : 0 ≤ (p : ℝ)*(|c-a|+|d-e|) := by positivity
  linarith only [h,hmul,hp0]

/-- Every endpoint product on the full shooting rectangle stays positive;
this conclusion does not presuppose the boundary equation. -/
theorem endpointProduct_bounds {p : ℕ} (hp : 17 ≤ p) {c d : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p))
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) :
    3/5 ≤ endpointProduct c p d ∧ endpointProduct c p d ≤ 1 := by
  have hwide := wide_band hp hc
  have hds := terminal_small hp hd
  have hn : ((p-1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have heps : 0 ≤ c+2 := by linarith [hc.1]
  have hbudget : ((p-1 : ℕ) : ℝ)*(c+2) ≤ 1/10000 := by
    have h1 := mul_le_mul_of_nonneg_right hn heps
    have h2 := mul_le_mul_of_nonneg_left
      (show c+2 ≤ 20*scale p by linarith [hc.2]) (show (0 : ℝ) ≤ p by positivity)
    have hq := horizon_scale_small hp
    nlinarith only [h1,h2,hq]
  have hpd : ((p-1 : ℕ) : ℝ)*d ≤ 1/200 := by
    have h1 := mul_le_mul_of_nonneg_right hn hd.1
    have h2 := mul_le_mul_of_nonneg_left hd.2 (show (0 : ℝ) ≤ p by positivity)
    have hq := horizon_scale_small hp
    nlinarith only [h1,h2,hq]
  have hbase := normalized_inverse_product_lower (p-1) (by omega) (small_band hp hc)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 2 by norm_num) hbudget
  have hzero : endpointProduct c p 0 =
      ∏ j ∈ Finset.range (p-1), back c (j+1) 0/2 := by
    unfold endpointProduct
    apply Finset.prod_congr rfl
    intro j hj
    simp only [neg_zero]
    ring
  have hdiff := endpointProduct_lipschitz_raw p hwide hwide hds
    (show (0 : ℝ) ∈ Icc (0 : ℝ) (1/100) by norm_num)
  rw [sub_self,abs_zero,sub_zero,abs_of_nonneg hd.1,zero_add,hzero] at hdiff
  have hlo := (abs_le.mp hdiff).1
  constructor
  · linarith only [hbase,hlo,hpd]
  · unfold endpointProduct
    exact Finset.prod_le_one
      (fun j _ => (factor_bounds hwide hds j).1)
      (fun j _ => (factor_bounds hwide hds j).2)

/-- The exact inverse secant identity giving the endpoint boundary equation. -/
theorem endpointProduct_identity {p : ℕ} (hp : 17 ≤ p) {c d : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p))
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) :
    (back c (p-1) d-back c (p-1) (-d))*4^(p-1)*endpointProduct c p d=2*d := by
  have hds := terminal_small hp hd
  have hsec := GlobalInverseWindow.inverse_difference_product (small_band hp hc)
    (show d ∈ Icc (-3/2 : ℝ) 2 by constructor <;> linarith [hds.1,hds.2])
    (show -d ∈ Icc (-3/2 : ℝ) 2 by constructor <;> linarith [hds.1,hds.2]) (p-1)
  have hprod : (∏ j ∈ Finset.range (p-1), (back c (j+1) d+back c (j+1) (-d))) =
      4^(p-1)*endpointProduct c p d := by
    unfold endpointProduct
    calc
      _ = ∏ j ∈ Finset.range (p-1),
          4*((back c (j+1) d+back c (j+1) (-d))/4) := by
        apply Finset.prod_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  rw [hprod] at hsec
  nlinarith only [hsec]

end
end GlobalWindowBoundaryProduct
