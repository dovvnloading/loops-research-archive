import GlobalWindowLocalization

/-!
# Quantitative thickness of the entire positive restrictive window

The parameter separation is controlled by the actual critical-return
separation.  Combining the inverse-endpoint localization with this estimate
bounds the diameter of the full physical parameter class at the base-sixteen
scale; neither parameter is selected by a prescribed critical relation.
-/

namespace GlobalWindowThickness

open Set Function Finset NearTwoInverse NearTwoShooting
open LimitingCrestQuadraticReturn GlobalRestrictiveWindow
open scoped BigOperators

noncomputable section

private theorem band {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000)) :
    c ∈ Icc (-2 : ℝ) (-49/25) :=
  ⟨hc.1,by linarith [hc.2]⟩

/-- A uniform secant estimate on the positive inverse branch, with its
complete product rather than a product of separate coarse contractions. -/
theorem positive_inverse_secant {c x y : ℝ} {n : ℕ} (hn : 3 ≤ n)
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hbudget : (n : ℝ)*(c+2) ≤ 1/10000)
    (hx : x ∈ Icc (0 : ℝ) 2) (hy : y ∈ Icc (0 : ℝ) 2) :
    (3/5 : ℝ)*4^n*|back c n x-back c n y| ≤ |x-y| := by
  let P := ∏ j ∈ Finset.range n, (back c (j+1) x+back c (j+1) y)
  have hbase := normalized_inverse_product_lower n hn hc
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 2 by norm_num) hbudget
  have hprod : (4 : ℝ)^n *
      (∏ j ∈ Finset.range n, back c (j+1) 0/2) ≤ P := by
    calc
      _ = ∏ j ∈ Finset.range n, 4*(back c (j+1) 0/2) := by
        rw [Finset.prod_mul_distrib]
        simp
      _ ≤ P := by
        apply Finset.prod_le_prod
        · intro j hj
          have h := back_bounds (band hc)
            (show (0 : ℝ) ∈ Icc (0 : ℝ) 2 by norm_num) (j+1)
          have hb : 0 ≤ back c (j+1) 0 := h.1
          positivity
        · intro j hj
          have h1 := back_mono_initial c (j+1) hx.1
          have h2 := back_mono_initial c (j+1) hy.1
          linarith only [h1,h2]
  have hp0 : (0 : ℝ) ≤ 4^n := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbase hp0
  have hPlower : (3/5 : ℝ)*4^n ≤ P := by
    nlinarith only [hmul,hprod,hp0]
  have hPnonneg : 0 ≤ P := (by positivity : (0 : ℝ) ≤ (3/5)*4^n).trans hPlower
  have hsec := GlobalInverseWindow.inverse_difference_product hc
    (show x ∈ Icc (-3/2 : ℝ) 2 from ⟨by linarith [hx.1],hx.2⟩)
    (show y ∈ Icc (-3/2 : ℝ) 2 from ⟨by linarith [hy.1],hy.2⟩) n
  change (back c n x-back c n y)*P=x-y at hsec
  have habs := congrArg abs hsec
  rw [abs_mul,abs_of_nonneg hPnonneg] at habs
  have hcmp := mul_le_mul_of_nonneg_right hPlower
    (abs_nonneg (back c n x-back c n y))
  nlinarith only [hcmp,habs]

private theorem parameter_shooting_lower {a c d e : ℝ} (n : ℕ)
    (ha : a ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (he : e ∈ Icc (0 : ℝ) 2)
    (ha0 : shooting n e a=0) (hc0 : shooting n d c=0) :
    (12/5 : ℝ)*|c-a| ≤ |back c n d-back c n e| := by
  have hpar := NearTwoInverse.back_parameter_lipschitz (band hc) (band ha) he n
  have hid : c^2+c-(a^2+a) = back c n d-back a n e := by
    dsimp [shooting] at ha0 hc0
    linarith only [ha0,hc0]
  have hfactor : c^2+c-(a^2+a) = (c-a)*(c+a+1) := by ring
  have hsgn : c+a+1<0 := by linarith [ha.2,hc.2]
  have habs : |c^2+c-(a^2+a)| = |c-a| * (-(c+a+1)) := by
    rw [hfactor,abs_mul,abs_of_neg hsgn]
  have htri : |back c n d-back a n e| ≤
      |back c n d-back c n e|+|back c n e-back a n e| := by
    exact abs_sub_le _ _ _
  have hcoef : 299/100 ≤ -(c+a+1) := by linarith [ha.2,hc.2]
  have hmul := mul_le_mul_of_nonneg_left hcoef (abs_nonneg (c-a))
  rw [hid] at habs
  nlinarith only [hpar,htri,habs,hmul,abs_nonneg (c-a)]

/-- Parameter differences along the complete shooting relation are
controlled by the terminal-return differences at an explicit inverse scale. -/
theorem shooting_parameter_comparison {a c d e : ℝ} {p : ℕ}
    (hp : 17 ≤ p)
    (ha : a ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hc : c ∈ Icc (-2 : ℝ) (-2+1/10000))
    (hbudget : ((p-2 : ℕ) : ℝ)*(c+2) ≤ 1/10000)
    (hd : d ∈ Icc (0 : ℝ) 2) (he : e ∈ Icc (0 : ℝ) 2)
    (ha0 : shooting (p-2) e a=0) (hc0 : shooting (p-2) d c=0) :
    (9/100 : ℝ)*4^p*|c-a| ≤ |d-e| := by
  have hs := parameter_shooting_lower (p-2) ha hc he ha0 hc0
  have hi := positive_inverse_secant (by omega : 3 ≤ p-2) hc hbudget hd he
  have hm := mul_le_mul_of_nonneg_left hs
    (show (0 : ℝ) ≤ (3/5)*4^(p-2) by positivity)
  have hpower : (4 : ℝ)^p=4^(p-2)*16 := by
    have heq := pow_add (4 : ℝ) (p-2) 2
    rw [Nat.sub_add_cancel (by omega : 2 ≤ p)] at heq
    norm_num at heq
    exact heq
  rw [hpower]
  nlinarith only [hs,hi,hm]

private theorem restrictive_shooting {c : ℝ} {p : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p) :
    shooting (p-2) (criticalValue c p) c=0 := by
  have he := NearTwoShooting.forward_orbit_shooting (c := c) (n := p-2)
    (by
      intro j hj
      exact (h.critical_prefix (j+2) (by omega) (by omega)).le)
  simpa only [Nat.sub_add_cancel (by omega : 2 ≤ p)] using he

/-- The entire physical positive-itinerary restrictive parameter class
has diameter less than 160 times 16 to the negative period. -/
theorem restrictive_parameter_thickness {a c : ℝ} {p : ℕ}
    (hp : 17 ≤ p)
    (ha : PositiveRestrictiveReturn a p) (hc : PositiveRestrictiveReturn c p) :
    |c-a| < 160*(1/16 : ℝ)^p := by
  have har := ha.return_scale hp
  have hcr := hc.return_scale hp
  have hq0 := scale_pos p
  have hq := scale_small hp
  have hb : ((p-2 : ℕ) : ℝ)*(c+2) ≤ 1/10000 := by
    have hn : ((p-2 : ℕ) : ℝ) ≤ (p-1 : ℕ) := by exact_mod_cast (show p-2 ≤ p-1 by omega)
    have hmul := mul_le_mul_of_nonneg_right hn (show 0 ≤ c+2 by linarith [hc.parameter_band.1])
    exact hmul.trans (hc.inverse_parameter_budget hp)
  have hcomp := shooting_parameter_comparison hp (ha.small_parameter_band hp)
    (hc.small_parameter_band hp) hb
    (show criticalValue c p ∈ Icc (0 : ℝ) 2 from
      ⟨hc.return_pos.le,by linarith⟩)
    (show criticalValue a p ∈ Icc (0 : ℝ) 2 from
      ⟨ha.return_pos.le,by linarith⟩)
    (restrictive_shooting hp ha) (restrictive_shooting hp hc)
  have hdif : |criticalValue c p-criticalValue a p| < 14*scale p := by
    apply abs_lt.mpr
    constructor <;> linarith [ha.return_pos,hc.return_pos]
  have hsmall : (9/100 : ℝ)*4^p*|c-a| < 14*scale p := hcomp.trans_lt hdif
  have hm := mul_lt_mul_of_pos_right hsmall hq0
  have hpow : (4 : ℝ)^p*scale p=1 := by
    unfold scale
    rw [← mul_pow]
    norm_num
  have hbound : (9/100 : ℝ)*|c-a| < 14*(scale p)^2 := by
    calc
      (9/100 : ℝ)*|c-a| = ((9/100 : ℝ)*4^p*|c-a|)*scale p := by
        calc
          (9/100 : ℝ)*|c-a| = ((9/100 : ℝ)*|c-a|)*(4^p*scale p) := by
            rw [hpow]
            ring
          _ = _ := by ring
      _ < (14*scale p)*scale p := hm
      _ = _ := by ring
  have hsq : 0 < (scale p)^2 := sq_pos_of_pos hq0
  have hfinish : |c-a| < 160*(scale p)^2 := by nlinarith only [hbound,hsq]
  have hscale : (scale p)^2 = (1/16 : ℝ)^p := by
    unfold scale
    rw [pow_two,← mul_pow]
    norm_num
  simpa only [hscale] using hfinish

end
end GlobalWindowThickness
