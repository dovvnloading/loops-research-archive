import GlobalWindowInverseShape
import GlobalWindowSignedChart

/-!
# Parameter secants of the complete physical return

The normalized return is related to an exact positive inverse product.
Solving that implicit identity controls its quadratic error in both the
normalized coefficient and the spatial variable.  No derivative estimate
for the high iterate is assumed.
-/

namespace GlobalWindowParameterSecant

open Set Function Finset NearTwoInverse NearTwoShooting
open LimitingCrestQuadraticReturn GlobalRestrictiveWindow
open GlobalWindowInverseShape GlobalWindowSignedChart
open scoped BigOperators

noncomputable section

def returnError (c : ℝ) (p : ℕ) (z : ℝ) : ℝ :=
  realReturn c p z-(1-kappa p c*z^2)

private theorem unit_square {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) : z^2 ≤ 1 := by
  nlinarith [mul_nonneg (show 0 ≤ 1-z by linarith [hz.2])
    (show 0 ≤ 1+z by linarith [hz.1])]

private theorem unit_square_difference {z w : ℝ}
    (hz : z ∈ Icc (-1 : ℝ) 1) (hw : w ∈ Icc (-1 : ℝ) 1) :
    |z^2-w^2| ≤ 2*|z-w| := by
  have hsum : |z+w| ≤ 2 := by
    have htri := abs_add_le z w
    linarith [abs_le.mpr hz,abs_le.mpr hw]
  have hm := mul_le_mul_of_nonneg_left hsum (abs_nonneg (z-w))
  rw [show z^2-w^2=(z-w)*(z+w) by ring,abs_mul]
  nlinarith only [hm]

private theorem physical_input {c z : ℝ} {p : ℕ}
    (hc : PositiveRestrictiveReturn c p) (hz : z ∈ Icc (-1 : ℝ) 1) :
    criticalValue c p*z ∈ returnInterval c p := by
  have hlo := mul_le_mul_of_nonneg_left hz.1 hc.return_pos.le
  have hup := mul_le_mul_of_nonneg_left hz.2 hc.return_pos.le
  constructor <;> linarith only [hlo,hup]

/-- Exact implicit equation for the literal normalized return. -/
theorem inverse_return_identity {p : ℕ} (hp : 17 ≤ p) {c z : ℝ}
    (hc : PositiveRestrictiveReturn c p) (hz : z ∈ Icc (-1 : ℝ) 1) :
    realReturn c p z = 1-kappa p c*z^2*inverseRatio c p (realReturn c p z) := by
  let d := criticalValue c p
  let y := realReturn c p z
  have hd : 0 < d := hc.return_pos
  have hy : y ∈ Icc (-1 : ℝ) 1 := realReturn_mapsTo hc hz
  have hinput := physical_input hc hz
  have hreturn : d*y=(realMap c)^[p] (d*z) := by
    dsimp [d,y,realReturn]
    field_simp [hc.return_pos.ne']
  have hback := hc.inverse_endpoint (by omega : 2 ≤ p) hinput
  have hcrit := hc.critical_inverse (by omega : 2 ≤ p)
  have hback' : back c (p-1) (d*y) = -c-(d*z)^2 := by
    rw [hreturn]
    change back c (p-1) ((realMap c)^[p] (d*z)) = -c-(d*z)^2
    dsimp [realMap] at hback
    nlinarith only [hback]
  have hdiff : back c (p-1) d-back c (p-1) (d*y)=d^2*z^2 := by
    change back c (p-1) d = -c at hcrit
    nlinarith only [hcrit,hback']
  have hdsmall : d ≤ 1/100 := by
    have hs := hc.return_scale hp
    have hq := scale_small hp
    dsimp [d]
    linarith
  have hdylo := mul_le_mul_of_nonneg_left hy.1 hd.le
  have hdyup := mul_le_mul_of_nonneg_left hy.2 hd.le
  have hsec := GlobalInverseWindow.inverse_difference_product (hc.small_parameter_band hp)
    (show d ∈ Icc (-3/2 : ℝ) 2 by constructor <;> linarith only [hd.le,hdsmall])
    (show d*y ∈ Icc (-3/2 : ℝ) 2 by
      constructor <;> nlinarith only [hdylo,hdyup,hdsmall]) (p-1)
  have hprod : (∏ j ∈ Finset.range (p-1), (back c (j+1) d+back c (j+1) (d*y))) =
      (4 : ℝ)^(p-1)*phaseProduct c p d y := by
    unfold phaseProduct
    calc
      _ = ∏ j ∈ Finset.range (p-1), 4*((back c (j+1) d+back c (j+1) (d*y))/4) := by
        apply Finset.prod_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  rw [hdiff,hprod] at hsec
  have hmain : d*z^2*(4 : ℝ)^(p-1)*phaseProduct c p d y = 1-y := by
    apply mul_left_cancel₀ hd.ne'
    nlinarith only [hsec]
  have hP := phaseProduct_bounds hp hc (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
  have hP0 : phaseProduct c p d 1 ≠ 0 := by
    have hlow : 3/5 ≤ phaseProduct c p d 1 := hP.1
    linarith only [hlow]
  have hratio : kappa p c*z^2*inverseRatio c p y =
      d*z^2*(4 : ℝ)^(p-1)*phaseProduct c p d y := by
    rw [kappa_product hp hc]
    dsimp [inverseRatio,d]
    field_simp [hP0]
    ring
  change y=1-kappa p c*z^2*inverseRatio c p y
  rw [hratio]
  linarith only [hmain]

theorem returnError_identity {p : ℕ} (hp : 17 ≤ p) {c z : ℝ}
    (hc : PositiveRestrictiveReturn c p) (hz : z ∈ Icc (-1 : ℝ) 1) :
    returnError c p z = kappa p c*z^2*(1-inverseRatio c p (realReturn c p z)) := by
  have h := inverse_return_identity hp hc hz
  unfold returnError
  nlinarith only [h]

private theorem error_difference (k l s t R S : ℝ) :
    |k*s*(1-R)-l*t*(1-S)| ≤ |k*s-l*t| * |1-R| + |l*t| * |R-S| := by
  have hid : k*s*(1-R)-l*t*(1-S)=(k*s-l*t)*(1-R)-l*t*(R-S) := by ring
  rw [hid]
  have ht := abs_sub ((k*s-l*t)*(1-R)) (l*t*(R-S))
  simpa only [abs_mul] using ht

private theorem return_difference (c a z w : ℝ) (p : ℕ) :
    |realReturn c p z-realReturn a p w| ≤
      |kappa p c*z^2-kappa p a*w^2| + |returnError c p z-returnError a p w| := by
  have hid : realReturn c p z-realReturn a p w =
      (returnError c p z-returnError a p w)-(kappa p c*z^2-kappa p a*w^2) := by
    unfold returnError
    ring
  rw [hid]
  have ht := abs_sub (returnError c p z-returnError a p w)
    (kappa p c*z^2-kappa p a*w^2)
  linarith only [ht]

private theorem coefficient_term_bound {p : ℕ} (hp : 17 ≤ p) {c z : ℝ}
    (hc : PositiveRestrictiveReturn c p) (hz : z ∈ Icc (-1 : ℝ) 1) :
    |kappa p c*z^2| ≤ 7/2 := by
  have hk := kappa_bounds hp hc
  have hs := unit_square hz
  rw [abs_of_nonneg (mul_nonneg hk.1.le (sq_nonneg z))]
  have hm := mul_le_mul_of_nonneg_left hs hk.1.le
  nlinarith only [hm,hk.2]

private theorem absorption_budget {p : ℕ} (hp : 17 ≤ p) :
    (49/2 : ℝ)*(p : ℝ)*scale p ≤ 1/100 := by
  have hq := horizon_scale_small hp
  linarith

/-- The quadratic error changes at most by 200 p 4^(-p) times the
actual normalized-coefficient separation.  Both maps are complete
physical restrictive returns; no derivative control is assumed. -/
theorem parameter_error_lipschitz {p : ℕ} (hp : 17 ≤ p) {c a z : ℝ}
    (hc : PositiveRestrictiveReturn c p) (ha : PositiveRestrictiveReturn a p)
    (hz : z ∈ Icc (-1 : ℝ) 1) :
    |(realReturn c p z-(1-kappa p c*z^2))-
      (realReturn a p z-(1-kappa p a*z^2))| ≤
      200*(p : ℝ)*scale p*|kappa p c-kappa p a| := by
  have hcy := realReturn_mapsTo hc hz
  have hay := realReturn_mapsTo ha hz
  have hs := unit_square hz
  have hcoef : |kappa p c*z^2-kappa p a*z^2| ≤ |kappa p c-kappa p a| := by
    rw [show kappa p c*z^2-kappa p a*z^2=(kappa p c-kappa p a)*z^2 by ring,
      abs_mul,abs_of_nonneg (sq_nonneg z)]
    have hm := mul_le_mul_of_nonneg_left hs (abs_nonneg (kappa p c-kappa p a))
    nlinarith only [hm]
  have hratio := inverseRatio_lipschitz hp hc ha hcy hay
  have hscale := return_scale_kappa_lipschitz hp hc ha
  have hmScale := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 5*(p : ℝ) by positivity)
  have hratio' : |inverseRatio c p (realReturn c p z)-inverseRatio a p (realReturn a p z)| ≤
      40*(p : ℝ)*scale p*|kappa p c-kappa p a| + 
        7*(p : ℝ)*scale p*|realReturn c p z-realReturn a p z| := by
    nlinarith only [hratio,hmScale]
  have hnear := inverseRatio_near_one hp hc hcy
  rw [abs_sub_comm] at hnear
  have htriangle := error_difference (kappa p c) (kappa p a) (z^2) (z^2)
    (inverseRatio c p (realReturn c p z)) (inverseRatio a p (realReturn a p z))
  rw [← returnError_identity hp hc hz,← returnError_identity hp ha hz] at htriangle
  have hm1 := mul_le_mul hcoef hnear (abs_nonneg _)
    (abs_nonneg (kappa p c-kappa p a))
  have hm2 := mul_le_mul (coefficient_term_bound hp ha hz) hratio'
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 7/2)
  have herror : |returnError c p z-returnError a p z| ≤
      14*(p : ℝ)*scale p*|kappa p c-kappa p a| + 
      (7/2)*(40*(p : ℝ)*scale p*|kappa p c-kappa p a| + 
        7*(p : ℝ)*scale p*|realReturn c p z-realReturn a p z|) := by
    nlinarith only [htriangle,hm1,hm2]
  have hmap0 := return_difference c a z z p
  have hmap : |realReturn c p z-realReturn a p z| ≤
      |kappa p c-kappa p a| + |returnError c p z-returnError a p z| := by
    linarith only [hmap0,hcoef]
  have hmapmul := mul_le_mul_of_nonneg_left hmap
    (show 0 ≤ (49/2 : ℝ)*(p : ℝ)*scale p by positivity)
  have habsorb := mul_le_mul_of_nonneg_right (absorption_budget hp)
    (abs_nonneg (returnError c p z-returnError a p z))
  have hn : 0 ≤ (p : ℝ)*scale p*|kappa p c-kappa p a| := by positivity
  change |returnError c p z-returnError a p z| ≤ _
  nlinarith only [herror,hmapmul,habsorb,hn]

/-- The same complete error is spatially Lipschitz with an explicitly
small constant throughout the invariant unit interval. -/
theorem spatial_error_lipschitz {p : ℕ} (hp : 17 ≤ p) {c z w : ℝ}
    (hc : PositiveRestrictiveReturn c p)
    (hz : z ∈ Icc (-1 : ℝ) 1) (hw : w ∈ Icc (-1 : ℝ) 1) :
    |(realReturn c p z-(1-kappa p c*z^2))-
      (realReturn c p w-(1-kappa p c*w^2))| ≤
      300*(p : ℝ)*scale p*|z-w| := by
  have hzy := realReturn_mapsTo hc hz
  have hwy := realReturn_mapsTo hc hw
  have hk := kappa_bounds hp hc
  have hs := unit_square_difference hz hw
  have hcoef : |kappa p c*z^2-kappa p c*w^2| ≤ 7*|z-w| := by
    rw [show kappa p c*z^2-kappa p c*w^2=kappa p c*(z^2-w^2) by ring,
      abs_mul,abs_of_pos hk.1]
    have hm := mul_le_mul hk.2.le hs (abs_nonneg (z^2-w^2))
      (by norm_num : (0 : ℝ) ≤ 7/2)
    nlinarith only [hm]
  have hratio := inverseRatio_lipschitz hp hc hc hzy hwy
  simp only [sub_self,abs_zero,mul_zero,zero_add] at hratio
  have hnear := inverseRatio_near_one hp hc hzy
  rw [abs_sub_comm] at hnear
  have htriangle := error_difference (kappa p c) (kappa p c) (z^2) (w^2)
    (inverseRatio c p (realReturn c p z)) (inverseRatio c p (realReturn c p w))
  rw [← returnError_identity hp hc hz,← returnError_identity hp hc hw] at htriangle
  have hm1 := mul_le_mul hcoef hnear (abs_nonneg _)
    (show 0 ≤ 7*|z-w| by positivity)
  have hm2 := mul_le_mul (coefficient_term_bound hp hc hw) hratio
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 7/2)
  have herror : |returnError c p z-returnError c p w| ≤
      98*(p : ℝ)*scale p*|z-w| + 
        (49/2)*(p : ℝ)*scale p*|realReturn c p z-realReturn c p w| := by
    nlinarith only [htriangle,hm1,hm2]
  have hmap0 := return_difference c c z w p
  have hmap : |realReturn c p z-realReturn c p w| ≤
      7*|z-w| + |returnError c p z-returnError c p w| := by
    linarith only [hmap0,hcoef]
  have hmapmul := mul_le_mul_of_nonneg_left hmap
    (show 0 ≤ (49/2 : ℝ)*(p : ℝ)*scale p by positivity)
  have habsorb := mul_le_mul_of_nonneg_right (absorption_budget hp)
    (abs_nonneg (returnError c p z-returnError c p w))
  have hn : 0 ≤ (p : ℝ)*scale p*|z-w| := by positivity
  change |returnError c p z-returnError c p w| ≤ _
  nlinarith only [herror,hmapmul,habsorb,hn]

end
end GlobalWindowParameterSecant
