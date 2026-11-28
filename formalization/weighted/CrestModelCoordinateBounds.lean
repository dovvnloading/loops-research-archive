import LimitingCrestParameter
import CrestResponseConstants
import Mathlib.Tactic

/-!
# Exact enclosures of the limiting endpoint coordinates

The centers below are not selected numerical substitutes.  Strict
monotonicity of the existing signed critical relation isolates its unique
root.  The backward endpoint equations then isolate every positive
coordinate, by rational inequalities checked in the kernel.
-/

namespace CrestModelCoordinateBounds

open Set LoopsLimitingCrestParameter CrestResponseConstants

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private def kLo : ℝ := 1790327491999345703396901954182 / 10^30
private def kHi : ℝ := 1790327491999345703396901954183 / 10^30
private def tLo : ℝ := 105693616295483635833232893739 / 10^29
private def tHi : ℝ := 105693616295483635833232893744 / 10^29
private def yLo : ℝ := 1783314158186803426422684216 / 10^28
private def yHi : ℝ := 1783314158186803426422684221 / 10^28
private def sLo : ℝ := 567369155071188741146305252 / 10^27
private def sHi : ℝ := 567369155071188741146305257 / 10^27
private def xLo : ℝ := 7503086636018655687544370 / 10^25
private def xHi : ℝ := 7503086636018655687544375 / 10^25
private def vLo : ℝ := 663781921655845594656450 / 10^25
private def vHi : ℝ := 663781921655845594656455 / 10^25
private def rLo : ℝ := 6637890981622391796485 / 10^23
private def rHi : ℝ := 6637890981622391796490 / 10^23

private theorem isolating_signs : relation kLo < 0 ∧ 0 < relation kHi := by
  norm_num [kLo,kHi,relation,criticalOrbit,Q]

private theorem parameter_bounds {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) : kLo ≤ k ∧ k ≤ kHi := by
  have hL : kLo ∈ parameterInterval := by norm_num [kLo,parameterInterval]
  have hU : kHi ∈ parameterInterval := by norm_num [kHi,parameterInterval]
  constructor
  · by_contra h
    have hm := relation_strictMonoOn hk hL (lt_of_not_ge h)
    rw [hroot] at hm
    linarith only [hm,isolating_signs.1]
  · by_contra h
    have hm := relation_strictMonoOn hU hk (lt_of_not_ge h)
    rw [hroot] at hm
    linarith only [hm,isolating_signs.2]

/-- The existing limiting parameter, rather than a separately chosen
rational value, lies in the stated certified neighborhood. -/
theorem limiting_parameter_center {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) : |k-kRef| ≤ 1/10^22 := by
  obtain ⟨hl,hu⟩ := parameter_bounds hk hroot
  dsimp [kLo,kHi] at hl hu
  dsimp [kRef]
  exact abs_le.mpr ⟨by linarith only [hl],by linarith only [hu]⟩

private theorem weighted_square_bounds {a aL aU x xL xU sL sU : ℝ}
    (haL : 0 < aL) (ha : aL ≤ a ∧ a ≤ aU) (hx : 0 ≤ x)
    (hxL : 0 ≤ xL) (hxU : 0 ≤ xU)
    (hs : sL ≤ a*x^2 ∧ a*x^2 ≤ sU)
    (hL : aU*xL^2 ≤ sL) (hU : sU ≤ aL*xU^2) :
    xL ≤ x ∧ x ≤ xU := by
  have haU : 0 < aU := lt_of_lt_of_le (lt_of_lt_of_le haL ha.1) ha.2
  constructor
  · apply (sq_le_sq₀ hxL hx).mp
    have hm := hL.trans (hs.1.trans (mul_le_mul_of_nonneg_right ha.2 (sq_nonneg x)))
    by_contra h
    have ht := mul_lt_mul_of_pos_left (lt_of_not_ge h) haU
    exact (not_lt_of_ge hm) ht
  · apply (sq_le_sq₀ hx hxU).mp
    have hm := (mul_le_mul_of_nonneg_right ha.1 (sq_nonneg x)).trans (hs.2.trans hU)
    by_contra h
    have ht := mul_lt_mul_of_pos_left (lt_of_not_ge h) haL
    exact (not_lt_of_ge hm) ht

/-- Every positive solution of the exact backward endpoint system at
the canonical limiting parameter has the same small coordinate boxes.
The later physical theorem supplies these equations for the archive's
actual selected model endpoint. -/
theorem model_system_center_bounds {k T Y x v r : ℝ}
    (hk : k ∈ parameterInterval) (hroot : relation k = 0)
    (hT0 : 0 ≤ T) (hY0 : 0 ≤ Y) (hx0 : 0 ≤ x) (hv0 : 0 ≤ v) (hr0 : 0 ≤ r)
    (hT : k*T^2 = 2) (hY : 1+k*Y^2 = T)
    (hx : k*(x^2-v^2) = 1) (hv : 2*k*x*v = Y)
    (hr : (x-3/4)^2+v^2 = r^2) :
    |k-kRef| ≤ 1/10^22 ∧ |T-tRef| ≤ 1/10^22 ∧
      |Y-yRef| ≤ 1/10^22 ∧ |x-xRef| ≤ 1/10^22 ∧
      |v-vRef| ≤ 1/10^22 ∧ |r-rRef| ≤ 1/10^22 := by
  have hkb := parameter_bounds hk hroot
  have hkl : 0 < kLo := by norm_num [kLo]
  have hk0 : 0 < k := lt_of_lt_of_le hkl hkb.1
  have htb : tLo ≤ T ∧ T ≤ tHi := by
    apply weighted_square_bounds hkl hkb hT0
      (by norm_num [tLo]) (by norm_num [tHi])
      (show (2 : ℝ) ≤ k*T^2 ∧ k*T^2 ≤ 2 by rw [hT]; exact ⟨le_rfl,le_rfl⟩)
    · norm_num [kHi,tLo]
    · norm_num [kLo,tHi]
  have hyb : yLo ≤ Y ∧ Y ≤ yHi := by
    apply weighted_square_bounds hkl hkb hY0
      (by norm_num [yLo]) (by norm_num [yHi])
      (show tLo-1 ≤ k*Y^2 ∧ k*Y^2 ≤ tHi-1 by
        constructor <;> linarith only [hY,htb.1,htb.2])
    · norm_num [kHi,yLo,tLo]
    · norm_num [kLo,yHi,tHi]
  have hk2 : kLo^2 ≤ k^2 ∧ k^2 ≤ kHi^2 :=
    ⟨pow_le_pow_left₀ hkl.le hkb.1 2,pow_le_pow_left₀ hk0.le hkb.2 2⟩
  have hy2 : yLo^2 ≤ Y^2 ∧ Y^2 ≤ yHi^2 :=
    ⟨pow_le_pow_left₀ (by norm_num [yLo]) hyb.1 2,
      pow_le_pow_left₀ hY0 hyb.2 2⟩
  have hsEq : k^2*(x^2+v^2)^2 = 1+Y^2 := by
    have ha := congrArg (fun z : ℝ => z^2) hx
    have hb := congrArg (fun z : ℝ => z^2) hv
    nlinarith only [ha,hb]
  have hsb : sLo ≤ x^2+v^2 ∧ x^2+v^2 ≤ sHi := by
    apply weighted_square_bounds (sq_pos_of_pos hkl) hk2 (by positivity)
      (by norm_num [sLo]) (by norm_num [sHi])
      (show 1+yLo^2 ≤ k^2*(x^2+v^2)^2 ∧
          k^2*(x^2+v^2)^2 ≤ 1+yHi^2 by
        rw [hsEq]
        exact ⟨add_le_add le_rfl hy2.1,add_le_add le_rfl hy2.2⟩)
    · norm_num [kHi,sLo,yLo]
    · norm_num [kLo,sHi,yHi]
  have hdiff : x^2-v^2 = 1/k := by
    apply (eq_div_iff hk0.ne').mpr
    nlinarith only [hx]
  have hrec : 1/kHi ≤ 1/k ∧ 1/k ≤ 1/kLo := by
    constructor
    · apply (le_div_iff₀ hk0).mpr
      have hm := mul_le_mul_of_nonneg_left hkb.2 (by norm_num [kHi] : 0 ≤ 1/kHi)
      norm_num [kHi] at hm ⊢
      linarith only [hm]
    · apply (div_le_iff₀ hk0).mpr
      have hm := mul_le_mul_of_nonneg_left hkb.1 (by norm_num [kLo] : 0 ≤ 1/kLo)
      norm_num [kLo] at hm ⊢
      linarith only [hm]
  have hxb : xLo ≤ x ∧ x ≤ xHi := by
    constructor
    · apply (sq_le_sq₀ (by norm_num [xLo]) hx0).mp
      have hcert : 2*xLo^2 ≤ sLo+1/kHi := by norm_num [xLo,sLo,kHi]
      nlinarith only [hdiff,hrec.1,hsb.1,hcert]
    · apply (sq_le_sq₀ hx0 (by norm_num [xHi])).mp
      have hcert : sHi+1/kLo ≤ 2*xHi^2 := by norm_num [xHi,sHi,kLo]
      nlinarith only [hdiff,hrec.2,hsb.2,hcert]
  have hvb : vLo ≤ v ∧ v ≤ vHi := by
    constructor
    · apply (sq_le_sq₀ (by norm_num [vLo]) hv0).mp
      have hcert : 2*vLo^2 ≤ sLo-1/kLo := by norm_num [vLo,sLo,kLo]
      nlinarith only [hdiff,hrec.2,hsb.1,hcert]
    · apply (sq_le_sq₀ hv0 (by norm_num [vHi])).mp
      have hcert : sHi-1/kHi ≤ 2*vHi^2 := by norm_num [vHi,sHi,kHi]
      nlinarith only [hdiff,hrec.1,hsb.2,hcert]
  have hrb : rLo ≤ r ∧ r ≤ rHi := by
    constructor
    · apply (sq_le_sq₀ (by norm_num [rLo]) hr0).mp
      have hcert : rLo^2 ≤ sLo-(3/2)*xHi+9/16 := by norm_num [rLo,sLo,xHi]
      nlinarith only [hr,hsb.1,hxb.2,hcert]
    · apply (sq_le_sq₀ hr0 (by norm_num [rHi])).mp
      have hcert : sHi-(3/2)*xLo+9/16 ≤ rHi^2 := by norm_num [rHi,sHi,xLo]
      nlinarith only [hr,hsb.2,hxb.1,hcert]
  refine ⟨limiting_parameter_center hk hroot,?_,?_,?_,?_,?_⟩
  · dsimp [tLo,tHi] at htb
    dsimp [tRef]
    exact abs_le.mpr ⟨by linarith only [htb.1],by linarith only [htb.2]⟩
  · dsimp [yLo,yHi] at hyb
    dsimp [yRef]
    exact abs_le.mpr ⟨by linarith only [hyb.1],by linarith only [hyb.2]⟩
  · dsimp [xLo,xHi] at hxb
    dsimp [xRef]
    exact abs_le.mpr ⟨by linarith only [hxb.1],by linarith only [hxb.2]⟩
  · dsimp [vLo,vHi] at hvb
    dsimp [vRef]
    exact abs_le.mpr ⟨by linarith only [hvb.1],by linarith only [hvb.2]⟩
  · dsimp [rLo,rHi] at hrb
    dsimp [rRef]
    exact abs_le.mpr ⟨by linarith only [hrb.1],by linarith only [hrb.2]⟩

end
end CrestModelCoordinateBounds
