import GlobalWindowSignedChart
import QuadraticCrestDividedDifference

/-!
# Uniform even secants on the full physical restrictive window

The complete divided-difference estimate is applied at the globally
derived return scale.  Its exact identity permits cancellation of the
period-three center factor before comparing signed return relations.
-/

namespace GlobalWindowSecant

open Set Function NearTwoShooting LimitingCrestQuadraticReturn
open GlobalRestrictiveWindow GlobalWindowSignedChart QuadraticCrestDividedDifference

noncomputable section

def realSecant (c : ℝ) (p : ℕ) (x y : ℝ) : ℝ :=
  -(normalizedSecant c p (x : ℂ) (y : ℂ)).re

theorem normalized_secant_error {c : ℝ} {p : ℕ} (hp : 17≤p)
    (h : PositiveRestrictiveReturn c p) {z w : ℂ} (hz : ‖z‖≤1) (hw : ‖w‖≤1) :
    ‖normalizedSecant c p z w+(kappa p c : ℂ)‖≤43*scale p := by
  let d := criticalValue c p
  let S : ℝ := 4^p
  have hd : 0<d := h.return_pos
  have hS : 0<S := by dsimp [S]; positivity
  have hSq : S*scale p=1 := by
    dsimp [S,scale]
    rw [← mul_pow]
    norm_num
  have hq := scale_small hp
  have hSd : S*d≤14 := by
    have hm := mul_le_mul_of_nonneg_left (h.return_scale hp).le hS.le
    change S*d≤S*(14*scale p) at hm
    nlinarith only [hm,hSq]
  have hSd0 : 0≤S*d := mul_nonneg hS.le hd.le
  have hscale : S*d^2≤1 := by
    have hm := mul_le_mul_of_nonneg_right hSd hd.le
    have hsmall : d≤14*scale p := (h.return_scale hp).le
    nlinarith only [hm,hsmall,hq]
  have hdz : ‖(d : ℂ)*z‖≤d := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hd.le
  have hdw : ‖(d : ℂ)*w‖≤d := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hw hd.le
  have he := evenSecant_error c (p-1) d ((d : ℂ)*z) ((d : ℂ)*w) hd.le
    (fun j _ => critical_bound c ⟨h.parameter_band.1,by linarith [h.parameter_band.2]⟩ j)
    (by simpa only [Nat.sub_add_cancel (by omega : 1≤p)] using hscale) hdz hdw
  rw [Nat.sub_add_cancel (by omega : 1≤p)] at he
  change ‖evenSecant c (p-1) ((d : ℂ)*z) ((d : ℂ)*w)-
    (quadraticCoefficient c (p-1) : ℂ)‖≤4^(p-1)*(S*d^2)/16 at he
  have hid : normalizedSecant c p z w+(kappa p c : ℂ)=
      (d : ℂ)*(evenSecant c (p-1) ((d : ℂ)*z) ((d : ℂ)*w)-
        (quadraticCoefficient c (p-1) : ℂ)) := by
    simp only [normalizedSecant,kappa,Complex.ofReal_mul,Complex.ofReal_neg]
    change (d : ℂ)*_+(-(quadraticCoefficient c (p-1) : ℂ))*(d : ℂ)=_
    ring
  rw [hid,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
  apply (mul_le_mul_of_nonneg_left he hd.le).trans
  have hpower : (4 : ℝ)^(p-1)*4=S := by
    dsimp [S]
    rw [← pow_succ,Nat.sub_add_cancel (by omega : 1≤p)]
  have hform : (d*(4^(p-1)*(S*d^2)/16))*S=(S*d)^3/64 := by
    rw [← hpower]
    ring
  have hcube := pow_le_pow_left₀ hSd0 hSd 3
  have hbound : d*(4^(p-1)*(S*d^2)/16)≤43/S := by
    apply (le_div_iff₀ hS).mpr
    rw [hform]
    nlinarith only [hcube]
  have h43 : 43/S=43*scale p := by
    apply (div_eq_iff hS.ne').mpr
    nlinarith only [hSq]
  exact hbound.trans_eq h43

theorem realSecant_error {c : ℝ} {p : ℕ} (hp : 17≤p)
    (h : PositiveRestrictiveReturn c p) {x y : ℝ}
    (hx : x∈Icc (-1 : ℝ) 1) (hy : y∈Icc (-1 : ℝ) 1) :
    |realSecant c p x y-kappa p c|≤43*scale p := by
  have he := normalized_secant_error hp h
    (show ‖(x : ℂ)‖≤1 by simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_le.mpr hx)
    (show ‖(y : ℂ)‖≤1 by simpa only [Complex.norm_real,Real.norm_eq_abs] using abs_le.mpr hy)
  have hre := (Complex.abs_re_le_norm
    (normalizedSecant c p (x : ℂ) (y : ℂ)+(kappa p c : ℂ))).trans he
  simp only [Complex.add_re,Complex.ofReal_re] at hre
  have hid : realSecant c p x y-kappa p c=
      -((normalizedSecant c p (x : ℂ) (y : ℂ)).re+kappa p c) := by
    unfold realSecant
    ring
  rw [hid,abs_neg]
  exact hre

theorem realReturn_difference {c : ℝ} {p : ℕ} (hp : 0<p)
    (hd : criticalValue c p≠0) (x y : ℝ) :
    realReturn c p x-realReturn c p y= -realSecant c p x y*(x^2-y^2) := by
  have h := normalized_difference c p hp hd (x : ℂ) (y : ℂ)
  rw [normalized_real_value,normalized_real_value] at h
  have hid : (x : ℂ)^2-(y : ℂ)^2=((x^2-y^2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hid] at h
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hre
  rw [hre]
  unfold realSecant
  ring

end
end GlobalWindowSecant
