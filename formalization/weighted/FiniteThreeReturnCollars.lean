import DepthThreeRemainder
import QuadraticCrestDividedDifference
import FiniteThreeReturnCertificates

/-!
# The fixed three-return collar for the finite periods

The exact archived parameter boxes are interpreted as actual real
parameters.  Complete complex remainder bounds establish the fixed
annular barrier and all intermediate phase separations.  A product
factorization then proves that the actual three-return map has exactly
the signed quadratic collisions throughout the closed outer disk.
-/

namespace FiniteThreeReturnCollars

open Set Function
open LoopsFormal.Period27 LoopsFormal.DepthThree
open LoopsDepthThreeReal LoopsDepthThreeRemainder
open LimitingCrestQuadraticReturn QuadraticCrestDividedDifference
open FiniteThreeReturnCertificates

noncomputable section

private theorem scale_pos {S : Int} (hS : 0 < S) : 0 < (S : ℝ) := by
  exact_mod_cast hS

private theorem polynomial_eq_criticalValue (c : ℝ) (n : ℕ) :
    LoopsRealPeriod27.polynomial n c = criticalValue c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [polynomial_succ, ih]
    simp only [criticalValue, iterate_succ_apply']

private theorem orbit_eq_iterate (c : ℝ) (n : ℕ) (z : ℂ) :
    QuadraticEscape.orbit (c : ℂ) n z = ((quadraticMap c)^[n]) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [QuadraticEscape.orbit, ih, iterate_succ_apply']
    rfl

private theorem normalized_iterate_eq_div (c : ℝ) (p : ℕ)
    (hd : criticalValue c p ≠ 0) (k : ℕ) (z : ℂ) :
    ((normalizedReturn c p)^[k]) z =
      QuadraticEscape.orbit (c : ℂ) (k*p) ((criticalValue c p : ℂ)*z) /
        (criticalValue c p : ℂ) := by
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [eq_div_iff hdC, mul_comm]
  exact (normalized_iterate_scale c p hd k z).trans (orbit_eq_iterate c (k*p) _).symm

private theorem row_enclosed {S : Int} (hS : 0 < S) {p : ℕ}
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c)
    {j : ℕ} (hj : j ≤ 3*p) :
    RealRowEnclosed S (rowAt (collarRows S p C) j) j c :=
  trace_enclosed hS hc (3*p) j hj

private theorem d_enclosed {S : Int} (hS : 0 < S) {p : ℕ}
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c) :
    RealEnclosed S (collarD S p C) (criticalValue c p) := by
  simpa only [polynomial_eq_criticalValue, collarD] using
    (row_enclosed hS hc (j := p) (by omega)).1

private theorem physical_radius_bound {S : Int} (hS : 0 < S) {p : ℕ}
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c)
    (hd : 0 < criticalValue c p) {z : ℂ} (hz : ‖z‖ ≤ 1/6) :
    ‖(criticalValue c p : ℂ)*z‖ ≤
      ((collarRadius S p C).num : ℝ) / ((collarRadius S p C).den : ℝ) := by
  have hdup := ((realEnclosed_iff hS _ _).mp (d_enclosed hS (p := p) hc)).2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  calc
    criticalValue c p * ‖z‖ ≤ criticalValue c p * (1/6) :=
      mul_le_mul_of_nonneg_left hz hd.le
    _ ≤ ((collarD S p C).hi : ℝ) / (S : ℝ) * (1/6) :=
      mul_le_mul_of_nonneg_right hdup (by norm_num)
    _ = _ := by simp only [collarRadius, Int.cast_mul, Int.cast_ofNat]; ring

private theorem physical_deviation_bound {S : Int} (hS : 0 < S) {p : ℕ}
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c)
    {j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ 3*p) {z : ℂ}
    (hz : ‖z‖ ≤ ((collarRadius S p C).num : ℝ) /
      ((collarRadius S p C).den : ℝ)) :
    ‖QuadraticEscape.orbit (c : ℂ) j z - (criticalValue c j : ℂ)‖ ≤
      (collarDeviation S p C j : ℝ) / (S : ℝ) := by
  have hr : (collarRadius S p C).den ≠ 0 := by
    change 6*S ≠ 0
    exact mul_ne_zero (by norm_num) (ne_of_gt hS)
  have he := errors_sound hS hc (3*p) (3*p) le_rfl (collarRadius S p C) hr z hz
    j hj hjp
  have hrow := row_enclosed hS hc hjp
  have ha := abs_enclosed hS hrow.2.2
  have hA : 0 ≤ (absHi (rowAt (collarRows S p C) j).quadratic : ℝ)/(S:ℝ) :=
    (abs_nonneg _).trans ha
  have hrr := radius_squared_sound hS (collarRadius S p C) hr
  have hp := upperProduct_sound hS
    (absHi (rowAt (collarRows S p C) j).quadratic)
    (radiusSquaredUpper S (collarRadius S p C))
  have hlead : ‖(LoopsDepthThreeReal.quadraticCoefficient j c : ℂ)*z^2‖ ≤
      (upperProduct S (absHi (rowAt (collarRows S p C) j).quadratic)
        (radiusSquaredUpper S (collarRadius S p C)) : ℝ)/(S:ℝ) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    apply le_trans _ hp
    exact (mul_le_mul_of_nonneg_right ha (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left
        ((pow_le_pow_left₀ (norm_nonneg _) hz 2).trans hrr) hA)
  have hid : QuadraticEscape.orbit (c : ℂ) j z - (criticalValue c j : ℂ) =
      (LoopsDepthThreeReal.quadraticCoefficient j c : ℂ)*z^2 + remainder c j z := by
    rw [remainder, polynomial_eq_criticalValue]
    ring
  rw [hid]
  calc
    _ ≤ ‖(LoopsDepthThreeReal.quadraticCoefficient j c : ℂ)*z^2‖ + ‖remainder c j z‖ :=
      norm_add_le _ _
    _ ≤ _ := by
      have hh := add_le_add hlead he
      simpa only [collarDeviation, collarErrors, collarRows, Int.cast_add, add_div] using hh

private theorem normalized_deviation_bound {S : Int} (hS : 0 < S) {p : ℕ}
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c)
    (hD : 0 < (collarD S p C).lo) {k : ℕ}
    (hk : 1 ≤ k*p) (hkp : k*p ≤ 3*p) {z : ℂ} (hz : ‖z‖ ≤ 1/6) :
    ‖((normalizedReturn c p)^[k]) z -
      ((criticalValue c (k*p) / criticalValue c p : ℝ) : ℂ)‖ ≤
      (collarDeviation S p C (k*p) : ℝ) / ((collarD S p C).lo : ℝ) := by
  have hs := scale_pos hS
  have hdlo : (0:ℝ) < ((collarD S p C).lo : ℝ) := by exact_mod_cast hD
  have hdbox := (realEnclosed_iff hS _ _).mp (d_enclosed hS (p := p) hc)
  have hd : 0 < criticalValue c p := lt_of_lt_of_le (div_pos hdlo hs) hdbox.1
  have he := physical_deviation_bound hS hc hk hkp (physical_radius_bound hS hc hd hz)
  have hn : 0 ≤ (collarDeviation S p C (k*p) : ℝ)/(S:ℝ) := (norm_nonneg _).trans he
  rw [normalized_iterate_eq_div c p hd.ne' k z, Complex.ofReal_div, ← sub_div,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  calc
    _ ≤ ((collarDeviation S p C (k*p) : ℝ)/(S:ℝ))/criticalValue c p :=
      div_le_div_of_nonneg_right he hd.le
    _ ≤ ((collarDeviation S p C (k*p) : ℝ)/(S:ℝ))/
        (((collarD S p C).lo : ℝ)/(S:ℝ)) :=
      div_le_div_of_nonneg_left hn (div_pos hdlo hs) hdbox.1
    _ = _ := by field_simp

private theorem geometry_positive {S : Int} {p : ℕ} {C : Bounds}
    (hG : GeometryCertificate S p C) {c : ℝ} (hc : RealEnclosed S C c) :
    0 < criticalValue c p := by
  have hS := hG.1
  have hD := hG.2.2.1
  have hdlo : (0:ℝ) < ((collarD S p C).lo : ℝ) := by exact_mod_cast hD
  exact lt_of_lt_of_le (div_pos hdlo (scale_pos hS))
    (((realEnclosed_iff hS _ _).mp (d_enclosed hS (p := p) hc)).1)

private theorem scaled_division_bound {S D d v A : ℝ}
    (hS : 0 < S) (hD : 0 < D) (hden : D/S ≤ d)
    (hv : 0 ≤ v) (hbound : v ≤ A/S) : v/d ≤ A/D := by
  have hd : 0 < d := lt_of_lt_of_le (div_pos hD hS) hden
  calc
    v/d ≤ (A/S)/d := div_le_div_of_nonneg_right hbound hd.le
    _ ≤ (A/S)/(D/S) :=
      div_le_div_of_nonneg_left (hv.trans hbound) (div_pos hD hS) hden
    _ = A/D := by field_simp

private theorem geometry_critical_value {S : Int} {p : ℕ} {C : Bounds}
    (hG : GeometryCertificate S p C) {c : ℝ} (hc : RealEnclosed S C c) :
    criticalValue c (3*p) < 0 ∧
      ‖((normalizedReturn c p)^[3]) 0‖ < 1/6 := by
  have hd := geometry_positive hG hc
  rcases hG with ⟨hS, hp, hD, hxsign, hxsmall, _⟩
  have hs := scale_pos hS
  have hdlo : (0:ℝ) < ((collarD S p C).lo : ℝ) := by exact_mod_cast hD
  have hx := (row_enclosed hS hc (j := 3*p) le_rfl).1
  have hxa := abs_enclosed hS hx
  rw [polynomial_eq_criticalValue] at hx hxa
  constructor
  · have hh : ((rowAt (collarRows S p C) (3*p)).orbit.hi : ℝ) < 0 := by
      exact_mod_cast hxsign
    have : criticalValue c (3*p) * (S:ℝ) < 0 := hx.2.trans_lt hh
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg (le_of_not_gt hn) hs.le)) this
  · rw [normalized_iterate_eq_div c p hd.ne' 3 0, mul_zero,
      critical_orbit_cast, polynomial_eq_criticalValue, norm_div,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hd]
    have hb := scaled_division_bound hs hdlo
      (((realEnclosed_iff hS _ _).mp (d_enclosed hS (p := p) hc)).1)
      (abs_nonneg _) hxa
    apply hb.trans_lt
    apply (div_lt_iff₀ hdlo).mpr
    have hh : 8*(absHi (rowAt (collarRows S p C) (3*p)).orbit : ℝ) <
        ((collarD S p C).lo : ℝ) := by exact_mod_cast hxsmall
    linarith only [hh, hdlo]

private theorem band_arithmetic {S D A X T : ℝ}
    (hS : 0 < S) (hD : 0 < D)
    (h : 6000*S^2*(X+T)+1012*S^2*D < 135*A*D^2) :
    1/6+1/500+X/D+T/D < (A/S)*(D/S)*(3/20)^2 := by
  have hP : 0 < 6000*S^2*D := by positivity
  apply (mul_lt_mul_iff_right₀ hP).mp
  calc
    (6000*S^2*D)*(1/6+1/500+X/D+T/D) =
        6000*S^2*(X+T)+1012*S^2*D := by field_simp; ring
    _ < 135*A*D^2 := h
    _ = (6000*S^2*D)*((A/S)*(D/S)*(3/20)^2) := by field_simp; ring

private theorem geometry_annular_barrier {S : Int} {p : ℕ} {C : Bounds}
    (hG : GeometryCertificate S p C) {c : ℝ} (hc : RealEnclosed S C c)
    {z : ℂ} (hzlo : (3/20:ℝ) ≤ ‖z‖) (hzhi : ‖z‖ ≤ 1/6) :
    1/6+1/500 < ‖((normalizedReturn c p)^[3]) z‖ := by
  have hd := geometry_positive hG hc
  rcases hG with ⟨hS, hp, hD, _, _, _, _, _, _, ht, ha0, hgap, _⟩
  have hs := scale_pos hS
  have hdlo : (0:ℝ) < ((collarD S p C).lo : ℝ) := by exact_mod_cast hD
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  let D : ℝ := ((collarD S p C).lo : ℝ)
  let A : ℝ := (absLo (rowAt (collarRows S p C) (3*p)).quadratic : ℝ)
  let X : ℝ := (absHi (rowAt (collarRows S p C) (3*p)).orbit : ℝ)
  let T : ℝ := (errorAt (collarErrors S p C) (3*p) : ℝ)
  have hden : D/(S:ℝ) ≤ criticalValue c p :=
    ((realEnclosed_iff hS _ _).mp (d_enclosed hS (p := p) hc)).1
  have hrow := row_enclosed hS hc (j := 3*p) le_rfl
  have hxa := abs_enclosed hS hrow.1
  rw [polynomial_eq_criticalValue] at hxa
  have hca : |criticalValue c (3*p)| / criticalValue c p ≤ X/D :=
    scaled_division_bound hs hdlo hden (abs_nonneg _) hxa
  have hr : (collarRadius S p C).den ≠ 0 := by
    change 6*S ≠ 0
    exact mul_ne_zero (by norm_num) hS.ne'
  have he := errors_sound hS hc (3*p) (3*p) le_rfl (collarRadius S p C) hr
    ((criticalValue c p : ℂ)*z) (physical_radius_bound hS hc hd hzhi)
    (3*p) (by omega) le_rfl
  have hea : ‖remainder c (3*p) ((criticalValue c p : ℂ)*z)‖ /
      criticalValue c p ≤ T/D :=
    scaled_division_bound hs hdlo hden (norm_nonneg _) he
  have ha := absLo_enclosed hS hrow.2.2
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact_mod_cast ha0
  have hlead : (A/(S:ℝ))*(D/(S:ℝ))*(3/20)^2 ≤
      |LoopsDepthThreeReal.quadraticCoefficient (3*p) c| * criticalValue c p * ‖z‖^2 := by
    apply mul_le_mul
    · exact mul_le_mul ha hden (div_pos hdlo hs).le (abs_nonneg _)
    · exact pow_le_pow_left₀ (by norm_num) hzlo 2
    · positivity
    · positivity
  have harith : 1/6+1/500+X/D+T/D < (A/(S:ℝ))*(D/(S:ℝ))*(3/20)^2 := by
    apply band_arithmetic hs hdlo
    dsimp only [A, D, X, T]
    exact_mod_cast hgap
  have hid : ((normalizedReturn c p)^[3]) z =
      ((criticalValue c (3*p) / criticalValue c p : ℝ) : ℂ) +
      ((LoopsDepthThreeReal.quadraticCoefficient (3*p) c * criticalValue c p : ℝ) : ℂ)*z^2 +
      remainder c (3*p) ((criticalValue c p : ℂ)*z) / (criticalValue c p : ℂ) := by
    rw [normalized_iterate_eq_div c p hd.ne' 3 z]
    simp only [remainder, polynomial_eq_criticalValue]
    push_cast
    field_simp [hdC]
    ring
  have htriangle : |LoopsDepthThreeReal.quadraticCoefficient (3*p) c| *
      criticalValue c p * ‖z‖^2 ≤
      ‖((normalizedReturn c p)^[3]) z‖ +
      |criticalValue c (3*p)|/criticalValue c p +
      ‖remainder c (3*p) ((criticalValue c p : ℂ)*z)‖/criticalValue c p := by
    have hi : ((LoopsDepthThreeReal.quadraticCoefficient (3*p) c * criticalValue c p : ℝ) : ℂ)*z^2 =
        ((normalizedReturn c p)^[3]) z -
          ((criticalValue c (3*p) / criticalValue c p : ℝ) : ℂ) -
          remainder c (3*p) ((criticalValue c p : ℂ)*z) / (criticalValue c p : ℂ) := by
      rw [hid]
      ring
    have hn := norm_sub_le
      (((normalizedReturn c p)^[3]) z - ((criticalValue c (3*p) / criticalValue c p : ℝ) : ℂ))
      (remainder c (3*p) ((criticalValue c p : ℂ)*z) / (criticalValue c p : ℂ))
    have hn2 := norm_sub_le (((normalizedReturn c p)^[3]) z)
      ((criticalValue c (3*p) / criticalValue c p : ℝ) : ℂ)
    rw [← hi] at hn
    simp only [norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hd] at hn hn2
    linarith only [hn, hn2]
  linarith only [harith, hlead, htriangle, hca, hea]

private theorem geometry_intermediate_separation {S : Int} {p : ℕ} {C : Bounds}
    (hG : GeometryCertificate S p C) {c : ℝ} (hc : RealEnclosed S C c)
    {j : ℕ} (hj : 1 ≤ j) (hjp : j < 3*p) {z w : ℂ}
    (hz : ‖z‖ ≤ 1/6) (hw : ‖w‖ ≤ 1/6) :
    ((quadraticMap c)^[j]) ((criticalValue c p : ℂ)*z) +
      ((quadraticMap c)^[j]) ((criticalValue c p : ℂ)*w) ≠ 0 := by
  have hd := geometry_positive hG hc
  rcases hG with ⟨hS, _, _, _, _, _, _, _, _, _, _, _, hsep⟩
  have hs := scale_pos hS
  have hh := List.all_eq_true.mp hsep j (List.mem_range.mpr hjp)
  have hji : j ≠ 0 := by omega
  have hdev : collarDeviation S p C j < absLo (rowAt (collarRows S p C) j).orbit := by
    simpa only [if_neg hji, decide_eq_true_eq] using hh
  have hdevR : (collarDeviation S p C j : ℝ)/(S:ℝ) <
      (absLo (rowAt (collarRows S p C) j).orbit : ℝ)/(S:ℝ) := by
    apply (div_lt_div_iff_of_pos_right hs).mpr
    exact_mod_cast hdev
  have hx := absLo_enclosed hS (row_enclosed hS hc hjp.le).1
  rw [polynomial_eq_criticalValue] at hx
  have hzdev := physical_deviation_bound hS hc hj hjp.le (physical_radius_bound hS hc hd hz)
  have hwdev := physical_deviation_bound hS hc hj hjp.le (physical_radius_bound hS hc hd hw)
  rw [orbit_eq_iterate] at hzdev hwdev
  intro he
  have hid :
      (((quadraticMap c)^[j]) ((criticalValue c p : ℂ)*z) - (criticalValue c j : ℂ)) +
      (((quadraticMap c)^[j]) ((criticalValue c p : ℂ)*w) - (criticalValue c j : ℂ)) =
      -2*(criticalValue c j : ℂ) := by
    calc
      _ = (((quadraticMap c)^[j]) ((criticalValue c p : ℂ)*z) +
        ((quadraticMap c)^[j]) ((criticalValue c p : ℂ)*w)) - 2*(criticalValue c j : ℂ) := by ring
      _ = _ := by rw [he]; ring
  have hn := norm_add_le
    (((quadraticMap c)^[j]) ((criticalValue c p : ℂ)*z) - (criticalValue c j : ℂ))
    (((quadraticMap c)^[j]) ((criticalValue c p : ℂ)*w) - (criticalValue c j : ℂ))
  rw [hid] at hn
  norm_num only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs] at hn
  linarith only [hn, hzdev, hwdev, hdevR, hx]

private theorem secant_nonzero (c : ℝ) (n : ℕ) (z w : ℂ)
    (hsep : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      ((quadraticMap c)^[j]) z + ((quadraticMap c)^[j]) w ≠ 0) :
    evenSecant c n z w ≠ 0 := by
  induction n with
  | zero => simp [evenSecant]
  | succ n ih =>
    rw [evenSecant]
    exact mul_ne_zero (hsep (n+1) (by omega) le_rfl)
      (ih (fun j hj hjn => hsep j hj (by omega)))

private theorem geometry_collision_iff {S : Int} {p : ℕ} {C : Bounds}
    (hG : GeometryCertificate S p C) {c : ℝ} (hc : RealEnclosed S C c)
    {z w : ℂ} (hz : ‖z‖ ≤ 1/6) (hw : ‖w‖ ≤ 1/6) :
    ((normalizedReturn c p)^[3]) z = ((normalizedReturn c p)^[3]) w ↔
      z = w ∨ z = -w := by
  have hp := hG.2.1
  have hd := geometry_positive hG hc
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hn : 3*p-1+1 = 3*p := by omega
  have hsec := secant_nonzero c (3*p-1)
    ((criticalValue c p : ℂ)*z) ((criticalValue c p : ℂ)*w)
    (fun j hj hjn => geometry_intermediate_separation hG hc hj (by omega) hz hw)
  have hid := iterate_difference c (3*p-1)
    ((criticalValue c p : ℂ)*z) ((criticalValue c p : ℂ)*w)
  rw [hn] at hid
  constructor
  · intro he
    have hf : ((quadraticMap c)^[3*p]) ((criticalValue c p : ℂ)*z) =
        ((quadraticMap c)^[3*p]) ((criticalValue c p : ℂ)*w) := by
      rw [← normalized_iterate_scale c p hd.ne' 3 z,
        ← normalized_iterate_scale c p hd.ne' 3 w, he]
    have hsq : ((criticalValue c p : ℂ)*z)^2 - ((criticalValue c p : ℂ)*w)^2 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hsec
      rw [← hid, hf, sub_self]
    have hprod : (z-w)*(z+w) = 0 := by
      apply (mul_eq_zero.mp (show (criticalValue c p : ℂ)^2*((z-w)*(z+w)) = 0 from ?_)).resolve_left
        (pow_ne_zero 2 hdC)
      calc
        _ = ((criticalValue c p : ℂ)*z)^2 - ((criticalValue c p : ℂ)*w)^2 := by ring
        _ = 0 := hsq
    rcases mul_eq_zero.mp hprod with he | he
    · exact Or.inl (sub_eq_zero.mp he)
    · exact Or.inr (eq_neg_of_add_eq_zero_left he)
  · intro he
    have hf : ((quadraticMap c)^[3*p]) ((criticalValue c p : ℂ)*z) =
        ((quadraticMap c)^[3*p]) ((criticalValue c p : ℂ)*w) := by
      apply sub_eq_zero.mp
      rw [hid]
      rcases he with he | he
      · rw [he, sub_self, zero_mul]
      · rw [he, mul_neg, neg_sq, sub_self, zero_mul]
    apply mul_left_cancel₀ hdC
    rw [normalized_iterate_scale c p hd.ne' 3 z,
      normalized_iterate_scale c p hd.ne' 3 w, hf]

private theorem geometry_phase_bounds {S : Int} {p : ℕ} {C : Bounds}
    (hG : GeometryCertificate S p C) {c : ℝ} (hc : RealEnclosed S C c)
    {z : ℂ} (hz : ‖z‖ ≤ 1/6) :
    ‖normalizedReturn c p z - 1‖ < 3/50 ∧
      ‖((normalizedReturn c p)^[2]) z -
        ((criticalValue c (2*p)/criticalValue c p : ℝ):ℂ)‖ < 19/100 ∧
      criticalValue c (2*p)/criticalValue c p ∈ Icc (-(4/5:ℝ)) (-(3/4:ℝ)) ∧
      (‖normalizedReturn c p z‖ ≤ 23/20 ∧
        ‖normalizedReturn c p (normalizedReturn c p z)‖ ≤ 23/20 ∧
        0 < (normalizedReturn c p z).re ∧
        (normalizedReturn c p (normalizedReturn c p z)).re < 0) := by
  have hd := geometry_positive hG hc
  rcases hG with ⟨hS, hp, hD, _, _, hfirst, hsecond, hlo, hhi, _⟩
  have hs := scale_pos hS
  have hdlo : (0:ℝ) < ((collarD S p C).lo : ℝ) := by exact_mod_cast hD
  have hdev1 := normalized_deviation_bound hS hc hD
    (k := 1) (by omega) (by omega) hz
  simp only [one_mul, div_self hd.ne', Complex.ofReal_one, iterate_one] at hdev1
  have hphase1 : ‖normalizedReturn c p z - 1‖ < 3/50 := by
    apply hdev1.trans_lt
    apply (div_lt_iff₀ hdlo).mpr
    have hcast : 50*(collarDeviation S p C p : ℝ) < 3*((collarD S p C).lo : ℝ) := by
      exact_mod_cast hfirst
    linarith only [hcast]
  have hdev2 := normalized_deviation_bound hS hc hD
    (k := 2) (by omega) (by omega) hz
  have hphase2 : ‖normalizedReturn c p (normalizedReturn c p z) -
      ((criticalValue c (2*p)/criticalValue c p : ℝ):ℂ)‖ < 19/100 := by
    apply hdev2.trans_lt
    apply (div_lt_iff₀ hdlo).mpr
    have hcast : 100*(collarDeviation S p C (2*p) : ℝ) <
        19*((collarD S p C).lo : ℝ) := by exact_mod_cast hsecond
    linarith only [hcast]
  have hx := (row_enclosed hS (p := p) hc (j := 2*p) (by omega)).1
  rw [polynomial_eq_criticalValue] at hx
  have hdbox := d_enclosed hS (p := p) hc
  have hloR : -4*((collarD S p C).lo : ℝ) ≤
      5*((rowAt (collarRows S p C) (2*p)).orbit.lo : ℝ) := by exact_mod_cast hlo
  have hhiR : 4*((rowAt (collarRows S p C) (2*p)).orbit.hi : ℝ) ≤
      -3*((collarD S p C).hi : ℝ) := by exact_mod_cast hhi
  have hcenter : -(4/5:ℝ) ≤ criticalValue c (2*p)/criticalValue c p ∧
      criticalValue c (2*p)/criticalValue c p ≤ -(3/4:ℝ) := by
    constructor
    · apply (le_div_iff₀ hd).mpr
      apply (mul_le_mul_iff_right₀ hs).mp
      nlinarith only [hloR, hx.1, hdbox.1]
    · apply (div_le_iff₀ hd).mpr
      apply (mul_le_mul_iff_right₀ hs).mp
      nlinarith only [hhiR, hx.2, hdbox.2]
  have hcenterabs : |criticalValue c (2*p)/criticalValue c p| ≤ 4/5 :=
    abs_le.mpr ⟨hcenter.1, by linarith only [hcenter.2]⟩
  have hn1 := norm_le_norm_sub_add (normalizedReturn c p z) (1:ℂ)
  norm_num only [norm_one] at hn1
  have hn2 := norm_le_norm_sub_add (normalizedReturn c p (normalizedReturn c p z))
    ((criticalValue c (2*p)/criticalValue c p : ℝ):ℂ)
  simp only [Complex.norm_real, Real.norm_eq_abs] at hn2
  have hr1 := (Complex.abs_re_le_norm (normalizedReturn c p z-1)).trans_lt hphase1
  have hr2 := (Complex.abs_re_le_norm (normalizedReturn c p (normalizedReturn c p z)-
    ((criticalValue c (2*p)/criticalValue c p : ℝ):ℂ))).trans_lt hphase2
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hr1 hr2
  refine ⟨hphase1, hphase2, hcenter, ?_, ?_, ?_, ?_⟩
  · linarith only [hn1, hphase1]
  · linarith only [hn2, hphase2, hcenterabs]
  · linarith only [(abs_lt.mp hr1).1]
  · linarith only [(abs_lt.mp hr2).2, hcenter.2]

/-- The finite period index selects a kernel-checked root and fixed-collar
certificate, with no numerical hypotheses left to the caller. -/
theorem finite_certificates {p : ℕ} (hp3 : 3 ≤ p) (hp16 : p ≤ 16) :
    RootCertificate finiteScale p (parameterBox p) ∧
      GeometryCertificate finiteScale p (parameterBox p) := by
  have hmem : p-3 ∈ List.range 14 := List.mem_range.mpr (by omega)
  have h := List.all_eq_true.mp finite_certificates_valid (p-3) hmem
  have he : p-3+3 = p := by omega
  simpa only [he, decide_eq_true_eq] using h

/-- An actual real solution of the signed critical relation, enclosed
in the archived dyadic box. -/
def CertifiedParameter (p : ℕ) (c : ℝ) : Prop :=
  RealEnclosed finiteScale (parameterBox p) c ∧
    criticalValue c (6*p) + criticalValue c (3*p) = 0

/-- Every finite period has an actual real parameter in its strict
certificate box satisfying the exact signed critical orbit equation. -/
theorem exists_finite_parameter (p : ℕ) (hp3 : 3 ≤ p) (hp16 : p ≤ 16) :
    ∃ c : ℝ, CertifiedParameter p c := by
  have hh := finite_certificates hp3 hp16
  obtain ⟨c, hc, _⟩ := certified_unique_real_root hh.1
  refine ⟨c, ?_, ?_⟩
  · exact (realEnclosed_iff hh.2.1 _ _).mpr ⟨hc.1.le, hc.2.1.le⟩
  · have hr := hc.2.2
    simp only [collisionPolynomial, polynomial_eq_criticalValue] at hr
    simpa only [add_comm] using hr

/-- The finite parameters have a positive first critical return and a
negative third critical return. -/
theorem finite_critical_signs {p : ℕ} (hp3 : 3 ≤ p) (hp16 : p ≤ 16)
    {c : ℝ} (hc : CertifiedParameter p c) :
    0 < criticalValue c p ∧ criticalValue c (3*p) < 0 := by
  have hG := (finite_certificates hp3 hp16).2
  exact ⟨geometry_positive hG hc.1, (geometry_critical_value hG hc.1).1⟩

/-- The exact critical value of the third normalized return is inside
the fixed target disk. -/
theorem finite_critical_value_bound {p : ℕ} (hp3 : 3 ≤ p) (hp16 : p ≤ 16)
    {c : ℝ} (hc : CertifiedParameter p c) :
    ‖((normalizedReturn c p)^[3]) 0‖ < 1/6 :=
  (geometry_critical_value (finite_certificates hp3 hp16).2 hc.1).2

/-- Every point of the full closed radial band maps past the fixed
target circle, with the same explicit margin as in the infinite tail. -/
theorem finite_annular_barrier {p : ℕ} (hp3 : 3 ≤ p) (hp16 : p ≤ 16)
    {c : ℝ} (hc : CertifiedParameter p c) {z : ℂ}
    (hzlo : (3/20:ℝ) ≤ ‖z‖) (hzhi : ‖z‖ ≤ 1/6) :
    1/6+1/500 < ‖((normalizedReturn c p)^[3]) z‖ :=
  geometry_annular_barrier (finite_certificates hp3 hp16).2 hc.1 hzlo hzhi

/-- The complete actual three-return polynomial has exactly the two
signed sheets on the entire closed outer disk. -/
theorem finite_three_return_collision_iff {p : ℕ} (hp3 : 3 ≤ p) (hp16 : p ≤ 16)
    {c : ℝ} (hc : CertifiedParameter p c) {z w : ℂ}
    (hz : ‖z‖ ≤ 1/6) (hw : ‖w‖ ≤ 1/6) :
    ((normalizedReturn c p)^[3]) z = ((normalizedReturn c p)^[3]) w ↔
      z = w ∨ z = -w :=
  geometry_collision_iff (finite_certificates hp3 hp16).2 hc.1 hz hw

/-- The finite phase disks use fixed centers and radii, with no
additional restriction of the selected central disk. -/
theorem finite_phase_bounds {p : ℕ} (hp3 : 3 ≤ p) (hp16 : p ≤ 16)
    {c : ℝ} (hc : CertifiedParameter p c) {z : ℂ} (hz : ‖z‖ ≤ 1/6) :
    ‖normalizedReturn c p z - 1‖ < 3/50 ∧
      ‖((normalizedReturn c p)^[2]) z -
        ((criticalValue c (2*p)/criticalValue c p : ℝ):ℂ)‖ < 19/100 ∧
      criticalValue c (2*p)/criticalValue c p ∈ Icc (-(4/5:ℝ)) (-(3/4:ℝ)) := by
  have h := geometry_phase_bounds (finite_certificates hp3 hp16).2 hc.1 hz
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Both noncentral phase images stay in the common control disk and
on opposite strict sides of the imaginary axis. -/
theorem finite_phase_control {p : ℕ} (hp3 : 3 ≤ p) (hp16 : p ≤ 16)
    {c : ℝ} (hc : CertifiedParameter p c) {z : ℂ} (hz : ‖z‖ ≤ 1/6) :
    ‖normalizedReturn c p z‖ ≤ 23/20 ∧
      ‖normalizedReturn c p (normalizedReturn c p z)‖ ≤ 23/20 ∧
      0 < (normalizedReturn c p z).re ∧
      (normalizedReturn c p (normalizedReturn c p z)).re < 0 :=
  (geometry_phase_bounds (finite_certificates hp3 hp16).2 hc.1 hz).2.2.2

end

end FiniteThreeReturnCollars
