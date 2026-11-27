import FiniteThreeReturnCollars
import FiniteFirstReturnCertificates

/-!
# The actual finite p-return control disk

The full normalized disk of radius 23/20 has an escaping boundary
and exactly the signed quadratic collisions for every finite parameter.
These conclusions provide a canonical enclosing p-return domain
for the three fixed phases, without further reducing their radii.
-/

namespace FiniteFirstReturnBounds

open Set Function
open LoopsFormal.Period27 LoopsFormal.DepthThree
open LoopsDepthThreeReal LoopsDepthThreeRemainder
open LimitingCrestQuadraticReturn QuadraticCrestDividedDifference
open FiniteThreeReturnCertificates FiniteThreeReturnCollars
open FiniteFirstReturnCertificates

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
    (hd : 0 < criticalValue c p) {z : ℂ} (hz : ‖z‖ ≤ 23/20) :
    ‖(criticalValue c p : ℂ)*z‖ ≤
      ((parentRadius S p C).num : ℝ) / ((parentRadius S p C).den : ℝ) := by
  have hdup := ((realEnclosed_iff hS _ _).mp (d_enclosed hS (p := p) hc)).2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  calc
    criticalValue c p * ‖z‖ ≤ criticalValue c p * (23/20) :=
      mul_le_mul_of_nonneg_left hz hd.le
    _ ≤ ((collarD S p C).hi : ℝ) / (S : ℝ) * (23/20) :=
      mul_le_mul_of_nonneg_right hdup (by norm_num)
    _ = _ := by simp only [parentRadius, Int.cast_mul, Int.cast_ofNat]; ring

private theorem physical_deviation_bound {S : Int} (hS : 0 < S) {p : ℕ}
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c)
    {j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p) {z : ℂ}
    (hz : ‖z‖ ≤ ((parentRadius S p C).num : ℝ) /
      ((parentRadius S p C).den : ℝ)) :
    ‖QuadraticEscape.orbit (c : ℂ) j z - (criticalValue c j : ℂ)‖ ≤
      (parentDeviation S p C j : ℝ) / (S : ℝ) := by
  have hr : (parentRadius S p C).den ≠ 0 := by
    change 20*S ≠ 0
    exact mul_ne_zero (by norm_num) (ne_of_gt hS)
  have he := errors_sound hS hc (3*p) p (by omega) (parentRadius S p C) hr z hz
    j hj hjp
  have hrow := row_enclosed hS (p := p) hc (j := j) (by omega)
  have ha := abs_enclosed hS hrow.2.2
  have hA : 0 ≤ (absHi (rowAt (collarRows S p C) j).quadratic : ℝ)/(S:ℝ) :=
    (abs_nonneg _).trans ha
  have hrr := radius_squared_sound hS (parentRadius S p C) hr
  have hp := upperProduct_sound hS
    (absHi (rowAt (collarRows S p C) j).quadratic)
    (radiusSquaredUpper S (parentRadius S p C))
  have hlead : ‖(LoopsDepthThreeReal.quadraticCoefficient j c : ℂ)*z^2‖ ≤
      (upperProduct S (absHi (rowAt (collarRows S p C) j).quadratic)
        (radiusSquaredUpper S (parentRadius S p C)) : ℝ)/(S:ℝ) := by
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
      simpa only [parentDeviation, parentErrors, collarRows, Int.cast_add, add_div] using hh

private theorem geometry_positive {S : Int} {p : ℕ} {C : Bounds}
    (hG : FirstReturnCertificate S p C) {c : ℝ} (hc : RealEnclosed S C c) :
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

private theorem first_return_scale (c : ℝ) (p : ℕ)
    (hd : criticalValue c p ≠ 0) (z : ℂ) :
    (criticalValue c p : ℂ)*normalizedReturn c p z =
      ((quadraticMap c)^[p]) ((criticalValue c p : ℂ)*z) := by
  simpa only [iterate_one, one_mul] using normalized_iterate_scale c p hd 1 z

private theorem parent_arithmetic {S D A T : ℝ}
    (hS : 0 < S) (hD : 0 < D)
    (h : 900*S^2*D+400*S^2*T < 529*A*D^2) :
    23/20+1/10+1+T/D < (A/S)*(D/S)*(23/20)^2 := by
  have hP : 0 < 400*S^2*D := by positivity
  apply (mul_lt_mul_iff_right₀ hP).mp
  calc
    (400*S^2*D)*(23/20+1/10+1+T/D) = 900*S^2*D+400*S^2*T := by field_simp; ring
    _ < 529*A*D^2 := h
    _ = (400*S^2*D)*((A/S)*(D/S)*(23/20)^2) := by field_simp; ring

private theorem geometry_sphere_barrier {S : Int} {p : ℕ} {C : Bounds}
    (hG : FirstReturnCertificate S p C) {c : ℝ} (hc : RealEnclosed S C c)
    {z : ℂ} (hz : ‖z‖ = 23/20) :
    23/20+1/10 < ‖normalizedReturn c p z‖ := by
  have hd := geometry_positive hG hc
  rcases hG with ⟨hS, hp, hD, ha0, _, hgap, _⟩
  have hs := scale_pos hS
  have hdlo : (0:ℝ) < ((collarD S p C).lo : ℝ) := by exact_mod_cast hD
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  let D : ℝ := ((collarD S p C).lo : ℝ)
  let A : ℝ := (absLo (rowAt (collarRows S p C) p).quadratic : ℝ)
  let T : ℝ := (errorAt (parentErrors S p C) p : ℝ)
  have hden : D/(S:ℝ) ≤ criticalValue c p :=
    ((realEnclosed_iff hS _ _).mp (d_enclosed hS (p := p) hc)).1
  have hrow := row_enclosed hS (p := p) hc (j := p) (by omega)
  have hr : (parentRadius S p C).den ≠ 0 := by
    change 20*S ≠ 0
    exact mul_ne_zero (by norm_num) hS.ne'
  have he := errors_sound hS hc (3*p) p (by omega) (parentRadius S p C) hr
    ((criticalValue c p : ℂ)*z) (physical_radius_bound hS hc hd hz.le)
    p (by omega) le_rfl
  have hea : ‖remainder c p ((criticalValue c p : ℂ)*z)‖ /
      criticalValue c p ≤ T/D :=
    scaled_division_bound hs hdlo hden (norm_nonneg _) he
  have ha := absLo_enclosed hS hrow.2.2
  have hA : 0 ≤ A := by dsimp only [A]; exact_mod_cast ha0
  have hlead : (A/(S:ℝ))*(D/(S:ℝ))*(23/20)^2 ≤
      |LoopsDepthThreeReal.quadraticCoefficient p c| * criticalValue c p * ‖z‖^2 := by
    rw [hz]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul ha hden (div_pos hdlo hs).le (abs_nonneg _)) (sq_nonneg _)
  have harith : 23/20+1/10+1+T/D < (A/(S:ℝ))*(D/(S:ℝ))*(23/20)^2 := by
    apply parent_arithmetic hs hdlo
    dsimp only [A, D, T]
    exact_mod_cast hgap
  have hid : normalizedReturn c p z = 1 +
      ((LoopsDepthThreeReal.quadraticCoefficient p c * criticalValue c p : ℝ) : ℂ)*z^2 +
      remainder c p ((criticalValue c p : ℂ)*z) / (criticalValue c p : ℂ) := by
    simp only [normalizedReturn, remainder, polynomial_eq_criticalValue, orbit_eq_iterate]
    push_cast
    field_simp [hdC]
    ring
  have htriangle : |LoopsDepthThreeReal.quadraticCoefficient p c| * criticalValue c p * ‖z‖^2 ≤
      ‖normalizedReturn c p z‖ + 1 +
      ‖remainder c p ((criticalValue c p : ℂ)*z)‖/criticalValue c p := by
    have hi : ((LoopsDepthThreeReal.quadraticCoefficient p c * criticalValue c p : ℝ) : ℂ)*z^2 =
        normalizedReturn c p z - 1 -
          remainder c p ((criticalValue c p : ℂ)*z) / (criticalValue c p : ℂ) := by rw [hid]; ring
    have hn := norm_sub_le (normalizedReturn c p z - 1)
      (remainder c p ((criticalValue c p : ℂ)*z) / (criticalValue c p : ℂ))
    have hn2 := norm_sub_le (normalizedReturn c p z) (1:ℂ)
    rw [← hi] at hn
    simp only [norm_mul, norm_pow, norm_div, norm_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hd] at hn hn2
    linarith only [hn, hn2]
  linarith only [harith, hlead, htriangle, hea]

private theorem geometry_intermediate_separation {S : Int} {p : ℕ} {C : Bounds}
    (hG : FirstReturnCertificate S p C) {c : ℝ} (hc : RealEnclosed S C c)
    {j : ℕ} (hj : 1 ≤ j) (hjp : j < p) {z w : ℂ}
    (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    ((quadraticMap c)^[j]) ((criticalValue c p : ℂ)*z) +
      ((quadraticMap c)^[j]) ((criticalValue c p : ℂ)*w) ≠ 0 := by
  have hd := geometry_positive hG hc
  rcases hG with ⟨hS, _, _, _, _, _, hsep⟩
  have hs := scale_pos hS
  have hh := List.all_eq_true.mp hsep j (List.mem_range.mpr hjp)
  have hji : j ≠ 0 := by omega
  have hdev : parentDeviation S p C j < absLo (rowAt (collarRows S p C) j).orbit := by
    simpa only [if_neg hji, decide_eq_true_eq] using hh
  have hdevR : (parentDeviation S p C j : ℝ)/(S:ℝ) <
      (absLo (rowAt (collarRows S p C) j).orbit : ℝ)/(S:ℝ) := by
    apply (div_lt_div_iff_of_pos_right hs).mpr
    exact_mod_cast hdev
  have hx := absLo_enclosed hS (row_enclosed hS (p := p) hc (j := j) (by omega)).1
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
    (hG : FirstReturnCertificate S p C) {c : ℝ} (hc : RealEnclosed S C c)
    {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    normalizedReturn c p z = normalizedReturn c p w ↔ z = w ∨ z = -w := by
  have hp := hG.2.1
  have hd := geometry_positive hG hc
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hn : p-1+1 = p := by omega
  have hsec := secant_nonzero c (p-1)
    ((criticalValue c p : ℂ)*z) ((criticalValue c p : ℂ)*w)
    (fun j hj hjn => geometry_intermediate_separation hG hc hj (by omega) hz hw)
  have hid := iterate_difference c (p-1)
    ((criticalValue c p : ℂ)*z) ((criticalValue c p : ℂ)*w)
  rw [hn] at hid
  constructor
  · intro he
    have hf : ((quadraticMap c)^[p]) ((criticalValue c p : ℂ)*z) =
        ((quadraticMap c)^[p]) ((criticalValue c p : ℂ)*w) := by
      rw [← first_return_scale c p hd.ne' z, ← first_return_scale c p hd.ne' w, he]
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
    have hf : ((quadraticMap c)^[p]) ((criticalValue c p : ℂ)*z) =
        ((quadraticMap c)^[p]) ((criticalValue c p : ℂ)*w) := by
      apply sub_eq_zero.mp
      rw [hid]
      rcases he with he | he
      · rw [he, sub_self, zero_mul]
      · rw [he, mul_neg, neg_sq, sub_self, zero_mul]
    apply mul_left_cancel₀ hdC
    rw [first_return_scale c p hd.ne' z, first_return_scale c p hd.ne' w, hf]

/-- Each finite period selects its checked p-return certificate. -/
theorem finite_first_return_certificate {p : ℕ} (hp3 : 3 ≤ p) (hp16 : p ≤ 16) :
    FirstReturnCertificate finiteScale p (parameterBox p) := by
  have hmem : p-3 ∈ List.range 14 := List.mem_range.mpr (by omega)
  have h := List.all_eq_true.mp finite_first_return_certificates_valid (p-3) hmem
  have he : p-3+3 = p := by omega
  simpa only [he, decide_eq_true_eq] using h

/-- The entire enclosing circle maps strictly past radius 23/20,
with an additional uniform margin 1/10. -/
theorem finite_first_return_sphere_barrier {p : ℕ} (hp3 : 3 ≤ p) (hp16 : p ≤ 16)
    {c : ℝ} (hc : CertifiedParameter p c) {z : ℂ} (hz : ‖z‖ = 23/20) :
    23/20+1/10 < ‖normalizedReturn c p z‖ :=
  geometry_sphere_barrier (finite_first_return_certificate hp3 hp16) hc.1 hz

/-- The actual p-return has exactly the signed quadratic
collisions throughout the complete enclosing closed disk. -/
theorem finite_first_return_collision_iff {p : ℕ} (hp3 : 3 ≤ p) (hp16 : p ≤ 16)
    {c : ℝ} (hc : CertifiedParameter p c) {z w : ℂ}
    (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    normalizedReturn c p z = normalizedReturn c p w ↔ z = w ∨ z = -w :=
  geometry_collision_iff (finite_first_return_certificate hp3 hp16) hc.1 hz hw

/-- The physical enclosing control disk lies strictly inside the
archived ambient source disk, including the exceptional period-three
radius 1/4. -/
theorem finite_parent_scale_bound {p : ℕ} (hp3 : 3 ≤ p) (hp16 : p ≤ 16)
    {c : ℝ} (hc : CertifiedParameter p c) :
    criticalValue c p * (23/20) < if p = 3 then (1/4:ℝ) else 1/(2:ℝ)^p := by
  have hmem : p-3 ∈ List.range 14 := List.mem_range.mpr (by omega)
  have h := List.all_eq_true.mp finite_parent_scale_certificates_valid (p-3) hmem
  have he : p-3+3 = p := by omega
  have hcert : 0 < archiveRadiusDen p ∧
      23*(collarD finiteScale p (parameterBox p)).hi * archiveRadiusDen p < 20*finiteScale := by
    simpa only [he, decide_eq_true_eq] using h
  have hS := (finite_first_return_certificate hp3 hp16).1
  have hs := scale_pos hS
  have hden : (0:ℝ) < (archiveRadiusDen p : ℝ) := by exact_mod_cast hcert.1
  have hdhi := ((realEnclosed_iff hS _ _).mp (d_enclosed hS (p := p) hc.1)).2
  have hcast : 23*((collarD finiteScale p (parameterBox p)).hi : ℝ)*(archiveRadiusDen p : ℝ) <
      20*(finiteScale:ℝ) := by exact_mod_cast hcert.2
  have hr : ((collarD finiteScale p (parameterBox p)).hi : ℝ)/(finiteScale:ℝ)*(23/20) <
      1/(archiveRadiusDen p : ℝ) := by
    apply (lt_div_iff₀ hden).mpr
    calc
      _ = (23*((collarD finiteScale p (parameterBox p)).hi : ℝ)*(archiveRadiusDen p : ℝ)) /
          (20*(finiteScale:ℝ)) := by ring
      _ < 1 := (div_lt_one (by positivity)).mpr hcast
  have hfinal := (mul_le_mul_of_nonneg_right hdhi (show (0:ℝ) ≤ 23/20 by norm_num)).trans_lt hr
  by_cases hp : p = 3
  · subst p
    simpa [archiveRadiusDen] using hfinal
  · simpa only [archiveRadiusDen, if_neg hp, Int.cast_pow, Int.cast_ofNat] using hfinal

/-- The fixed finite phase images satisfy the strict control-disk
hypotheses of the enclosing p-return restriction. -/
theorem finite_parent_phase_control {p : ℕ} (hp3 : 3 ≤ p) (hp16 : p ≤ 16)
    {c : ℝ} (hc : CertifiedParameter p c) {z : ℂ} (hz : ‖z‖ ≤ 1/6) :
    ‖normalizedReturn c p z‖ < 23/20 ∧
      ‖normalizedReturn c p (normalizedReturn c p z)‖ < 23/20 := by
  have h := finite_phase_bounds hp3 hp16 hc hz
  have hn1 := norm_le_norm_sub_add (normalizedReturn c p z) (1:ℂ)
  simp only [norm_one] at hn1
  have hn2 := norm_le_norm_sub_add (normalizedReturn c p (normalizedReturn c p z))
    ((criticalValue c (2*p)/criticalValue c p : ℝ):ℂ)
  simp only [Complex.norm_real, Real.norm_eq_abs] at hn2
  have ha : |criticalValue c (2*p)/criticalValue c p| ≤ 4/5 :=
    abs_le.mpr ⟨h.2.2.1, by linarith only [h.2.2.2]⟩
  have hsecond : ‖normalizedReturn c p (normalizedReturn c p z) -
      ((criticalValue c (2*p)/criticalValue c p : ℝ):ℂ)‖ < 19/100 := h.2.1
  exact ⟨by linarith only [hn1, h.1], by linarith only [hn2, hsecond, ha]⟩

end

end FiniteFirstReturnBounds
