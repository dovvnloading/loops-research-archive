import TwoLevelPerturbation

/-!
# Complete-iterate perturbation with a signed moving return scale

The critical scale at a further return can be negative.  The estimates
below keep that sign and compare both the input rescaling and the output
division.  No bound for a perturbed orbit is assumed: it follows from
the reference orbit bounds and the complete perturbation budget.
-/

namespace ThreeLevelPerturbation

open Set Function LimitingCrestQuadraticReturn NearTwoShooting
open TwoLevelPerturbation

noncomputable section

/-- A relative error below one half controls the absolute moving scale,
without requiring either scale to be positive. -/
theorem moving_scale_control (d D E : ℝ) (hd : d ≠ 0)
    (hsmall : E ≤ |d|/2) (hdiff : |D-d| ≤ E) :
    |d|/2 ≤ |D| ∧ |D| ≤ 3*|d|/2 ∧ D ≠ 0 := by
  have hlower : |d| ≤ |D-d|+|D| := by
    calc
      |d| = |(d-D)+D| := by congr 1; ring
      _ ≤ |d-D|+|D| := abs_add_le _ _
      _ = |D-d|+|D| := by rw [abs_sub_comm d D]
  have hupper : |D| ≤ |D-d|+|d| := by
    calc
      |D| = |(D-d)+d| := by congr 1; ring
      _ ≤ |D-d|+|d| := abs_add_le _ _
  have hdabs : 0 < |d| := abs_pos.mpr hd
  refine ⟨by linarith, by linarith, ?_⟩
  apply abs_pos.mp
  linarith

/-- The negative scale retains its sign, with the actual order of the
two endpoints recorded explicitly. -/
theorem moving_scale_negative (d D : ℝ) (hd : d < 0)
    (hdiff : |D-d| ≤ |d|/2) :
    D < 0 ∧ 3*d/2 ≤ D ∧ D ≤ d/2 := by
  rw [abs_of_neg hd] at hdiff
  obtain ⟨hlo, hhi⟩ := abs_le.mp hdiff
  constructor
  · linarith
  constructor <;> linarith

/-- A signed moving scale and the complete iterate are perturbed
together.  The normalized reference-output bound avoids an artificial
second inverse power of the return scale. -/
theorem normalized_iterate_stability
    (H : ℂ → ℂ) (a : ℝ) (N : ℕ) (ε d D R M : ℝ)
    (hε : 0 ≤ ε) (hd : d ≠ 0)
    (hbudget : ε*(5 : ℝ)^N ≤ 1/10)
    (hrelative : ε*(5 : ℝ)^N ≤ |d|/2)
    (hdiff : |D-d| ≤ (5 : ℝ)^N*ε)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 12/5 →
      ‖H w-quadraticMap a w‖ ≤ ε)
    {z : ℂ} (hz : ‖z‖ ≤ R)
    (hDmodel : ∀ n : ℕ, n ≤ N →
      ‖((quadraticMap a)^[n]) ((D : ℂ)*z)‖ ≤ 21/10)
    (hdmodel : ∀ n : ℕ, n ≤ N →
      ‖((quadraticMap a)^[n]) ((d : ℂ)*z)‖ ≤ 21/10)
    (houtput : ‖((quadraticMap a)^[N]) ((d : ℂ)*z)/(d : ℂ)‖ ≤ M) :
    D ≠ 0 ∧
      ‖(H^[N]) ((D : ℂ)*z)/(D : ℂ)-
          ((quadraticMap a)^[N]) ((d : ℂ)*z)/(d : ℂ)‖ ≤
        2*(1+R+M)*ε*(5 : ℝ)^(2*N)/|d| := by
  let b : ℝ := (5 : ℝ)^N
  let E : ℝ := ε*b
  have hb1 : 1 ≤ b := one_le_pow₀ (by norm_num)
  have hb0 : 0 ≤ b := by positivity
  have hE0 : 0 ≤ E := mul_nonneg hε hb0
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have hM : 0 ≤ M := (norm_nonneg _).trans houtput
  have hdabs : 0 < |d| := abs_pos.mpr hd
  have hEd : E ≤ |d|/2 := hrelative
  have hdiffE : |D-d| ≤ E := by
    dsimp [E, b]
    nlinarith only [hdiff]
  obtain ⟨hDlower, _, hDne⟩ := moving_scale_control d D E hd hEd hdiffE
  have hDabs : 0 < |D| := abs_pos.mpr hDne
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hDC : (D : ℂ) ≠ 0 := by exact_mod_cast hDne
  have hpert : ‖(H^[N]) ((D : ℂ)*z)-
      ((quadraticMap a)^[N]) ((D : ℂ)*z)‖ ≤ E := by
    have he := (iterate_stability H a ((D : ℂ)*z) N ε hε hbudget
      hclose hDmodel N le_rfl).1
    dsimp [E, b]
    nlinarith only [he]
  have hinput : ‖(D : ℂ)*z-(d : ℂ)*z‖ ≤ E*R := by
    rw [← sub_mul, norm_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hdiffE hz (norm_nonneg z) hE0
  have hlip : ‖((quadraticMap a)^[N]) ((D : ℂ)*z)-
      ((quadraticMap a)^[N]) ((d : ℂ)*z)‖ ≤ b*(E*R) := by
    have he := quadratic_iterate_lipschitz a ((D : ℂ)*z) ((d : ℂ)*z) N
      (fun n hn => (hDmodel n hn).trans (by norm_num))
      (fun n hn => (hdmodel n hn).trans (by norm_num)) N le_rfl
    exact he.trans (mul_le_mul_of_nonneg_left hinput hb0)
  let A : ℂ := (H^[N]) ((D : ℂ)*z)
  let B : ℂ := ((quadraticMap a)^[N]) ((d : ℂ)*z)
  have hnum : ‖A-B‖ ≤ E+b*(E*R) := by
    have ht : ‖A-B‖ ≤ ‖(H^[N]) ((D : ℂ)*z)-
        ((quadraticMap a)^[N]) ((D : ℂ)*z)‖+
        ‖((quadraticMap a)^[N]) ((D : ℂ)*z)-
          ((quadraticMap a)^[N]) ((d : ℂ)*z)‖ := by
      simpa only [A, B, dist_eq_norm] using dist_triangle
        ((H^[N]) ((D : ℂ)*z)) (((quadraticMap a)^[N]) ((D : ℂ)*z))
        (((quadraticMap a)^[N]) ((d : ℂ)*z))
    exact ht.trans (add_le_add hpert hlip)
  have hproduct : ‖B/(d : ℂ)‖*|D-d| ≤ M*E :=
    mul_le_mul houtput hdiffE (abs_nonneg _) hM
  have hid : A/(D : ℂ)-B/(d : ℂ) =
      (A-B)/(D : ℂ)+(B/(d : ℂ))*((d : ℂ)-(D : ℂ))/(D : ℂ) := by
    field_simp [hdC, hDC]
    <;> ring
  have hquot : ‖A/(D : ℂ)-B/(d : ℂ)‖ ≤
      (E+b*(E*R)+M*E)/|D| := by
    rw [hid]
    calc
      _ ≤ ‖(A-B)/(D : ℂ)‖+
          ‖(B/(d : ℂ))*((d : ℂ)-(D : ℂ))/(D : ℂ)‖ := norm_add_le _ _
      _ = ‖A-B‖/|D|+‖B/(d : ℂ)‖*|D-d|/|D| := by
        rw [norm_div, norm_div, norm_mul]
        simp only [← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_sub_comm d D]
      _ ≤ (E+b*(E*R))/|D|+(M*E)/|D| :=
        add_le_add (div_le_div_of_nonneg_right hnum hDabs.le)
          (div_le_div_of_nonneg_right hproduct hDabs.le)
      _ = _ := by rw [add_div]
  let K : ℝ := (1+R+M)*ε*b^2
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hEb : E ≤ E*b := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb1 hE0
  have hMEb : M*E ≤ M*(E*b) := mul_le_mul_of_nonneg_left hEb hM
  have hnumK : E+b*(E*R)+M*E ≤ K := by
    dsimp [K, E] at *
    nlinarith only [hEb, hMEb]
  have hdivide : K/|D| ≤ 2*K/|d| := by
    apply (div_le_div_iff₀ hDabs hdabs).mpr
    have hm := mul_le_mul_of_nonneg_left hDlower hK0
    nlinarith only [hm]
  refine ⟨hDne, hquot.trans ((div_le_div_of_nonneg_right hnumK hDabs.le).trans ?_)⟩
  calc
    K/|D| ≤ 2*K/|d| := hdivide
    _ = 2*(1+R+M)*ε*(5 : ℝ)^(2*N)/|d| := by
      dsimp [K, b]
      rw [show 2*N = N*2 by omega, pow_mul]
      ring

/-- The comparison applies to the actual real critical return scale.
Its perturbation estimate is proved by following the complete critical
orbit, rather than included as an independent assumption. -/
theorem normalized_critical_return_stability
    (H : ℂ → ℂ) (a : ℝ) (ha : a ∈ Icc (-2 : ℝ) 0)
    (N : ℕ) (ε R M : ℝ) (hε : 0 ≤ ε)
    (hd : criticalValue a N ≠ 0)
    (hbudget : ε*(5 : ℝ)^N ≤ 1/10)
    (hrelative : ε*(5 : ℝ)^N ≤ |criticalValue a N|/2)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 12/5 →
      ‖H w-quadraticMap a w‖ ≤ ε)
    {z : ℂ} (hz : ‖z‖ ≤ R)
    (hDmodel : ∀ n : ℕ, n ≤ N →
      ‖((quadraticMap a)^[n]) ((((H^[N]) 0).re : ℂ)*z)‖ ≤ 21/10)
    (hdmodel : ∀ n : ℕ, n ≤ N →
      ‖((quadraticMap a)^[n]) ((criticalValue a N : ℂ)*z)‖ ≤ 21/10)
    (houtput : ‖normalizedReturn a N z‖ ≤ M) :
    ((H^[N]) 0).re ≠ 0 ∧
      ‖(H^[N]) ((((H^[N]) 0).re : ℂ)*z)/(((H^[N]) 0).re : ℂ)-
          normalizedReturn a N z‖ ≤
        2*(1+R+M)*ε*(5 : ℝ)^(2*N)/|criticalValue a N| := by
  exact normalized_iterate_stability H a N ε (criticalValue a N)
    ((H^[N]) 0).re R M hε hd hbudget hrelative
    (critical_return_scale_error H a ha N ε hε hbudget hclose)
    hclose hz hDmodel hdmodel houtput

/-- A product-separated outer period pays for twelve complete middle
and inner returns, even against the square of their combined scale. -/
theorem separated_three_period_error (p q r : ℕ)
    (hq : 2 ≤ q) (hr : 2 ≤ r) (hp : 20*(q*r)+100 ≤ p) :
    (128*scale p)*(5 : ℝ)^(12*(q*r)) ≤
      (scale (q+r))^2/1000000000000000000000000 := by
  have hqr : q+r ≤ q*r := by
    have hqmul := Nat.mul_le_mul_left q hr
    have hrmul := Nat.mul_le_mul_right r hq
    nlinarith only [hqmul, hrmul]
  have hp' : 18*(q*r)+(2*(q+r)+100) ≤ p := by
    nlinarith only [hp, hqr]
  have hs : scale p ≤ scale (18*(q*r)+(2*(q+r)+100)) :=
    pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) ≤ 1) hp'
  have hpow : (5 : ℝ)^(12*(q*r)) ≤ (4 : ℝ)^(18*(q*r)) := by
    calc
      (5 : ℝ)^(12*(q*r)) = ((5 : ℝ)^12)^(q*r) := pow_mul _ _ _
      _ ≤ ((4 : ℝ)^18)^(q*r) :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) (q*r)
      _ = (4 : ℝ)^(18*(q*r)) := (pow_mul _ _ _).symm
  have he : scale (18*(q*r)+(2*(q+r)+100))*(4 : ℝ)^(18*(q*r)) =
      (scale (q+r))^2*scale 100 := by
    have hdouble : (1/4 : ℝ)^(2*(q+r)) = ((1/4 : ℝ)^(q+r))^2 := by
      rw [Nat.mul_comm 2 (q+r), pow_mul]
    simp only [scale, pow_add]
    rw [hdouble]
    have hu : (1/4 : ℝ)^(18*(q*r))*(4 : ℝ)^(18*(q*r)) = 1 :=
      scale_mul_power (18*(q*r))
    calc
      _ = ((1/4 : ℝ)^(18*(q*r))*(4 : ℝ)^(18*(q*r)))*
          (((1/4 : ℝ)^(q+r))^2*(1/4 : ℝ)^100) := by ring
      _ = _ := by rw [hu]; simp only [one_mul, pow_add]
  calc
    (128*scale p)*(5 : ℝ)^(12*(q*r)) ≤
        (128*scale (18*(q*r)+(2*(q+r)+100)))*(4 : ℝ)^(18*(q*r)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) hpow
        (by positivity) (mul_nonneg (by norm_num) (scale_pos _).le)
    _ = 128*((scale (q+r))^2*scale 100) := by rw [mul_assoc, he]
    _ ≤ (scale (q+r))^2/1000000000000000000000000 := by
      have hc : 128*scale 100 ≤ (1/1000000000000000000000000 : ℝ) := by
        norm_num [scale]
      have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg (scale (q+r)))
      nlinarith only [hm]

/-- The same period wedge supplies the product-scale budget used by
the physical three-level construction. -/
theorem separated_three_period_product_error (p q r : ℕ)
    (hq : 2 ≤ q) (hr : 2 ≤ r) (hp : 20*(r*q)+100 ≤ p) :
    (128*scale p)*(5 : ℝ)^(12*(r*q)) ≤
      scale q*scale r/1000000000000 := by
  have he := separated_three_period_error p r q hr hq hp
  have hs0 : 0 ≤ scale (r+q) := (scale_pos (r+q)).le
  have hs1 : scale (r+q) ≤ 1 := by
    exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) ≤ 1)
  have hsq : (scale (r+q))^2 ≤ scale (r+q) := by
    have hm := mul_le_mul_of_nonneg_left hs1 hs0
    nlinarith only [hm]
  have hi : scale (r+q) = scale q*scale r := by
    simp only [scale, pow_add]
    ring
  rw [← hi]
  nlinarith only [he, hsq, hs0]

end

end ThreeLevelPerturbation
