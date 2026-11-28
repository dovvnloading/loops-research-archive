import GlobalWindowLocalization

/-!
# The signed fourth return enters the coefficient chart globally

The physical restrictive interval supplies the unit invariant interval
for its normalized return.  A complete remainder bound then excludes
coefficients at least two whenever the fourth return is positive.
-/

namespace GlobalWindowSignedChart

open Set Function NearTwoInverse NearTwoShooting
open LimitingCrestQuadraticReturn GlobalRestrictiveWindow

noncomputable section

def realReturn (c : ℝ) (p : ℕ) (t : ℝ) : ℝ :=
  (realMap c)^[p] (criticalValue c p*t)/criticalValue c p

theorem critical_bound (c : ℝ) (hc : c ∈ Icc (-2 : ℝ) 0) (j : ℕ) :
    |criticalValue c j|≤2 := by
  have hinterval : ∀ n : ℕ, criticalValue c n ∈ Icc c (-c) := by
    intro n
    induction n with
    | zero =>
      change c≤(0 : ℝ) ∧ (0 : ℝ)≤ -c
      constructor <;> linarith [hc.2]
    | succ n ih =>
      have hsquare : (criticalValue c n)^2≤(-c)^2 :=
        sq_le_sq' (by linarith [ih.1]) ih.2
      have hproduct : c*(c+2)≤0 :=
        mul_nonpos_of_nonpos_of_nonneg hc.2 (by linarith [hc.1])
      rw [criticalValue_step]
      constructor
      · nlinarith only [sq_nonneg (criticalValue c n)]
      · nlinarith only [hsquare,hproduct]
  have hj := hinterval j
  rw [abs_le]
  constructor <;> linarith [hc.1,hj.1,hj.2]

private theorem scale_identity (p : ℕ) : (4 : ℝ)^p*scale p=1 := by
  unfold scale
  rw [← mul_pow]
  norm_num

/-- The complete normalized complex return on the unit disk has a
uniform error bound over the entire physical restrictive class. -/
theorem normalized_return_error {c : ℝ} {p : ℕ} (hp : 17≤p)
    (h : PositiveRestrictiveReturn c p) {z : ℂ} (hz : ‖z‖≤1) :
    ‖normalizedReturn c p z-LimitingCrest.complexMap (kappa p c) z‖≤
      22*scale p := by
  let d := criticalValue c p
  let S : ℝ := 4^p
  have hd : 0<d := h.return_pos
  have hS : 0<S := by dsimp [S]; positivity
  have hSq : S*scale p=1 := scale_identity p
  have hq := scale_small hp
  have hSd : S*d≤14 := by
    have hm := mul_le_mul_of_nonneg_left (h.return_scale hp).le hS.le
    change S*d≤S*(14*scale p) at hm
    calc
      S*d≤S*(14*scale p) := hm
      _=14 := by nlinarith only [hSq]
  have hSd0 : 0≤S*d := mul_nonneg hS.le hd.le
  have hscale : S*d^2≤1 := by
    have hm := mul_le_mul_of_nonneg_right hSd hd.le
    have hsmall : d≤14*scale p := (h.return_scale hp).le
    nlinarith only [hm,hsmall,hq]
  have hdz : ‖(d : ℂ)*z‖≤d := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hd.le
  have herr := complete_remainder_bound c (p-1) d ((d : ℂ)*z) hd.le
    (fun j _ => critical_bound c ⟨h.parameter_band.1,by linarith [h.parameter_band.2]⟩ j)
    (by simpa only [Nat.sub_add_cancel (by omega : 1≤p)] using hscale) hdz
  rw [Nat.sub_add_cancel (by omega : 1≤p)] at herr
  change ‖quadraticRemainder c (p-1) ((d : ℂ)*z)‖≤(S*d^2)^2/128 at herr
  have hdne : (d : ℂ)≠0 := by exact_mod_cast hd.ne'
  have hid : normalizedReturn c p z-LimitingCrest.complexMap (kappa p c) z=
      quadraticRemainder c (p-1) ((d : ℂ)*z)/(d : ℂ) := by
    unfold normalizedReturn LimitingCrest.complexMap quadraticRemainder kappa
    rw [Nat.sub_add_cancel (by omega : 1≤p)]
    change (quadraticMap c)^[p] ((d : ℂ)*z)/(d : ℂ)-
      (1-((-quadraticCoefficient c (p-1)*d : ℝ) : ℂ)*z^2)=
        ((quadraticMap c)^[p] ((d : ℂ)*z)-(d : ℂ)-
          (quadraticCoefficient c (p-1) : ℂ)*((d : ℂ)*z)^2)/(d : ℂ)
    push_cast
    field_simp [hdne]
    ring
  have hcubed := pow_le_pow_left₀ hSd0 hSd 3
  have hbound : (S*d^2)^2/128/d≤22/S := by
    apply (div_le_div_iff₀ hd hS).mpr
    have hm := mul_le_mul_of_nonneg_right hcubed hd.le
    have hform : ((S*d^2)^2/128)*S=(S*d)^3*d/128 := by ring
    rw [hform]
    nlinarith only [hm,hd]
  have h22 : 22/S=22*scale p := by
    apply (div_eq_iff hS.ne').mpr
    nlinarith only [hSq]
  rw [hid,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
  exact ((div_le_div_of_nonneg_right herr hd.le).trans hbound).trans_eq h22

private theorem complex_iterate_real (c t : ℝ) (n : ℕ) :
    (quadraticMap c)^[n] (t : ℂ)=(((realMap c)^[n] t : ℝ) : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih]
    simp only [quadraticMap,realMap,Complex.ofReal_add,Complex.ofReal_pow]

theorem normalized_real_value (c t : ℝ) (p : ℕ) :
    normalizedReturn c p (t : ℂ)=(realReturn c p t : ℂ) := by
  unfold normalizedReturn realReturn
  rw [← Complex.ofReal_mul,complex_iterate_real,Complex.ofReal_div]

theorem realReturn_error {c : ℝ} {p : ℕ} (hp : 17≤p)
    (h : PositiveRestrictiveReturn c p) {t : ℝ} (ht : t∈Icc (-1 : ℝ) 1) :
    |realReturn c p t-(1-kappa p c*t^2)|≤22*scale p := by
  have htNorm : ‖(t : ℂ)‖≤1 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ht
  have he := normalized_return_error hp h htNorm
  rw [normalized_real_value] at he
  have hid : (realReturn c p t : ℂ)-LimitingCrest.complexMap (kappa p c) (t : ℂ)=
      ((realReturn c p t-(1-kappa p c*t^2) : ℝ) : ℂ) := by
    simp only [LimitingCrest.complexMap]
    push_cast
    ring
  rw [hid,Complex.norm_real,Real.norm_eq_abs] at he
  exact he

theorem realReturn_mapsTo {c : ℝ} {p : ℕ} (h : PositiveRestrictiveReturn c p) :
    MapsTo (realReturn c p) (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) := by
  intro t ht
  have hin : criticalValue c p*t∈returnInterval c p := by
    constructor
    · have hm := mul_le_mul_of_nonneg_left ht.1 h.return_pos.le
      simpa only [mul_neg_one] using hm
    · have hm := mul_le_mul_of_nonneg_left ht.2 h.return_pos.le
      simpa only [mul_one] using hm
  have hout := h.invariant hin
  constructor
  · exact (le_div_iff₀ h.return_pos).mpr (by simpa only [neg_one_mul] using hout.1)
  · exact (div_le_iff₀ h.return_pos).mpr (by simpa only [one_mul] using hout.2)

theorem realReturn_zero {c : ℝ} {p : ℕ} (hd : criticalValue c p≠0) :
    realReturn c p 0=1 := by
  unfold realReturn
  rw [mul_zero]
  change criticalValue c p/criticalValue c p=1
  exact div_self hd

theorem realReturn_iterate_zero {c : ℝ} {p : ℕ} (hd : criticalValue c p≠0) (n : ℕ) :
    (realReturn c p)^[n] 0=criticalValue c (n*p)/criticalValue c p := by
  induction n with
  | zero => simp [criticalValue]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    unfold realReturn
    rw [mul_div_cancel₀ _ hd]
    change (realMap c)^[p] ((realMap c)^[n*p] 0)/criticalValue c p=
      (realMap c)^[(n+1)*p] 0/criticalValue c p
    rw [← Function.iterate_add_apply,show p+n*p=(n+1)*p by ring]

private theorem fourth_iterate (c : ℝ) (p : ℕ) (hd : criticalValue c p≠0) :
    realReturn c p (realReturn c p (realReturn c p 1))=
      criticalValue c (4*p)/criticalValue c p := by
  have h := realReturn_iterate_zero hd 4
  simpa only [show (4 : ℕ)=3+1 from rfl,show (3 : ℕ)=2+1 from rfl,
    show (2 : ℕ)=1+1 from rfl,Function.iterate_succ_apply',Function.iterate_one,
    Function.iterate_zero,id_eq,realReturn_zero hd] using h

/-- A positive fourth return excludes the boundary and exterior of the
classical coefficient chart for every globally restrictive parameter. -/
theorem kappa_lt_two_of_fourth_return_pos {c : ℝ} {p : ℕ} (hp : 17≤p)
    (h : PositiveRestrictiveReturn c p) (hfourth : 0<criticalValue c (4*p)) :
    kappa p c<2 := by
  let x := realReturn c p 1
  let y := realReturn c p x
  have hxmem : x∈Icc (-1 : ℝ) 1 := realReturn_mapsTo h (by norm_num)
  have hymem : y∈Icc (-1 : ℝ) 1 := realReturn_mapsTo h hxmem
  have he1 := (abs_le.mp (realReturn_error hp h (show (1 : ℝ)∈Icc (-1 : ℝ) 1 by norm_num))).2
  have hex := (abs_le.mp (realReturn_error hp h hxmem)).2
  have hey := (abs_le.mp (realReturn_error hp h hymem)).2
  change x-(1-kappa p c*1^2)≤22*scale p at he1
  change y-(1-kappa p c*x^2)≤22*scale p at hex
  have hq : 22*scale p≤1/1000 := by linarith [scale_small hp]
  have hpositive : 0<realReturn c p y := by
    change 0<realReturn c p (realReturn c p (realReturn c p 1))
    rw [fourth_iterate c p h.return_pos.ne']
    exact div_pos hfourth h.return_pos
  by_contra hk
  have hk2 : 2≤kappa p c := le_of_not_gt hk
  have hx : x≤ -99/100 := by nlinarith only [he1,hq,hk2]
  have hxsq : (99/100 : ℝ)^2≤x^2 := by
    have hm := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤99/100)
      (show (99/100 : ℝ)≤ -x by linarith) 2
    simpa only [neg_sq] using hm
  have hmx := mul_le_mul_of_nonneg_right hk2 (sq_nonneg x)
  have hy : y≤ -9/10 := by nlinarith only [hex,hq,hxsq,hmx]
  have hysq : (9/10 : ℝ)^2≤y^2 := by
    have hm := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤9/10)
      (show (9/10 : ℝ)≤ -y by linarith) 2
    simpa only [neg_sq] using hm
  have hmy := mul_le_mul_of_nonneg_right hk2 (sq_nonneg y)
  nlinarith only [hey,hq,hysq,hmy,hpositive]

theorem kappa_pos_of_second_return_neg {c : ℝ} {p : ℕ} (hp : 17≤p)
    (h : PositiveRestrictiveReturn c p) (hsecond : criticalValue c (2*p)<0) :
    0<kappa p c := by
  have he := (abs_le.mp (realReturn_error hp h
    (show (1 : ℝ)∈Icc (-1 : ℝ) 1 by norm_num))).1
  have hiter := realReturn_iterate_zero h.return_pos.ne' 2
  have hvalue : realReturn c p 1=criticalValue c (2*p)/criticalValue c p := by
    simpa only [show (2 : ℕ)=1+1 from rfl,Function.iterate_succ_apply',
      Function.iterate_one,Function.iterate_zero,id_eq,realReturn_zero h.return_pos.ne'] using hiter
  have hneg : realReturn c p 1<0 := by
    rw [hvalue]
    exact div_neg_of_neg_of_pos hsecond h.return_pos
  have hq := scale_small hp
  nlinarith only [he,hneg,hq]

/-- The two indicated signed returns force the complete physical class
into the open normalized coefficient chart, without a relation premise. -/
theorem signed_coefficient_chart {c : ℝ} {p : ℕ} (hp : 17≤p)
    (h : PositiveRestrictiveReturn c p)
    (hsecond : criticalValue c (2*p)<0) (hfourth : 0<criticalValue c (4*p)) :
    kappa p c∈Ioo (0 : ℝ) 2 :=
  ⟨kappa_pos_of_second_return_neg hp h hsecond,
    kappa_lt_two_of_fourth_return_pos hp h hfourth⟩

end
end GlobalWindowSignedChart
