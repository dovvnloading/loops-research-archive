import GlobalCrestEstimates

/-!
# The sign and order of the complete actual return remainder

All physical pre-return points after the first quadratic image remain
positive.  The first factor of the even divided difference is negative
and increases with the initial real point; its later positive factors
decrease.  The resulting complete divided difference increases strictly.
Consequently the nonlinear remainder is positive and ordered on the
whole real unit interval.  No truncated Taylor polynomial is substituted
for the actual return.
-/

namespace ActualCrestRemainderOrder

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open GlobalCrestEstimates

noncomputable section

def realIterate (c : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((fun x : ℝ => x^2+c)^[n]) t

theorem realIterate_zero (c t : ℝ) : realIterate c 0 t = t := rfl

theorem realIterate_succ (c : ℝ) (n : ℕ) (t : ℝ) :
    realIterate c (n+1) t = (realIterate c n t)^2+c := by
  exact iterate_succ_apply' (fun x : ℝ => x^2+c) n t

theorem realIterate_at_zero (c : ℝ) (n : ℕ) :
    realIterate c n 0 = criticalValue c n := rfl

theorem realIterate_neg_succ (c : ℝ) (n : ℕ) (t : ℝ) :
    realIterate c (n+1) (-t) = realIterate c (n+1) t := by
  unfold realIterate
  rw [iterate_succ_apply,iterate_succ_apply]
  simp only [neg_sq]

theorem realIterate_cast (c t : ℝ) (n : ℕ) :
    ((quadraticMap c)^[n]) (t : ℂ) = (realIterate c n t : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',ih,realIterate_succ]
    simp only [quadraticMap,Complex.ofReal_add,Complex.ofReal_pow]

theorem normalizedReturn_real_eq (c : ℝ) (p : ℕ) (x : ℝ) :
    (normalizedReturn c p (x : ℂ)).re =
      realIterate c p (criticalValue c p*x)/criticalValue c p := by
  unfold normalizedReturn
  rw [← Complex.ofReal_mul,realIterate_cast,← Complex.ofReal_div]
  rfl

private theorem critical_one (c : ℝ) : criticalValue c 1 = c := by
  simp [criticalValue]

private theorem scale_mul_power (n : ℕ) : scale n*(4 : ℝ)^n = 1 := by
  unfold scale
  rw [one_div_pow]
  exact one_div_mul_cancel (pow_ne_zero n (by norm_num))

private theorem scale_power_bound {p n k : ℕ} (h : n+k ≤ p) :
    scale p*(4 : ℝ)^n ≤ (1/4 : ℝ)^k := by
  have hm : scale p ≤ scale (n+k) :=
    pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) ≤ 1) h
  calc
    scale p*(4 : ℝ)^n ≤ scale (n+k)*(4 : ℝ)^n :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ = (1/4 : ℝ)^k := by
      rw [show scale (n+k) = scale n*(1/4 : ℝ)^k by
        unfold scale; rw [pow_add]]
      calc
        scale n*(1/4 : ℝ)^k*4^n = (scale n*4^n)*(1/4 : ℝ)^k := by ring
        _ = (1/4 : ℝ)^k := by rw [scale_mul_power,one_mul]

private theorem critical_deficit (c : ℝ) (hc : -2 ≤ c) (n : ℕ) :
    2-criticalValue c (n+2) ≤ 3*(c+2)*(4 : ℝ)^n := by
  induction n with
  | zero =>
    rw [criticalValue_two]
    norm_num only [pow_zero,mul_one]
    nlinarith only [sq_nonneg (c+2)]
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega,criticalValue_step,pow_succ (4 : ℝ) n]
    nlinarith only [ih,sq_nonneg (2-criticalValue c (n+2)),hc]

/-- Every physical critical point before the small return, apart from
the first negative point, stays uniformly to the right of one. -/
theorem critical_prefix_lower {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {j : ℕ} (hj2 : 2 ≤ j) (hjp : j ≤ p-1) :
    (17/16 : ℝ) ≤ criticalValue c j := by
  have hd := critical_deficit c hc.1.1 (j-2)
  rw [Nat.sub_add_cancel hj2] at hd
  have hpow := scale_power_bound (p := p) (n := j-2) (k := 3) (by omega)
  norm_num only [show (1/4 : ℝ)^3 = 1/64 by norm_num] at hpow
  have hε : c+2 ≤ 20*scale p := by linarith [hc.1.2]
  have hm := mul_le_mul_of_nonneg_right hε
    (show 0 ≤ 3*(4 : ℝ)^(j-2) by positivity)
  nlinarith only [hd,hm,hpow]

private theorem physical_input_small {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {t : ℝ} (ht : t ∈ Icc 0 (criticalValue c p)) :
    t ≤ 1/100 := by
  have hq := scale_small hp
  linarith [ht.2,hc.2.2.1]

private theorem physical_first_neg {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {t : ℝ} (ht : t ∈ Icc 0 (criticalValue c p)) :
    c+t^2 < 0 := by
  have ht2 := pow_le_pow_left₀ ht.1 (physical_input_small hp hc ht) 2
  have hb := parameter_band hp hc.1
  nlinarith only [ht2,hb.2]

private theorem physical_error_budget {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {t : ℝ} (ht : t ∈ Icc 0 (criticalValue c p))
    {j : ℕ} (hj2 : 2 ≤ j) (hjp : j ≤ p-1) :
    (4 : ℝ)^(j-1)*t^2 ≤ 9*scale p := by
  have htq : t ≤ 12*scale p := ht.2.trans hc.2.2.1
  have hs := pow_le_pow_left₀ ht.1 htq 2
  have hpow := scale_power_bound (p := p) (n := j-1) (k := 2) (by omega)
  norm_num only [show (1/4 : ℝ)^2 = 1/16 by norm_num] at hpow
  calc
    (4 : ℝ)^(j-1)*t^2 ≤ 4^(j-1)*(12*scale p)^2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (144*scale p)*(scale p*4^(j-1)) := by ring
    _ ≤ (144*scale p)*(1/16) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) (scale_pos p).le)
    _ = 9*scale p := by ring

/-- The complete real prefix starting anywhere between zero and the
physical return scale remains positive.  Its displacement from the
critical prefix retains an explicit quadratic input bound. -/
theorem physical_prefix_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {t : ℝ} (ht : t ∈ Icc 0 (criticalValue c p))
    {j : ℕ} (hj2 : 2 ≤ j) (hjp : j ≤ p-1) :
    (0 ≤ criticalValue c j-realIterate c j t ∧
      criticalValue c j-realIterate c j t ≤ (4 : ℝ)^(j-1)*t^2) ∧
      1 ≤ realIterate c j t := by
  have hq := scale_small hp
  have close_lower {n : ℕ} (hn2 : 2 ≤ n) (hnp : n ≤ p-1)
      (he : criticalValue c n-realIterate c n t ≤ (4 : ℝ)^(n-1)*t^2) :
      1 ≤ realIterate c n t := by
    have ha := critical_prefix_lower hp hc hn2 hnp
    have hb := physical_error_budget hp hc ht hn2 hnp
    linarith
  have hall : ∀ n : ℕ, 2 ≤ n → n ≤ p-1 →
      (0 ≤ criticalValue c n-realIterate c n t ∧
        criticalValue c n-realIterate c n t ≤ (4 : ℝ)^(n-1)*t^2) ∧
        1 ≤ realIterate c n t := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro hnp
      have hv : realIterate c 2 t = (c+t^2)^2+c := by
        simp only [show 2=1+1 from rfl,realIterate_succ,realIterate_zero]
        ring
      have hneg := physical_first_neg hp hc ht
      have horder : -(c+t^2) ≤ -c := by nlinarith only [sq_nonneg t]
      have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ -(c+t^2)) horder 2
      have hlo : 0 ≤ criticalValue c 2-realIterate c 2 t := by
        rw [criticalValue_two,hv]
        nlinarith only [hsq]
      have hm := mul_le_mul_of_nonneg_right
        (show -2*c ≤ 4 by linarith [hc.1.1]) (sq_nonneg t)
      have hhi : criticalValue c 2-realIterate c 2 t ≤ (4 : ℝ)^(2-1)*t^2 := by
        rw [criticalValue_two,hv]
        norm_num only [Nat.reduceSub,pow_one]
        nlinarith only [hm,sq_nonneg (t^2)]
      exact ⟨⟨hlo,hhi⟩,close_lower (by norm_num) hnp hhi⟩
    | succ n hn ih =>
      intro hnp
      have hprev := ih (by omega)
      have ha := critical_prefix_lower hp hc hn (by omega)
      have habs := hc.2.2.2.2.2.2 n (by omega)
      have hupper : criticalValue c n+realIterate c n t ≤ 4 := by
        linarith [(abs_le.mp habs).2,hprev.1.1]
      have hnonneg : 0 ≤ criticalValue c n+realIterate c n t := by
        linarith [hprev.2]
      have hid : criticalValue c (n+1)-realIterate c (n+1) t =
          (criticalValue c n+realIterate c n t)*
            (criticalValue c n-realIterate c n t) := by
        rw [criticalValue_step,realIterate_succ]
        ring
      have hlo : 0 ≤ criticalValue c (n+1)-realIterate c (n+1) t := by
        rw [hid]
        exact mul_nonneg hnonneg hprev.1.1
      have hhi : criticalValue c (n+1)-realIterate c (n+1) t ≤
          (4 : ℝ)^((n+1)-1)*t^2 := by
        rw [hid]
        calc
          _ ≤ 4*((4 : ℝ)^(n-1)*t^2) :=
            mul_le_mul hupper hprev.1.2 hprev.1.1 (by norm_num)
          _ = (4 : ℝ)^((n+1)-1)*t^2 := by
            rw [Nat.add_sub_cancel]
            have he : n = (n-1)+1 := by omega
            conv_rhs => rw [he,pow_succ]
            ring
      exact ⟨⟨hlo,hhi⟩,close_lower (by omega) hnp hhi⟩
  exact hall j hj2 hjp

private theorem physical_prefix_antitone {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {j : ℕ} (hj2 : 2 ≤ j) (hjp : j ≤ p-1) :
    AntitoneOn (realIterate c j) (Icc 0 (criticalValue c p)) := by
  have hall : ∀ n : ℕ, 2 ≤ n → n ≤ p-1 →
      AntitoneOn (realIterate c n) (Icc 0 (criticalValue c p)) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro hnp x hx y hy hxy
      have hs := pow_le_pow_left₀ hx.1 hxy 2
      have hny := physical_first_neg hp hc hy
      have hnxy : -(c+y^2) ≤ -(c+x^2) := by linarith
      have hh := pow_le_pow_left₀ (by linarith : 0 ≤ -(c+y^2)) hnxy 2
      change (y^2+c)^2+c ≤ (x^2+c)^2+c
      nlinarith only [hh]
    | succ n hn ih =>
      intro hnp x hx y hy hxy
      have horder := ih (by omega) hx hy hxy
      have hypos := (physical_prefix_bounds hp hc hy hn (by omega)).2
      have hs := pow_le_pow_left₀ (by linarith : 0 ≤ realIterate c n y) horder 2
      rw [realIterate_succ,realIterate_succ]
      exact add_le_add hs le_rfl
  exact hall j hj2 hjp

def realSecant (c : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n+1, t =>
      (realIterate c (n+1) t+criticalValue c (n+1))*realSecant c n t

theorem realSecant_at_zero (c : ℝ) (n : ℕ) :
    realSecant c n 0 = quadraticCoefficient c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [realSecant,realIterate_at_zero,ih,quadraticCoefficient]
    ring

theorem iterate_difference_zero (c : ℝ) (n : ℕ) (t : ℝ) :
    realIterate c (n+1) t-criticalValue c (n+1) = t^2*realSecant c n t := by
  induction n with
  | zero =>
    simp [realIterate_succ,realIterate_zero,critical_one,realSecant]
  | succ n ih =>
    calc
      realIterate c (n+1+1) t-criticalValue c (n+1+1) =
          (realIterate c (n+1) t+criticalValue c (n+1))*
            (realIterate c (n+1) t-criticalValue c (n+1)) := by
        rw [realIterate_succ,criticalValue_step]
        ring
      _ = t^2*realSecant c (n+1) t := by
        rw [ih,realSecant]
        ring

/-- The complete even divided difference is negative and strictly
increases along the whole physical input interval. -/
theorem physical_secant_order {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {n : ℕ} (hn : 1 ≤ n) (hnp : n ≤ p-1) :
    (∀ t ∈ Icc 0 (criticalValue c p), realSecant c n t < 0) ∧
      StrictMonoOn (realSecant c n) (Icc 0 (criticalValue c p)) := by
  have hall : ∀ n : ℕ, 1 ≤ n → n ≤ p-1 →
      (∀ t ∈ Icc 0 (criticalValue c p), realSecant c n t < 0) ∧
        StrictMonoOn (realSecant c n) (Icc 0 (criticalValue c p)) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro hnp
      have he (t : ℝ) : realSecant c 1 t = 2*c+t^2 := by
        simp [realSecant,realIterate_succ,realIterate_zero,critical_one] <;> ring
      constructor
      · intro t ht
        rw [he]
        have h := physical_first_neg hp hc ht
        have hb := parameter_band hp hc.1
        linarith [hb.2]
      · intro x hx y hy hxy
        rw [he,he]
        have hs := pow_lt_pow_left₀ hxy hx.1 (by decide : (2 : ℕ) ≠ 0)
        linarith
    | succ n hn ih =>
      intro hnp
      have hprev := ih (by omega)
      have hapos := critical_prefix_lower hp hc (j := n+1) (by omega) hnp
      have hpos (t : ℝ) (ht : t ∈ Icc 0 (criticalValue c p)) :
          0 < realIterate c (n+1) t+criticalValue c (n+1) := by
        have htpos := (physical_prefix_bounds hp hc ht (by omega) hnp).2
        linarith
      constructor
      · intro t ht
        rw [realSecant]
        exact mul_neg_of_pos_of_neg (hpos t ht) (hprev.1 t ht)
      · intro x hx y hy hxy
        have hfactor := physical_prefix_antitone hp hc (j := n+1) (by omega) hnp hx hy hxy.le
        have hfactor' : realIterate c (n+1) y+criticalValue c (n+1) ≤
            realIterate c (n+1) x+criticalValue c (n+1) :=
          add_le_add hfactor le_rfl
        rw [realSecant,realSecant]
        exact (mul_le_mul_of_nonpos_right hfactor' (hprev.1 x hx).le).trans_lt
          (mul_lt_mul_of_pos_left (hprev.2 hx hy hxy) (hpos y hy))
  exact hall n hn hnp

def physicalRemainder (c : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  realIterate c (n+1) t-criticalValue c (n+1)-quadraticCoefficient c n*t^2

theorem physicalRemainder_eq_secant (c : ℝ) (n : ℕ) (t : ℝ) :
    physicalRemainder c n t = t^2*(realSecant c n t-realSecant c n 0) := by
  rw [physicalRemainder,iterate_difference_zero,realSecant_at_zero]
  ring

theorem physicalRemainder_neg (c : ℝ) (n : ℕ) (t : ℝ) :
    physicalRemainder c n (-t) = physicalRemainder c n t := by
  simp only [physicalRemainder,realIterate_neg_succ,neg_sq]

theorem physicalRemainder_step (c : ℝ) (n : ℕ) (t : ℝ) :
    physicalRemainder c (n+1) t =
      2*criticalValue c (n+1)*physicalRemainder c n t+
        (quadraticCoefficient c n*t^2+physicalRemainder c n t)^2 := by
  simp only [physicalRemainder,realIterate_succ,criticalValue_step,quadraticCoefficient]
  ring

theorem physical_remainder_nonneg {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {t : ℝ} (ht : t ∈ Icc 0 (criticalValue c p))
    {n : ℕ} (hn : n+1 ≤ p) : 0 ≤ physicalRemainder c n t := by
  rw [physicalRemainder_eq_secant]
  by_cases hn0 : n=0
  · simp [hn0,realSecant]
  · have hm := (physical_secant_order hp hc (n := n) (by omega) (by omega)).2.monotoneOn
    have h := hm (show (0 : ℝ) ∈ Icc 0 (criticalValue c p) from ⟨le_rfl,hc.2.1.le⟩)
      ht ht.1
    exact mul_nonneg (sq_nonneg t) (sub_nonneg.mpr h)

theorem physical_remainder_mono {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {n : ℕ} (hn : n+1 ≤ p) :
    MonotoneOn (physicalRemainder c n) (Icc 0 (criticalValue c p)) := by
  intro x hx y hy hxy
  rw [physicalRemainder_eq_secant,physicalRemainder_eq_secant]
  by_cases hn0 : n=0
  · simp [hn0,realSecant]
  · have hm := (physical_secant_order hp hc (n := n) (by omega) (by omega)).2.monotoneOn
    have h0 := hm (show (0 : ℝ) ∈ Icc 0 (criticalValue c p) from ⟨le_rfl,hc.2.1.le⟩)
      hx hx.1
    exact mul_le_mul (pow_le_pow_left₀ hx.1 hxy 2)
      (sub_le_sub_right (hm hx hy hxy) _) (sub_nonneg.mpr h0) (sq_nonneg y)

def realRemainder (c : ℝ) (p : ℕ) (x : ℝ) : ℝ :=
  (normalizedReturn c p (x : ℂ)).re-(1-kappa p c*x^2)

theorem realRemainder_eq_physical {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (x : ℝ) :
    realRemainder c p x =
      physicalRemainder c (p-1) (criticalValue c p*x)/criticalValue c p := by
  rw [realRemainder,normalizedReturn_real_eq]
  unfold physicalRemainder kappa
  simp only [show p-1+1=p by omega]
  field_simp [hc.2.1.ne']
  ring

theorem realRemainder_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : realRemainder c p 0 = 0 := by
  rw [realRemainder_eq_physical hp hc]
  simp [physicalRemainder_eq_secant]

private theorem realRemainder_neg {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (x : ℝ) : realRemainder c p (-x) = realRemainder c p x := by
  rw [realRemainder_eq_physical hp hc,realRemainder_eq_physical hp hc,mul_neg,
    physicalRemainder_neg]

/-- The entire nonlinear correction has its minimum at zero and its
maximum at the real unit endpoints.  All higher polynomial terms are
included in this order statement. -/
theorem actual_remainder_order {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {x : ℝ} (hx : |x| ≤ 1) :
    0 ≤ realRemainder c p x ∧ realRemainder c p x ≤ realRemainder c p 1 := by
  have habs : realRemainder c p x = realRemainder c p |x| := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h,realRemainder_neg hp hc]
  have ht : criticalValue c p*|x| ∈ Icc 0 (criticalValue c p) := by
    refine ⟨mul_nonneg hc.2.1.le (abs_nonneg x),?_⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx hc.2.1.le
  have hd : criticalValue c p ∈ Icc 0 (criticalValue c p) := ⟨hc.2.1.le,le_rfl⟩
  have h : 0 ≤ realRemainder c p |x| ∧
      realRemainder c p |x| ≤ realRemainder c p 1 := by
    simp only [realRemainder_eq_physical hp hc,mul_one]
    exact ⟨div_nonneg (physical_remainder_nonneg hp hc ht (by omega)) hc.2.1.le,
      div_le_div_of_nonneg_right
        (physical_remainder_mono hp hc (n := p-1) (by omega) ht hd ht.2) hc.2.1.le⟩
  simpa only [← habs] using h

/-- The actual return has a strictly positive nonlinear correction at
the real unit endpoint; it is never exactly its quadratic model. -/
theorem actual_remainder_one_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : 0 < realRemainder c p 1 := by
  rw [realRemainder_eq_physical hp hc,mul_one,physicalRemainder_eq_secant]
  have hmono := (physical_secant_order hp hc (n := p-1) (by omega) le_rfl).2
  have hs := hmono
    (show (0 : ℝ) ∈ Icc 0 (criticalValue c p) from ⟨le_rfl,hc.2.1.le⟩)
    (show criticalValue c p ∈ Icc 0 (criticalValue c p) from ⟨hc.2.1.le,le_rfl⟩)
    hc.2.1
  exact div_pos (mul_pos (pow_pos hc.2.1 2) (sub_pos.mpr hs)) hc.2.1

end
end ActualCrestRemainderOrder
