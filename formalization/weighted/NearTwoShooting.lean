import NearTwoInverse
import NearTwoProduct
import LimitingCrestQuadraticReturn
import ParabolicShooting

/-!
# A whole real shooting chart near minus two

The chart is constructed with the positive inverse branch of the actual
quadratic polynomial. It will be used to select a genuine critical relation
inside the sharp normalized coefficient interval.
-/

namespace NearTwoShooting

open Set Function Finset
open NearTwoInverse LimitingCrestQuadraticReturn
noncomputable section

def scale (p : ℕ) : ℝ := (1/4)^p

theorem scale_pos (p : ℕ) : 0 < scale p := by unfold scale; positivity

theorem scale_succ (p : ℕ) : scale (p+1) = scale p/4 := by
  unfold scale
  rw [pow_succ]
  ring

theorem scale_small {p : ℕ} (hp : 17 ≤ p) :
    scale p ≤ 1/17179869184 := by
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/4)
    (by norm_num : (1/4 : ℝ) ≤ 1) hp
  norm_num at h
  exact h

theorem horizon_scale_small {p : ℕ} (hp : 17 ≤ p) :
    (p : ℝ)*scale p ≤ 17/17179869184 := by
  induction p, hp using Nat.le_induction with
  | base => norm_num [scale]
  | succ n hn ih =>
    have hq := (scale_pos n).le
    have hn' : (17 : ℝ) ≤ n := by exact_mod_cast hn
    rw [scale_succ]
    push_cast
    have h : ((n : ℝ)+1)*scale n/4 ≤ (n : ℝ)*scale n := by
      have hmul := mul_nonneg (show (0 : ℝ) ≤ 3*n-1 by linarith) hq
      nlinarith only [hmul]
    linarith

theorem parameter_band {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p)) :
    c ∈ Icc (-2 : ℝ) (-49/25) := by
  refine ⟨hc.1, ?_⟩
  have hq := scale_small hp
  linarith [hc.2]

theorem terminal_band {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (12*scale p)) : d ∈ Icc (0 : ℝ) 2 := by
  refine ⟨hd.1, ?_⟩
  have hq := scale_small hp
  linarith [hd.2]

def shooting (n : ℕ) (d c : ℝ) : ℝ := c^2+c-back c n d

theorem continuous_shooting (n : ℕ) (d : ℝ) : Continuous (shooting n d) := by
  unfold shooting
  exact ((continuous_id.pow 2).add continuous_id).sub
    (continuous_back_parameter n d)

theorem shooting_strictAnti (n : ℕ) {d : ℝ} (hd : d ∈ Icc (0 : ℝ) 2) :
    StrictAntiOn (shooting n d) (Icc (-2 : ℝ) (-49/25)) := by
  intro a ha b hb hab
  have h := back_parameter_lipschitz ha hb hd n
  have he : |a-b| = b-a := by rw [abs_of_neg (sub_neg.mpr hab)]; ring
  rw [he] at h
  have hdiff := (le_abs_self (back a n d-back b n d)).trans h
  have hs : a+b+1+(5/9 : ℝ) < 0 := by linarith [ha.2,hb.2]
  have hm := mul_neg_of_neg_of_pos hs (sub_pos.mpr hab)
  dsimp [shooting]
  nlinarith only [hdiff,hm]

private theorem chebyshev_back_lt_two {d : ℝ} (hd : d < 2) (n : ℕ) :
    back (-2) n d < 2 := by
  induction n with
  | zero => exact hd
  | succ n ih =>
    rw [back_succ, B]
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).mpr (by nlinarith)

theorem shooting_left_pos {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (12*scale p)) :
    0 < shooting (p-2) d (-2) := by
  have hq := scale_small hp
  have hd2 : d < 2 := by linarith [hd.2]
  have h := chebyshev_back_lt_two hd2 (p-2)
  dsimp [shooting]
  linarith

theorem shooting_right_neg {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (12*scale p)) :
    shooting (p-2) d (-2+20*scale p) < 0 := by
  let c := -2+20*scale p
  have hq0 := scale_pos p
  have hq := scale_small hp
  have hc : c ∈ Icc (-2 : ℝ) (-49/25) :=
    parameter_band hp ⟨by dsimp [c]; linarith, le_rfl⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 2 := by norm_num
  have h := back_parameter_lipschitz (c := (-2 : ℝ)) (by norm_num) hc h0 (p-2)
  have habs : |(-2 : ℝ)-c| = 20*scale p := by
    rw [abs_of_nonpos (by dsimp [c]; linarith)]
    dsimp [c]
    ring
  rw [habs] at h
  have hdiff := (le_abs_self (back (-2) (p-2) 0-back c (p-2) 0)).trans h
  have hmon := back_mono_initial c (p-2) hd.1
  have hcheb := chebyshev_deficit_upper (p-2)
  have hp2 : (1/4 : ℝ)^(p-2) = 16*scale p := by
    have he := pow_add (1/4 : ℝ) (p-2) 2
    rw [Nat.sub_add_cancel (by omega : 2 ≤ p)] at he
    norm_num at he
    dsimp [scale]
    linarith
  rw [hp2] at hcheb
  have hsq := mul_le_mul_of_nonneg_left hq hq0.le
  change c^2+c-back c (p-2) d < 0
  dsimp [c] at *
  nlinarith only [hcheb,hdiff,hmon,hsq,hq0]

theorem unique_shooting_parameter {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (12*scale p)) :
    ∃! c : ℝ, c ∈ Icc (-2 : ℝ) (-2+20*scale p) ∧
      shooting (p-2) d c = 0 := by
  have hab : (-2 : ℝ) ≤ -2+20*scale p := by linarith [scale_pos p]
  obtain ⟨c,hc,hz⟩ := intermediate_value_Icc' hab
    (continuous_shooting (p-2) d).continuousOn
    (show (0 : ℝ) ∈ Icc (shooting (p-2) d (-2+20*scale p))
      (shooting (p-2) d (-2)) from
      ⟨(shooting_right_neg hp hd).le,(shooting_left_pos hp hd).le⟩)
  refine ⟨c,⟨hc,hz⟩,?_⟩
  intro x hx
  exact (shooting_strictAnti (p-2) (terminal_band hp hd)).injOn
    (parameter_band hp hx.1) (parameter_band hp hc) (hx.2.trans hz.symm)

theorem criticalValue_step (c : ℝ) (n : ℕ) :
    criticalValue c (n+1) = (criticalValue c n)^2+c := by
  simp only [criticalValue, iterate_succ_apply']

theorem criticalValue_two (c : ℝ) : criticalValue c 2 = c^2+c := by
  simp [criticalValue, Function.iterate_succ_apply']

/-- A shooting identity identifies every intermediate literal critical
iterate with the selected positive inverse orbit. -/
theorem shooting_critical_itinerary {c d : ℝ} {n : ℕ}
    (hc : c ∈ Icc (-2 : ℝ) (-49/25)) (hd : d ∈ Icc (0 : ℝ) 2)
    (hs : shooting n d c = 0) :
    ∀ j ≤ n, criticalValue c (j+2) = back c (n-j) d := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.zero_add,Nat.sub_zero,criticalValue_two]
    dsimp [shooting] at hs
    linarith only [hs]
  | succ j ih =>
    intro hj
    have hjn : j ≤ n := by omega
    have hi := ih hjn
    have hsub : n-j = (n-(j+1))+1 := by omega
    rw [show j+1+2 = (j+2)+1 by omega, criticalValue_step, hi, hsub, back_succ]
    have hsq := B_sq (show c ≤ 0 by linarith [hc.2])
      (back_bounds hc hd (n-(j+1))).1
    linarith only [hsq]

theorem shooting_terminal_value {c d : ℝ} {n : ℕ}
    (hc : c ∈ Icc (-2 : ℝ) (-49/25)) (hd : d ∈ Icc (0 : ℝ) 2)
    (hs : shooting n d c = 0) : criticalValue c (n+2) = d := by
  simpa only [Nat.sub_self, back_zero] using shooting_critical_itinerary hc hd hs n le_rfl

/-- Between two inverse shooting graphs, every real critical iterate
stays on the selected positive branch, and the terminal value stays
between the terminal shooting values. -/
theorem shooting_sandwich {c d : ℝ} {n : ℕ}
    (hc : c ∈ Icc (-2 : ℝ) (-49/25)) (hd : d ∈ Icc (0 : ℝ) 2)
    (hl : back c n 0 ≤ c^2+c) (hu : c^2+c ≤ back c n d) :
    ∀ j ≤ n, criticalValue c (j+2) ∈
      Icc (back c (n-j) 0) (back c (n-j) d) := by
  intro j
  induction j with
  | zero =>
    intro _
    simpa only [Nat.zero_add,Nat.sub_zero,criticalValue_two,Set.mem_Icc] using And.intro hl hu
  | succ j ih =>
    intro hj
    have hs := ih (by omega)
    have hsub : n-j = (n-(j+1))+1 := by omega
    have hzl := back_bounds hc (show (0 : ℝ) ∈ Icc (0 : ℝ) 2 by norm_num) (n-j)
    have hzl' := back_bounds hc (show (0 : ℝ) ∈ Icc (0 : ℝ) 2 by norm_num) (n-(j+1))
    have hzu' := back_bounds hc hd (n-(j+1))
    have hslo := pow_le_pow_left₀ hzl.1 hs.1 2
    have hsup := pow_le_pow_left₀ (hzl.1.trans hs.1) hs.2 2
    rw [hsub, back_succ] at hslo hsup
    rw [B_sq (by linarith [hc.2]) hzl'.1] at hslo
    rw [B_sq (by linarith [hc.2]) hzu'.1] at hsup
    rw [show j+1+2 = (j+2)+1 by omega, criticalValue_step]
    constructor <;> linarith

private theorem back_strictMono_initial {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-49/25)) (n : ℕ) :
    StrictMonoOn (back c n) (Icc (0 : ℝ) 2) := by
  induction n with
  | zero => intro x hx y hy hxy; exact hxy
  | succ n ih =>
    intro x hx y hy hxy
    rw [back_succ,back_succ]
    unfold B
    exact Real.sqrt_lt_sqrt
      (by linarith [(back_bounds hc hx n).1,hc.2])
      (sub_lt_sub_right (ih hx hy hxy) c)

theorem forward_orbit_shooting {c : ℝ} {n : ℕ}
    (hnonneg : ∀ j ≤ n, 0 ≤ criticalValue c (j+2)) :
    shooting n (criticalValue c (n+2)) c = 0 := by
  have he : ∀ j ≤ n, back c j (criticalValue c (n+2)) =
      criticalValue c (n-j+2) := by
    intro j
    induction j with
    | zero => intro _; simp only [back_zero,Nat.sub_zero]
    | succ j ih =>
      intro hj
      rw [back_succ,ih (by omega)]
      have hindex : n-j+2 = (n-(j+1)+2)+1 := by omega
      rw [hindex,criticalValue_step]
      unfold B
      rw [add_sub_cancel_right]
      exact Real.sqrt_sq (hnonneg (n-(j+1)) (by omega))
  have hfin := he n le_rfl
  simp only [Nat.sub_self,Nat.zero_add,criticalValue_two] at hfin
  unfold shooting
  rw [hfin]
  ring

structure RealChart (p : ℕ) (a b : ℝ) : Prop where
  left_band : a ∈ Icc (-2 : ℝ) (-2+20*scale p)
  right_band : b ∈ Icc (-2 : ℝ) (-2+20*scale p)
  ordered : a < b
  left_return : criticalValue a p = 12*scale p
  right_return : criticalValue b p = 0
  return_range : ∀ c ∈ Icc a b, criticalValue c p ∈ Icc (0 : ℝ) (12*scale p)
  itinerary : ∀ c ∈ Icc a b, shooting (p-2) (criticalValue c p) c = 0

theorem exists_real_chart (p : ℕ) (hp : 17 ≤ p) : ∃ a b, RealChart p a b := by
  have hscale := scale_pos p
  have hD : (12*scale p : ℝ) ∈ Icc (0 : ℝ) (12*scale p) :=
    ⟨by positivity,le_rfl⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (12*scale p) :=
    ⟨le_rfl,by positivity⟩
  obtain ⟨a,⟨ha,ha0⟩,_⟩ := unique_shooting_parameter hp hD
  obtain ⟨b,⟨hb,hb0⟩,_⟩ := unique_shooting_parameter hp h0
  have ha' := parameter_band hp ha
  have hb' := parameter_band hp hb
  have hapos : 0 < shooting (p-2) 0 a := by
    have hs := back_strictMono_initial ha' (p-2)
      (terminal_band hp h0) (terminal_band hp hD)
      (show (0 : ℝ) < 12*scale p by positivity)
    dsimp [shooting] at ha0 ⊢
    linarith only [hs,ha0]
  have hab : a < b := by
    by_contra! h
    have hs := (shooting_strictAnti (p-2) (terminal_band hp h0)).antitoneOn hb' ha' h
    linarith only [hs,hb0,hapos]
  have sub {c : ℝ} (hc : c ∈ Icc a b) : c ∈ Icc (-2 : ℝ) (-2+20*scale p) :=
    ⟨ha.1.trans hc.1,hc.2.trans hb.2⟩
  have hsand {c : ℝ} (hc : c ∈ Icc a b) :
      ∀ j ≤ p-2, criticalValue c (j+2) ∈
        Icc (back c ((p-2)-j) 0) (back c ((p-2)-j) (12*scale p)) := by
    have hc' := parameter_band hp (sub hc)
    have hlo := (shooting_strictAnti (p-2) (terminal_band hp h0)).antitoneOn hc' hb' hc.2
    have hup := (shooting_strictAnti (p-2) (terminal_band hp hD)).antitoneOn ha' hc' hc.1
    apply shooting_sandwich hc' (terminal_band hp hD)
    · dsimp [shooting] at hlo hb0
      linarith only [hlo,hb0]
    · dsimp [shooting] at hup ha0
      linarith only [hup,ha0]
  have hp2 : p-2+2 = p := by omega
  refine ⟨a,b,ha,hb,hab,?_,?_,?_,?_⟩
  · simpa only [hp2] using shooting_terminal_value ha' (terminal_band hp hD) ha0
  · simpa only [hp2] using shooting_terminal_value hb' (terminal_band hp h0) hb0
  · intro c hc
    simpa only [hp2,Nat.sub_self,back_zero] using hsand hc (p-2) le_rfl
  · intro c hc
    have h := forward_orbit_shooting (n := p-2) (c := c) (by
      intro j hj
      exact (back_bounds (parameter_band hp (sub hc))
        (terminal_band hp h0) ((p-2)-j)).1.trans (hsand hc j hj).1)
    simpa only [hp2] using h

theorem coefficient_product (c : ℝ) (n : ℕ) :
    quadraticCoefficient c (n+1) =
      (2*c)*4^n*∏ j ∈ Finset.range n, criticalValue c (j+2)/2 := by
  induction n with
  | zero => simp [quadraticCoefficient,criticalValue,iterate_succ_apply']
  | succ n ih =>
    rw [quadraticCoefficient,ih,Finset.prod_range_succ,pow_succ]
    ring

theorem shooting_coefficient_product {c d : ℝ} {n : ℕ}
    (hc : c ∈ Icc (-2 : ℝ) (-49/25)) (hd : d ∈ Icc (0 : ℝ) 2)
    (hs : shooting n d c = 0) :
    -quadraticCoefficient c (n+1)*scale (n+2) =
      (-c)/8*∏ j ∈ Finset.range n, back c (j+1) d/2 := by
  have hprod : (∏ j ∈ Finset.range n, criticalValue c (j+2)/2) =
      ∏ j ∈ Finset.range n, back c (j+1) d/2 := by
    calc
      (∏ j ∈ Finset.range n, criticalValue c (j+2)/2) =
          ∏ j ∈ Finset.range n, back c (n-1-j+1) d/2 := by
            apply Finset.prod_congr rfl
            intro j hj
            have hjn : j < n := Finset.mem_range.mp hj
            rw [shooting_critical_itinerary hc hd hs j hjn.le]
            congr 2
            omega
      _ = _ := Finset.prod_range_reflect (fun j => back c (j+1) d/2) n
  rw [coefficient_product,hprod]
  simp only [scale,one_div_pow,pow_add]
  field_simp
  ring

theorem chart_coefficient_lower {p : ℕ} (hp : 17 ≤ p) {c d : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p))
    (hd : d ∈ Icc (0 : ℝ) (12*scale p))
    (hs : shooting (p-2) d c = 0) :
    (3/20 : ℝ) < -quadraticCoefficient c (p-1)*scale p := by
  have hq := scale_small hp
  have hpq := horizon_scale_small hp
  have hcsmall : c ∈ Icc (-2 : ℝ) (-2+1/10000) :=
    ⟨hc.1,by linarith [hc.2]⟩
  have hbudget : ((p-2 : ℕ) : ℝ)*(c+2) ≤ 1/10000 := by
    have hpn : ((p-2 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 2
    have hp0 : (0 : ℝ) ≤ p := by positivity
    have hmul := mul_le_mul_of_nonneg_left (show c+2 ≤ 20*scale p by linarith [hc.2]) hp0
    have hmul' := mul_le_mul_of_nonneg_right hpn (show 0 ≤ c+2 by linarith [hc.1])
    nlinarith only [hmul,hmul',hpq]
  have hprod := NearTwoInverse.normalized_inverse_product_lower (p-2)
    (by omega) hcsmall (terminal_band hp hd) hbudget
  have he := shooting_coefficient_product (parameter_band hp hc) (terminal_band hp hd) hs
  have he' : -quadraticCoefficient c (p-1)*scale p =
      (-c)/8*∏ j ∈ Finset.range (p-2), back c (j+1) d/2 := by
    simpa only [show p-2+1 = p-1 by omega, show p-2+2 = p by omega] using he
  rw [he']
  have hcoef : (19999/80000 : ℝ) ≤ -c/8 := by linarith [hcsmall.2]
  have hmul := mul_le_mul hcoef hprod (by norm_num : (0 : ℝ) ≤ 241/400)
    (by linarith [hcsmall.2] : 0 ≤ -c/8)
  linarith only [hmul]

theorem continuous_criticalValue (n : ℕ) : Continuous (fun c => criticalValue c n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    simp only [criticalValue_step]
    exact (ih.pow 2).add continuous_id

theorem continuous_quadraticCoefficient (n : ℕ) :
    Continuous (fun c => quadraticCoefficient c n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    simp only [quadraticCoefficient]
    exact (continuous_const.mul (continuous_criticalValue (n+1))).mul ih

def kappa (p : ℕ) (c : ℝ) : ℝ :=
  -quadraticCoefficient c (p-1)*criticalValue c p

theorem continuous_kappa (p : ℕ) : Continuous (kappa p) :=
  (continuous_quadraticCoefficient (p-1)).neg.mul (continuous_criticalValue p)

structure SharpChart (p : ℕ) (a b : ℝ) : Prop where
  ordered : a < b
  left_coefficient : kappa p a = 17904/10000
  right_coefficient : kappa p b = 17903/10000
  parameter_range : ∀ c ∈ Icc a b, c ∈ Icc (-2 : ℝ) (-2+20*scale p)
  return_range : ∀ c ∈ Icc a b, 0 < criticalValue c p ∧ criticalValue c p ≤ 12*scale p
  coefficient_range : MapsTo (kappa p) (Icc a b) (Icc (17903/10000) (17904/10000))
  itinerary : ∀ c ∈ Icc a b, shooting (p-2) (criticalValue c p) c = 0

/-- Every sufficiently large period has a full real parameter corridor
crossing both sharp normalized-coefficient walls. The return scale and
the coefficient estimates are conclusions of the construction. -/
theorem exists_sharp_chart (p : ℕ) (hp : 17 ≤ p) : ∃ a b, SharpChart p a b := by
  obtain ⟨u,v,h⟩ := exists_real_chart p hp
  have hu : u ∈ Icc u v := left_mem_Icc.mpr h.ordered.le
  have hv : v ∈ Icc u v := right_mem_Icc.mpr h.ordered.le
  have hlow := chart_coefficient_lower hp h.left_band (h.return_range u hu) (h.itinerary u hu)
  have hleft : (17904/10000 : ℝ) ≤ kappa p u := by
    unfold kappa
    rw [h.left_return]
    nlinarith only [hlow]
  have hright : kappa p v ≤ (17903/10000 : ℝ) := by
    unfold kappa
    rw [h.right_return]
    norm_num
  obtain ⟨a,b,hua,hab,hbv,ha,hb,hmap⟩ :=
    LoopsParabolic.exists_descending_crossing_Icc h.ordered.le
      (continuous_kappa p).continuousOn hleft (by norm_num :
        (17903/10000 : ℝ) < 17904/10000) hright
  have sub {c : ℝ} (hc : c ∈ Icc a b) : c ∈ Icc u v :=
    ⟨hua.trans hc.1,hc.2.trans hbv⟩
  refine ⟨a,b,hab,ha,hb,?_,?_,hmap,?_⟩
  · intro c hc
    exact ⟨h.left_band.1.trans (sub hc).1,(sub hc).2.trans h.right_band.2⟩
  · intro c hc
    have hret := h.return_range c (sub hc)
    refine ⟨?_,hret.2⟩
    apply lt_of_le_of_ne hret.1
    intro he
    have hzero : kappa p c = 0 := by unfold kappa; rw [← he]; ring
    have hk := (hmap hc).1
    rw [hzero] at hk
    norm_num at hk
  · intro c hc
    exact h.itinerary c (sub hc)

theorem SharpChart.critical_orbit_bound {p : ℕ} (hp : 17 ≤ p) {a b : ℝ}
    (h : SharpChart p a b) {c : ℝ} (hc : c ∈ Icc a b) :
    ∀ j ≤ p, |criticalValue c j| ≤ 2 := by
  have hpar := h.parameter_range c hc
  have hband := parameter_band hp hpar
  have hret := h.return_range c hc
  have hd := terminal_band hp (show criticalValue c p ∈ Icc (0 : ℝ) (12*scale p) from
    ⟨hret.1.le,hret.2⟩)
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    norm_num [criticalValue]
  by_cases hj1 : j = 1
  · subst j
    have hval : criticalValue c 1 = c := by simp [criticalValue]
    rw [hval,abs_of_nonpos (by linarith [hband.2])]
    linarith [hpar.1]
  have hj2 : 2 ≤ j := by omega
  have hs := shooting_critical_itinerary hband hd (h.itinerary c hc) (j-2) (by omega)
  rw [Nat.sub_add_cancel hj2] at hs
  rw [hs]
  have hb := back_bounds hband hd ((p-2)-(j-2))
  rw [abs_of_nonneg hb.1]
  exact hb.2

end
end NearTwoShooting
