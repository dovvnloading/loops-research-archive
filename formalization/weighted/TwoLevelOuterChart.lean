import NearTwoShooting
import QuadraticCrestDividedDifference

/-!
# Literal monic outer return charts reaching the quadratic endpoint

The terminal shooting window is enlarged to fourteen times the first-return
scale. This gives a continuous parameter chart through the entire near-minus-two
monic parameter interval. The maps are affine normalizations of literal
quadratic iterates, and their error is estimated on a fixed complex disk.
-/

namespace TwoLevelOuterChart

open Set Function
open NearTwoInverse NearTwoShooting LimitingCrestQuadraticReturn
open scoped BigOperators

noncomputable section

def returnCoefficient (p : ℕ) (c : ℝ) : ℝ := quadraticCoefficient c (p-1)

def monicParameter (p : ℕ) (c : ℝ) : ℝ :=
  returnCoefficient p c * criticalValue c p

def outerMap (c : ℝ) (p : ℕ) (z : ℂ) : ℂ :=
  (returnCoefficient p c : ℂ) *
    ((quadraticMap c)^[p]) (z/(returnCoefficient p c : ℂ))

private theorem terminal_band_fourteen {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) : d ∈ Icc (0 : ℝ) 2 := by
  refine ⟨hd.1, ?_⟩
  have hq := scale_small hp
  linarith [hd.2]

private theorem chebyshev_back_lt_two {d : ℝ} (hd : d < 2) (n : ℕ) :
    back (-2) n d < 2 := by
  induction n with
  | zero => exact hd
  | succ n ih =>
    rw [back_succ, B]
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).mpr (by nlinarith)

private theorem shooting_left_positive {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) :
    0 < shooting (p-2) d (-2) := by
  have hq := scale_small hp
  have h := chebyshev_back_lt_two (show d < 2 by linarith [hd.2]) (p-2)
  dsimp [shooting]
  linarith

private theorem shooting_right_negative {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) :
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
  nlinarith only [hcheb, hdiff, hmon, hsq, hq0]

private theorem unique_shooting_fourteen {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) :
    ∃! c : ℝ, c ∈ Icc (-2 : ℝ) (-2+20*scale p) ∧
      shooting (p-2) d c = 0 := by
  have hab : (-2 : ℝ) ≤ -2+20*scale p := by linarith [scale_pos p]
  obtain ⟨c, hc, hz⟩ := intermediate_value_Icc' hab
    (continuous_shooting (p-2) d).continuousOn
    (show (0 : ℝ) ∈ Icc (shooting (p-2) d (-2+20*scale p))
      (shooting (p-2) d (-2)) from
      ⟨(shooting_right_negative hp hd).le, (shooting_left_positive hp hd).le⟩)
  refine ⟨c, ⟨hc, hz⟩, ?_⟩
  intro x hx
  exact (shooting_strictAnti (p-2) (terminal_band_fourteen hp hd)).injOn
    (parameter_band hp hx.1) (parameter_band hp hc) (hx.2.trans hz.symm)

private theorem back_strictMono_initial {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-49/25)) (n : ℕ) :
    StrictMonoOn (back c n) (Icc (0 : ℝ) 2) := by
  induction n with
  | zero => intro x hx y hy hxy; exact hxy
  | succ n ih =>
    intro x hx y hy hxy
    rw [back_succ, back_succ]
    unfold B
    exact Real.sqrt_lt_sqrt
      (by linarith [(back_bounds hc hx n).1, hc.2])
      (sub_lt_sub_right (ih hx hy hxy) c)

private structure RawChart (p : ℕ) (a b : ℝ) : Prop where
  left_band : a ∈ Icc (-2 : ℝ) (-2+20*scale p)
  right_band : b ∈ Icc (-2 : ℝ) (-2+20*scale p)
  ordered : a < b
  left_return : criticalValue a p = 14*scale p
  right_return : criticalValue b p = 0
  return_range : ∀ c ∈ Icc a b, criticalValue c p ∈ Icc (0 : ℝ) (14*scale p)
  itinerary : ∀ c ∈ Icc a b, shooting (p-2) (criticalValue c p) c = 0

private theorem exists_raw_chart (p : ℕ) (hp : 17 ≤ p) : ∃ a b, RawChart p a b := by
  have hscale := scale_pos p
  have hD : (14*scale p : ℝ) ∈ Icc (0 : ℝ) (14*scale p) := ⟨by positivity, le_rfl⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (14*scale p) := ⟨le_rfl, by positivity⟩
  obtain ⟨a, ⟨ha, ha0⟩, _⟩ := unique_shooting_fourteen hp hD
  obtain ⟨b, ⟨hb, hb0⟩, _⟩ := unique_shooting_fourteen hp h0
  have ha' := parameter_band hp ha
  have hb' := parameter_band hp hb
  have hapos : 0 < shooting (p-2) 0 a := by
    have hs := back_strictMono_initial ha' (p-2)
      (terminal_band_fourteen hp h0) (terminal_band_fourteen hp hD)
      (show (0 : ℝ) < 14*scale p by positivity)
    dsimp [shooting] at ha0 ⊢
    linarith only [hs, ha0]
  have hab : a < b := by
    by_contra! h
    have hs := (shooting_strictAnti (p-2) (terminal_band_fourteen hp h0)).antitoneOn hb' ha' h
    linarith only [hs, hb0, hapos]
  have sub {c : ℝ} (hc : c ∈ Icc a b) : c ∈ Icc (-2 : ℝ) (-2+20*scale p) :=
    ⟨ha.1.trans hc.1, hc.2.trans hb.2⟩
  have hsand {c : ℝ} (hc : c ∈ Icc a b) :
      ∀ j ≤ p-2, criticalValue c (j+2) ∈
        Icc (back c ((p-2)-j) 0) (back c ((p-2)-j) (14*scale p)) := by
    have hc' := parameter_band hp (sub hc)
    have hlo := (shooting_strictAnti (p-2) (terminal_band_fourteen hp h0)).antitoneOn hc' hb' hc.2
    have hup := (shooting_strictAnti (p-2) (terminal_band_fourteen hp hD)).antitoneOn ha' hc' hc.1
    apply shooting_sandwich hc' (terminal_band_fourteen hp hD)
    · dsimp [shooting] at hlo hb0
      linarith only [hlo, hb0]
    · dsimp [shooting] at hup ha0
      linarith only [hup, ha0]
  have hp2 : p-2+2 = p := by omega
  refine ⟨a, b, ha, hb, hab, ?_, ?_, ?_, ?_⟩
  · simpa only [hp2] using shooting_terminal_value ha' (terminal_band_fourteen hp hD) ha0
  · simpa only [hp2] using shooting_terminal_value hb' (terminal_band_fourteen hp h0) hb0
  · intro c hc
    simpa only [hp2, Nat.sub_self, back_zero] using hsand hc (p-2) le_rfl
  · intro c hc
    have h := forward_orbit_shooting (n := p-2) (c := c) (by
      intro j hj
      exact (back_bounds (parameter_band hp (sub hc))
        (terminal_band_fourteen hp h0) ((p-2)-j)).1.trans (hsand hc j hj).1)
    simpa only [hp2] using h

private theorem coefficient_lower_fourteen {p : ℕ} (hp : 17 ≤ p) {c d : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p))
    (hd : d ∈ Icc (0 : ℝ) (14*scale p))
    (hs : shooting (p-2) d c = 0) :
    (3/20 : ℝ) < -returnCoefficient p c*scale p := by
  have hq := scale_small hp
  have hpq := horizon_scale_small hp
  have hcsmall : c ∈ Icc (-2 : ℝ) (-2+1/10000) :=
    ⟨hc.1, by linarith [hc.2]⟩
  have hbudget : ((p-2 : ℕ) : ℝ)*(c+2) ≤ 1/10000 := by
    have hpn : ((p-2 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 2
    have hmul := mul_le_mul_of_nonneg_left
      (show c+2 ≤ 20*scale p by linarith [hc.2]) (show (0 : ℝ) ≤ p by positivity)
    have hmul' := mul_le_mul_of_nonneg_right hpn (show 0 ≤ c+2 by linarith [hc.1])
    nlinarith only [hmul, hmul', hpq]
  have hprod := NearTwoInverse.normalized_inverse_product_lower (p-2)
    (by omega) hcsmall (terminal_band_fourteen hp hd) hbudget
  have he := shooting_coefficient_product (parameter_band hp hc) (terminal_band_fourteen hp hd) hs
  have he' : -returnCoefficient p c*scale p =
      (-c)/8*∏ j ∈ Finset.range (p-2), back c (j+1) d/2 := by
    simpa only [returnCoefficient, show p-2+1 = p-1 by omega,
      show p-2+2 = p by omega] using he
  rw [he']
  have hcoef : (19999/80000 : ℝ) ≤ -c/8 := by linarith [hcsmall.2]
  have hmul := mul_le_mul hcoef hprod (by norm_num : (0 : ℝ) ≤ 241/400)
    (by linarith [hcsmall.2] : 0 ≤ -c/8)
  linarith only [hmul]

private theorem chart_orbit_bound {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p))
    (hd : criticalValue c p ∈ Icc (0 : ℝ) (14*scale p))
    (hs : shooting (p-2) (criticalValue c p) c = 0) :
    ∀ j ≤ p, |criticalValue c j| ≤ 2 := by
  have hband := parameter_band hp hc
  have hd' := terminal_band_fourteen hp hd
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    norm_num [criticalValue]
  by_cases hj1 : j = 1
  · subst j
    have hval : criticalValue c 1 = c := by simp [criticalValue]
    rw [hval, abs_of_nonpos (by linarith [hband.2])]
    linarith [hc.1]
  have hj2 : 2 ≤ j := by omega
  have he := shooting_critical_itinerary hband hd' hs (j-2) (by omega)
  rw [Nat.sub_add_cancel hj2] at he
  rw [he]
  have hb := back_bounds hband hd' ((p-2)-(j-2))
  rw [abs_of_nonneg hb.1]
  exact hb.2

/-- A literal quadratic parameter interval covering a prescribed interval of
monic return parameters, together with pointwise orbit and coefficient data. -/
structure OuterChart (p : ℕ) (a b l r : ℝ) : Prop where
  ordered : l < r
  left_monicParameter : monicParameter p l = a
  right_monicParameter : monicParameter p r = b
  parameter_range : ∀ c ∈ Icc l r, c ∈ Icc (-2 : ℝ) (-2+20*scale p)
  return_range : ∀ c ∈ Icc l r, 0 < criticalValue c p ∧ criticalValue c p ≤ 14*scale p
  coefficient_lower : ∀ c ∈ Icc l r, (3/20 : ℝ) < -returnCoefficient p c*scale p
  monic_range : MapsTo (monicParameter p) (Icc l r) (Icc a b)
  critical_orbit : ∀ c ∈ Icc l r, ∀ j ≤ p, |criticalValue c j| ≤ 2
  itinerary : ∀ c ∈ Icc l r, shooting (p-2) (criticalValue c p) c = 0

/-- The enlarged shooting window reaches every subinterval of the whole
near-minus-two monic parameter band, for every sufficiently large outer period. -/
theorem exists_outer_chart (p : ℕ) (hp : 17 ≤ p) (a b : ℝ)
    (ha : -2 ≤ a) (hab : a < b) (hb : b ≤ -49/25) :
    ∃ l r : ℝ, OuterChart p a b l r := by
  obtain ⟨u, v, h⟩ := exists_raw_chart p hp
  have hu : u ∈ Icc u v := left_mem_Icc.mpr h.ordered.le
  have hv : v ∈ Icc u v := right_mem_Icc.mpr h.ordered.le
  have hlow := coefficient_lower_fourteen hp h.left_band (h.return_range u hu) (h.itinerary u hu)
  have hleft : -a ≤ kappa p u := by
    unfold kappa
    rw [h.left_return]
    change (3/20 : ℝ) < -quadraticCoefficient u (p-1)*scale p at hlow
    nlinarith only [hlow, ha]
  have hright : kappa p v ≤ -b := by
    unfold kappa
    rw [h.right_return]
    linarith only [hb]
  obtain ⟨l, r, hul, hlr, hrv, hl, hr, hmap⟩ :=
    LoopsParabolic.exists_descending_crossing_Icc h.ordered.le
      (continuous_kappa p).continuousOn hleft (by linarith : -b < -a) hright
  have sub {c : ℝ} (hc : c ∈ Icc l r) : c ∈ Icc u v :=
    ⟨hul.trans hc.1, hc.2.trans hrv⟩
  have band {c : ℝ} (hc : c ∈ Icc l r) : c ∈ Icc (-2 : ℝ) (-2+20*scale p) :=
    ⟨h.left_band.1.trans (sub hc).1, (sub hc).2.trans h.right_band.2⟩
  have hidentity (c : ℝ) : monicParameter p c = -kappa p c := by
    simp only [monicParameter, returnCoefficient, kappa]
    ring
  refine ⟨l, r, hlr, ?_, ?_, fun c hc => band hc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hidentity, hl]
    ring
  · rw [hidentity, hr]
    ring
  · intro c hc
    have hret := h.return_range c (sub hc)
    refine ⟨?_, hret.2⟩
    have hk := (hmap hc).1
    by_contra! hn
    have hz : criticalValue c p = 0 := le_antisymm hn hret.1
    have hzero : kappa p c = 0 := by unfold kappa; rw [hz]; ring
    rw [hzero] at hk
    linarith only [hk, hb]
  · intro c hc
    exact coefficient_lower_fourteen hp (band hc) (h.return_range c (sub hc)) (h.itinerary c (sub hc))
  · intro c hc
    rw [hidentity]
    have hm := hmap hc
    constructor <;> linarith [hm.1, hm.2]
  · intro c hc
    exact chart_orbit_bound hp (band hc) (h.return_range c (sub hc)) (h.itinerary c (sub hc))
  · intro c hc
    exact h.itinerary c (sub hc)

theorem continuous_monicParameter (p : ℕ) : Continuous (monicParameter p) := by
  exact (continuous_quadraticCoefficient (p-1)).mul (continuous_criticalValue p)

theorem coefficient_negative {p : ℕ} {c : ℝ}
    (hlower : (3/20 : ℝ) < -returnCoefficient p c*scale p) :
    returnCoefficient p c < 0 := by
  have hq := scale_pos p
  by_contra! hn
  have hm := mul_nonneg hn hq.le
  nlinarith only [hlower, hm]

private theorem coefficient_bound (c : ℝ) (n : ℕ) :
    (∀ j : ℕ, j ≤ n+1 → |criticalValue c j| ≤ 2) →
      |quadraticCoefficient c n| ≤ (4 : ℝ)^n := by
  induction n with
  | zero => intro h; norm_num [quadraticCoefficient]
  | succ n ih =>
    intro h
    have ha := ih (fun j hj => h j (by omega))
    have hd := h (n+1) (by omega)
    calc
      |quadraticCoefficient c (n+1)| =
          (2*|criticalValue c (n+1)|)*|quadraticCoefficient c n| := by
            norm_num [quadraticCoefficient, abs_mul]
      _ ≤ 4*(4 : ℝ)^n :=
        mul_le_mul (by linarith) ha (abs_nonneg _) (by norm_num)
      _ = (4 : ℝ)^(n+1) := by rw [pow_succ]; ring

private theorem power_mul_scale (p : ℕ) : (4 : ℝ)^p*scale p = 1 := by
  simp [scale, one_div_pow]

/-- The exact affine normalization of the original p-th iterate is uniformly
close to its monic quadratic on the disk of radius twelve fifths. -/
theorem outerMap_error {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hcrit : ∀ j ≤ p, |criticalValue c j| ≤ 2)
    (hlower : (3/20 : ℝ) < -returnCoefficient p c*scale p)
    (z : ℂ) (hz : ‖z‖ ≤ 12/5) :
    ‖outerMap c p z - (z^2+(monicParameter p c : ℂ))‖ ≤ 128*scale p := by
  let q : ℝ := scale p
  let A : ℝ := returnCoefficient p c
  have hq : 0 < q := scale_pos p
  have hqsmall : q ≤ 1/17179869184 := scale_small hp
  have hAneg : A < 0 := coefficient_negative hlower
  have hAabs : |A| = -A := abs_of_neg hAneg
  have hApos : 0 < |A| := abs_pos.mpr hAneg.ne
  have hAne : (A : ℂ) ≠ 0 := by exact_mod_cast hAneg.ne
  have hp1 : p-1+1 = p := by omega
  have hscale : (4 : ℝ)^p*q = 1 := power_mul_scale p
  have hpow : (4 : ℝ)^(p-1)*q = 1/4 := by
    have he := pow_succ (4 : ℝ) (p-1)
    rw [hp1] at he
    rw [he] at hscale
    nlinarith only [hscale]
  have hAbound : |A| *q ≤ 1/4 := by
    have hb := coefficient_bound c (p-1) (fun j hj => hcrit j (by omega))
    have hm := mul_le_mul_of_nonneg_right hb hq.le
    change |A| *q ≤ _ at hm
    linarith only [hm, hpow]
  have hlower' : (3/20 : ℝ) < |A| *q := by
    rw [hAabs]
    exact hlower
  have hzin : ‖z/(A : ℂ)‖ ≤ 16*q := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_iff₀ hApos).mpr
    nlinarith only [hlower', hz]
  have hsmall : (4 : ℝ)^p*(16*q)^2 ≤ 1 := by
    have hid : (4 : ℝ)^p*(16*q)^2 = 256*q := by
      calc
        _ = 256*((4 : ℝ)^p*q)*q := by ring
        _ = 256*q := by rw [hscale]; ring
    rw [hid]
    linarith only [hqsmall]
  have hR := complete_remainder_bound c (p-1) (16*q) (z/(A : ℂ))
    (by positivity) (fun j hj => hcrit j (by omega))
    (by simpa only [hp1] using hsmall) hzin
  have hRbound : ‖quadraticRemainder c (p-1) (z/(A : ℂ))‖ ≤ 512*q^2 := by
    rw [hp1] at hR
    have hid : ((4 : ℝ)^p*(16*q)^2)^2/128 = 512*q^2 := by
      have he : (4 : ℝ)^p*(16*q)^2 = 256*q := by
        calc
          _ = 256*((4 : ℝ)^p*q)*q := by ring
          _ = 256*q := by rw [hscale]; ring
      rw [he]
      ring
    simpa only [hid] using hR
  have hid : outerMap c p z-(z^2+(monicParameter p c : ℂ)) =
      (A : ℂ)*quadraticRemainder c (p-1) (z/(A : ℂ)) := by
    unfold outerMap monicParameter quadraticRemainder
    rw [hp1]
    change (A : ℂ)*((quadraticMap c)^[p]) (z/(A : ℂ)) -
      (z^2+((A*criticalValue c p : ℝ) : ℂ)) =
      (A : ℂ)*(((quadraticMap c)^[p]) (z/(A : ℂ))-
        (criticalValue c p : ℂ)-(A : ℂ)*(z/(A : ℂ))^2)
    push_cast
    field_simp [hAne]
    ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |A| *‖quadraticRemainder c (p-1) (z/(A : ℂ))‖ ≤ |A| *(512*q^2) :=
      mul_le_mul_of_nonneg_left hRbound (abs_nonneg A)
    _ = 512*(|A| *q)*q := by ring
    _ ≤ 512*(1/4)*q := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAbound (by norm_num)) hq.le
    _ = 128*scale p := by dsimp [q]; ring

theorem OuterChart.outerMap_error {p : ℕ} (hp : 17 ≤ p) {a b l r : ℝ}
    (h : OuterChart p a b l r) {c : ℝ} (hc : c ∈ Icc l r)
    (z : ℂ) (hz : ‖z‖ ≤ 12/5) :
    ‖outerMap c p z-(z^2+(monicParameter p c : ℂ))‖ ≤ 128*scale p :=
  TwoLevelOuterChart.outerMap_error hp (h.critical_orbit c hc) (h.coefficient_lower c hc) z hz

private theorem outer_input_bound {p : ℕ} {c : ℝ}
    (hlower : (3/20 : ℝ) < -returnCoefficient p c*scale p)
    {z : ℂ} (hz : ‖z‖ ≤ 12/5) :
    ‖z/(returnCoefficient p c : ℂ)‖ ≤ 16*scale p := by
  have hA := coefficient_negative hlower
  have hApos : 0 < |returnCoefficient p c| := abs_pos.mpr hA.ne
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
  apply (div_le_iff₀ hApos).mpr
  rw [abs_of_neg hA]
  nlinarith only [hlower, hz]

private theorem outer_secant_nonzero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hcrit : ∀ j ≤ p, |criticalValue c j| ≤ 2)
    (hlower : (3/20 : ℝ) < -returnCoefficient p c*scale p)
    {z w : ℂ} (hz : ‖z‖ ≤ 12/5) (hw : ‖w‖ ≤ 12/5) :
    QuadraticCrestDividedDifference.evenSecant c (p-1)
      (z/(returnCoefficient p c : ℂ)) (w/(returnCoefficient p c : ℂ)) ≠ 0 := by
  let q := scale p
  have hq : 0 < q := scale_pos p
  have hqs : q ≤ 1/17179869184 := scale_small hp
  have hp1 : p-1+1 = p := by omega
  have hscale : (4 : ℝ)^p*q = 1 := power_mul_scale p
  have hpow : (4 : ℝ)^(p-1)*q = 1/4 := by
    have he := pow_succ (4 : ℝ) (p-1)
    rw [hp1] at he
    rw [he] at hscale
    nlinarith only [hscale]
  have hsmall : (4 : ℝ)^(p-1+1)*(16*q)^2 ≤ 1 := by
    rw [hp1]
    calc
      _ = 256*((4 : ℝ)^p*q)*q := by ring
      _ = 256*q := by rw [hscale]; ring
      _ ≤ 1 := by linarith only [hqs]
  have hE := QuadraticCrestDividedDifference.evenSecant_error c (p-1)
    (16*q) (z/(returnCoefficient p c : ℂ)) (w/(returnCoefficient p c : ℂ))
    (by positivity) (fun j hj => hcrit j (by omega)) hsmall
    (outer_input_bound hlower hz) (outer_input_bound hlower hw)
  have hright : (4 : ℝ)^(p-1)*((4 : ℝ)^(p-1+1)*(16*q)^2)/16 = 4 := by
    rw [hp1]
    calc
      _ = 16*((4 : ℝ)^(p-1)*q)*((4 : ℝ)^p*q) := by ring
      _ = 4 := by rw [hpow, hscale]; norm_num
  rw [hright] at hE
  intro hzero
  rw [hzero, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hE
  have hA := coefficient_negative hlower
  change |returnCoefficient p c| ≤ 4 at hE
  rw [abs_of_neg hA] at hE
  have hm := mul_le_mul_of_nonneg_right hE hq.le
  change -returnCoefficient p c*q ≤ 4*q at hm
  nlinarith only [hlower, hm, hqs]

/-- On the entire fixed disk the literal p-return has exactly its two even
collision branches. This controls all points of the disk, not sampled arcs. -/
theorem outerMap_collision_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hcrit : ∀ j ≤ p, |criticalValue c j| ≤ 2)
    (hlower : (3/20 : ℝ) < -returnCoefficient p c*scale p)
    {z w : ℂ} (hz : ‖z‖ ≤ 12/5) (hw : ‖w‖ ≤ 12/5) :
    outerMap c p z = outerMap c p w ↔ z = w ∨ z = -w := by
  let A : ℂ := (returnCoefficient p c : ℂ)
  have hA : A ≠ 0 := by
    dsimp [A]
    exact_mod_cast (coefficient_negative hlower).ne
  have hp1 : p-1+1 = p := by omega
  have hid := QuadraticCrestDividedDifference.iterate_difference c (p-1) (z/A) (w/A)
  rw [hp1] at hid
  have hsec := outer_secant_nonzero hp hcrit hlower hz hw
  constructor
  · intro h
    change A*((quadraticMap c)^[p]) (z/A) = A*((quadraticMap c)^[p]) (w/A) at h
    have hf := mul_left_cancel₀ hA h
    have hzero : ((z/A)^2-(w/A)^2)*
        QuadraticCrestDividedDifference.evenSecant c (p-1) (z/A) (w/A) = 0 := by
      rw [← hid, hf, sub_self]
    have hs := (mul_eq_zero.mp hzero).resolve_right hsec
    have hsquare : (z/A)^2 = (w/A)^2 := sub_eq_zero.mp hs
    have heq : z^2 = w^2 := by
      field_simp [hA] at hsquare
      exact hsquare
    exact sq_eq_sq_iff_eq_or_eq_neg.mp heq
  · intro h
    have hsquare : z^2 = w^2 := sq_eq_sq_iff_eq_or_eq_neg.mpr h
    have hscaled : (z/A)^2-(w/A)^2 = 0 := by rw [div_pow, div_pow, hsquare, sub_self]
    rw [hscaled, zero_mul] at hid
    have hf := sub_eq_zero.mp hid
    unfold outerMap
    exact congrArg (fun x : ℂ => A*x) hf

private theorem iterate_real (c t : ℝ) (n : ℕ) :
    ((quadraticMap c)^[n]) (t : ℂ) =
      (((fun x : ℝ => x^2+c)^[n]) t : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih]
    simp only [quadraticMap, Complex.ofReal_add, Complex.ofReal_pow]

theorem outerMap_real (c : ℝ) (p : ℕ) (t : ℝ) :
    (outerMap c p (t : ℂ)).im = 0 := by
  unfold outerMap
  rw [← Complex.ofReal_div, iterate_real, ← Complex.ofReal_mul]
  simp

theorem outerMap_zero (c : ℝ) (p : ℕ) :
    outerMap c p 0 = (monicParameter p c : ℂ) := by
  unfold outerMap monicParameter
  simpa only [zero_div, Complex.ofReal_zero, criticalValue, Complex.ofReal_mul] using
    congrArg (fun w : ℂ => (returnCoefficient p c : ℂ)*w) (iterate_real c 0 p)

theorem outerMap_imaginary (c : ℝ) (p : ℕ) (hp : 0 < p) (t : ℝ) :
    (outerMap c p ((t : ℂ)*Complex.I)).im = 0 := by
  have hp1 : p-1+1 = p := by omega
  let A := returnCoefficient p c
  have hinput : ((t : ℂ)*Complex.I)/(A : ℂ) = ((t/A : ℝ) : ℂ)*Complex.I := by
    push_cast
    ring
  have hfirst : quadraticMap c (((t/A : ℝ) : ℂ)*Complex.I) =
      ((c-(t/A)^2 : ℝ) : ℂ) := by
    unfold quadraticMap
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  unfold outerMap
  change ((A : ℂ)*((quadraticMap c)^[p]) (((t : ℂ)*Complex.I)/(A : ℂ))).im = 0
  rw [hinput, ← hp1, iterate_succ_apply, hfirst, iterate_real, ← Complex.ofReal_mul]
  simp

/-- Iterating the monic outer return is exactly an affine change of coordinates
in the original quadratic dynamics, with time multiplied by the outer period. -/
theorem outerMap_iterate (c : ℝ) (p n : ℕ)
    (hA : returnCoefficient p c ≠ 0) (z : ℂ) :
    ((outerMap c p)^[n]) z = (returnCoefficient p c : ℂ)*
      ((quadraticMap c)^[p*n]) (z/(returnCoefficient p c : ℂ)) := by
  have hAC : (returnCoefficient p c : ℂ) ≠ 0 := by exact_mod_cast hA
  induction n with
  | zero =>
    simp only [Nat.mul_zero, iterate_zero, id_eq]
    field_simp [hAC] <;> ring
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    unfold outerMap
    have hcancel (w : ℂ) :
        ((returnCoefficient p c : ℂ)*w)/(returnCoefficient p c : ℂ) = w := by
      field_simp [hAC] <;> ring
    rw [hcancel, ← iterate_add_apply]
    rw [Nat.mul_succ, Nat.add_comm (p*n) p]

theorem outerMap_continuous (c : ℝ) (p : ℕ) : Continuous (outerMap c p) := by
  have hf : Continuous (quadraticMap c) := by unfold quadraticMap; fun_prop
  exact ((hf.iterate p).comp (continuous_id.div_const _)).const_mul _

theorem outerMap_differentiable (c : ℝ) (p : ℕ) : Differentiable ℂ (outerMap c p) := by
  have hf : Differentiable ℂ (quadraticMap c) := by unfold quadraticMap; fun_prop
  exact ((hf.iterate p).comp (differentiable_id.div_const _)).const_mul _

private theorem iterate_continuous_parameter (p : ℕ) :
    Continuous (fun x : ℝ × ℂ => ((quadraticMap x.1)^[p]) x.2) := by
  induction p with
  | zero => exact continuous_snd
  | succ n ih =>
    simp only [iterate_succ_apply', quadraticMap]
    exact (ih.pow 2).add (Complex.continuous_ofReal.comp continuous_fst)

theorem OuterChart.outerMap_continuous_parameter {p : ℕ} {a b l r : ℝ}
    (h : OuterChart p a b l r) (z : ℂ) :
    ContinuousOn (fun c : ℝ => outerMap c p z) (Icc l r) := by
  have hA : Continuous (fun c : ℝ => (returnCoefficient p c : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_quadraticCoefficient (p-1))
  have hne : ∀ c ∈ Icc l r, (returnCoefficient p c : ℂ) ≠ 0 := by
    intro c hc
    exact_mod_cast (coefficient_negative (h.coefficient_lower c hc)).ne
  have hinput : ContinuousOn
      (fun c : ℝ => (c, z/(returnCoefficient p c : ℂ))) (Icc l r) :=
    continuous_id.continuousOn.prodMk (continuous_const.continuousOn.div hA.continuousOn hne)
  exact hA.continuousOn.mul ((iterate_continuous_parameter p).comp_continuousOn hinput)

theorem OuterChart.outer_iterate_continuous_parameter {p : ℕ} {a b l r : ℝ}
    (h : OuterChart p a b l r) (n : ℕ) (z : ℂ) :
    ContinuousOn (fun c : ℝ => ((outerMap c p)^[n]) z) (Icc l r) := by
  have hA : Continuous (fun c : ℝ => (returnCoefficient p c : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_quadraticCoefficient (p-1))
  have hne : ∀ c ∈ Icc l r, (returnCoefficient p c : ℂ) ≠ 0 := by
    intro c hc
    exact_mod_cast (coefficient_negative (h.coefficient_lower c hc)).ne
  have hsub (v : ℝ → ℂ) (hv : ContinuousOn v (Icc l r)) :
      ContinuousOn (fun c => outerMap c p (v c)) (Icc l r) := by
    have hi : ContinuousOn (fun c => (c, v c/(returnCoefficient p c : ℂ))) (Icc l r) :=
      continuous_id.continuousOn.prodMk (hv.div hA.continuousOn hne)
    exact hA.continuousOn.mul ((iterate_continuous_parameter p).comp_continuousOn hi)
  induction n with
  | zero => exact continuous_const.continuousOn
  | succ n ih =>
    simp only [iterate_succ_apply']
    exact hsub _ ih

end
end TwoLevelOuterChart
