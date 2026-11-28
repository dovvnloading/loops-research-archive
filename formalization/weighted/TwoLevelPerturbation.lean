import NearTwoShooting

/-!
# Quantitative composition estimates for a second physical return

The estimates in this file compare complete iterates on a complex disk.
The perturbed orbit bounds are conclusions, derived from the reference
orbit and the accumulated error budget.
-/

namespace TwoLevelPerturbation

open Set Function LimitingCrestQuadraticReturn NearTwoShooting

noncomputable section

theorem quadratic_disk_lipschitz (a : ℝ) {z w : ℂ}
    (hz : ‖z‖ ≤ 12/5) (hw : ‖w‖ ≤ 12/5) :
    ‖quadraticMap a z - quadraticMap a w‖ ≤ 5 * ‖z-w‖ := by
  have hid : quadraticMap a z - quadraticMap a w = (z-w)*(z+w) := by
    simp only [quadraticMap]
    ring
  rw [hid, norm_mul]
  have hsum : ‖z+w‖ ≤ 5 := by linarith [norm_add_le z w]
  nlinarith only [mul_le_mul_of_nonneg_left hsum (norm_nonneg (z-w))]

/-- The full perturbation sum, without a previously assumed perturbed
orbit bound. The margin between the two disks pays for accumulated error. -/
theorem iterate_stability_sum (H : ℂ → ℂ) (a : ℝ) (z : ℂ)
    (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbudget : ε * (5 : ℝ)^N ≤ 1/10)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 12/5 → ‖H w-quadraticMap a w‖ ≤ ε)
    (hmodel : ∀ n : ℕ, n ≤ N → ‖((quadraticMap a)^[n]) z‖ ≤ 21/10) :
    ∀ n : ℕ, n ≤ N →
      ‖(H^[n]) z-((quadraticMap a)^[n]) z‖ ≤
          (((5 : ℝ)^n-1)/4)*ε ∧
      ‖(H^[n]) z‖ ≤ 12/5 := by
  intro n
  induction n with
  | zero =>
    intro hn
    refine ⟨by simp, ?_⟩
    simpa using (hmodel 0 hn).trans (by norm_num : (21/10 : ℝ) ≤ 12/5)
  | succ n ih =>
    intro hn
    have hn' : n ≤ N := by omega
    obtain ⟨herr, hH⟩ := ih hn'
    have hQ : ‖((quadraticMap a)^[n]) z‖ ≤ 12/5 :=
      (hmodel n hn').trans (by norm_num)
    have hnext : ‖(H^[n+1]) z-((quadraticMap a)^[n+1]) z‖ ≤
        (((5 : ℝ)^(n+1)-1)/4)*ε := by
      rw [iterate_succ_apply', iterate_succ_apply']
      calc
        ‖H ((H^[n]) z)-quadraticMap a (((quadraticMap a)^[n]) z)‖ ≤
            ‖H ((H^[n]) z)-quadraticMap a ((H^[n]) z)‖ +
              ‖quadraticMap a ((H^[n]) z)-
                quadraticMap a (((quadraticMap a)^[n]) z)‖ := by
                  simpa only [dist_eq_norm] using dist_triangle
                    (H ((H^[n]) z)) (quadraticMap a ((H^[n]) z))
                    (quadraticMap a (((quadraticMap a)^[n]) z))
        _ ≤ ε+5*((((5 : ℝ)^n-1)/4)*ε) :=
          add_le_add (hclose _ hH)
            ((quadratic_disk_lipschitz a hH hQ).trans
              (mul_le_mul_of_nonneg_left herr (by norm_num)))
        _ = (((5 : ℝ)^(n+1)-1)/4)*ε := by rw [pow_succ]; ring
    refine ⟨hnext, ?_⟩
    have hpow : (5 : ℝ)^(n+1) ≤ (5 : ℝ)^N :=
      pow_le_pow_right₀ (by norm_num) hn
    have he : (((5 : ℝ)^(n+1)-1)/4)*ε ≤ 1/10 := by
      have hnonneg : 0 ≤ (5 : ℝ)^(n+1) := by positivity
      have hle : ((5 : ℝ)^(n+1)-1)/4 ≤ (5 : ℝ)^(n+1) := by linarith
      calc
        _ ≤ (5 : ℝ)^(n+1)*ε := mul_le_mul_of_nonneg_right hle hε
        _ ≤ (5 : ℝ)^N*ε := mul_le_mul_of_nonneg_right hpow hε
        _ ≤ 1/10 := by nlinarith only [hbudget]
    have ht := norm_le_norm_sub_add ((H^[n+1]) z)
      (((quadraticMap a)^[n+1]) z)
    linarith [hmodel (n+1) hn]

theorem iterate_stability (H : ℂ → ℂ) (a : ℝ) (z : ℂ)
    (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbudget : ε * (5 : ℝ)^N ≤ 1/10)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 12/5 → ‖H w-quadraticMap a w‖ ≤ ε)
    (hmodel : ∀ n : ℕ, n ≤ N → ‖((quadraticMap a)^[n]) z‖ ≤ 21/10)
    (n : ℕ) (hn : n ≤ N) :
    ‖(H^[n]) z-((quadraticMap a)^[n]) z‖ ≤ (5 : ℝ)^n*ε ∧
      ‖(H^[n]) z‖ ≤ 12/5 := by
  obtain ⟨he, hH⟩ := iterate_stability_sum H a z N ε hε hbudget hclose hmodel n hn
  refine ⟨he.trans ?_, hH⟩
  apply mul_le_mul_of_nonneg_right _ hε
  have h : 0 ≤ (5 : ℝ)^n := by positivity
  linarith

theorem critical_orbit_bound (a : ℝ) (ha : a ∈ Icc (-2 : ℝ) 0) (j : ℕ) :
    |criticalValue a j| ≤ 2 := by
  have hs (n : ℕ) : criticalValue a (n+1) = (criticalValue a n)^2+a := by
    simp only [criticalValue, iterate_succ_apply']
  have hi : ∀ n : ℕ, criticalValue a n ∈ Icc a (-a) := by
    intro n
    induction n with
    | zero =>
      change a ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ -a
      constructor <;> linarith [ha.2]
    | succ n ih =>
      have hsq : (criticalValue a n)^2 ≤ (-a)^2 :=
        sq_le_sq' (show -(-a) ≤ criticalValue a n by linarith [ih.1]) ih.2
      have hp : a*(a+2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ha.2 (by linarith [ha.1])
      rw [hs]
      constructor
      · nlinarith only [sq_nonneg (criticalValue a n)]
      · nlinarith only [hsq, hp]
  have hj := hi j
  rw [abs_le]
  constructor <;> linarith [ha.1, hj.1, hj.2]

theorem coefficient_bound (a : ℝ) (n : ℕ)
    (h : ∀ j : ℕ, j ≤ n+1 → |criticalValue a j| ≤ 2) :
    |quadraticCoefficient a n| ≤ (4 : ℝ)^n := by
  induction n with
  | zero => norm_num [quadraticCoefficient]
  | succ n ih =>
    have hA := ih (fun j hj => h j (by omega))
    have hd := h (n+1) (by omega)
    calc
      |quadraticCoefficient a (n+1)| =
          (2*|criticalValue a (n+1)|)*|quadraticCoefficient a n| := by
            norm_num [quadraticCoefficient, abs_mul]
      _ ≤ 4*(4 : ℝ)^n :=
        mul_le_mul (by linarith) hA (abs_nonneg _) (by norm_num)
      _ = (4 : ℝ)^(n+1) := by rw [pow_succ]; ring

theorem orbit_displacement (a : ℝ) (n : ℕ) (r : ℝ) (z : ℂ)
    (hr : 0 ≤ r)
    (hcrit : ∀ j : ℕ, j ≤ n+1 → |criticalValue a j| ≤ 2)
    (hscale : (4 : ℝ)^(n+1)*r^2 ≤ 1) (hz : ‖z‖ ≤ r) :
    ‖((quadraticMap a)^[n+1]) z-(criticalValue a (n+1) : ℂ)‖ ≤
      (4 : ℝ)^(n+1)*r^2/3 := by
  let T : ℝ := (4 : ℝ)^(n+1)*r^2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hT1 : T ≤ 1 := hscale
  have hE := complete_remainder_bound a n r z hr hcrit hscale hz
  have hA := coefficient_bound a n hcrit
  have hz2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hlead : ‖(quadraticCoefficient a n : ℂ)*z^2‖ ≤ T/4 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      |quadraticCoefficient a n| * ‖z‖^2 ≤ (4 : ℝ)^n*r^2 :=
        mul_le_mul hA hz2 (sq_nonneg _) (by positivity)
      _ = T/4 := by dsimp [T]; rw [pow_succ]; ring
  have hi : ((quadraticMap a)^[n+1]) z-(criticalValue a (n+1) : ℂ) =
      (quadraticCoefficient a n : ℂ)*z^2+quadraticRemainder a n z := by
    unfold quadraticRemainder
    ring
  rw [hi]
  have ht := norm_add_le ((quadraticCoefficient a n : ℂ)*z^2)
    (quadraticRemainder a n z)
  change ‖quadraticRemainder a n z‖ ≤ T^2/128 at hE
  change _ ≤ T/3
  nlinarith only [ht, hlead, hE, mul_le_mul_of_nonneg_left hT1 hT]

/-- Every intermediate image of a small complex input lies in the model
disk. The proof uses the complete polynomial remainder at every time. -/
theorem quadratic_orbit_disk (a : ℝ) (ha : a ∈ Icc (-2 : ℝ) 0)
    (N : ℕ) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 21/10)
    (hscale : (4 : ℝ)^N*r^2 ≤ 3/10) {z : ℂ} (hz : ‖z‖ ≤ r)
    (n : ℕ) (hn : n ≤ N) :
    ‖((quadraticMap a)^[n]) z‖ ≤ 21/10 := by
  cases n with
  | zero => simpa using hz.trans hrmax
  | succ n =>
    have hpow : (4 : ℝ)^(n+1) ≤ (4 : ℝ)^N :=
      pow_le_pow_right₀ (by norm_num) hn
    have ht : (4 : ℝ)^(n+1)*r^2 ≤ 3/10 :=
      (mul_le_mul_of_nonneg_right hpow (sq_nonneg r)).trans hscale
    have he := orbit_displacement a n r z hr
      (fun j _ => critical_orbit_bound a ha j) (by linarith) hz
    have hnorm : ‖(criticalValue a (n+1) : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact critical_orbit_bound a ha (n+1)
    have htri := norm_le_norm_sub_add (((quadraticMap a)^[n+1]) z)
      (criticalValue a (n+1) : ℂ)
    linarith

theorem scale_mul_power (q : ℕ) : scale q * (4 : ℝ)^q = 1 := by
  simp only [scale, ← mul_pow]
  norm_num

theorem reference_disk_orbit (a : ℝ) (ha : a ∈ Icc (-2 : ℝ) 0)
    (q : ℕ) (hq : 17 ≤ q) {z : ℂ} (hz : ‖z‖ ≤ 14*scale q)
    (n : ℕ) (hn : n ≤ q) :
    ‖((quadraticMap a)^[n]) z‖ ≤ 21/10 := by
  have hs := scale_small hq
  have hs0 := (scale_pos q).le
  apply quadratic_orbit_disk a ha q (14*scale q) (by positivity)
    (by linarith) _ hz n hn
  have hi : (4 : ℝ)^q*(14*scale q)^2 = 196*scale q := by
    calc
      _ = 196*scale q*(scale q*(4 : ℝ)^q) := by ring
      _ = _ := by rw [scale_mul_power]; ring
  rw [hi]
  linarith

/-- Two reference trajectories need only remain in the comparison disk;
no bound on a larger forward invariant set is used. -/
theorem quadratic_iterate_lipschitz (a : ℝ) (z w : ℂ) (N : ℕ)
    (hz : ∀ n : ℕ, n ≤ N → ‖((quadraticMap a)^[n]) z‖ ≤ 12/5)
    (hw : ∀ n : ℕ, n ≤ N → ‖((quadraticMap a)^[n]) w‖ ≤ 12/5)
    (n : ℕ) (hn : n ≤ N) :
    ‖((quadraticMap a)^[n]) z-((quadraticMap a)^[n]) w‖ ≤
      (5 : ℝ)^n*‖z-w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n ≤ N := by omega
    rw [iterate_succ_apply', iterate_succ_apply']
    calc
      _ ≤ 5*‖((quadraticMap a)^[n]) z-((quadraticMap a)^[n]) w‖ :=
        quadratic_disk_lipschitz a (hz n hn') (hw n hn')
      _ ≤ 5*((5 : ℝ)^n*‖z-w‖) :=
        mul_le_mul_of_nonneg_left (ih hn') (by norm_num)
      _ = (5 : ℝ)^(n+1)*‖z-w‖ := by rw [pow_succ]; ring

theorem complex_criticalValue (a : ℝ) (n : ℕ) :
    ((quadraticMap a)^[n]) 0 = (criticalValue a n : ℂ) := by
  induction n with
  | zero => simp [criticalValue]
  | succ n ih =>
    rw [iterate_succ_apply', ih, criticalValue_step]
    simp only [quadraticMap, Complex.ofReal_add, Complex.ofReal_pow]

theorem critical_iterate_stability (H : ℂ → ℂ) (a : ℝ)
    (ha : a ∈ Icc (-2 : ℝ) 0) (N : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbudget : ε*(5 : ℝ)^N ≤ 1/10)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 12/5 → ‖H w-quadraticMap a w‖ ≤ ε)
    (n : ℕ) (hn : n ≤ N) :
    ‖(H^[n]) 0-(criticalValue a n : ℂ)‖ ≤ (5 : ℝ)^n*ε := by
  rw [← complex_criticalValue]
  apply (iterate_stability H a 0 N ε hε hbudget hclose _ n hn).1
  intro j hj
  rw [complex_criticalValue, Complex.norm_real, Real.norm_eq_abs]
  exact (critical_orbit_bound a ha j).trans (by norm_num)

theorem critical_return_scale_error (H : ℂ → ℂ) (a : ℝ)
    (ha : a ∈ Icc (-2 : ℝ) 0) (q : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbudget : ε*(5 : ℝ)^q ≤ 1/10)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 12/5 → ‖H w-quadraticMap a w‖ ≤ ε) :
    |((H^[q]) 0).re-criticalValue a q| ≤ (5 : ℝ)^q*ε := by
  have he := critical_iterate_stability H a ha q ε hε hbudget hclose q le_rfl
  have hr := Complex.abs_re_le_norm ((H^[q]) 0-(criticalValue a q : ℂ))
  simpa only [Complex.sub_re, Complex.ofReal_re] using hr.trans he

/-- The signed sixth-plus-third collision test survives an arbitrary
length second return; the error is evaluated before normalization. -/
theorem signed_relation_stability (H : ℂ → ℂ) (a : ℝ)
    (ha : a ∈ Icc (-2 : ℝ) 0) (q : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbudget : ε*(5 : ℝ)^(6*q) ≤ 1/10)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 12/5 → ‖H w-quadraticMap a w‖ ≤ ε) :
    |((H^[6*q]) 0).re+((H^[3*q]) 0).re-
      (criticalValue a (6*q)+criticalValue a (3*q))| ≤
        2*ε*(5 : ℝ)^(6*q) := by
  have h6 := critical_iterate_stability H a ha (6*q) ε hε hbudget hclose (6*q) le_rfl
  have h3 := critical_iterate_stability H a ha (6*q) ε hε hbudget hclose (3*q) (by omega)
  have hr6 := (Complex.abs_re_le_norm
    ((H^[6*q]) 0-(criticalValue a (6*q) : ℂ))).trans h6
  have hr3 := (Complex.abs_re_le_norm
    ((H^[3*q]) 0-(criticalValue a (3*q) : ℂ))).trans h3
  simp only [Complex.sub_re, Complex.ofReal_re] at hr6 hr3
  have hp : (5 : ℝ)^(3*q) ≤ (5 : ℝ)^(6*q) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hm := mul_le_mul_of_nonneg_right hp hε
  have ht := abs_add_le (((H^[6*q]) 0).re-criticalValue a (6*q))
    (((H^[3*q]) 0).re-criticalValue a (3*q))
  have hi : ((H^[6*q]) 0).re+((H^[3*q]) 0).re-
      (criticalValue a (6*q)+criticalValue a (3*q)) =
        (((H^[6*q]) 0).re-criticalValue a (6*q))+
        (((H^[3*q]) 0).re-criticalValue a (3*q)) := by ring
  rw [hi]
  nlinarith only [hr6, hr3, hm, ht]

theorem reference_disk_displacement (a : ℝ) (ha : a ∈ Icc (-2 : ℝ) 0)
    (q : ℕ) (hq : 17 ≤ q) {z : ℂ} (hz : ‖z‖ ≤ 14*scale q)
    (n : ℕ) (hn0 : 0 < n) (hn : n ≤ q) :
    ‖((quadraticMap a)^[n]) z-(criticalValue a n : ℂ)‖ ≤
      196*scale q/3 := by
  cases n with
  | zero => omega
  | succ n =>
    have hs := scale_small hq
    have hp : (4 : ℝ)^(n+1) ≤ (4 : ℝ)^q :=
      pow_le_pow_right₀ (by norm_num) hn
    have he : (4 : ℝ)^q*(14*scale q)^2 = 196*scale q := by
      calc
        _ = 196*scale q*(scale q*(4 : ℝ)^q) := by ring
        _ = _ := by rw [scale_mul_power]; ring
    have hmul := mul_le_mul_of_nonneg_right hp (sq_nonneg (14*scale q))
    rw [he] at hmul
    have hscale : (4 : ℝ)^(n+1)*(14*scale q)^2 ≤ 1 := by linarith
    have hd := orbit_displacement a n (14*scale q) z (by positivity)
      (fun j _ => critical_orbit_bound a ha j) hscale hz
    linarith

/-- All noninitial phases stay near their corresponding reference
critical value. This supplies the strict half-plane separation used in
backward cancellation of the second-return fibers. -/
theorem perturbed_phase_displacement (H : ℂ → ℂ) (a : ℝ)
    (ha : a ∈ Icc (-2 : ℝ) 0) (q : ℕ) (hq : 17 ≤ q)
    (ε : ℝ) (hε : 0 ≤ ε) (hbudget : ε*(5 : ℝ)^q ≤ 1/10)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 12/5 → ‖H w-quadraticMap a w‖ ≤ ε)
    {z : ℂ} (hz : ‖z‖ ≤ 14*scale q) (n : ℕ) (hn0 : 0 < n) (hn : n ≤ q) :
    ‖(H^[n]) z-(criticalValue a n : ℂ)‖ ≤ 1/5 := by
  have hpert := (iterate_stability H a z q ε hε hbudget hclose
    (reference_disk_orbit a ha q hq hz) n hn).1
  have hmodel := reference_disk_displacement a ha q hq hz n hn0 hn
  have hp : (5 : ℝ)^n ≤ (5 : ℝ)^q := pow_le_pow_right₀ (by norm_num) hn
  have hm := mul_le_mul_of_nonneg_right hp hε
  have ht : ‖(H^[n]) z-(criticalValue a n : ℂ)‖ ≤
      ‖(H^[n]) z-((quadraticMap a)^[n]) z‖+
        ‖((quadraticMap a)^[n]) z-(criticalValue a n : ℂ)‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      ((H^[n]) z) (((quadraticMap a)^[n]) z) (criticalValue a n : ℂ)
  have hs := scale_small hq
  nlinarith only [hpert, hmodel, hm, ht, hs, hbudget]

/-- A linearly separated period wedge pays for the complete six-return
composition, even after division by the second return scale. -/
theorem separated_period_error (p q : ℕ) (hp : 10*q+30 ≤ p) :
    (128*scale p)*(5 : ℝ)^(6*q) ≤ scale q/100000000 := by
  have hp0 : 0 ≤ scale p := (scale_pos p).le
  have hs : scale p ≤ scale (10*q+30) :=
    pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) ≤ 1) hp
  have hpow : (5 : ℝ)^(6*q) ≤ (4 : ℝ)^(9*q) := by
    rw [pow_mul, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) q
  have he : scale (10*q+30)*(4 : ℝ)^(9*q) = scale q*scale 30 := by
    have hi : 10*q+30 = 9*q+(q+30) := by omega
    rw [hi]
    simp only [scale, pow_add]
    have hu : (1/4 : ℝ)^(9*q)*(4 : ℝ)^(9*q) = 1 := scale_mul_power (9*q)
    calc
      _ = ((1/4 : ℝ)^(9*q)*(4 : ℝ)^(9*q))*((1/4 : ℝ)^q*(1/4 : ℝ)^30) := by ring
      _ = _ := by rw [hu]; ring
  calc
    (128*scale p)*(5 : ℝ)^(6*q) ≤
        (128*scale (10*q+30))*(4 : ℝ)^(9*q) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) hpow
        (by positivity) (by positivity)
    _ = 128*(scale q*scale 30) := by rw [mul_assoc, he]
    _ ≤ scale q/100000000 := by
      have hc : 128*scale 30 ≤ (1/100000000 : ℝ) := by norm_num [scale]
      have hm := mul_le_mul_of_nonneg_left hc (scale_pos q).le
      nlinarith only [hm]

theorem return_scale_times_five (q : ℕ) {d : ℝ}
    (hd : 7*scale q ≤ d) : 1 ≤ d*(5 : ℝ)^q := by
  have hp : (1 : ℝ) ≤ (5/4 : ℝ)^q := one_le_pow₀ (by norm_num)
  have he : scale q*(5 : ℝ)^q = (5/4 : ℝ)^q := by
    simp only [scale, ← mul_pow]
    norm_num
  have hm := mul_le_mul_of_nonneg_right hd (show (0 : ℝ) ≤ 5^q by positivity)
  rw [mul_assoc, he] at hm
  linarith

/-- The change in the actual return scale is included. Both the input
rescaling and the output division are compared, on the complete disk. -/
theorem normalized_return_stability (H : ℂ → ℂ) (a : ℝ)
    (ha : a ∈ Icc (-2 : ℝ) 0) (q : ℕ) (hq : 17 ≤ q)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hclose : ∀ w : ℂ, ‖w‖ ≤ 12/5 → ‖H w-quadraticMap a w‖ ≤ ε)
    (hdlo : 7*scale q ≤ criticalValue a q)
    (hdhi : criticalValue a q ≤ 12*scale q)
    (D : ℝ) (hDdiff : |D-criticalValue a q| ≤ (5 : ℝ)^q*ε)
    (hbudget : ε*(5 : ℝ)^(2*q) ≤ criticalValue a q/100000000)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20) :
    ‖(H^[q]) ((D : ℂ)*z)/(D : ℂ)-normalizedReturn a q z‖ ≤
      1/10000000 := by
  let d := criticalValue a q
  let b : ℝ := (5 : ℝ)^q
  let E : ℝ := ε*b
  have hdpos : 0 < d := by
    dsimp [d]
    have hs := scale_pos q
    linarith
  have hb1 : 1 ≤ b := one_le_pow₀ (by norm_num)
  have hb0 : 0 ≤ b := by positivity
  have hE0 : 0 ≤ E := mul_nonneg hε hb0
  have hEb : E*b ≤ d/100000000 := by
    have he : (5 : ℝ)^(2*q) = b*b := by
      dsimp [b]
      rw [show 2*q = q+q by omega, pow_add]
    rw [he] at hbudget
    dsimp [E, d]
    nlinarith only [hbudget]
  have hEsmall : E ≤ d/100000000 := by
    have hm := mul_le_mul_of_nonneg_left hb1 hE0
    linarith
  have hdiff : |D-d| ≤ E := by
    dsimp [E, d, b]
    nlinarith only [hDdiff]
  have hDlower : 3*d/4 ≤ D := by
    have h := (abs_le.mp hdiff).1
    linarith
  have hDupper : D ≤ (1001/1000)*d := by
    have h := (abs_le.mp hdiff).2
    linarith
  have hDpos : 0 < D := by linarith
  have hdmax : d ≤ 12*scale q := hdhi
  have hDmax : D ≤ (12012/1000)*scale q := by linarith
  have hzD : ‖(D : ℂ)*z‖ ≤ 14*scale q := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDpos]
    calc
      D*‖z‖ ≤ D*(23/20) := mul_le_mul_of_nonneg_left hz hDpos.le
      _ ≤ 14*scale q := by linarith [scale_pos q]
  have hzd : ‖(d : ℂ)*z‖ ≤ 14*scale q := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdpos]
    calc
      d*‖z‖ ≤ d*(23/20) := mul_le_mul_of_nonneg_left hz hdpos.le
      _ ≤ 14*scale q := by linarith [scale_pos q]
  have hDmodel (n : ℕ) (hn : n ≤ q) :
      ‖((quadraticMap a)^[n]) ((D : ℂ)*z)‖ ≤ 21/10 :=
    reference_disk_orbit a ha q hq hzD n hn
  have hdmodel (n : ℕ) (hn : n ≤ q) :
      ‖((quadraticMap a)^[n]) ((d : ℂ)*z)‖ ≤ 21/10 :=
    reference_disk_orbit a ha q hq hzd n hn
  have hsmall : ε*(5 : ℝ)^q ≤ 1/10 := by
    change E ≤ 1/10
    have hs := scale_small hq
    linarith
  have hpert : ‖(H^[q]) ((D : ℂ)*z)-
      ((quadraticMap a)^[q]) ((D : ℂ)*z)‖ ≤ E := by
    have he := (iterate_stability H a ((D : ℂ)*z) q ε hε hsmall
      hclose hDmodel q le_rfl).1
    dsimp [E, b]
    nlinarith only [he]
  have hinput : ‖(D : ℂ)*z-(d : ℂ)*z‖ ≤ E*(23/20) := by
    rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hdiff hz (norm_nonneg z) hE0
  have hlip : ‖((quadraticMap a)^[q]) ((D : ℂ)*z)-
      ((quadraticMap a)^[q]) ((d : ℂ)*z)‖ ≤ b*(E*(23/20)) := by
    have he := quadratic_iterate_lipschitz a ((D : ℂ)*z) ((d : ℂ)*z) q
      (fun n hn => (hDmodel n hn).trans (by norm_num))
      (fun n hn => (hdmodel n hn).trans (by norm_num)) q le_rfl
    exact he.trans (mul_le_mul_of_nonneg_left hinput hb0)
  let A := (H^[q]) ((D : ℂ)*z)
  let B := ((quadraticMap a)^[q]) ((d : ℂ)*z)
  have hnum : ‖A-B‖ ≤ 3*d/100000000 := by
    have ht : ‖A-B‖ ≤ ‖(H^[q]) ((D : ℂ)*z)-
        ((quadraticMap a)^[q]) ((D : ℂ)*z)‖+
        ‖((quadraticMap a)^[q]) ((D : ℂ)*z)-
          ((quadraticMap a)^[q]) ((d : ℂ)*z)‖ := by
      simpa only [A, B, dist_eq_norm] using dist_triangle
        ((H^[q]) ((D : ℂ)*z)) (((quadraticMap a)^[q]) ((D : ℂ)*z))
        (((quadraticMap a)^[q]) ((d : ℂ)*z))
    have hm := mul_le_mul_of_nonneg_left hb1 hE0
    nlinarith only [ht, hpert, hlip, hEb, hm, hdpos]
  have hB : ‖B‖ ≤ 21/10 := hdmodel q le_rfl
  have hdb : 1 ≤ d*b := return_scale_times_five q hdlo
  have hEsq : E ≤ d^2/100000000 := by
    have hm := mul_le_mul_of_nonneg_right hEb hdpos.le
    have ht := mul_le_mul_of_nonneg_left hdb hE0
    nlinarith only [hm, ht]
  have hfirst : ‖A-B‖/D ≤ 4/100000000 := by
    apply (div_le_iff₀ hDpos).mpr
    linarith
  have hsecond : ‖B‖*|D-d|/(D*d) ≤ 3/100000000 := by
    apply (div_le_iff₀ (mul_pos hDpos hdpos)).mpr
    have hnorm : ‖B‖*|D-d| ≤ (21/10)*E :=
      mul_le_mul hB hdiff (abs_nonneg _) (by norm_num)
    have hden := mul_le_mul_of_nonneg_right hDlower hdpos.le
    nlinarith only [hnorm, hEsq, hden, sq_nonneg d]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hDC : (D : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hid : A/(D : ℂ)-B/(d : ℂ) =
      (A-B)/(D : ℂ)+B*((d : ℂ)-(D : ℂ))/((D : ℂ)*(d : ℂ)) := by
    field_simp [hdC, hDC]
    <;> ring
  change ‖A/(D : ℂ)-B/(d : ℂ)‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖(A-B)/(D : ℂ)‖+
        ‖B*((d : ℂ)-(D : ℂ))/((D : ℂ)*(d : ℂ))‖ := norm_add_le _ _
    _ = ‖A-B‖/D+‖B‖*|D-d|/(D*d) := by
      simp only [norm_div, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hdpos, abs_of_pos hDpos, abs_sub_comm d D]
    _ ≤ 4/100000000+3/100000000 := add_le_add hfirst hsecond
    _ ≤ 1/10000000 := by norm_num

end

end TwoLevelPerturbation
