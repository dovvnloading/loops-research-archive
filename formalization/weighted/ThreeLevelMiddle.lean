import ThreeLevelDomains
import ThreeLevelReference
import ThreeLevelPerturbation
import TwoLevelOuterDomain

/-!
# The complete middle return on a whole parameter chart

A first return close to a quadratic is iterated through the entire
middle period.  The estimates here retain the large middle target disk,
its complete central source, and every intermediate complex phase.
The reference parameter is allowed to vary through an outer chart;
no terminal tip condition is imposed on the middle return.
-/

namespace ThreeLevelMiddle

open Set Function Metric
open LimitingCrestQuadraticReturn NearTwoShooting TwoLevelOuterChart
open TwoLevelPerturbation

noncomputable section

def radius (q : ℕ) : ℝ := TwoLevelOuterDomain.targetRadius q

theorem radius_pos (q : ℕ) : 0 < radius q :=
  TwoLevelOuterDomain.targetRadius_pos q

theorem radius_sq (q : ℕ) : (radius q)^2 = scale q :=
  TwoLevelOuterDomain.targetRadius_sq q

theorem radius_small {q : ℕ} (hq : 17 ≤ q) :
    radius q ≤ 1/131072 := by
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hq
  norm_num at h
  exact h

theorem scale_inside_radius {q : ℕ} (hq : 17 ≤ q) :
    128*scale q < radius q := by
  have hp := radius_pos q
  have hm := mul_le_mul_of_nonneg_right (radius_small hq) hp.le
  have hs := radius_sq q
  nlinarith only [hp, hm, hs]

theorem half_radius_scale (q : ℕ) :
    (4 : ℝ)^q*(radius q/2)^2 = 1/4 := by
  calc
    _ = ((radius q)^2*(4 : ℝ)^q)/4 := by ring
    _ = _ := by rw [radius_sq, scale_mul_power]; norm_num

theorem reference_half_disk {q : ℕ} (hq : 17 ≤ q)
    {a b l u t : ℝ} (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    {z : ℂ} (hz : ‖z‖ ≤ radius q/2) (j : ℕ) (hj : j ≤ q) :
    ‖((quadraticMap t)^[j]) z‖ ≤ 21/10 := by
  apply quadratic_orbit_disk t (ThreeLevelReference.chart_parameter_band hq g ht)
    q (radius q/2) (by linarith [radius_pos q])
    (by linarith [radius_small hq]) _ hz j hj
  rw [half_radius_scale]
  norm_num

/-- Complete orbit comparison on the entire middle barrier disk. -/
theorem perturbed_half_disk (H : ℂ → ℂ) {q : ℕ} (hq : 17 ≤ q)
    {a b l u t : ℝ} (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    (ε : ℝ) (hε : 0 ≤ ε) (hbudget : ε*(5 : ℝ)^q ≤ scale q)
    (hclose : ∀ z : ℂ, ‖z‖ ≤ 12/5 → ‖H z-quadraticMap t z‖ ≤ ε)
    {z : ℂ} (hz : ‖z‖ ≤ radius q/2) (j : ℕ) (hj : j ≤ q) :
    ‖(H^[j]) z-((quadraticMap t)^[j]) z‖ ≤ (5 : ℝ)^j*ε ∧
      ‖(H^[j]) z‖ ≤ 12/5 := by
  exact iterate_stability H t z q ε hε
    (by linarith [scale_small hq]) hclose
    (fun n hn => reference_half_disk hq g ht hz n hn) j hj

/-- A fixed numerical margin survives the first-return perturbation;
it is much larger than the exponentially small middle target. -/
theorem reference_barrier_margin {q : ℕ} (hq : 17 ≤ q)
    {a b l u t : ℝ} (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    {z : ℂ} (hz : ‖z‖ = radius q/2) :
    (1/32 : ℝ) < ‖((quadraticMap t)^[q]) z‖ := by
  have he : q-1+1 = q := by omega
  have hs := half_radius_scale q
  have hE := complete_remainder_bound t (q-1) (radius q/2) z
    (by linarith [radius_pos q])
    (fun j hj => g.critical_orbit t ht j (by omega))
    (by rw [he, hs]; norm_num) hz.le
  rw [he, hs] at hE
  norm_num at hE
  have hA := coefficient_negative (g.coefficient_lower t ht)
  have hlead : (3/80 : ℝ) < ‖(returnCoefficient q t : ℂ)*z^2‖ := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg hA, hz]
    have hsq : (radius q/2)^2 = scale q/4 := by
      nlinarith only [radius_sq q]
    rw [hsq]
    nlinarith only [g.coefficient_lower t ht]
  have hid : (returnCoefficient q t : ℂ)*z^2 =
      ((quadraticMap t)^[q]) z-(criticalValue t q : ℂ)-
        quadraticRemainder t (q-1) z := by
    simp only [quadraticRemainder, returnCoefficient, he]
    ring
  have ht1 := norm_sub_le
    (((quadraticMap t)^[q]) z-(criticalValue t q : ℂ))
    (quadraticRemainder t (q-1) z)
  rw [← hid] at ht1
  have ht2 := norm_sub_le (((quadraticMap t)^[q]) z) (criticalValue t q : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (g.return_range t ht).1] at ht2
  linarith [(g.return_range t ht).2, scale_small hq]

theorem middle_barrier (H : ℂ → ℂ) {q : ℕ} (hq : 17 ≤ q)
    {a b l u t : ℝ} (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    (ε : ℝ) (hε : 0 ≤ ε) (hbudget : ε*(5 : ℝ)^q ≤ scale q)
    (hclose : ∀ z : ℂ, ‖z‖ ≤ 12/5 → ‖H z-quadraticMap t z‖ ≤ ε)
    {z : ℂ} (hz : ‖z‖ = radius q/2) :
    radius q < ‖(H^[q]) z‖ := by
  have href := reference_barrier_margin hq g ht hz
  have he := (perturbed_half_disk H hq g ht ε hε hbudget hclose hz.le q le_rfl).1
  have ht1 := norm_le_norm_sub_add (((quadraticMap t)^[q]) z) ((H^[q]) z)
  rw [norm_sub_rev] at ht1
  nlinarith only [href, he, ht1, hbudget, radius_small hq, scale_small hq]

theorem middle_critical_norm (H : ℂ → ℂ) {q : ℕ} (hq : 17 ≤ q)
    {a b l u t : ℝ} (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    (ε : ℝ) (hε : 0 ≤ ε) (hbudget : ε*(5 : ℝ)^q ≤ scale q)
    (hclose : ∀ z : ℂ, ‖z‖ ≤ 12/5 → ‖H z-quadraticMap t z‖ ≤ ε) :
    ‖(H^[q]) 0‖ ≤ 15*scale q ∧ ‖(H^[q]) 0‖ < radius q := by
  have he := critical_iterate_stability H t
    (ThreeLevelReference.chart_parameter_band hq g ht) q ε hε
    (by linarith [scale_small hq]) hclose q le_rfl
  have ht1 := norm_le_norm_sub_add ((H^[q]) 0) (criticalValue t q : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (g.return_range t ht).1] at ht1
  have hb : ‖(H^[q]) 0‖ ≤ 15*scale q := by
    nlinarith only [he, ht1, hbudget, (g.return_range t ht).2]
  exact ⟨hb, by linarith [scale_inside_radius hq, scale_pos q]⟩

/-- Intermediate phases stay near the physical critical itinerary,
uniformly over every point of the middle barrier disk. -/
theorem middle_phase_displacement (H : ℂ → ℂ) {q : ℕ} (hq : 17 ≤ q)
    {a b l u t : ℝ} (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    (ε : ℝ) (hε : 0 ≤ ε) (hbudget : ε*(5 : ℝ)^q ≤ scale q)
    (hclose : ∀ z : ℂ, ‖z‖ ≤ 12/5 → ‖H z-quadraticMap t z‖ ≤ ε)
    {z : ℂ} (hz : ‖z‖ ≤ radius q/2) (j : ℕ) (hj : 1 ≤ j) (hjq : j ≤ q) :
    ‖(H^[j]) z-(criticalValue t j : ℂ)‖ ≤ 1/5 := by
  have hp := (perturbed_half_disk H hq g ht ε hε hbudget hclose hz j hjq).1
  have hjform : j-1+1 = j := by omega
  have hp4 : (4 : ℝ)^j ≤ (4 : ℝ)^q :=
    pow_le_pow_right₀ (by norm_num) hjq
  have ht4 := mul_le_mul_of_nonneg_right hp4 (sq_nonneg (radius q/2))
  rw [half_radius_scale] at ht4
  have hd := orbit_displacement t (j-1) (radius q/2) z
    (by linarith [radius_pos q])
    (fun k hk => g.critical_orbit t ht k (by omega))
    (by rw [hjform]; linarith) hz
  rw [hjform] at hd
  have hp5 : (5 : ℝ)^j ≤ (5 : ℝ)^q :=
    pow_le_pow_right₀ (by norm_num) hjq
  have he := mul_le_mul_of_nonneg_right hp5 hε
  have ht1 : ‖(H^[j]) z-(criticalValue t j : ℂ)‖ ≤
      ‖(H^[j]) z-((quadraticMap t)^[j]) z‖ +
      ‖((quadraticMap t)^[j]) z-(criticalValue t j : ℂ)‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      ((H^[j]) z) (((quadraticMap t)^[j]) z) (criticalValue t j : ℂ)
  nlinarith only [hp, hd, ht4, he, ht1, hbudget, scale_small hq]

private theorem separated_from_negative {u v : ℂ} {x : ℝ}
    (hx : (7/5 : ℝ) ≤ |x|)
    (hu : ‖u-(x : ℂ)‖ ≤ 1/5) (hv : ‖v-(x : ℂ)‖ ≤ 1/5) :
    u ≠ -v := by
  intro heq
  have hur := (Complex.abs_re_le_norm (u-(x : ℂ))).trans hu
  have hvr := (Complex.abs_re_le_norm (v-(x : ℂ))).trans hv
  simp only [Complex.sub_re, Complex.ofReal_re] at hur hvr
  have he := congrArg Complex.re heq
  simp only [Complex.neg_re] at he
  have hxb : |x| ≤ (1/5 : ℝ) := by
    rw [abs_le]
    have hu' := abs_le.mp hur
    have hv' := abs_le.mp hvr
    constructor <;> linarith [hu'.1, hu'.2, hv'.1, hv'.2]
  linarith only [hx, hxb]

/-- All later apparent sign collisions are excluded by the actual
noncentral itinerary.  Only the original quadratic sign pair remains. -/
theorem middle_collision (H : ℂ → ℂ) {q : ℕ} (hq : 17 ≤ q)
    {a b l u t : ℝ} (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    (ε : ℝ) (hε : 0 ≤ ε) (hbudget : ε*(5 : ℝ)^q ≤ scale q)
    (hclose : ∀ z : ℂ, ‖z‖ ≤ 12/5 → ‖H z-quadraticMap t z‖ ≤ ε)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 12/5 → ‖w‖ ≤ 12/5 →
      (H z = H w ↔ z = w ∨ z = -w))
    {z w : ℂ} (hz : ‖z‖ ≤ radius q/2) (hw : ‖w‖ ≤ radius q/2) :
    (H^[q]) z = (H^[q]) w ↔ z = w ∨ z = -w := by
  have hbound (v : ℂ) (hv : ‖v‖ ≤ radius q/2) (j : ℕ) (hj : j ≤ q) :
      ‖(H^[j]) v‖ ≤ 12/5 :=
    (perturbed_half_disk H hq g ht ε hε hbudget hclose hv j hj).2
  have hzR : ‖z‖ ≤ 12/5 := by simpa using hbound z hz 0 (by omega)
  have hwR : ‖w‖ ≤ 12/5 := by simpa using hbound w hw 0 (by omega)
  have hphase (j : ℕ) (hj : 1 ≤ j) (hjq : j < q) :
      (H^[j]) z ≠ -((H^[j]) w) := by
    apply separated_from_negative (ThreeLevelReference.outer_phase_abs hq g ht hj hjq)
    · exact middle_phase_displacement H hq g ht ε hε hbudget hclose hz j hj hjq.le
    · exact middle_phase_displacement H hq g ht ε hε hbudget hclose hw j hj hjq.le
  constructor
  · intro heq
    have hcancel : ∀ j : ℕ, j ≤ q → 1 ≤ j →
        (H^[j]) z = (H^[j]) w → H z = H w := by
      intro j
      induction j with
      | zero => intro _ hj _; omega
      | succ j ih =>
        intro hjq hj he
        by_cases hj0 : j = 0
        · subst j
          simpa using he
        · have hj1 : 1 ≤ j := by omega
          rw [iterate_succ_apply', iterate_succ_apply'] at he
          rcases (hcollision (hbound z hz j (by omega))
            (hbound w hw j (by omega))).mp he with hsame | hnegative
          · exact ih (by omega) hj1 hsame
          · exact False.elim (hphase j hj1 (by omega) hnegative)
    exact (hcollision hzR hwR).mp (hcancel q le_rfl (by omega) heq)
  · rintro (he | he)
    · rw [he]
    · have hsame := (hcollision hzR hwR).mpr (Or.inr he)
      have hqform : q = (q-1)+1 := by omega
      rw [hqform, iterate_succ_apply, iterate_succ_apply, hsame]

theorem middle_noncentral_phase (H : ℂ → ℂ) {q : ℕ} (hq : 17 ≤ q)
    {a b l u t : ℝ} (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    (ε : ℝ) (hε : 0 ≤ ε) (hbudget : ε*(5 : ℝ)^q ≤ scale q)
    (hclose : ∀ z : ℂ, ‖z‖ ≤ 12/5 → ‖H z-quadraticMap t z‖ ≤ ε)
    {z : ℂ} (hz : ‖z‖ ≤ radius q/2) (j : ℕ) (hj : 1 ≤ j) (hjq : j < q) :
    (6/5 : ℝ) ≤ ‖(H^[j]) z‖ := by
  have he := middle_phase_displacement H hq g ht ε hε hbudget hclose hz j hj hjq.le
  have hb := ThreeLevelReference.outer_phase_abs hq g ht hj hjq
  have ht1 := norm_le_norm_sub_add (criticalValue t j : ℂ) ((H^[j]) z)
  rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs] at ht1
  linarith only [he, hb, ht1]

/-- A disk substantially larger than the terminal source maps into the
middle target.  This is the quantitative nesting input. -/
theorem middle_small_disk_image (H : ℂ → ℂ) {q : ℕ} (hq : 17 ≤ q)
    {a b l u t : ℝ} (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    (ε : ℝ) (hε : 0 ≤ ε) (hbudget : ε*(5 : ℝ)^q ≤ scale q)
    (hclose : ∀ z : ℂ, ‖z‖ ≤ 12/5 → ‖H z-quadraticMap t z‖ ≤ ε)
    {z : ℂ} (hz : ‖z‖ ≤ 16*scale q) :
    ‖(H^[q]) z‖ < radius q := by
  have hs : (4 : ℝ)^q*(16*scale q)^2 = 256*scale q := by
    calc
      _ = 256*scale q*(scale q*(4 : ℝ)^q) := by ring
      _ = _ := by rw [scale_mul_power]; ring
  have hreference (j : ℕ) (hj : j ≤ q) :
      ‖((quadraticMap t)^[j]) z‖ ≤ 21/10 := by
    apply quadratic_orbit_disk t (ThreeLevelReference.chart_parameter_band hq g ht)
      q (16*scale q) (by positivity) (by linarith [scale_small hq]) _ hz j hj
    rw [hs]
    linarith [scale_small hq]
  have he := (iterate_stability H t z q ε hε
    (by linarith [scale_small hq]) hclose hreference q le_rfl).1
  have hqform : q-1+1 = q := by omega
  have hd := orbit_displacement t (q-1) (16*scale q) z (by positivity)
    (fun j hj => g.critical_orbit t ht j (by omega))
    (by rw [hqform, hs]; linarith [scale_small hq]) hz
  rw [hqform, hs] at hd
  have ht1 := norm_le_norm_sub_add ((H^[q]) z) (((quadraticMap t)^[q]) z)
  have ht2 := norm_le_norm_sub_add (((quadraticMap t)^[q]) z) (criticalValue t q : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (g.return_range t ht).1] at ht2
  nlinarith only [he, hd, ht1, ht2, hbudget, (g.return_range t ht).2,
    scale_inside_radius hq, scale_pos q]

/-- Every point of the full secondary monic comparison disk maps into
the selected middle target, with the actual reference coefficient. -/
theorem middle_monic_disk_image (H : ℂ → ℂ) {q : ℕ} (hq : 17 ≤ q)
    {a b l u t : ℝ} (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    (ε : ℝ) (hε : 0 ≤ ε) (hbudget : ε*(5 : ℝ)^q ≤ scale q)
    (hclose : ∀ z : ℂ, ‖z‖ ≤ 12/5 → ‖H z-quadraticMap t z‖ ≤ ε)
    {z : ℂ} (hz : ‖z‖ ≤ 12/5) :
    ‖(H^[q]) (z/(returnCoefficient q t : ℂ))‖ < radius q := by
  apply middle_small_disk_image H hq g ht ε hε hbudget hclose
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
  have hA := coefficient_negative (g.coefficient_lower t ht)
  apply (div_le_iff₀ (abs_pos.mpr hA.ne)).mpr
  rw [abs_of_neg hA]
  nlinarith only [hz, g.coefficient_lower t ht]

/-- At every middle checkpoint the entire perturbed terminal source lies
in the small disk already proved to belong to the middle component. -/
theorem terminal_block_bound (H : ℂ → ℂ) {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u t : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    (ε : ℝ) (hε : 0 ≤ ε) (hbudget : ε*(5 : ℝ)^(r*q) ≤ scale q)
    (hclose : ∀ z : ℂ, ‖z‖ ≤ 12/5 → ‖H z-quadraticMap t z‖ ≤ ε)
    (D : ℝ) (hD : |D-criticalValue t (r*q)| ≤ |criticalValue t (r*q)| / 100)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20) (j : ℕ) (hjr : j ≤ r) :
    ‖(H^[j*q]) ((D : ℂ)*z)‖ ≤ 15*scale q := by
  have hq : 17 ≤ q := by omega
  have hd := (ThreeLevelReference.terminal_scale_negative hr hqr h g ht).ne
  obtain ⟨hw, hid⟩ := ThreeLevelPerturbation.moving_scale_input
    (criticalValue t (r*q)) D hd hD hz
  have hmodel (n : ℕ) (hn : n ≤ r*q) :
      ‖((quadraticMap t)^[n]) ((D : ℂ)*z)‖ ≤ 21/10 := by
    rw [← hid]
    exact ThreeLevelReference.physical_orbit_disk hr hqr h g ht hw n hn
  have hjN := Nat.mul_le_mul_right q hjr
  have he := (iterate_stability H t ((D : ℂ)*z) (r*q) ε hε
    (by linarith [scale_small hq]) hclose hmodel (j*q) hjN).1
  have href := ThreeLevelReference.physical_block_input hr hqr h g ht hw j hjr
  rw [hid] at href
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5) hjN
  have hm := mul_le_mul_of_nonneg_right hp hε
  have ht1 := norm_le_norm_sub_add ((H^[j*q]) ((D : ℂ)*z))
    (((quadraticMap t)^[j*q]) ((D : ℂ)*z))
  nlinarith only [he, href, hp, hm, hbudget, ht1]

/-- No intermediate first-return time can enter the terminal scale:
the bound includes times inside a middle block and its checkpoints. -/
theorem terminal_noncentral_phase (H : ℂ → ℂ) {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u t : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    (ε : ℝ) (hε : 0 ≤ ε) (hbudget : ε*(5 : ℝ)^(r*q) ≤ scale q)
    (hclose : ∀ z : ℂ, ‖z‖ ≤ 12/5 → ‖H z-quadraticMap t z‖ ≤ ε)
    (D : ℝ) (hD : |D-criticalValue t (r*q)| ≤ |criticalValue t (r*q)| / 100)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20) (n : ℕ) (hn : 1 ≤ n) (hnN : n < r*q) :
    scale q ≤ ‖(H^[n]) ((D : ℂ)*z)‖ := by
  have hq : 17 ≤ q := by omega
  have hd := (ThreeLevelReference.terminal_scale_negative hr hqr h g ht).ne
  obtain ⟨hw, hid⟩ := ThreeLevelPerturbation.moving_scale_input
    (criticalValue t (r*q)) D hd hD hz
  have hmodel (j : ℕ) (hj : j ≤ r*q) :
      ‖((quadraticMap t)^[j]) ((D : ℂ)*z)‖ ≤ 21/10 := by
    rw [← hid]
    exact ThreeLevelReference.physical_orbit_disk hr hqr h g ht hw j hj
  have he := (iterate_stability H t ((D : ℂ)*z) (r*q) ε hε
    (by linarith [scale_small hq]) hclose hmodel n hnN.le).1
  have href := ThreeLevelReference.physical_phase_pair_lower hr hqr h g ht hw hw n hn hnN
  rw [hid] at href
  have hdouble (v : ℂ) : ‖v+v‖ = 2*‖v‖ := by
    rw [← two_mul, norm_mul]
    norm_num
  rw [hdouble] at href
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5) hnN.le
  have hm := mul_le_mul_of_nonneg_right hp hε
  have ht1 := norm_le_norm_sub_add
    (((quadraticMap t)^[n]) ((D : ℂ)*z)) ((H^[n]) ((D : ℂ)*z))
  rw [norm_sub_rev] at ht1
  nlinarith only [he, href, hm, hbudget, ht1]

end
end ThreeLevelMiddle
