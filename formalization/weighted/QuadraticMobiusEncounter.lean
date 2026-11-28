import Mathlib

/-!
# Two quadratic encounters with three parabolic Möbius flights

The actual ordered rational composition considered here is

`flight r ∘ encounter b ∘ flight t ∘ encounter a ∘ flight s`,

where `encounter a u = u + a*u^2` and `flight s u = u / (1-s*u)`.
Its denominator is one at zero. If its identity defect vanishes through
degree five, then both quadratic encounters vanish and the three flight
times sum to zero. Degree four does not suffice, as an explicit complex
example shows.

This is an exact rational-composition obstruction. Identifying a limiting
block of actual quadratic iterates with these Möbius flights is a separate
geometric hypothesis and is not asserted in this module.
-/

namespace QuadraticMobiusEncounter

open Filter
open scoped Topology

noncomputable section

/-- A normalized quadratic critical encounter in the squared coordinate. -/
def encounter (a u : ℂ) : ℂ := u + a*u^2

/-- The time parameter adds under composition wherever the maps are defined. -/
def flight (t u : ℂ) : ℂ := u / (1-t*u)

/-- Numerator of the first encounter after clearing the initial flight. -/
def initialNumerator (a s u : ℂ) : ℂ := u*(1-s*u) + a*u^2

/-- Numerator of the full two-encounter, three-flight composition. -/
def numerator (a b s t u : ℂ) : ℂ :=
  initialNumerator a s u *
    ((1-s*u)^2 + (b-t)*initialNumerator a s u)

/-- Denominator of that same rational composition. -/
def denominator (a b s t r u : ℂ) : ℂ :=
  ((1-s*u)^2 - t*initialNumerator a s u)^2 -
    r*numerator a b s t u

private theorem encounter_fraction (a n d : ℂ) (hd : d ≠ 0) :
    encounter a (n/d) = (n*d+a*n^2)/d^2 := by
  unfold encounter
  field_simp [hd]
  <;> ring

private theorem flight_fraction (r n d : ℂ) (hd : d ≠ 0)
    (hr : d-r*n ≠ 0) :
    flight r (n/d) = n/(d-r*n) := by
  unfold flight
  have he : 1-r*(n/d) = (d-r*n)/d := by
    field_simp [hd]
    <;> ring
  rw [he]
  field_simp [hd, hr]
  <;> ring

/-- Exact rational formula for the actual composition, with its three
denominator conditions explicitly stated. -/
theorem composition_formula (a b s t r u : ℂ)
    (hpre : 1-s*u ≠ 0)
    (hmid : (1-s*u)^2-t*initialNumerator a s u ≠ 0)
    (hpost : denominator a b s t r u ≠ 0) :
    flight r (encounter b (flight t (encounter a (flight s u)))) =
      numerator a b s t u / denominator a b s t r u := by
  let p : ℂ := 1-s*u
  let H : ℂ := u*p+a*u^2
  let L : ℂ := p^2-t*H
  have hp : p ≠ 0 := hpre
  have hL : L ≠ 0 := hmid
  change flight r (encounter b (flight t (encounter a (u/p)))) = _
  rw [encounter_fraction a u p hp]
  change flight r (encounter b (flight t (H/p^2))) = _
  rw [flight_fraction t H (p^2) (pow_ne_zero 2 hp) hL]
  rw [encounter_fraction b H L hL]
  have hn : H*L+b*H^2 = numerator a b s t u := by
    dsimp [H, L, p, numerator, initialNumerator]
    ring
  rw [hn]
  have hr : L^2-r*numerator a b s t u ≠ 0 := hpost
  rw [flight_fraction r (numerator a b s t u) (L^2) (pow_ne_zero 2 hL) hr]
  rfl

/-- Clearing denominators does not introduce an exceptional point at zero. -/
theorem denominator_at_zero (a b s t r : ℂ) :
    denominator a b s t r 0 = 1 := by
  norm_num [denominator, numerator, initialNumerator]

/-- Quadratic identity-defect coefficient without the initial flight. -/
def core2 (a b t q : ℂ) : ℂ := a+b+t+q

/-- Cubic identity-defect coefficient without the initial flight. -/
def core3 (a b t q : ℂ) : ℂ := 2*a*b+q*(a+b-t)-t^2

/-- Quartic identity-defect coefficient without the initial flight. -/
def core4 (a b t q : ℂ) : ℂ := a^2*(b-t)-2*a*(t^2-q*(b-t))

/-- Quintic identity-defect coefficient without the initial flight. -/
def core5 (a b t q : ℂ) : ℂ := -a^2*(t^2-q*(b-t))

/-- The initial flight is retained through the effective final time `r+s`. -/
def jet2 (a b s t r : ℂ) : ℂ := core2 a b t (r+s)

def jet3 (a b s t r : ℂ) : ℂ :=
  core3 a b t (r+s)-3*s*core2 a b t (r+s)

def jet4 (a b s t r : ℂ) : ℂ :=
  core4 a b t (r+s)-2*s*core3 a b t (r+s)+3*s^2*core2 a b t (r+s)

def jet5 (a b s t r : ℂ) : ℂ :=
  core5 a b t (r+s)-s*core4 a b t (r+s)+s^2*core3 a b t (r+s)-
    s^3*core2 a b t (r+s)

/-- The complete cleared identity defect is a degree-at-most-five
polynomial. No unexamined remainder occurs in this identity. -/
theorem cleared_defect_expansion (a b s t r u : ℂ) :
    numerator a b s t u-u*denominator a b s t r u =
      jet2 a b s t r*u^2 + jet3 a b s t r*u^3 +
      jet4 a b s t r*u^4 + jet5 a b s t r*u^5 := by
  simp only [numerator, denominator, initialNumerator,
    jet2, jet3, jet4, jet5, core2, core3, core4, core5]
  ring

/-- Eliminating the quadratic defect leaves a particularly simple exact
formula for the three remaining coefficients. -/
theorem core_coefficients_after_quadratic_cancellation (a b t : ℂ) :
    core2 a b t (-a-b-t) = 0 ∧
    core3 a b t (-a-b-t) = -(a^2+b^2) ∧
    core4 a b t (-a-b-t) = a^2*(t-b)-2*a*b^2 ∧
    core5 a b t (-a-b-t) = a^2*(a*(t-b)-b^2) := by
  unfold core2 core3 core4 core5
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Two quadratic encounters cannot be hidden through degree five by an
arbitrary intermediate and final Möbius flight. -/
theorem two_encounter_core_flat (a b t q : ℂ)
    (h2 : core2 a b t q = 0)
    (h3 : core3 a b t q = 0)
    (h4 : core4 a b t q = 0)
    (h5 : core5 a b t q = 0) :
    a = 0 ∧ b = 0 ∧ t+q = 0 := by
  have hq : q = -a-b-t := by
    dsimp [core2] at h2
    linear_combination h2
  rw [hq] at h3 h4 h5
  rcases core_coefficients_after_quadratic_cancellation a b t with
    ⟨_, hc3, hc4, hc5⟩
  rw [hc3] at h3
  rw [hc4] at h4
  rw [hc5] at h5
  have hs : a^2+b^2 = 0 := by linear_combination -h3
  have hp : (a*b)*(a*b) = 0 := by
    linear_combination h5-a*h4
  have hab : a*b = 0 := by
    rcases mul_eq_zero.mp hp with h | h <;> exact h
  have ha : a = 0 := by
    rcases mul_eq_zero.mp hab with ha | hb
    · exact ha
    · have haa : a*a = 0 := by simpa [hb, pow_two] using hs
      rcases mul_eq_zero.mp haa with ha | ha <;> exact ha
  have hb : b = 0 := by
    have hbb : b*b = 0 := by simpa [ha, pow_two] using hs
    rcases mul_eq_zero.mp hbb with hb | hb <;> exact hb
  refine ⟨ha, hb, ?_⟩
  simpa [core2, ha, hb] using h2

/-- The obstruction retains three arbitrary Möbius flights, including one
before the first encounter. Their coordinate changes cannot remove it. -/
theorem two_encounter_three_flight_flat (a b s t r : ℂ)
    (h2 : jet2 a b s t r = 0)
    (h3 : jet3 a b s t r = 0)
    (h4 : jet4 a b s t r = 0)
    (h5 : jet5 a b s t r = 0) :
    a = 0 ∧ b = 0 ∧ s+t+r = 0 := by
  have hc2 : core2 a b t (r+s) = 0 := h2
  have hc3 : core3 a b t (r+s) = 0 := by
    dsimp [jet3] at h3
    linear_combination h3+3*s*hc2
  have hc4 : core4 a b t (r+s) = 0 := by
    dsimp [jet4] at h4
    linear_combination h4+2*s*hc3-3*s^2*hc2
  have hc5 : core5 a b t (r+s) = 0 := by
    dsimp [jet5] at h5
    linear_combination h5+s*hc4-s^2*hc3+s^3*hc2
  rcases two_encounter_core_flat a b t (r+s) hc2 hc3 hc4 hc5 with
    ⟨ha, hb, htime⟩
  refine ⟨ha, hb, ?_⟩
  linear_combination htime

/-- Identity on an actual neighborhood is impossible for a nonzero
two-encounter profile. The defect polynomial has infinitely many roots,
so all four of its coefficients vanish. -/
theorem two_encounter_identity_germ (a b s t r : ℂ)
    (h : ∀ᶠ u in 𝓝 (0 : ℂ),
      numerator a b s t u = u*denominator a b s t r u) :
    a = 0 ∧ b = 0 ∧ s+t+r = 0 := by
  let p : Polynomial ℂ :=
    Polynomial.monomial 2 (jet2 a b s t r) +
    Polynomial.monomial 3 (jet3 a b s t r) +
    Polynomial.monomial 4 (jet4 a b s t r) +
    Polynomial.monomial 5 (jet5 a b s t r)
  have heval (u : ℂ) : p.eval u =
      numerator a b s t u-u*denominator a b s t r u := by
    rw [cleared_defect_expansion]
    simp only [p, Polynomial.eval_add, Polynomial.eval_monomial]
  have hroots : ∀ᶠ u in 𝓝 (0 : ℂ), p.IsRoot u := by
    filter_upwards [h] with u hu
    change p.eval u = 0
    rw [heval]
    exact sub_eq_zero.mpr hu
  have hp : p = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot p (infinite_of_mem_nhds (0 : ℂ) hroots)
  apply two_encounter_three_flight_flat a b s t r
  · simpa [p, Polynomial.coeff_monomial] using congrArg (fun q : Polynomial ℂ => q.coeff 2) hp
  · simpa [p, Polynomial.coeff_monomial] using congrArg (fun q : Polynomial ℂ => q.coeff 3) hp
  · simpa [p, Polynomial.coeff_monomial] using congrArg (fun q : Polynomial ℂ => q.coeff 4) hp
  · simpa [p, Polynomial.coeff_monomial] using congrArg (fun q : Polynomial ℂ => q.coeff 5) hp

/-- The same obstruction directly for the rational composition as a germ.
All denominator conditions are proved on a neighborhood of zero. -/
theorem two_encounter_composition_identity_germ (a b s t r : ℂ)
    (h : ∀ᶠ u in 𝓝 (0 : ℂ),
      flight r (encounter b (flight t (encounter a (flight s u)))) = u) :
    a = 0 ∧ b = 0 ∧ s+t+r = 0 := by
  have hprecont : Continuous (fun u : ℂ => 1-s*u) := by fun_prop
  have hmidcont : Continuous
      (fun u : ℂ => (1-s*u)^2-t*initialNumerator a s u) := by
    unfold initialNumerator
    fun_prop
  have hpostcont : Continuous (denominator a b s t r) := by
    unfold denominator numerator initialNumerator
    fun_prop
  have hpre : ∀ᶠ u in 𝓝 (0 : ℂ), 1-s*u ≠ 0 :=
    hprecont.continuousAt.eventually_ne (by norm_num)
  have hmid : ∀ᶠ u in 𝓝 (0 : ℂ), (1-s*u)^2-t*initialNumerator a s u ≠ 0 :=
    hmidcont.continuousAt.eventually_ne (by norm_num [initialNumerator])
  have hpost : ∀ᶠ u in 𝓝 (0 : ℂ), denominator a b s t r u ≠ 0 :=
    hpostcont.continuousAt.eventually_ne (by rw [denominator_at_zero]; exact one_ne_zero)
  apply two_encounter_identity_germ a b s t r
  filter_upwards [h, hpre, hmid, hpost] with u hu hpu hmu hdu
  rw [composition_formula a b s t r u hpu hmu hdu] at hu
  exact (div_eq_iff hdu).mp hu

set_option maxHeartbeats 1000000 in
/-- A convergent two-encounter, three-flight profile cannot lose both
encounters in its identity jet. All convergence assumptions concern this
explicit rational-composition profile; no realization by an actual
quadratic renormalization is included in the statement. -/
theorem two_encounter_three_flight_limit_flat
    (a b s t r : ℕ → ℂ) (α β σ τ ρ : ℂ)
    (ha : Tendsto a atTop (𝓝 α))
    (hb : Tendsto b atTop (𝓝 β))
    (hs : Tendsto s atTop (𝓝 σ))
    (ht : Tendsto t atTop (𝓝 τ))
    (hr : Tendsto r atTop (𝓝 ρ))
    (h2 : Tendsto (fun n => jet2 (a n) (b n) (s n) (t n) (r n))
      atTop (𝓝 0))
    (h3 : Tendsto (fun n => jet3 (a n) (b n) (s n) (t n) (r n))
      atTop (𝓝 0))
    (h4 : Tendsto (fun n => jet4 (a n) (b n) (s n) (t n) (r n))
      atTop (𝓝 0))
    (h5 : Tendsto (fun n => jet5 (a n) (b n) (s n) (t n) (r n))
      atTop (𝓝 0)) :
    α = 0 ∧ β = 0 ∧ σ+τ+ρ = 0 := by
  have hq := hr.add hs
  have hc2 : Tendsto (fun n => core2 (a n) (b n) (t n) (r n+s n))
      atTop (𝓝 (core2 α β τ (ρ+σ))) := by
    unfold core2
    exact ((ha.add hb).add ht).add hq
  have hc3 : Tendsto (fun n => core3 (a n) (b n) (t n) (r n+s n))
      atTop (𝓝 (core3 α β τ (ρ+σ))) := by
    unfold core3
    exact (((tendsto_const_nhds.mul ha).mul hb).add
      (hq.mul ((ha.add hb).sub ht))).sub (ht.pow 2)
  have hc4 : Tendsto (fun n => core4 (a n) (b n) (t n) (r n+s n))
      atTop (𝓝 (core4 α β τ (ρ+σ))) := by
    unfold core4
    exact ((ha.pow 2).mul (hb.sub ht)).sub
      ((tendsto_const_nhds.mul ha).mul ((ht.pow 2).sub (hq.mul (hb.sub ht))))
  have hc5 : Tendsto (fun n => core5 (a n) (b n) (t n) (r n+s n))
      atTop (𝓝 (core5 α β τ (ρ+σ))) := by
    unfold core5
    exact (ha.pow 2).neg.mul ((ht.pow 2).sub (hq.mul (hb.sub ht)))
  have hj2 : Tendsto (fun n => jet2 (a n) (b n) (s n) (t n) (r n))
      atTop (𝓝 (jet2 α β σ τ ρ)) := hc2
  have hj3 : Tendsto (fun n => jet3 (a n) (b n) (s n) (t n) (r n))
      atTop (𝓝 (jet3 α β σ τ ρ)) := by
    unfold jet3
    exact hc3.sub ((tendsto_const_nhds.mul hs).mul hc2)
  have hj4 : Tendsto (fun n => jet4 (a n) (b n) (s n) (t n) (r n))
      atTop (𝓝 (jet4 α β σ τ ρ)) := by
    unfold jet4
    exact (hc4.sub ((tendsto_const_nhds.mul hs).mul hc3)).add
      ((tendsto_const_nhds.mul (hs.pow 2)).mul hc2)
  have hj5 : Tendsto (fun n => jet5 (a n) (b n) (s n) (t n) (r n))
      atTop (𝓝 (jet5 α β σ τ ρ)) := by
    unfold jet5
    exact ((hc5.sub (hs.mul hc4)).add ((hs.pow 2).mul hc3)).sub ((hs.pow 3).mul hc2)
  exact two_encounter_three_flight_flat α β σ τ ρ
    (tendsto_nhds_unique hj2 h2) (tendsto_nhds_unique hj3 h3)
    (tendsto_nhds_unique hj4 h4) (tendsto_nhds_unique hj5 h5)

/-- The fifth-order threshold is sharp: two nonzero encounters and
genuine complex Möbius flights can cancel the entire lower identity jet. -/
theorem sharp_two_encounter_coefficients :
    jet2 1 Complex.I 0 (Complex.I-2) (1-2*Complex.I) = 0 ∧
    jet3 1 Complex.I 0 (Complex.I-2) (1-2*Complex.I) = 0 ∧
    jet4 1 Complex.I 0 (Complex.I-2) (1-2*Complex.I) = 0 ∧
    jet5 1 Complex.I 0 (Complex.I-2) (1-2*Complex.I) = -1 := by
  unfold jet2 jet3 jet4 jet5 core2 core3 core4 core5
  norm_num [Complex.I_sq]
  <;> ring_nf
  <;> norm_num [Complex.I_sq]

/-- The sharpness example has exactly the cleared defect `-u^5`. -/
theorem sharp_two_encounter_defect (u : ℂ) :
    numerator 1 Complex.I 0 (Complex.I-2) u -
      u*denominator 1 Complex.I 0 (Complex.I-2) (1-2*Complex.I) u = -u^5 := by
  rw [cleared_defect_expansion]
  rcases sharp_two_encounter_coefficients with ⟨h2, h3, h4, h5⟩
  rw [h2, h3, h4, h5]
  ring

#print axioms composition_formula
#print axioms denominator_at_zero
#print axioms cleared_defect_expansion
#print axioms core_coefficients_after_quadratic_cancellation
#print axioms two_encounter_core_flat
#print axioms two_encounter_three_flight_flat
#print axioms two_encounter_identity_germ
#print axioms two_encounter_composition_identity_germ
#print axioms two_encounter_three_flight_limit_flat
#print axioms sharp_two_encounter_coefficients
#print axioms sharp_two_encounter_defect

end

end QuadraticMobiusEncounter
