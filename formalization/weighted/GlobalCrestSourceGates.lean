import ActualCrestCrossingWindow
import LimitingCrestArcGates

/-!
# The actual source cuts on every retained crest radius

These estimates concern the literal normalized quadratic return and its
real iterates.  They supply the eight real inequalities called `other_gates`
in the source crest verifier, on the entire enclosing terminal collar.
They do not identify marked accesses or a KKL curve family.
-/

namespace GlobalCrestSourceGates

open Set Function LimitingCrest LimitingCrestQuadraticReturn
open NearTwoTip NearTwoShooting QuadraticCrestDividedDifference
open LoopsLimitingCrestParameter

noncomputable section

/-- The restriction of the actual normalized polynomial to the real line. -/
def actualMap (c : ℝ) (p : ℕ) (x : ℝ) : ℝ :=
  (normalizedReturn c p (x : ℂ)).re

/-- Complete real iterates of the actual normalized return. -/
def actualOrbit (c : ℝ) (p : ℕ) (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n+1 => actualMap c p (actualOrbit c p x n)

private theorem actualMap_cast (c x : ℝ) (p : ℕ) :
    (actualMap c p x : ℂ) = normalizedReturn c p (x : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, ActualCrestCrossingWindow.normalizedReturn_real]

/-- No replacement real dynamics is introduced by `actualOrbit`. -/
theorem actualOrbit_cast (c x : ℝ) (p n : ℕ) :
    (actualOrbit c p x n : ℂ) = ((normalizedReturn c p)^[n]) (x : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [actualOrbit, actualMap_cast, iterate_succ_apply', ih]

/-- The real-return coordinates describe literal iterates in the original
dynamical plane, with the same positive critical scale. -/
theorem actualOrbit_physical (c x : ℝ) (p n : ℕ)
    (hd : 0 < criticalValue c p) :
    ((quadraticMap c)^[n*p]) ((criticalValue c p : ℂ)*(x : ℂ)) =
      ((criticalValue c p*actualOrbit c p x n : ℝ) : ℂ) := by
  rw [← normalized_iterate_scale c p hd.ne' n (x : ℂ), ← actualOrbit_cast]
  simp only [Complex.ofReal_mul]

private theorem real_error {p : ℕ} (hp : 17 ≤ p) {c x : ℝ}
    (hc : ActualTip p c) (hx : |x| ≤ 23/20) :
    |actualMap c p x-realMap (kappa p c) x| ≤ 1/100000000 := by
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  have herr := normalized_return_error c p (by omega)
    hc.2.2.2.2.2.2 hc.2.1 hsmall (x : ℂ)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx)
  have hpow : (17179869184 : ℝ) ≤ (4 : ℝ)^p := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hp
    norm_num at h
    exact h
  have he : (24 : ℝ)/(4 : ℝ)^p ≤ 1/100000000 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4^p)).mpr
    linarith
  have hre := (Complex.abs_re_le_norm
    (normalizedReturn c p (x : ℂ)-complexMap (kappa p c) (x : ℂ))).trans herr
  simpa only [complexMap_real, Complex.sub_re, Complex.ofReal_re, actualMap]
    using hre.trans he

private theorem step_sq {p : ℕ} (hp : 17 ≤ p) {c x a b l u : ℝ}
    (hc : ActualTip p c) (hxd : |x| ≤ 23/20)
    (hx : a ≤ x^2 ∧ x^2 ≤ b) (ha : 0 ≤ a)
    (hl : l ≤ 1-(17904/10000)*b-1/100000000)
    (hu : 1-(17903/10000)*a+1/100000000 ≤ u) :
    actualMap c p x ∈ Icc l u := by
  have hk := hc.2.2.2.1
  have hlo := mul_le_mul hk.1 hx.1 ha (by linarith [hk.1])
  have hhi := mul_le_mul hk.2 hx.2 (sq_nonneg x) (by norm_num)
  have he := abs_le.mp (real_error hp hc hxd)
  dsimp [realMap] at he
  constructor <;> linarith

private theorem step_pos {p : ℕ} (hp : 17 ≤ p) {c x a b l u : ℝ}
    (hc : ActualTip p c) (hx : x ∈ Icc a b)
    (ha : 0 ≤ a) (hb : b ≤ 23/20)
    (hl : l ≤ 1-(17904/10000)*b^2-1/100000000)
    (hu : 1-(17903/10000)*a^2+1/100000000 ≤ u) :
    actualMap c p x ∈ Icc l u := by
  apply step_sq hp hc
    (abs_le.mpr ⟨by linarith [hx.1], hx.2.trans hb⟩)
    ⟨pow_le_pow_left₀ ha hx.1 2,
      pow_le_pow_left₀ (ha.trans hx.1) hx.2 2⟩ (sq_nonneg a) hl hu

private theorem step_neg {p : ℕ} (hp : 17 ≤ p) {c x a b l u : ℝ}
    (hc : ActualTip p c) (hx : x ∈ Icc a b)
    (ha : -(23/20) ≤ a) (hb : b ≤ 0)
    (hl : l ≤ 1-(17904/10000)*a^2-1/100000000)
    (hu : 1-(17903/10000)*b^2+1/100000000 ≤ u) :
    actualMap c p x ∈ Icc l u := by
  have hs : b^2 ≤ x^2 ∧ x^2 ≤ a^2 := by
    constructor
    · simpa only [neg_sq] using
        pow_le_pow_left₀ (neg_nonneg.mpr hb) (neg_le_neg hx.2) 2
    · simpa only [neg_sq] using
        pow_le_pow_left₀ (neg_nonneg.mpr (hx.2.trans hb)) (neg_le_neg hx.1) 2
  exact step_sq hp hc
    (abs_le.mpr ⟨ha.trans hx.1, by linarith [hx.2]⟩) hs (sq_nonneg b) hl hu

private theorem actualMap_continuous (c : ℝ) (p : ℕ) :
    Continuous (actualMap c p) :=
  Complex.continuous_re.comp
    ((ActualCrestCrossingWindow.normalizedReturn_continuous c p).comp
      Complex.continuous_ofReal)

private theorem actualMap_injective_nonnegative {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : InjOn (actualMap c p) (Icc 0 (23/20)) := by
  intro x hx y hy he
  have hband := parameter_band hp hc.1
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  have heC : normalizedReturn c p (x : ℂ) = normalizedReturn c p (y : ℂ) := by
    rw [← actualMap_cast, ← actualMap_cast, he]
  have hcol := (normalized_return_collision_iff c p (by omega)
    ⟨hband.1, by linarith [hband.2]⟩ hc.2.1 hsmall hc.2.2.2.1
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy.1] using hy.2)).mp heC
  rcases hcol with h | h
  · exact Complex.ofReal_injective h
  · have hreal := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re] at hreal
    linarith [hx.1, hy.1]

private theorem actualMap_strictAnti {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : StrictAntiOn (actualMap c p) (Icc 0 (23/20)) := by
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc' (by norm_num : (0 : ℝ) ≤ 23/20)
    (actualMap_continuous c p).continuousOn (actualMap_injective_nonnegative hp hc)
    with hmono | hanti
  · have hm := hmono (show (0 : ℝ) ∈ Icc 0 (23/20) by norm_num)
      (show (1 : ℝ) ∈ Icc 0 (23/20) by norm_num) (by norm_num)
    have he0 := abs_le.mp (real_error hp hc (x := 0) (by norm_num))
    have he1 := abs_le.mp (real_error hp hc (x := 1) (by norm_num))
    have hk := hc.2.2.2.1
    norm_num [realMap] at he0 he1
    exact (by linarith [hk.1] : False).elim
  · exact hanti

/-- The actual positive fixed cut is constructed, quantitatively located,
and unique throughout the positive part of the approximation disk. -/
theorem actual_positive_fixed_cut {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    ∃ α : ℝ, α ∈ Ioo (518/1000 : ℝ) (519/1000) ∧
      normalizedReturn c p (α : ℂ) = (α : ℂ) ∧
      ∀ β ∈ Icc (0 : ℝ) (23/20),
        normalizedReturn c p (β : ℂ) = (β : ℂ) → β = α := by
  let g : ℝ → ℝ := fun x => actualMap c p x-x
  have hk := hc.2.2.2.1
  have heL := abs_le.mp (real_error hp hc (x := 518/1000) (by norm_num))
  have heU := abs_le.mp (real_error hp hc (x := 519/1000) (by norm_num))
  have hL : 0 < g (518/1000) := by
    dsimp [g, realMap] at *
    nlinarith [hk.2]
  have hU : g (519/1000) < 0 := by
    dsimp [g, realMap] at *
    nlinarith [hk.1]
  have hcont : Continuous g := (actualMap_continuous c p).sub continuous_id
  obtain ⟨α,hα,hzero⟩ := intermediate_value_Icc'
    (by norm_num : (518/1000 : ℝ) ≤ 519/1000) hcont.continuousOn ⟨hU.le,hL.le⟩
  have hfix : actualMap c p α = α := sub_eq_zero.mp hzero
  have ha : α ∈ Ioo (518/1000 : ℝ) (519/1000) := by
    constructor
    · apply lt_of_le_of_ne hα.1
      intro he
      rw [he, hzero] at hL
      exact (lt_irrefl _ hL)
    · apply lt_of_le_of_ne hα.2
      intro he
      rw [← he, hzero] at hU
      exact (lt_irrefl _ hU)
  have hαD : α ∈ Icc (0 : ℝ) (23/20) := by constructor <;> linarith [ha.1,ha.2]
  refine ⟨α,ha,by rw [← actualMap_cast,hfix],?_⟩
  intro β hβ hβfix
  have hb : actualMap c p β = β := by
    simpa only [actualMap, Complex.ofReal_re] using congrArg Complex.re hβfix
  have hm := actualMap_strictAnti hp hc
  rcases lt_trichotomy β α with hlt | he | hgt
  · have hh := hm hβ hαD hlt
    rw [hfix,hb] at hh
    linarith
  · exact he
  · have hh := hm hαD hβ hgt
    rw [hfix,hb] at hh
    linarith

private structure CriticalBounds (c : ℝ) (p : ℕ) : Prop where
  c2 : actualOrbit c p 0 2 ∈ Icc (-790401/1000000) (-790299/1000000)
  c3 : actualOrbit c p 0 3 ∈ Icc (-119/1000) (-117/1000)
  c4 : actualOrbit c p 0 4 ∈ Icc (9746/10000) (9756/10000)
  c5 : actualOrbit c p 0 5 ∈ Icc (-705/1000) (-700/1000)
  c6 : actualOrbit c p 0 6 ∈ Icc (110/1000) (123/1000)

private theorem critical_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : CriticalBounds c p := by
  have c0 : (0 : ℝ) ∈ Icc 0 0 := ⟨le_rfl,le_rfl⟩
  have c1 : actualOrbit c p 0 1 ∈ Icc (99999999/100000000) (100000001/100000000) :=
    step_pos hp hc c0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c2 : actualOrbit c p 0 2 ∈ Icc (-790401/1000000) (-790299/1000000) :=
    step_pos hp hc c1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c3 : actualOrbit c p 0 3 ∈ Icc (-119/1000) (-117/1000) :=
    step_neg hp hc c2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c4 : actualOrbit c p 0 4 ∈ Icc (9746/10000) (9756/10000) :=
    step_neg hp hc c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c5 : actualOrbit c p 0 5 ∈ Icc (-705/1000) (-700/1000) :=
    step_pos hp hc c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c6 : actualOrbit c p 0 6 ∈ Icc (110/1000) (123/1000) :=
    step_neg hp hc c5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨c2,c3,c4,c5,c6⟩

private structure EndpointBounds (c : ℝ) (p : ℕ) (s : ℝ) : Prop where
  q1 : actualOrbit c p (qEndpoint s) 1 ∈ Icc (1537/10000) (1637/10000)
  q2 : actualOrbit c p (qEndpoint s) 2 ∈ Icc (952/1000) (958/1000)
  q3 : actualOrbit c p (qEndpoint s) 3 ∈ Icc (-644/1000) (-622/1000)
  q4 : actualOrbit c p (qEndpoint s) 4 ∈ Icc (257/1000) (308/1000)
  w1 : actualOrbit c p (wEndpoint s) 1 ∈ Icc (-1937/10000) (-1818/10000)
  w2 : actualOrbit c p (wEndpoint s) 2 ∈ Icc (932/1000) (942/1000)

private theorem endpoint_bounds {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) :
    EndpointBounds c p s := by
  have q0 : qEndpoint s ∈ Icc (-6875/10000) (-6835/10000) := by
    dsimp [qEndpoint]; constructor <;> linarith [hs.1,hs.2]
  have w0 : wEndpoint s ∈ Icc (-8165/10000) (-8125/10000) := by
    dsimp [wEndpoint]; constructor <;> linarith [hs.1,hs.2]
  have q1 : actualOrbit c p (qEndpoint s) 1 ∈ Icc (1537/10000) (1637/10000) :=
    step_neg hp hc q0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q2 : actualOrbit c p (qEndpoint s) 2 ∈ Icc (952/1000) (958/1000) :=
    step_pos hp hc q1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q3 : actualOrbit c p (qEndpoint s) 3 ∈ Icc (-644/1000) (-622/1000) :=
    step_pos hp hc q2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have q4 : actualOrbit c p (qEndpoint s) 4 ∈ Icc (257/1000) (308/1000) :=
    step_neg hp hc q3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have w1 : actualOrbit c p (wEndpoint s) 1 ∈ Icc (-1937/10000) (-1818/10000) :=
    step_neg hp hc w0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have w2 : actualOrbit c p (wEndpoint s) 2 ∈ Icc (932/1000) (942/1000) :=
    step_neg hp hc w1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨q1,q2,q3,q4,w1,w2⟩

/-- The exact eight source real-cut tests.  Every cut and endpoint is an
iterate of the actual normalized polynomial. -/
def ActualEndpointGates (c : ℝ) (p : ℕ) (s α : ℝ) : Prop :=
  qEndpoint s ∈ Ioo (actualOrbit c p 0 5) (-α) ∧
  wEndpoint s ∈ Ioo (-actualOrbit c p 0 4) (actualOrbit c p 0 2) ∧
  actualOrbit c p (qEndpoint s) 1 ∈ Ioo (actualOrbit c p 0 6) α ∧
  actualOrbit c p (wEndpoint s) 1 ∈ Ioo (-α) (actualOrbit c p 0 3) ∧
  actualOrbit c p (qEndpoint s) 2 ∈ Ioo (-actualOrbit c p 0 2) (actualOrbit c p 0 4) ∧
  actualOrbit c p (wEndpoint s) 2 ∈ Ioo (-actualOrbit c p 0 2) (actualOrbit c p 0 4) ∧
  actualOrbit c p (qEndpoint s) 3 ∈ Ioo (actualOrbit c p 0 5) (-α) ∧
  actualOrbit c p (qEndpoint s) 4 ∈ Ioo (actualOrbit c p 0 6) α

/-- Every real source gate survives on the whole enclosing retained
collar, uniformly from period seventeen onward. -/
theorem actual_endpoint_gates {p : ℕ} (hp : 17 ≤ p) {c s α : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Icc (1/16 : ℝ) (133/2000))
    (hα : α ∈ Ioo (518/1000 : ℝ) (519/1000)) :
    ActualEndpointGates c p s α := by
  rcases critical_bounds hp hc with ⟨⟨c2l,c2u⟩,⟨c3l,c3u⟩,⟨c4l,c4u⟩,
    ⟨c5l,c5u⟩,⟨c6l,c6u⟩⟩
  rcases endpoint_bounds hp hc hs with ⟨⟨q1l,q1u⟩,⟨q2l,q2u⟩,⟨q3l,q3u⟩,
    ⟨q4l,q4u⟩,⟨w1l,w1u⟩,⟨w2l,w2u⟩⟩
  rcases hα with ⟨al,au⟩
  rcases hs with ⟨sl,su⟩
  unfold ActualEndpointGates
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,
    ⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    dsimp [qEndpoint,wEndpoint] at * <;> linarith

/-- One constructed actual fixed cut works simultaneously for all
retained radii and all eight endpoint comparisons. -/
theorem actual_complete_endpoint_gates {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    ∃ α : ℝ, α ∈ Ioo (518/1000 : ℝ) (519/1000) ∧
      normalizedReturn c p (α : ℂ) = (α : ℂ) ∧
      (∀ β ∈ Icc (0 : ℝ) (23/20),
        normalizedReturn c p (β : ℂ) = (β : ℂ) → β = α) ∧
      ∀ s ∈ Icc (1/16 : ℝ) (133/2000), ActualEndpointGates c p s α := by
  obtain ⟨α,hα,hfix,hunique⟩ := actual_positive_fixed_cut hp hc
  exact ⟨α,hα,hfix,hunique,fun s hs => actual_endpoint_gates hp hc hs hα⟩

end
end GlobalCrestSourceGates
