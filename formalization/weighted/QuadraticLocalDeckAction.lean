import QuadraticLocalFiberCensus

/-!
# Analytic cyclic sheet actions for actual quadratic iterates

Every finite quadratic iterate has a physical disk chart. Conjugating
root-of-unity rotations through that chart constructs all local sheet
symmetries, including at repeated critical encounters. Their action is
free away from the anchor, and its orbits are the complete local fibers.
-/

namespace LoopsQuadraticLocalDeckAction

open Set Function Filter
open scoped Topology
open QuadraticEscape LoopsTelescopeRamification LoopsQuadraticPowerNormalForm

/-- A normalized analytic power chart on one actual open source
neighborhood. The inverse coordinate is defined on the entire round
disk, so every root-of-unity rotation stays in the same chart. -/
structure PowerChart (f : ℂ → ℂ) (x : ℂ) (m : ℕ) where
  a : ℂ
  r : ℝ
  source : Set ℂ
  coord : ℂ → ℂ
  inv : ℂ → ℂ
  degree_pos : 0 < m
  a_ne_zero : a ≠ 0
  radius_pos : 0 < r
  isOpen_source : IsOpen source
  mem_source : x ∈ source
  coord_center : coord x = 0
  coord_deriv : HasDerivAt coord 1 x
  coord_mapsTo : MapsTo coord source (Metric.ball (0 : ℂ) r)
  inv_mapsTo : MapsTo inv (Metric.ball (0 : ℂ) r) source
  left_inv : LeftInvOn inv coord source
  right_inv : RightInvOn inv coord (Metric.ball (0 : ℂ) r)
  coord_analytic : AnalyticOnNhd ℂ coord source
  inv_analytic : AnalyticOnNhd ℂ inv (Metric.ball (0 : ℂ) r)
  normal_form : ∀ z ∈ source, f z - f x = a * (coord z)^m

/-- The generic chart is constructed for the genuine polynomial
iterate with its orbit-derived local multiplicity. -/
theorem exists_quadratic_powerChart (c x : ℂ) (n : ℕ) :
    Nonempty (PowerChart (orbit c n) x (2^criticalVisits c x n)) := by
  obtain ⟨a, r, U, φ, χ, ha, hr, hU, hxU, hφ0, hφd,
      hmapφ, hmapχ, hleft, hright, hφa, hχa, hform⟩ :=
    quadratic_power_disk_chart c x n
  exact ⟨⟨a, r, U, φ, χ, by positivity, ha, hr, hU, hxU,
    hφ0, hφd, hmapφ, hmapχ, hleft, hright, hφa, hχa, hform⟩⟩

namespace PowerChart

variable {f : ℂ → ℂ} {x : ℂ} {m : ℕ} (C : PowerChart f x m)

/-- A rotation in the analytic coordinate, transported back into
the physical source plane. -/
def deck (ζ z : ℂ) : ℂ := C.inv (ζ * C.coord z)

theorem inv_zero : C.inv 0 = x := by
  simpa only [C.coord_center] using C.left_inv C.mem_source

theorem coord_injOn : InjOn C.coord C.source := by
  intro z hz w hw he
  calc
    z = C.inv (C.coord z) := (C.left_inv hz).symm
    _ = C.inv (C.coord w) := congrArg C.inv he
    _ = w := C.left_inv hw

theorem coord_eq_zero_iff (z : ℂ) (hz : z ∈ C.source) :
    C.coord z = 0 ↔ z = x := by
  constructor
  · intro he
    exact C.coord_injOn hz C.mem_source (he.trans C.coord_center.symm)
  · rintro rfl
    exact C.coord_center

/-- Every complex root of unity has modulus one. The positive degree
is retained explicitly, including the unramified degree-one case. -/
theorem root_norm (ζ : ℂ) (hζ : ζ^m = 1) : ‖ζ‖ = 1 := by
  have hp : ‖ζ‖^m = 1 := by
    simpa only [norm_pow, norm_one] using congrArg norm hζ
  have hm : m ≠ 0 := Nat.ne_of_gt C.degree_pos
  apply le_antisymm
  · by_contra! h
    have ht := one_lt_pow₀ h hm
    rw [hp] at ht
    exact (lt_irrefl (1 : ℝ)) ht
  · by_contra! h
    have ht := pow_lt_one₀ (norm_nonneg ζ) h hm
    rw [hp] at ht
    exact (lt_irrefl (1 : ℝ)) ht

theorem root_mul_mem_ball (ζ z : ℂ) (hζ : ζ^m = 1)
    (hz : z ∈ Metric.ball (0 : ℂ) C.r) :
    ζ*z ∈ Metric.ball (0 : ℂ) C.r := by
  simpa only [Metric.mem_ball, dist_zero_right, norm_mul,
    C.root_norm ζ hζ, one_mul] using hz

theorem deck_mem (ζ z : ℂ) (hζ : ζ^m = 1) (hz : z ∈ C.source) :
    C.deck ζ z ∈ C.source :=
  C.inv_mapsTo (C.root_mul_mem_ball ζ (C.coord z) hζ (C.coord_mapsTo hz))

theorem deck_coord (ζ z : ℂ) (hζ : ζ^m = 1) (hz : z ∈ C.source) :
    C.coord (C.deck ζ z) = ζ*C.coord z :=
  C.right_inv (C.root_mul_mem_ball ζ (C.coord z) hζ (C.coord_mapsTo hz))

theorem deck_one (z : ℂ) (hz : z ∈ C.source) : C.deck 1 z = z := by
  simpa only [deck, one_mul] using C.left_inv hz

/-- Multiplication of phases is composition of the actual analytic
source maps; no abstract sheet permutation is supplied as an input. -/
theorem deck_mul (ζ η z : ℂ) (hη : η^m = 1) (hz : z ∈ C.source) :
    C.deck (ζ*η) z = C.deck ζ (C.deck η z) := by
  change C.inv ((ζ*η)*C.coord z) = C.inv (ζ*C.coord (C.deck η z))
  rw [C.deck_coord η z hη hz, mul_assoc]

theorem deck_center (ζ : ℂ) : C.deck ζ x = x := by
  simp only [deck, C.coord_center, mul_zero, C.inv_zero]

theorem deck_preserves (ζ z : ℂ) (hζ : ζ^m = 1) (hz : z ∈ C.source) :
    f (C.deck ζ z) = f z := by
  have he := C.normal_form (C.deck ζ z) (C.deck_mem ζ z hζ hz)
  rw [C.deck_coord ζ z hζ hz, mul_pow, hζ, one_mul] at he
  have hzform := C.normal_form z hz
  linear_combination he - hzform

/-- The constructed source symmetries are analytic throughout their
common physical neighborhood. -/
theorem deck_analytic (ζ : ℂ) (hζ : ζ^m = 1) :
    AnalyticOnNhd ℂ (C.deck ζ) C.source := by
  intro z hz
  have hb := C.root_mul_mem_ball ζ (C.coord z) hζ (C.coord_mapsTo hz)
  exact (C.inv_analytic _ hb).comp
    (f := fun w : ℂ => ζ*C.coord w) (x := z)
    (analyticAt_const.mul (C.coord_analytic z hz))

theorem inv_deriv_zero : HasDerivAt C.inv 1 0 := by
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) C.r := Metric.mem_ball_self C.radius_pos
  have hi := (C.inv_analytic 0 h0).differentiableAt.hasDerivAt
  have hic : HasDerivAt C.inv (deriv C.inv 0) (C.coord x) := by
    simpa only [C.coord_center] using hi
  have hcomp := hic.comp x C.coord_deriv
  have hid : (fun z => C.inv (C.coord z)) =ᶠ[𝓝 x] (id : ℂ → ℂ) := by
    filter_upwards [C.isOpen_source.mem_nhds C.mem_source] with z hz
    exact C.left_inv hz
  have he := hcomp.unique ((hasDerivAt_id x).congr_of_eventuallyEq hid)
  have hd : deriv C.inv 0 = 1 := by simpa only [mul_one] using he
  exact hi.congr_deriv hd

/-- The phase is exactly the derivative at the anchor; this will also
distinguish every constructed local sheet symmetry. -/
theorem deck_deriv_center (ζ : ℂ) : HasDerivAt (C.deck ζ) ζ x := by
  have hi : HasDerivAt C.inv 1 (ζ*C.coord x) := by
    simpa only [C.coord_center, mul_zero] using C.inv_deriv_zero
  have hd := hi.comp x (C.coord_deriv.const_mul ζ)
  simpa only [deck, one_mul, mul_one] using hd

/-- Every nonidentity phase has only the branch anchor as a fixed
point. This holds for arbitrary repeated critical encounters. -/
theorem deck_fixed_iff (ζ z : ℂ) (hζ : ζ^m = 1) (hz : z ∈ C.source) :
    C.deck ζ z = z ↔ ζ = 1 ∨ z = x := by
  constructor
  · intro he
    have hc := C.deck_coord ζ z hζ hz
    rw [he] at hc
    have hp : (ζ-1)*C.coord z = 0 := by linear_combination -hc
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr ((C.coord_eq_zero_iff z hz).mp h)
  · rintro (rfl | rfl)
    · exact C.deck_one z hz
    · exact C.deck_center ζ

/-- All and only the points in a physical local iterate fiber differ
by one root-of-unity phase in the constructed analytic coordinates. -/
theorem same_fiber_iff_deck (z w : ℂ) (hz : z ∈ C.source) (hw : w ∈ C.source) :
    f w = f z ↔ ∃ ζ : ℂ, ζ^m = 1 ∧ C.deck ζ z = w := by
  constructor
  · intro he
    have hp : (C.coord w)^m = (C.coord z)^m := by
      apply mul_left_cancel₀ C.a_ne_zero
      rw [← C.normal_form w hw, ← C.normal_form z hz, he]
    by_cases hz0 : C.coord z = 0
    · have hw0 : C.coord w = 0 := by
        have hp0 : (C.coord w)^m = 0 := by
          rw [hp, hz0, zero_pow (Nat.ne_of_gt C.degree_pos)]
        by_contra hn
        exact pow_ne_zero m hn hp0
      have hzx := (C.coord_eq_zero_iff z hz).mp hz0
      have hwx := (C.coord_eq_zero_iff w hw).mp hw0
      exact ⟨1, one_pow m, (C.deck_one z hz).trans (hzx.trans hwx.symm)⟩
    · refine ⟨C.coord w/C.coord z, ?_, ?_⟩
      · rw [div_pow, hp, div_self (pow_ne_zero m hz0)]
      · change C.inv ((C.coord w/C.coord z)*C.coord z) = w
        rw [div_mul_cancel₀ _ hz0]
        exact C.left_inv hw
  · rintro ⟨ζ, hζ, rfl⟩
    exact C.deck_preserves ζ z hζ hz

/-- At every noncentral source point the phase reaching another
point is unique. Thus the root-of-unity action on each noncentral
fiber is free and transitive, not merely a surjective enumeration. -/
theorem deck_phase_unique (ζ η z : ℂ) (hζ : ζ^m = 1) (hη : η^m = 1)
    (hz : z ∈ C.source) (hzx : z ≠ x) :
    C.deck ζ z = C.deck η z ↔ ζ = η := by
  constructor
  · intro he
    have hc := congrArg C.coord he
    rw [C.deck_coord ζ z hζ hz, C.deck_coord η z hη hz] at hc
    exact mul_right_cancel₀ (fun h => hzx ((C.coord_eq_zero_iff z hz).mp h)) hc
  · rintro rfl
    rfl

/-- Every repeated application of one phase is the corresponding
power of that phase on the same physical source neighborhood. -/
theorem deck_iterate (ζ z : ℂ) (hζ : ζ^m = 1) (hz : z ∈ C.source) (k : ℕ) :
    (C.deck ζ)^[k] z = C.deck (ζ^k) z := by
  induction k with
  | zero => exact (C.deck_one z hz).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    exact (C.deck_mul ζ (ζ^k) z (by rw [← pow_mul, Nat.mul_comm k m, pow_mul, hζ, one_pow]) hz).symm

/-- The local action has finite period equal to a divisor of the
actual local degree; individual phases retain their exact power. -/
theorem deck_iterate_degree (ζ z : ℂ) (hζ : ζ^m = 1) (hz : z ∈ C.source) :
    (C.deck ζ)^[m] z = z := by
  rw [C.deck_iterate ζ z hζ hz m, hζ, C.deck_one z hz]

/-- The canonical primitive phase in the normalized local coordinate. -/
noncomputable def phaseGenerator (_C : PowerChart f x m) : ℂ :=
  Complex.exp (2*Real.pi*Complex.I/(m : ℂ))

theorem phaseGenerator_primitive : IsPrimitiveRoot C.phaseGenerator m :=
  Complex.isPrimitiveRoot_exp m (Nat.ne_of_gt C.degree_pos)

/-- Every permissible local phase is a power of the one explicit
primitive phase, with an index strictly below the local degree. -/
theorem phase_eq_generator_power (ζ : ℂ) (hζ : ζ^m = 1) :
    ∃ i < m, C.phaseGenerator^i = ζ := by
  letI : NeZero m := ⟨Nat.ne_of_gt C.degree_pos⟩
  exact C.phaseGenerator_primitive.eq_pow_of_pow_eq_one hζ

/-- The analytic generator has exact order m at every noncentral
point: return times are precisely the multiples of the local degree. -/
theorem generator_period_iff (z : ℂ) (hz : z ∈ C.source) (hzx : z ≠ x) (k : ℕ) :
    (C.deck C.phaseGenerator)^[k] z = z ↔ m ∣ k := by
  have hp := C.phaseGenerator_primitive.pow_eq_one
  have hpk : (C.phaseGenerator^k)^m = 1 := by
    rw [← pow_mul, Nat.mul_comm k m, pow_mul, hp, one_pow]
  rw [C.deck_iterate C.phaseGenerator z hp hz k,
    C.deck_fixed_iff (C.phaseGenerator^k) z hpk hz]
  simp only [hzx, or_false]
  exact C.phaseGenerator_primitive.pow_eq_one_iff_dvd k

/-- Every analytic phase constructed by the chart is one of the
first m iterates of the explicit cyclic generator. -/
theorem deck_eq_generator_iterate (ζ : ℂ) (hζ : ζ^m = 1) :
    ∃ i < m, ∀ z ∈ C.source,
      C.deck ζ z = (C.deck C.phaseGenerator)^[i] z := by
  obtain ⟨i, hi, hp⟩ := C.phase_eq_generator_power ζ hζ
  refine ⟨i, hi, ?_⟩
  intro z hz
  rw [C.deck_iterate C.phaseGenerator z C.phaseGenerator_primitive.pow_eq_one hz i, hp]

/-- One explicit analytic cyclic generator traverses every complete
local fiber, with no missing inverse points. -/
theorem same_fiber_iff_generator_iterate (z w : ℂ)
    (hz : z ∈ C.source) (hw : w ∈ C.source) :
    f w = f z ↔ ∃ i < m, (C.deck C.phaseGenerator)^[i] z = w := by
  constructor
  · intro hf
    obtain ⟨ζ, hζ, hzw⟩ := (C.same_fiber_iff_deck z w hz hw).mp hf
    obtain ⟨i, hi, he⟩ := C.deck_eq_generator_iterate ζ hζ
    exact ⟨i, hi, (he z hz).symm.trans hzw⟩
  · rintro ⟨i, hi, hzw⟩
    apply (C.same_fiber_iff_deck z w hz hw).mpr
    have hp := C.phaseGenerator_primitive.pow_eq_one
    refine ⟨C.phaseGenerator^i, ?_, ?_⟩
    · rw [← pow_mul, Nat.mul_comm i m, pow_mul, hp, one_pow]
    · rw [← C.deck_iterate C.phaseGenerator z hp hz i]
      exact hzw

end PowerChart

end LoopsQuadraticLocalDeckAction
