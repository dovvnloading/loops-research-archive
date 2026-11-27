import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# Winding parity of actual continuous square-root lifts

The integer is constructed from the exponential covering lift of the given
nonzero loop. It is not a separately supplied address or parity label.
-/

namespace LoopsSquarePathMonodromy

open Set Function Topology

noncomputable section

/-- Regard an actual nonzero complex path as a path in the punctured plane. -/
def nonzeroPath (γ : C(unitInterval, ℂ)) (hzero : ∀ t, γ t ≠ 0) :
    C(unitInterval, {z : ℂ // z ≠ 0}) :=
  ⟨fun t => ⟨γ t, hzero t⟩, γ.continuous.subtype_mk _⟩

/-- The actual exponential-cover lift, based at the principal logarithm of
the initial value. No choice of an integer is made here. -/
def logLift (γ : C(unitInterval, ℂ)) (hzero : ∀ t, γ t ≠ 0) :
    C(unitInterval, ℂ) :=
  Complex.isCoveringMap_exp.liftPath (nonzeroPath γ hzero) (Complex.log (γ 0))
    (by apply Subtype.ext; exact (Complex.exp_log (hzero 0)).symm)

theorem logLift_exp (γ : C(unitInterval, ℂ)) (hzero : ∀ t, γ t ≠ 0)
    (t : unitInterval) : Complex.exp (logLift γ hzero t) = γ t := by
  exact congrArg Subtype.val (congrFun
    (Complex.isCoveringMap_exp.liftPath_lifts (nonzeroPath γ hzero)
      (Complex.log (γ 0)) (by apply Subtype.ext; exact (Complex.exp_log (hzero 0)).symm)) t)

theorem logLift_zero (γ : C(unitInterval, ℂ)) (hzero : ∀ t, γ t ≠ 0) :
    logLift γ hzero 0 = Complex.log (γ 0) := by
  exact Complex.isCoveringMap_exp.liftPath_zero _ _ _

theorem exists_logLift_increment (γ : C(unitInterval, ℂ))
    (hzero : ∀ t, γ t ≠ 0) (hloop : γ 1 = γ 0) :
    ∃ n : ℤ, logLift γ hzero 1 = logLift γ hzero 0 +
      n * (2 * (Real.pi : ℂ) * Complex.I) := by
  apply Complex.exp_eq_exp_iff_exists_int.mp
  rw [logLift_exp, logLift_exp, hloop]

/-- The integer winding of a continuous nonzero loop, measured by the
increment of its exponential-cover lift. -/
def windingNumber (γ : C(unitInterval, ℂ)) (hzero : ∀ t, γ t ≠ 0)
    (hloop : γ 1 = γ 0) : ℤ :=
  (exists_logLift_increment γ hzero hloop).choose

theorem windingNumber_increment (γ : C(unitInterval, ℂ))
    (hzero : ∀ t, γ t ≠ 0) (hloop : γ 1 = γ 0) :
    logLift γ hzero 1 = logLift γ hzero 0 +
      windingNumber γ hzero hloop * (2 * (Real.pi : ℂ) * Complex.I) :=
  (exists_logLift_increment γ hzero hloop).choose_spec

/-- Every continuous logarithm has the same endpoint difference as the
canonical cover lift, independently of its starting logarithm. -/
theorem logarithm_increment_eq (γ L : C(unitInterval, ℂ))
    (hzero : ∀ t, γ t ≠ 0) (hexp : ∀ t, Complex.exp (L t) = γ t) :
    L 1 - L 0 = logLift γ hzero 1 - logLift γ hzero 0 := by
  let K : C(unitInterval, ℂ) :=
    ⟨fun t => L t - L 0 + Complex.log (γ 0), by fun_prop⟩
  have hKexp (t : unitInterval) : Complex.exp (K t) = γ t := by
    change Complex.exp (L t - L 0 + Complex.log (γ 0)) = γ t
    rw [Complex.exp_add, Complex.exp_sub, hexp t, hexp 0, Complex.exp_log (hzero 0)]
    exact div_mul_cancel₀ _ (hzero 0)
  have hK : (K : unitInterval → ℂ) = logLift γ hzero := by
    refine Complex.isCoveringMap_exp.eq_of_comp_eq K.continuous
      (logLift γ hzero).continuous ?_ (0 : unitInterval) ?_
    · funext t
      apply Subtype.ext
      exact (hKexp t).trans (logLift_exp γ hzero t).symm
    · change L 0 - L 0 + Complex.log (γ 0) = logLift γ hzero 0
      simp [logLift_zero]
  have h1 := congrFun hK 1
  have h0 := congrFun hK 0
  change L 1 - L 0 + Complex.log (γ 0) = _ at h1
  change L 0 - L 0 + Complex.log (γ 0) = _ at h0
  linear_combination h1 - h0

/-- Winding can be computed using any continuous logarithm of the actual
path, so its definition is independent of the initial logarithm. -/
theorem windingNumber_from_logarithm (γ L : C(unitInterval, ℂ))
    (hzero : ∀ t, γ t ≠ 0) (hloop : γ 1 = γ 0)
    (hexp : ∀ t, Complex.exp (L t) = γ t) :
    L 1 - L 0 = windingNumber γ hzero hloop *
      (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [logarithm_increment_eq γ L hzero hexp, windingNumber_increment γ hzero hloop]
  ring

/-- The two square-root lifts of the same nonzero path cannot switch
their sign at an intermediate time. -/
theorem square_lifts_eq_of_initial (γ η ρ : C(unitInterval, ℂ))
    (hzero : ∀ t, γ t ≠ 0) (hη : ∀ t, η t ^ 2 = γ t)
    (hρ : ∀ t, ρ t ^ 2 = γ t) (hstart : η 0 = ρ 0) : η = ρ := by
  have hηzero (t : unitInterval) : η t ≠ 0 := by
    intro h
    apply hzero t
    rw [← hη t, h]
    norm_num
  have hρzero (t : unitInterval) : ρ t ≠ 0 := by
    intro h
    apply hzero t
    rw [← hρ t, h]
    norm_num
  have he := (isCoveringMap_npow (𝕜 := ℂ) 2 (by norm_num)).eq_of_comp_eq
    (nonzeroPath η hηzero).continuous (nonzeroPath ρ hρzero).continuous
    (by funext t; apply Subtype.ext; exact (hη t).trans (hρ t).symm)
    (0 : unitInterval) (Subtype.ext hstart)
  apply ContinuousMap.ext
  intro t
  exact congrArg Subtype.val (congrFun he t)

/-- Exact endpoint monodromy of every supplied continuous square-root
lift of a nonzero loop. The exponent is the constructed winding integer. -/
theorem square_lift_endpoint (γ η : C(unitInterval, ℂ))
    (hzero : ∀ t, γ t ≠ 0) (hloop : γ 1 = γ 0)
    (hsquare : ∀ t, η t ^ 2 = γ t) :
    η 1 = (-1 : ℂ) ^ windingNumber γ hzero hloop * η 0 := by
  let L := logLift γ hzero
  let ρ : C(unitInterval, ℂ) :=
    ⟨fun t => η 0 * Complex.exp ((L t - L 0) / 2), by fun_prop⟩
  have hρ (t : unitInterval) : ρ t ^ 2 = γ t := by
    change (η 0 * Complex.exp ((L t - L 0) / 2)) ^ 2 = γ t
    rw [mul_pow, hsquare 0, ← Complex.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℂ) * ((L t - L 0) / 2) = L t - L 0 by ring,
      Complex.exp_sub, logLift_exp, logLift_exp]
    exact mul_div_cancel₀ _ (hzero 0)
  have heq : η = ρ := square_lifts_eq_of_initial γ η ρ hzero hsquare hρ (by
    change η 0 = η 0 * Complex.exp ((L 0 - L 0) / 2)
    simp)
  have hperiod : (L 1 - L 0) / 2 =
      (windingNumber γ hzero hloop : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    dsimp [L]
    rw [windingNumber_increment γ hzero hloop]
    ring
  calc
    η 1 = η 0 * Complex.exp ((L 1 - L 0) / 2) := congrArg (fun f : C(unitInterval, ℂ) => f 1) heq
    _ = η 0 * (-1 : ℂ) ^ windingNumber γ hzero hloop := by
      rw [hperiod, Complex.exp_int_mul, Complex.exp_pi_mul_I]
    _ = _ := mul_comm _ _

/-- A square-root lift closes exactly for even winding. -/
theorem square_lift_closed_iff_even (γ η : C(unitInterval, ℂ))
    (hzero : ∀ t, γ t ≠ 0) (hloop : γ 1 = γ 0)
    (hsquare : ∀ t, η t ^ 2 = γ t) :
    η 1 = η 0 ↔ Even (windingNumber γ hzero hloop) := by
  have hηzero : η 0 ≠ 0 := by
    intro h
    apply hzero 0
    rw [← hsquare 0, h]
    norm_num
  rw [square_lift_endpoint γ η hzero hloop hsquare,
    mul_eq_right₀ hηzero, neg_one_zpow_eq_ite]
  split_ifs with he
  · simp [he]
  · norm_num [he]

/-- A square-root lift ends on the opposite sheet exactly for odd winding. -/
theorem square_lift_endpoint_eq_neg_iff_odd (γ η : C(unitInterval, ℂ))
    (hzero : ∀ t, γ t ≠ 0) (hloop : γ 1 = γ 0)
    (hsquare : ∀ t, η t ^ 2 = γ t) :
    η 1 = -η 0 ↔ Odd (windingNumber γ hzero hloop) := by
  have hηzero : η 0 ≠ 0 := by
    intro h
    apply hzero 0
    rw [← hsquare 0, h]
    norm_num
  rw [square_lift_endpoint γ η hzero hloop hsquare]
  have hcancel : ((-1 : ℂ) ^ windingNumber γ hzero hloop) * η 0 = -η 0 ↔
      (-1 : ℂ) ^ windingNumber γ hzero hloop = -1 := by
    rw [← neg_one_mul (η 0)]
    exact mul_left_inj' hηzero
  rw [hcancel, neg_one_zpow_eq_ite]
  split_ifs with he
  · have hodd : ¬ Odd (windingNumber γ hzero hloop) := by
      simpa only [Int.not_odd_iff_even] using he
    norm_num [hodd]
  · have hodd : Odd (windingNumber γ hzero hloop) := Int.not_even_iff_odd.mp he
    simp [hodd]

end

end LoopsSquarePathMonodromy
