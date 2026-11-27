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

/-- An independently computed logarithmic increment determines the
constructed integer uniquely. -/
theorem windingNumber_eq_of_logarithm_increment (γ L : C(unitInterval, ℂ))
    (hzero : ∀ t, γ t ≠ 0) (hloop : γ 1 = γ 0)
    (hexp : ∀ t, Complex.exp (L t) = γ t) (n : ℤ)
    (hincrement : L 1 - L 0 = n * (2 * (Real.pi : ℂ) * Complex.I)) :
    windingNumber γ hzero hloop = n := by
  have hperiod : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hmul := (windingNumber_from_logarithm γ L hzero hloop hexp).symm.trans hincrement
  exact_mod_cast mul_right_cancel₀ hperiod hmul

/-- Endpoint-preserving homotopy in the actual punctured plane preserves
the integer, not only its parity. -/
theorem windingNumber_homotopic (γ δ : C(unitInterval, ℂ))
    (hγ : ∀ t, γ t ≠ 0) (hδ : ∀ t, δ t ≠ 0)
    (hγloop : γ 1 = γ 0) (hδloop : δ 1 = δ 0)
    (hhom : (nonzeroPath γ hγ).HomotopicRel (nonzeroPath δ hδ) {0, 1}) :
    windingNumber γ hγ hγloop = windingNumber δ hδ hδloop := by
  have hbase : γ 0 = δ 0 := congrArg Subtype.val (hhom.fst_eq_snd (by simp))
  have hend : logLift γ hγ 1 = logLift δ hδ 1 := by
    unfold logLift
    have hlift := Complex.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel
      hhom (Complex.log (δ 0))
      (by apply Subtype.ext; change γ 0 = Complex.exp (Complex.log (δ 0))
          rw [hbase, Complex.exp_log (hδ 0)])
      (by apply Subtype.ext; exact (Complex.exp_log (hδ 0)).symm)
    simpa only [hbase] using hlift
  apply windingNumber_eq_of_logarithm_increment γ (logLift γ hγ) hγ hγloop
    (logLift_exp γ hγ)
  rw [hend, logLift_zero, hbase, ← logLift_zero δ hδ,
    windingNumber_increment δ hδ hδloop]
  ring

/-- Multiplying actual nonzero loops adds their winding integers. -/
theorem windingNumber_mul (γ δ : C(unitInterval, ℂ))
    (hγ : ∀ t, γ t ≠ 0) (hδ : ∀ t, δ t ≠ 0)
    (hγloop : γ 1 = γ 0) (hδloop : δ 1 = δ 0) :
    windingNumber (γ * δ) (fun t => mul_ne_zero (hγ t) (hδ t))
      (by change γ 1 * δ 1 = γ 0 * δ 0; rw [hγloop, hδloop]) =
      windingNumber γ hγ hγloop + windingNumber δ hδ hδloop := by
  let L : C(unitInterval, ℂ) := logLift γ hγ + logLift δ hδ
  apply windingNumber_eq_of_logarithm_increment (γ * δ) L
  · intro t
    change Complex.exp (logLift γ hγ t + logLift δ hδ t) = γ t * δ t
    rw [Complex.exp_add, logLift_exp, logLift_exp]
  · change (logLift γ hγ 1 + logLift δ hδ 1) -
      (logLift γ hγ 0 + logLift δ hδ 0) = _
    rw [windingNumber_increment γ hγ hγloop, windingNumber_increment δ hδ hδloop]
    push_cast
    ring

/-- Pointwise integer powers are continuous because the path avoids zero. -/
def zpowPath (γ : C(unitInterval, ℂ)) (hzero : ∀ t, γ t ≠ 0) (n : ℤ) :
    C(unitInterval, ℂ) :=
  ⟨fun t => γ t ^ n, γ.continuous.zpow₀ n (fun t => Or.inl (hzero t))⟩

/-- All integer powers, including reciprocal paths, multiply the
winding integer by their exponent. -/
theorem windingNumber_zpow (γ : C(unitInterval, ℂ))
    (hzero : ∀ t, γ t ≠ 0) (hloop : γ 1 = γ 0) (n : ℤ) :
    windingNumber (zpowPath γ hzero n) (fun t => zpow_ne_zero n (hzero t))
      (by change γ 1 ^ n = γ 0 ^ n; rw [hloop]) =
      n * windingNumber γ hzero hloop := by
  let L : C(unitInterval, ℂ) :=
    ⟨fun t => (n : ℂ) * logLift γ hzero t, by fun_prop⟩
  apply windingNumber_eq_of_logarithm_increment (zpowPath γ hzero n) L
  · intro t
    change Complex.exp ((n : ℂ) * logLift γ hzero t) = γ t ^ n
    rw [Complex.exp_int_mul, logLift_exp]
  · change (n : ℂ) * logLift γ hzero 1 - (n : ℂ) * logLift γ hzero 0 = _
    rw [windingNumber_increment γ hzero hloop]
    push_cast
    ring

/-- Inversion reverses the winding integer. -/
theorem windingNumber_inv (γ : C(unitInterval, ℂ))
    (hzero : ∀ t, γ t ≠ 0) (hloop : γ 1 = γ 0) :
    windingNumber (zpowPath γ hzero (-1)) (fun t => zpow_ne_zero (-1) (hzero t))
      (by change γ 1 ^ (-1 : ℤ) = γ 0 ^ (-1 : ℤ); rw [hloop]) =
      -windingNumber γ hzero hloop := by
  simpa only [neg_one_mul] using windingNumber_zpow γ hzero hloop (-1)

/-- A genuine complex loop that traverses the circle with signed
integer multiplicity `n`, based at the actual complex number `r`. -/
def exponentialLoop (r : ℂ) (n : ℤ) : C(unitInterval, ℂ) :=
  ⟨fun t => r * Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) *
    (t : ℝ)), by fun_prop⟩

theorem exponentialLoop_zero (r : ℂ) (n : ℤ) : exponentialLoop r n 0 = r := by
  simp [exponentialLoop]

theorem exponentialLoop_one (r : ℂ) (n : ℤ) : exponentialLoop r n 1 = r := by
  change r * Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * 1) = r
  rw [mul_one, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem exponentialLoop_ne_zero (r : ℂ) (hr : r ≠ 0) (n : ℤ)
    (t : unitInterval) : exponentialLoop r n t ≠ 0 :=
  mul_ne_zero hr (Complex.exp_ne_zero _)

/-- The constructed winding integer takes every integer value on an
explicit actual loop. This fixes its orientation and normalization. -/
theorem windingNumber_exponentialLoop (r : ℂ) (hr : r ≠ 0) (n : ℤ) :
    windingNumber (exponentialLoop r n) (exponentialLoop_ne_zero r hr n)
      ((exponentialLoop_one r n).trans (exponentialLoop_zero r n).symm) = n := by
  let L : C(unitInterval, ℂ) :=
    ⟨fun t => Complex.log r + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) *
      (t : ℝ), by fun_prop⟩
  apply windingNumber_eq_of_logarithm_increment (exponentialLoop r n) L
  · intro t
    change Complex.exp (Complex.log r + (n : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I) * (t : ℝ)) = _
    rw [Complex.exp_add, Complex.exp_log hr]
    rfl
  · change (Complex.log r + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * 1) -
      (Complex.log r + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * 0) = _
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
