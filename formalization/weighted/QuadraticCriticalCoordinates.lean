import QuadraticCollisionFactorization
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Analytic parameter coordinates for actual quadratic critical relations

The coordinates in this file concern the ambient complex parameter plane.
No relative local-connectivity or global tower-rigidity conclusion is asserted.
-/

namespace LoopsQuadraticCoordinates

open Filter
open scoped Topology
open LoopsQuadraticTransversality

noncomputable section

/-- Every finite critical iterate is analytic in the actual parameter. -/
theorem criticalOrbit_analyticAt (n : ℕ) (c : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => orbit w n) c := by
  induction n with
  | zero => simpa only [orbit] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) c)
  | succ n ih => exact (ih.pow 2).add analyticAt_id

private theorem analytic_inverse_at_zero (f : ℂ → ℂ) (c d : ℂ)
    (hf : AnalyticAt ℂ f c) (hzero : f c = 0)
    (hd : HasDerivAt f d c) (hne : d ≠ 0) :
    ∃ ψ : ℂ → ℂ, ψ 0 = c ∧ AnalyticAt ℂ ψ 0 ∧ HasDerivAt ψ d⁻¹ 0 ∧
      (∀ᶠ w in 𝓝 c, ψ (f w) = w) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), f (ψ t) = t) := by
  have hderiv : deriv f c ≠ 0 := by rwa [hd.deriv]
  let ψ := hf.hasStrictDerivAt.localInverse f (deriv f c) c hderiv
  have hleft : ∀ᶠ w in 𝓝 c, ψ (f w) = w :=
    HasStrictDerivAt.eventually_left_inverse ..
  have hright : ∀ᶠ t in 𝓝 (f c), f (ψ t) = t :=
    HasStrictDerivAt.eventually_right_inverse ..
  have hinv : HasDerivAt ψ (deriv f c)⁻¹ (f c) :=
    (hf.hasStrictDerivAt.to_localInverse hderiv).hasDerivAt
  refine ⟨ψ, ?_, ?_, ?_, hleft, ?_⟩
  · simpa only [hzero] using hleft.self_of_nhds
  · simpa only [hzero] using hf.analyticAt_localInverse hderiv
  · simpa only [hzero, hd.deriv] using hinv
  · simpa only [hzero] using hright

/-- At every positive critical return, the actual return polynomial
is a local analytic parameter coordinate, with an analytic inverse.
The theorem does not require the return time to be the minimal period. -/
theorem center_parameter_coordinate (c : ℂ) (n : ℕ)
    (h : orbit c (n+1) = 0) :
    ∃ ψ : ℂ → ℂ, ψ 0 = c ∧ AnalyticAt ℂ ψ 0 ∧
      HasDerivAt ψ (slope c (n+1))⁻¹ 0 ∧
      (∀ᶠ w in 𝓝 c, ψ (orbit w (n+1)) = w) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), orbit (ψ t) (n+1) = t) := by
  exact analytic_inverse_at_zero (fun w => orbit w (n+1)) c (slope c (n+1))
    (criticalOrbit_analyticAt (n+1) c) h (orbit_hasDerivAt (n+1) c)
    (center_transverse c n h)

/-- A first critical collision determines an actual analytic moving
periodic point and a locally invertible critical-entrance coordinate.
Its explicit analytic secant factor is nonvanishing. The zero-coordinate
equivalence identifies the original collision and isolates that parameter.
The inverse and factorization use the same motion; none is assumed. -/
theorem first_collision_parameter_coordinate (c : ℂ) (a b : ℕ)
    (hab : a < b)
    (hcoll : orbit c (a+2) = orbit c (b+2))
    (hprev : orbit c (a+1) ≠ orbit c (b+1)) :
    ∃ ζ ψ : ℂ → ℂ,
      ζ c = orbit c (a+2) ∧ AnalyticAt ℂ ζ c ∧
      (fun w : ℂ => returnOrbit w (ζ w) (b-a)) =ᶠ[𝓝 c] ζ ∧
      AnalyticAt ℂ (fun w => orbit w (a+2) - ζ w) c ∧
      HasDerivAt (fun w => orbit w (a+2) - ζ w)
        ((slope c (b+2) - slope c (a+2)) /
          (returnMultiplier c (orbit c (a+2)) (b-a) - 1)) c ∧
      (slope c (b+2) - slope c (a+2)) /
          (returnMultiplier c (orbit c (a+2)) (b-a) - 1) ≠ 0 ∧
      ψ 0 = c ∧ AnalyticAt ℂ ψ 0 ∧
      HasDerivAt ψ
        ((returnMultiplier c (orbit c (a+2)) (b-a) - 1) /
          (slope c (b+2) - slope c (a+2))) 0 ∧
      (∀ᶠ w in 𝓝 c, ψ (orbit w (a+2) - ζ w) = w) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), orbit (ψ t) (a+2) - ζ (ψ t) = t) ∧
      (∀ᶠ w in 𝓝 c,
        (orbit w (b+2) = orbit w (a+2) ↔ orbit w (a+2) - ζ w = 0) ∧
        (orbit w (a+2) - ζ w = 0 ↔ w = c)) ∧
      AnalyticAt ℂ (motionSecantFactor ζ (a+2) (b-a)) c ∧
      motionSecantFactor ζ (a+2) (b-a) c =
        returnMultiplier c (orbit c (a+2)) (b-a) - 1 ∧
      (∀ᶠ w in 𝓝 c, motionSecantFactor ζ (a+2) (b-a) w ≠ 0 ∧
        orbit w (b+2) - orbit w (a+2) =
          (orbit w (a+2) - ζ w) * motionSecantFactor ζ (a+2) (b-a) w) := by
  have hp : 0 < b-a := Nat.sub_pos_of_lt hab
  have hindex : a+2+(b-a) = b+2 := by omega
  have hper : returnOrbit c (orbit c (a+2)) (b-a) = orbit c (a+2) := by
    rw [returnOrbit_orbit, hindex]
    exact hcoll.symm
  obtain ⟨ζ, hself, hζ, hmotion, huniq, hdζ⟩ :=
    collision_parameter_periodic_point_motion c (a+2) (b+2)
      (by omega) hcoll (orbit c (a+2)) (b-a) hp hper
  let d : ℂ := -(returnTangent c (orbit c (a+2)) 0 (b-a)) /
    (returnMultiplier c (orbit c (a+2)) (b-a) - 1)
  have hdζ' : HasDerivAt ζ d c := hdζ
  let E : ℂ → ℂ := fun w => orbit w (a+2) - ζ w
  have hE : AnalyticAt ℂ E c := (criticalOrbit_analyticAt (a+2) c).sub hζ
  have hEzero : E c = 0 := sub_eq_zero.mpr hself.symm
  have hED : HasDerivAt E (slope c (a+2)-d) c :=
    (orbit_hasDerivAt (a+2) c).sub hdζ'
  have hid := landing_motion_identity c (a+2) (b-a) ζ d hdζ' hself hmotion
  rw [hindex] at hid
  have hdelta := first_collision_transverse c a b hab hcoll hprev
  have hmult : returnMultiplier c (orbit c (a+2)) (b-a) - 1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hid
    exact hdelta hid
  have hformula : slope c (a+2)-d =
      (slope c (b+2)-slope c (a+2)) /
        (returnMultiplier c (orbit c (a+2)) (b-a)-1) := by
    apply (eq_div_iff hmult).mpr
    rw [mul_comm]
    exact hid.symm
  have hnonzero : (slope c (b+2)-slope c (a+2)) /
      (returnMultiplier c (orbit c (a+2)) (b-a)-1) ≠ 0 :=
    div_ne_zero hdelta hmult
  have hderiv := hED.congr_deriv hformula
  obtain ⟨ψ, hψzero, hψ, hψD, hleft, hright⟩ :=
    analytic_inverse_at_zero E c _ hE hEzero hderiv hnonzero
  have hpath : Tendsto (fun w : ℂ => (w,orbit w (a+2)))
      (𝓝 c) (𝓝 (c,orbit c (a+2))) :=
    continuousAt_id.prodMk (orbit_hasDerivAt (a+2) c).continuousAt
  have hrelation : ∀ᶠ w in 𝓝 c,
      orbit w (b+2) = orbit w (a+2) ↔ E w = 0 := by
    filter_upwards [hpath.eventually huniq] with w hw
    change returnOrbit w (orbit w (a+2)) (b-a) = orbit w (a+2) ↔
      ζ w = orbit w (a+2) at hw
    rw [returnOrbit_orbit, hindex] at hw
    change orbit w (b+2) = orbit w (a+2) ↔ orbit w (a+2) - ζ w = 0
    rw [sub_eq_zero]
    exact hw.trans eq_comm
  obtain ⟨hQan, hQself, hQne, hQfactor⟩ :=
    motion_collision_factorization c (a+2) (b-a) ζ hself hζ hmotion
      (sub_ne_zero.mp hmult)
  refine ⟨ζ, ψ, hself, hζ, hmotion, hE, hderiv, hnonzero,
    hψzero, hψ, ?_, hleft, hright, ?_, hQan, hQself, ?_⟩
  · simpa only [inv_div] using hψD
  · filter_upwards [hrelation, hleft] with w hrel hw
    refine ⟨hrel, ?_⟩
    constructor
    · intro hz
      change E w = 0 at hz
      rw [hz, hψzero] at hw
      exact hw.symm
    · intro hwc
      subst w
      exact hEzero
  · filter_upwards [hQne, hQfactor] with w hn hw
    exact ⟨hn, by simpa only [hindex] using hw⟩

end
end LoopsQuadraticCoordinates
