import QuadraticMultiplierArithmetic

/-!
# Analytic continuation of actual quadratic periodic points

The periodic branch is constructed from the complex implicit function
theorem. Its local uniqueness and parameter derivative are proved for the
actual polynomial iterates. Arithmetic nonneutrality supplies the
nondegeneracy hypothesis at every algebraic-integer parameter.
-/

namespace LoopsQuadraticTransversality

open Filter
open scoped Topology ContDiff

noncomputable section

/-- The actual return iterate is jointly analytic in parameter and point. -/
theorem returnOrbit_contDiff (p : ℕ) :
    ContDiff ℂ ω (fun v : ℂ × ℂ => returnOrbit v.1 v.2 p) := by
  induction p with
  | zero => exact contDiff_snd
  | succ p ih =>
    exact (ih.pow 2).add contDiff_fst

private theorem periodic_equation_partial (c z : ℂ) (p : ℕ) :
    fderiv ℂ (fun v : ℂ × ℂ => returnOrbit v.1 v.2 p - v.2) (c,z) ∘L
        ContinuousLinearMap.inr ℂ ℂ ℂ =
      ContinuousLinearMap.toSpanSingleton ℂ (returnMultiplier c z p - 1) := by
  have hdiff : DifferentiableAt ℂ
      (fun v : ℂ × ℂ => returnOrbit v.1 v.2 p - v.2) (c,z) :=
    ((returnOrbit_contDiff p).sub contDiff_snd).differentiable
      (by simp) (c,z)
  have hcomp := hdiff.hasFDerivAt.comp z (hasFDerivAt_prodMk_right c z)
  exact hcomp.unique
    (((returnMultiplier_hasDerivAt c z p).sub (hasDerivAt_id z)).hasFDerivAt)

private theorem scalar_partial_invertible (a : ℂ) (ha : a ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℂ a).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℂ a⁻¹)
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, ha]
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, ha]

/-- Every nondegenerate actual periodic point has a locally unique analytic
motion, with its exact parameter derivative. The root criterion is local
in both variables, not only along the constructed branch. -/
theorem periodic_point_motion (c z : ℂ) (p : ℕ)
    (hper : returnOrbit c z p = z)
    (hmult : returnMultiplier c z p ≠ 1) :
    ∃ ζ : ℂ → ℂ,
      ζ c = z ∧ AnalyticAt ℂ ζ c ∧
      (fun w : ℂ => returnOrbit w (ζ w) p) =ᶠ[𝓝 c] ζ ∧
      (∀ᶠ v : ℂ × ℂ in 𝓝 (c,z),
        returnOrbit v.1 v.2 p = v.2 ↔ ζ v.1 = v.2) ∧
      HasDerivAt ζ
        (-(returnTangent c z 0 p) / (returnMultiplier c z p - 1)) c := by
  let F : ℂ × ℂ → ℂ := fun v => returnOrbit v.1 v.2 p - v.2
  have hF : ContDiffAt ℂ ω F (c,z) :=
    ((returnOrbit_contDiff p).sub contDiff_snd).contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hpartial : (fderiv ℂ F (c,z) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    change (fderiv ℂ (fun v : ℂ × ℂ => returnOrbit v.1 v.2 p - v.2) (c,z) ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible
    rw [periodic_equation_partial]
    exact scalar_partial_invertible _ (sub_ne_zero.mpr hmult)
  let ζ : ℂ → ℂ := hF.implicitFunction hn hpartial
  have hself : ζ c = z := hF.implicitFunction_apply_self hn hpartial
  have han : AnalyticAt ℂ ζ c :=
    (hF.contDiffAt_implicitFunction hn hpartial).analyticAt
  have hzero : F (c,z) = 0 := sub_eq_zero.mpr hper
  have hmotion : (fun w : ℂ => returnOrbit w (ζ w) p) =ᶠ[𝓝 c] ζ := by
    filter_upwards [hF.eventually_apply_implicitFunction hn hpartial] with w hw
    exact sub_eq_zero.mp (hw.trans hzero)
  have huniq : ∀ᶠ v : ℂ × ℂ in 𝓝 (c,z),
      returnOrbit v.1 v.2 p = v.2 ↔ ζ v.1 = v.2 := by
    filter_upwards [hF.eventually_apply_eq_iff_implicitFunction hn hpartial] with v hv
    simpa only [F, hzero, sub_eq_zero] using hv
  refine ⟨ζ, hself, han, hmotion, huniq, ?_⟩
  have hd : HasDerivAt ζ (deriv ζ c) c := han.differentiableAt.hasDerivAt
  have hret := (returnTangent_hasDerivAt c ζ (deriv ζ c) hd p).unique
    (hd.congr_of_eventuallyEq hmotion)
  rw [hself] at hret
  have hsub := returnTangent_sub c z (deriv ζ c) 0 p
  rw [hret, sub_zero] at hsub
  have he : deriv ζ c = -(returnTangent c z 0 p) / (returnMultiplier c z p - 1) := by
    apply (eq_div_iff (sub_ne_zero.mpr hmult)).mpr
    linear_combination -hsub
  exact hd.congr_deriv he

/-- At an algebraic-integer parameter, arithmetic excludes degeneracy for
every positive-period orbit, so no multiplier hypothesis is needed. -/
theorem integral_parameter_periodic_point_motion (c z : ℂ)
    (hc : IsIntegral ℤ c) (p : ℕ) (hp : 0 < p)
    (hper : returnOrbit c z p = z) :
    ∃ ζ : ℂ → ℂ,
      ζ c = z ∧ AnalyticAt ℂ ζ c ∧
      (fun w : ℂ => returnOrbit w (ζ w) p) =ᶠ[𝓝 c] ζ ∧
      (∀ᶠ v : ℂ × ℂ in 𝓝 (c,z),
        returnOrbit v.1 v.2 p = v.2 ↔ ζ v.1 = v.2) ∧
      HasDerivAt ζ
        (-(returnTangent c z 0 p) / (returnMultiplier c z p - 1)) c := by
  have hz : IsIntegral ℤ z := integral_of_spatial_collision hc 0 p hp
    (show returnOrbit c z 0 = returnOrbit c z p from hper.symm)
  apply periodic_point_motion c z p hper
  intro hm
  apply returnMultiplier_not_neutral hc hz p hp
  rw [hm, norm_one]

/-- Every periodic cycle at a critical-collision parameter has a locally
unique analytic continuation, whether or not that cycle is postcritical. -/
theorem collision_parameter_periodic_point_motion (c : ℂ) (a b : ℕ)
    (hab : a < b) (hcoll : orbit c a = orbit c b)
    (z : ℂ) (p : ℕ) (hp : 0 < p)
    (hper : returnOrbit c z p = z) :
    ∃ ζ : ℂ → ℂ,
      ζ c = z ∧ AnalyticAt ℂ ζ c ∧
      (fun w : ℂ => returnOrbit w (ζ w) p) =ᶠ[𝓝 c] ζ ∧
      (∀ᶠ v : ℂ × ℂ in 𝓝 (c,z),
        returnOrbit v.1 v.2 p = v.2 ↔ ζ v.1 = v.2) ∧
      HasDerivAt ζ
        (-(returnTangent c z 0 p) / (returnMultiplier c z p - 1)) c :=
  integral_parameter_periodic_point_motion c z (integral_of_collision c a b hab hcoll)
    p hp hper

end

end LoopsQuadraticTransversality
