import QuadraticPeriodicMotion

/-!
# Explicit analytic factors for actual critical collisions

The finite secant product below factors differences of genuine quadratic
iterates. Along the constructed periodic motion it gives an explicit
nonvanishing analytic factor relating the critical-relation equation to
the displacement from the moving periodic point.
-/

namespace LoopsQuadraticTransversality

open Filter
open scoped Topology ContDiff

noncomputable section

/-- The actual finite secant product, defined without division. -/
def returnSecant (c x y : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => (returnOrbit c x n + returnOrbit c y n) * returnSecant c x y n

/-- Exact difference factorization at every parameter, pair of points,
and finite horizon, including coincident points. -/
theorem returnOrbit_sub_secant (c x y : ℂ) (n : ℕ) :
    returnOrbit c x n - returnOrbit c y n = (x-y) * returnSecant c x y n := by
  induction n with
  | zero => simp [returnOrbit, returnSecant]
  | succ n ih =>
    simp only [returnOrbit, returnSecant]
    calc
      (returnOrbit c x n ^ 2 + c) - (returnOrbit c y n ^ 2 + c) =
          (returnOrbit c x n - returnOrbit c y n) *
            (returnOrbit c x n + returnOrbit c y n) := by ring
      _ = (x-y) * ((returnOrbit c x n + returnOrbit c y n) *
          returnSecant c x y n) := by rw [ih]; ring

/-- The diagonal value is the genuine spatial multiplier. -/
theorem returnSecant_diagonal (c z : ℂ) (n : ℕ) :
    returnSecant c z z n = returnMultiplier c z n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [returnSecant, returnMultiplier, ih]; ring

/-- The secant product is jointly analytic in the parameter and both
dynamical points, including its entire diagonal. -/
theorem returnSecant_contDiff (n : ℕ) :
    ContDiff ℂ ω (fun v : ℂ × ℂ × ℂ => returnSecant v.1 v.2.1 v.2.2 n) := by
  have hx : ContDiff ℂ ω (fun v : ℂ × ℂ × ℂ => (v.1,v.2.1)) := by fun_prop
  have hy : ContDiff ℂ ω (fun v : ℂ × ℂ × ℂ => (v.1,v.2.2)) := by fun_prop
  induction n with
  | zero => exact contDiff_const
  | succ n ih =>
    exact (((returnOrbit_contDiff n).comp hx).add
      ((returnOrbit_contDiff n).comp hy)).mul ih

private theorem critical_orbit_contDiff (n : ℕ) :
    ContDiff ℂ ω (fun c : ℂ => orbit c n) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih => exact (ih.pow 2).add contDiff_id

/-- The explicit residual factor for the displacement from a moving
periodic point. No division by that displacement occurs. -/
def motionSecantFactor (ζ : ℂ → ℂ) (m p : ℕ) (w : ℂ) : ℂ :=
  returnSecant w (orbit w m) (ζ w) p - 1

/-- An analytic periodic motion gives an explicit analytic factorization
of the actual critical relation. Its factor is a local analytic unit
whenever the periodic multiplier differs from one. -/
theorem motion_collision_factorization (c : ℂ) (m p : ℕ) (ζ : ℂ → ℂ)
    (hself : ζ c = orbit c m) (han : AnalyticAt ℂ ζ c)
    (hper : (fun w : ℂ => returnOrbit w (ζ w) p) =ᶠ[𝓝 c] ζ)
    (hmult : returnMultiplier c (orbit c m) p ≠ 1) :
    AnalyticAt ℂ (motionSecantFactor ζ m p) c ∧
      motionSecantFactor ζ m p c = returnMultiplier c (orbit c m) p - 1 ∧
      (∀ᶠ w in 𝓝 c, motionSecantFactor ζ m p w ≠ 0) ∧
      (fun w : ℂ => orbit w (m+p) - orbit w m) =ᶠ[𝓝 c]
        (fun w : ℂ => (orbit w m - ζ w) * motionSecantFactor ζ m p w) := by
  have hpath : ContDiffAt ℂ ω (fun w : ℂ => (w,orbit w m,ζ w)) c :=
    contDiffAt_id.prodMk ((critical_orbit_contDiff m).contDiffAt.prodMk han.contDiffAt)
  have hQan : AnalyticAt ℂ (motionSecantFactor ζ m p) c :=
    (((returnSecant_contDiff p).contDiffAt.comp c hpath).sub contDiffAt_const).analyticAt
  have hQself : motionSecantFactor ζ m p c =
      returnMultiplier c (orbit c m) p - 1 := by
    simp only [motionSecantFactor, hself, returnSecant_diagonal]
  have hQne : motionSecantFactor ζ m p c ≠ 0 := by
    rw [hQself]
    exact sub_ne_zero.mpr hmult
  refine ⟨hQan, hQself, hQan.continuousAt.eventually_ne hQne, ?_⟩
  filter_upwards [hper] with w hw
  have hdiff := returnOrbit_sub_secant w (orbit w m) (ζ w) p
  rw [returnOrbit_orbit, hw] at hdiff
  dsimp only [motionSecantFactor]
  linear_combination hdiff

/-- At every first critical collision, the periodic motion and the
explicit nonvanishing analytic factor are constructed. The displacement
factor has nonzero derivative, so the factorization retains the simple
zero of the actual critical-relation polynomial. -/
theorem first_collision_analytic_factorization (c : ℂ) (a b : ℕ)
    (hab : a < b) (hcoll : orbit c (a+2) = orbit c (b+2))
    (hprev : orbit c (a+1) ≠ orbit c (b+1)) :
    ∃ ζ Q : ℂ → ℂ,
      ζ c = orbit c (a+2) ∧ AnalyticAt ℂ ζ c ∧
      (fun w : ℂ => returnOrbit w (ζ w) (b-a)) =ᶠ[𝓝 c] ζ ∧
      Q = motionSecantFactor ζ (a+2) (b-a) ∧ AnalyticAt ℂ Q c ∧
      Q c = returnMultiplier c (orbit c (a+2)) (b-a) - 1 ∧
      (∀ᶠ w in 𝓝 c, Q w ≠ 0) ∧
      (fun w : ℂ => orbit w (b+2) - orbit w (a+2)) =ᶠ[𝓝 c]
        (fun w : ℂ => (orbit w (a+2) - ζ w) * Q w) ∧
      deriv (fun w : ℂ => orbit w (a+2) - ζ w) c ≠ 0 := by
  have hp : 0 < b-a := by omega
  have hind : a+2+(b-a) = b+2 := by omega
  have hper : returnOrbit c (orbit c (a+2)) (b-a) = orbit c (a+2) := by
    rw [returnOrbit_orbit, hind]
    exact hcoll.symm
  have hc : IsIntegral ℤ c := integral_of_collision c (a+2) (b+2) (by omega) hcoll
  have hmult : returnMultiplier c (orbit c (a+2)) (b-a) ≠ 1 := by
    intro hm
    apply returnMultiplier_not_neutral hc (orbit_integral hc (a+2)) (b-a) hp
    rw [hm, norm_one]
  obtain ⟨ζ, hself, han, hmotion, _, hd⟩ :=
    periodic_point_motion c (orbit c (a+2)) (b-a) hper hmult
  obtain ⟨hQan, hQself, hQne, hfactor⟩ :=
    motion_collision_factorization c (a+2) (b-a) ζ hself han hmotion hmult
  refine ⟨ζ, motionSecantFactor ζ (a+2) (b-a), hself, han, hmotion,
    rfl, hQan, hQself, hQne, ?_, ?_⟩
  · simpa only [hind] using hfactor
  · have hid := landing_motion_identity c (a+2) (b-a) ζ _ hd hself hmotion
    rw [hind] at hid
    have hderiv := ((orbit_hasDerivAt (a+2) c).sub hd).deriv
    intro hzero
    change deriv ((fun w : ℂ => orbit w (a+2)) - ζ) c = 0 at hzero
    rw [← hderiv, hzero, mul_zero] at hid
    exact first_collision_transverse c a b hab hcoll hprev hid

end

end LoopsQuadraticTransversality
