import QuadraticPeriodicStability

/-!
# The first-return multiplier at a quadratic center

The initial critical factor is split from the genuine spatial multiplier.
Along any differentiable motion through zero this isolates its parameter
derivative. Exact critical period makes every remaining factor nonzero.
-/

namespace LoopsQuadraticCenterMultiplier

open Filter
open scoped Topology ContDiff
open LoopsQuadraticTransversality

noncomputable section

/-- Removing the first step from the actual orbit. -/
theorem returnOrbit_step_start (c z : ℂ) (n : ℕ) :
    returnOrbit c (z ^ 2 + c) n = returnOrbit c z (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change returnOrbit c (z ^ 2 + c) n ^ 2 + c =
      returnOrbit c z (n+1) ^ 2 + c
    rw [ih]

/-- Split the initial derivative factor from the genuine return multiplier. -/
theorem returnMultiplier_initial_factor (c z : ℂ) (n : ℕ) :
    returnMultiplier c z (n+1) =
      (2*z) * returnMultiplier c (z ^ 2 + c) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [returnMultiplier, ih]
    rw [returnMultiplier, returnOrbit_step_start]
    ring

/-- Every positive-length return starting at the critical point has zero
spatial multiplier, independently of its terminal value. -/
theorem returnMultiplier_zero_start (c : ℂ) (n : ℕ) :
    returnMultiplier c 0 (n+1) = 0 := by
  rw [returnMultiplier_initial_factor]
  simp

/-- A finite spatial derivative is nonzero when none of its initial orbit
points is critical. -/
theorem returnMultiplier_ne_zero_of_orbit_ne_zero (c z : ℂ) (n : ℕ) :
    (∀ k : ℕ, k < n → returnOrbit c z k ≠ 0) →
      returnMultiplier c z n ≠ 0 := by
  induction n with
  | zero => intro _; simp [returnMultiplier]
  | succ n ih =>
    intro h
    rw [returnMultiplier]
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (h n (Nat.lt_succ_self n)))
      (ih (fun k hk => h k (Nat.lt_trans hk (Nat.lt_succ_self n))))

/-- At an exact-period center, the tail after the critical step contains
no further zero derivative factor before the first return. -/
theorem center_tail_multiplier_ne_zero (c : ℂ) (n : ℕ)
    (hmin : ∀ k : ℕ, 0 < k → k < n+1 → orbit c k ≠ 0) :
    returnMultiplier c c n ≠ 0 := by
  apply returnMultiplier_ne_zero_of_orbit_ne_zero
  intro k hk
  have hstart : orbit c 1 = c := by simp [orbit]
  have heq := returnOrbit_orbit c 1 k
  rw [hstart] at heq
  rw [heq]
  exact hmin (1+k) (by omega) (by omega)

/-- Differentiating the initial critical factor kills the derivative of
the tail. This statement needs only a differentiable motion through zero. -/
theorem moving_center_multiplier_hasDerivAt (c : ℂ) (n : ℕ)
    (ζ : ℂ → ℂ) (d : ℂ) (hζ : HasDerivAt ζ d c) (hzero : ζ c = 0) :
    HasDerivAt (fun w : ℂ => returnMultiplier w (ζ w) (n+1))
      (2*d*returnMultiplier c c n) c := by
  let A : ℂ → ℂ := fun w => returnMultiplier w ((ζ w)^2+w) n
  have hA : DifferentiableAt ℂ A c := by
    have hpath := (hasDerivAt_id c).prodMk ((hζ.pow 2).add (hasDerivAt_id c))
    exact ((returnMultiplier_contDiff n).differentiable (by simp) _).comp c
      hpath.differentiableAt
  have hprod := (hζ.const_mul (2 : ℂ)).mul hA.hasDerivAt
  have hfactor : (fun w : ℂ => returnMultiplier w (ζ w) (n+1)) =
      (fun w : ℂ => (2*ζ w)*A w) := by
    funext w
    exact returnMultiplier_initial_factor w (ζ w) n
  rw [hfactor]
  exact hprod.congr_deriv (by simp [A, hzero])

/-- The analytic periodic point through the critical point moves with
exactly the critical-return parameter tangent. -/
theorem moving_center_hasDerivAt (c : ℂ) (n : ℕ) (ζ : ℂ → ℂ)
    (hζ : AnalyticAt ℂ ζ c) (hzero : ζ c = 0)
    (hret : (fun w : ℂ => returnOrbit w (ζ w) (n+1)) =ᶠ[𝓝 c] ζ) :
    HasDerivAt ζ (slope c (n+1)) c := by
  have hd := hζ.differentiableAt.hasDerivAt
  have hmatch : ζ c = orbit c 0 := hzero
  have hi := landing_motion_identity c 0 (n+1) ζ (deriv ζ c) hd hmatch hret
  simp only [Nat.zero_add] at hi
  change slope c (n+1) - 0 =
    (returnMultiplier c 0 (n+1) - 1) * (0 - deriv ζ c) at hi
  rw [returnMultiplier_zero_start] at hi
  have he : deriv ζ c = slope c (n+1) := by linear_combination -hi
  exact hd.congr_deriv he

/-- The first-return multiplier derivative is nonzero at every actual
exact-period quadratic center, including period one. -/
theorem center_multiplier_derivative_ne_zero (c : ℂ) (n : ℕ)
    (hreturn : orbit c (n+1) = 0)
    (hmin : ∀ k : ℕ, 0 < k → k < n+1 → orbit c k ≠ 0) :
    2*slope c (n+1)*returnMultiplier c c n ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (center_transverse c n hreturn))
    (center_tail_multiplier_ne_zero c n hmin)

end

end LoopsQuadraticCenterMultiplier
