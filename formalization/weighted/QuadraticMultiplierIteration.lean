import QuadraticPeriodicStability

/-!
# Multipliers of repeated quadratic returns

The spatial derivative satisfies its actual orbit cocycle. On a periodic
motion the multiplier of the p*k return is the kth power of the p-return
multiplier. At a superattracting base, repetition by k >= 2 destroys a
nonzero parameter derivative and prevents a differentiable local inverse.
These are statements about the actual quadratic iterates.
-/

namespace LoopsQuadraticTransversality

open Filter
open scoped Topology

noncomputable section

/-- Splitting an actual return orbit at an arbitrary intermediate time. -/
theorem returnOrbit_add_steps (c z : ℂ) (m n : ℕ) :
    returnOrbit c z (m+n) = returnOrbit c (returnOrbit c z m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change returnOrbit c z (m+n) ^ 2 + c =
      returnOrbit c (returnOrbit c z m) n ^ 2 + c
    rw [ih]

/-- The genuine spatial multiplier obeys the derivative cocycle. -/
theorem returnMultiplier_add_steps (c z : ℂ) (m n : ℕ) :
    returnMultiplier c z (m+n) =
      returnMultiplier c (returnOrbit c z m) n * returnMultiplier c z m := by
  induction n with
  | zero => simp only [Nat.add_zero, returnMultiplier, one_mul]
  | succ n ih =>
    change 2 * returnOrbit c z (m+n) * returnMultiplier c z (m+n) =
      (2 * returnOrbit c (returnOrbit c z m) n *
        returnMultiplier c (returnOrbit c z m) n) * returnMultiplier c z m
    rw [returnOrbit_add_steps, ih]
    ring

/-- Every nonnegative multiple of a specified period is a return time. -/
theorem periodic_returnOrbit_mul (c z : ℂ) (p k : ℕ)
    (hper : returnOrbit c z p = z) : returnOrbit c z (p*k) = z := by
  induction k with
  | zero => simp only [Nat.mul_zero, returnOrbit]
  | succ k ih =>
    rw [Nat.mul_succ, returnOrbit_add_steps, ih]
    exact hper

/-- The multiplier of a repeated return is the corresponding exact power.
The specified period need not be minimal. -/
theorem periodic_returnMultiplier_mul (c z : ℂ) (p k : ℕ)
    (hper : returnOrbit c z p = z) :
    returnMultiplier c z (p*k) = returnMultiplier c z p ^ k := by
  induction k with
  | zero => simp only [Nat.mul_zero, returnMultiplier, pow_zero]
  | succ k ih =>
    rw [Nat.mul_succ, returnMultiplier_add_steps,
      periodic_returnOrbit_mul c z p k hper, ih, pow_succ]
    ring

/-- The repeated-return power identity holds on the same periodic motion,
with the same parameter neighborhood. -/
theorem periodic_motion_returnMultiplier_mul (c : ℂ) (ζ : ℂ → ℂ)
    (p k : ℕ)
    (hper : (fun w : ℂ => returnOrbit w (ζ w) p) =ᶠ[𝓝 c] ζ) :
    (fun w => returnMultiplier w (ζ w) (p*k)) =ᶠ[𝓝 c]
      (fun w => returnMultiplier w (ζ w) p ^ k) := by
  filter_upwards [hper] with w hw
  exact periodic_returnMultiplier_mul w (ζ w) p k hw

/-- At a superattracting base of an analytic periodic motion, every return
repeated at least twice has zero parameter derivative. -/
theorem repeated_returnMultiplier_hasDerivAt_zero (c : ℂ) (ζ : ℂ → ℂ)
    (p k : ℕ) (hζ : AnalyticAt ℂ ζ c)
    (hper : (fun w : ℂ => returnOrbit w (ζ w) p) =ᶠ[𝓝 c] ζ)
    (hzero : returnMultiplier c (ζ c) p = 0) (hk : 2 ≤ k) :
    HasDerivAt (fun w => returnMultiplier w (ζ w) (p*k)) 0 c := by
  have hλ : AnalyticAt ℂ (fun w => returnMultiplier w (ζ w) p) c :=
    ((returnMultiplier_contDiff p).contDiffAt.analyticAt).comp
      (analyticAt_id.prod hζ)
  have hkm1 : k-1 ≠ 0 := by omega
  have hd := hλ.differentiableAt.hasDerivAt.pow k
  have hd0 : HasDerivAt (fun w => returnMultiplier w (ζ w) p ^ k) 0 c := by
    simpa only [hzero, zero_pow hkm1, mul_zero, zero_mul] using hd
  exact hd0.congr_of_eventuallyEq
    (periodic_motion_returnMultiplier_mul c ζ p k hper)

/-- Consequently a repeated return of order at least two cannot be a local
parameter coordinate with a differentiable left inverse. -/
theorem repeated_returnMultiplier_no_differentiable_left_inverse
    (c : ℂ) (ζ : ℂ → ℂ) (p k : ℕ) (hζ : AnalyticAt ℂ ζ c)
    (hper : (fun w : ℂ => returnOrbit w (ζ w) p) =ᶠ[𝓝 c] ζ)
    (hzero : returnMultiplier c (ζ c) p = 0) (hk : 2 ≤ k) :
    ¬ ∃ ψ : ℂ → ℂ, DifferentiableAt ℂ ψ 0 ∧
      (∀ᶠ w in 𝓝 c, ψ (returnMultiplier w (ζ w) (p*k)) = w) := by
  rintro ⟨ψ, hψ, hleft⟩
  have hk0 : k ≠ 0 := by omega
  have hbase : returnOrbit c (ζ c) p = ζ c := hper.self_of_nhds
  have hrepzero : returnMultiplier c (ζ c) (p*k) = 0 := by
    rw [periodic_returnMultiplier_mul c (ζ c) p k hbase, hzero,
      zero_pow hk0]
  have hd := repeated_returnMultiplier_hasDerivAt_zero c ζ p k hζ hper hzero hk
  have hψ' : HasDerivAt ψ (deriv ψ 0) (returnMultiplier c (ζ c) (p*k)) := by
    simpa only [hrepzero] using hψ.hasDerivAt
  have hcomp : HasDerivAt (fun w => ψ (returnMultiplier w (ζ w) (p*k))) 0 c := by
    simpa only [mul_zero, zero_mul] using hψ'.comp c hd
  have hid : HasDerivAt (fun w => ψ (returnMultiplier w (ζ w) (p*k))) 1 c :=
    (hasDerivAt_id c).congr_of_eventuallyEq hleft
  exact zero_ne_one (hcomp.unique hid)

end
end LoopsQuadraticTransversality
