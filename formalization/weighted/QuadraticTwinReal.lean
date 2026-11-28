import Mathlib

/-!
# A normalized quadratic semiconjugacy fixes the real axis

The algebraic input is the actual quadratic identity together with covariance
under the unit translation.  At a rational point p/q, translating the argument
by q translates its quadratic image by the integer 2p+q^2.  Comparing the two
images determines the value of the semiconjugacy at p/q.  Continuity is needed
only on the real axis to pass from rational points to real points.

This supporting argument uses elementary rational algebra and density.  It is
not claimed independently as the new parameter-rigidity contribution.
-/

namespace QuadraticTwinReal

/-- Unit-translation covariance iterates to every natural translation. -/
theorem natural_covariance (h : ℂ → ℂ)
    (hunit : ∀ z : ℂ, h (z + 1) = h z + 1)
    (z : ℂ) (n : ℕ) :
    h (z + (n : ℂ)) = h z + (n : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa [Nat.cast_add, add_assoc, ih] using hunit (z + (n : ℂ))

/-- Unit-translation covariance also gives every negative translation. -/
theorem integer_covariance (h : ℂ → ℂ)
    (hunit : ∀ z : ℂ, h (z + 1) = h z + 1)
    (z : ℂ) (n : ℤ) :
    h (z + (n : ℂ)) = h z + (n : ℂ) := by
  cases n with
  | ofNat n =>
      simpa using natural_covariance h hunit z n
  | negSucc n =>
      have hh :
          h (z - ((n + 1 : ℕ) : ℂ)) + ((n + 1 : ℕ) : ℂ) = h z := by
        simpa only [sub_add_cancel] using
          (natural_covariance h hunit
            (z - ((n + 1 : ℕ) : ℂ)) (n + 1)).symm
      have hh' :
          h (z - ((n + 1 : ℕ) : ℂ)) = h z - ((n + 1 : ℕ) : ℂ) :=
        eq_sub_iff_add_eq.mpr hh
      simpa [Int.cast_negSucc, sub_eq_add_neg] using hh'

/-- The quadratic identity and one normalized translation already determine
every rational value; no continuity or injectivity is required here. -/
theorem fixes_rat (h : ℂ → ℂ) (c d : ℂ)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = (h z) ^ 2 + d)
    (hunit : ∀ z : ℂ, h (z + 1) = h z + 1)
    (r : ℚ) : h (r : ℂ) = (r : ℂ) := by
  have hq : (r.den : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt r.den_pos)
  have hr : (r : ℂ) * (r.den : ℂ) = (r.num : ℂ) := by
    rw [Rat.cast_def]
    exact div_mul_cancel₀ _ hq
  have halg :
      ((r : ℂ) + (r.den : ℂ)) ^ 2 + c =
        ((r : ℂ) ^ 2 + c) +
          ((2 * r.num + (r.den : ℤ) ^ 2 : ℤ) : ℂ) := by
    push_cast
    linear_combination 2 * hr
  have hcompare := congrArg h halg
  rw [hquad ((r : ℂ) + (r.den : ℂ)),
    natural_covariance h hunit (r : ℂ) r.den,
    integer_covariance h hunit ((r : ℂ) ^ 2 + c)
      (2 * r.num + (r.den : ℤ) ^ 2),
    hquad (r : ℂ)] at hcompare
  push_cast at hcompare
  have heq :
      (2 * (r.den : ℂ)) * (h (r : ℂ) - (r : ℂ)) = 0 := by
    linear_combination hcompare - 2 * hr
  have hdiff : h (r : ℂ) - (r : ℂ) = 0 :=
    (mul_eq_zero.mp heq).resolve_left (mul_ne_zero (by norm_num) hq)
  exact sub_eq_zero.mp hdiff

/-- Continuity restricted to the real axis extends rational rigidity to all
real points.  Continuity elsewhere in the plane is not assumed. -/
theorem fixes_real (h : ℂ → ℂ) (c d : ℂ)
    (hcont : Continuous (fun x : ℝ => h (x : ℂ)))
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = (h z) ^ 2 + d)
    (hunit : ∀ z : ℂ, h (z + 1) = h z + 1)
    (x : ℝ) : h (x : ℂ) = (x : ℂ) := by
  have heq : (fun y : ℝ => h (y : ℂ)) = (fun y : ℝ => (y : ℂ)) := by
    apply (Rat.denseRange_cast : DenseRange (fun r : ℚ => (r : ℝ))).equalizer
      hcont Complex.continuous_ofReal
    funext r
    simpa only [Function.comp_apply, Complex.ofReal_ratCast] using
      fixes_rat h c d hquad hunit r
  exact congrFun heq x

end QuadraticTwinReal
