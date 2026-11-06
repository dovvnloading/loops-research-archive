import Mathlib
import Period27RationalDerivative

/-!
# Exact real parameter bridge for the period-27 critical orbit

The root Lean sources already prove universal rational enclosure soundness
and opposite signs at the two exact dyadic endpoints. This module connects
those results to the *actual real* critical-orbit polynomial, proves its
parameter-derivative recurrence by calculus, and constructs a real root
in the certified parameter bracket using the intermediate value theorem.

All analytic work uses pinned mathlib; no assumption that a root exists is
added. A subsequent module handles strict uniqueness via the uniform
negative derivative bound (including passage from rationals to reals).
This does not identify analytic quadratic-like domains or prove MLC.
-/

namespace LoopsRealPeriod27

open LoopsFormal.Period27

noncomputable section

/-- Exact fraction interpreted as a genuine real number. -/
def value (x : ExactFraction) : ℝ := (x.num : ℝ) / (x.den : ℝ)

private theorem den_pos (x : ExactFraction) : 0 < (x.den : ℝ) := by
  exact_mod_cast x.den_pos

private theorem den_ne (x : ExactFraction) : (x.den : ℝ) ≠ 0 :=
  ne_of_gt (den_pos x)

theorem value_zero : value fzero = 0 := by
  norm_num [value, fzero]

theorem value_one : value fone = 1 := by
  norm_num [value, fone]

theorem value_add (a b : ExactFraction) :
    value (fadd a b) = value a + value b := by
  simp only [value, fadd, Int.cast_add, Int.cast_mul]
  field_simp [den_ne a, den_ne b]
  <;> ring

theorem value_mul (a b : ExactFraction) :
    value (fmul a b) = value a * value b := by
  simp only [value, fmul, Int.cast_mul]
  field_simp [den_ne a, den_ne b]
  <;> ring

theorem value_square (a : ExactFraction) :
    value (fsquare a) = (value a) ^ 2 := by
  simp only [value, fsquare, Int.cast_mul, pow_two]
  field_simp [den_ne a]
  <;> ring

theorem value_double (a : ExactFraction) :
    value (fdouble a) = 2 * value a := by
  simp [value, fdouble, Int.cast_mul]
  <;> ring

/-- A real quadratic step together with its *parameter* derivative. -/
def next (c : ℝ) (st : ℝ × ℝ) : ℝ × ℝ :=
  (st.1 ^ 2 + c, 2 * st.1 * st.2 + 1)

/-- Tail-recursive real iteration with its derivative coordinate. -/
def realIter (c : ℝ) : Nat → (ℝ × ℝ) → (ℝ × ℝ)
  | 0, st => st
  | n + 1, st => realIter c n (next c st)

/-- The real version of a rational algebraic joint state. -/
def jointValue (st : ExactJoint) : ℝ × ℝ :=
  (value st.orbit, value st.deriv)

/-- The precise rational joint recurrence commutes with real embedding. -/
theorem jointValue_next (c : ExactFraction) (st : ExactJoint) :
    jointValue (exactJointNext c st) =
      next (value c) (jointValue st) := by
  apply Prod.ext
  · simp [jointValue, next, exactJointNext, fnext,
      value_add, value_square]
  · simp [jointValue, next, exactJointNext,
      value_add, value_mul, value_double, value_one]

/-- Every rational algebraic iteration, at any time, is exactly the
    corresponding real joint iteration. No approximation is used here. -/
theorem jointValue_iter (c : ExactFraction)
    (n : Nat) (st : ExactJoint) :
    jointValue (exactJointIter c n st) =
      realIter (value c) n (jointValue st) := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
      change jointValue (exactJointIter c n (exactJointNext c st)) =
        realIter (value c) n (next (value c) (jointValue st))
      rw [ih, jointValue_next]

/-- The orbit field of a rational joint iteration is the earlier,
    independently certified rational orbit recurrence. -/
theorem exactJoint_orbit (c : ExactFraction)
    (n : Nat) (st : ExactJoint) :
    (exactJointIter c n st).orbit = exactIter c n st.orbit := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
      change (exactJointIter c n (exactJointNext c st)).orbit =
        exactIter c n (fnext c st.orbit)
      exact ih (exactJointNext c st)

/-- A useful algebraic time-order identity for the tail recursion. -/
theorem realIter_succ (c : ℝ) (n : Nat) (st : ℝ × ℝ) :
    realIter c (n + 1) st = next c (realIter c n st) := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
      change realIter c (n + 1) (next c st) =
        next c (realIter c n (next c st))
      exact ih (next c st)

/-- The actual critical-orbit and parameter-derivative polynomials:
    these are ordinary functions on the real line, not rounded intervals. -/
def state (n : Nat) (c : ℝ) : ℝ × ℝ :=
  realIter c n (0,0)

def polynomial (n : Nat) (c : ℝ) : ℝ := (state n c).1

def derivativePolynomial (n : Nat) (c : ℝ) : ℝ := (state n c).2

theorem state_zero (c : ℝ) : state 0 c = (0,0) := rfl

theorem state_succ (n : Nat) (c : ℝ) :
    state (n+1) c = next c (state n c) := by
  exact realIter_succ c n (0,0)

/-- This is the *calculus* derivative identity, for every iterate and
    every real parameter: P_n'(c)=D_n(c). The recurrence defining D_n
    is the same as the exact joint arithmetic source. -/
theorem hasDerivAt_polynomial (n : Nat) :
    ∀ c : ℝ,
      HasDerivAt (polynomial n) (derivativePolynomial n c) c := by
  induction n with
  | zero =>
      intro c
      change HasDerivAt (fun _ : ℝ => 0) 0 c
      exact hasDerivAt_const c 0
  | succ n ih =>
      intro c
      have hsquare := (ih c).pow 2
      have hsum := hsquare.add (hasDerivAt_id c)
      have hh : HasDerivAt
          (polynomial n ^ 2 + id)
          (2 * (polynomial n c) * (derivativePolynomial n c) + 1) c := by
        simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hsum
      have heq : polynomial (n+1) = polynomial n ^ 2 + id := by
        funext x
        simp [polynomial, state_succ, next]
      have hd : derivativePolynomial (n+1) c =
          2 * polynomial n c * derivativePolynomial n c + 1 := by
        simp [derivativePolynomial, polynomial, state_succ, next]
      rw [heq, hd]
      exact hh

/-- Both real orbit and real derivative recurrence are continuous for
    arbitrary time and all real parameters. -/
theorem state_continuous (n : Nat) :
    Continuous (state n) := by
  induction n with
  | zero =>
      change Continuous (fun _ : ℝ => ((0:ℝ), (0:ℝ)))
      fun_prop
  | succ n ih =>
      have heq : state (n+1) =
          fun c : ℝ => next c (state n c) := by
        funext c
        exact state_succ n c
      rw [heq]
      change Continuous
        (fun c : ℝ =>
          ((state n c).1 ^ 2 + c,
            2 * (state n c).1 * (state n c).2 + 1))
      fun_prop

theorem polynomial_continuous (n : Nat) :
    Continuous (polynomial n) := by
  change Continuous (fun c => (state n c).1)
  exact continuous_fst.comp (state_continuous n)

theorem derivativePolynomial_continuous (n : Nat) :
    Continuous (derivativePolynomial n) := by
  change Continuous (fun c => (state n c).2)
  exact continuous_snd.comp (state_continuous n)

/-- Both dyadic endpoints, exactly as represented by the source.
    They are not decimal approximations. -/
def left : ℝ := value lowerEndpointFraction
def right : ℝ := value upperEndpointFraction

theorem left_lt_right : left < right := by
  have hu : (0 : ℝ) < (unit : ℝ) := by
    exact_mod_cast (show (0 : Int) < unit by decide +kernel)
  have hstep : parameterLower < parameterLower + parameterStep := by
    have hp : (0 : Int) < parameterStep := by decide +kernel
    omega
  change ((parameterLower : ℝ) / (unit : ℝ)) <
      (((parameterLower + parameterStep : Int) : ℝ) / (unit : ℝ))
  exact (div_lt_div_iff_of_pos_right hu).mpr
    (by exact_mod_cast hstep)

/-- A positive exact rational numerator (with positive denominator)
    corresponds to a genuinely positive real value. -/
theorem value_pos {x : ExactFraction} (h : 0 < x.num) :
    0 < value x := by
  exact div_pos (by exact_mod_cast h) (den_pos x)

theorem value_neg {x : ExactFraction} (h : x.num < 0) :
    value x < 0 := by
  exact div_neg_of_neg_of_pos (by exact_mod_cast h) (den_pos x)

/-- The raw source endpoint signs become signs of the real orbit
    polynomial, via the exact fraction-to-real algebraic homomorphism. -/
theorem lower_real_sign : 0 < polynomial 27 left := by
  have h : 0 < (exactJointIter lowerEndpointFraction 27 zeroJoint).orbit.num := by
    simpa [exactJoint_orbit, zeroJoint] using
      exact_lower_endpoint_critical_iterate_positive
  have hval := value_pos h
  have hemb := jointValue_iter lowerEndpointFraction 27 zeroJoint
  change 0 < (state 27 (value lowerEndpointFraction)).1
  have h0 : jointValue zeroJoint = ((0:ℝ), (0:ℝ)) := by
    simp [jointValue, zeroJoint, value_zero]
  rw [h0] at hemb
  exact (congrArg Prod.fst hemb) ▸ hval

theorem upper_real_sign : polynomial 27 right < 0 := by
  have h : (exactJointIter upperEndpointFraction 27 zeroJoint).orbit.num < 0 := by
    simpa [exactJoint_orbit, zeroJoint] using
      exact_upper_endpoint_critical_iterate_negative
  have hval := value_neg h
  have hemb := jointValue_iter upperEndpointFraction 27 zeroJoint
  change (state 27 (value upperEndpointFraction)).1 < 0
  have h0 : jointValue zeroJoint = ((0:ℝ), (0:ℝ)) := by
    simp [jointValue, zeroJoint, value_zero]
  rw [h0] at hemb
  exact (congrArg Prod.fst hemb) ▸ hval

/-- REAL EXISTENCE: from verified exact rational endpoint signs, via
    the classical intermediate value theorem. There is at least one
    real critical-period-27 *candidate* root inside the tiny bracket.
    Exact period and root uniqueness are separate obligations. -/
theorem exists_real_period27_root :
    ∃ c : ℝ, left < c ∧ c < right ∧ polynomial 27 c = 0 := by
  let g : ℝ → ℝ := fun c => -polynomial 27 c
  have hg : ContinuousOn g (Set.Icc left right) := by
    dsimp [g]
    exact (polynomial_continuous 27).neg.continuousOn
  have hleft : g left < 0 := by
    dsimp [g]
    linarith [lower_real_sign]
  have hright : 0 < g right := by
    dsimp [g]
    linarith [upper_real_sign]
  have himage : (0 : ℝ) ∈ g '' Set.Icc left right :=
    (intermediate_value_Icc left_lt_right.le hg) ⟨hleft.le, hright.le⟩
  obtain ⟨c, hc, hzero⟩ := himage
  refine ⟨c, ?_, ?_, ?_⟩
  · rcases hc with ⟨hcl, hcr⟩
    rcases hcl.eq_or_lt with heq | hlt
    · subst c
      exact False.elim ((ne_of_lt hleft) hzero)
    · exact hlt
  · rcases hc with ⟨hcl, hcr⟩
    rcases hcr.eq_or_lt with heq | hlt
    · subst c
      exact False.elim ((ne_of_gt hright) hzero)
    · exact hlt
  · dsimp [g] at hzero
    linarith

#print axioms hasDerivAt_polynomial
#print axioms lower_real_sign
#print axioms upper_real_sign
#print axioms exists_real_period27_root

end

end LoopsRealPeriod27
