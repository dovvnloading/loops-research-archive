import Period27RationalTrace

/-!
# Rational parameter-derivative recurrence and interval soundness

For every rational c in the isolated dyadic parameter bracket, the
source-defined algebraic derivative recurrence
  d_0 = 0, d_(n+1) = 2*x_n*d_n+1
is proved to be enclosed at every stage by the same outward interval
arithmetic engine as the original 27-step signed certificate.

The signed 27th derivative is then proved strictly negative as an
exact rational fraction, via a kernel-checked negative enclosure.
This is a correct algebraic derivative RECURRENCE, but the separate
calculus theorem identifying the recurrence with d/dc f_c^n(0),
real IVT/MVT, and actual existence of the real center are outside
this specific module and remain open tasks.
-/

namespace LoopsFormal.Period27

structure ExactJoint where
  orbit : ExactFraction
  deriv : ExactFraction

/-- Initial exact rational critical orbit and derivative state. -/
def zeroJoint : ExactJoint := ⟨fzero, fzero⟩

/-- One algebraic state transition for f_c and its parameter derivative. -/
def exactJointNext (c : ExactFraction) (st : ExactJoint) : ExactJoint :=
  ⟨fnext c st.orbit,
   fadd (fmul (fdouble st.orbit) st.deriv) fone⟩

def roundedJointNext (C : Bounds) (st : Bounds × Bounds) :
    Bounds × Bounds :=
  ⟨nextOrbit C st.1,
   addBounds (mulBounds (doubleBounds st.1) st.2) oneBound⟩

/-- Soundness of one joint orbit/parameter-derivative transition.
    The parameter and both state coordinates may be any rationals. -/
theorem exact_joint_next_enclosed
    (C X D : Bounds) (c x d : ExactFraction)
    (hc : Encloses C c)
    (hx : Encloses X x) (hd : Encloses D d) :
    Encloses (roundedJointNext C (X,D)).1
      (exactJointNext c ⟨x,d⟩).orbit ∧
    Encloses (roundedJointNext C (X,D)).2
      (exactJointNext c ⟨x,d⟩).deriv := by
  constructor
  · exact nextOrbit_encloses_rational C X c x hc hx
  · exact exact_rational_addition_sound
      (mulBounds (doubleBounds X) D) oneBound
      (fmul (fdouble x) d) fone
      (exact_rational_multiplication_sound
        (doubleBounds X) D (fdouble x) d
        (exact_rational_double_sound X x hx) hd)
      one_fraction_enclosed

def exactJointIter (c : ExactFraction) :
    Nat → ExactJoint → ExactJoint
  | 0, st => st
  | k + 1, st =>
      exactJointIter c k (exactJointNext c st)

def roundedJointIter (C : Bounds) :
    Nat → (Bounds × Bounds) → (Bounds × Bounds)
  | 0, st => st
  | k + 1, st =>
      roundedJointIter C k (roundedJointNext C st)

/-- Uniform correctness for any number of polynomial and parameter
    derivative steps, for every rational parameter in the input
    interval and any rational initial state. -/
theorem joint_rational_trace_enclosed
    (C : Bounds) (c : ExactFraction) (hc : Encloses C c)
    (n : Nat) (st : Bounds × Bounds) (x : ExactJoint)
    (hx : Encloses st.1 x.orbit)
    (hd : Encloses st.2 x.deriv) :
    Encloses (roundedJointIter C n st).1
      (exactJointIter c n x).orbit ∧
    Encloses (roundedJointIter C n st).2
      (exactJointIter c n x).deriv := by
  induction n generalizing st x with
  | zero =>
      exact ⟨hx, hd⟩
  | succ n ih =>
      have hs :=
        exact_joint_next_enclosed C st.1 st.2 c x.orbit x.deriv
          hc hx hd
      exact ih (roundedJointNext C st) (exactJointNext c x)
        hs.1 hs.2

/-- A strict negative derivative enclosure at period 27, recomputed
    by Lean from the fixed signed dyadic recurrence and not assumed. -/
theorem every_bracket_derivative_interval_is_negative :
    ((roundedJointIter centerParameter 27
        (zeroBound, zeroBound)).2).hi < 0 := by
  decide +kernel

/-- A genuine rational semantic conclusion: for every rational c in
    the full parameter bracket, the exact rational algebraic
    parameter-derivative RECURRENCE has a negative numerator.
    The positive denominator is built into ExactFraction. -/
theorem all_rational_bracket_parameter_derivatives_are_negative
    (c : ExactFraction)
    (hc : Encloses centerParameter c) :
    (exactJointIter c 27 zeroJoint).deriv.num < 0 := by
  have h :=
    joint_rational_trace_enclosed centerParameter c hc
      27 (zeroBound, zeroBound) zeroJoint
      zero_fraction_enclosed zero_fraction_enclosed
  exact numerator_neg_of_negative_interval
    (roundedJointIter centerParameter 27 (zeroBound, zeroBound)).2
    (exactJointIter c 27 zeroJoint).deriv
    every_bracket_derivative_interval_is_negative h.2

#print axioms joint_rational_trace_enclosed
#print axioms all_rational_bracket_parameter_derivatives_are_negative

end LoopsFormal.Period27
