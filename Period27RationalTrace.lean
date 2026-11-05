import Period27IntervalSound

/-!
# Rational enclosure preservation under arbitrary quadratic iteration

This module provides a formal soundness bridge between the integer
interval operations and the actual rational polynomial recurrence.

A mathematical rational is represented by an integer numerator and a
strictly positive integer denominator. FractionEnclosed is an exact
cross-multiplied condition, not a numerical approximation. Since all
rational values have such a representation, the theorems apply to
arbitrary rational inputs including off-grid fractions.

Theorems are parametric in the number of iterates, so no induction
conclusion is asserted by a finite 27-step decide computation.

What is NOT closed: IVT/MVT for the real parameter, real root
existence/uniqueness, actual complex polynomial-like source geometry,
MLC and KL ray/sheet transport.
-/

namespace LoopsFormal.Period27

/-- A positive-denominator representation of any rational number. -/
structure ExactFraction where
  num : Int
  den : Int
  den_pos : 0 < den

def fzero : ExactFraction := ⟨0, 1, by decide⟩
def fone : ExactFraction := ⟨1, 1, by decide⟩

def fadd (a b : ExactFraction) : ExactFraction :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den,
    Int.mul_pos a.den_pos b.den_pos⟩

def fmul (a b : ExactFraction) : ExactFraction :=
  ⟨a.num * b.num, a.den * b.den,
    Int.mul_pos a.den_pos b.den_pos⟩

def fsquare (a : ExactFraction) : ExactFraction :=
  ⟨a.num * a.num, a.den * a.den,
    Int.mul_pos a.den_pos a.den_pos⟩

def fdouble (a : ExactFraction) : ExactFraction :=
  ⟨2 * a.num, a.den, a.den_pos⟩

/-- Exact cross-multiplied rational enclosure at the pinned grid scale. -/
def Encloses (b : Bounds) (x : ExactFraction) : Prop :=
  FractionEnclosed unit b x.num x.den

private theorem scale_positive : 0 < unit := by decide +kernel

theorem zero_fraction_enclosed : Encloses zeroBound fzero := by
  simp [Encloses, FractionEnclosed, fzero, zeroBound, unit]

theorem one_fraction_enclosed : Encloses oneBound fone := by
  simp [Encloses, FractionEnclosed, fone, oneBound, unit]

theorem exact_rational_addition_sound
    (a b : Bounds) (x y : ExactFraction)
    (hx : Encloses a x) (hy : Encloses b y) :
    Encloses (addBounds a b) (fadd x y) := by
  exact signed_add_sound_for_fractions unit a b
    x.num x.den y.num y.den hx hy

theorem exact_rational_multiplication_sound
    (a b : Bounds) (x y : ExactFraction)
    (hx : Encloses a x) (hy : Encloses b y) :
    Encloses (mulBounds a b) (fmul x y) := by
  exact signed_mul_sound_for_fractions unit scale_positive a b
    x.num x.den y.num y.den hx hy

theorem exact_rational_square_sound
    (a : Bounds) (x : ExactFraction)
    (hx : Encloses a x) :
    Encloses (squareBounds a) (fsquare x) := by
  exact signed_square_sound_for_fractions unit scale_positive a
    x.num x.den hx

theorem exact_rational_double_sound
    (a : Bounds) (x : ExactFraction)
    (hx : Encloses a x) :
    Encloses (doubleBounds a) (fdouble x) := by
  exact signed_double_sound_for_fractions unit a x.num x.den hx

/-- One exact parameter-dependent quadratic step on fractions. -/
def fnext (c x : ExactFraction) : ExactFraction :=
  fadd (fsquare x) c

/-- One outward interval step from the source dyadic engine encloses
    the corresponding exact quadratic operation on any rational. -/
theorem nextOrbit_encloses_rational
    (C X : Bounds) (c x : ExactFraction)
    (hc : Encloses C c) (hx : Encloses X x) :
    Encloses (nextOrbit C X) (fnext c x) := by
  exact exact_rational_addition_sound
    (squareBounds X) C (fsquare x) c
    (exact_rational_square_sound X x hx) hc

/-- The same recursive order as pointAfterAt, on exact rational
    fractions rather than rounded integer intervals. -/
def exactIter (c : ExactFraction) :
    Nat → ExactFraction → ExactFraction
  | 0, x => x
  | n + 1, x => exactIter c n (fnext c x)

/-- Universal rational soundness for the ACTUAL quadratic orbit.
    For every n, all rational parameters c in the selected interval
    and all rational initial values x in the starting interval are
    enclosed by pointAfterAt after n iterations. -/
theorem pointAfterAt_encloses_all_rational_orbits
    (C : Bounds) (c : ExactFraction) (hc : Encloses C c)
    (n : Nat) (X : Bounds) (x : ExactFraction)
    (hx : Encloses X x) :
    Encloses (pointAfterAt unit n C X) (exactIter c n x) := by
  induction n generalizing X x with
  | zero =>
      simpa only [pointAfterAt, exactIter] using hx
  | succ n ih =>
      exact ih (nextOrbit C X) (fnext c x)
        (nextOrbit_encloses_rational C X c x hc hx)

/-- Strict interval positivity implies exact rational numerator
    positivity, without evaluating or approximating that fraction. -/
theorem numerator_pos_of_positive_interval
    (b : Bounds) (x : ExactFraction)
    (hpositive : 0 < b.lo)
    (hx : Encloses b x) :
    0 < x.num := by
  rcases hx with ⟨hd, hlo, _⟩
  have hbprod : 0 < b.lo * x.den := Int.mul_pos hpositive hd
  have hnprod : 0 < x.num * unit := by omega
  exact Int.pos_of_mul_pos_left hnprod scale_positive

/-- A negative upper interval bound implies a negative exact
    rational numerator; the denominator is already strictly positive. -/
theorem numerator_neg_of_negative_interval
    (b : Bounds) (x : ExactFraction)
    (hnegative : b.hi < 0)
    (hx : Encloses b x) :
    x.num < 0 := by
  rcases hx with ⟨hd, _, hhi⟩
  have hbprod : b.hi * x.den < 0 :=
    Int.mul_neg_of_neg_of_pos hnegative hd
  have hnprod : x.num * unit < 0 := by omega
  exact Int.neg_of_mul_neg_left hnprod scale_positive

#print axioms signed_square_sound_for_fractions
#print axioms nextOrbit_encloses_rational
#print axioms pointAfterAt_encloses_all_rational_orbits
#print axioms numerator_pos_of_positive_interval

end LoopsFormal.Period27
