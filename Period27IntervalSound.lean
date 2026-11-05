import Period27Dyadic

/-!
# Signed interval rounding and squaring: kernel-checked universal lemmas

Earlier certificates checked the VALUES returned by dyadic interval
operations. This module starts proving that their ARITHMETIC
definitions are sound, for *arbitrary signed integer arguments*.

These are parametric theorems, not data copied from the period-27
orbit. The input grid coordinate x represents x / scale and the
output enclosure, multiplied by scale, bounds the exact integer
product x*x. Additional work is required to extend these claims to
arbitrary rational/real inputs and to the bivariate multiplication
used by the parameter derivative.

No real IVT/MVT, ray theorem, or MLC gate is claimed.
-/

namespace LoopsFormal.Period27

/-- Signed Euclidean integer division rounds downward at any
    nonzero positive grid scale. -/
theorem signed_floor_rounds_outward
    (n scale : Int) (hscale : 0 < scale) :
    (n / scale) * scale ≤ n := by
  exact Int.ediv_mul_le n (by omega)

/-- The negative-floor formula used in both Python and Lean is an
    exact ceiling, valid even for negative input integers. -/
theorem signed_ceil_rounds_outward
    (n scale : Int) (hscale : 0 < scale) :
    n ≤ - ((-n) / scale) * scale := by
  have h : (-n / scale) * scale ≤ -n :=
    signed_floor_rounds_outward (-n) scale hscale
  simpa only [Int.neg_mul, Int.neg_neg] using (neg_le_neg h)

/-- A square cannot escape the squares of the bounding endpoints,
    except that an interval crossing zero has minimum zero.
    No order positivity assumption is made on either endpoint. -/
theorem integer_square_between_endpoints
    (lo hi x : Int) (hl : lo ≤ x) (hh : x ≤ hi) :
    (if lo ≤ 0 ∧ 0 ≤ hi then 0
       else min (lo * lo) (hi * hi)) ≤ x * x ∧
    x * x ≤ max (lo * lo) (hi * hi) := by
  have hnonneg : 0 ≤ x * x := Int.mul_self_nonneg x
  constructor
  · by_cases hcross : lo ≤ 0 ∧ 0 ≤ hi
    · simp only [hcross, ↓reduceIte]
      exact hnonneg
    · simp only [hcross, ↓reduceIte]
      by_cases hleft : 0 ≤ lo
      · have h : lo * lo ≤ x * x :=
          Int.mul_self_le_mul_self hleft hl
        exact le_trans (min_le_left ..) h
      · have hright : hi ≤ 0 := by omega
        have h : -hi ≤ -x := by omega
        have hs : (-hi) * (-hi) ≤ (-x) * (-x) :=
          Int.mul_self_le_mul_self (by omega) h
        have hs' : hi * hi ≤ x * x := by
          simpa only [Int.neg_mul_neg] using hs
        exact le_trans (min_le_right ..) hs'
  · by_cases hx : 0 ≤ x
    · have h : x * x ≤ hi * hi :=
        Int.mul_self_le_mul_self hx hh
      exact le_trans h (le_max_right ..)
    · have h : -x ≤ -lo := by omega
      have hs : (-x) * (-x) ≤ (-lo) * (-lo) :=
        Int.mul_self_le_mul_self (by omega) h
      have hs' : x * x ≤ lo * lo := by
        simpa only [Int.neg_mul_neg] using hs
      exact le_trans hs' (le_max_left ..)

/-- The exact implementation of squareBoundsAt encloses every
    integer grid input lying between the represented endpoints.
    The lower/upper comparisons are in units of 1/scale². -/
theorem signed_square_rounding_sound_on_grid
    (scale : Int) (hscale : 0 < scale)
    (b : Bounds) (x : Int)
    (hl : b.lo ≤ x) (hh : x ≤ b.hi) :
    (squareBoundsAt scale b).lo * scale ≤ x * x ∧
    x * x ≤ (squareBoundsAt scale b).hi * scale := by
  let low := if b.lo ≤ 0 ∧ 0 ≤ b.hi then 0
             else min (b.lo * b.lo) (b.hi * b.hi)
  let high := max (b.lo * b.lo) (b.hi * b.hi)
  have hsquare := integer_square_between_endpoints b.lo b.hi x hl hh
  have hlow : low ≤ x * x := hsquare.1
  have hhigh : x * x ≤ high := hsquare.2
  change (low / scale) * scale ≤ x * x ∧
    x * x ≤ (- ((-high) / scale)) * scale
  exact ⟨(signed_floor_rounds_outward low scale hscale).trans hlow,
    hhigh.trans (signed_ceil_rounds_outward high scale hscale)⟩

/-- Addition of already enclosed values needs no loss of precision. -/
theorem signed_interval_add_sound_on_grid
    (a b : Bounds) (x y : Int)
    (hxlo : a.lo ≤ x) (hxhi : x ≤ a.hi)
    (hylo : b.lo ≤ y) (hyhi : y ≤ b.hi) :
    (addBounds a b).lo ≤ x + y ∧
    x + y ≤ (addBounds a b).hi := by
  dsimp [addBounds]
  constructor <;> omega

/-- Multiplication by two is exact on signed grid coordinates. -/
theorem signed_double_sound_on_grid
    (a : Bounds) (x : Int)
    (hxlo : a.lo ≤ x) (hxhi : x ≤ a.hi) :
    (doubleBounds a).lo ≤ 2 * x ∧
    2 * x ≤ (doubleBounds a).hi := by
  dsimp [doubleBounds]
  constructor <;> omega

#print axioms signed_floor_rounds_outward
#print axioms signed_ceil_rounds_outward
#print axioms integer_square_between_endpoints
#print axioms signed_square_rounding_sound_on_grid

end LoopsFormal.Period27
