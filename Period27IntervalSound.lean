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
  have h' : n ≤ - (((-n / scale) * scale)) := by omega
  simpa only [Int.neg_mul, Int.neg_neg] using h'

/-- A square cannot escape the squares of the bounding endpoints,
    except that an interval crossing zero has minimum zero.
    No order positivity assumption is made on either endpoint. -/
theorem integer_square_between_endpoints
    (lo hi x : Int) (hl : lo ≤ x) (hh : x ≤ hi) :
    (if lo ≤ 0 ∧ 0 ≤ hi then 0
       else min (lo * lo) (hi * hi)) ≤ x * x ∧
    x * x ≤ max (lo * lo) (hi * hi) := by
  have hnonneg : 0 ≤ x * x := by
    by_cases hx : 0 ≤ x
    · exact Int.mul_nonneg hx hx
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  constructor
  · by_cases hcross : lo ≤ 0 ∧ 0 ≤ hi
    · simp only [hcross, ↓reduceIte]
      exact hnonneg
    · simp only [hcross, ↓reduceIte]
      by_cases hleft : 0 ≤ lo
      · have h : lo * lo ≤ x * x :=
          Int.mul_self_le_mul_self hleft hl
        exact Int.le_trans (Int.min_le_left ..) h
      · have hright : hi ≤ 0 := by omega
        have h : -hi ≤ -x := by omega
        have hs : (-hi) * (-hi) ≤ (-x) * (-x) :=
          Int.mul_self_le_mul_self (by omega) h
        have hs' : hi * hi ≤ x * x := by
          simpa only [Int.neg_mul_neg] using hs
        exact Int.le_trans (Int.min_le_right ..) hs'
  · by_cases hx : 0 ≤ x
    · have h : x * x ≤ hi * hi :=
        Int.mul_self_le_mul_self hx hh
      exact Int.le_trans h (Int.le_max_right ..)
    · have h : -x ≤ -lo := by omega
      have hs : (-x) * (-x) ≤ (-lo) * (-lo) :=
        Int.mul_self_le_mul_self (by omega) h
      have hs' : x * x ≤ lo * lo := by
        simpa only [Int.neg_mul_neg] using hs
      exact Int.le_trans hs' (Int.le_max_left ..)

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
  exact ⟨Int.le_trans (signed_floor_rounds_outward low scale hscale) hlow,
    Int.le_trans hhigh (signed_ceil_rounds_outward high scale hscale)⟩


/-- A product z*t lies between the two endpoint products regardless
    of the sign of t. This is the one-dimensional rectangle lemma. -/
private theorem integer_product_between_two_endpoints
    (lo hi z t : Int) (hl : lo ≤ z) (hh : z ≤ hi) :
    min (lo * t) (hi * t) ≤ z * t ∧
    z * t ≤ max (lo * t) (hi * t) := by
  by_cases ht : 0 ≤ t
  · have h1 := Int.mul_le_mul_of_nonneg_right hl ht
    have h2 := Int.mul_le_mul_of_nonneg_right hh ht
    constructor
    · exact Int.le_trans (Int.min_le_left ..) h1
    · exact Int.le_trans h2 (Int.le_max_right ..)
  · have ht' : t ≤ 0 := by omega
    have h1 := Int.mul_le_mul_of_nonpos_right hh ht'
    have h2 := Int.mul_le_mul_of_nonpos_right hl ht'
    constructor
    · exact Int.le_trans (Int.min_le_right ..) h1
    · exact Int.le_trans h2 (Int.le_max_left ..)

/-- The full four-corner multiplication theorem for any signed
    integer rectangle. Neither interval needs to avoid zero. -/
theorem integer_product_between_four_corners
    (a b : Bounds) (x y : Int)
    (hax : a.lo ≤ x) (hxa : x ≤ a.hi)
    (hby : b.lo ≤ y) (hyb : y ≤ b.hi) :
    min (min (a.lo * b.lo) (a.lo * b.hi))
        (min (a.hi * b.lo) (a.hi * b.hi)) ≤ x * y ∧
    x * y ≤
      max (max (a.lo * b.lo) (a.lo * b.hi))
          (max (a.hi * b.lo) (a.hi * b.hi)) := by
  let low :=
    min (min (a.lo * b.lo) (a.lo * b.hi))
        (min (a.hi * b.lo) (a.hi * b.hi))
  let high :=
    max (max (a.lo * b.lo) (a.lo * b.hi))
        (max (a.hi * b.lo) (a.hi * b.hi))
  have hax' := integer_product_between_two_endpoints a.lo a.hi x y hax hxa
  have hbylo := integer_product_between_two_endpoints b.lo b.hi y a.lo hby hyb
  have hbyhi := integer_product_between_two_endpoints b.lo b.hi y a.hi hby hyb
  have hlo_lo :
      min (a.lo * b.lo) (a.lo * b.hi) ≤ a.lo * y := by
    simpa only [Int.mul_comm a.lo b.lo,
      Int.mul_comm a.lo b.hi, Int.mul_comm a.lo y] using hbylo.1
  have hhi_lo :
      min (a.hi * b.lo) (a.hi * b.hi) ≤ a.hi * y := by
    simpa only [Int.mul_comm a.hi b.lo,
      Int.mul_comm a.hi b.hi, Int.mul_comm a.hi y] using hbyhi.1
  have hlo_hi :
      a.lo * y ≤ max (a.lo * b.lo) (a.lo * b.hi) := by
    simpa only [Int.mul_comm a.lo b.lo,
      Int.mul_comm a.lo b.hi, Int.mul_comm a.lo y] using hbylo.2
  have hhi_hi :
      a.hi * y ≤ max (a.hi * b.lo) (a.hi * b.hi) := by
    simpa only [Int.mul_comm a.hi b.lo,
      Int.mul_comm a.hi b.hi, Int.mul_comm a.hi y] using hbyhi.2
  have hlowlo : low ≤ a.lo * y :=
    Int.le_trans (Int.min_le_left ..) hlo_lo
  have hlowhi : low ≤ a.hi * y :=
    Int.le_trans (Int.min_le_right ..) hhi_lo
  have hhighlo : a.lo * y ≤ high :=
    Int.le_trans hlo_hi (Int.le_max_left ..)
  have hhighhi : a.hi * y ≤ high :=
    Int.le_trans hhi_hi (Int.le_max_right ..)
  have hlow : low ≤ min (a.lo * y) (a.hi * y) :=
    Int.le_min.mpr ⟨hlowlo, hlowhi⟩
  have hhigh : max (a.lo * y) (a.hi * y) ≤ high :=
    Int.max_le.mpr ⟨hhighlo, hhighhi⟩
  exact ⟨Int.le_trans hlow hax'.1, Int.le_trans hax'.2 hhigh⟩

/-- Kernel-proved signed outward multiplication. For arbitrary integer
    grid inputs x and y in the two bounds, the exact product x*y is
    enclosed by the interval generated by mulBoundsAt, in signed
    integer grid units. -/
theorem signed_multiplication_rounding_sound_on_grid
    (scale : Int) (hscale : 0 < scale)
    (a b : Bounds) (x y : Int)
    (hax : a.lo ≤ x) (hxa : x ≤ a.hi)
    (hby : b.lo ≤ y) (hyb : y ≤ b.hi) :
    (mulBoundsAt scale a b).lo * scale ≤ x * y ∧
    x * y ≤ (mulBoundsAt scale a b).hi * scale := by
  let low :=
    min (min (a.lo * b.lo) (a.lo * b.hi))
        (min (a.hi * b.lo) (a.hi * b.hi))
  let high :=
    max (max (a.lo * b.lo) (a.lo * b.hi))
        (max (a.hi * b.lo) (a.hi * b.hi))
  have hbox := integer_product_between_four_corners a b x y hax hxa hby hyb
  have hlo : low ≤ x * y := hbox.1
  have hhi : x * y ≤ high := hbox.2
  change (low / scale) * scale ≤ x * y ∧
    x * y ≤ (- ((-high) / scale)) * scale
  exact ⟨Int.le_trans (signed_floor_rounds_outward low scale hscale) hlo,
    Int.le_trans hhi (signed_ceil_rounds_outward high scale hscale)⟩

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
#print axioms integer_product_between_four_corners
#print axioms signed_multiplication_rounding_sound_on_grid

end LoopsFormal.Period27
