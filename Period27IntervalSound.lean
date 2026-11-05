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


/-- A fraction n/d with d>0 is inside a signed grid interval when
    all three terms of this cross-multiplied inequality hold.
    This represents an ARBITRARY rational, not only grid points. -/
def FractionEnclosed (scale : Int) (b : Bounds)
    (numer denom : Int) : Prop :=
  0 < denom ∧
  b.lo * denom ≤ numer * scale ∧
  numer * scale ≤ b.hi * denom

/-- Arithmetic addition soundness for arbitrary rational inputs.
    No assumption that either exact input lies on the dyadic grid. -/
theorem signed_add_sound_for_fractions
    (scale : Int) (a b : Bounds)
    (na da nb db : Int)
    (ha : FractionEnclosed scale a na da)
    (hb : FractionEnclosed scale b nb db) :
    FractionEnclosed scale (addBounds a b)
      (na * db + nb * da) (da * db) := by
  rcases ha with ⟨hda, halo, hahi⟩
  rcases hb with ⟨hdb, hblo, hbhi⟩
  have hda0 : 0 ≤ da := by omega
  have hdb0 : 0 ≤ db := by omega
  have hloA := Int.mul_le_mul_of_nonneg_right halo hdb0
  have hloB := Int.mul_le_mul_of_nonneg_right hblo hda0
  have hhiA := Int.mul_le_mul_of_nonneg_right hahi hdb0
  have hhiB := Int.mul_le_mul_of_nonneg_right hbhi hda0
  dsimp only [FractionEnclosed, addBounds]
  constructor
  · exact Int.mul_pos hda hdb
  constructor
  · have hsum := Int.add_le_add hloA hloB
    grind
  · have hsum := Int.add_le_add hhiA hhiB
    grind


/-- Full rounding-and-rectangle containment for arbitrary rational
    values na/da and nb/db, with positive denominators. This extends
    signed_multiplication_rounding_sound_on_grid to inputs that are
    NOT represented exactly on the working dyadic grid. -/
theorem signed_mul_sound_for_fractions
    (scale : Int) (hscale : 0 < scale)
    (a b : Bounds)
    (na da nb db : Int)
    (ha : FractionEnclosed scale a na da)
    (hb : FractionEnclosed scale b nb db) :
    FractionEnclosed scale (mulBoundsAt scale a b)
      (na * nb) (da * db) := by
  rcases ha with ⟨hda, halo, hahi⟩
  rcases hb with ⟨hdb, hblo, hbhi⟩
  let L : Int :=
    min (min (a.lo * b.lo) (a.lo * b.hi))
        (min (a.hi * b.lo) (a.hi * b.hi))
  let U : Int :=
    max (max (a.lo * b.lo) (a.lo * b.hi))
        (max (a.hi * b.lo) (a.hi * b.hi))
  have hden : 0 ≤ da * db := Int.le_of_lt (Int.mul_pos hda hdb)
  have hdown : (L / scale) * scale ≤ L :=
    signed_floor_rounds_outward L scale hscale
  have hup : U ≤ (- ((-U) / scale)) * scale :=
    signed_ceil_rounds_outward U scale hscale
  have hL1 : L ≤ a.lo * b.lo :=
    Int.le_trans (Int.min_le_left ..) (Int.min_le_left ..)
  have hL2 : L ≤ a.lo * b.hi :=
    Int.le_trans (Int.min_le_left ..) (Int.min_le_right ..)
  have hL3 : L ≤ a.hi * b.lo :=
    Int.le_trans (Int.min_le_right ..) (Int.min_le_left ..)
  have hL4 : L ≤ a.hi * b.hi :=
    Int.le_trans (Int.min_le_right ..) (Int.min_le_right ..)
  have hU1 : a.lo * b.lo ≤ U :=
    Int.le_trans (Int.le_max_left ..) (Int.le_max_left ..)
  have hU2 : a.lo * b.hi ≤ U :=
    Int.le_trans (Int.le_max_right ..) (Int.le_max_left ..)
  have hU3 : a.hi * b.lo ≤ U :=
    Int.le_trans (Int.le_max_left ..) (Int.le_max_right ..)
  have hU4 : a.hi * b.hi ≤ U :=
    Int.le_trans (Int.le_max_right ..) (Int.le_max_right ..)
  have cornerLower (p q : Int) (hl : L ≤ p * q) :
      ((L / scale) * scale) * (da * db) ≤
        (p * da) * (q * db) := by
    calc
      ((L / scale) * scale) * (da * db)
          ≤ (p * q) * (da * db) :=
            Int.mul_le_mul_of_nonneg_right (Int.le_trans hdown hl) hden
      _ = (p * da) * (q * db) := by ac_rfl
  have cornerUpper (p q : Int) (hu : p * q ≤ U) :
      (p * da) * (q * db) ≤
        ((- ((-U) / scale)) * scale) * (da * db) := by
    calc
      (p * da) * (q * db) = (p * q) * (da * db) := by ac_rfl
      _ ≤ ((- ((-U) / scale)) * scale) * (da * db) :=
        Int.mul_le_mul_of_nonneg_right (Int.le_trans hu hup) hden
  have hbox :=
    integer_product_between_four_corners
      (⟨a.lo * da, a.hi * da⟩ : Bounds)
      (⟨b.lo * db, b.hi * db⟩ : Bounds)
      (na * scale) (nb * scale)
      halo hahi hblo hbhi
  have hlowbox :
      ((L / scale) * scale) * (da * db) ≤
        (na * scale) * (nb * scale) := by
    have hcorner :
        ((L / scale) * scale) * (da * db) ≤
          min
            (min ((a.lo * da) * (b.lo * db))
                 ((a.lo * da) * (b.hi * db)))
            (min ((a.hi * da) * (b.lo * db))
                 ((a.hi * da) * (b.hi * db))) :=
      Int.le_min.mpr
        ⟨Int.le_min.mpr ⟨cornerLower a.lo b.lo hL1,
          cornerLower a.lo b.hi hL2⟩,
         Int.le_min.mpr ⟨cornerLower a.hi b.lo hL3,
          cornerLower a.hi b.hi hL4⟩⟩
    exact Int.le_trans hcorner hbox.1
  have hhighbox :
      (na * scale) * (nb * scale) ≤
        ((- ((-U) / scale)) * scale) * (da * db) := by
    have hcorner :
        max
          (max ((a.lo * da) * (b.lo * db))
               ((a.lo * da) * (b.hi * db)))
          (max ((a.hi * da) * (b.lo * db))
               ((a.hi * da) * (b.hi * db))) ≤
        ((- ((-U) / scale)) * scale) * (da * db) :=
      Int.max_le.mpr
        ⟨Int.max_le.mpr ⟨cornerUpper a.lo b.lo hU1,
          cornerUpper a.lo b.hi hU2⟩,
         Int.max_le.mpr ⟨cornerUpper a.hi b.lo hU3,
          cornerUpper a.hi b.hi hU4⟩⟩
    exact Int.le_trans hbox.2 hcorner
  have hlower :
      (L / scale) * (da * db) ≤ (na * nb) * scale := by
    apply Int.le_of_mul_le_mul_right (by
      calc
        ((L / scale) * (da * db)) * scale =
            ((L / scale) * scale) * (da * db) := by ac_rfl
        _ ≤ (na * scale) * (nb * scale) := hlowbox
        _ = ((na * nb) * scale) * scale := by ac_rfl) hscale
  have hupper :
      (na * nb) * scale ≤ (- ((-U) / scale)) * (da * db) := by
    apply Int.le_of_mul_le_mul_right (by
      calc
        ((na * nb) * scale) * scale =
            (na * scale) * (nb * scale) := by ac_rfl
        _ ≤ ((- ((-U) / scale)) * scale) * (da * db) := hhighbox
        _ = ((- ((-U) / scale)) * (da * db)) * scale := by ac_rfl) hscale
  dsimp only [FractionEnclosed]
  constructor
  · exact Int.mul_pos hda hdb
  constructor
  · change (L / scale) * (da * db) ≤ (na * nb) * scale
    exact hlower
  · change (na * nb) * scale ≤ (- ((-U) / scale)) * (da * db)
    exact hupper


/-- The zero-crossing-aware squaring algorithm encloses the square of
    ANY rational input n/d whose endpoints are in a signed grid interval.
    A rational is represented directly by integer cross-products;
    no rounding assumption on its numerator or denominator is made. -/
theorem signed_square_sound_for_fractions
    (scale : Int) (hscale : 0 < scale)
    (a : Bounds) (n d : Int)
    (ha : FractionEnclosed scale a n d) :
    FractionEnclosed scale (squareBoundsAt scale a) (n * n) (d * d) := by
  rcases ha with ⟨hd, hlo, hhi⟩
  let L : Int :=
    if a.lo ≤ 0 ∧ 0 ≤ a.hi then 0
    else min (a.lo * a.lo) (a.hi * a.hi)
  let U : Int := max (a.lo * a.lo) (a.hi * a.hi)
  have hden : 0 ≤ d * d := Int.mul_nonneg (by omega) (by omega)
  have hroundlow : (L / scale) * scale ≤ L :=
    signed_floor_rounds_outward L scale hscale
  have hroundup : U ≤ (- ((-U) / scale)) * scale :=
    signed_ceil_rounds_outward U scale hscale
  have hsquare := integer_square_between_endpoints
    (a.lo * d) (a.hi * d) (n * scale) hlo hhi
  have hmainlower :
      ((L / scale) * scale) * (d * d) ≤
        (n * scale) * (n * scale) := by
    by_cases hcross : a.lo ≤ 0 ∧ 0 ≤ a.hi
    · have hz : 0 ≤ (n * scale) * (n * scale) := by
        by_cases hp : 0 ≤ n * scale
        · exact Int.mul_nonneg hp hp
        · exact Int.mul_nonneg_of_nonpos_of_nonpos
            (by omega) (by omega)
      have hL : L = 0 := by simp [L, hcross]
      have hlow0 : (L / scale) * scale ≤ 0 := by
        simpa only [hL] using hroundlow
      exact Int.le_trans
        (Int.mul_le_mul_of_nonneg_right hlow0 hden)
        (by simpa using hz)
    · have hcscaled : ¬ (a.lo * d ≤ 0 ∧ 0 ≤ a.hi * d) := by
        intro hc
        have hl : a.lo ≤ 0 :=
          Int.nonpos_of_mul_nonpos_left hc.1 hd
        have hh : 0 ≤ a.hi :=
          Int.nonneg_of_mul_nonneg_left hc.2 hd
        exact hcross ⟨hl, hh⟩
      have hsqscaled :
          min ((a.lo * d) * (a.lo * d))
              ((a.hi * d) * (a.hi * d)) ≤
            (n * scale) * (n * scale) := by
        simpa only [hcscaled, ↓reduceIte] using hsquare.1
      have hLmin : L = min (a.lo * a.lo) (a.hi * a.hi) := by
        simp only [L, hcross, ↓reduceIte]
      have hL1 : ((L / scale) * scale) ≤ a.lo * a.lo :=
        Int.le_trans hroundlow (by
          rw [hLmin]
          exact Int.min_le_left ..)
      have hL2 : ((L / scale) * scale) ≤ a.hi * a.hi :=
        Int.le_trans hroundlow (by
          rw [hLmin]
          exact Int.min_le_right ..)
      have hC1 :
          ((L / scale) * scale) * (d * d) ≤
            (a.lo * d) * (a.lo * d) := by
        calc
          _ ≤ (a.lo * a.lo) * (d * d) :=
            Int.mul_le_mul_of_nonneg_right hL1 hden
          _ = (a.lo * d) * (a.lo * d) := by ac_rfl
      have hC2 :
          ((L / scale) * scale) * (d * d) ≤
            (a.hi * d) * (a.hi * d) := by
        calc
          _ ≤ (a.hi * a.hi) * (d * d) :=
            Int.mul_le_mul_of_nonneg_right hL2 hden
          _ = (a.hi * d) * (a.hi * d) := by ac_rfl
      exact Int.le_trans (Int.le_min.mpr ⟨hC1, hC2⟩) hsqscaled
  have hmainupper :
      (n * scale) * (n * scale) ≤
        ((- ((-U) / scale)) * scale) * (d * d) := by
    have hU1 : a.lo * a.lo ≤ U := Int.le_max_left ..
    have hU2 : a.hi * a.hi ≤ U := Int.le_max_right ..
    have hC1 :
        (a.lo * d) * (a.lo * d) ≤
          ((- ((-U) / scale)) * scale) * (d * d) := by
      calc
        _ = (a.lo * a.lo) * (d * d) := by ac_rfl
        _ ≤ U * (d * d) :=
          Int.mul_le_mul_of_nonneg_right hU1 hden
        _ ≤ ((- ((-U) / scale)) * scale) * (d * d) :=
          Int.mul_le_mul_of_nonneg_right hroundup hden
    have hC2 :
        (a.hi * d) * (a.hi * d) ≤
          ((- ((-U) / scale)) * scale) * (d * d) := by
      calc
        _ = (a.hi * a.hi) * (d * d) := by ac_rfl
        _ ≤ U * (d * d) :=
          Int.mul_le_mul_of_nonneg_right hU2 hden
        _ ≤ ((- ((-U) / scale)) * scale) * (d * d) :=
          Int.mul_le_mul_of_nonneg_right hroundup hden
    exact Int.le_trans hsquare.2 (Int.max_le.mpr ⟨hC1, hC2⟩)
  have hfraclower :
      (L / scale) * (d * d) ≤ (n * n) * scale := by
    apply Int.le_of_mul_le_mul_right (by
      calc
        ((L / scale) * (d * d)) * scale =
          ((L / scale) * scale) * (d * d) := by ac_rfl
        _ ≤ (n * scale) * (n * scale) := hmainlower
        _ = ((n * n) * scale) * scale := by ac_rfl) hscale
  have hfracupper :
      (n * n) * scale ≤ (- ((-U) / scale)) * (d * d) := by
    apply Int.le_of_mul_le_mul_right (by
      calc
        ((n * n) * scale) * scale =
            (n * scale) * (n * scale) := by ac_rfl
        _ ≤ ((- ((-U) / scale)) * scale) * (d * d) := hmainupper
        _ = ((- ((-U) / scale)) * (d * d)) * scale := by ac_rfl) hscale
  dsimp only [FractionEnclosed]
  constructor
  · exact Int.mul_pos hd hd
  constructor
  · change (L / scale) * (d * d) ≤ (n * n) * scale
    exact hfraclower
  · change (n * n) * scale ≤ (- ((-U) / scale)) * (d * d)
    exact hfracupper

/-- Multiplication by two is sound on arbitrary rational inputs. -/
theorem signed_double_sound_for_fractions
    (scale : Int) (a : Bounds)
    (n d : Int) (h : FractionEnclosed scale a n d) :
    FractionEnclosed scale (doubleBounds a) (2 * n) d := by
  rcases h with ⟨hd, hlo, hhi⟩
  dsimp only [FractionEnclosed, doubleBounds]
  constructor
  · exact hd
  constructor
  · have hw := Int.mul_le_mul_of_nonneg_left hlo (by omega : (0 : Int) ≤ 2)
    grind
  · have hw := Int.mul_le_mul_of_nonneg_left hhi (by omega : (0 : Int) ≤ 2)
    grind

#print axioms signed_floor_rounds_outward
#print axioms signed_ceil_rounds_outward
#print axioms integer_square_between_endpoints
#print axioms signed_square_rounding_sound_on_grid
#print axioms integer_product_between_four_corners
#print axioms signed_add_sound_for_fractions
#print axioms signed_mul_sound_for_fractions
#print axioms signed_square_sound_for_fractions
#print axioms signed_double_sound_for_fractions
#print axioms signed_multiplication_rounding_sound_on_grid

end LoopsFormal.Period27
