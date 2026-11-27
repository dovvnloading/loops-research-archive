import Period27RealCenter
import DepthThreeCert

/-!
# Real semantics of the depth-three integer certificates

The scale is arbitrary and every enclosure below applies to every real
parameter in its interval. The collision polynomial is the actual critical
orbit relation `x_(3*n) + x_(6*n)`, with `x_0 = 0` and
`x_(j+1) = x_j^2 + c`. Strict interval certificates produce unique real
roots by the intermediate value theorem and the derivative criterion.
-/

namespace LoopsDepthThreeReal

open Set
open LoopsFormal.Period27
open LoopsFormal.DepthThree

noncomputable section

/-- A signed integer interval encloses a real value in units of `1 / S`.
The multiplication form avoids any rounding of the real input. -/
def RealEnclosed (S : Int) (b : Bounds) (x : ℝ) : Prop :=
  (b.lo : ℝ) ≤ x * (S : ℝ) ∧ x * (S : ℝ) ≤ (b.hi : ℝ)

private theorem scale_pos {S : Int} (hS : 0 < S) : 0 < (S : ℝ) := by
  exact_mod_cast hS

theorem realEnclosed_iff {S : Int} (hS : 0 < S) (b : Bounds) (x : ℝ) :
    RealEnclosed S b x ↔
      (b.lo : ℝ) / (S : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ) / (S : ℝ) := by
  exact and_congr (div_le_iff₀ (scale_pos hS)).symm
    (le_div_iff₀ (scale_pos hS)).symm

private theorem real_product_two (lo hi x t : ℝ)
    (hl : lo ≤ x) (hh : x ≤ hi) :
    min (lo * t) (hi * t) ≤ x * t ∧
      x * t ≤ max (lo * t) (hi * t) := by
  by_cases ht : 0 ≤ t
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl ht),
      (mul_le_mul_of_nonneg_right hh ht).trans (le_max_right _ _)⟩
  · have ht' : t ≤ 0 := le_of_not_ge ht
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hh ht'),
      (mul_le_mul_of_nonpos_right hl ht').trans (le_max_left _ _)⟩

private theorem real_product_four (al ah bl bh x y : ℝ)
    (hax : al ≤ x) (hxa : x ≤ ah) (hby : bl ≤ y) (hyb : y ≤ bh) :
    min (min (al * bl) (al * bh)) (min (ah * bl) (ah * bh)) ≤ x * y ∧
      x * y ≤ max (max (al * bl) (al * bh)) (max (ah * bl) (ah * bh)) := by
  have hx := real_product_two al ah x y hax hxa
  have hlo := real_product_two bl bh y al hby hyb
  have hhi := real_product_two bl bh y ah hby hyb
  rw [mul_comm bl al, mul_comm bh al, mul_comm y al] at hlo
  rw [mul_comm bl ah, mul_comm bh ah, mul_comm y ah] at hhi
  constructor
  · apply le_trans _ hx.1
    exact le_min ((min_le_left _ _).trans hlo.1)
      ((min_le_right _ _).trans hhi.1)
  · apply le_trans hx.2
    exact max_le (hlo.2.trans (le_max_left _ _))
      (hhi.2.trans (le_max_right _ _))

/-- Outward multiplication is sound on arbitrary real inputs, including
intervals crossing zero and negative endpoint products. -/
theorem real_mul_enclosed {S : Int} (hS : 0 < S)
    {a b : Bounds} {x y : ℝ}
    (hx : RealEnclosed S a x) (hy : RealEnclosed S b y) :
    RealEnclosed S (mulBoundsAt S a b) (x * y) := by
  let low : Int := min (min (a.lo * b.lo) (a.lo * b.hi))
    (min (a.hi * b.lo) (a.hi * b.hi))
  let high : Int := max (max (a.lo * b.lo) (a.lo * b.hi))
    (max (a.hi * b.lo) (a.hi * b.hi))
  have hbox : (low : ℝ) ≤ (x * (S : ℝ)) * (y * (S : ℝ)) ∧
      (x * (S : ℝ)) * (y * (S : ℝ)) ≤ (high : ℝ) := by
    simpa only [low, high, Int.cast_min, Int.cast_max, Int.cast_mul] using
      real_product_four (a.lo : ℝ) (a.hi : ℝ) (b.lo : ℝ) (b.hi : ℝ)
        (x * (S : ℝ)) (y * (S : ℝ)) hx.1 hx.2 hy.1 hy.2
  have hf : ((low / S : Int) : ℝ) * (S : ℝ) ≤ (low : ℝ) := by
    exact_mod_cast signed_floor_rounds_outward low S hS
  have hc : (high : ℝ) ≤ ((-((-high) / S) : Int) : ℝ) * (S : ℝ) := by
    exact_mod_cast signed_ceil_rounds_outward high S hS
  change ((low / S : Int) : ℝ) ≤ (x * y) * (S : ℝ) ∧
    (x * y) * (S : ℝ) ≤ ((-((-high) / S) : Int) : ℝ)
  constructor
  · apply (mul_le_mul_iff_right₀ (scale_pos hS)).mp
    convert hf.trans hbox.1 using 1 <;> ring
  · apply (mul_le_mul_iff_right₀ (scale_pos hS)).mp
    convert hbox.2.trans hc using 1 <;> ring

/-- The tighter interval square remains sound for all real inputs; in
particular a zero-crossing interval uses the exact lower bound zero. -/
theorem real_square_enclosed {S : Int} (hS : 0 < S)
    {b : Bounds} {x : ℝ} (hx : RealEnclosed S b x) :
    RealEnclosed S (squareBoundsAt S b) (x ^ 2) := by
  let low : Int := if b.lo ≤ 0 ∧ 0 ≤ b.hi then 0
    else min (b.lo * b.lo) (b.hi * b.hi)
  let high : Int := max (b.lo * b.lo) (b.hi * b.hi)
  have hlow : (low : ℝ) ≤ (x * (S : ℝ)) * (x * (S : ℝ)) := by
    dsimp only [low]
    split_ifs with hcross
    · simp only [Int.cast_zero]
      exact mul_self_nonneg _
    · by_cases hpos : 0 ≤ b.lo
      · have hp : (0 : ℝ) ≤ (b.lo : ℝ) := by exact_mod_cast hpos
        have hs : (b.lo : ℝ) * (b.lo : ℝ) ≤
            (x * (S : ℝ)) * (x * (S : ℝ)) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hx.1)
            (show 0 ≤ x * (S : ℝ) + (b.lo : ℝ) by linarith [hx.1])]
        have hm : ((min (b.lo * b.lo) (b.hi * b.hi) : Int) : ℝ) ≤
            (b.lo : ℝ) * (b.lo : ℝ) := by
          exact_mod_cast (min_le_left (b.lo * b.lo) (b.hi * b.hi))
        exact hm.trans hs
      · have hn : b.hi ≤ 0 := by omega
        have hp : (b.hi : ℝ) ≤ 0 := by exact_mod_cast hn
        have hs : (b.hi : ℝ) * (b.hi : ℝ) ≤
            (x * (S : ℝ)) * (x * (S : ℝ)) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hx.2)
            (show 0 ≤ -(x * (S : ℝ)) - (b.hi : ℝ) by linarith [hx.2])]
        have hm : ((min (b.lo * b.lo) (b.hi * b.hi) : Int) : ℝ) ≤
            (b.hi : ℝ) * (b.hi : ℝ) := by
          exact_mod_cast (min_le_right (b.lo * b.lo) (b.hi * b.hi))
        exact hm.trans hs
  have hhigh : (x * (S : ℝ)) * (x * (S : ℝ)) ≤ (high : ℝ) := by
    by_cases hp : 0 ≤ x * (S : ℝ)
    · have hs : (x * (S : ℝ)) * (x * (S : ℝ)) ≤
          (b.hi : ℝ) * (b.hi : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hx.2)
          (show 0 ≤ (b.hi : ℝ) + x * (S : ℝ) by linarith [hx.2])]
      have hm : (b.hi : ℝ) * (b.hi : ℝ) ≤ (high : ℝ) := by
        exact_mod_cast (le_max_right (b.lo * b.lo) (b.hi * b.hi))
      exact hs.trans hm
    · have hp' : x * (S : ℝ) ≤ 0 := le_of_not_ge hp
      have hs : (x * (S : ℝ)) * (x * (S : ℝ)) ≤
          (b.lo : ℝ) * (b.lo : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hx.1)
          (show 0 ≤ -(b.lo : ℝ) - x * (S : ℝ) by linarith [hx.1])]
      have hm : (b.lo : ℝ) * (b.lo : ℝ) ≤ (high : ℝ) := by
        exact_mod_cast (le_max_left (b.lo * b.lo) (b.hi * b.hi))
      exact hs.trans hm
  have hf : ((low / S : Int) : ℝ) * (S : ℝ) ≤ (low : ℝ) := by
    exact_mod_cast signed_floor_rounds_outward low S hS
  have hc : (high : ℝ) ≤ ((-((-high) / S) : Int) : ℝ) * (S : ℝ) := by
    exact_mod_cast signed_ceil_rounds_outward high S hS
  change ((low / S : Int) : ℝ) ≤ x ^ 2 * (S : ℝ) ∧
    x ^ 2 * (S : ℝ) ≤ ((-((-high) / S) : Int) : ℝ)
  constructor
  · apply (mul_le_mul_iff_right₀ (scale_pos hS)).mp
    convert hf.trans hlow using 1 <;> ring
  · apply (mul_le_mul_iff_right₀ (scale_pos hS)).mp
    convert hhigh.trans hc using 1 <;> ring

theorem real_add_enclosed {S : Int} {a b : Bounds} {x y : ℝ}
    (hx : RealEnclosed S a x) (hy : RealEnclosed S b y) :
    RealEnclosed S (addBounds a b) (x + y) := by
  change ((a.lo + b.lo : Int) : ℝ) ≤ (x + y) * (S : ℝ) ∧
    (x + y) * (S : ℝ) ≤ ((a.hi + b.hi : Int) : ℝ)
  push_cast
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem real_double_enclosed {S : Int} {b : Bounds} {x : ℝ}
    (hx : RealEnclosed S b x) :
    RealEnclosed S (doubleBounds b) (2 * x) := by
  change ((2 * b.lo : Int) : ℝ) ≤ (2 * x) * (S : ℝ) ∧
    (2 * x) * (S : ℝ) ≤ ((2 * b.hi : Int) : ℝ)
  push_cast
  constructor <;> linarith [hx.1, hx.2]

private theorem zero_enclosed (S : Int) : RealEnclosed S zeroBound 0 := by
  simp [RealEnclosed, zeroBound]

private theorem one_enclosed (S : Int) : RealEnclosed S (oneAt S) 1 := by
  simp [RealEnclosed, oneAt]

private theorem point_enclosed {S : Int} (hS : 0 < S) (k : Int) :
    RealEnclosed S ⟨k, k⟩ ((k : ℝ) / (S : ℝ)) := by
  simp [RealEnclosed, ne_of_gt (scale_pos hS)]

private theorem joint_next_enclosed {S : Int} (hS : 0 < S)
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c)
    {b : Bounds × Bounds} {st : ℝ × ℝ}
    (hx : RealEnclosed S b.1 st.1) (hd : RealEnclosed S b.2 st.2) :
    RealEnclosed S (jointNext S C b).1 (LoopsRealPeriod27.next c st).1 ∧
      RealEnclosed S (jointNext S C b).2 (LoopsRealPeriod27.next c st).2 := by
  exact ⟨real_add_enclosed (real_square_enclosed hS hx) hc,
    real_add_enclosed
      (real_mul_enclosed hS (real_double_enclosed hx) hd) (one_enclosed S)⟩

/-- The whole rounded joint trace encloses the actual real critical
iteration and its actual parameter derivative at every finite time. -/
theorem joint_iter_enclosed {S : Int} (hS : 0 < S)
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c)
    (n : Nat) (b : Bounds × Bounds) (st : ℝ × ℝ)
    (hx : RealEnclosed S b.1 st.1) (hd : RealEnclosed S b.2 st.2) :
    RealEnclosed S (jointIter S C n b).1 (LoopsRealPeriod27.realIter c n st).1 ∧
      RealEnclosed S (jointIter S C n b).2
        (LoopsRealPeriod27.realIter c n st).2 := by
  induction n generalizing b st with
  | zero => exact ⟨hx, hd⟩
  | succ n ih =>
      have hn := joint_next_enclosed hS hc hx hd
      exact ih (jointNext S C b) (LoopsRealPeriod27.next c st) hn.1 hn.2

theorem orbit_enclosed {S : Int} (hS : 0 < S)
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c) (n : Nat) :
    RealEnclosed S (LoopsFormal.DepthThree.orbitAt S C n)
      (LoopsRealPeriod27.polynomial n c) := by
  exact (joint_iter_enclosed hS hc n (zeroBound, zeroBound) (0, 0)
    (zero_enclosed S) (zero_enclosed S)).1

theorem derivative_enclosed {S : Int} (hS : 0 < S)
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c) (n : Nat) :
    RealEnclosed S (derivAt S C n)
      (LoopsRealPeriod27.derivativePolynomial n c) := by
  exact (joint_iter_enclosed hS hc n (zeroBound, zeroBound) (0, 0)
    (zero_enclosed S) (zero_enclosed S)).2

/-- The actual collision polynomial, without any rounded evaluations. -/
def collisionPolynomial (n : Nat) (c : ℝ) : ℝ :=
  LoopsRealPeriod27.polynomial (3 * n) c +
    LoopsRealPeriod27.polynomial (6 * n) c

def collisionDerivative (n : Nat) (c : ℝ) : ℝ :=
  LoopsRealPeriod27.derivativePolynomial (3 * n) c +
    LoopsRealPeriod27.derivativePolynomial (6 * n) c

theorem collision_hasDerivAt (n : Nat) (c : ℝ) :
    HasDerivAt (collisionPolynomial n) (collisionDerivative n c) c := by
  exact (LoopsRealPeriod27.hasDerivAt_polynomial (3 * n) c).add
    (LoopsRealPeriod27.hasDerivAt_polynomial (6 * n) c)

theorem collision_continuous (n : Nat) : Continuous (collisionPolynomial n) :=
  (LoopsRealPeriod27.polynomial_continuous (3 * n)).add
    (LoopsRealPeriod27.polynomial_continuous (6 * n))

theorem collision_enclosed {S : Int} (hS : 0 < S)
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c) (n : Nat) :
    RealEnclosed S (collision S C n) (collisionPolynomial n c) :=
  real_add_enclosed (orbit_enclosed hS hc (3 * n)) (orbit_enclosed hS hc (6 * n))

theorem collision_derivative_enclosed {S : Int} (hS : 0 < S)
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c) (n : Nat) :
    RealEnclosed S (collisionDeriv S C n) (collisionDerivative n c) :=
  real_add_enclosed (derivative_enclosed hS hc (3 * n))
    (derivative_enclosed hS hc (6 * n))

private theorem positive_of_enclosed {S : Int} (hS : 0 < S)
    {b : Bounds} {x : ℝ} (hx : RealEnclosed S b x) (hb : 0 < b.lo) : 0 < x := by
  have hl : (0 : ℝ) < (b.lo : ℝ) := by exact_mod_cast hb
  apply (mul_lt_mul_iff_right₀ (scale_pos hS)).mp
  simpa [mul_comm] using hl.trans_le hx.1

private theorem negative_of_enclosed {S : Int} (hS : 0 < S)
    {b : Bounds} {x : ℝ} (hx : RealEnclosed S b x) (hb : b.hi < 0) : x < 0 := by
  have hh : (b.hi : ℝ) < 0 := by exact_mod_cast hb
  apply (mul_lt_mul_iff_right₀ (scale_pos hS)).mp
  simpa [mul_comm] using hx.2.trans_lt hh

/-- A root certificate forces injectivity on the whole closed parameter
interval, not just at its endpoints or its rational points. -/
theorem certified_collision_injective {S : Int} {n : Nat} {C : Bounds}
    (h : RootCertificate S n C) :
    InjOn (collisionPolynomial n)
      (Icc ((C.lo : ℝ) / (S : ℝ)) ((C.hi : ℝ) / (S : ℝ))) := by
  rcases h with ⟨hS, _, _, hder⟩
  rcases hder with hpos | hneg
  · have hm : StrictMonoOn (collisionPolynomial n)
        (Icc ((C.lo : ℝ) / (S : ℝ)) ((C.hi : ℝ) / (S : ℝ))) := by
      apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
        (collision_continuous n).continuousOn
        (fun x _ => (collision_hasDerivAt n x).hasDerivWithinAt)
      intro x hx
      have hxI : x ∈ Icc ((C.lo : ℝ) / (S : ℝ)) ((C.hi : ℝ) / (S : ℝ)) :=
        interior_subset hx
      have hc := (realEnclosed_iff hS C x).mpr hxI
      exact positive_of_enclosed hS (collision_derivative_enclosed hS hc n) hpos
    exact hm.injOn
  · have hm : StrictAntiOn (collisionPolynomial n)
        (Icc ((C.lo : ℝ) / (S : ℝ)) ((C.hi : ℝ) / (S : ℝ))) := by
      apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
        (collision_continuous n).continuousOn
        (fun x _ => (collision_hasDerivAt n x).hasDerivWithinAt)
      intro x hx
      have hxI : x ∈ Icc ((C.lo : ℝ) / (S : ℝ)) ((C.hi : ℝ) / (S : ℝ)) :=
        interior_subset hx
      have hc := (realEnclosed_iff hS C x).mpr hxI
      exact negative_of_enclosed hS (collision_derivative_enclosed hS hc n) hneg
    exact hm.injOn

/-- From only the finite integer certificate, construct the unique
actual real root in the strict parameter chart. -/
theorem certified_unique_real_root {S : Int} {n : Nat} {C : Bounds}
    (h : RootCertificate S n C) :
    ∃! c : ℝ, (C.lo : ℝ) / (S : ℝ) < c ∧
      c < (C.hi : ℝ) / (S : ℝ) ∧ collisionPolynomial n c = 0 := by
  have hinj := certified_collision_injective h
  rcases h with ⟨hS, hC, hends, _⟩
  let L : ℝ := (C.lo : ℝ) / (S : ℝ)
  let R : ℝ := (C.hi : ℝ) / (S : ℝ)
  have hLR : L < R := by
    apply (div_lt_div_iff_of_pos_right (scale_pos hS)).mpr
    exact_mod_cast hC
  have hl := collision_enclosed hS (point_enclosed hS C.lo) n
  have hr := collision_enclosed hS (point_enclosed hS C.hi) n
  have hsign : (collisionPolynomial n L < 0 ∧ 0 < collisionPolynomial n R) ∨
      (collisionPolynomial n R < 0 ∧ 0 < collisionPolynomial n L) := by
    rcases hends with hh | hh
    · exact Or.inl ⟨negative_of_enclosed hS hl hh.1,
        positive_of_enclosed hS hr hh.2⟩
    · exact Or.inr ⟨negative_of_enclosed hS hr hh.1,
        positive_of_enclosed hS hl hh.2⟩
  have hLne : collisionPolynomial n L ≠ 0 := by
    rcases hsign with hh | hh
    · exact ne_of_lt hh.1
    · exact ne_of_gt hh.2
  have hRne : collisionPolynomial n R ≠ 0 := by
    rcases hsign with hh | hh
    · exact ne_of_gt hh.2
    · exact ne_of_lt hh.1
  have hzero : (0 : ℝ) ∈ collisionPolynomial n '' Icc L R := by
    rcases hsign with hh | hh
    · exact intermediate_value_Icc hLR.le (collision_continuous n).continuousOn
        ⟨hh.1.le, hh.2.le⟩
    · exact intermediate_value_Icc' hLR.le (collision_continuous n).continuousOn
        ⟨hh.1.le, hh.2.le⟩
  obtain ⟨c, hc, hroot⟩ := hzero
  have hlc : L < c := by
    rcases hc.1.eq_or_lt with heq | hlt
    · subst c
      exact (hLne hroot).elim
    · exact hlt
  have hcr : c < R := by
    rcases hc.2.eq_or_lt with heq | hlt
    · subst c
      exact (hRne hroot).elim
    · exact hlt
  refine ⟨c, ⟨hlc, hcr, hroot⟩, ?_⟩
  intro y hy
  exact hinj ⟨hy.1.le, hy.2.1.le⟩ hc (hy.2.2.trans hroot.symm)

/-- The quadratic coefficient of the critical return. Its interpretation
as the coefficient of `z²` in the actual complex iterate is established in
`DepthThreeRemainder`. -/
def quadraticCoefficient : Nat → ℝ → ℝ
  | 0, _ => 0
  | j + 1, c => if j = 0 then 1
      else 2 * LoopsRealPeriod27.polynomial j c * quadraticCoefficient j c

def RealRowEnclosed (S : Int) (row : TraceRow) (j : Nat) (c : ℝ) : Prop :=
  RealEnclosed S row.orbit (LoopsRealPeriod27.polynomial j c) ∧
    RealEnclosed S row.deriv (LoopsRealPeriod27.derivativePolynomial j c) ∧
    RealEnclosed S row.quadratic (quadraticCoefficient j c)

theorem polynomial_succ (j : Nat) (c : ℝ) :
    LoopsRealPeriod27.polynomial (j + 1) c =
      LoopsRealPeriod27.polynomial j c ^ 2 + c := by
  simp [LoopsRealPeriod27.polynomial, LoopsRealPeriod27.state_succ,
    LoopsRealPeriod27.next]

private theorem derivativePolynomial_succ (j : Nat) (c : ℝ) :
    LoopsRealPeriod27.derivativePolynomial (j + 1) c =
      2 * LoopsRealPeriod27.polynomial j c *
        LoopsRealPeriod27.derivativePolynomial j c + 1 := by
  simp [LoopsRealPeriod27.derivativePolynomial, LoopsRealPeriod27.polynomial,
    LoopsRealPeriod27.state_succ, LoopsRealPeriod27.next]

theorem row_next_enclosed {S : Int} (hS : 0 < S)
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c)
    {j : Nat} {row : TraceRow} (hrow : RealRowEnclosed S row j c) :
    RealRowEnclosed S (rowNext S C j row) (j + 1) c := by
  refine ⟨?_, ?_, ?_⟩
  · change RealEnclosed S (addBounds (squareBoundsAt S row.orbit) C)
      (LoopsRealPeriod27.polynomial (j + 1) c)
    rw [polynomial_succ]
    exact real_add_enclosed (real_square_enclosed hS hrow.1) hc
  · change RealEnclosed S
      (addBounds (mulBoundsAt S (doubleBounds row.orbit) row.deriv) (oneAt S))
      (LoopsRealPeriod27.derivativePolynomial (j + 1) c)
    rw [derivativePolynomial_succ]
    exact real_add_enclosed
      (real_mul_enclosed hS (real_double_enclosed hrow.1) hrow.2.1)
      (one_enclosed S)
  · change RealEnclosed S
      (if j = 0 then oneAt S
       else mulBoundsAt S (doubleBounds row.orbit) row.quadratic)
      (quadraticCoefficient (j + 1) c)
    rw [quadraticCoefficient]
    split_ifs
    · exact one_enclosed S
    · exact real_mul_enclosed hS (real_double_enclosed hrow.1) hrow.2.2

theorem row_trace_enclosed {S : Int} (hS : 0 < S)
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c)
    (n j k : Nat) (hk : k ≤ n) (row : TraceRow)
    (hrow : RealRowEnclosed S row j c) :
    RealRowEnclosed S (rowAt (rowTrace S C n j row) k) (j + k) c := by
  induction n generalizing j k row with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simpa [rowAt, rowTrace] using hrow
  | succ n ih =>
      cases k with
      | zero => simpa [rowAt, rowTrace] using hrow
      | succ k =>
          have hnext := row_next_enclosed hS hc hrow
          have hrec := ih (j + 1) k (by omega) (rowNext S C j row) hnext
          change RealRowEnclosed S
            (rowAt (rowTrace S C n (j + 1) (rowNext S C j row)) k)
            (j + (k + 1)) c
          convert hrec using 1 <;> omega

/-- Every stored trace row, including the quadratic Taylor coefficient,
encloses the actual quantities throughout the closed parameter chart. -/
theorem trace_enclosed {S : Int} (hS : 0 < S)
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c)
    (n k : Nat) (hk : k ≤ n) :
    RealRowEnclosed S (rowAt (trace S C n) k) k c := by
  have hz : RealRowEnclosed S zeroRow 0 c :=
    ⟨zero_enclosed S, zero_enclosed S, zero_enclosed S⟩
  simpa only [trace, Nat.zero_add] using
    row_trace_enclosed hS hc n 0 k hk zeroRow hz

end

end LoopsDepthThreeReal
