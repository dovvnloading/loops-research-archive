import Period27RealCenter

/-!
# Strict real uniqueness of the isolated period-27 critical parameter

The core Lean certificate proves that, for every rational parameter in
an exact dyadic bracket, the period-27 algebraic parameter derivative
is enclosed in one *strictly negative* signed interval. The preceding
mathlib module proves that this recurrence is the ordinary real
derivative of the actual critical-orbit polynomial.

This module proves that the fixed rational upper bound extends to all
real parameters in the closed bracket. The key point is that the upper
bound is STRICTLY negative: merely taking limits of pointwise strict
rational inequalities would not suffice. It then proves strict
monotonicity and a unique *real* zero in the dyadic bracket.

The conclusion is about a specific real polynomial; it does not
establish complex ray landing, KL sheet markings, or MLC.
-/

namespace LoopsRealPeriod27

open LoopsFormal.Period27

noncomputable section

private theorem scale_positive_real : (0 : ℝ) < (unit : ℝ) := by
  exact_mod_cast (show (0 : Int) < unit by decide +kernel)

private theorem fraction_den_positive_real (x : ExactFraction) :
    (0 : ℝ) < (x.den : ℝ) := by
  exact_mod_cast x.den_pos

/-- Source signed-integer enclosures are equivalent to closed real
    interval inequalities for arbitrary positive-denominator fractions. -/
theorem enclosed_iff_real (b : Bounds) (x : ExactFraction) :
    Encloses b x ↔
      (b.lo : ℝ) / (unit : ℝ) ≤ value x ∧
      value x ≤ (b.hi : ℝ) / (unit : ℝ) := by
  change (0 < x.den ∧ b.lo * x.den ≤ x.num * unit ∧
      x.num * unit ≤ b.hi * x.den) ↔ _
  constructor
  · rintro ⟨_, hlo, hhi⟩
    have hrlo : (b.lo : ℝ) * (x.den : ℝ) ≤
        (x.num : ℝ) * (unit : ℝ) := by
      exact_mod_cast hlo
    have hrhi : (x.num : ℝ) * (unit : ℝ) ≤
        (b.hi : ℝ) * (x.den : ℝ) := by
      exact_mod_cast hhi
    exact ⟨(div_le_div_iff₀ scale_positive_real
      (fraction_den_positive_real x)).mpr hrlo,
      (div_le_div_iff₀ (fraction_den_positive_real x)
        scale_positive_real).mpr hrhi⟩
  · rintro ⟨hlo, hhi⟩
    have hrlo := (div_le_div_iff₀ scale_positive_real
      (fraction_den_positive_real x)).mp hlo
    have hrhi := (div_le_div_iff₀ (fraction_den_positive_real x)
      scale_positive_real).mp hhi
    refine ⟨x.den_pos, ?_, ?_⟩
    · exact_mod_cast hrlo
    · exact_mod_cast hrhi

/-- Every rational number has a canonical exact signed-integer
    numerator and positive-integer-denominator representation. -/
def fromRat (q : ℚ) : ExactFraction :=
  ⟨q.num, (q.den : ℤ), by exact_mod_cast q.pos⟩

theorem fromRat_value (q : ℚ) : value (fromRat q) = (q : ℝ) := by
  change (q.num : ℝ) / (q.den : ℝ) = (q : ℝ)
  exact (Rat.cast_def q).symm

/-- The existing interval certificate applies to every rational in
    the real bracket, not merely its two endpoints. -/
theorem rat_parameter_enclosed (q : ℚ)
    (hl : left ≤ (q : ℝ)) (hr : (q : ℝ) ≤ right) :
    Encloses centerParameter (fromRat q) := by
  apply (enclosed_iff_real centerParameter (fromRat q)).mpr
  change left ≤ value (fromRat q) ∧ value (fromRat q) ≤ right
  rw [fromRat_value]
  exact ⟨hl, hr⟩

/-- Same exact derivative interval as the source's 27-step joint engine. -/
def derivativeCertificate : Bounds :=
  (roundedJointIter centerParameter 27 (zeroBound, zeroBound)).2

/-- A uniform quantitative upper bound, and not merely a sign. -/
def derivativeCap : ℝ :=
  (derivativeCertificate.hi : ℝ) / (unit : ℝ)

theorem derivativeCap_strict_negative : derivativeCap < 0 := by
  have h : derivativeCertificate.hi < 0 :=
    every_bracket_derivative_interval_is_negative
  unfold derivativeCap
  exact div_neg_of_neg_of_pos (by exact_mod_cast h)
    scale_positive_real

/-- The exact rational joint engine and the real calculus derivative
    agree, and its source integer enclosure gives the same fixed
    negative upper bound for EVERY rational parameter in the bracket. -/
theorem rational_derivative_le_cap (q : ℚ)
    (hl : left ≤ (q : ℝ)) (hr : (q : ℝ) ≤ right) :
    derivativePolynomial 27 (q : ℝ) ≤ derivativeCap := by
  let e := fromRat q
  have hpar : Encloses centerParameter e :=
    rat_parameter_enclosed q hl hr
  have htrace :=
    joint_rational_trace_enclosed
      centerParameter e hpar 27 (zeroBound, zeroBound)
      zeroJoint zero_fraction_enclosed zero_fraction_enclosed
  have hbound :
      value (exactJointIter e 27 zeroJoint).deriv ≤ derivativeCap :=
    (enclosed_iff_real derivativeCertificate
      (exactJointIter e 27 zeroJoint).deriv).mp htrace.2 |>.2
  have hemb := jointValue_iter e 27 zeroJoint
  have hz : jointValue zeroJoint = ((0 : ℝ), (0 : ℝ)) := by
    simp [jointValue, zeroJoint, value_zero]
  rw [hz] at hemb
  have hval : value e = (q : ℝ) := fromRat_value q
  rw [hval] at hemb
  have hderiv : derivativePolynomial 27 (q : ℝ) =
      value (exactJointIter e 27 zeroJoint).deriv := by
    exact (congrArg Prod.snd hemb).symm
  rw [hderiv]
  exact hbound

/-- General topological transfer lemma. A continuous function bounded
    by a fixed cap on *all rational points* of a closed nontrivial real
    interval is bounded by that same cap on *all real points*.
    Proof: density inside the open interval, then closure of that
    interval; both steps preserve membership in the closed set (-∞,M]. -/
theorem continuous_cap_of_rationals (a b M : ℝ)
    (hab : a < b) (F : ℝ → ℝ) (hF : Continuous F)
    (hq : ∀ q : ℚ, a ≤ (q : ℝ) → (q : ℝ) ≤ b →
      F (q : ℝ) ≤ M) (x : ℝ) (hl : a ≤ x) (hr : x ≤ b) :
    F x ≤ M := by
  let cast : ℚ → ℝ := fun q => (q : ℝ)
  have hcast : DenseRange cast := Rat.denseRange_cast
  have hdense : Set.Ioo a b ⊆
      closure (cast '' (cast ⁻¹' Set.Ioo a b)) :=
    hcast.subset_closure_image_preimage_of_isOpen isOpen_Ioo
  have hmap : Set.MapsTo F
      (cast '' (cast ⁻¹' Set.Ioo a b)) (Set.Iic M) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := hy
    exact hq q hq.1.le hq.2.le
  have hopen : Set.MapsTo F (Set.Ioo a b) (Set.Iic M) := by
    intro y hy
    exact (hmap.closure_left hF isClosed_Iic) (hdense hy)
  have hclosed := hopen.closure_left hF isClosed_Iic
  have hx : x ∈ closure (Set.Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨hl, hr⟩
  exact hclosed hx

/-- The decisive strict REAL bound for all parameters, including the
    irrational zero and both bracket endpoints. -/
theorem real_derivative_le_cap (c : ℝ)
    (hc : c ∈ Set.Icc left right) :
    derivativePolynomial 27 c ≤ derivativeCap := by
  exact continuous_cap_of_rationals left right derivativeCap
    left_lt_right (derivativePolynomial 27)
    (derivativePolynomial_continuous 27)
    (fun q hl hr => rational_derivative_le_cap q hl hr)
    c hc.1 hc.2

theorem real_derivative_strict_negative (c : ℝ)
    (hc : c ∈ Set.Icc left right) :
    derivativePolynomial 27 c < 0 := by
  exact lt_of_le_of_lt (real_derivative_le_cap c hc)
    derivativeCap_strict_negative

/-- The 27th real critical-orbit polynomial is strictly decreasing
    across the *entire certified bracket*. -/
theorem polynomial27_strictAntiOn :
    StrictAntiOn (polynomial 27) (Set.Icc left right) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg
      (convex_Icc left right)
      (polynomial_continuous 27).continuousOn
      (fun x _ => (hasDerivAt_polynomial 27 x).hasDerivWithinAt)
  intro x hx
  exact real_derivative_strict_negative x (Set.interior_subset hx)

/-- Unique REAL root in the exact 2^-128 dyadic bracket.
    This combines the previously kernel-proved real IVT existence with
    the uniformly negative real derivative transported from the exact
    signed-integer certificate, and a mean-value monotonicity theorem. -/
theorem exists_unique_period27_center_in_dyadic_bracket :
    ∃! c : ℝ, left < c ∧ c < right ∧ polynomial 27 c = 0 := by
  obtain ⟨c, hl, hr, hroot⟩ := exists_real_period27_root
  refine ⟨c, ⟨hl, hr, hroot⟩, ?_⟩
  intro y hy
  have hc : c ∈ Set.Icc left right := ⟨hl.le, hr.le⟩
  have hy' : y ∈ Set.Icc left right :=
    ⟨hy.1.le, hy.2.1.le⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hh := polynomial27_strictAntiOn hc hy' hlt
    linarith [hroot, hy.2.2]
  · have hh := polynomial27_strictAntiOn hy' hc hgt
    linarith [hroot, hy.2.2]

#print axioms enclosed_iff_real
#print axioms continuous_cap_of_rationals
#print axioms rational_derivative_le_cap
#print axioms real_derivative_strict_negative
#print axioms exists_unique_period27_center_in_dyadic_bracket

end

end LoopsRealPeriod27
