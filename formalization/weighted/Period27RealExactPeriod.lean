import Period27RealUniqueness
import Paper2Phase

/-!
# Actual exact period 27 for the uniquely isolated real quadratic center

The mathlib bridge already proves a unique REAL parameter c in the exact
dyadic bracket with P_27(c)=0. The statements here strengthen that result
by transferring the sound outward integer ORBIT bounds through rational
density, for every iterate n and every real parameter in the bracket.

The source's fixed interval recurrence then strictly separates zero from
P_n(c) for each 1 ≤ n < 27, yielding true *minimal period 27* rather
than merely a 27-step return. These results involve the real quadratic
polynomial, not a symbolic label or an assumed period.

No complex polynomial-like source realization, ray landing, KL marked
access or sheet transport, or MLC claim is inferred.
-/

namespace LoopsRealPeriod27

open LoopsFormal.Period27

noncomputable section

/-- Exact upper and lower dyadic grid bounds for n critical iterates
    on the *entire* parameter bracket. -/
def orbitCertificate (n : Nat) : Bounds :=
  (roundedJointIter centerParameter n (zeroBound, zeroBound)).1

/-- The original arbitrary-rational soundness certificate gives
    bounds on the actual real-valued polynomial for every rational
    parameter, with no floating-point approximations. -/
theorem rational_orbit_bounds (n : Nat) (q : ℚ)
    (hl : left ≤ (q : ℝ)) (hr : (q : ℝ) ≤ right) :
    ((orbitCertificate n).lo : ℝ) / (unit : ℝ) ≤
      polynomial n (q : ℝ) ∧
    polynomial n (q : ℝ) ≤
      ((orbitCertificate n).hi : ℝ) / (unit : ℝ) := by
  let e := fromRat q
  have hc : Encloses centerParameter e :=
    rat_parameter_enclosed q hl hr
  have htrace :=
    joint_rational_trace_enclosed centerParameter e hc n
      (zeroBound, zeroBound) zeroJoint
      zero_fraction_enclosed zero_fraction_enclosed
  have hbound :=
    (enclosed_iff_real (orbitCertificate n)
      (exactJointIter e n zeroJoint).orbit).mp htrace.1
  have hemb := jointValue_iter e n zeroJoint
  have hz : jointValue zeroJoint = ((0 : ℝ), (0 : ℝ)) := by
    simp [jointValue, zeroJoint, value_zero]
  rw [hz] at hemb
  have he : value e = (q : ℝ) := fromRat_value q
  rw [he] at hemb
  have hpoly : polynomial n (q : ℝ) =
      value (exactJointIter e n zeroJoint).orbit :=
    (congrArg Prod.fst hemb).symm
  rw [hpoly]
  exact hbound

/-- Rational upper enclosures lift to all REAL parameters in the
    bracket by density and continuity. -/
theorem real_orbit_upper (n : Nat) (c : ℝ)
    (hc : c ∈ Set.Icc left right) :
    polynomial n c ≤
      ((orbitCertificate n).hi : ℝ) / (unit : ℝ) := by
  exact continuous_cap_of_rationals left right
    (((orbitCertificate n).hi : ℝ) / (unit : ℝ))
    left_lt_right (polynomial n) (polynomial_continuous n)
    (fun q hl hr => (rational_orbit_bounds n q hl hr).2)
    c hc.1 hc.2

/-- Symmetric lower enclosure; transform it into an upper bound for
    the *negative* polynomial before applying the density theorem. -/
theorem real_orbit_lower (n : Nat) (c : ℝ)
    (hc : c ∈ Set.Icc left right) :
    ((orbitCertificate n).lo : ℝ) / (unit : ℝ) ≤
      polynomial n c := by
  have hn : -polynomial n c ≤
      -(((orbitCertificate n).lo : ℝ) / (unit : ℝ)) := by
    apply continuous_cap_of_rationals left right
      (-(((orbitCertificate n).lo : ℝ) / (unit : ℝ)))
      left_lt_right (fun x : ℝ => -polynomial n x)
      (polynomial_continuous n).neg
    · intro q hl hr
      have h := (rational_orbit_bounds n q hl hr).1
      linarith
    · exact hc.1
    · exact hc.2
  linarith

/-- Fully real-valued correctness of the source integer orbit
    enclosure at *every* iteration count, for *every* real parameter
    in the interval (including irrational parameters). -/
theorem real_orbit_bounds (n : Nat) (c : ℝ)
    (hc : c ∈ Set.Icc left right) :
    ((orbitCertificate n).lo : ℝ) / (unit : ℝ) ≤
      polynomial n c ∧
    polynomial n c ≤
      ((orbitCertificate n).hi : ℝ) / (unit : ℝ) :=
  ⟨real_orbit_lower n c hc, real_orbit_upper n c hc⟩

/-- Exact kernel computation of the source interval recursion, with
    one conclusion for ALL 26 nonzero early iterates. The quantifier
    is over the entire finite range, not a small sample of indices. -/
theorem all_first_26_orbit_bounds_strict :
    ∀ j : Fin 26,
      (orbitCertificate (j.val + 1)).hi < 0 ∨
      0 < (orbitCertificate (j.val + 1)).lo := by
  decide +kernel

private theorem positive_real_scale : (0 : ℝ) < (unit : ℝ) := by
  exact_mod_cast (show (0 : Int) < unit by decide +kernel)

/-- For every real parameter in the certified bracket, each of the
    26 earlier critical iterates is nonzero. This is stronger than the
    proper-divisor check 1,3,9 and bypasses any external periodic-point
    divisibility theorem. -/
theorem real_no_early_critical_return
    (c : ℝ) (hc : c ∈ Set.Icc left right) :
    ∀ j : Nat, 0 < j → j < 27 → polynomial j c ≠ 0 := by
  intro j hj hlt
  let k : Fin 26 := ⟨j - 1, by omega⟩
  have hs := all_first_26_orbit_bounds_strict k
  have hjEq : k.val + 1 = j := by
    dsimp [k]
    omega
  rw [hjEq] at hs
  obtain ⟨hlo, hhi⟩ := real_orbit_bounds j c hc
  rcases hs with hneg | hpos
  · have hhigh :
        ((orbitCertificate j).hi : ℝ) / (unit : ℝ) < 0 :=
      div_neg_of_neg_of_pos (by exact_mod_cast hneg)
        positive_real_scale
    exact ne_of_lt (lt_of_le_of_lt hhi hhigh)
  · have hlow :
        0 < ((orbitCertificate j).lo : ℝ) / (unit : ℝ) :=
      div_pos (by exact_mod_cast hpos) positive_real_scale
    exact ne_of_gt (lt_of_lt_of_le hlow hlo)

/-- The unique parameter is an actual **exact period-27** critical
    point for the real quadratic, in the strongest elementary sense:
    its 27th iterate vanishes and none of the 26 earlier positive-time
    iterates does. -/
theorem exists_unique_exact_period27_center :
    ∃! c : ℝ,
      left < c ∧ c < right ∧
      polynomial 27 c = 0 ∧
      (∀ j : Nat, 0 < j → j < 27 → polynomial j c ≠ 0) := by
  obtain ⟨c, ⟨hl, hr, hroot⟩, hunique⟩ :=
    exists_unique_period27_center_in_dyadic_bracket
  refine ⟨c, ⟨hl, hr, hroot, ?_⟩, ?_⟩
  · exact real_no_early_critical_return c ⟨hl.le, hr.le⟩
  · intro y hy
    exact hunique y ⟨hy.1, hy.2.1, hy.2.2.1⟩

/-- The actual real quadratic as a self-map. -/
def quadratic (c : ℝ) : ℝ → ℝ :=
  fun x => x ^ 2 + c

/-- The real critical-orbit polynomial of our joint recurrence is
    exactly the iterate of the *actual* quadratic self-map at zero. -/
theorem polynomial_eq_quadratic_iterate (n : Nat) (c : ℝ) :
    polynomial n c =
      LoopsFormal.Paper2.iterate (quadratic c) n 0 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change (state (n + 1) c).1 =
        quadratic c (LoopsFormal.Paper2.iterate (quadratic c) n 0)
      rw [state_succ]
      change (polynomial n c) ^ 2 + c =
        (LoopsFormal.Paper2.iterate (quadratic c) n 0) ^ 2 + c
      rw [ih]

/-- Source-facing reformulation without using the helper name
    'polynomial': the critical point 0 for f_c(x)=x²+c returns
    for the first time precisely at 27. -/
theorem exact_real_quadratic_period27 :
    ∃! c : ℝ,
      left < c ∧ c < right ∧
      LoopsFormal.Paper2.iterate (quadratic c) 27 0 = 0 ∧
      (∀ j : Nat, 0 < j → j < 27 →
        LoopsFormal.Paper2.iterate (quadratic c) j 0 ≠ 0) := by
  obtain ⟨c, ⟨hl, hr, hroot, hnone⟩, hu⟩ :=
    exists_unique_exact_period27_center
  refine ⟨c, ⟨hl, hr, ?_, ?_⟩, ?_⟩
  · simpa only [polynomial_eq_quadratic_iterate] using hroot
  · intro j hj hlt
    simpa only [polynomial_eq_quadratic_iterate] using
      hnone j hj hlt
  · intro y hy
    apply hu y
    refine ⟨hy.1, hy.2.1, ?_, ?_⟩
    · simpa only [polynomial_eq_quadratic_iterate] using hy.2.2.1
    · intro j hj hlt
      simpa only [polynomial_eq_quadratic_iterate] using
        hy.2.2.2 j hj hlt

#print axioms real_orbit_bounds
#print axioms all_first_26_orbit_bounds_strict
#print axioms real_no_early_critical_return
#print axioms exists_unique_exact_period27_center
#print axioms exact_real_quadratic_period27

end

end LoopsRealPeriod27
