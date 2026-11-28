import ThreeLevelPhysical

/-!
# Literal first returns at every original iterate

The three nested sources are selected in the original polynomial plane.
The estimates at outer-return checkpoints extend to every integer time:
between checkpoints the complete outer source misses the outer target,
and both deeper target disks lie inside that target.
-/

namespace ThreeLevelFirstReturn

open Set Function Metric
open LimitingCrestQuadraticReturn NearTwoShooting TwoLevelOuterChart TwoLevelConjugacy
open ThreeLevelSelection ThreeLevelPhysical ThreeReturnParent TwoLevelPhysicalGate

noncomputable section

private theorem first_return_of_blocks (F : ℂ → ℂ) (p Q : ℕ)
    (S W V : Set ℂ) (hp : 0 < p)
    (hphases : ∀ m : ℕ, m ≤ Q → (F^[m*p]) '' S ⊆ W)
    (houter : ∀ i : ℕ, 1 ≤ i → i < p → Disjoint ((F^[i]) '' W) V)
    (hblocks : ∀ m : ℕ, 1 ≤ m → m < Q → Disjoint ((F^[m*p]) '' S) V)
    (n : ℕ) (hn : 1 ≤ n) (hnQ : n < Q*p) :
    Disjoint ((F^[n]) '' S) V := by
  have he := Nat.mod_add_div n p
  have hdiv : n/p < Q := by
    by_contra! hh
    have hm := Nat.mul_le_mul_right p hh
    nlinarith only [he, hm, hnQ, Nat.zero_le (n%p)]
  have hnform : n = n%p+(n/p)*p := by nlinarith only [he]
  by_cases hmod : n%p = 0
  · have hdpos : 1 ≤ n/p := by
      cases hquot : n/p with
      | zero =>
        have hnzero : n = 0 := by
          simpa only [hmod, hquot, Nat.mul_zero, Nat.add_zero] using he.symm
        omega
      | succ k => exact Nat.succ_le_succ (Nat.zero_le k)
    have hnblock : n = (n/p)*p := by
      simpa only [hmod, zero_add] using hnform
    rw [hnblock]
    exact hblocks (n/p) hdpos hdiv
  · have hi : 1 ≤ n%p := by omega
    have himax : n%p < p := Nat.mod_lt n hp
    apply Set.disjoint_left.mpr
    rintro _ ⟨z, hz, rfl⟩ hy
    have hzW : (F^[(n/p)*p]) z ∈ W :=
      hphases (n/p) hdiv.le ⟨z, hz, rfl⟩
    apply (Set.disjoint_left.mp (houter (n%p) hi himax)) _ hy
    refine ⟨(F^[(n/p)*p]) z, hzW, ?_⟩
    simpa only [iterate_add_apply] using
      congrArg (fun k : ℕ => (F^[k]) z) hnform.symm

/-- The middle target is strictly smaller than the outer target in
the same original coordinate; the signed scale is used only through
its absolute value when comparing the two radii. -/
theorem middleRadius_lt_outerRadius {p q : ℕ} (hp : 17 ≤ p) (hq : 17 ≤ q)
    {a b L U c : ℝ} (j : OuterChart p a b L U) (hc : c ∈ Icc L U) :
    middleRadius c p q < TwoLevelOuterDomain.targetRadius p := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hAa : 0 < |returnCoefficient p c| := abs_pos.mpr hA.ne
  have hs : scale p ≤ TwoLevelOuterDomain.targetRadius p := by
    have h := ThreeLevelMiddle.scale_inside_radius hp
    change 128*scale p < TwoLevelOuterDomain.targetRadius p at h
    linarith [scale_pos p]
  have hm := mul_le_mul_of_nonneg_left hs hAa.le
  have hlo : (3/20 : ℝ) < |returnCoefficient p c| * scale p := by
    rw [abs_of_neg hA]
    exact j.coefficient_lower c hc
  unfold middleRadius
  apply (div_lt_iff₀ hAa).mpr
  nlinarith only [hm, hlo, ThreeLevelMiddle.radius_small hq]

/-- The terminal physical target fits inside the complete middle target,
uniformly throughout the entire nested parameter chart. -/
theorem terminalRadius_lt_middleRadius {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U) :
    |criticalValue c ((r*q)*p)| * (23/20) < middleRadius c p q := by
  have hq : 17 ≤ q := by omega
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hAa : 0 < |returnCoefficient p c| := abs_pos.mpr hA.ne
  have href := ThreeLevelReference.terminal_scale_upper hr hqr h g (j.monic_range hc)
  have hrel := chart_scale_relative hr hqr hp h g j hc
  have htriangle : |secondScale c p (r*q)| ≤
      |secondScale c p (r*q)-criticalValue (monicParameter p c) (r*q)| +
        |criticalValue (monicParameter p c) (r*q)| := by
    calc
      _ = |(secondScale c p (r*q)-criticalValue (monicParameter p c) (r*q))+
        criticalValue (monicParameter p c) (r*q)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hsr : scale r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hprod := mul_le_mul_of_nonneg_left hsr (scale_pos q).le
  have hD : |secondScale c p (r*q)| < 82*scale q := by
    nlinarith only [href, hrel, htriangle, hprod, scale_pos q]
  have hphysical : |returnCoefficient p c| * |criticalValue c ((r*q)*p)| =
      |secondScale c p (r*q)| := by
    rw [← abs_mul]
    rfl
  unfold middleRadius
  apply (lt_div_iff₀ hAa).mpr
  calc
    |criticalValue c ((r*q)*p)| * (23/20) * |returnCoefficient p c| =
        |secondScale c p (r*q)| * (23/20) := by rw [← hphysical]; ring
    _ < ThreeLevelMiddle.radius q := by
      nlinarith only [hD, ThreeLevelMiddle.scale_inside_radius hq, scale_pos q]

theorem terminalTarget_subset_middleTarget {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U) :
    physicalTarget c ((r*q)*p) ⊆ ball 0 (middleRadius c p q) :=
  ball_subset_ball (terminalRadius_lt_middleRadius hr hqr hp h g j hc).le

theorem middleTarget_subset_outerTarget {p q : ℕ} (hp : 17 ≤ p) (hq : 17 ≤ q)
    {a b L U c : ℝ} (j : OuterChart p a b L U) (hc : c ∈ Icc L U) :
    ball (0 : ℂ) (middleRadius c p q) ⊆ ball 0 (TwoLevelOuterDomain.targetRadius p) :=
  ball_subset_ball (middleRadius_lt_outerRadius hp hq j hc).le

theorem chart_outer_first_return {p : ℕ} (hp : 17 ≤ p)
    {a b L U c : ℝ} (j : OuterChart p a b L U) (hc : c ∈ Icc L U)
    (n : ℕ) (hn : 1 ≤ n) (hnp : n < p) :
    Disjoint (((quadraticMap c)^[n]) '' TwoLevelOuterDomain.source c p)
      (ball 0 (TwoLevelOuterDomain.targetRadius p)) := by
  have hcl := (TwoLevelOuterDomain.source_closure hp (j.critical_orbit c hc)
    (j.return_range c hc).1 (j.return_range c hc).2 (j.coefficient_lower c hc)).1
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩ hy
  have hzsmall : ‖z‖ < TwoLevelOuterDomain.targetRadius p/2 := by
    simpa only [mem_ball_zero_iff] using hcl (subset_closure hz)
  have hzR : ‖z‖ ≤ TwoLevelOuterDomain.targetRadius p := by
    linarith [TwoLevelOuterDomain.targetRadius_pos p]
  have hex := TwoLevelOuterDomain.outer_first_return_exclusion hp (j.parameter_range c hc)
    (j.critical_orbit c hc) (j.return_range c hc).1 (j.return_range c hc).2
    (j.itinerary c hc) n hn hnp hzR
  have hyR : ‖((quadraticMap c)^[n]) z‖ < TwoLevelOuterDomain.targetRadius p := by
    simpa only [mem_ball_zero_iff] using hy
  exact (not_lt_of_ge hex.le) hyR

/-- The whole middle source has literal first-return time `q*p`,
with exclusion at every earlier positive integer time. -/
theorem chart_middle_first_return_all {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U)
    (n : ℕ) (hn : 1 ≤ n) (hnq : n < q*p) :
    Disjoint (((quadraticMap c)^[n]) '' middleSource c p q)
      (ball 0 (middleRadius c p q)) := by
  refine first_return_of_blocks (quadraticMap c) p q
    (middleSource c p q) (TwoLevelOuterDomain.source c p)
    (ball 0 (middleRadius c p q)) (by omega)
    (chart_middle_phases_nested hr hqr hp h g j hc) ?_
    (chart_middle_first_return hr hqr hp h g j hc) n hn hnq
  intro i hi hip
  exact (chart_outer_first_return (by omega) j hc i hi hip).mono_right
    (middleTarget_subset_outerTarget (by omega) (by omega) j hc)

/-- The whole terminal source has literal first-return time `(r*q)*p`.
The exclusion includes every time inside an outer-return block. -/
theorem chart_terminal_first_return_all {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U)
    (n : ℕ) (hn : 1 ≤ n) (hnr : n < (r*q)*p) :
    Disjoint (((quadraticMap c)^[n]) '' physicalParentSource c ((r*q)*p))
      (physicalTarget c ((r*q)*p)) := by
  refine first_return_of_blocks (quadraticMap c) p (r*q)
    (physicalParentSource c ((r*q)*p)) (TwoLevelOuterDomain.source c p)
    (physicalTarget c ((r*q)*p)) (by omega)
    (chart_terminal_outer_phases hr hqr hp h g j hc) ?_
    (chart_terminal_first_return hr hqr hp h g j hc) n hn hnr
  intro i hi hip
  exact (chart_outer_first_return (by omega) j hc i hi hip).mono_right
    ((terminalTarget_subset_middleTarget hr hqr hp h g j hc).trans
      (middleTarget_subset_outerTarget (by omega) (by omega) j hc))

/-- Three actual proper degree-two returns with exclusion at every
earlier original iterate and strict nesting of their target disks. -/
structure FirstReturnThreeLevelGate (p q r : ℕ) (c : ℝ) : Prop
    extends PhysicalThreeLevelGate p q r c where
  middle_first_all : ∀ n : ℕ, 1 ≤ n → n < q*p →
    Disjoint (((quadraticMap c)^[n]) '' middleSource c p q)
      (ball 0 (middleRadius c p q))
  terminal_first_all : ∀ n : ℕ, 1 ≤ n → n < (r*q)*p →
    Disjoint (((quadraticMap c)^[n]) '' physicalParentSource c ((r*q)*p))
      (physicalTarget c ((r*q)*p))
  middle_radius_lt_outer : middleRadius c p q < TwoLevelOuterDomain.targetRadius p
  terminal_radius_lt_middle :
    |criticalValue c ((r*q)*p)| * (23/20) < middleRadius c p q

/-- For every product-separated period triple, one original quadratic
has simultaneous complete physical return components of periods `p`,
`q*p`, and `(r*q)*p`, all with literal first-return exclusion. -/
theorem exists_first_return_three_level_gate (p q r : ℕ) (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p) :
    ∃ c : ℝ, FirstReturnThreeLevelGate p q r c := by
  obtain ⟨a, b, l, u, L, U, c, h, g, j, hc, hrel, _⟩ :=
    exists_three_level_parameter p q r hr hqr hp
  exact ⟨c, {
    toPhysicalThreeLevelGate := chart_physical_three_level_gate hr hqr hp h g j hc hrel
    middle_first_all := chart_middle_first_return_all hr hqr hp h g j hc
    terminal_first_all := chart_terminal_first_return_all hr hqr hp h g j hc
    middle_radius_lt_outer := middleRadius_lt_outerRadius (by omega) (by omega) j hc
    terminal_radius_lt_middle := terminalRadius_lt_middleRadius hr hqr hp h g j hc }⟩

end
end ThreeLevelFirstReturn
