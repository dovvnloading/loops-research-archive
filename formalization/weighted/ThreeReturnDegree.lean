import QuadraticCrestDividedDifference
import ThreeReturnEstimates
import Mathlib.Data.Set.Card

/-!
# The two sheets of the actual three-return restriction

The first normalized return has exactly the quadratic signed collisions
throughout its control disk.  The two later phase images have opposite
strict real signs.  Thus neither later return can create another sheet
on the selected central disk.  The diagonal divided difference also
identifies the actual complex derivative and its only critical point.

The final fiber statements use literal subsets of the complex plane.
Their domain hypotheses are supplied by the canonical pullback-component
construction, rather than by an assigned degree label.
-/

namespace ThreeReturnDegree

open Set Function LimitingCrestQuadraticReturn
open QuadraticCrestDividedDifference
open NearTwoShooting NearTwoTip ThreeReturnEstimates

noncomputable section

/-- Phase separation propagates the exact signed collision relation
through three returns. -/
theorem three_return_collision_iff (F : ℂ → ℂ) {R L : ℝ}
    (hRL : R ≤ L)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ L → ‖w‖ ≤ L →
      (F z = F w ↔ z = w ∨ z = -w))
    (hphase : ∀ z : ℂ, ‖z‖ ≤ R →
      ‖F z‖ ≤ L ∧ ‖F (F z)‖ ≤ L ∧
      0 < (F z).re ∧ (F (F z)).re < 0)
    {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    (F^[3]) z = (F^[3]) w ↔ z = w ∨ z = -w := by
  have hzP := hphase z hz
  have hwP := hphase w hw
  change F (F (F z)) = F (F (F w)) ↔ z = w ∨ z = -w
  constructor
  · intro h
    have hsecond : F (F z) = F (F w) := by
      rcases (hcollision hzP.2.1 hwP.2.1).mp h with he | he
      · exact he
      · have hre := congrArg Complex.re he
        simp only [Complex.neg_re] at hre
        linarith [hzP.2.2.2, hwP.2.2.2]
    have hfirst : F z = F w := by
      rcases (hcollision hzP.1 hwP.1).mp hsecond with he | he
      · exact he
      · have hre := congrArg Complex.re he
        simp only [Complex.neg_re] at hre
        linarith [hzP.2.2.1, hwP.2.2.1]
    exact (hcollision (hz.trans hRL) (hw.trans hRL)).mp hfirst
  · intro h
    rw [(hcollision (hz.trans hRL) (hw.trans hRL)).mpr h]

/-- The collision theorem applies to the complete actual polynomial
return, under its previously certified parameter bounds. -/
theorem normalized_three_return_collision_iff (c : ℝ) (p : ℕ)
    (hp : 13 ≤ p) (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12 / (4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1) * criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000))
    (hphase : ∀ z : ℂ, ‖z‖ ≤ 1/6 →
      ‖normalizedReturn c p z‖ ≤ 23/20 ∧
      ‖normalizedReturn c p (normalizedReturn c p z)‖ ≤ 23/20 ∧
      0 < (normalizedReturn c p z).re ∧
      (normalizedReturn c p (normalizedReturn c p z)).re < 0)
    {z w : ℂ} (hz : ‖z‖ ≤ 1/6) (hw : ‖w‖ ≤ 1/6) :
    ((normalizedReturn c p)^[3]) z = ((normalizedReturn c p)^[3]) w ↔
      z = w ∨ z = -w := by
  exact three_return_collision_iff (normalizedReturn c p)
    (by norm_num : (1/6 : ℝ) ≤ 23/20)
    (normalized_return_collision_iff c p hp hc hd hsmall hk) hphase hz hw

/-- The diagonal of the complete even secant is the exact derivative
factor after the original critical quadratic step. -/
theorem iterate_hasDerivAt (c : ℝ) (n : ℕ) (z : ℂ) :
    HasDerivAt ((quadraticMap c)^[n+1])
      (2 * z * evenSecant c n z z) z := by
  have hquad (u : ℂ) : HasDerivAt (quadraticMap c) (2 * u) u := by
    change HasDerivAt (fun w : ℂ => w^2 + (c : ℂ)) (2 * u) u
    exact (((hasDerivAt_id u).pow 2).add_const (c : ℂ)).congr_deriv (by simp)
  induction n with
  | zero => simpa [evenSecant] using hquad z
  | succ n ih =>
    have h := (hquad (((quadraticMap c)^[n+1]) z)).comp z ih
    have he : (quadraticMap c)^[n+1+1] =
        quadraticMap c ∘ (quadraticMap c)^[n+1] := by
      funext w
      exact iterate_succ_apply' (quadraticMap c) (n+1) w
    rw [he]
    exact h.congr_deriv (by
      simp only [evenSecant]
      ring
      )

/-- Complex differentiation of the literal normalization preserves the
complete divided difference, including every iterate term. -/
theorem normalized_return_hasDerivAt (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : criticalValue c p ≠ 0) (z : ℂ) :
    HasDerivAt (normalizedReturn c p)
      (2 * z * normalizedSecant c p z z) z := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hdC : (criticalValue c (n+1) : ℂ) ≠ 0 := by exact_mod_cast hd
  have hscale : HasDerivAt (fun w : ℂ => (criticalValue c (n+1) : ℂ) * w)
      (criticalValue c (n+1) : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (criticalValue c (n+1) : ℂ)
  have h := ((iterate_hasDerivAt c n
    ((criticalValue c (n+1) : ℂ) * z)).comp z hscale).div_const
      (criticalValue c (n+1) : ℂ)
  change HasDerivAt (fun w : ℂ =>
    ((quadraticMap c)^[n+1]) ((criticalValue c (n+1) : ℂ) * w) /
      (criticalValue c (n+1) : ℂ)) _ z
  exact h.congr_deriv (by
    simp only [normalizedSecant, Nat.succ_sub_one]
    field_simp [hdC]
    )

/-- Exactly the origin is critical for the actual three-return on the
entire selected disk; the two later factors are regular there. -/
theorem normalized_three_return_deriv_eq_zero_iff (c : ℝ) (p : ℕ)
    (hp : 13 ≤ p) (hc : c ∈ Icc (-2 : ℝ) 0)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12 / (4 : ℝ)^p)
    (hk : -quadraticCoefficient c (p-1) * criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000))
    (hphase : ∀ z : ℂ, ‖z‖ ≤ 1/6 →
      ‖normalizedReturn c p z‖ ≤ 23/20 ∧
      ‖normalizedReturn c p (normalizedReturn c p z)‖ ≤ 23/20 ∧
      0 < (normalizedReturn c p z).re ∧
      (normalizedReturn c p (normalizedReturn c p z)).re < 0)
    {z : ℂ} (hz : ‖z‖ ≤ 1/6) :
    deriv ((normalizedReturn c p)^[3]) z = 0 ↔ z = 0 := by
  let F := normalizedReturn c p
  let D := normalizedSecant c p
  have hP := hphase z hz
  have hsec {w : ℂ} (hw : ‖w‖ ≤ 23/20) : D w w ≠ 0 := by
    have h := (normalizedSecant_norm_bounds c p hp hc hd hsmall hk hw hw).1
    intro he
    change normalizedSecant c p w w = 0 at he
    rw [he, norm_zero] at h
    norm_num at h
  have hs0 : D z z ≠ 0 := hsec (hz.trans (by norm_num))
  have hs1 : D (F z) (F z) ≠ 0 := hsec hP.1
  have hs2 : D (F (F z)) (F (F z)) ≠ 0 := hsec hP.2.1
  have hf1 : F z ≠ 0 := by
    intro he
    have hre := hP.2.2.1
    change 0 < (F z).re at hre
    simp only [he, Complex.zero_re, lt_self_iff_false] at hre
  have hf2 : F (F z) ≠ 0 := by
    intro he
    have hre := hP.2.2.2
    change (F (F z)).re < 0 at hre
    simp only [he, Complex.zero_re, lt_self_iff_false] at hre
  have h0 := normalized_return_hasDerivAt c p (by omega) hd.ne' z
  have h1 := normalized_return_hasDerivAt c p (by omega) hd.ne' (F z)
  have h2 := normalized_return_hasDerivAt c p (by omega) hd.ne' (F (F z))
  have hthree := h2.comp z (h1.comp z h0)
  change HasDerivAt (F^[3])
      ((2 * F (F z) * D (F (F z)) (F (F z))) *
        ((2 * F z * D (F z) (F z)) * (2 * z * D z z))) z at hthree
  change deriv (F^[3]) z = 0 ↔ z = 0
  rw [hthree.deriv]
  simp [mul_eq_zero, hs0, hs1, hs2, hf1, hf2]

/-- The numerical enclosures give the two strict phase signs on the
entire canonical outer disk, with no domain shrinking. -/
theorem actual_phase_signs {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 1/6) :
    ‖normalizedReturn c p z‖ ≤ 23/20 ∧
    ‖normalizedReturn c p (normalizedReturn c p z)‖ ≤ 23/20 ∧
    0 < (normalizedReturn c p z).re ∧
    (normalizedReturn c p (normalizedReturn c p z)).re < 0 := by
  have hb := actual_phase_bounds hp hc hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [iterate_one] using (hb.2.2.2 1 (by omega)).le
  · exact (hb.2.2.2 2 (by omega)).le
  · have hre := (abs_le.mp
      (Complex.abs_re_le_norm (normalizedReturn c p z - 1))).1
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith [hb.1]
  · have hsecond := hb.2.1
    change ‖normalizedReturn c p (normalizedReturn c p z) -
      ((1 - kappa p c : ℝ) : ℂ)‖ < 19/100 at hsecond
    have hre := (abs_le.mp (Complex.abs_re_le_norm
      (normalizedReturn c p (normalizedReturn c p z) -
        ((1 - kappa p c : ℝ) : ℂ)))).2
    simp only [Complex.sub_re, Complex.ofReal_re] at hre
    have hk := hc.2.2.2.1.1
    change 17903/10000 ≤ kappa p c at hk
    linarith

private theorem actual_parameter_data {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    c ∈ Icc (-2 : ℝ) 0 ∧ 0 < criticalValue c p ∧
    criticalValue c p ≤ 12 / (4 : ℝ)^p ∧
    -quadraticCoefficient c (p-1) * criticalValue c p ∈
      Icc (17903/10000 : ℝ) (17904/10000) := by
  have hband := parameter_band hp hc.1
  refine ⟨⟨hband.1, by linarith [hband.2]⟩, hc.2.1, ?_, hc.2.2.2.1⟩
  simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1

/-- Every actual parameter supplied by the all-period tip construction
has precisely the two signed sheets on the whole canonical outer disk. -/
theorem actual_three_return_collision_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ} (hz : ‖z‖ ≤ 1/6) (hw : ‖w‖ ≤ 1/6) :
    ((normalizedReturn c p)^[3]) z = ((normalizedReturn c p)^[3]) w ↔
      z = w ∨ z = -w := by
  obtain ⟨hpar, hd, hsmall, hk⟩ := actual_parameter_data hp hc
  exact normalized_three_return_collision_iff c p (by omega) hpar hd hsmall hk
    (fun _ hz => actual_phase_signs hp hc hz) hz hw

/-- The actual three-return has exactly one complex critical point on
the canonical outer disk, uniformly for all periods at least seventeen. -/
theorem actual_three_return_deriv_eq_zero_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 1/6) :
    deriv ((normalizedReturn c p)^[3]) z = 0 ↔ z = 0 := by
  obtain ⟨hpar, hd, hsmall, hk⟩ := actual_parameter_data hp hc
  exact normalized_three_return_deriv_eq_zero_iff c p (by omega) hpar hd hsmall hk
    (fun _ hz => actual_phase_signs hp hc hz) hz

/-- Exact equality of the actual central fiber with its signed pair. -/
theorem symmetric_fiber_pair (H : ℂ → ℂ) (W : Set ℂ)
    (hcollision : ∀ {z w : ℂ}, z ∈ W → w ∈ W →
      (H z = H w ↔ z = w ∨ z = -w))
    (hsym : ∀ z ∈ W, -z ∈ W) {z : ℂ} (hz : z ∈ W) :
    {w : ℂ | w ∈ W ∧ H w = H z} = {z, -z} := by
  ext w
  simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hw, he⟩
    exact (hcollision hw hz).mp he
  · rintro (rfl | rfl)
    · exact ⟨hz, rfl⟩
    · exact ⟨hsym z hz, (hcollision (hsym z hz) hz).mpr (Or.inr rfl)⟩

/-- The critical value has one and only one point in the selected domain. -/
theorem critical_fiber_singleton (H : ℂ → ℂ) (W : Set ℂ) (h0 : (0 : ℂ) ∈ W)
    (hcollision : ∀ {z w : ℂ}, z ∈ W → w ∈ W →
      (H z = H w ↔ z = w ∨ z = -w)) :
    {w : ℂ | w ∈ W ∧ H w = H 0} = {0} := by
  ext w
  simp only [mem_setOf_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hw, he⟩
    simpa using (hcollision hw h0).mp he
  · rintro rfl
    exact ⟨h0, rfl⟩

/-- Surjectivity and signed collision control identify every regular
fiber as two distinct physical points. -/
theorem noncritical_fiber_pair (H : ℂ → ℂ) (W V : Set ℂ)
    (hcollision : ∀ {z w : ℂ}, z ∈ W → w ∈ W →
      (H z = H w ↔ z = w ∨ z = -w))
    (hsym : ∀ z ∈ W, -z ∈ W) (honto : SurjOn H W V)
    {y : ℂ} (hy : y ∈ V) (hy0 : y ≠ H 0) :
    ∃ z ∈ W, z ≠ 0 ∧ z ≠ -z ∧
      {w : ℂ | w ∈ W ∧ H w = y} = {z, -z} := by
  obtain ⟨z, hz, hzy⟩ := honto hy
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hy0 hzy.symm
  refine ⟨z, hz, hz0, ?_, ?_⟩
  · exact fun he => hz0 (CharZero.eq_neg_self_iff.mp he)
  · rw [← hzy]
    exact symmetric_fiber_pair H W hcollision hsym hz

/-- A cardinality statement over genuine plane fibers, with the unique
critical fiber distinguished explicitly. -/
theorem fiber_ncard (H : ℂ → ℂ) (W V : Set ℂ) (h0 : (0 : ℂ) ∈ W)
    (hcollision : ∀ {z w : ℂ}, z ∈ W → w ∈ W →
      (H z = H w ↔ z = w ∨ z = -w))
    (hsym : ∀ z ∈ W, -z ∈ W) (honto : SurjOn H W V)
    {y : ℂ} (hy : y ∈ V) :
    {w : ℂ | w ∈ W ∧ H w = y}.ncard = if y = H 0 then 1 else 2 := by
  classical
  by_cases hy0 : y = H 0
  · rw [if_pos hy0, hy0, critical_fiber_singleton H W h0 hcollision]
    exact ncard_singleton 0
  · rw [if_neg hy0]
    obtain ⟨z, _, _, hsign, hfiber⟩ :=
      noncritical_fiber_pair H W V hcollision hsym honto hy hy0
    rw [hfiber]
    exact ncard_pair hsign

end

end ThreeReturnDegree
