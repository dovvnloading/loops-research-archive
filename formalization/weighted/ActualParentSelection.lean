import ActualParentSupremum
import GlobalPrimitiveTipUniqueness
import GlobalWindowLocalization
import GlobalRestrictiveConverse
import GlobalWindowBoundaryProduct

/-!
# The named physical signed-tip selection and its literal kneading chart

The parameter is selected from the unique global physical signed-tip
class. Membership in the source's explicit signed kneading chart is a
conclusion, including its exact orbit-product coefficient. This module
does not identify an entire maximal primitive parameter component.
-/

namespace ActualParentSelection

open Set Filter Function
open NearTwoShooting NearTwoTip LimitingCrestQuadraticReturn
open GlobalRestrictiveWindow GlobalActualWindow GlobalPrimitiveTipUniqueness
open ActualParentSupremum LoopsLimitingCrestParameter
open scoped Topology

noncomputable section

/-- The literal product coefficient used by the source's signed chart. -/
def tau (p : ℕ) (c : ℝ) : ℝ :=
  (∏ j ∈ Finset.range (p-1), 2*criticalValue c (j+1)) * criticalValue c p

theorem quadraticCoefficient_eq_orbit_product (c : ℝ) (n : ℕ) :
    quadraticCoefficient c n =
      ∏ j ∈ Finset.range n, 2*criticalValue c (j+1) := by
  induction n with
  | zero => simp [quadraticCoefficient]
  | succ n ih =>
    rw [quadraticCoefficient,Finset.prod_range_succ,ih]
    ring

theorem tau_eq_neg_kappa (p : ℕ) (c : ℝ) : tau p c = -kappa p c := by
  rw [tau,← quadraticCoefficient_eq_orbit_product]
  unfold kappa
  ring

/-- A positive shooting parameter with normalized quadratic coefficient
below two already has the whole physical invariant return interval.
The exact inverse secant product, not a model-map estimate, supplies
the endpoint inequality used by the global converse. -/
theorem restrictive_of_shooting_kappa_lt_two {p : ℕ} (hp : 17 ≤ p) {c d : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p))
    (hd : 0 < d) (hdu : d ≤ 14*scale p)
    (hs : shooting (p-2) d c = 0) (hk : kappa p c < 2) :
    PositiveRestrictiveReturn c p := by
  have hq := scale_small hp
  have hcb := NearTwoShooting.parameter_band hp hc
  have hdb : d ∈ Icc (0 : ℝ) 2 := ⟨hd.le,by linarith⟩
  have hcneg : c < 0 := by linarith [hcb.2]
  have hcv : criticalValue c p = d := by
    simpa only [Nat.sub_add_cancel (by omega : 2 ≤ p)] using
      shooting_terminal_value hcb hdb hs
  have hbackcrit : NearTwoInverse.back c (p-1) d = -c := by
    have he : NearTwoInverse.back c (p-2) d = c^2+c := by
      dsimp [shooting] at hs
      linarith only [hs]
    rw [show p-1=(p-2)+1 by omega,NearTwoInverse.back_succ,he,NearTwoInverse.B,
      add_sub_cancel_right,Real.sqrt_sq_eq_abs,abs_of_neg hcneg]
  let P : ℝ := ∏ j ∈ Finset.range (p-1), NearTwoInverse.back c (j+1) d/2
  have hcoef := shooting_coefficient_product hcb hdb hs
  have hcoef' : -quadraticCoefficient c (p-1)*scale p =
      (-c)/8*∏ j ∈ Finset.range (p-2), NearTwoInverse.back c (j+1) d/2 := by
    simpa only [show p-2+1=p-1 by omega,show p-2+2=p by omega] using hcoef
  have hP : P = 4*(-quadraticCoefficient c (p-1)*scale p) := by
    rw [hcoef']
    dsimp [P]
    rw [show p-1=(p-2)+1 by omega,Finset.prod_range_succ]
    rw [show p-2+1=p-1 by omega,hbackcrit]
    ring
  have hscale := GlobalWindowInverseShape.scale_power_identity (p := p) (by omega)
  have hkP : kappa p c = d*(4 : ℝ)^(p-1)*P := by
    unfold kappa
    rw [hcv,hP]
    calc
      -quadraticCoefficient c (p-1)*d =
          (-quadraticCoefficient c (p-1)*d)*(4*((4 : ℝ)^(p-1)*scale p)) := by
            rw [hscale]
            ring
      _ = _ := by ring
  have hPsec : GlobalWindowBoundaryProduct.endpointProduct c p d ≤ P := by
    unfold GlobalWindowBoundaryProduct.endpointProduct
    apply Finset.prod_le_prod
    · intro j _
      apply div_nonneg
      · apply add_nonneg
        · rw [NearTwoInverse.back_succ]
          exact NearTwoInverse.B_nonneg c _
        · rw [NearTwoInverse.back_succ]
          exact NearTwoInverse.B_nonneg c _
      · norm_num
    · intro j _
      have hm := NearTwoInverse.back_mono_initial c (j+1) (show -d ≤ d by linarith)
      linarith only [hm]
  have hprod := GlobalWindowBoundaryProduct.endpointProduct_bounds hp hc ⟨hd.le,hdu⟩
  have hf : 0 < (4 : ℝ)^(p-1)*GlobalWindowBoundaryProduct.endpointProduct c p d :=
    mul_pos (by positivity) (by linarith [hprod.1])
  have hlt : d*((4 : ℝ)^(p-1)*GlobalWindowBoundaryProduct.endpointProduct c p d) < 2 := by
    have hm := mul_le_mul_of_nonneg_left hPsec
      (show 0 ≤ d*(4 : ℝ)^(p-1) by positivity)
    rw [← hkP] at hm
    nlinarith only [hm,hk]
  have hid := GlobalWindowBoundaryProduct.endpointProduct_identity hp hc ⟨hd.le,hdu⟩
  have hm := mul_lt_mul_of_pos_left hlt hd
  have hend : d^2 < NearTwoInverse.back c (p-1) d-NearTwoInverse.back c (p-1) (-d) := by
    apply (mul_lt_mul_iff_left₀ hf).mp
    nlinarith only [hm,hid]
  exact (GlobalWindowShooting.restrictive_iff_endpoint hp hc hd hdu hs).mpr hend.le

/-- The large-period signed kneading chart of the family statement.
The signed sixth-versus-third equation is not part of this definition. -/
structure SignedKneadingChart (p : ℕ) (c : ℝ) : Prop where
  parameter : c+2 ∈ Ioo (14*scale p) (16*scale p)
  return_size : |criticalValue c p| < 14*scale p
  coefficient : tau p c ∈ Ioo (-2 : ℝ) (1/4)
  first_negative : criticalValue c 1 < 0
  positive_prefix : ∀ j : ℕ, 2 ≤ j → j ≤ p → 0 < criticalValue c j
  first_return : 0 < criticalValue c p
  second_return : criticalValue c (2*p) < 0
  third_return : criticalValue c (3*p) < 0
  fourth_return : 0 < criticalValue c (4*p)
  fifth_return : criticalValue c (5*p) < 0
  sixth_return : 0 < criticalValue c (6*p)

/-- The archived actual parameters satisfy the source's narrower named
chart and its complete finite sign prescription. -/
theorem actual_tip_mem_signedKneadingChart {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : SignedKneadingChart p c := by
  have h := actual_tip_restrictive_return hp hc
  have hs := actual_tip_physical hp hc
  refine {
    parameter := h.sharp_parameter_bounds hp
    return_size := ?_
    coefficient := ?_
    first_negative := ?_
    positive_prefix := h.critical_prefix
    first_return := hs.return_pos
    second_return := hs.second_neg
    third_return := hs.third_neg
    fourth_return := hs.fourth_pos
    fifth_return := hs.fifth_neg
    sixth_return := ?_ }
  · rw [abs_of_pos h.return_pos]
    exact h.return_scale hp
  · rw [tau_eq_neg_kappa]
    have hk := hc.2.2.2.1
    constructor <;> linarith [hk.1,hk.2]
  · have hn := h.negative_first 0 h.zero_mem
    simpa [criticalValue,realMap] using hn
  · linarith [hs.signed_relation,hs.third_neg]

/-- Every point of the literal signed chart has the canonical physical
return interval; the interval is derived rather than added to the chart. -/
theorem SignedKneadingChart.restrictive {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : SignedKneadingChart p c) : PositiveRestrictiveReturn c p := by
  have hq := scale_pos p
  have hband : c ∈ Icc (-2 : ℝ) (-2+20*scale p) := by
    constructor <;> linarith [hc.parameter.1,hc.parameter.2]
  have hsmall : criticalValue c p ≤ 14*scale p :=
    (le_abs_self _).trans hc.return_size.le
  have hs := forward_orbit_shooting (c := c) (n := p-2) (by
    intro j hj
    exact (hc.positive_prefix (j+2) (by omega) (by omega)).le)
  have hs' : shooting (p-2) (criticalValue c p) c = 0 := by
    simpa only [Nat.sub_add_cancel (by omega : 2 ≤ p)] using hs
  have hk : kappa p c < 2 := by
    have h := hc.coefficient.1
    rw [tau_eq_neg_kappa] at h
    linarith
  exact restrictive_of_shooting_kappa_lt_two hp hband hc.first_return hsmall hs' hk

theorem SignedKneadingChart.physical_signed_tip {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : SignedKneadingChart p c)
    (hroot : criticalValue c (6*p)+criticalValue c (3*p)=0) :
    PhysicalSignedTip p c := by
  have h := hc.restrictive hp
  exact ⟨⟨criticalValue c p,⟨h.return_pos,h.negative_first,h.positive_phases,h.invariant⟩⟩,
    hc.first_return,hc.second_return,hc.third_return,hc.fourth_return,hc.fifth_return,hroot⟩

/-- The literal source signed-chart root and the archived quantitative
actual-tip predicate describe exactly the same parameter. -/
theorem signed_chart_root_iff_actual_tip {p : ℕ} (hp : 17 ≤ p) {c : ℝ} :
    (SignedKneadingChart p c ∧
      criticalValue c (6*p)+criticalValue c (3*p)=0) ↔ ActualTip p c := by
  constructor
  · rintro ⟨hc,hroot⟩
    exact (physical_signed_tip_iff_actual_tip hp).mp (hc.physical_signed_tip hp hroot)
  · intro hc
    exact ⟨actual_tip_mem_signedKneadingChart hp hc,hc.2.2.2.2.1⟩

/-- Existence and uniqueness are proved in the source's equation-free
signed kneading chart itself, without an extra invariant-interval premise. -/
theorem exists_unique_signed_chart_root (p : ℕ) (hp : 17 ≤ p) :
    ∃! c : ℝ, SignedKneadingChart p c ∧
      criticalValue c (6*p)+criticalValue c (3*p)=0 := by
  obtain ⟨c,hc,hunique⟩ := GlobalActualSignedUniqueness.exists_unique_actual_tip p hp
  exact ⟨c,(signed_chart_root_iff_actual_tip hp).mpr hc,
    fun a ha => hunique a ((signed_chart_root_iff_actual_tip hp).mp ha)⟩


/-- The unique parameter in the complete physical signed class. -/
def canonicalParameter (p : ℕ) (hp : 17 ≤ p) : ℝ :=
  Classical.choose (exists_unique_physical_signed_tip p hp)

theorem canonicalParameter_physical (p : ℕ) (hp : 17 ≤ p) :
    PhysicalSignedTip p (canonicalParameter p hp) :=
  (Classical.choose_spec (exists_unique_physical_signed_tip p hp)).1

theorem canonicalParameter_actual (p : ℕ) (hp : 17 ≤ p) :
    ActualTip p (canonicalParameter p hp) :=
  (physical_signed_tip_iff_actual_tip hp).mp (canonicalParameter_physical p hp)

theorem canonicalParameter_chart (p : ℕ) (hp : 17 ≤ p) :
    SignedKneadingChart p (canonicalParameter p hp) :=
  actual_tip_mem_signedKneadingChart hp (canonicalParameter_actual p hp)

/-- Any literal physical signed root is the named parameter, without
assuming a chart, return-scale bound, or normalized coefficient window. -/
theorem physical_tip_eq_canonical {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : PhysicalSignedTip p c) : c = canonicalParameter p hp :=
  physical_signed_tip_unique hp hc (canonicalParameter_physical p hp)

/-- The uniquely named root in the original signed kneading chart
is exactly the canonical physical parameter used for the width sequence. -/
theorem signed_chart_root_eq_canonical {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : SignedKneadingChart p c)
    (hroot : criticalValue c (6*p)+criticalValue c (3*p)=0) :
    c = canonicalParameter p hp :=
  physical_tip_eq_canonical hp (hc.physical_signed_tip hp hroot)


/-- The fixed tail used for convergence; no arbitrary parameter choices
remain in this sequence. -/
def canonicalSequence (n : ℕ) : ℝ := canonicalParameter (n+17) (by omega)

theorem canonicalSequence_actual (n : ℕ) : ActualTip (n+17) (canonicalSequence n) :=
  canonicalParameter_actual (n+17) (by omega)

theorem physical_sequence_eq_canonical (c : ℕ → ℝ)
    (hc : ∀ n, PhysicalSignedTip (n+17) (c n)) : c = canonicalSequence := by
  funext n
  exact physical_tip_eq_canonical (by omega) (hc n)

theorem canonical_physical_parent_optimum_real_converges
    {k : ℝ} (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    Tendsto (fun n =>
      (physicalParentWidth (by omega : 17 ≤ n+17)
        (canonicalSequence_actual n) hk hroot).toReal)
      atTop (𝓝 (limitingParentWidth k hk).toReal) :=
  physical_parent_optimum_real_converges hk hroot canonicalSequence canonicalSequence_actual

end
end ActualParentSelection

