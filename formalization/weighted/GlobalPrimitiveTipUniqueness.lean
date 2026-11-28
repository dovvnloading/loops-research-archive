import GlobalPrimitiveIntervalRecognition
import GlobalWindowRootLocalization
import GlobalActualSignedUniqueness
import GlobalWindowPhases

/-!
# Global uniqueness from a literal physical return interval

The parameter ranges over all real numbers and the supplied invariant
interval may have any positive radius.  No parameter chart, normalized
coefficient interval, or critical-return scale is included in the
definition of a physical signed tip.
-/

namespace GlobalPrimitiveTipUniqueness

open Set Function NearTwoShooting NearTwoTip
open LimitingCrestQuadraticReturn GlobalRestrictiveWindow
open GlobalPrimitiveIntervalRecognition GlobalWindowSignedChart
open GlobalWindowRootFactor GlobalWindowRootLocalization GlobalSignedModelFactor
open GlobalActualWindow GlobalActualSignedUniqueness LoopsLimitingCrestParameter

noncomputable section

/-- An actual signed tip described by a physical invariant interval
and literal critical-return signs. All quantitative chart conditions are
conclusions of the theorems below. -/
structure PhysicalSignedTip (p : ℕ) (c : ℝ) : Prop where
  interval : ∃ r : ℝ, PositiveReturnInterval c p r
  return_pos : 0 < criticalValue c p
  second_neg : criticalValue c (2*p) < 0
  third_neg : criticalValue c (3*p) < 0
  fourth_pos : 0 < criticalValue c (4*p)
  fifth_neg : criticalValue c (5*p) < 0
  signed_relation : criticalValue c (6*p)+criticalValue c (3*p)=0

theorem PhysicalSignedTip.canonical_interval {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (h : PhysicalSignedTip p c) : PositiveRestrictiveReturn c p := by
  obtain ⟨r,hr⟩ := h.interval
  exact recognize_canonical_return (by omega : 3 ≤ p) hr h.return_pos h.fourth_pos

/-- Every physical signed root enters the narrow coefficient isolator;
the isolator is not a hypothesis on the global root. -/
theorem PhysicalSignedTip.coefficient_interval {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (h : PhysicalSignedTip p c) : kappa p c ∈ parameterInterval := by
  have hc := h.canonical_interval hp
  have hk := signed_coefficient_chart hp hc h.second_neg h.fourth_pos
  have hcoarse := signed_root_coarse_interval hp hc h.second_neg h.third_neg
    h.fourth_pos h.fifth_neg h.signed_relation
  have herr := signed_root_model_error hp hc ⟨hk.1.le,hk.2.le⟩
    h.third_neg h.signed_relation
  have hsmall : 50000*scale p < 1/1000 := by linarith [scale_small hp]
  have hnarrow := modelFactor_near_two_implies_narrow hcoarse (herr.trans_lt hsmall)
  exact ⟨hnarrow.1.le,hnarrow.2.le⟩

/-- Global uniqueness over every real parameter and every physical
interval radius with the specified primitive-return itinerary. -/
theorem physical_signed_tip_unique {p : ℕ} (hp : 17 ≤ p) {c a : ℝ}
    (hc : PhysicalSignedTip p c) (ha : PhysicalSignedTip p a) : c=a :=
  physical_signed_collision_unique hp (hc.canonical_interval hp)
    (ha.canonical_interval hp) (hc.coefficient_interval hp)
    (ha.coefficient_interval hp) hc.signed_relation ha.signed_relation

private theorem actual_tip_signs {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    criticalValue c (2*p)<0 ∧ 0<criticalValue c (4*p) ∧
      criticalValue c (5*p)<0 := by
  have h := actual_tip_restrictive_return hp hc
  let x₂ := realReturn c p 1
  let x₃ := realReturn c p x₂
  let x₄ := realReturn c p x₃
  let x₅ := realReturn c p x₄
  have htwo : x₂ ∈ Icc (-1 : ℝ) 1 := realReturn_mapsTo h (by norm_num)
  have hthree : x₃ ∈ Icc (-1 : ℝ) 1 := realReturn_mapsTo h htwo
  have hfour : x₄ ∈ Icc (-1 : ℝ) 1 := realReturn_mapsTo h hthree
  have he₂ := abs_le.mp (realReturn_error hp h (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num))
  have he₃ := abs_le.mp (realReturn_error hp h htwo)
  have he₄ := abs_le.mp (realReturn_error hp h hthree)
  have he₅ := abs_le.mp (realReturn_error hp h hfour)
  change -(22*scale p) ≤ x₂-(1-kappa p c*1^2) ∧
    x₂-(1-kappa p c*1^2) ≤ 22*scale p at he₂
  change -(22*scale p) ≤ x₃-(1-kappa p c*x₂^2) ∧
    x₃-(1-kappa p c*x₂^2) ≤ 22*scale p at he₃
  change -(22*scale p) ≤ x₄-(1-kappa p c*x₃^2) ∧
    x₄-(1-kappa p c*x₃^2) ≤ 22*scale p at he₄
  change -(22*scale p) ≤ x₅-(1-kappa p c*x₄^2) ∧
    x₅-(1-kappa p c*x₄^2) ≤ 22*scale p at he₅
  have hk := hc.2.2.2.1
  have hklo : (179/100 : ℝ) ≤ kappa p c := by linarith [hk.1]
  have hkhi : kappa p c ≤ (9/5 : ℝ) := by linarith [hk.2]
  have hkpos : 0 ≤ kappa p c := by linarith
  have hε : 22*scale p ≤ 1/100000000 := by linarith [scale_small hp]
  have hx₂ : x₂ ∈ Icc (-4/5 : ℝ) (-39/50) := by
    constructor <;> nlinarith only [he₂.1,he₂.2,hklo,hkhi,hε,hk.1,hk.2]
  have hx₂sqlo : (39/50 : ℝ)^2 ≤ x₂^2 := by
    simpa only [neg_sq] using pow_le_pow_left₀
      (by norm_num : (0 : ℝ) ≤ 39/50) (show (39/50 : ℝ) ≤ -x₂ by linarith [hx₂.2]) 2
  have hx₂sqhi : x₂^2 ≤ (4/5 : ℝ)^2 :=
    sq_le_sq' (by linarith [hx₂.1]) (by linarith [hx₂.2])
  have hm₂lo := mul_le_mul hklo hx₂sqlo (by positivity : (0 : ℝ) ≤ (39/50)^2) hkpos
  have hm₂hi := mul_le_mul hkhi hx₂sqhi (sq_nonneg x₂) (by norm_num : (0 : ℝ) ≤ 9/5)
  have hx₃ : x₃ ∈ Icc (-4/25 : ℝ) (-2/25) := by
    constructor <;> nlinarith only [he₃.1,he₃.2,hm₂lo,hm₂hi,hε]
  have hx₃sq : x₃^2 ≤ (4/25 : ℝ)^2 :=
    sq_le_sq' (by linarith [hx₃.1]) (by linarith [hx₃.2])
  have hm₃ := mul_le_mul hkhi hx₃sq (sq_nonneg x₃) (by norm_num : (0 : ℝ) ≤ 9/5)
  have hx₄ : (19/20 : ℝ) ≤ x₄ := by nlinarith only [he₄.1,hm₃,hε]
  have hx₄sq : (19/20 : ℝ)^2 ≤ x₄^2 :=
    pow_le_pow_left₀ (by norm_num) hx₄ 2
  have hm₄ := mul_le_mul hklo hx₄sq (by positivity : (0 : ℝ) ≤ (19/20)^2) hkpos
  have hx₅ : x₅<0 := by nlinarith only [he₅.2,hm₄,hε]
  have h₂eq : x₂=criticalValue c (2*p)/criticalValue c p := by
    have hi := realReturn_iterate_zero h.return_pos.ne' 2
    change realReturn c p (realReturn c p 0)=_ at hi
    rw [realReturn_zero h.return_pos.ne'] at hi
    exact hi
  have h₄eq : x₄=criticalValue c (4*p)/criticalValue c p := by
    have hi := realReturn_iterate_zero h.return_pos.ne' 4
    change realReturn c p (realReturn c p (realReturn c p (realReturn c p 0)))=_ at hi
    rw [realReturn_zero h.return_pos.ne'] at hi
    exact hi
  have h₅eq : x₅=criticalValue c (5*p)/criticalValue c p := by
    have hi := realReturn_iterate_zero h.return_pos.ne' 5
    change realReturn c p (realReturn c p (realReturn c p
      (realReturn c p (realReturn c p 0))))=_ at hi
    rw [realReturn_zero h.return_pos.ne'] at hi
    exact hi
  have hn₂ : criticalValue c (2*p)/criticalValue c p < 0 := by
    rw [← h₂eq]
    linarith [hx₂.2]
  have hp₄ : 0 < criticalValue c (4*p)/criticalValue c p := by
    rw [← h₄eq]
    linarith only [hx₄]
  have hn₅ : criticalValue c (5*p)/criticalValue c p < 0 := by rwa [← h₅eq]
  refine ⟨?_,?_,?_⟩
  · simpa only [zero_mul] using (div_lt_iff₀ h.return_pos).mp hn₂
  · simpa only [zero_mul] using (lt_div_iff₀ h.return_pos).mp hp₄
  · simpa only [zero_mul] using (div_lt_iff₀ h.return_pos).mp hn₅

/-- Existing actual tips witness the unrestricted physical predicate. -/
theorem actual_tip_physical {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : PhysicalSignedTip p c := by
  have h := actual_tip_restrictive_return hp hc
  obtain ⟨h₂,h₄,h₅⟩ := actual_tip_signs hp hc
  refine ⟨⟨criticalValue c p,?_⟩,hc.2.1,h₂,hc.2.2.2.2.2.1,h₄,h₅,hc.2.2.2.2.1⟩
  exact ⟨h.return_pos,h.negative_first,h.positive_phases,h.invariant⟩

/-- Every period from seventeen onward has exactly one signed tip in
the whole physical interval class, over all real parameters. -/
theorem exists_unique_physical_signed_tip (p : ℕ) (hp : 17 ≤ p) :
    ∃! c : ℝ, PhysicalSignedTip p c := by
  obtain ⟨c,hc⟩ := exists_actual_tip p hp
  exact ⟨c,actual_tip_physical hp hc,
    fun a ha => physical_signed_tip_unique hp ha (actual_tip_physical hp hc)⟩

/-- The global physical predicate is equivalent to the archived
quantitative actual-tip predicate, once the period is at least seventeen. -/
theorem physical_signed_tip_iff_actual_tip {p : ℕ} (hp : 17 ≤ p) {c : ℝ} :
    PhysicalSignedTip p c ↔ ActualTip p c := by
  constructor
  · intro hc
    obtain ⟨a,ha⟩ := exists_actual_tip p hp
    have heq := physical_signed_tip_unique hp hc (actual_tip_physical hp ha)
    rwa [heq]
  · exact actual_tip_physical hp

end
end GlobalPrimitiveTipUniqueness
