import ActualChildMarks
import ActualChildSource
import ChildSlitLimit
import ChildSlitFinite
import ChildSlitScaling

/-!
# The complete independent child optimum on actual quadratic sources

The domain is the exact central component of the physical p-return
pullback of the disk of radius 2⁻ᵖ. The six cuts are literal critical
iterates and a proved positive fixed point of that same return.
The result concerns the supremum over every geometric Borel same-bank
Wave, with relative homotopies contained in the actual source domain.
The physical and normalized suprema are proved equal by dilation.
-/

namespace ActualChildSupremum

open Set Filter Metric
open MarkedSlitTransport SlitWaveModulus ChildSlitModel ChildSlitTransport
open ChildSlitLimit ActualChildMarks ActualChildSource
open NearTwoTip NearTwoShooting LoopsLimitingCrestParameter
open LimitingCrestQuadraticReturn
open scoped Topology ENNReal

noncomputable section

def markingOfCuts (a : Fin 6 → ℝ) (ha : StrictMono a) : ChildMarking where
  left := a 0
  firstLo := a 1
  firstHi := a 2
  secondLo := a 3
  secondHi := a 4
  right := a 5
  left_lt_firstLo := ha (by decide : (0 : Fin 6) < 1)
  firstLo_lt_firstHi := ha (by decide : (1 : Fin 6) < 2)
  firstHi_lt_secondLo := ha (by decide : (2 : Fin 6) < 3)
  secondLo_lt_secondHi := ha (by decide : (3 : Fin 6) < 4)
  secondHi_lt_right := ha (by decide : (4 : Fin 6) < 5)

theorem markCoords_markingOfCuts (a : Fin 6 → ℝ) (ha : StrictMono a) (i : Fin 6) :
    markCoords (markingOfCuts a ha) i = a i := by
  fin_cases i <;> rfl

def limitMarking (k : ℝ) (hk : k ∈ parameterInterval) : ChildMarking :=
  markingOfCuts (limitChildCuts k) (limitChildCuts_strictMono hk)

def actualMarking {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) : ChildMarking :=
  markingOfCuts (actualChildCuts c p) (actualChildCuts_strictMono hp hc hk hroot)

/-- The complete independent upper-child optimum in the normalized
literal source component. -/
def actualChildWidth {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) : ℝ≥0∞ :=
  width (actualMarking hp hc hk hroot) (normalizedSource c p)

def limitingChildWidth (k : ℝ) (hk : k ∈ parameterInterval) : ℝ≥0∞ :=
  width (limitMarking k hk) univ

/-- Both the complete source-domain exhaustion and all six mark limits
are discharged for the actual polynomial family. No domain convergence,
family transport, or existence of an optimizer is assumed. -/
theorem actual_child_optimum_converges {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => actualChildWidth (by omega : 17 ≤ n+17) (hc n) hk hroot)
      atTop (𝓝 (limitingChildWidth k hk)) := by
  apply width_tendsto_of_source_exhaustion (limitMarking k hk)
    (fun n => actualMarking (by omega : 17 ≤ n+17) (hc n) hk hroot)
    (fun n => innerRadius (c n) (n+17))
    (fun n => normalizedSource (c n) (n+17)) (r := 1/100) (by norm_num)
  · intro i j hij
    simp only [limitMarking,markCoords_markingOfCuts]
    exact (by norm_num : (1/100 : ℝ) ≤ 1/50).trans
      (limitChildCuts_separated hk hij).le
  · intro i
    simpa only [actualMarking,limitMarking,markCoords_markingOfCuts] using
      actualChildCuts_tendsto hk hroot c hc i
  · exact innerRadius_tendsto c hc
  · intro n
    exact ball_subset_closedBall.trans
      (closedBall_subset_normalizedSource (by omega) (hc n))

theorem actualChildWidth_ne_top {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    actualChildWidth hp hc hk hroot ≠ ⊤ := ChildSlitFinite.width_ne_top _ _

theorem limitingChildWidth_ne_top (k : ℝ) (hk : k ∈ parameterInterval) :
    limitingChildWidth k hk ≠ ⊤ := ChildSlitFinite.width_ne_top _ _

theorem actual_child_optimum_real_converges {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => (actualChildWidth (by omega : 17 ≤ n+17) (hc n) hk hroot).toReal)
      atTop (𝓝 (limitingChildWidth k hk).toReal) :=
  (ENNReal.tendsto_toReal (limitingChildWidth_ne_top k hk)).comp
    (actual_child_optimum_converges hk hroot c hc)

def physicalMarking {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) : ChildMarking :=
  markingOfCuts (physicalChildCuts c p) (physicalChildCuts_strictMono hp hc hk hroot)

/-- The physical optimum uses the original source component and the
original critical-orbit and fixed-point electrode endpoints. -/
def physicalChildWidth {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) : ℝ≥0∞ :=
  width (physicalMarking hp hc hk hroot) (TwoLevelOuterDomain.source c p)

theorem actualMarking_scale {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    (actualMarking hp hc hk hroot).map
      (OrderIso.mulLeft₀ (criticalValue c p) hc.2.1) = physicalMarking hp hc hk hroot := by
  apply marking_ext
  · exact physicalChildCuts_scale hc.2.1.ne' 0
  · exact physicalChildCuts_scale hc.2.1.ne' 1
  · exact physicalChildCuts_scale hc.2.1.ne' 2
  · exact physicalChildCuts_scale hc.2.1.ne' 3
  · exact physicalChildCuts_scale hc.2.1.ne' 4
  · exact physicalChildCuts_scale hc.2.1.ne' 5

/-- Exact equality of full physical and normalized optima; the maps
transport every leaf and its source-contained relative homotopy. -/
theorem physicalChildWidth_eq_actual {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    physicalChildWidth hp hc hk hroot = actualChildWidth hp hc hk hroot := by
  have hscale := ChildSlitScaling.width_dilation (actualMarking hp hc hk hroot)
    (normalizedSource c p) (criticalValue c p) hc.2.1
  have hsource : SlitWaveScaling.dilation (criticalValue c p) hc.2.1 ''
      normalizedSource c p = TwoLevelOuterDomain.source c p := by
    simpa only [SlitWaveScaling.dilation_apply,Complex.real_smul] using
      scaled_normalizedSource hc
  rw [actualMarking_scale,hsource] at hscale
  exact hscale

theorem physicalChildWidth_ne_top {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    physicalChildWidth hp hc hk hroot ≠ ⊤ := ChildSlitFinite.width_ne_top _ _

/-- Convergence of finite real independent child optima on the literal
unscaled quadratic source domains. -/
theorem physical_child_optimum_real_converges {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => (physicalChildWidth (by omega : 17 ≤ n+17) (hc n) hk hroot).toReal)
      atTop (𝓝 (limitingChildWidth k hk).toReal) := by
  simpa only [physicalChildWidth_eq_actual] using
    actual_child_optimum_real_converges hk hroot c hc

/-- Parameter existence, finiteness, and the physical child limit are
constructed together. The final statement has no assumed quadratic family. -/
theorem exists_physical_child_optima_converging :
    ∃ (k : ℝ) (hk : k ∈ parameterInterval) (hroot : relation k = 0),
      ∃ (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)),
        (∀ n, physicalChildWidth (by omega : 17 ≤ n+17) (hc n) hk hroot ≠ ⊤) ∧
        limitingChildWidth k hk ≠ ⊤ ∧
        Tendsto (fun n => (physicalChildWidth (by omega : 17 ≤ n+17) (hc n) hk hroot).toReal)
          atTop (𝓝 (limitingChildWidth k hk).toReal) := by
  classical
  obtain ⟨k,⟨hk,hroot⟩,_⟩ := exists_unique_limiting_parameter
  choose c hc using fun n : ℕ => exists_actual_tip (n+17) (by omega)
  exact ⟨k,hk,hroot,c,hc,
    (fun n => physicalChildWidth_ne_top (by omega) (hc n) hk hroot),
    limitingChildWidth_ne_top k hk,physical_child_optimum_real_converges hk hroot c hc⟩

end
end ActualChildSupremum
