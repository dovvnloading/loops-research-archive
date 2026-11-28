import ThreeLevelTerminal
import ThreeLevelDomains

/-!
# Numerical chart data for an arbitrary finite physical return tower

The invariant consists only of explicit estimates for complete quadratic
iterates on disks. Proper domains are derived from these estimates later.
The positive radius and error reserves may shrink under prefixing; the
terminal gate constants do not depend on the number of ancestors.
-/

namespace DepthGate

open Set Function Metric
open LimitingCrestQuadraticReturn LimitingCrest NearTwoShooting
open TwoLevelOuterChart TwoLevelConjugacy

noncomputable section

structure TerminalChart where
  period : ℕ
  left : ℝ
  right : ℝ
  margin : ℝ
  buffer : ℝ
  slack : ℝ
  orientation : ℝ
  coefficient : ℝ → ℝ
  period_ge : 17 ≤ period
  ordered : left < right
  parameter_band : Icc left right ⊆ Icc (-2 : ℝ) (-49/25)
  margin_pos : 0 < margin
  margin_le : margin ≤ 1/100
  buffer_pos : 0 < buffer
  buffer_le : buffer ≤ 1/20
  slack_pos : 0 < slack
  slack_le : slack ≤ 1/1000000
  orientation_unit : orientation = 1 ∨ orientation = -1
  coefficient_band : ∀ t ∈ Icc left right,
    coefficient t ∈ Icc (17903/10000 : ℝ) (17904/10000)
  scale_bounds : ∀ t ∈ Icc left right,
    margin ≤ |criticalValue t period| ∧ |criticalValue t period| ≤ 1/100
  orbit_bound : ∀ t ∈ Icc left right, ∀ {z : ℂ},
    ‖z‖ ≤ 23/20+buffer → ∀ n : ℕ, n ≤ period →
      ‖((quadraticMap t)^[n]) ((criticalValue t period : ℂ)*z)‖ ≤ 21/10
  pair_bound : ∀ t ∈ Icc left right, ∀ {z w : ℂ},
    ‖z‖ ≤ 23/20+buffer → ‖w‖ ≤ 23/20+buffer →
    ∀ n : ℕ, 1 ≤ n → n < period →
      margin ≤ ‖((quadraticMap t)^[n]) ((criticalValue t period : ℂ)*z)+
        ((quadraticMap t)^[n]) ((criticalValue t period : ℂ)*w)‖
  first_bound : ∀ t ∈ Icc left right, ∀ {z : ℂ},
    ‖z‖ ≤ 23/20+buffer → ∀ n : ℕ, 1 ≤ n → n < period →
      |criticalValue t period| *(23/20)+margin ≤
        ‖((quadraticMap t)^[n]) ((criticalValue t period : ℂ)*z)‖
  normalized_error : ∀ t ∈ Icc left right, ∀ z : ℂ, ‖z‖ ≤ 23/20 →
    ‖normalizedReturn t period z-complexMap (coefficient t) z‖ ≤ 1/500000-slack
  relation_left : orientation*
    (criticalValue left (6*period)+criticalValue left (3*period)) ≤ -margin
  relation_right : margin ≤ orientation*
    (criticalValue right (6*period)+criticalValue right (3*period))

namespace TerminalChart

def radius (C : TerminalChart) : ℝ := 23/20+C.buffer

/-- One deliberately conservative positive budget pays all finite
analytical and geometric tolerances, including both moving scales. -/
def budget (C : TerminalChart) : ℝ := C.margin*C.buffer*C.slack/10000

def prefixMargin (C : TerminalChart) (p : ℕ) : ℝ := C.margin*scale p/100

def AdmissiblePrefix (C : TerminalChart) (p : ℕ) : Prop :=
  17 ≤ p ∧ 128*scale p*(5 : ℝ)^(6*C.period) ≤ C.budget

theorem radius_lower (C : TerminalChart) : (23/20 : ℝ) < C.radius := by
  unfold radius
  linarith [C.buffer_pos]

theorem radius_upper (C : TerminalChart) : C.radius ≤ 6/5 := by
  unfold radius
  linarith [C.buffer_le]

theorem budget_pos (C : TerminalChart) : 0 < C.budget := by
  exact div_pos (mul_pos (mul_pos C.margin_pos C.buffer_pos) C.slack_pos) (by norm_num)

theorem prefixMargin_pos (C : TerminalChart) (p : ℕ) : 0 < C.prefixMargin p :=
  div_pos (mul_pos C.margin_pos (scale_pos p)) (by norm_num)

end TerminalChart

/-- Nonterminal levels carry uniform disk estimates. The terminal level
uses its own signed critical scale and reserved normalized radius. -/
structure Ancestors (C : TerminalChart) (depth : ℕ) where
  period : Fin depth → ℕ
  target : Fin depth → ℝ → ℝ
  barrier : Fin depth → ℝ → ℝ
  core : Fin depth → ℝ → ℝ
  barrier_eq_half : ∀ i t, barrier i t = target i t/2
  period_ge : ∀ i, 17 ≤ period i
  period_divides : ∀ i, period i ∣ C.period
  period_lt : ∀ i, period i < C.period
  period_order : ∀ i j, i.val < j.val → period i < period j
  radii : ∀ i t, t ∈ Icc C.left C.right →
    C.margin ≤ core i t ∧ core i t+C.margin ≤ barrier i t ∧
      barrier i t+C.margin ≤ target i t ∧ target i t ≤ 1/100
  orbit_bound : ∀ i t, t ∈ Icc C.left C.right → ∀ {z : ℂ},
    ‖z‖ ≤ barrier i t → ∀ n : ℕ, n ≤ period i →
      ‖((quadraticMap t)^[n]) z‖ ≤ 21/10
  critical_inside : ∀ i t, t ∈ Icc C.left C.right →
    ‖((quadraticMap t)^[period i]) 0‖ ≤ target i t-C.margin
  circle_escape : ∀ i t, t ∈ Icc C.left C.right → ∀ z : ℂ,
    ‖z‖ = barrier i t → target i t+C.margin ≤ ‖((quadraticMap t)^[period i]) z‖
  core_inside : ∀ i t, t ∈ Icc C.left C.right → ∀ {z : ℂ},
    ‖z‖ ≤ core i t → ‖((quadraticMap t)^[period i]) z‖ ≤ target i t-C.margin
  pair_bound : ∀ i t, t ∈ Icc C.left C.right → ∀ {z w : ℂ},
    ‖z‖ ≤ barrier i t → ‖w‖ ≤ barrier i t →
    ∀ n : ℕ, 1 ≤ n → n < period i →
      C.margin ≤ ‖((quadraticMap t)^[n]) z+((quadraticMap t)^[n]) w‖
  first_bound : ∀ i t, t ∈ Icc C.left C.right → ∀ {z : ℂ},
    ‖z‖ ≤ barrier i t → ∀ n : ℕ, 1 ≤ n → n < period i →
      target i t+C.margin ≤ ‖((quadraticMap t)^[n]) z‖
  target_nesting : ∀ i j, i.val < j.val → ∀ t, t ∈ Icc C.left C.right →
    target j t+C.margin ≤ core i t
  nesting : ∀ i j, i.val < j.val → ∀ t, t ∈ Icc C.left C.right →
    ∀ {z : ℂ}, ‖z‖ ≤ barrier j t → ∀ m : ℕ, m*period i ≤ period j →
      ‖((quadraticMap t)^[m*period i]) z‖ ≤ core i t-C.margin
  terminal_nesting : ∀ i t, t ∈ Icc C.left C.right →
    ∀ {z : ℂ}, ‖z‖ ≤ C.radius → ∀ m : ℕ, m*period i ≤ C.period →
      ‖((quadraticMap t)^[m*period i]) ((criticalValue t C.period : ℂ)*z)‖ ≤
        core i t-C.margin

end
end DepthGate
