import DepthGateBase
import DepthGateAncestors
import DepthGateRealization

/-!
# Unconditional physical return towers of every finite depth

The base is an actual sharp quadratic parameter corridor. Each step
constructs a new outer chart and proves preservation of all finite disk
estimates. Only then is one parameter selected and every physical
component realized. The terminal gate constants are independent of depth.
-/

namespace DepthGate

open Set
open NearTwoShooting TwoLevelOuterChart

noncomputable section

/-- A fully initialized numerical chart with any prescribed finite
number of distinct nonterminal ancestors. All estimates in the output
are conclusions of the base-and-prefix induction. -/
theorem exists_tower_chart (depth : ℕ) :
    ∃ C : TerminalChart, Nonempty (Ancestors C depth) := by
  induction depth with
  | zero =>
    obtain ⟨C⟩ := exists_initial_chart
    exact ⟨C,⟨Ancestors.empty C⟩⟩
  | succ depth ih =>
    obtain ⟨C,⟨A⟩⟩ := ih
    obtain ⟨p,_,hp⟩ := C.exists_admissible_prefix 17
    have hl := C.parameter_band (left_mem_Icc.mpr C.ordered.le)
    have hr := C.parameter_band (right_mem_Icc.mpr C.ordered.le)
    obtain ⟨L,U,j⟩ := exists_outer_chart p hp.1 C.left C.right hl.1 C.ordered hr.2
    exact ⟨C.prefix p hp j,⟨A.prefix p hp j⟩⟩

/-- For every depth there is one real quadratic with depth+1 distinct
nested complete physical proper two-sheeted first-return restrictions.
Every positive earlier original iterate is excluded. The terminal
source contains the same relative closed round gate at every depth. -/
theorem exists_physical_tower (depth : ℕ) : Nonempty (PhysicalTower depth) := by
  obtain ⟨C,⟨A⟩⟩ := exists_tower_chart depth
  obtain ⟨c,hc,hrelation⟩ := C.select_parameter
  exact ⟨{
    chart := C
    ancestors := A
    parameter := c
    realization := realization_of_chart C A hc hrelation }⟩

end
end DepthGate
