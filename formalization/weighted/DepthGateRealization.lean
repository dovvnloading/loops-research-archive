import DepthGateChart

/-!
# Physical realization of the numerical tower invariant

Every restriction is the component containing zero of a complete
polynomial pullback. The numerical estimates imply degree, properness,
first return, nested complete targets, and whole-source phase nesting.
-/

namespace DepthGate

open Set Function Metric
open LimitingCrestQuadraticReturn LimitingCrest NearTwoShooting
open TwoLevelOuterChart TwoLevelConjugacy ThreeReturnParent TwoLevelPhysicalGate

noncomputable section

private theorem quadratic_signed_collision (c : ℝ) (z w : ℂ) :
    quadraticMap c z = quadraticMap c w ↔ z = w ∨ z = -w := by
  constructor
  · intro h
    have hs : z^2 = w^2 := add_right_cancel h
    have hf : (z-w)*(z+w) = 0 := by
      calc
        _ = z^2-w^2 := by ring
        _ = 0 := sub_eq_zero.mpr hs
    rcases mul_eq_zero.mp hf with he | he
    · exact Or.inl (sub_eq_zero.mp he)
    · exact Or.inr (eq_neg_of_add_eq_zero_left he)
  · rintro (he | he)
    · rw [he]
    · simp only [he, quadraticMap, neg_sq]

theorem TerminalChart.scale_ne (C : TerminalChart) {c : ℝ}
    (hc : c ∈ Icc C.left C.right) : criticalValue c C.period ≠ 0 :=
  abs_pos.mp (C.margin_pos.trans_le (C.scale_bounds c hc).1)

theorem TerminalChart.collision (C : TerminalChart) {c : ℝ}
    (hc : c ∈ Icc C.left C.right) {z w : ℂ}
    (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    normalizedReturn c C.period z = normalizedReturn c C.period w ↔ z = w ∨ z = -w := by
  have hperiod := C.period_ge
  have hzR : ‖z‖ ≤ C.radius := hz.trans C.radius_lower.le
  have hwR : ‖w‖ ≤ C.radius := hw.trans C.radius_lower.le
  have hdC : (criticalValue c C.period : ℂ) ≠ 0 := by exact_mod_cast C.scale_ne hc
  have hraw := ThreeLevelPerturbation.iterate_signed_collision
    (quadraticMap c) c C.period (by omega) 0 C.margin (by norm_num)
    (by simp) (by simpa using C.margin_pos)
    (by intro v hv; simp)
    (fun {u v} _ _ => quadratic_signed_collision c u v)
    (fun n hn => C.orbit_bound c hc hzR n hn)
    (fun n hn => C.orbit_bound c hc hwR n hn)
    (fun n hn hnp => C.pair_bound c hc hzR hwR n hn hnp)
  unfold normalizedReturn
  rw [div_left_inj' hdC, hraw]
  constructor
  · rintro (he | he)
    · exact Or.inl (mul_left_cancel₀ hdC he)
    · exact Or.inr (mul_left_cancel₀ hdC (by simpa only [mul_neg] using he))
  · rintro (he | he)
    · exact Or.inl (congrArg (fun u : ℂ => (criticalValue c C.period : ℂ)*u) he)
    · exact Or.inr (by rw [he,mul_neg])

theorem TerminalChart.centralGate (C : TerminalChart) {c : ℝ}
    (hc : c ∈ Icc C.left C.right) : TwoLevelGateDomain.CentralGate c C.period := by
  have hn := C.period_ge
  apply TwoLevelGateDomain.central_gate_of_estimates c C.period (by omega)
    (C.scale_ne hc) (C.coefficient_band c hc)
  · intro z hz
    exact (C.normalized_error c hc z hz).trans (by linarith [C.slack_pos])
  · exact fun hz hw => C.collision hc hz hw

theorem TerminalChart.physicalGate (C : TerminalChart) {c : ℝ}
    (hc : c ∈ Icc C.left C.right) : PhysicalGate c C.period :=
  physical_gate_of_central (C.centralGate hc)

theorem TerminalChart.firstReturn (C : TerminalChart) {c : ℝ}
    (hc : c ∈ Icc C.left C.right) (n : ℕ) (hn : 1 ≤ n) (hnN : n < C.period) :
    Disjoint (((quadraticMap c)^[n]) '' physicalParentSource c C.period)
      (physicalTarget c C.period) := by
  have hgate := C.centralGate hc
  apply Set.disjoint_left.mpr
  rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩ hy
  have hzR : ‖z‖ ≤ C.radius := by
    have hh : ‖z‖ < 23/20 := by simpa using hgate.closure_inside (subset_closure hz)
    exact hh.le.trans C.radius_lower.le
  have hlo := C.first_bound c hc hzR n hn hnN
  have hy' : ‖((quadraticMap c)^[n]) ((criticalValue c C.period : ℂ)*z)‖ <
      |criticalValue c C.period| *(23/20) := by simpa [physicalTarget] using hy
  linarith [C.margin_pos]

theorem TerminalChart.select_parameter (C : TerminalChart) :
    ∃ c ∈ Icc C.left C.right,
      criticalValue c (6*C.period)+criticalValue c (3*C.period) = 0 := by
  let P : ℝ → ℝ := fun c =>
    C.orientation*(criticalValue c (6*C.period)+criticalValue c (3*C.period))
  have hP : Continuous P := continuous_const.mul
    ((continuous_criticalValue (6*C.period)).add (continuous_criticalValue (3*C.period)))
  have hleft : P C.left ≤ 0 := by
    dsimp [P]
    linarith [C.relation_left, C.margin_pos]
  have hright : 0 ≤ P C.right := by
    dsimp [P]
    linarith [C.relation_right, C.margin_pos]
  obtain ⟨c,hc,hzero⟩ := intermediate_value_Icc C.ordered.le hP.continuousOn
    (show (0 : ℝ) ∈ Icc (P C.left) (P C.right) from ⟨hleft,hright⟩)
  have ho : C.orientation ≠ 0 := by
    rcases C.orientation_unit with he | he <;> rw [he] <;> norm_num
  exact ⟨c,hc,(mul_eq_zero.mp hzero).resolve_left ho⟩

def Ancestors.source {C : TerminalChart} {depth : ℕ} (A : Ancestors C depth)
    (c : ℝ) (i : Fin depth) : Set ℂ :=
  ThreeLevelDomains.source c (A.period i) (A.target i c)

theorem Ancestors.restriction {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {c : ℝ} (hc : c ∈ Icc C.left C.right) (i : Fin depth) :
    ThreeLevelDomains.Restriction c (A.period i) (A.target i c) (A.barrier i c) := by
  have hn := A.period_ge i
  have hr := A.radii i c hc
  apply ThreeLevelDomains.restriction_of_estimates c (A.period i)
    (A.target i c) (A.barrier i c) (by omega)
    (by linarith [C.margin_pos]) (by linarith [C.margin_pos])
  · linarith [A.critical_inside i c hc, C.margin_pos]
  · intro z hz
    linarith [A.circle_escape i c hc z hz, C.margin_pos]
  · intro z w hz hw
    exact ThreeLevelPerturbation.iterate_signed_collision
      (quadraticMap c) c (A.period i) (by omega) 0 C.margin (by norm_num)
      (by simp) (by simpa using C.margin_pos)
      (by intro v hv; simp)
      (fun {u v} _ _ => quadratic_signed_collision c u v)
      (fun n hn => A.orbit_bound i c hc hz n hn)
      (fun n hn => A.orbit_bound i c hc hw n hn)
      (fun n hn hnP => A.pair_bound i c hc hz hw n hn hnP)

theorem Ancestors.core_subset_source {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {c : ℝ} (hc : c ∈ Icc C.left C.right) (i : Fin depth) :
    closedBall (0 : ℂ) (A.core i c) ⊆ A.source c i := by
  apply ThreeLevelDomains.disk_in_source c (A.period i) (A.target i c) (A.core i c)
    (C.margin_pos.le.trans (A.radii i c hc).1)
  intro z hz
  linarith [A.core_inside i c hc hz, C.margin_pos]

theorem Ancestors.firstReturn {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {c : ℝ} (hc : c ∈ Icc C.left C.right)
    (i : Fin depth) (n : ℕ) (hn : 1 ≤ n) (hnP : n < A.period i) :
    Disjoint (((quadraticMap c)^[n]) '' A.source c i) (ball 0 (A.target i c)) := by
  have hr := A.restriction hc i
  apply Set.disjoint_left.mpr
  rintro _ ⟨z,hz,rfl⟩ hy
  have hzR : ‖z‖ ≤ A.barrier i c :=
    (show ‖z‖ < A.barrier i c by simpa using hr.closure_inside (subset_closure hz)).le
  have hlo := A.first_bound i c hc hzR n hn hnP
  have hy' : ‖((quadraticMap c)^[n]) z‖ < A.target i c := by simpa using hy
  linarith [C.margin_pos]

theorem Ancestors.targets_nested {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {c : ℝ} (hc : c ∈ Icc C.left C.right)
    (i j : Fin depth) (hij : i.val < j.val) :
    ball (0 : ℂ) (A.target j c) ⊆ A.source c i := by
  intro z hz
  apply A.core_subset_source hc i
  rw [mem_closedBall_zero_iff]
  have hz' : ‖z‖ < A.target j c := by simpa using hz
  linarith [A.target_nesting i j hij c hc, C.margin_pos]

theorem Ancestors.phases_nested {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {c : ℝ} (hc : c ∈ Icc C.left C.right)
    (i j : Fin depth) (hij : i.val < j.val) (m : ℕ) (hm : m*A.period i ≤ A.period j) :
    ((quadraticMap c)^[m*A.period i]) '' A.source c j ⊆ A.source c i := by
  have hr := A.restriction hc j
  rintro _ ⟨z,hz,rfl⟩
  have hzR : ‖z‖ ≤ A.barrier j c :=
    (show ‖z‖ < A.barrier j c by simpa using hr.closure_inside (subset_closure hz)).le
  apply A.core_subset_source hc i
  rw [mem_closedBall_zero_iff]
  have hb := A.nesting i j hij c hc hzR m hm
  linarith [C.margin_pos]

theorem Ancestors.terminal_target_inside {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {c : ℝ} (hc : c ∈ Icc C.left C.right) (i : Fin depth) :
    physicalTarget c C.period ⊆ A.source c i := by
  have hz : ‖(23/20 : ℂ)‖ ≤ C.radius := by
    norm_num
    exact C.radius_lower.le
  have hb := A.terminal_nesting i c hc hz 0 (by simp)
  simp only [zero_mul, Function.iterate_zero, id_eq, norm_mul, Complex.norm_real,
    Real.norm_eq_abs] at hb
  norm_num at hb
  intro z hz'
  apply A.core_subset_source hc i
  rw [mem_closedBall_zero_iff]
  have hnorm : ‖z‖ < |criticalValue c C.period| *(23/20) := by
    simpa [physicalTarget] using hz'
  linarith [C.margin_pos]

theorem Ancestors.terminal_phases_nested {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {c : ℝ} (hc : c ∈ Icc C.left C.right)
    (i : Fin depth) (m : ℕ) (hm : m*A.period i ≤ C.period) :
    ((quadraticMap c)^[m*A.period i]) '' physicalParentSource c C.period ⊆ A.source c i := by
  have hgate := C.centralGate hc
  rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩
  have hzR : ‖z‖ ≤ C.radius := by
    have hh : ‖z‖ < 23/20 := by simpa using hgate.closure_inside (subset_closure hz)
    exact hh.le.trans C.radius_lower.le
  apply A.core_subset_source hc i
  rw [mem_closedBall_zero_iff]
  have hb := A.terminal_nesting i c hc hzR m hm
  linarith [C.margin_pos]

structure Realization (C : TerminalChart) {depth : ℕ} (A : Ancestors C depth) (c : ℝ) : Prop where
  parameter_mem : c ∈ Icc C.left C.right
  critical_relation : criticalValue c (6*C.period)+criticalValue c (3*C.period) = 0
  terminal_gate : PhysicalGate c C.period
  terminal_first : ∀ n : ℕ, 1 ≤ n → n < C.period →
    Disjoint (((quadraticMap c)^[n]) '' physicalParentSource c C.period) (physicalTarget c C.period)
  ancestors : ∀ i : Fin depth,
    ThreeLevelDomains.Restriction c (A.period i) (A.target i c) (A.target i c/2)
  ancestor_first : ∀ i : Fin depth, ∀ n : ℕ, 1 ≤ n → n < A.period i →
    Disjoint (((quadraticMap c)^[n]) '' A.source c i) (ball 0 (A.target i c))
  targets_nested : ∀ i j : Fin depth, i.val < j.val →
    ball (0 : ℂ) (A.target j c) ⊆ A.source c i
  phases_nested : ∀ i j : Fin depth, i.val < j.val →
    ∀ m : ℕ, m*A.period i ≤ A.period j →
      ((quadraticMap c)^[m*A.period i]) '' A.source c j ⊆ A.source c i
  terminal_target_nested : ∀ i : Fin depth, physicalTarget c C.period ⊆ A.source c i
  terminal_phases_nested : ∀ i : Fin depth, ∀ m : ℕ, m*A.period i ≤ C.period →
    ((quadraticMap c)^[m*A.period i]) '' physicalParentSource c C.period ⊆ A.source c i

theorem realization_of_chart (C : TerminalChart) {depth : ℕ} (A : Ancestors C depth)
    {c : ℝ} (hc : c ∈ Icc C.left C.right)
    (hrel : criticalValue c (6*C.period)+criticalValue c (3*C.period) = 0) :
    Realization C A c := by
  refine ⟨hc,hrel,C.physicalGate hc,C.firstReturn hc,?_,A.firstReturn hc,
    A.targets_nested hc,A.phases_nested hc,A.terminal_target_inside hc,
    A.terminal_phases_nested hc⟩
  intro i
  simpa only [A.barrier_eq_half] using A.restriction hc i

/-- The index counts nonterminal ancestors, so this object has
depth+1 distinct physical first-return levels. -/
structure PhysicalTower (depth : ℕ) where
  chart : TerminalChart
  ancestors : Ancestors chart depth
  parameter : ℝ
  realization : Realization chart ancestors parameter

end
end DepthGate
