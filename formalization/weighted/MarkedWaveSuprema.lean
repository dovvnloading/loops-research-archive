import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# The passage from metric witnesses to the three independent Wave suprema

Source: tip-family preprint v2, § "Conditional canonical marked widths and
unbuffered defect", equations `eq:width`, `eq:gain` and `eq:gain-cases`.
Instantiate `Leaf` with proper curves in the specified marked slit and
`Density` with nonnegative measurable conformal densities of finite area energy.
An extended line integral may be clipped at 1 before conversion to ℝ: this
preserves its unit-length test, even for infinite length. A finite feasible
metric makes omission of infinite-energy candidates harmless to the infimum.
The geometry must identify the Wave classes, integrals and witnesses. The
results below prove the variational and period arithmetic steps for those
inputs. They require neither existence of maximizers nor reflection symmetry.
-/

namespace LoopsFormal.MarkedWaveSuprema
open Set

/-- Data only. On the marked surface these functions are area energy and
(clipped) line integral along a leaf in the same conformal metric. -/
structure Metrics (Leaf Density : Type*) where
  energy : Density → ℝ
  length : Density → Leaf → ℝ

namespace Metrics
variable {Leaf Density : Type*} (m : Metrics Leaf Density)

/-- The constraint in eq:width ranges over every leaf. -/
def admissible (Γ : Set Leaf) (ρ : Density) : Prop :=
  ∀ γ ∈ Γ, 1 ≤ m.length ρ γ

noncomputable def width (Γ : Set Leaf) : ℝ :=
  sInf (m.energy '' {ρ | m.admissible Γ ρ})

noncomputable def optimum (waves : Set (Set Leaf)) : ℝ :=
  sSup (m.width '' waves)

/-- One metric gives an upper bound only after it passes the test on all
leaves. Nonnegative energy provides the lower bound needed for a real infimum. -/
theorem width_le_energy (henergy : ∀ ρ, 0 ≤ m.energy ρ) {Γ : Set Leaf}
    {ρ : Density} (hρ : m.admissible Γ ρ) : m.width Γ ≤ m.energy ρ :=
  csInf_le ⟨0, fun _ ⟨σ, _, h⟩ => h ▸ henergy σ⟩ ⟨ρ, hρ, rfl⟩

/-- The lower estimate for one embedded parent foliation must hold for
every feasible metric, and at least one such metric must exist. -/
theorem le_width {Γ : Set Leaf} {L : ℝ} (hfeasible : ∃ ρ, m.admissible Γ ρ)
    (hbound : ∀ ρ, m.admissible Γ ρ → L ≤ m.energy ρ) : L ≤ m.width Γ := by
  obtain ⟨ρ, hρ⟩ := hfeasible
  exact le_csInf ⟨_, ρ, hρ, rfl⟩ fun _ ⟨σ, hσ, h⟩ => h ▸ hbound σ hσ

/-- Quantifiers for a child upper bound. Each physical Wave gets a metric
valid for all of its leaves. A positive witness bounds its supremum away
from zero. The maximizing Wave need not exist. -/
theorem optimum_positive_le {waves : Set (Set Leaf)} {U : ℝ}
    (henergy : ∀ ρ, 0 ≤ m.energy ρ)
    (hwitness : ∃ Γ ∈ waves, 0 < m.width Γ)
    (hmetrics : ∀ Γ ∈ waves, ∃ ρ, m.admissible Γ ρ ∧ m.energy ρ ≤ U) :
    0 < m.optimum waves ∧ m.optimum waves ≤ U := by
  obtain ⟨Γ, hΓ, hpos⟩ := hwitness
  have hupper : U ∈ upperBounds (m.width '' waves) := by
    rintro _ ⟨Λ, hΛ, rfl⟩
    obtain ⟨ρ, hρ, hU⟩ := hmetrics Λ hΛ
    exact (m.width_le_energy henergy hρ).trans hU
  have hmem : m.width Γ ∈ m.width '' waves := ⟨Γ, hΓ, rfl⟩
  exact ⟨hpos.trans_le (le_csSup ⟨U, hupper⟩ hmem), csSup_le ⟨_, hmem⟩ hupper⟩

end Metrics

/-- Lower parent / upper child width in the four ranges of eq:gain-cases.
The p ≥ 13 parent floor uses the corrected 2026-11-23 coordinate-error
certificate; its reciprocal margin is 40/819. -/
noncomputable def bounds (p : ℕ) : ℝ × ℝ :=
  if p = 3 then (49 / 100, 487 / 500)
  else if p = 4 then (511 / 1000, 197 / 200)
  else if p ≤ 12 then (581 / 1000, 247 / 250)
  else (13 / 20, 63 / 50)

/-- A separate rational calculation, valid also when p passes from 12 to 13. -/
theorem period_margin (p : ℕ) (_hp : 3 ≤ p) :
    0 < (bounds p).1 ∧ 0 < (bounds p).2 ∧
    1 / 100 < 1 / (bounds p).2 + 1 / (bounds p).2 - 1 / (bounds p).1 := by
  unfold bounds
  by_cases h3 : p = 3
  · norm_num [h3]
  by_cases h4 : p = 4
  · norm_num [h3, h4]
  by_cases h12 : p ≤ 12 <;> norm_num [h3, h4, h12]

/-- Eq:gain after making the geometric inputs individually visible.
The parent witness must belong to the full marked parent class. Child
inputs are quantified separately over both full marked classes. The
finite parent envelope is needed for the real supremum. -/
theorem gain_of_marked_metric_witnesses
    {L₁ D₁ L₂ D₂ : Type*} (parent : Metrics L₁ D₁) (child : Metrics L₂ D₂)
    (p : ℕ) (hp : 3 ≤ p) (parents : Set (Set L₁)) (children : Bool → Set (Set L₂))
    (Γ : Set L₁) (hΓ : Γ ∈ parents)
    (hfeasible : ∃ ρ, parent.admissible Γ ρ)
    (hparent : ∀ ρ, parent.admissible Γ ρ → (bounds p).1 ≤ parent.energy ρ)
    (hfinite : BddAbove (parent.width '' parents))
    (hnonneg : ∀ ρ, 0 ≤ child.energy ρ)
    (hpositive : ∀ side, ∃ Λ ∈ children side, 0 < child.width Λ)
    (hchild : ∀ side Λ, Λ ∈ children side →
      ∃ ρ, child.admissible Λ ρ ∧ child.energy ρ ≤ (bounds p).2) :
    1 / 100 < 1 / child.optimum (children true) + 1 / child.optimum (children false) -
      1 / parent.optimum parents := by
  obtain ⟨hL, _, hgap⟩ := period_margin p hp
  have hP : (bounds p).1 ≤ parent.optimum parents :=
    (parent.le_width hfeasible hparent).trans (le_csSup hfinite ⟨Γ, hΓ, rfl⟩)
  have hC (side : Bool) :=
    child.optimum_positive_le hnonneg (hpositive side) (hchild side)
  have hplus := one_div_le_one_div_of_le (hC true).1 (hC true).2
  have hminus := one_div_le_one_div_of_le (hC false).1 (hC false).2
  exact hgap.trans_le (sub_le_sub (add_le_add hplus hminus) (one_div_le_one_div_of_le hL hP))

/-- Testing only the displayed leaf can accept an inadmissible density. -/
theorem one_test_leaf_misses_a_constraint :
    let m : Metrics Bool Unit := ⟨fun _ => 1, fun _ γ => if γ then 0 else 1⟩
    m.admissible {false} () ∧ ¬m.admissible Set.univ () := by
  dsimp [Metrics.admissible]
  simp

#print axioms period_margin
#print axioms gain_of_marked_metric_witnesses
#print axioms one_test_leaf_misses_a_constraint

end LoopsFormal.MarkedWaveSuprema
