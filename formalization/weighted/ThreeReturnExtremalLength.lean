import ThreeReturnInradius
import CollarHorizontalFamily

/-!
# Two-sided extremal length for the actual uniform three-return collars

The actual source contains a closed disk of radius d/40 and has closure
inside the disk of radius 3*d/20, while the target radius is d/6. These
give independent two-sided bounds on Dirichlet capacity and the standard
modulus of all continuous rectifiable joining curves.

No capacity-duality or conformal-uniformization identity is assumed.
The parameter and domains come from the imported all-period realization;
all geometric inclusions below are conclusions for actual polynomials.
-/

namespace ThreeReturnExtremalLength

open Set Metric MeasureTheory
open LimitingCrestQuadraticReturn ThreeReturnDomain ThreeReturnCollar
open ThreeReturnPhysical UniformThreeReturn UniformThreeReturnRenormalization
open ThreeReturnAnnulus CollarExtremalLength
open scoped ENNReal NNReal Topology

noncomputable section

private theorem inner_ratio {d : ℝ} (hd : 0 < d) :
    (d/40)/(d/6) = 3/20 := by
  field_simp [hd.ne'] <;> ring

private theorem outer_ratio {d : ℝ} (hd : 0 < d) :
    (d/6)/(d/40) = 20/3 := by
  field_simp [hd.ne'] <;> ring

/-- The positive-radius disk lies in the actual inner plate. -/
theorem selected_inner_plate_disk {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    ball (0 : ℂ) (criticalValue c p/40) ⊆ closure (physicalSource c p) :=
  ball_subset_closedBall.trans
    ((ThreeReturnInradius.selected_physical_closedBall_subset hp hc).trans subset_closure)

/-- The compact inner plate lies strictly inside the physical target. -/
theorem selected_inner_plate_inside_target {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    closure (physicalSource c p) ⊆ ball 0 (criticalValue c p/6) := by
  have h := selected_canonical_collar hp hc
  exact h.physical_closure_inside.trans (ball_subset_ball (by linarith [h.scale_pos]))

/-- A scale-independent positive lower bound for the existing capacity. -/
theorem selected_capacity_lower {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    ENNReal.ofReal (3/20 : ℝ) ≤
      capacity (closure (physicalSource c p)) (physicalTarget c p) := by
  have hd := (selected_critical_data hp hc).1
  have h := CollarCapacityLower.capacity_lower
    (show 0 < criticalValue c p/40 by positivity)
    (show 0 < criticalValue c p/6 by positivity)
    (selected_inner_plate_disk hp hc)
  rw [inner_ratio hd] at h
  exact h

theorem selected_capacity_bounds {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    ENNReal.ofReal (3/20 : ℝ) ≤
      capacity (closure (physicalSource c p)) (physicalTarget c p) ∧
      capacity (closure (physicalSource c p)) (physicalTarget c p) < 60 :=
  ⟨selected_capacity_lower hp hc, (selected_canonical_collar hp hc).capacity_lt⟩

/-- The previously defined reciprocal variational capacity is finite. -/
theorem selected_variationalModulus_upper {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    variationalModulus (closure (physicalSource c p)) (physicalTarget c p) ≤
      ENNReal.ofReal (20/3 : ℝ) := by
  have hd := (selected_critical_data hp hc).1
  have h := CollarCapacityLower.variationalModulus_le
    (show 0 < criticalValue c p/40 by positivity)
    (show 0 < criticalValue c p/6 by positivity)
    (selected_inner_plate_disk hp hc)
  rw [outer_ratio hd] at h
  exact h

theorem selected_variationalModulus_bounds {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    (60 : ℝ≥0∞)⁻¹ <
      variationalModulus (closure (physicalSource c p)) (physicalTarget c p) ∧
      variationalModulus (closure (physicalSource c p)) (physicalTarget c p) ≤
        ENNReal.ofReal (20/3 : ℝ) :=
  ⟨(selected_canonical_collar hp hc).modulus_gt,
    selected_variationalModulus_upper hp hc⟩

/-- A positive-area family of actual joining segments bounds the modulus
of the full continuous rectifiable family from below. -/
theorem selected_curveModulus_lower {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    ENNReal.ofReal (3/20 : ℝ) ≤
      curveModulus (closure (physicalSource c p)) (criticalValue c p/6) := by
  have hcanonical := selected_canonical_collar hp hc
  have hd := hcanonical.scale_pos
  have h := CollarHorizontalFamily.curveModulus_lower
    (physical_compact_closure hcanonical) (selected_inner_plate_inside_target hp hc)
    (show 0 < criticalValue c p/40 by positivity)
    (show criticalValue c p/40 < criticalValue c p/6 by linarith)
    (selected_inner_plate_disk hp hc)
  rw [inner_ratio hd] at h
  exact h

/-- An explicit density is admissible for every rectifiable joining curve. -/
theorem selected_curveModulus_upper {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    curveModulus (closure (physicalSource c p)) (criticalValue c p/6) ≤
      ENNReal.ofReal (100*Real.pi) := by
  have h := selected_canonical_collar hp hc
  exact physical_curveModulus_le h.scale_pos
    (h.physical_closure_inside.trans ball_subset_closedBall)

theorem selected_curveModulus_bounds {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    ENNReal.ofReal (3/20 : ℝ) ≤
      curveModulus (closure (physicalSource c p)) (criticalValue c p/6) ∧
      curveModulus (closure (physicalSource c p)) (criticalValue c p/6) ≤
        ENNReal.ofReal (100*Real.pi) :=
  ⟨selected_curveModulus_lower hp hc, selected_curveModulus_upper hp hc⟩

/-- A scale-independent finite upper bound on standard extremal length. -/
theorem selected_extremalLength_upper {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    extremalLength (closure (physicalSource c p)) (criticalValue c p/6) ≤
      ENNReal.ofReal (20/3 : ℝ) := by
  have hcanonical := selected_canonical_collar hp hc
  have hd := hcanonical.scale_pos
  have h := CollarHorizontalFamily.extremalLength_le_of_disk_subset
    (physical_compact_closure hcanonical) (selected_inner_plate_inside_target hp hc)
    (show 0 < criticalValue c p/40 by positivity)
    (show criticalValue c p/40 < criticalValue c p/6 by linarith)
    (selected_inner_plate_disk hp hc)
  rw [outer_ratio hd] at h
  exact h

/-- A strictly positive universal lower bound on standard extremal length. -/
theorem selected_extremalLength_lower {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    (ENNReal.ofReal (100*Real.pi))⁻¹ ≤
      extremalLength (closure (physicalSource c p)) (criticalValue c p/6) := by
  have h := selected_canonical_collar hp hc
  exact physical_extremalLength_ge h.scale_pos
    (h.physical_closure_inside.trans ball_subset_closedBall)

/-- Uniform two-sided standard joining-curve extremal length on the
selected actual physical three-return collars. -/
theorem selected_extremalLength_bounds {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    (ENNReal.ofReal (100*Real.pi))⁻¹ ≤
      extremalLength (closure (physicalSource c p)) (criticalValue c p/6) ∧
      extremalLength (closure (physicalSource c p)) (criticalValue c p/6) ≤
        ENNReal.ofReal (20/3 : ℝ) :=
  ⟨selected_extremalLength_lower hp hc, selected_extremalLength_upper hp hc⟩

/-- The standard invariant is neither zero nor infinite. -/
theorem selected_extremalLength_pos_finite {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    0 < extremalLength (closure (physicalSource c p)) (criticalValue c p/6) ∧
      extremalLength (closure (physicalSource c p)) (criticalValue c p/6) < ⊤ := by
  have h := selected_extremalLength_bounds hp hc
  constructor
  · exact lt_of_lt_of_le (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) h.1
  · exact h.2.trans_lt ENNReal.ofReal_lt_top

/-- Every integer period at least three admits the same actual physical
renormalization with the new inradius, positive capacity and two-sided
standard extremal-length bounds. No domain-existence premise is supplied. -/
theorem exists_physical_renormalization_with_extremal_bounds (p : ℕ) (hp : 3 ≤ p) :
    ∃ c : ℝ, SelectedParameter p c ∧ PhysicalRenormalization c p ∧
      closedBall (0 : ℂ) (criticalValue c p/40) ⊆ physicalSource c p ∧
      ENNReal.ofReal (3/20 : ℝ) ≤
        capacity (closure (physicalSource c p)) (physicalTarget c p) ∧
      capacity (closure (physicalSource c p)) (physicalTarget c p) < 60 ∧
      (ENNReal.ofReal (100*Real.pi))⁻¹ ≤
        extremalLength (closure (physicalSource c p)) (criticalValue c p/6) ∧
      extremalLength (closure (physicalSource c p)) (criticalValue c p/6) ≤
        ENNReal.ofReal (20/3 : ℝ) := by
  obtain ⟨c, hc⟩ := exists_selected_parameter p hp
  exact ⟨c, hc, selected_physical_renormalization hp hc,
    ThreeReturnInradius.selected_physical_closedBall_subset hp hc,
    selected_capacity_lower hp hc, (selected_canonical_collar hp hc).capacity_lt,
    selected_extremalLength_lower hp hc, selected_extremalLength_upper hp hc⟩

end
end ThreeReturnExtremalLength

