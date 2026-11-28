import ActualThreeReturnNormalization

/-!
# All-depth cylinders of the literal physical three-return

The itinerary is read from signs of the actual quadratic iterates in the
original dynamical plane.  The canonical interval is the image of the
unit interval under the scale determined by the actual critical orbit.
-/

namespace ActualThreeReturnCylinders

open Set Function
open LimitingCrestQuadraticReturn NearTwoTip GlobalCrestSourceGates
open AngularCylinderExpansion ActualThreeReturnNormalization

noncomputable section

/-- The actual central closed carrier in the physical plane. -/
def physicalInterval (c : ℝ) (p : ℕ) : Set ℂ :=
  physicalPoint c p '' Icc (-1 : ℝ) 1

/-- Two physical points share their complete closed-branch itinerary. -/
def PhysicalSameItinerary (c : ℝ) (p n : ℕ) (z w : ℂ) : Prop :=
  ∀ j : ℕ, j < n →
    SameBranch ((((quadraticMap c)^[(3*p)*j]) z).re)
      ((((quadraticMap c)^[(3*p)*j]) w).re)

theorem physicalPoint_iterate {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (n : ℕ) (x : ℝ) :
    ((quadraticMap c)^[(3*p)*n]) (physicalPoint c p x) =
      physicalPoint c p (((centralMap c p)^[n]) x) := by
  rw [iterate_mul]
  exact ((physicalPoint_semiconj hp hc).iterate_right n x).symm

theorem physicalPoint_distance {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (x y : ℝ) :
    ‖physicalPoint c p x-physicalPoint c p y‖ =
      criticalValue c p*centralRadius c p*|x-y| := by
  have ht := centralRadius_pos hp hc
  simp only [physicalPoint, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have he : -criticalValue c p*centralRadius c p*x-
      (-criticalValue c p*centralRadius c p*y) =
      -(criticalValue c p*centralRadius c p)*(x-y) := by ring
  rw [he, abs_mul, abs_neg, abs_of_pos (mul_pos hc.2.1 ht)]

theorem physical_sameBranch_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (x y : ℝ) :
    SameBranch (physicalPoint c p x).re (physicalPoint c p y).re ↔ SameBranch x y := by
  have ht := centralRadius_pos hp hc
  have hs : -criticalValue c p*centralRadius c p < 0 :=
    mul_neg_of_neg_of_pos (neg_neg_of_pos hc.2.1) ht
  have hnonneg (v : ℝ) : 0 ≤ -criticalValue c p*centralRadius c p*v ↔ v ≤ 0 := by
    constructor
    · intro hv
      rcases mul_nonneg_iff.mp hv with hv | hv
      · exact False.elim (not_le_of_gt hs hv.1)
      · exact hv.2
    · intro hv
      exact mul_nonneg_of_nonpos_of_nonpos hs.le hv
  have hnonpos (v : ℝ) : -criticalValue c p*centralRadius c p*v ≤ 0 ↔ 0 ≤ v := by
    constructor
    · intro hv
      rcases mul_nonpos_iff.mp hv with hv | hv
      · exact False.elim (not_le_of_gt hs hv.1)
      · exact hv.2
    · intro hv
      exact mul_nonpos_of_nonpos_of_nonneg hs.le hv
  simp only [SameBranch, physicalPoint, Complex.ofReal_re, hnonneg, hnonpos]
  exact or_comm

theorem physical_itinerary_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (n : ℕ) (x y : ℝ) :
    PhysicalSameItinerary c p n (physicalPoint c p x) (physicalPoint c p y) ↔
      SameItinerary (centralMap c p) n x y := by
  constructor <;> intro h j hj
  · have hs := h j hj
    rw [physicalPoint_iterate hp hc, physicalPoint_iterate hp hc] at hs
    exact (physical_sameBranch_iff hp hc _ _).mp hs
  · have hs := (physical_sameBranch_iff hp hc _ _).mpr (h j hj)
    simpa only [physicalPoint_iterate hp hc] using hs

/-- Every two points in any actual depth-n branch cylinder are this close.
All periods p >= 17 and every actual selected parameter obey the same rate. -/
theorem physical_cylinder_pair_bound {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (n : ℕ) {z w : ℂ}
    (hz : z ∈ physicalInterval c p) (hw : w ∈ physicalInterval c p)
    (hi : PhysicalSameItinerary c p n z w) :
    ‖z-w‖ ≤ criticalValue c p*centralRadius c p*Real.pi*(19/30 : ℝ)^n := by
  obtain ⟨x,hx,rfl⟩ := hz
  obtain ⟨y,hy,rfl⟩ := hw
  have ht := centralRadius_pos hp hc
  have hn := (centralMap_square_bounds hp hc).cylinder_diameter_le n hx hy
    ((physical_itinerary_iff hp hc n x y).mp hi)
  have hratio : (19*centralRadius c p)/(2*(15*centralRadius c p)) = (19/30 : ℝ) := by
    field_simp [ht.ne']
    <;> ring
  rw [hratio] at hn
  rw [physicalPoint_distance hp hc]
  have hmul := mul_le_mul_of_nonneg_left hn (mul_nonneg hc.2.1.le ht.le)
  simpa only [mul_assoc] using hmul

/-- A physical separation exceeding the cylinder bound forces an actual
branch disagreement before the stated horizon. -/
theorem physical_branch_separation {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (n : ℕ) {z w : ℂ}
    (hz : z ∈ physicalInterval c p) (hw : w ∈ physicalInterval c p)
    (hsize : criticalValue c p*centralRadius c p*Real.pi*(19/30 : ℝ)^n < ‖z-w‖) :
    ∃ j : ℕ, j < n ∧
      ¬SameBranch ((((quadraticMap c)^[(3*p)*j]) z).re)
        ((((quadraticMap c)^[(3*p)*j]) w).re) := by
  by_contra h
  push_neg at h
  have hi : PhysicalSameItinerary c p n z w := h
  exact (not_lt_of_ge (physical_cylinder_pair_bound hp hc n hz hw hi)) hsize

/-- Existence is inherited from the literal signed-tip construction;
neither a parameter nor a conjugacy is supplied by the caller. -/
theorem exists_physical_cylinder_contraction (p : ℕ) (hp : 17 ≤ p) :
    ∃ c : ℝ, ActualTip p c ∧ ∀ (n : ℕ) (z w : ℂ),
      z ∈ physicalInterval c p → w ∈ physicalInterval c p →
      PhysicalSameItinerary c p n z w →
      ‖z-w‖ ≤ criticalValue c p*centralRadius c p*Real.pi*(19/30 : ℝ)^n := by
  obtain ⟨c,hc⟩ := exists_actual_tip p hp
  exact ⟨c,hc,fun n _ _ hz hw hi => physical_cylinder_pair_bound hp hc n hz hw hi⟩

end
end ActualThreeReturnCylinders
