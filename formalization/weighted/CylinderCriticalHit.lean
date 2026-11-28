import AngularCylinderExpansion

/-!
# A physical interval larger than a cylinder contains a precritical cut

The cylinder estimate applies to any two points with the same complete
finite sign itinerary.  Its contrapositive, followed by the intermediate
value theorem for the actual continuous iterate, places a preimage of the
critical point strictly inside every interval exceeding that estimate.

The strict size threshold retains the exact time range `j < n`; no
logarithmic rounding convention or endpoint exception is implicit.
-/

namespace AngularCylinderExpansion

open Set Function

private theorem interior_zero_of_not_sameBranch {g : ℝ → ℝ} {x y : ℝ}
    (hg : Continuous g) (hxy : x < y) (hs : ¬ SameBranch (g x) (g y)) :
    ∃ z ∈ Ioo x y, g z = 0 := by
  have hopp : (g x < 0 ∧ 0 < g y) ∨ (0 < g x ∧ g y < 0) := by
    by_cases hx : 0 ≤ g x
    · have hy : g y < 0 :=
        lt_of_not_ge (fun hy => hs (Or.inl ⟨hx, hy⟩))
      have hx' : 0 < g x :=
        lt_of_not_ge (fun hx' => hs (Or.inr ⟨hx', hy.le⟩))
      exact Or.inr ⟨hx', hy⟩
    · have hx' : g x < 0 := lt_of_not_ge hx
      have hy : 0 < g y :=
        lt_of_not_ge (fun hy => hs (Or.inr ⟨hx'.le, hy⟩))
      exact Or.inl ⟨hx', hy⟩
  have hleft : g x ≠ 0 := by
    rcases hopp with ⟨hx, _⟩ | ⟨hx, _⟩
    · exact hx.ne
    · exact hx.ne'
  have hright : g y ≠ 0 := by
    rcases hopp with ⟨_, hy⟩ | ⟨_, hy⟩
    · exact hy.ne'
    · exact hy.ne
  have hzero : (0 : ℝ) ∈ g '' Icc x y := by
    rcases hopp with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact intermediate_value_Icc hxy.le hg.continuousOn ⟨hx.le, hy.le⟩
    · exact intermediate_value_Icc' hxy.le hg.continuousOn ⟨hy.le, hx.le⟩
  obtain ⟨z, hz, hgz⟩ := hzero
  have hxz : x < z := by
    by_contra hn
    have he : z = x := le_antisymm (le_of_not_gt hn) hz.1
    exact hleft (by simpa only [he] using hgz)
  have hzy : z < y := by
    by_contra hn
    have he : z = y := le_antisymm hz.2 (le_of_not_gt hn)
    exact hright (by simpa only [he] using hgz)
  exact ⟨z, ⟨hxz, hzy⟩, hgz⟩

namespace EvenQuadraticBounds

/-- Every real interval larger than the explicit depth-`n` cylinder
bound contains an actual critical preimage at a time strictly below `n`.
The witness lies in the open interval, even when its endpoints themselves
have critical or endpoint encounters. -/
theorem exists_interior_precritical {f : ℝ → ℝ} {a b : ℝ}
    (h : EvenQuadraticBounds f a b) (n : ℕ) {x y : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1)
    (hxy : x < y) (hsize : Real.pi * (b / (2 * a)) ^ n < y - x) :
    ∃ j < n, ∃ z ∈ Ioo x y, (f^[j]) z = 0 := by
  classical
  have hnot : ¬ SameItinerary f n x y := by
    intro hi
    have hd := h.cylinder_diameter_le n hx hy hi
    rw [abs_of_nonpos (sub_nonpos.mpr hxy.le)] at hd
    linarith only [hd, hsize]
  have hex : ∃ j < n, ¬ SameBranch ((f^[j]) x) ((f^[j]) y) := by
    by_contra hn
    apply hnot
    intro j hj
    by_contra hs
    exact hn ⟨j, hj, hs⟩
  obtain ⟨j, hj, hs⟩ := hex
  obtain ⟨z, hz, hzero⟩ :=
    interior_zero_of_not_sameBranch (h.continuous.iterate j) hxy hs
  exact ⟨j, hj, z, hz, hzero⟩

end EvenQuadraticBounds

end AngularCylinderExpansion
