import ParabolicComplexComponent
import ParabolicCenterBranch
import ParabolicTipRate

/-!
# Primitive Chebyshev-tip parameters converging to the real period-three root

For each p = 3n, n ≥ 6, the critical point has exact preperiod p+1
and exact eventual period p. Its central interval has p disjoint phases,
and in the complex plane it is an isolated component of its full pullback.
-/
namespace LoopsParabolic
open Set Function Filter Topology
noncomputable section

theorem Shot.on_exit_slab {t e : ℝ} {k : ℕ} (hs : Shot k t e) : t ∈ exitSlab k :=
  exitSlab_iff_orbit.mpr ⟨⟨hs.t_pos.le,hs.t_small⟩,hs.first_corridor,hs.first_exit⟩

/-- The selected tip lies strictly to the left of the unique center with
the same exit itinerary. The center also has exact physical period p. -/
theorem Shot.companion_center {t e : ℝ} {k : ℕ} (hs : Shot k t e) :
    ∃! s, (s ∈ exitSlab k ∧ (H s)^[k+2] 0 = 0) ∧
      t < s ∧ minimalPeriod (quad (-7/4+s)) 0 = 3*(k+2) := by
  obtain ⟨s,hsr,hzero,hstay,hex⟩ := hs.center_right
  have hsl := exitSlab_iff_orbit.mpr
    ⟨⟨hs.t_pos.le.trans hsr.1.le,hsr.2⟩,hstay,hex⟩
  exact ⟨s,⟨⟨hsl,hzero⟩,hsr.1,exit_center_minimalPeriod hsl hzero⟩,
    fun r hr => (exit_return_strictAnti k).injOn hr.1.1 hsl (hr.1.2.trans hzero.symm)⟩

/-- A quantitative family theorem in the original parameter and time
coordinates. All clauses refer to the same parameter c and interval I. -/
theorem near_parabolic_primitive_tips (n : ℕ) (hn : 6 ≤ n) :
    let p := 3*n
    ∃ c e : ℝ, -7/4 < c ∧ c < -(87/50) ∧ 0 < e ∧
      (1/25 ≤ ((p:ℝ)-6)^2*(c+7/4) ∧ ((p:ℝ)-6)^2*(c+7/4) ≤ 900) ∧
      (quad c)^[p] 0 = -e ∧ (quad c)^[2*p] 0 = e ∧
      minimalPeriod (quad c) ((quad c)^[p+1] 0) = p ∧
      (∀ m ≤ p, (quad c)^[m] 0 ∉ periodicPts (quad c)) ∧
      (∀ i j : ℕ, i < j → j < p →
        Disjoint ((quad c)^[i] '' Icc (-e) e) ((quad c)^[j] '' Icc (-e) e)) ∧
      ((quad c)^[p] '' Icc (-e) 0 = Icc (-e) e ∧ (quad c)^[p] '' Icc 0 e = Icc (-e) e) ∧
      ((cquad c)^[p] '' realSegment e = realSegment e) ∧
      connectedComponentIn ((cquad c)^[p] ⁻¹' realSegment e) 0 = realSegment e := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+2 := ⟨n-2,by omega⟩
  intro p
  obtain ⟨t,e,hs⟩ := shot_exists k (by omega)
  let c := -7/4+t
  have hp : 0 < p := by dsimp [p]; omega
  have hcycle := exact_period_of_shot ⟨hs.t_pos.le,hs.t_small⟩ hs.e_pos hs.e_small
    hs.corridor hs.penultimate hs.collision
  obtain ⟨hmin,htail⟩ := critical_preperiod_of_shot hs.e_pos hs.critical hcycle
  have hlast : (quad c)^[p] 0 = -e := by
    simpa [p,c,hs.critical] using reflected_blocks t 0 (k+2)
  have htwice : (quad c)^[2*p] 0 = e := by
    rw [two_mul,iterate_add_apply,hlast,← positive_iterates_even c e hp]
    exact hcycle.1
  have rate := channel_inverse_square hs.t_pos hs.t_small hs.first_corridor hs.first_exit.1
  have convertRate : ((p:ℝ)-6)^2*(c+7/4) = 9*((k:ℝ)^2*t) := by
    dsimp [p,c]; push_cast; ring
  obtain ⟨s,hsr,_⟩ := hs.center_right
  refine ⟨c,e,by dsimp [c]; linarith [hs.t_pos],by dsimp [c]; linarith [hsr.1,hsr.2],
    hs.e_pos,?_,hlast,htwice,hmin,htail,fun _ _ hij hj => phase_images_disjoint hs hij hj,
    (full_branches hs).2.2,complex_segment_invariant hs,complex_pullback_component hs⟩
  rw [convertRate]
  constructor <;> linarith [rate.1,rate.2]

/-- With index m=0,1,... the physical period is 18+3m. All choices of a
shot at each index give strictly decreasing parameters tending to −7/4. -/
theorem tip_sequence_converges {t e : ℕ → ℝ}
    (h : ∀ m, Shot (m+4) (t m) (e m)) :
    StrictAnti (fun m => -7/4+t m) ∧
      Tendsto (fun m => -7/4+t m) atTop (𝓝 (-7/4:ℝ)) := by
  constructor
  · intro i j hij
    have hh := exit_slabs_ordered (by omega : i+4<j+4)
      (h i).on_exit_slab (h j).on_exit_slab
    linarith
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := exists_nat_gt (1/ε)
    refine ⟨N,?_⟩
    intro m hm
    have hNm : (N:ℝ) ≤ m := by exact_mod_cast hm
    have hlarge : 1 < ε*((m:ℝ)+4) := by
      have := (div_lt_iff₀ hε).mp (hN.trans_le hNm)
      linarith
    have hs := (h m).first_rate_bound
    push_cast at hs
    have hlt : t m < ε := by
      by_contra! hn
      have hh := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (m:ℝ)+4)
      linarith
    rw [Real.dist_eq, show -7/4+t m-(-7/4) = t m by ring, abs_of_pos (h m).t_pos]
    exact hlt

#print axioms near_parabolic_primitive_tips
#print axioms open_complex_isolation
#print axioms interior_complex_fiber
#print axioms tip_sequence_converges

end
end LoopsParabolic
