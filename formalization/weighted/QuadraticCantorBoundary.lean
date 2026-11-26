import QuadraticCantorCoding
import Mathlib.Topology.Perfect
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Perfect boundary and exterior density of the physical Cantor filled set

The actual filled set has no isolated points, is perfect, has empty interior,
and equals its planar frontier. The positive-escape locus is consequently
dense. These statements apply to the proved large-parameter regime and do not
identify native decoration charts or prime ends.
-/

namespace QuadraticCantor

open Set Function QuadraticEscape

/-- Flipping a sufficiently late symbol gives a distinct physical bounded
orbit point at every prescribed positive Euclidean accuracy. -/
theorem filled_no_isolated (c : ℂ) (hc : 8 ≤ ‖c‖) (z : ℂ)
    (hz : z ∈ filled c) (ε : ℝ) (hε : 0 < ε) :
    ∃ w : ℂ, w ∈ filled c ∧ w ≠ z ∧ dist z w < ε := by
  classical
  let x : filled c := ⟨z, hz⟩
  let a : ℕ → Fin 2 := coding c hc x
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖c‖ / ε)
    (by norm_num : (1 : ℝ) < 2)
  let b : ℕ → Fin 2 := fun k =>
    if k = n then (if a n = 0 then 1 else 0) else a k
  have hbn : b n ≠ a n := by
    by_cases h : a n = 0
    · simp [b, h]
    · simp [b, h, Ne.symm h]
  let y : filled c := (coding c hc).symm b
  have hy : coding c hc y = b := (coding c hc).apply_symm_apply b
  have hne : (y : ℂ) ≠ z := by
    intro he
    have hxy : y = x := Subtype.ext he
    apply hbn
    have h := congrFun hy n
    rw [hxy] at h
    exact h.symm
  have hprefix : ∀ k < n, coding c hc x k = coding c hc y k := by
    intro k hk
    rw [hy]
    simp only [b, if_neg (Nat.ne_of_lt hk)]
    rfl
  have hd := coding_prefix_bound c hc n x y hprefix
  have hsmall : ‖c‖ / (2 : ℝ)^n < ε := by
    apply (div_lt_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hn
  exact ⟨(y : ℂ), y.property, hne, hd.trans_lt hsmall⟩

/-- Perfectness is established in the ambient complex plane, including
the absence of isolated points of the actual filled set. -/
theorem filled_perfect (c : ℂ) (hc : 8 ≤ ‖c‖) : Perfect (filled c) := by
  refine ⟨filled_closed c, preperfect_iff_nhds.mpr ?_⟩
  intro z hz U hU
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨w, hw, hne, hd⟩ := filled_no_isolated c hc z hz ε hε
  exact ⟨w, ⟨hsub (Metric.mem_ball.mpr (by simpa only [dist_comm] using hd)), hw⟩,
    hne⟩

/-- A totally disconnected physical filled set cannot contain any open
complex ball, so its planar interior is empty. -/
theorem filled_interior_empty (c : ℂ) (hc : 8 ≤ ‖c‖) :
    interior (filled c) = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hz
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hz)
  have hs : (Metric.ball z ε).Subsingleton :=
    filled_totally_disconnected c hc (Metric.ball z ε) hsub
      (convex_ball z ε).isPreconnected
  have hw : z + ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have he : z = z + ((ε / 2 : ℝ) : ℂ) := hs (Metric.mem_ball_self hε) hw
  have hzero : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination -he
  have hr : ε / 2 = 0 := Complex.ofReal_eq_zero.mp hzero
  linarith

/-- The entire physical filled set is its own planar boundary. -/
theorem filled_frontier (c : ℂ) (hc : 8 ≤ ‖c‖) :
    frontier (filled c) = filled c := by
  rw [(filled_closed c).frontier_eq, filled_interior_empty c hc, Set.sdiff_empty]

/-- Positive escape points are dense in the plane in this parameter range. -/
theorem positive_escape_dense (c : ℂ) (hc : 8 ≤ ‖c‖) :
    Dense {z : ℂ | 0 < escape c z} := by
  have he : {z : ℂ | 0 < escape c z} = (filled c)ᶜ := by
    ext z
    change 0 < escape c z ↔ ¬escape c z = 0
    constructor
    · exact ne_of_gt
    · intro h
      exact lt_of_le_of_ne (escape_nonneg c z) (Ne.symm h)
  rw [he]
  exact interior_eq_empty_iff_dense_compl.mp (filled_interior_empty c hc)

end QuadraticCantor
