import SlitPotentialReflection

/-!
# Local upper-half-plane reflection

The sharp reflected slope estimate only needs a primitive in an open
neighborhood of the folded trace. In particular, a disk primitive need
not extend beyond the disk boundary.
-/

namespace SlitLocalReflection

open Set Filter Metric Complex SlitPotentialLength SlitPotentialReflection
open scoped Topology NNReal ENNReal
noncomputable section

private theorem upper_halfball_lipschitz_on {F F' : ℂ → ℂ} {U : Set ℂ}
    (hc : ContinuousOn F (U ∩ {z | 0 ≤ z.im}))
    (hd : ∀ z ∈ U, 0 < z.im → HasDerivAt F (F' z) z)
    {x : ℂ} {r : ℝ} {K : ℝ≥0} (hball : closedBall x r ⊆ U)
    (hK : ∀ z ∈ ball x r, ‖F' z‖₊ ≤ K) :
    LipschitzOnWith K F (ball x r ∩ {z : ℂ | 0 ≤ z.im}) := by
  let V := ball x r ∩ {z : ℂ | 0 < z.im}
  have hV : Convex ℝ V := (convex_ball x r).inter (convex_halfSpace_im_gt 0)
  have hLip : LipschitzOnWith K F V :=
    hV.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => (hd z (hball (ball_subset_closedBall hz.1)) hz.2).hasDerivWithinAt)
      (fun z hz => hK z hz.1)
  have hclH : closure V ⊆ {z : ℂ | 0 ≤ z.im} := by
    rw [← Complex.closure_setOf_lt_im]
    exact closure_mono inter_subset_right
  have hclU : closure V ⊆ U :=
    (closure_mono inter_subset_left).trans (closure_ball_subset_closedBall.trans hball)
  have hsub : ball x r ∩ {z : ℂ | 0 ≤ z.im} ⊆ closure V := by
    rw [← Complex.closure_setOf_lt_im]
    exact isOpen_ball.inter_closure
  exact (LipschitzOnWith.closure (hc.mono (subset_inter hclU hclH)) hLip).mono hsub

/-- Sharp local slope for a reflected primitive defined on an arbitrary
open neighborhood of the folded set. -/
theorem localSlopeBound_fold_re_on {F F' : ℂ → ℂ} {S U : Set ℂ}
    (hU : IsOpen U) (hfold : ∀ x ∈ S, fold x ∈ U)
    (hc : ContinuousOn F (U ∩ {z | 0 ≤ z.im}))
    (hd : ∀ z ∈ U, 0 < z.im → HasDerivAt F (F' z) z)
    (hF' : ∀ x ∈ S, ContinuousAt F' (fold x))
    {B : ℝ} (hB : 0 < B) :
    LocalSlopeBound (fun z => (F (fold z)).re / B)
      (fun z => ‖F' (fold z)‖ / B) S := by
  intro x hx L hL
  have hLB : ‖F' (fold x)‖ < L * B := (div_lt_iff₀ hB).mp hL
  have hL0 : 0 ≤ L := le_of_lt ((div_nonneg (norm_nonneg _) hB.le).trans_lt hL)
  have hUevent : ∀ᶠ z in 𝓝 (fold x), z ∈ U := hU.mem_nhds (hfold x hx)
  have hnear : ∀ᶠ z in 𝓝 (fold x), z ∈ U ∧ ‖F' z‖ < L * B :=
    hUevent.and ((hF' x hx).norm.eventually (gt_mem_nhds hLB))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hhalf : 0 < r / 2 := half_pos hr
  have hclosed : closedBall (fold x) (r / 2) ⊆ U := by
    intro z hz
    exact (hball (lt_of_le_of_lt hz (half_lt_self hr))).1
  have hLip := upper_halfball_lipschitz_on hc hd hclosed
    (K := Real.toNNReal (L * B)) (fun z hz =>
      (Real.le_toNNReal_iff_coe_le (mul_nonneg hL0 hB.le)).mpr
        (hball (hz.trans (half_lt_self hr))).2.le)
  refine ⟨ball x (r / 2), ball_mem_nhds x hhalf, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y hy z hz
  have hfy : fold y ∈ ball (fold x) (r / 2) :=
    (fold_lipschitz.dist_le_mul y x).trans_lt (by simpa using hy)
  have hfz : fold z ∈ ball (fold x) (r / 2) :=
    (fold_lipschitz.dist_le_mul z x).trans_lt (by simpa using hz)
  have hFdist := hLip.dist_le_mul (fold y) ⟨hfy, fold_im_nonneg y⟩
    (fold z) ⟨hfz, fold_im_nonneg z⟩
  rw [Real.coe_toNNReal _ (mul_nonneg hL0 hB.le)] at hFdist
  have hfoldDist : dist (fold y) (fold z) ≤ dist y z := by
    simpa using fold_lipschitz.dist_le_mul y z
  have hre : |(F (fold y)).re - (F (fold z)).re| ≤
      dist (F (fold y)) (F (fold z)) := by
    simpa only [dist_eq_norm, Complex.sub_re] using
      Complex.abs_re_le_norm (F (fold y) - F (fold z))
  rw [Real.coe_toNNReal _ hL0, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hB]
  apply (div_le_iff₀ hB).mpr
  calc
    |(F (fold y)).re - (F (fold z)).re| ≤
        (L * B) * dist (fold y) (fold z) := hre.trans hFdist
    _ ≤ (L * B) * dist y z := mul_le_mul_of_nonneg_left hfoldDist (mul_nonneg hL0 hB.le)
    _ = (L * dist y z) * B := by ring

end
end SlitLocalReflection
