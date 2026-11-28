import SlitCubicImaginaryBoundary
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# The actual cubic primitive takes values in the open rectangle

The proof uses the actual boundary values and uniform decay at infinity.
If a real-linear coordinate exceeded its boundary bound, it would attain
an interior maximum on a compact upper half-disk.  Fermat's theorem and
the nonzero complex derivative exclude that maximum.  The same argument
excludes equality in the interior.  No image or uniformization hypothesis
is imposed on the primitive.
-/

namespace SlitCubicRectangle

open Set Filter Metric MeasureTheory Complex
open SlitCubicCalibration SlitCubicBoundary SlitCubicBoundaryRange
open scoped Topology

noncomputable section

def openRectangle (B C : ℝ) : Set ℂ :=
  {w | 0 < w.re ∧ w.re < B ∧ -C < w.im ∧ w.im < 0}

theorem openRectangle_isOpen (B C : ℝ) : IsOpen (openRectangle B C) := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

theorem openRectangle_convex (B C : ℝ) : Convex ℝ (openRectangle B C) :=
  (convex_halfSpace_re_gt 0).inter ((convex_halfSpace_re_lt B).inter
    ((convex_halfSpace_im_gt (-C)).inter (convex_halfSpace_im_lt 0)))

theorem differential_ne_zero_upper (a b c : ℝ) {z : ℂ} (hz : z ∈ upper) :
    differential a b c z ≠ 0 := by
  have hn (t : ℝ) : z ≠ (t : ℂ) := by
    intro he
    have him := congrArg Complex.im he
    simp only [Complex.ofReal_im] at him
    exact hz.ne' him
  exact inv_ne_zero (mul_ne_zero
    (mul_ne_zero (upperRoot_ne_zero hz.le (hn a)) (upperRoot_ne_zero hz.le (hn b)))
    (upperRoot_ne_zero hz.le (hn c)))

private theorem not_isLocalMax_linear {F : ℂ → ℂ} {g z : ℂ}
    (hF : HasDerivAt F g z) (hg : g ≠ 0)
    (L : ℂ →L[ℝ] ℝ) (hL : L ≠ 0) : ¬ IsLocalMax (fun w => L (F w)) z := by
  intro hm
  have hzero := hm.hasFDerivAt_eq_zero
    (L.hasFDerivAt.comp z hF.complexToReal_fderiv)
  apply hL
  ext v
  have hv := congrArg (fun T : ℂ →L[ℝ] ℝ => T (g⁻¹ * v)) hzero
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hg,
    one_mul, ContinuousLinearMap.zero_apply] using hv

private theorem linear_coordinate_lt_boundary_bound {F : ℂ → ℂ} {q : ℂ → ℝ}
    (hq : ContinuousOn q closedUpper)
    (hnorm : ∀ z ∈ closedUpper, q z ≤ ‖F z‖)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R > 0,
      ∀ z ∈ closedUpper, R ≤ ‖z‖ → ‖F z‖ < ε)
    {B : ℝ} (hB : 0 ≤ B) (hboundary : ∀ x : ℝ, q (x : ℂ) ≤ B)
    (hmax : ∀ z ∈ upper, ¬ IsLocalMax q z) {z : ℂ} (hz : z ∈ upper) :
    q z < B := by
  have hclosed : IsClosed closedUpper := isClosed_le continuous_const Complex.continuous_im
  have hsub : upper ⊆ closedUpper := fun u hu => (show 0 < u.im from hu).le
  have hweak : ∀ v ∈ closedUpper, q v ≤ B := by
    intro v hv
    by_contra hnot
    have hvB : B < q v := lt_of_not_ge hnot
    have hv0 : 0 < q v := hB.trans_lt hvB
    obtain ⟨R, hR, hdec⟩ := hdecay (q v) hv0
    have hvR : ‖v‖ < R := by
      by_contra hn
      exact (lt_irrefl (q v)) ((hnorm v hv).trans_lt (hdec v hv (le_of_not_gt hn)))
    let K := closedUpper ∩ closedBall (0 : ℂ) R
    have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) R).inter_left hclosed
    have hvK : v ∈ K := ⟨hv, by simpa only [mem_closedBall, dist_zero_right] using hvR.le⟩
    obtain ⟨w, hwK, hwm⟩ := hK.exists_isMaxOn ⟨v, hvK⟩ (hq.mono inter_subset_left)
    have hvw : q v ≤ q w := hwm hvK
    have hwUpper : w ∈ upper := by
      by_contra hn
      have hwim : w.im = 0 := le_antisymm (le_of_not_gt hn) hwK.1
      have hwreal : w = (w.re : ℂ) := Complex.ext rfl (by simpa using hwim)
      have hwb : q w ≤ B := hwreal ▸ hboundary w.re
      linarith
    have hwR : ‖w‖ < R := by
      by_contra hn
      exact (not_lt_of_ge hvw) ((hnorm w hwK.1).trans_lt (hdec w hwK.1 (le_of_not_gt hn)))
    have hKn : K ∈ 𝓝 w := by
      apply inter_mem
      · exact mem_of_superset (upper_open.mem_nhds hwUpper) hsub
      · exact mem_of_superset
          (isOpen_ball.mem_nhds (by simpa only [mem_ball, dist_zero_right] using hwR))
          ball_subset_closedBall
    exact hmax w hwUpper (hwm.isLocalMax hKn)
  have hzle := hweak z (hsub hz)
  rcases lt_or_eq_of_le hzle with h | he
  · exact h
  · have hm : IsMaxOn q upper z := fun w hw => (hweak w (hsub hw)).trans_eq he.symm
    exact (hmax z hz (hm.isLocalMax (upper_open.mem_nhds hz))).elim

private theorem reCLM_ne_zero : (Complex.reCLM : ℂ →L[ℝ] ℝ) ≠ 0 := by
  intro h
  have he := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) h
  norm_num at he

private theorem imCLM_ne_zero : (Complex.imCLM : ℂ →L[ℝ] ℝ) ≠ 0 := by
  intro h
  have he := congrArg (fun L : ℂ →L[ℝ] ℝ => L I) h
  norm_num at he

private theorem tail_coordinate_lt {a b c B : ℝ} (hab : a < b) (hbc : b < c)
    (L : ℂ →L[ℝ] ℝ) (hL : L ≠ 0) (hbound : ∀ w : ℂ, L w ≤ ‖w‖)
    (hB : 0 ≤ B) (hboundary : ∀ x : ℝ, L (tail a b c (x : ℂ)) ≤ B)
    {z : ℂ} (hz : z ∈ upper) : L (tail a b c z) < B := by
  have hi := realDensity_integrable hab hbc
  exact linear_coordinate_lt_boundary_bound
    (L.continuous.comp_continuousOn (tail_continuousOn_closedUpper hi))
    (fun z _ => hbound (tail a b c z))
    (fun ε hε => tail_uniform_decay hi hε) hB hboundary
    (fun z hz => not_isLocalMax_linear (tail_hasDerivAt hi hz)
      (neg_ne_zero.mpr (differential_ne_zero_upper a b c hz)) L hL) hz

theorem tail_re_pos {a b c : ℝ} (hab : a < b) (hbc : b < c) {z : ℂ} (hz : z ∈ upper) :
    0 < (tail a b c z).re := by
  have h := tail_coordinate_lt hab hbc (-Complex.reCLM) (neg_ne_zero.mpr reCLM_ne_zero)
    (fun w => (neg_le_abs w.re).trans (Complex.abs_re_le_norm w)) (le_refl (0 : ℝ))
    (fun x => by simpa using neg_nonpos.mpr (tail_re_mem_Icc hab hbc x).1) hz
  simpa only [ContinuousLinearMap.neg_apply, Complex.reCLM_apply, neg_lt_zero] using h

theorem tail_re_lt_period {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {z : ℂ} (hz : z ∈ upper) : (tail a b c z).re < period a b c :=
  tail_coordinate_lt hab hbc Complex.reCLM reCLM_ne_zero
    (fun w => (le_abs_self w.re).trans (Complex.abs_re_le_norm w)) (period_pos hab hbc).le
    (fun x => (tail_re_mem_Icc hab hbc x).2) hz

theorem neg_height_lt_tail_im {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {z : ℂ} (hz : z ∈ upper) : -height a b c < (tail a b c z).im := by
  have h := tail_coordinate_lt hab hbc (-Complex.imCLM) (neg_ne_zero.mpr imCLM_ne_zero)
    (fun w => (neg_le_abs w.im).trans (Complex.abs_im_le_norm w)) (height_pos hab hbc).le
    (fun x => by
      have h := (SlitCubicImaginaryBoundary.tail_im_mem_Icc hab hbc x).1
      change -(tail a b c (x : ℂ)).im ≤ height a b c
      linarith) hz
  change -(tail a b c z).im < height a b c at h
  linarith

theorem tail_im_neg {a b c : ℝ} (hab : a < b) (hbc : b < c) {z : ℂ} (hz : z ∈ upper) :
    (tail a b c z).im < 0 :=
  tail_coordinate_lt hab hbc Complex.imCLM imCLM_ne_zero
    (fun w => (le_abs_self w.im).trans (Complex.abs_im_le_norm w)) (le_refl (0 : ℝ))
    (fun x => (SlitCubicImaginaryBoundary.tail_im_mem_Icc hab hbc x).2) hz

/-- Every interior point is carried into the actual open period rectangle. -/
theorem tail_mem_openRectangle {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {z : ℂ} (hz : z ∈ upper) :
    tail a b c z ∈ openRectangle (period a b c) (height a b c) :=
  ⟨tail_re_pos hab hbc hz, tail_re_lt_period hab hbc hz,
    neg_height_lt_tail_im hab hbc hz, tail_im_neg hab hbc hz⟩

end
end SlitCubicRectangle
