import ThreeReturnCollar
import PlanarFullification
import Mathlib.Analysis.Complex.AbsMax

/-!
# Fullness of the canonical three-return closure

The closed source is identified with the central component of the complete
closed disk pullback.  The maximum modulus principle then rules out every
bounded complementary component.  Thus fullness is proved for the actual
chosen polynomial component, rather than imposed on a replacement hull.
The literal physical collar is then proved open and connected, and the
number of its nonempty complementary components is proved to be exactly two.

These statements concern planar topology.  They do not identify the
variational capacity with a conformal uniformization modulus.
-/

namespace ThreeReturnFullness

open Set Metric Bornology Topology
open LoopsFormal.ProtectedCarriers LoopsQuadraticCylinderCensus
open ThreeReturnDomain ThreeReturnCollar ThreeReturnDegree
open ThreeReturnEstimates LimitingCrestQuadraticReturn NearTwoTip
open scoped Classical

noncomputable section

private theorem closed_component_isClosed {S : Set ℂ} (hS : IsClosed S)
    {a : ℂ} (ha : a ∈ S) : IsClosed (connectedComponentIn S a) := by
  apply closure_subset_iff_isClosed.mp
  exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
    (subset_closure (mem_connectedComponentIn ha))
    (hS.closure_subset_iff.mpr (connectedComponentIn_subset S a))

private theorem complementary_component_frontier {S : Set ℂ} (hS : IsClosed S)
    (z : ℂ) : frontier (connectedComponentIn Sᶜ z) ⊆ S := by
  intro w hw
  by_contra hwS
  have ho : IsOpen (connectedComponentIn Sᶜ z) :=
    hS.isOpen_compl.connectedComponentIn
  have hc := open_component_relative_closed Sᶜ hS.isOpen_compl z
  change w ∈ closure (connectedComponentIn Sᶜ z) ∧
    w ∉ interior (connectedComponentIn Sᶜ z) at hw
  exact hw.2 (ho.interior_eq.symm ▸ hc ⟨hw.1, hwS⟩)

/-- Every connected component of a closed disk pullback by an entire
function is full: no bounded component can be removed from its complement.
The proof uses the maximum modulus principle on each possible hole. -/
theorem entire_closed_disk_component_full (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (R : ℝ) (a : ℂ)
    (ha : f a ∈ closedBall 0 R) :
    planarFill (connectedComponentIn (f ⁻¹' closedBall 0 R) a) =
      connectedComponentIn (f ⁻¹' closedBall 0 R) a := by
  let S := f ⁻¹' closedBall 0 R
  let C := connectedComponentIn S a
  have hS : IsClosed S := isClosed_closedBall.preimage hf.continuous
  have haC : a ∈ C := mem_connectedComponentIn ha
  have hC : IsClosed C := closed_component_isClosed hS ha
  apply Subset.antisymm _ (planarFill_extensive C)
  intro z hz
  change IsBounded (connectedComponentIn Cᶜ z) at hz
  by_contra hzC
  let U := connectedComponentIn Cᶜ z
  have hzU : z ∈ U := mem_connectedComponentIn hzC
  obtain ⟨w, hw, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm hz
    ⟨z, hzU⟩ hf.diffContOnCl
  have hwC : w ∈ C := complementary_component_frontier hC z hw
  have hwR : ‖f w‖ ≤ R := by
    simpa [S] using connectedComponentIn_subset S a hwC
  have hclU : closure U ⊆ S := by
    intro v hv
    have hvR : ‖f v‖ ≤ R := (hmax hv).trans hwR
    simpa [S] using hvR
  have hjoin : IsPreconnected (C ∪ closure U) :=
    IsPreconnected.union' ⟨w, hwC, frontier_subset_closure hw⟩
      isPreconnected_connectedComponentIn isPreconnected_connectedComponentIn.closure
  have hsub : C ∪ closure U ⊆ C :=
    hjoin.subset_connectedComponentIn (Or.inl haC)
      (union_subset (connectedComponentIn_subset S a) hclU)
  exact hzC (hsub (Or.inr (subset_closure hzU)))

/-- A strict sphere barrier also traps the component of the closed
pullback, including every boundary point of that component. -/
theorem closed_component_inside_barrier (f : ℂ → ℂ) (r R : ℝ)
    (hr : 0 < r) (hzero : ‖f 0‖ ≤ R)
    (hbarrier : ∀ z : ℂ, ‖z‖ = r → R < ‖f z‖) :
    connectedComponentIn (f ⁻¹' closedBall 0 R) 0 ⊆ ball 0 r := by
  let C := connectedComponentIn (f ⁻¹' closedBall 0 R) 0
  have h0 : (0 : ℂ) ∈ C := mem_connectedComponentIn (by simpa using hzero)
  intro z hz
  rw [mem_ball_zero_iff]
  by_contra! hzbig
  have hpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hin : r ∈ Icc (‖(0 : ℂ)‖) ‖z‖ := by simpa using And.intro hr.le hzbig
  obtain ⟨w, hw, hwr⟩ := hpre.intermediate_value h0 hz continuous_norm.continuousOn hin
  have hsmall : ‖f w‖ ≤ R := by
    simpa using connectedComponentIn_subset (f ⁻¹' closedBall 0 R) 0 hw
  exact (not_lt_of_ge hsmall) (hbarrier w hwr)

/-- Openness approximates a boundary value from inside the target disk.
Exact signed fibers force each nearby local preimage back into the chosen
symmetric source, so no additional closed sheet occurs at its boundary. -/
theorem mem_closure_of_open_signed_fibers (f : ℂ → ℂ) (hf : IsOpenMap f)
    (W : Set ℂ) (r R : ℝ) (hR : 0 < R)
    (hW : W ⊆ ball 0 r) (hsym : ∀ w ∈ W, -w ∈ W)
    (honto : f '' W = ball 0 R)
    (hcollision : ∀ {z w : ℂ}, z ∈ ball 0 r → w ∈ ball 0 r →
      f z = f w → z = w ∨ z = -w)
    {z : ℂ} (hz : z ∈ ball 0 r) (hvalue : f z ∈ closedBall 0 R) :
    z ∈ closure W := by
  apply _root_.mem_closure_iff.mpr
  intro V hVo hzV
  have hfo : IsOpen (f '' (V ∩ ball 0 r)) := hf _ (hVo.inter isOpen_ball)
  have hfz : f z ∈ f '' (V ∩ ball 0 r) := ⟨z, ⟨hzV, hz⟩, rfl⟩
  have hvalue' : f z ∈ closure (ball (0 : ℂ) R) := by
    rw [closure_ball 0 hR.ne']
    exact hvalue
  obtain ⟨y, hyV, hyR⟩ := _root_.mem_closure_iff.mp hvalue' _ hfo hfz
  obtain ⟨w, hwV, hwy⟩ := hyV
  have hyW : y ∈ f '' W := honto.symm ▸ hyR
  obtain ⟨v, hvW, hvy⟩ := hyW
  have hwW : w ∈ W := by
    rcases hcollision hwV.2 (hW hvW) (hwy.trans hvy.symm) with h | h
    · simpa only [h] using hvW
    · simpa only [h] using hsym v hvW
  exact ⟨w, hwV.1, hwW⟩

/-- The closed central pullback component is precisely the closure of
the open central pullback component.  The conclusion follows from the
strict barrier and the verified local two-sheet geometry. -/
theorem closed_component_eq_closure (f : ℂ → ℂ) (hf : Continuous f)
    (hfo : IsOpenMap f) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hzero : ‖f 0‖ < R)
    (hbarrier : ∀ z : ℂ, ‖z‖ = r → R < ‖f z‖)
    (hsym : ∀ w ∈ connectedComponentIn (f ⁻¹' ball 0 R) 0,
      -w ∈ connectedComponentIn (f ⁻¹' ball 0 R) 0)
    (honto : f '' connectedComponentIn (f ⁻¹' ball 0 R) 0 = ball 0 R)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ R → ‖w‖ ≤ R →
      f z = f w → z = w ∨ z = -w) :
    connectedComponentIn (f ⁻¹' closedBall 0 R) 0 =
      closure (connectedComponentIn (f ⁻¹' ball 0 R) 0) := by
  let W := connectedComponentIn (f ⁻¹' ball 0 R) 0
  let C := connectedComponentIn (f ⁻¹' closedBall 0 R) 0
  have hW0 : (0 : ℂ) ∈ W := mem_connectedComponentIn (by simpa using hzero)
  have hWcl := (component_closure_inside_barrier f hf r R hr hzero hbarrier).1
  have hWr : W ⊆ ball 0 R := by
    intro w hw
    exact ball_subset_ball hrR.le (hWcl (subset_closure hw))
  have hCr := closed_component_inside_barrier f r R hr hzero.le hbarrier
  apply Subset.antisymm
  · intro z hz
    apply mem_closure_of_open_signed_fibers f hfo W R R (hr.trans hrR)
      hWr hsym honto
      (fun hz hw hzw => hcollision (mem_ball_zero_iff.mp hz).le
        (mem_ball_zero_iff.mp hw).le hzw)
      (ball_subset_ball hrR.le (hCr hz))
    exact connectedComponentIn_subset (f ⁻¹' closedBall 0 R) 0 hz
  · exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure hW0)
      ((isClosed_closedBall.preimage hf).closure_subset_iff.mpr
        ((connectedComponentIn_subset (f ⁻¹' ball 0 R) 0).trans
          (preimage_mono ball_subset_closedBall)))

/-- Fullness of a bounded plane set gives a single connected exterior,
using the archived identification of the unique unbounded component. -/
theorem full_bounded_complement_connected {K : Set ℂ} (hK : IsBounded K)
    (hfull : planarFill K = K) : IsConnected Kᶜ := by
  obtain ⟨a, ha, _, he, _⟩ := planarFill_exterior hK
  rw [hfull] at he
  rw [he]
  exact ⟨⟨a, mem_connectedComponentIn ha⟩, isPreconnected_connectedComponentIn⟩

/-- The actual open source has a full closure under the same verified
barrier and exact signed-fiber hypotheses as the canonical collar. -/
theorem source_closure_full_of_bounds (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : criticalValue c p ≠ 0)
    (hzero : ‖threeReturn c p 0‖ < 1/6)
    (hbarrier : ∀ z : ℂ, ‖z‖ = 3/20 → 1/6 < ‖threeReturn c p z‖)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 1/6 → ‖w‖ ≤ 1/6 →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w)) :
    planarFill (closure (source c p)) = closure (source c p) := by
  have hF : Differentiable ℂ (normalizedReturn c p) :=
    fun z => (normalized_return_hasDerivAt c p hp hd z).differentiableAt
  have hdiff : Differentiable ℂ (threeReturn c p) := by
    simpa [threeReturn, Function.iterate_succ_apply', Function.comp_def] using
      hF.comp (hF.comp hF)
  have he := closed_component_eq_closure (threeReturn c p) hdiff.continuous
    (threeReturn_open c p hd) (3/20) (1/6) (by norm_num) (by norm_num)
    hzero hbarrier (source_symmetric c p hp hzero) (source_image c p hd hzero)
    (fun hz hw hzw => (hcollision hz hw).mp hzw)
  change connectedComponentIn (threeReturn c p ⁻¹' closedBall 0 (1/6)) 0 =
    closure (source c p) at he
  rw [← he]
  exact entire_closed_disk_component_full _ hdiff _ _ (by simpa using hzero.le)

/-- The selected actual source has a full closure at every period in
the analytic tail.  No filling operation changes this source. -/
theorem actual_source_closure_full {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    planarFill (closure (source c p)) = closure (source c p) := by
  apply source_closure_full_of_bounds c p (by omega) hc.2.1.ne'
    (actual_critical_value_bound hp hc)
  · intro z hz
    have hb := actual_annular_barrier hp hc (le_of_eq hz.symm)
      (by rw [hz]; norm_num [outerRadius])
    change 1/6 + 1/500 < ‖threeReturn c p z‖ at hb
    linarith
  · exact fun hz hw => actual_three_return_collision_iff hp hc hz hw

/-- The actual normalized source closure has one connected exterior. -/
theorem actual_source_exterior_connected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsConnected (closure (source c p))ᶜ :=
  full_bounded_complement_connected
    (actual_canonical_collar hp hc).compact_closure.isBounded
    (actual_source_closure_full hp hc)

/-- Scaling transports the connected exterior to the original physical
coordinate, with the actual physical source kept unchanged. -/
theorem physical_exterior_connected_of_normalized (c : ℝ) (p : ℕ)
    (hd : criticalValue c p ≠ 0)
    (hconn : IsConnected (closure (source c p))ᶜ) :
    IsConnected (closure (physicalSource c p))ᶜ := by
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd
  let e := Homeomorph.mulLeft₀ (criticalValue c p : ℂ) hdC
  have he : closure (physicalSource c p) = e '' closure (source c p) :=
    (e.image_closure (source c p)).symm
  rw [he, ← e.image_compl]
  exact hconn.image e e.continuous.continuousOn

theorem actual_physical_exterior_connected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : IsConnected (closure (physicalSource c p))ᶜ :=
  physical_exterior_connected_of_normalized c p hc.2.1.ne'
    (actual_source_exterior_connected hp hc)

private theorem round_annulus_preconnected (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    IsPreconnected (ball (0 : ℂ) R \ closedBall 0 r) := by
  have hR : 0 < R := hr.trans hrR
  have he : Complex.exp '' {w : ℂ | Real.log r < w.re ∧ w.re < Real.log R} =
      ball (0 : ℂ) R \ closedBall 0 r := by
    ext z
    simp only [mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff,
      not_le, mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Complex.norm_exp]
      exact ⟨by simpa [Real.exp_log hR] using Real.exp_lt_exp.mpr hw.2,
        by simpa [Real.exp_log hr] using Real.exp_lt_exp.mpr hw.1⟩
    · intro hz
      have hzpos : 0 < ‖z‖ := hr.trans hz.2
      refine ⟨Complex.log z, ?_, Complex.exp_log (norm_pos_iff.mp hzpos)⟩
      rw [Complex.log_re]
      exact ⟨Real.log_lt_log hr hz.2, Real.log_lt_log hzpos hz.1⟩
  rw [← he]
  exact ((convex_halfSpace_re_gt (Real.log r)).inter
    (convex_halfSpace_re_lt (Real.log R))).isPreconnected.image _
      Complex.continuous_exp.continuousOn

/-- Intersecting a connected exterior with a disk that leaves a round
collar around the inner set preserves connectedness.  A radial clamp
supplies a connected inner part, overlapping the round outer annulus. -/
theorem collar_connected_of_exterior_connected {K : Set ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hK : K ⊆ ball 0 r)
    (hconn : IsConnected Kᶜ) : IsConnected (ball (0 : ℂ) R \ K) := by
  let q := (r + R) / 2
  have hrq : r < q := by dsimp [q]; linarith
  have hqR : q < R := by dsimp [q]; linarith
  have hq : 0 < q := hr.trans hrq
  let g : ℂ → ℂ := fun z => (q / max q ‖z‖) • z
  have hmax (z : ℂ) : 0 < max q ‖z‖ := hq.trans_le (le_max_left _ _)
  have hg : Continuous g :=
    (continuous_const.div (continuous_const.max continuous_norm)
      (fun z => (hmax z).ne')).smul continuous_id
  have hgfix {z : ℂ} (hz : ‖z‖ ≤ q) : g z = z := by
    simp [g, max_eq_left hz, hq.ne']
  have hgnorm {z : ℂ} (hz : q ≤ ‖z‖) : ‖g z‖ = q := by
    have hzpos : 0 < ‖z‖ := hq.trans_le hz
    change ‖(q / max q ‖z‖) • z‖ = q
    rw [norm_smul, Real.norm_eq_abs, max_eq_right hz,
      abs_of_pos (div_pos hq hzpos), div_mul_cancel₀ _ hzpos.ne']
  have himage : g '' Kᶜ = closedBall 0 q \ K := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      by_cases hzq : ‖z‖ ≤ q
      · rw [hgfix hzq]
        exact ⟨by simpa using hzq, hz⟩
      · have hnorm := hgnorm (le_of_lt (lt_of_not_ge hzq))
        refine ⟨by simp [hnorm], ?_⟩
        intro hgz
        have hsmall : ‖g z‖ < r := by simpa using hK hgz
        rw [hnorm] at hsmall
        exact (not_lt_of_ge hrq.le) hsmall
    · intro z hz
      exact ⟨z, hz.2, hgfix (by simpa using hz.1)⟩
  have hinner : IsPreconnected (closedBall 0 q \ K) := by
    rw [← himage]
    exact hconn.isPreconnected.image g hg.continuousOn
  have hqnorm : ‖(q : ℂ)‖ = q := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  have hqK : (q : ℂ) ∉ K := by
    intro hk
    have hsmall : ‖(q : ℂ)‖ < r := by simpa using hK hk
    rw [hqnorm] at hsmall
    exact (not_lt_of_ge hrq.le) hsmall
  have hqinner : (q : ℂ) ∈ closedBall 0 q \ K :=
    ⟨mem_closedBall_zero_iff.mpr hqnorm.le, hqK⟩
  have hqouter : (q : ℂ) ∈ ball 0 R \ closedBall 0 r := by
    simpa only [mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, hqnorm]
      using And.intro hqR (not_le.mpr hrq)
  have hunion : (closedBall 0 q \ K) ∪ (ball 0 R \ closedBall 0 r) =
      ball 0 R \ K := by
    apply Subset.antisymm
    · rintro z (hz | hz)
      · exact ⟨(closedBall_subset_ball hqR) hz.1, hz.2⟩
      · exact ⟨hz.1, fun hk => hz.2 (ball_subset_closedBall (hK hk))⟩
    · intro z hz
      by_cases hzq : z ∈ closedBall 0 q
      · exact Or.inl ⟨hzq, hz.2⟩
      · exact Or.inr ⟨hz.1, fun hzr => hzq (closedBall_subset_closedBall hrq.le hzr)⟩
  rw [← hunion]
  exact ⟨⟨q, Or.inl hqinner⟩, IsPreconnected.union'
    ⟨q, hqinner, hqouter⟩ hinner (round_annulus_preconnected r R hr hrR)⟩

/-- The literal physical target minus the actual compact source closure
is connected; its nondegenerate embedded round collar is already fixed
by the quantitative construction. -/
theorem actual_physical_collar_connected {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    IsConnected (physicalTarget c p \ closure (physicalSource c p)) := by
  have h := actual_canonical_collar hp hc
  have hd := h.scale_pos
  exact collar_connected_of_exterior_connected
    (by positivity : 0 < 3 * criticalValue c p / 20)
    (by nlinarith [h.scale_pos] : 3 * criticalValue c p / 20 < criticalValue c p / 6)
    h.physical_closure_inside (actual_physical_exterior_connected hp hc)

private theorem outer_disk_preconnected (R : ℝ) (hR : 0 < R) :
    IsPreconnected (ball (0 : ℂ) R)ᶜ := by
  have he : Complex.exp '' {w : ℂ | Real.log R ≤ w.re} = (ball (0 : ℂ) R)ᶜ := by
    ext z
    simp only [mem_compl_iff, mem_ball_zero_iff, not_lt, mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Complex.norm_exp, ← Real.exp_log hR]
      exact Real.exp_le_exp.mpr hw
    · intro hz
      have hzpos : 0 < ‖z‖ := hR.trans_le hz
      exact ⟨Complex.log z, by simpa [Complex.log_re] using Real.log_le_log hR hz,
        Complex.exp_log (norm_pos_iff.mp hzpos)⟩
  rw [← he]
  exact (convex_halfSpace_re_ge (Real.log R)).isPreconnected.image _
    Complex.continuous_exp.continuousOn

private theorem collar_complement_no_crossing {K : Set ℂ} {r R : ℝ}
    (hrR : r < R) (hK : K ⊆ ball 0 r) {C : Set ℂ}
    (hC : IsPreconnected C) (hsub : C ⊆ (ball 0 R \ K)ᶜ)
    {a b : ℂ} (ha : a ∈ C) (haK : a ∈ K) (hb : b ∈ C)
    (hbR : b ∉ ball 0 R) : False := by
  have han : ‖a‖ < r := by simpa using hK haK
  have hbn : R ≤ ‖b‖ := by simpa using hbR
  obtain ⟨w, hwC, hwr⟩ := hC.intermediate_value ha hb continuous_norm.continuousOn
    (show r ∈ Icc ‖a‖ ‖b‖ from ⟨han.le, hrR.le.trans hbn⟩)
  change ‖w‖ = r at hwr
  apply hsub hwC
  refine ⟨by simpa [hwr] using hrR, ?_⟩
  intro hwK
  have hsmall : ‖w‖ < r := by simpa using hK hwK
  rw [hwr] at hsmall
  exact lt_irrefl r hsmall

/-- The complement of a collar around a connected inner set has exactly
the two expected kinds of components: the inner set and the exterior of
the round target.  This is a direct component calculation in the plane. -/
theorem collar_complement_component {K : Set ℂ} {r R : ℝ}
    (hR : 0 < R) (hrR : r < R) (hK : K ⊆ ball 0 r)
    (hconn : IsPreconnected K) {z : ℂ} (hz : z ∈ (ball 0 R \ K)ᶜ) :
    connectedComponentIn (ball 0 R \ K)ᶜ z =
      if z ∈ K then K else (ball 0 R)ᶜ := by
  let C := connectedComponentIn (ball 0 R \ K)ᶜ z
  have hzC : z ∈ C := mem_connectedComponentIn hz
  have hsub : C ⊆ (ball 0 R \ K)ᶜ := connectedComponentIn_subset _ _
  by_cases hzK : z ∈ K
  · rw [if_pos hzK]
    apply Subset.antisymm
    · intro w hw
      by_contra hwK
      have hwR : w ∉ ball 0 R := fun hwR => hsub hw ⟨hwR, hwK⟩
      exact collar_complement_no_crossing hrR hK isPreconnected_connectedComponentIn
        hsub hzC hzK hw hwR
    · exact hconn.subset_connectedComponentIn hzK (fun w hw hwa => hwa.2 hw)
  · rw [if_neg hzK]
    have hzR : z ∉ ball 0 R := fun hzR => hz ⟨hzR, hzK⟩
    apply Subset.antisymm
    · intro w hw hwR
      have hwK : w ∈ K := by
        by_contra hwK
        exact hsub hw ⟨hwR, hwK⟩
      exact collar_complement_no_crossing hrR hK isPreconnected_connectedComponentIn
        hsub hw hwK hzC hzR
    · exact (outer_disk_preconnected R hR).subset_connectedComponentIn hzR
        (fun w hw hwa => hw hwa.1)

/-- Every complementary component of the literal physical collar is
identified with one of its two actual complementary sets. -/
theorem actual_physical_complement_component {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ}
    (hz : z ∈ (physicalTarget c p \ closure (physicalSource c p))ᶜ) :
    connectedComponentIn (physicalTarget c p \ closure (physicalSource c p))ᶜ z =
      if z ∈ closure (physicalSource c p) then closure (physicalSource c p)
      else (physicalTarget c p)ᶜ := by
  have h := actual_canonical_collar hp hc
  have hd := h.scale_pos
  have hphys : IsConnected (physicalSource c p) :=
    h.isConnected_source.image _ (continuous_const.mul continuous_id).continuousOn
  exact collar_complement_component (by positivity)
    (by nlinarith [hd] : 3 * criticalValue c p / 20 < criticalValue c p / 6)
    h.physical_closure_inside hphys.closure.isPreconnected hz

/-- A common interface for both finite exact certificates and the
analytic tail: the same raw barrier and fiber inequalities give a full
actual source closure, a connected physical collar, and its complete
complementary-component identification. -/
theorem physical_collar_topology_of_bounds (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : 0 < criticalValue c p)
    (hzero : ‖threeReturn c p 0‖ < 1/6)
    (hbarrier : ∀ z : ℂ, ‖z‖ = 3/20 → 1/6 < ‖threeReturn c p z‖)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 1/6 → ‖w‖ ≤ 1/6 →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w)) :
    planarFill (closure (source c p)) = closure (source c p) ∧
    IsConnected (physicalTarget c p \ closure (physicalSource c p)) ∧
    ∀ z ∈ (physicalTarget c p \ closure (physicalSource c p))ᶜ,
      connectedComponentIn (physicalTarget c p \ closure (physicalSource c p))ᶜ z =
        if z ∈ closure (physicalSource c p) then closure (physicalSource c p)
        else (physicalTarget c p)ᶜ := by
  have h := canonical_collar_of_bounds c p hp hd hzero hbarrier hcollision
  have hfull := source_closure_full_of_bounds c p hp hd.ne' hzero hbarrier hcollision
  have hnormal := full_bounded_complement_connected h.compact_closure.isBounded hfull
  have hphysical := physical_exterior_connected_of_normalized c p hd.ne' hnormal
  have hconn := collar_connected_of_exterior_connected
    (by positivity : 0 < 3 * criticalValue c p / 20)
    (by nlinarith [hd] : 3 * criticalValue c p / 20 < criticalValue c p / 6)
    h.physical_closure_inside hphysical
  have hphys : IsConnected (physicalSource c p) :=
    h.isConnected_source.image _ (continuous_const.mul continuous_id).continuousOn
  refine ⟨hfull, hconn, fun z hz => ?_⟩
  exact collar_complement_component (by positivity)
    (by nlinarith [hd] : 3 * criticalValue c p / 20 < criticalValue c p / 6)
    h.physical_closure_inside hphys.closure.isPreconnected hz

/-- The physical collar is an open connected plane domain with exactly
two complementary components.  Both components are identified above;
this count does not use an annulus uniformization theorem. -/
theorem physical_ring_domain_of_components (c : ℝ) (p : ℕ)
    (h : CanonicalCollar c p)
    (hconnected : IsConnected (physicalTarget c p \ closure (physicalSource c p)))
    (hcomponent : ∀ z ∈ (physicalTarget c p \ closure (physicalSource c p))ᶜ,
      connectedComponentIn (physicalTarget c p \ closure (physicalSource c p))ᶜ z =
        if z ∈ closure (physicalSource c p) then closure (physicalSource c p)
        else (physicalTarget c p)ᶜ) :
    IsOpen (physicalTarget c p \ closure (physicalSource c p)) ∧
    IsConnected (physicalTarget c p \ closure (physicalSource c p)) ∧
    {C : Set ℂ | ∃ z ∈ (physicalTarget c p \ closure (physicalSource c p))ᶜ,
      connectedComponentIn (physicalTarget c p \ closure (physicalSource c p))ᶜ z = C}.ncard = 2 := by
  let K := closure (physicalSource c p)
  let V := physicalTarget c p
  let A := V \ K
  have hcomp (z : ℂ) (hz : z ∈ Aᶜ) :
      connectedComponentIn Aᶜ z = if z ∈ K then K else Vᶜ := hcomponent z hz
  have hd := h.scale_pos
  have hR : 0 < criticalValue c p / 6 := by positivity
  have h0K : (0 : ℂ) ∈ K := subset_closure ⟨0, h.zero_mem, mul_zero _⟩
  have h0V : (0 : ℂ) ∈ V := by simpa [V, physicalTarget] using hR
  have h0A : (0 : ℂ) ∈ Aᶜ := fun ha => ha.2 h0K
  have h0component : connectedComponentIn Aᶜ 0 = K := by
    simpa only [if_pos h0K] using hcomp 0 h0A
  let b : ℂ := (criticalValue c p / 6 : ℝ)
  have hbnorm : ‖b‖ = criticalValue c p / 6 := by
    simp only [b, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hbV : b ∉ V := by
    change b ∉ ball 0 (criticalValue c p / 6)
    rw [mem_ball_zero_iff, hbnorm]
    exact lt_irrefl _
  have hbK : b ∉ K := by
    intro hb
    have hn : ‖b‖ < 3 * criticalValue c p / 20 := by
      simpa using h.physical_closure_inside hb
    rw [hbnorm] at hn
    nlinarith [hd]
  have hbA : b ∈ Aᶜ := fun ha => hbV ha.1
  have hbcomponent : connectedComponentIn Aᶜ b = Vᶜ := by
    simpa only [if_neg hbK] using hcomp b hbA
  have hne : K ≠ Vᶜ := by
    intro he
    exact (he ▸ h0K) h0V
  have hcomponents : {C : Set ℂ | ∃ z ∈ Aᶜ, connectedComponentIn Aᶜ z = C} =
      {K, Vᶜ} := by
    ext C
    constructor
    · rintro ⟨z, hz, rfl⟩
      have he := hcomp z hz
      by_cases hzK : z ∈ K
      · exact Or.inl (by simpa only [if_pos hzK] using he)
      · exact Or.inr (mem_singleton_iff.mpr (by simpa only [if_neg hzK] using he))
    · intro hC
      rcases hC with hC | hC
      · exact ⟨0, h0A, h0component.trans hC.symm⟩
      · exact ⟨b, hbA, hbcomponent.trans hC.symm⟩
  refine ⟨isOpen_ball.sdiff isClosed_closure, hconnected, ?_⟩
  change {C : Set ℂ | ∃ z ∈ Aᶜ, connectedComponentIn Aᶜ z = C}.ncard = 2
  rw [hcomponents]
  exact ncard_pair hne

/-- The generic raw inequalities imply the complete ring-domain statement,
including an exact count of the complementary components. -/
theorem physical_ring_domain_of_bounds (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : 0 < criticalValue c p)
    (hzero : ‖threeReturn c p 0‖ < 1/6)
    (hbarrier : ∀ z : ℂ, ‖z‖ = 3/20 → 1/6 < ‖threeReturn c p z‖)
    (hcollision : ∀ {z w : ℂ}, ‖z‖ ≤ 1/6 → ‖w‖ ≤ 1/6 →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w)) :
    IsOpen (physicalTarget c p \ closure (physicalSource c p)) ∧
    IsConnected (physicalTarget c p \ closure (physicalSource c p)) ∧
    {C : Set ℂ | ∃ z ∈ (physicalTarget c p \ closure (physicalSource c p))ᶜ,
      connectedComponentIn (physicalTarget c p \ closure (physicalSource c p))ᶜ z = C}.ncard = 2 := by
  have h := physical_collar_topology_of_bounds c p hp hd hzero hbarrier hcollision
  exact physical_ring_domain_of_components c p
    (canonical_collar_of_bounds c p hp hd hzero hbarrier hcollision) h.2.1 h.2.2

/-- The actual physical collar is a ring domain at every analytic-tail
period, with its two complementary components counted in Lean. -/
theorem actual_physical_ring_domain {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    IsOpen (physicalTarget c p \ closure (physicalSource c p)) ∧
    IsConnected (physicalTarget c p \ closure (physicalSource c p)) ∧
    {C : Set ℂ | ∃ z ∈ (physicalTarget c p \ closure (physicalSource c p))ᶜ,
      connectedComponentIn (physicalTarget c p \ closure (physicalSource c p))ᶜ z = C}.ncard = 2 :=
  physical_ring_domain_of_components c p (actual_canonical_collar hp hc)
    (actual_physical_collar_connected hp hc)
    (fun _ hz => actual_physical_complement_component hp hc hz)

end
end ThreeReturnFullness
