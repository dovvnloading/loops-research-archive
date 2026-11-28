import ParentWaveEllipticChart
import ParentWaveEllipticBoundary
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Analytic continuation at regular points of the real boundary

The literal cubic differential selects a local holomorphic square root.
Connectedness fixes its sign against the upper-half-plane derivative.
The resulting primitive agrees with the given continuous closed-boundary
extension, so local derivative bounds apply to the canonical boundary traces.
-/

namespace ParentWaveUpperBoundary

open Set Complex Metric ParentWaveElliptic ParentWaveEllipticBoundary
open scoped Topology

noncomputable section

/-- At every finite point away from the three branch marks, the upper
primitive has a genuine local holomorphic extension.  Its derivative square
and norm agree with the physical cubic differential at every closed-upper
point of that neighborhood, including regular real boundary points. -/
theorem exists_local_extension (a b c : ℝ) {F E : ℂ → ℂ}
    (hF : ∀ z ∈ upperHalfPlane, HasDerivAt F (upperDifferential a b c z) z)
    (hE : ContinuousOn E (closure upperHalfPlane))
    (hFE : EqOn F E upperHalfPlane) {x : ℂ}
    (hx : (x-(a:ℂ))*(x-(b:ℂ))*(x-(c:ℂ)) ≠ 0) :
    ∃ r > 0, ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball x r) ∧
      EqOn E H (closure upperHalfPlane ∩ ball x r) ∧
      ∀ z ∈ closure upperHalfPlane ∩ ball x r,
        (deriv H z)^2 = ((z-(a:ℂ))*(z-(b:ℂ))*(z-(c:ℂ)))⁻¹ ∧
        ‖deriv H z‖ = ‖upperDifferential a b c z‖ ∧ deriv H z ≠ 0 := by
  let P (z : ℂ) := (z-(a:ℂ))*(z-(b:ℂ))*(z-(c:ℂ))
  let R (z : ℂ) := (P z)⁻¹
  let T : Set ℂ := {z | P z ≠ 0}
  have hP : Differentiable ℂ P := by dsimp [P]; fun_prop
  have hTo : IsOpen T := isOpen_ne.preimage hP.continuous
  have hR : DifferentiableOn ℂ R T :=
    fun z hz => ((hP z).inv hz).differentiableWithinAt
  obtain ⟨r,hr,hball,h,hh,hhn,hhsq⟩ :=
    exists_local_square_root hTo hR hx (inv_ne_zero hx)
  let S := upperHalfPlane ∩ ball x r
  let K := closure upperHalfPlane ∩ ball x r
  have hSo : IsOpen S := upperHalfPlane_open.inter isOpen_ball
  have hSc : Convex ℝ S := (convex_halfSpace_im_gt 0).inter (convex_ball x r)
  have hFd : DifferentiableOn ℂ F upperHalfPlane :=
    fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  have hd : ContinuousOn (upperDifferential a b c) upperHalfPlane := by
    apply (hFd.deriv upperHalfPlane_open).continuousOn.congr
    intro z hz
    exact (hF z hz).deriv.symm
  obtain ⟨H,hH,hFH⟩ := exists_extension_of_derivative_sq
    hSo hSc.isPreconnected isOpen_ball (convex_ball x r) inter_subset_right
    (fun z hz => hF z hz.1) (hd.mono inter_subset_left) hh
    (fun z hz => hhn z hz.2)
    (fun z hz => (upperDifferential_sq a b c z).trans (hhsq z hz.2).symm)
  have hSK : S ⊆ K := fun z hz => ⟨subset_closure hz.1,hz.2⟩
  have hKS : K ⊆ closure S := isOpen_ball.closure_inter
  have hEH : EqOn E H K := by
    have hs : EqOn E H S := fun z hz => (hFE hz.1).symm.trans (hFH hz)
    exact hs.of_subset_closure (hE.mono inter_subset_left)
      (hH.continuousOn.mono inter_subset_right) hSK hKS
  have hsquare : EqOn (fun z => (deriv H z)^2) R K := by
    have hs : EqOn (fun z => (deriv H z)^2) R S := by
      intro z hz
      change (deriv H z)^2 = R z
      have he : deriv H z = upperDifferential a b c z :=
        ((hFH.deriv hSo) hz).symm.trans (hF z hz.1).deriv
      rw [he]
      exact upperDifferential_sq a b c z
    exact hs.of_subset_closure
      (((hH.deriv isOpen_ball).continuousOn.pow 2).mono inter_subset_right)
      (hR.continuousOn.mono fun z hz => hball hz.2) hSK hKS
  refine ⟨r,hr,H,hH,hEH,?_⟩
  intro z hz
  have hsq : (deriv H z)^2 = R z := hsquare hz
  refine ⟨hsq,?_,?_⟩
  · have hn : ‖deriv H z‖^2 = ‖upperDifferential a b c z‖^2 := by
      rw [← norm_pow, hsq, upperDifferential_norm_sq]
    nlinarith [norm_nonneg (deriv H z), norm_nonneg (upperDifferential a b c z)]
  · intro he
    have hRz : R z ≠ 0 := inv_ne_zero (hball hz.2)
    exact hRz (by simpa [he] using hsq.symm)

/-- Specialization to the constructed Schwarz--Christoffel primitive;
all derivatives here are tied to its actual upper-half-plane chart. -/
theorem upperMap_exists_local_extension (a b c : ℝ) {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential (b-a) (c-a) t) t)
    (hE : ContinuousOn E (closure upperHalfPlane))
    (hGE : EqOn (upperMap a G) E upperHalfPlane) {x : ℂ}
    (hx : (x-(a:ℂ))*(x-(b:ℂ))*(x-(c:ℂ)) ≠ 0) :
    ∃ r > 0, ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball x r) ∧
      EqOn E H (closure upperHalfPlane ∩ ball x r) ∧
      ∀ z ∈ closure upperHalfPlane ∩ ball x r,
        (deriv H z)^2 = ((z-(a:ℂ))*(z-(b:ℂ))*(z-(c:ℂ)))⁻¹ ∧
        ‖deriv H z‖ = ‖upperDifferential a b c z‖ ∧ deriv H z ≠ 0 :=
  exists_local_extension a b c (fun _ hz => upperMap_hasDeriv a b c hG hz) hE hGE hx

end

end ParentWaveUpperBoundary
