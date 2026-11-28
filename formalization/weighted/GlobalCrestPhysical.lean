import GlobalCrestFinalCut
import GlobalCrestCoefficient
import ActualCrestProperReturn
import ActualCrestEndpoint

/-!
# Full-parent actual geometry and the original-plane terminal collision

Every candidate parent circle lies in the actual proper return component.
The globally classified endpoint is the same literal polynomial collision
used by the short-window theory; no independent geometric model is inserted.
-/

namespace GlobalCrestPhysical

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open GlobalCrestCrossing GlobalCrestOrder GlobalCrestClassification
open GlobalCrestFinalCut
open ThreeReturnParent ActualCrestProperReturn

noncomputable section

def fullParentDisk : Set ℂ := {z | ‖z+(3/4 : ℂ)‖ ≤ 1/8}

/-- The complete disk swept out by the full parent, including the
excluded outer radii, belongs to the actual proper central p-return. -/
theorem fullParentDisk_subset_parent {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : fullParentDisk ⊆ parentSource c p := by
  intro z hz
  have hzn : ‖z‖ ≤ 23/20 := by
    have h : ‖z‖ ≤ ‖z+(3/4 : ℂ)‖+‖(3/4 : ℂ)‖ := by
      simpa only [sub_neg_eq_add,norm_neg] using norm_le_norm_sub_add z (-(3/4 : ℂ))
    norm_num at h
    change ‖z+(3/4 : ℂ)‖ ≤ 1/8 at hz
    linarith
  exact actual_parent_exhaustion hp hc hzn ((first_image_small hp hc hz).trans (by norm_num))

/-- Physical full-parent inclusion with the original scale and center. -/
theorem physical_fullParentDisk_subset {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    {w : ℂ | ‖w+((3*criticalValue c p/4 : ℝ) : ℂ)‖ ≤ criticalValue c p/8} ⊆
      physicalParentSource c p ∩ archivedParentSource c p := by
  intro w hw
  let d := criticalValue c p
  have hd : 0 < d := hc.2.1
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hz : w/(d : ℂ) ∈ fullParentDisk := by
    change ‖w/(d : ℂ)+(3/4 : ℂ)‖ ≤ 1/8
    have he : w/(d : ℂ)+(3/4 : ℂ) = (w+((3*d/4 : ℝ) : ℂ))/(d : ℂ) := by
      push_cast
      field_simp
    rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    change ‖w+((3*d/4 : ℝ) : ℂ)‖ ≤ _ at hw
    linarith
  have hparent : w ∈ physicalParentSource c p := by
    refine ⟨w/(d : ℂ),fullParentDisk_subset_parent hp hc hz,?_⟩
    change (d : ℂ)*(w/(d : ℂ)) = w
    field_simp
  exact ⟨hparent,physical_parent_subset_archived c p hc.2.1
    (actual_parent_restriction hp hc) (actual_parent_scale_bound hp hc) hparent⟩

/-- Restriction to the old endpoint window preserves the literal
terminal function, so its previously proved limit refers to this branch. -/
theorem restricted_terminal_eq {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) :
    ActualCrestEndpoint.terminal (F.restrict hp hc) s = terminal F s := by
  unfold ActualCrestEndpoint.terminal ActualCrestEndpoint.point terminal point
  rw [ActualCrestEndpoint.radiusProjection_eq hs,
    radiusProjection_eq (show s ∈ Icc (1/16 : ℝ) (1/8) from
      ⟨hs.1,hs.2.trans (by norm_num)⟩)]
  rfl

theorem restricted_realAngle_eq {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) :
    ActualCrestEndpoint.realAngle (F.restrict hp hc) s = realAngle F s := by
  unfold ActualCrestEndpoint.realAngle realAngle
  rw [ActualCrestEndpoint.radiusProjection_eq hs,
    radiusProjection_eq (show s ∈ Icc (1/16 : ℝ) (1/8) from
      ⟨hs.1,hs.2.trans (by norm_num)⟩)]
  rfl

/-- The global endpoint is also the archived first-exit endpoint; there
is no freedom to choose a different endpoint for the limit theorem. -/
theorem global_endpoint_is_initial {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hr : r ∈ Ioo (663/10000 : ℝ) (133/2000)) (hzero : terminal F r = -1) :
    ActualCrestEndpoint.InitialCollar (F.restrict hp hc) r := by
  have hr' : r ∈ Ioo (1/16 : ℝ) (133/2000) :=
    ⟨by linarith [hr.1],hr.2⟩
  have hzero' : ActualCrestEndpoint.terminal (F.restrict hp hc) r = -1 := by
    rw [restricted_terminal_eq hp hc F ⟨hr'.1.le,hr'.2.le⟩]
    exact hzero
  have hbefore : ∀ s ∈ Ico (1/16 : ℝ) r,
      -1 < ActualCrestEndpoint.terminal (F.restrict hp hc) s := by
    intro s hs
    have hs' : s ∈ Icc (1/16 : ℝ) (133/2000) := ⟨hs.1,hs.2.le.trans hr'.2.le⟩
    rw [restricted_terminal_eq hp hc F hs']
    have h := actual_terminal_strictAnti hp hc F
      (show s ∈ Icc (1/16 : ℝ) (1/8) from ⟨hs.1,by linarith [hs.2,hr.2]⟩)
      (show r ∈ Icc (1/16 : ℝ) (1/8) by constructor <;> linarith [hr.1,hr.2]) hs.2
    rwa [hzero] at h
  exact ⟨hr',hzero',hbefore,CrestFirstExit.first_exit_component
    (ActualCrestEndpoint.terminal (F.restrict hp hc)) hr' hzero' hbefore⟩

/-- The full-parent endpoint gives an exact original-plane collision,
at a point in the same physical proper return and original archive component. -/
theorem actual_physical_endpoint {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hr : r ∈ Ioo (663/10000 : ℝ) (133/2000)) (hzero : terminal F r = -1) :
    ∃ z : ℂ, z ∈ physicalParentSource c p ∧ z ∈ archivedParentSource c p ∧
      ‖z+((3*criticalValue c p/4 : ℝ) : ℂ)‖ = criticalValue c p*r ∧
      (((quadraticMap c)^[p]) z).re = 0 ∧
      0 < (((quadraticMap c)^[p]) z).im ∧
      ((quadraticMap c)^[3*p]) z = -(criticalValue c p : ℂ) := by
  obtain ⟨z,hcircle,hre,him,hend⟩ := ActualCrestEndpoint.unscaled_endpoint hp hc
    (F.restrict hp hc) (global_endpoint_is_initial hp hc F hr hzero)
  have hz : ‖z+((3*criticalValue c p/4 : ℝ) : ℂ)‖ ≤ criticalValue c p/8 := by
    rw [hcircle]
    have h := mul_le_mul_of_nonneg_left
      (show r ≤ (1/8 : ℝ) by linarith [hr.2]) hc.2.1.le
    linarith
  have hmem := physical_fullParentDisk_subset hp hc hz
  exact ⟨z,hmem.1,hmem.2,hcircle,hre,him,hend⟩

/-- Parameters, the full crossing family, the fixed cut, and the unique
complete parent collar are all constructed for every return index p≥17. -/
theorem exists_actual_complete_parent (p : ℕ) (hp : 17 ≤ p) :
    ∃ c : ℝ, ActualTip p c ∧ ∃ F : Family p c,
      ∃ α ∈ Ioo (518/1000 : ℝ) (519/1000),
        normalizedReturn c p (α : ℂ) = (α : ℂ) ∧
        ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000),
          terminal F r = -1 ∧
          StrictAntiOn (terminal F) (Icc (1/16 : ℝ) (1/8)) ∧
          (∀ s ∈ Icc (1/16 : ℝ) (1/8), terminal F s = -1 ↔ s = r) ∧
          Icc (1/16 : ℝ) (parentOuter p) ∩
            {s | GlobalCrestSourceGates.ActualEndpointGates c p s α ∧
              terminalGate F s ∧ fourthTerminalGate F s} =
              Ico (1/16) r ∧
          (1/3 : ℝ) < CrestIntegralLimit.radialCoefficient p (realAngle F) r ∧
          ∃ z : ℂ, z ∈ physicalParentSource c p ∧ z ∈ archivedParentSource c p ∧
            ‖z+((3*criticalValue c p/4 : ℝ) : ℂ)‖ = criticalValue c p*r ∧
            (((quadraticMap c)^[p]) z).re = 0 ∧
            0 < (((quadraticMap c)^[p]) z).im ∧
            ((quadraticMap c)^[3*p]) z = -(criticalValue c p : ℂ) := by
  obtain ⟨c,hc⟩ := exists_actual_tip p hp
  obtain ⟨F⟩ := exists_family hp hc
  obtain ⟨α,hα,hfixed,r,hr,hzero,hanti,hunique,hcomplete⟩ :=
    actual_complete_cut_classification hp hc F
  exact ⟨c,hc,F,α,hα,hfixed,r,hr,hzero,hanti,hunique,hcomplete,
    GlobalCrestCoefficient.actual_radialCoefficient_gt_third hp hc F ⟨hr.1.le,hr.2.le⟩,
    actual_physical_endpoint hp hc F hr hzero⟩

end
end GlobalCrestPhysical
