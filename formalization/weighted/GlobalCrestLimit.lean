import GlobalCrestPhysical
import ActualCrestIntegral

/-!
# The archived radial limit belongs to the complete actual parent collar

The analytic limit is imported from the earlier contribution. The new
global classification removes the freedom to select a different component
or a later endpoint elsewhere in the original parent. Restriction preserves
the literal integral, and uniqueness identifies its moving endpoint.
-/

namespace GlobalCrestLimit

open Set Function Filter
open scoped Topology
open NearTwoTip NearTwoShooting LimitingCrest LoopsLimitingCrestParameter
open LimitingCrestQuadraticReturn CrestIntegralLimit
open GlobalCrestCrossing GlobalCrestClassification GlobalCrestPhysical
open GlobalCrestFinalCut

noncomputable section

/-- Restriction changes neither the angular data nor its integral up to
any retained endpoint. The parent normalization is unchanged. -/
theorem restricted_coefficient_eq {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) :
    radialCoefficient p (ActualCrestEndpoint.realAngle (F.restrict hp hc)) r =
      radialCoefficient p (realAngle F) r := by
  unfold radialCoefficient
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hr.1] at hs
  unfold radialIntegrand
  rw [restricted_realAngle_eq hp hc F ⟨hs.1,hs.2.trans hr.2⟩]

/-- Every sequence of globally classified endpoints has the archived
endpoint and coefficient limit. There is no eventual choice of a different
component in this statement. -/
theorem actual_global_coefficients_converge {k₀ : ℝ}
    (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0)
    (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n))
    (radii : ℕ → ℝ)
    (hr : ∀ n, radii n ∈ Ioo (663/10000 : ℝ) (133/2000))
    (he : ∀ n, terminal (F n) (radii n) = -1) :
    ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), crestTerminal k₀ r = -1 ∧
      Tendsto radii atTop (𝓝 r) ∧
      Tendsto (fun n => radialCoefficient (n+17) (realAngle (F n)) (radii n))
        atTop (𝓝 (fullModelCoefficient k₀ r)) ∧
      (1/3 : ℝ) < fullModelCoefficient k₀ r := by
  let G (n : ℕ) := (F n).restrict (by omega) (hc n)
  obtain ⟨r,hr₀,he₀,old,hmem,hlimit,hcollars,hcoeff,hpositive,_⟩ :=
    ActualCrestIntegral.actual_initial_coefficients_converge hk₀ hroot c hc G
  have heq : old =ᶠ[atTop] radii := by
    filter_upwards [hcollars] with n hn
    have hg := global_endpoint_is_initial (by omega) (hc n) (F n) (hr n) (he n)
    exact CrestFirstExit.first_exit_unique (ActualCrestEndpoint.terminal (G n))
      hn.1.1.le hg.1.1.le hn.2.1 hg.2.1 hn.2.2.1 hg.2.2.1
  have hcoeffeq :
      (fun n => radialCoefficient (n+17) (ActualCrestEndpoint.realAngle (G n)) (old n))
        =ᶠ[atTop]
      (fun n => radialCoefficient (n+17) (realAngle (F n)) (radii n)) := by
    filter_upwards [heq] with n hn
    rw [hn]
    exact restricted_coefficient_eq (by omega) (hc n) (F n)
      ⟨by linarith [(hr n).1],(hr n).2.le⟩
  exact ⟨r,hr₀,he₀,(tendsto_congr' heq).mp hlimit,
    (tendsto_congr' hcoeffeq).mp hcoeff,hpositive⟩

/-- One constructed sequence has complete actual parent collars at every
index p≥17, exact original-plane terminal collisions, and the previously
established positive limiting radial coefficient for those same collars. -/
theorem exists_complete_parents_and_positive_limit :
    ∃ k₀ ∈ parameterInterval, relation k₀ = 0 ∧
      ∃ c : ℕ → ℝ, (∀ n, ActualTip (n+17) (c n)) ∧
        ∃ F : ∀ n, Family (n+17) (c n),
          ∃ α radii : ℕ → ℝ,
            (∀ n,
              α n ∈ Ioo (518/1000 : ℝ) (519/1000) ∧
              normalizedReturn (c n) (n+17) (α n : ℂ) = (α n : ℂ) ∧
              radii n ∈ Ioo (663/10000 : ℝ) (133/2000) ∧
              terminal (F n) (radii n) = -1 ∧
              StrictAntiOn (terminal (F n)) (Icc (1/16 : ℝ) (1/8)) ∧
              (∀ s ∈ Icc (1/16 : ℝ) (1/8),
                terminal (F n) s = -1 ↔ s = radii n) ∧
              Icc (1/16 : ℝ) (parentOuter (n+17)) ∩
                {s | GlobalCrestSourceGates.ActualEndpointGates (c n) (n+17) s (α n) ∧
                  terminalGate (F n) s ∧ fourthTerminalGate (F n) s} =
                    Ico (1/16) (radii n)) ∧
            (∀ n, (1/3 : ℝ) <
              radialCoefficient (n+17) (realAngle (F n)) (radii n)) ∧
            (∀ n, ∃ z : ℂ,
              z ∈ ThreeReturnParent.physicalParentSource (c n) (n+17) ∧
              z ∈ ThreeReturnParent.archivedParentSource (c n) (n+17) ∧
              ‖z+((3*criticalValue (c n) (n+17)/4 : ℝ) : ℂ)‖ =
                criticalValue (c n) (n+17)*radii n ∧
              (((quadraticMap (c n))^[n+17]) z).re = 0 ∧
              0 < (((quadraticMap (c n))^[n+17]) z).im ∧
              ((quadraticMap (c n))^[3*(n+17)]) z =
                -(criticalValue (c n) (n+17) : ℂ)) ∧
            ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), crestTerminal k₀ r = -1 ∧
              Tendsto radii atTop (𝓝 r) ∧
              Tendsto (fun n => radialCoefficient (n+17) (realAngle (F n)) (radii n))
                atTop (𝓝 (fullModelCoefficient k₀ r)) ∧
              (1/3 : ℝ) < fullModelCoefficient k₀ r := by
  classical
  obtain ⟨k₀,⟨hk₀,hroot⟩,_⟩ := exists_unique_limiting_parameter
  choose c hc using fun n : ℕ => exists_actual_tip (n+17) (by omega)
  let F (n : ℕ) : Family (n+17) (c n) :=
    Classical.choice (exists_family (by omega) (hc n))
  choose α hα hfixed radii hr he hanti hunique hcomplete using
    fun n => actual_complete_cut_classification (by omega) (hc n) (F n)
  refine ⟨k₀,hk₀,hroot,c,hc,F,α,radii,?_,?_,?_,?_⟩
  · intro n
    exact ⟨hα n,hfixed n,hr n,he n,hanti n,hunique n,hcomplete n⟩
  · intro n
    exact GlobalCrestCoefficient.actual_radialCoefficient_gt_third
      (by omega) (hc n) (F n) ⟨(hr n).1.le,(hr n).2.le⟩
  · intro n
    exact actual_physical_endpoint (by omega) (hc n) (F n) (hr n) (he n)
  · exact actual_global_coefficients_converge hk₀ hroot c hc F radii hr he

end
end GlobalCrestLimit
