import ActualCrestEndpointResponse
import UniformCrestTransport

/-!
# Signed drift of the actual maximal physical crest endpoint

The quartic response is converted into bounds at the dynamical scale.
The endpoint is the endpoint of the complete actual gate classification,
and the assembled families retain their proved proper paths, density
moduli and original-plane polynomial collision.
-/

namespace ActualCrestEndpointDrift

open Set Function Filter
open scoped Topology
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter GlobalCrestCrossing GlobalCrestClassification
open GlobalCrestSourceGates GlobalCrestFinalCut ActualCrestTransportLimit
open ActualCrestQuarticScale ActualCrestEndpointResponse

noncomputable section

/-- The actual endpoint lies strictly above its limiting radius, with
matching upper and lower bounds at the first dynamical scale. -/
theorem actual_endpoint_signed_bounds {p : ℕ} (hp : 100 ≤ p) {c k₀ r r₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (F : Family p c)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) (he : terminal F r = -1)
    (hr₀ : r₀ ∈ Icc (1/16 : ℝ) (133/2000)) (he₀ : crestTerminal k₀ r₀ = -1) :
    (3/50 : ℝ)*scale p < r-r₀ ∧ r-r₀ < (21/100 : ℝ)*scale p := by
  have hscale := normalized_quartic_scale_bounds (by omega : 17 ≤ p) hc
  have hresponse := actual_endpoint_quartic_response hp hc hk₀ hroot F hr he hr₀ he₀
  constructor <;> linarith only [hscale.1,hscale.2,hresponse.1,hresponse.2]

/-- Consecutive actual maximal endpoints are strictly ordered.  The
statement allows independent choices of actual parameters and curves. -/
theorem actual_endpoint_strict_decrease {p : ℕ} (hp : 100 ≤ p)
    {c c' r r' : ℝ} (hc : ActualTip p c) (hc' : ActualTip (p+1) c')
    (F : Family p c) (F' : Family (p+1) c')
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) (he : terminal F r = -1)
    (hr' : r' ∈ Icc (1/16 : ℝ) (133/2000)) (he' : terminal F' r' = -1) :
    r' < r := by
  obtain ⟨k₀,⟨hk₀,hroot⟩,_⟩ := exists_unique_limiting_parameter
  obtain ⟨r₀,hr₀,he₀,_⟩ := unique_model_endpoint hk₀
  have hr₀' : r₀ ∈ Icc (1/16 : ℝ) (133/2000) :=
    ⟨by linarith [hr₀.1],hr₀.2.le⟩
  have hcurrent := actual_endpoint_signed_bounds hp hc hk₀ hroot F hr he hr₀' he₀
  have hnext := actual_endpoint_signed_bounds (by omega : 100 ≤ p+1)
    hc' hk₀ hroot F' hr' he' hr₀' he₀
  have hnextUpper := hnext.2
  rw [scale_succ] at hnextUpper
  linarith only [hcurrent.1,hnextUpper,scale_pos p]

private theorem scale_hundred_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ => C*scale (n+100)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (1/4 : ℝ)^n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [scale,pow_add,mul_zero,zero_mul] using
    (hbase.mul_const ((1/4 : ℝ)^100)).const_mul C

private theorem endpoint_bounds_tendsto {r₀ : ℝ} {radii : ℕ → ℝ}
    (hb : ∀ n, (3/50 : ℝ)*scale (n+100) < radii n-r₀ ∧
      radii n-r₀ < (21/100 : ℝ)*scale (n+100)) :
    Tendsto radii atTop (𝓝 r₀) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => by
      have hq := scale_pos (n+100)
      have h := (hb n).1
      linarith only [ha,hq,h]
  · intro b hb₀
    have hsmall : ∀ᶠ n : ℕ in atTop, (21/100 : ℝ)*scale (n+100) < b-r₀ :=
      (tendsto_order.mp (scale_hundred_tendsto_zero (21/100))).2
        (b-r₀) (sub_pos.mpr hb₀)
    filter_upwards [hsmall] with n hn
    linarith only [hn,(hb n).2]

/-- A common limiting endpoint and a sequence of actual maximal collars
are constructed.  The signed rate and strict decrease belong to these
same collars, with their complete physical gate set and modulus realization.
The original-plane endpoint is also an exact literal polynomial collision. -/
theorem exists_strictly_decreasing_physical_endpoints :
    ∃ k₀ ∈ parameterInterval, relation k₀ = 0 ∧
      ∃ r₀ ∈ Ioo (663/10000 : ℝ) (133/2000), crestTerminal k₀ r₀ = -1 ∧
        ∃ c : ℕ → ℝ, ∃ hc : ∀ n, ActualTip (n+100) (c n),
          ∃ F : ∀ n, Family (n+100) (c n), ∃ α radii : ℕ → ℝ,
            (∀ n, α n ∈ Ioo (518/1000 : ℝ) (519/1000) ∧
              normalizedReturn (c n) (n+100) (α n : ℂ) = (α n : ℂ) ∧
              radii n ∈ Ioo (663/10000 : ℝ) (133/2000) ∧
              terminal (F n) (radii n) = -1 ∧
              Icc (1/16 : ℝ) (parentOuter (n+100)) ∩
                {s | ActualEndpointGates (c n) (n+100) s (α n) ∧
                  terminalGate (F n) s ∧ fourthTerminalGate (F n) s} =
                    Ico (1/16) (radii n) ∧
              RealizedCollar (by omega) (hc n) (F n) (α n) (radii n) ∧
              (3/50 : ℝ)*scale (n+100) < radii n-r₀ ∧
              radii n-r₀ < (21/100 : ℝ)*scale (n+100) ∧
              ∃ z : ℂ,
                z ∈ ThreeReturnParent.physicalParentSource (c n) (n+100) ∧
                z ∈ ThreeReturnParent.archivedParentSource (c n) (n+100) ∧
                ‖z+((3*criticalValue (c n) (n+100)/4 : ℝ) : ℂ)‖ =
                  criticalValue (c n) (n+100)*radii n ∧
                (((quadraticMap (c n))^[n+100]) z).re = 0 ∧
                0 < (((quadraticMap (c n))^[n+100]) z).im ∧
                ((quadraticMap (c n))^[3*(n+100)]) z =
                  -(criticalValue (c n) (n+100) : ℂ)) ∧
            StrictAnti radii ∧ Tendsto radii atTop (𝓝 r₀) := by
  classical
  obtain ⟨k₀,⟨hk₀,hroot⟩,_⟩ := exists_unique_limiting_parameter
  obtain ⟨r₀,hr₀,he₀,_⟩ := unique_model_endpoint hk₀
  have hr₀' : r₀ ∈ Icc (1/16 : ℝ) (133/2000) :=
    ⟨by linarith [hr₀.1],hr₀.2.le⟩
  choose c hc using fun n : ℕ => exists_actual_tip (n+100) (by omega)
  let F (n : ℕ) : Family (n+100) (c n) :=
    Classical.choice (exists_family (by omega) (hc n))
  choose α hα hfixed radii hr he hanti hunique hcomplete using
    fun n => actual_complete_cut_classification (by omega) (hc n) (F n)
  have hr' (n : ℕ) : radii n ∈ Icc (1/16 : ℝ) (133/2000) :=
    ⟨by linarith [(hr n).1],(hr n).2.le⟩
  have hb (n : ℕ) : (3/50 : ℝ)*scale (n+100) < radii n-r₀ ∧
      radii n-r₀ < (21/100 : ℝ)*scale (n+100) :=
    actual_endpoint_signed_bounds (by omega) (hc n) hk₀ hroot (F n)
      (hr' n) (he n) hr₀' he₀
  refine ⟨k₀,hk₀,hroot,r₀,hr₀,he₀,c,hc,F,α,radii,?_,?_,endpoint_bounds_tendsto hb⟩
  · intro n
    exact ⟨hα n,hfixed n,hr n,he n,hcomplete n,
      UniformCrestTransport.all_period_realize_collar (by omega) (hc n) (F n)
        (hα n) (hr n) (he n),
      (hb n).1,(hb n).2,
      GlobalCrestPhysical.actual_physical_endpoint (by omega) (hc n) (F n) (hr n) (he n)⟩
  · have hstep (n : ℕ) : radii (n+1) < radii n := by
      have hcur := (hb n).1
      have hnxt := (hb (n+1)).2
      rw [show n+1+100 = (n+100)+1 by omega,scale_succ] at hnxt
      linarith only [hcur,hnxt,scale_pos (n+100)]
    have hneg : StrictMono (fun n => -radii n) :=
      strictMono_nat_of_lt_succ (fun n => neg_lt_neg (hstep n))
    intro i j hij
    have h := hneg hij
    linarith only [h]

end
end ActualCrestEndpointDrift
