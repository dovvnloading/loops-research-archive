import TelescopeRamification
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Analytic power coordinates for every finite quadratic iterate

The exact nonvanishing factor of the actual iterate produces a normalized
analytic root near the anchor. Its product with the translated source
coordinate has derivative one. An actual analytic inverse then realizes
every finite critical multiplicity as a power map, including repeated
critical encounters.
-/

namespace LoopsQuadraticPowerNormalForm

open Set Function Filter
open scoped Topology
open QuadraticEscape LoopsTelescopeRamification

/-- A positive-order analytic factor constructs mutually inverse local
analytic coordinates. The coordinate derivative is normalized to one;
the nonzero leading factor is retained in the target coordinate. -/
theorem analytic_factor_power_chart (f g : ℂ → ℂ) (x : ℂ) (m : ℕ)
    (hm : 0 < m) (hg : ∀ z, AnalyticAt ℂ g z) (hg0 : g x ≠ 0)
    (hfactor : ∀ z, f z-f x = (z-x)^m*g z) :
    ∃ (U V : Set ℂ) (φ χ : ℂ → ℂ),
      IsOpen U ∧ x ∈ U ∧ IsOpen V ∧ (0 : ℂ) ∈ V ∧
      φ x = 0 ∧ HasDerivAt φ 1 x ∧
      MapsTo φ U V ∧ MapsTo χ V U ∧
      LeftInvOn χ φ U ∧ RightInvOn χ φ V ∧
      AnalyticOnNhd ℂ φ U ∧ AnalyticOnNhd ℂ χ V ∧
      ∀ z ∈ U, f z-f x = g x*(φ z)^m := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hm
  let S : Set ℂ := {z | g z/g x ∈ Complex.slitPlane}
  have hgcont : Continuous g :=
    continuous_iff_continuousAt.mpr (fun z => (hg z).continuousAt)
  have hS : IsOpen S :=
    Complex.isOpen_slitPlane.preimage (hgcont.div_const (g x))
  have hxS : x ∈ S := by
    change g x/g x ∈ Complex.slitPlane
    rw [div_self hg0]
    exact Complex.one_mem_slitPlane
  let R : ℂ → ℂ := fun z =>
    Complex.exp (Complex.log (g z/g x)/(m : ℂ))
  have hRa (z : ℂ) (hz : z ∈ S) : AnalyticAt ℂ R z := by
    change AnalyticAt ℂ
      (fun w => Complex.exp (Complex.log (g w/g x)/(m : ℂ))) z
    exact (((hg z).div_const.clog hz).div_const).cexp
  have hRx : R x = 1 := by simp [R, div_self hg0]
  have hRpow (z : ℂ) (hz : z ∈ S) : R z^m = g z/g x := by
    dsimp [R]
    rw [← Complex.exp_nat_mul]
    have he : (m : ℂ)*(Complex.log (g z/g x)/(m : ℂ)) =
        Complex.log (g z/g x) := by
      field_simp [hmC] <;> ring
    rw [he, Complex.exp_log (Complex.slitPlane_ne_zero hz)]
  let φ : ℂ → ℂ := fun z => (z-x)*R z
  have hφa (z : ℂ) (hz : z ∈ S) : AnalyticAt ℂ φ z :=
    (analyticAt_id.sub analyticAt_const).mul (hRa z hz)
  have hφ0 : φ x = 0 := by simp [φ]
  have hφd : HasDerivAt φ 1 x := by
    have h := ((hasDerivAt_id x).sub_const x).mul
      ((hRa x hxS).differentiableAt.hasDerivAt)
    simpa only [φ, id_eq, hRx, one_mul, sub_self, zero_mul, add_zero] using h
  have hφax : AnalyticAt ℂ φ x := hφa x hxS
  have hdne : deriv φ x ≠ 0 := by rw [hφd.deriv]; norm_num
  let E : OpenPartialHomeomorph ℂ ℂ :=
    (hφax.hasStrictDerivAt.hasStrictFDerivAt_equiv hdne).toOpenPartialHomeomorph φ
  let χ : ℂ → ℂ := E.symm
  have hxE : x ∈ E.source :=
    (hφax.hasStrictDerivAt.hasStrictFDerivAt_equiv hdne).mem_toOpenPartialHomeomorph_source
  have hχa : AnalyticAt ℂ χ (φ x) := hφax.analyticAt_localInverse hdne
  let W : Set ℂ := {w | AnalyticAt ℂ χ w}
  let U : Set ℂ := (E.source ∩ E ⁻¹' W) ∩ S
  let V : Set ℂ := φ '' U
  have hU : IsOpen U :=
    (E.isOpen_inter_preimage (isOpen_analyticAt ℂ χ)).inter hS
  have hxU : x ∈ U := ⟨⟨hxE, hχa⟩, hxS⟩
  have hV : IsOpen V :=
    E.isOpen_image_of_subset_source hU (fun _ hz => hz.1.1)
  have hleft : LeftInvOn χ φ U := fun _ hz => E.left_inv hz.1.1
  have hmapχ : MapsTo χ V U := by
    rintro w ⟨z, hz, rfl⟩
    simpa only [hleft hz] using hz
  have hright : RightInvOn χ φ V := by
    rintro w ⟨z, hz, rfl⟩
    rw [hleft hz]
  refine ⟨U, V, φ, χ, hU, hxU, hV, ⟨x, hxU, hφ0⟩,
    hφ0, hφd, (fun z hz => ⟨z, hz, rfl⟩), hmapχ,
    hleft, hright, (fun z hz => hφa z hz.2), ?_, ?_⟩
  · rintro w ⟨z, hz, rfl⟩
    exact hz.1.2
  · intro z hz
    rw [hfactor]
    dsimp [φ]
    rw [mul_pow, hRpow z hz.2]
    field_simp [hg0] <;> ring

/-- Every actual finite quadratic iterate has analytic power coordinates
of exactly the multiplicity supplied by its critical-visit count. No
critical-avoidance or single-encounter hypothesis is required. -/
theorem quadratic_power_normal_form (c x : ℂ) (n : ℕ) :
    ∃ (a : ℂ) (U V : Set ℂ) (φ χ : ℂ → ℂ),
      a ≠ 0 ∧ IsOpen U ∧ x ∈ U ∧ IsOpen V ∧ (0 : ℂ) ∈ V ∧
      φ x = 0 ∧ HasDerivAt φ 1 x ∧
      MapsTo φ U V ∧ MapsTo χ V U ∧
      LeftInvOn χ φ U ∧ RightInvOn χ φ V ∧
      AnalyticOnNhd ℂ φ U ∧ AnalyticOnNhd ℂ χ V ∧
      ∀ z ∈ U,
        orbit c n z-orbit c n x = a*(φ z)^(2^criticalVisits c x n) := by
  obtain ⟨g, hga, hg0, hfactor⟩ := orbit_ramification_factor c x n
  obtain ⟨U, V, φ, χ, hU, hxU, hV, h0V, hφ0, hφd,
      hmapφ, hmapχ, hleft, hright, hφa, hχa, hform⟩ :=
    analytic_factor_power_chart (orbit c n) g x (2^criticalVisits c x n)
      (by positivity) hga hg0 hfactor
  exact ⟨g x, U, V, φ, χ, hg0, hU, hxU, hV, h0V, hφ0, hφd,
    hmapφ, hmapχ, hleft, hright, hφa, hχa, hform⟩

/-- The source chart can be made onto an actual round disk. This
normalization makes all rotations of the power coordinate available
inside the same physical source neighborhood. -/
theorem quadratic_power_disk_chart (c x : ℂ) (n : ℕ) :
    ∃ (a : ℂ) (r : ℝ) (U : Set ℂ) (φ χ : ℂ → ℂ),
      a ≠ 0 ∧ 0 < r ∧ IsOpen U ∧ x ∈ U ∧
      φ x = 0 ∧ HasDerivAt φ 1 x ∧
      MapsTo φ U (Metric.ball (0 : ℂ) r) ∧
      MapsTo χ (Metric.ball (0 : ℂ) r) U ∧
      LeftInvOn χ φ U ∧ RightInvOn χ φ (Metric.ball (0 : ℂ) r) ∧
      AnalyticOnNhd ℂ φ U ∧
      AnalyticOnNhd ℂ χ (Metric.ball (0 : ℂ) r) ∧
      ∀ z ∈ U,
        orbit c n z-orbit c n x = a*(φ z)^(2^criticalVisits c x n) := by
  obtain ⟨a, U, V, φ, χ, ha, hU, hxU, hV, h0V, hφ0, hφd,
      hmapφ, hmapχ, hleft, hright, hφa, hχa, hform⟩ :=
    quadratic_power_normal_form c x n
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV 0 h0V
  let S := U ∩ φ ⁻¹' Metric.ball (0 : ℂ) r
  have hφcont : ContinuousOn φ U := fun z hz => (hφa z hz).continuousAt.continuousWithinAt
  have hS : IsOpen S := hφcont.isOpen_inter_preimage hU Metric.isOpen_ball
  have hxS : x ∈ S := ⟨hxU, by simpa only [hφ0] using Metric.mem_ball_self hr⟩
  have hχmap : MapsTo χ (Metric.ball (0 : ℂ) r) S := by
    intro w hw
    exact ⟨hmapχ (hrV hw), by
      change φ (χ w) ∈ Metric.ball (0 : ℂ) r
      rwa [hright (hrV hw)]⟩
  exact ⟨a, r, S, φ, χ, ha, hr, hS, hxS, hφ0, hφd,
    (fun _ hz => hz.2), hχmap, (fun _ hz => hleft hz.1),
    (fun _ hw => hright (hrV hw)), (fun z hz => hφa z hz.1),
    (fun w hw => hχa w (hrV hw)), (fun z hz => hform z hz.1)⟩

end LoopsQuadraticPowerNormalForm
