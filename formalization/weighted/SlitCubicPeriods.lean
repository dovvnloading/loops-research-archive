import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
# A real change of variables for the cubic slit differential

The increasing fractional-linear substitution carries the finite interval
between the first two branch points to the ray beyond the third. Its
Jacobian cancels the cubic square-root density exactly. This is a supporting
period identity, not an extremal-width or attainment theorem.
-/

namespace SlitCubicPeriods

open Set MeasureTheory

noncomputable section

def density (a b c x : ℝ) : ℝ :=
  1 / (Real.sqrt |x-a| * Real.sqrt |x-b| * Real.sqrt |x-c|)

def transfer (a b c x : ℝ) : ℝ := b + (b-a)*(c-b)/(b-x)

private theorem transfer_subs {a b c x : ℝ} (hx : x < b) :
    transfer a b c x - a = (b-a)*(c-x)/(b-x) ∧
    transfer a b c x - b = (b-a)*(c-b)/(b-x) ∧
    transfer a b c x - c = (c-b)*(x-a)/(b-x) := by
  have hn : b-x ≠ 0 := (sub_pos.mpr hx).ne'
  dsimp [transfer]
  constructor
  · field_simp
    ring
  constructor
  · ring
  · field_simp
    ring

theorem transfer_gt_third {a b c x : ℝ} (_hab : a < b) (hbc : b < c)
    (hx : x ∈ Ioo a b) : c < transfer a b c x := by
  have hs := (transfer_subs (a := a) (c := c) hx.2).2.2
  have hp : 0 < (c-b)*(x-a)/(b-x) :=
    div_pos (mul_pos (sub_pos.mpr hbc) (sub_pos.mpr hx.1)) (sub_pos.mpr hx.2)
  linarith

theorem transfer_strictMonoOn {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    StrictMonoOn (transfer a b c) (Ioo a b) := by
  intro x hx y hy hxy
  dsimp [transfer]
  apply add_lt_add_right
  apply (div_lt_div_iff₀ (sub_pos.mpr hx.2) (sub_pos.mpr hy.2)).2
  have hp : 0 < (b-a)*(c-b) := mul_pos (sub_pos.mpr hab) (sub_pos.mpr hbc)
  nlinarith

theorem transfer_image {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    transfer a b c '' Ioo a b = Ioi c := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact transfer_gt_third hab hbc hx
  · intro hy
    change c < y at hy
    have hyb : 0 < y-b := sub_pos.mpr (hbc.trans hy)
    have hk : 0 < (b-a)*(c-b) := mul_pos (sub_pos.mpr hab) (sub_pos.mpr hbc)
    let x := b - (b-a)*(c-b)/(y-b)
    have hxb : x < b := by
      dsimp [x]
      linarith [div_pos hk hyb]
    have hxa : a < x := by
      have hq : (b-a)*(c-b)/(y-b) < b-a := by
        apply (div_lt_iff₀ hyb).2
        have hh : c-b < y-b := by linarith
        exact mul_lt_mul_of_pos_left hh (sub_pos.mpr hab)
      dsimp [x]
      linarith
    refine ⟨x,⟨hxa,hxb⟩,?_⟩
    dsimp [transfer,x]
    rw [sub_sub_cancel]
    have he : (b-a)*(c-b)/((b-a)*(c-b)/(y-b)) = y-b := by
      field_simp [hk.ne',hyb.ne']
      exact div_self hk.ne'
    rw [he]
    ring

theorem transfer_hasDerivAt {a b c x : ℝ} (hx : x < b) :
    HasDerivAt (transfer a b c) ((b-a)*(c-b)/(b-x)^2) x := by
  have h := ((hasDerivAt_const x ((b-a)*(c-b))).div
    ((hasDerivAt_const x b).sub (hasDerivAt_id x))
    (sub_pos.mpr hx).ne').const_add b
  change HasDerivAt (fun t : ℝ => b + (b-a)*(c-b)/(b-t)) _ _
  convert! h using 1; simp

private theorem denominator_sq (a b c x : ℝ) :
    (Real.sqrt |x-a| * Real.sqrt |x-b| * Real.sqrt |x-c|)^2 =
      |x-a| * |x-b| * |x-c| := by
  simp only [mul_pow, Real.sq_sqrt (abs_nonneg _)]

theorem transfer_density_jacobian {a b c x : ℝ}
    (hab : a < b) (hbc : b < c) (hx : x ∈ Ioo a b) :
    ((b-a)*(c-b)/(b-x)^2) * density a b c (transfer a b c x) =
      density a b c x := by
  have hxa : 0 < x-a := sub_pos.mpr hx.1
  have hbx : 0 < b-x := sub_pos.mpr hx.2
  have hcx : 0 < c-x := sub_pos.mpr (hx.2.trans hbc)
  have hT := transfer_gt_third hab hbc hx
  have hTa : 0 < transfer a b c x-a := sub_pos.mpr ((hab.trans hbc).trans hT)
  have hTb : 0 < transfer a b c x-b := sub_pos.mpr (hbc.trans hT)
  have hTc : 0 < transfer a b c x-c := sub_pos.mpr hT
  let D := Real.sqrt |x-a| * Real.sqrt |x-b| * Real.sqrt |x-c|
  let E := Real.sqrt |transfer a b c x-a| *
    Real.sqrt |transfer a b c x-b| * Real.sqrt |transfer a b c x-c|
  have hD : 0 < D := by
    dsimp [D]
    apply mul_pos (mul_pos (Real.sqrt_pos.2 (abs_pos.mpr hxa.ne'))
      (Real.sqrt_pos.2 (abs_pos.mpr (sub_neg.mpr hx.2).ne)))
      (Real.sqrt_pos.2 (abs_pos.mpr (sub_neg.mpr (hx.2.trans hbc)).ne))
  have hE : 0 < E := by
    dsimp [E]
    positivity
  let K := (b-a)*(c-b)
  have hK : 0 < K := mul_pos (sub_pos.mpr hab) (sub_pos.mpr hbc)
  have hsD : D^2 = (x-a)*(b-x)*(c-x) := by
    dsimp [D]
    rw [denominator_sq, abs_of_pos hxa, abs_of_neg (sub_neg.mpr hx.2),
      abs_of_neg (sub_neg.mpr (hx.2.trans hbc))]
    ring
  have hsE : E^2 = K^2*D^2/(b-x)^4 := by
    dsimp [E]
    rw [denominator_sq, abs_of_pos hTa, abs_of_pos hTb, abs_of_pos hTc]
    rcases transfer_subs (a := a) (c := c) hx.2 with ⟨h1,h2,h3⟩
    rw [h1,h2,h3,hsD]
    dsimp [K]
    field_simp
  have hs : (K*D/(b-x)^2)^2 = E^2 := by
    rw [hsE]
    field_simp [hbx.ne']
  have hden : E = K*D/(b-x)^2 := by
    have hp : 0 < K*D/(b-x)^2 := by positivity
    nlinarith
  change (K/(b-x)^2) * (1/E) = 1/D
  rw [hden]
  field_simp

/-- The two opposite boundary periods of the cubic differential agree.
This is an identity of the actual improper real integrals. -/
theorem ray_period_eq_finite_period {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    (∫ x in Ioi c, density a b c x) = ∫ x in Ioo a b, density a b c x := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x hx => (transfer_hasDerivAt (a := a) (c := c) hx.2).hasDerivWithinAt)
    (transfer_strictMonoOn hab hbc).injOn (density a b c)
  rw [transfer_image hab hbc] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  have hp : 0 ≤ (b-a)*(c-b)/(b-x)^2 := by positivity
  simpa only [abs_of_nonneg hp, smul_eq_mul] using
    transfer_density_jacobian hab hbc hx

end
end SlitCubicPeriods
