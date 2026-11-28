import QuadraticProjectiveUniversal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Continuity of the universal projective remainder

The same polynomial quotient can be evaluated along a varying quartic
correction.  Continuity is proved for this joint evaluation, so the
parameter-dependent correction does not require separate choices of
pointwise remainder polynomials.
-/

noncomputable section

namespace LoopsQuadraticProjective

open Polynomial Filter
open scoped Topology

/-- Joint evaluation remains continuous when both dynamical variables vary. -/
theorem continuousAt_bivariate_eval (Q : (ℂ[X])[X])
    {e q : ℂ → ℂ} {t : ℂ} (he : ContinuousAt e t) (hq : ContinuousAt q t) :
    ContinuousAt (fun z => Q.eval₂ (evalRingHom (e z)) (q z)) t := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [eval₂_add, Pi.add_def] using hP.add hQ
  | monomial n P =>
    simpa only [eval₂_monomial, coe_evalRingHom, Pi.mul_def, Pi.pow_def,
      Function.comp_def] using
      (P.continuousAt.comp he).mul (hq.pow n)

theorem continuousAt_denPoly (k : ℕ)
    {e q : ℂ → ℂ} {t : ℂ} (he : ContinuousAt e t) (hq : ContinuousAt q t) :
    ContinuousAt (fun z => (denPoly (e z) k).eval (q z)) t := by
  simpa only [eval₂_eq_eval_map, map_denU] using
    continuousAt_bivariate_eval (denU k) he hq

theorem continuousAt_remPoly (k : ℕ)
    {e q : ℂ → ℂ} {t : ℂ} (he : ContinuousAt e t) (hq : ContinuousAt q t) :
    ContinuousAt (fun z => (remPoly (e z) k).eval (q z)) t := by
  simpa only [eval₂_eq_eval_map, map_remU] using
    continuousAt_bivariate_eval (remU k) he hq

/-- The regular projective denominator stays nonzero near a zero multiplier,
also when the quartic correction varies with the parameter. -/
theorem denPoly_eventually_ne_zero (k : ℕ) (hk : 1 ≤ k)
    {e q : ℂ → ℂ} {t : ℂ} (he : ContinuousAt e t) (hq : ContinuousAt q t)
    (hq0 : q t = 0) :
    ∀ᶠ z in 𝓝 t, (denPoly (e z) k).eval (q z) ≠ 0 := by
  apply (continuousAt_denPoly k he hq).eventually_ne
  rw [hq0, denPoly_eval_zero (e t) k hk]
  norm_num

end LoopsQuadraticProjective
