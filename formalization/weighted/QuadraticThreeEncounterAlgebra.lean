import Mathlib

/-!
# Three ordered quadratic encounters cannot disappear through the fourth jet

For `h_a(u) = u + a*u^2`, the coefficients of `u^2`, `u^3`, and `u^4`
in `h_d (h_b (h_a u))` are the three expressions below. Their simultaneous
vanishing forces all three encounter coefficients to vanish. The limiting
version retains this conclusion for convergent encounter coefficients.

This module supplies the algebraic part of an actual-quadratic orbit
factorization; it does not by itself assert that a renormalization has
three encounters or that its intervening dynamics disappear in the limit.
-/

namespace QuadraticThreeEncounterAlgebra

open Filter
open scoped Topology

/-- A normalized quadratic encounter, with derivative one at the origin. -/
def encounter (a u : ℂ) : ℂ := u + a*u^2

/-- Exact polynomial expansion, including the entire higher-order remainder.
Thus the three coefficient expressions used below are computed from the
composition itself. -/
theorem three_encounter_expansion (a b d u : ℂ) :
    encounter d (encounter b (encounter a u)) =
      u + (a+b+d)*u^2 + (2*a*b+2*d*(a+b))*u^3 +
      (a^2*b+d*((a+b)^2+4*a*b))*u^4 +
      u^5*d*((6*a^2*b+4*a*b^2) + (2*a^3*b+6*a^2*b^2)*u +
        4*a^3*b^2*u^2 + a^4*b^2*u^3) := by
  unfold encounter
  ring

/-- The three nonidentity coefficients through degree four of an ordered
composition of three tangent-to-identity quadratics determine whether all
three encounter coefficients vanish. -/
theorem three_encounter_flat (a b d : ℂ)
    (hA : a + b + d = 0)
    (hB : 2*a*b + 2*d*(a+b) = 0)
    (hC : a^2*b + d*((a+b)^2 + 4*a*b) = 0) :
    a = 0 ∧ b = 0 ∧ d = 0 := by
  have hd : d = -a-b := by linear_combination hA
  rw [hd] at hB hC
  have hq : a^2 + a*b + b^2 = 0 := by
    linear_combination -(1/2 : ℂ) * hB
  have hp : (a*b)*(4*a+5*b) = 0 := by
    linear_combination -hC - (a+b)*hq
  have ha : a = 0 := by
    rcases mul_eq_zero.mp hp with hab | hlin
    · rcases mul_eq_zero.mp hab with ha | hb
      · exact ha
      · have hs : a*a = 0 := by simpa [hb, pow_two] using hq
        rcases mul_eq_zero.mp hs with ha | ha <;> exact ha
    · have hb : b = -(4/5 : ℂ)*a := by
        linear_combination (1/5 : ℂ) * hlin
      rw [hb] at hq
      have hs : a*a = 0 := by
        linear_combination (25/21 : ℂ) * hq
      rcases mul_eq_zero.mp hs with ha | ha <;> exact ha
  have hb : b = 0 := by
    have hs : b*b = 0 := by simpa [ha, pow_two] using hq
    rcases mul_eq_zero.mp hs with hb | hb <;> exact hb
  refine ⟨ha, hb, ?_⟩
  simpa [ha, hb] using hA

/-- Exact equivalence for the ordered three-encounter fourth jet. -/
theorem three_encounter_flat_iff (a b d : ℂ) :
    (a+b+d = 0 ∧ 2*a*b + 2*d*(a+b) = 0 ∧
      a^2*b + d*((a+b)^2 + 4*a*b) = 0) ↔
    (a = 0 ∧ b = 0 ∧ d = 0) := by
  constructor
  · rintro ⟨hA, hB, hC⟩
    exact three_encounter_flat a b d hA hB hC
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

/-- The first two nonidentity coefficients can cancel for three nonzero
complex encounters. The next coefficient detects that cancellation.
The hypothesis is the primitive-cube-root polynomial. -/
theorem three_encounter_two_jet_cancellation (w : ℂ)
    (hw : w^2 + w + 1 = 0) :
    (1+w+(-1-w) = 0) ∧
    (2*1*w + 2*(-1-w)*(1+w) = 0) ∧
    (1^2*w + (-1-w)*((1+w)^2 + 4*1*w) ≠ 0) := by
  have hA : (1 : ℂ)+w+(-1-w) = 0 := by ring
  have hB : (2 : ℂ)*1*w + 2*(-1-w)*(1+w) = 0 := by
    linear_combination -2 * hw
  refine ⟨hA, hB, ?_⟩
  intro hC
  have h := three_encounter_flat 1 w (-1-w) hA hB hC
  exact one_ne_zero h.1

/-- No nonzero convergent three-encounter profile has a composition whose
second, third and fourth coefficients all tend to zero. In a critical
quadratic coordinate these are the fourth, sixth and eighth coefficients.
The convergence of the encounter profile is an explicit hypothesis. -/
theorem three_encounter_limit_flat
    (a b d : ℕ → ℂ) (α β δ : ℂ)
    (ha : Tendsto a atTop (𝓝 α))
    (hb : Tendsto b atTop (𝓝 β))
    (hd : Tendsto d atTop (𝓝 δ))
    (hA : Tendsto (fun n => a n + b n + d n) atTop (𝓝 0))
    (hB : Tendsto (fun n => 2*a n*b n + 2*d n*(a n+b n))
      atTop (𝓝 0))
    (hC : Tendsto (fun n => (a n)^2*b n + d n*((a n+b n)^2 + 4*a n*b n))
      atTop (𝓝 0)) :
    α = 0 ∧ β = 0 ∧ δ = 0 := by
  have hA' : Tendsto (fun n => a n + b n + d n) atTop (𝓝 (α+β+δ)) :=
    (ha.add hb).add hd
  have hB' : Tendsto (fun n => 2*a n*b n + 2*d n*(a n+b n))
      atTop (𝓝 (2*α*β + 2*δ*(α+β))) :=
    ((tendsto_const_nhds.mul ha).mul hb).add
      ((tendsto_const_nhds.mul hd).mul (ha.add hb))
  have hC' : Tendsto
      (fun n => (a n)^2*b n + d n*((a n+b n)^2 + 4*a n*b n))
      atTop (𝓝 (α^2*β + δ*((α+β)^2 + 4*α*β))) :=
    ((ha.pow 2).mul hb).add
      (hd.mul (((ha.add hb).pow 2).add ((tendsto_const_nhds.mul ha).mul hb)))
  exact three_encounter_flat α β δ
    (tendsto_nhds_unique hA' hA)
    (tendsto_nhds_unique hB' hB)
    (tendsto_nhds_unique hC' hC)

#print axioms three_encounter_expansion
#print axioms three_encounter_flat
#print axioms three_encounter_flat_iff
#print axioms three_encounter_two_jet_cancellation
#print axioms three_encounter_limit_flat

end QuadraticThreeEncounterAlgebra
