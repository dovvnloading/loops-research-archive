import Mathlib
import SaturatedTelescope
import QuadraticCylinderCensus

/-!
# Analytic multiplicity of actual quadratic orbit segments

Local order is measured by Mathlib's analyticOrderAt, not by the
number of distinct points in a fiber. The chronology is the actual
spatial orbit of z ↦ z²+c.
-/

namespace LoopsTelescopeRamification

open Filter Set
open LoopsSaturatedTelescope
open scoped Topology

noncomputable section

local instance : DecidableEq ℂ := Classical.decEq ℂ

/-- Number of critical visits before the end of a physical orbit segment. -/
def criticalVisits (c x : ℂ) : ℕ → ℕ
  | 0 => 0
  | n+1 => criticalVisits c x n + if QuadraticEscape.orbit c n x = 0 then 1 else 0

theorem orbit_analytic (c : ℂ) (n : ℕ) (x : ℂ) :
    AnalyticAt ℂ (QuadraticEscape.orbit c n) x := by
  induction n with
  | zero => exact analyticAt_id
  | succ n ih =>
    change AnalyticAt ℂ (fun z => (QuadraticEscape.orbit c n z)^2+c) x
    exact (ih.pow 2).add analyticAt_const

/-- Global factorization with an entire factor nonzero at the anchor.
Each genuine critical visit doubles the exponent; all other steps
preserve it. This also treats repeated visits to the critical point. -/
theorem orbit_ramification_factor (c x : ℂ) (n : ℕ) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧ g x ≠ 0 ∧
      ∀ z, QuadraticEscape.orbit c n z - QuadraticEscape.orbit c n x =
        (z-x)^(2^criticalVisits c x n) * g z := by
  induction n with
  | zero =>
    refine ⟨fun _ => 1, fun _ => analyticAt_const, one_ne_zero, ?_⟩
    intro z
    simp [criticalVisits, QuadraticEscape.orbit]
  | succ n ih =>
    obtain ⟨g, hga, hgn, hg⟩ := ih
    by_cases hx : QuadraticEscape.orbit c n x = 0
    · refine ⟨fun z => (g z)^2, fun z => (hga z).pow 2, pow_ne_zero 2 hgn, ?_⟩
      intro z
      have hz : QuadraticEscape.orbit c n z =
          (z-x)^(2^criticalVisits c x n) * g z := by simpa [hx] using hg z
      change (QuadraticEscape.orbit c n z)^2+c -
        ((QuadraticEscape.orbit c n x)^2+c) =
          (z-x)^(2^criticalVisits c x (n+1)) * (g z)^2
      rw [hx, hz]
      simp only [criticalVisits, if_pos hx, pow_succ (2 : ℕ), pow_mul]
      ring
    · refine ⟨fun z => g z * (QuadraticEscape.orbit c n z +
        QuadraticEscape.orbit c n x),
        fun z => (hga z).mul ((orbit_analytic c n z).add analyticAt_const), ?_, ?_⟩
      · apply mul_ne_zero hgn
        intro h
        have ht : (2 : ℂ) * QuadraticEscape.orbit c n x = 0 := by linear_combination h
        exact hx ((mul_eq_zero.mp ht).resolve_left (by norm_num))
      · intro z
        change (QuadraticEscape.orbit c n z)^2+c -
          ((QuadraticEscape.orbit c n x)^2+c) =
            (z-x)^(2^criticalVisits c x (n+1)) *
              (g z * (QuadraticEscape.orbit c n z + QuadraticEscape.orbit c n x))
        simp only [criticalVisits, if_neg hx, Nat.add_zero]
        calc
          _ = (QuadraticEscape.orbit c n z - QuadraticEscape.orbit c n x) *
                (QuadraticEscape.orbit c n z + QuadraticEscape.orbit c n x) := by ring
          _ = _ := by rw [hg z]; ring

/-- The exact analytic order of the actual iterate at every point.
In particular a visit to zero at the final time is not counted. -/
theorem orbit_analytic_order (c x : ℂ) (n : ℕ) :
    analyticOrderAt (fun z => QuadraticEscape.orbit c n z -
      QuadraticEscape.orbit c n x) x = (2^criticalVisits c x n : ℕ) := by
  have ha : AnalyticAt ℂ (fun z => QuadraticEscape.orbit c n z -
      QuadraticEscape.orbit c n x) x :=
    (orbit_analytic c n x).sub analyticAt_const
  obtain ⟨g, hga, hgn, hg⟩ := orbit_ramification_factor c x n
  apply ha.analyticOrderAt_eq_natCast.mpr
  exact ⟨g, hga x, hgn, Filter.Eventually.of_forall
    (fun z => by simpa [smul_eq_mul] using hg z)⟩

/-- Chronological counting is additive under physical concatenation. -/
theorem criticalVisits_add (c x : ℂ) (m n : ℕ) :
    criticalVisits c x (m+n) = criticalVisits c x m +
      criticalVisits c (QuadraticEscape.orbit c m x) n := by
  induction n with
  | zero => simp [criticalVisits]
  | succ n ih =>
    rw [show m+(n+1) = m+n+1 by omega, criticalVisits, criticalVisits, ih,
      quadratic_orbit_add c m n x]
    omega

/-- Absence of critical visits is exactly zero chronological count. -/
theorem criticalVisits_zero_iff (c x : ℂ) (n : ℕ) :
    criticalVisits c x n = 0 ↔ ∀ j < n, QuadraticEscape.orbit c j x ≠ 0 := by
  induction n with
  | zero => simp [criticalVisits]
  | succ n ih =>
    constructor
    · intro h j hj
      have hn : criticalVisits c x n = 0 := by
        simp only [criticalVisits] at h
        omega
      by_cases he : j = n
      · subst j
        intro hz
        simp [criticalVisits, hz] at h
      · exact ih.mp hn j (by omega)
    · intro h
      have hn := ih.mpr (fun j hj => h j (by omega))
      have hz := h n (by omega)
      simp [criticalVisits, hn, hz]

/-- A single physical quadratic stage has local order two exactly at
zero, and one elsewhere. -/
theorem quadratic_step_order (c x : ℂ) :
    analyticOrderAt (fun z : ℂ => z^2+c-(x^2+c)) x =
      (if x = 0 then (2 : ℕ) else 1) := by
  simpa [QuadraticEscape.orbit, criticalVisits] using orbit_analytic_order c x 1

/-- Actual returns without critical visits have analytic order one. -/
theorem orbit_unramified_order (c x : ℂ) (n : ℕ)
    (h : ∀ j < n, QuadraticEscape.orbit c j x ≠ 0) :
    analyticOrderAt (fun z => QuadraticEscape.orbit c n z -
      QuadraticEscape.orbit c n x) x = 1 := by
  rw [orbit_analytic_order, (criticalVisits_zero_iff c x n).mpr h]
  norm_num

/-- The unique designated critical step contributes its exact local
multiplicity; prefix and suffix are required to have no critical visits. -/
theorem return_order_one_step (c x : ℂ) (a b : ℕ)
    (hp : ∀ j < a, QuadraticEscape.orbit c j x ≠ 0)
    (hs : ∀ j < b, QuadraticEscape.orbit c j
      (QuadraticEscape.orbit c (a+1) x) ≠ 0) :
    analyticOrderAt (fun z => QuadraticEscape.orbit c (a+1+b) z -
      QuadraticEscape.orbit c (a+1+b) x) x =
      (if QuadraticEscape.orbit c a x = 0 then (2 : ℕ) else 1) := by
  rw [orbit_analytic_order, criticalVisits_add,
    (criticalVisits_zero_iff _ _ _).mpr hs]
  have hp0 := (criticalVisits_zero_iff c x a).mpr hp
  by_cases h : QuadraticEscape.orbit c a x = 0 <;>
    simp [criticalVisits, hp0, h]

end

end LoopsTelescopeRamification
