import QuadraticPowerNormalForm
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Exact local fiber census for every actual quadratic iterate

The analytic disk chart constructs the physical neighborhood. Its inverse
sends the finite set of all power roots onto the entire local polynomial
fiber. Every noncentral sufficiently close target has exactly the local
multiplicity many distinct inverse points; the central target has one.
-/

namespace LoopsQuadraticLocalFiberCensus

open Set Function Polynomial
open scoped Classical
open QuadraticEscape LoopsTelescopeRamification LoopsQuadraticCylinderCensus
open LoopsQuadraticPowerNormalForm

/-- The complete set of nonzero complex power roots has the full
algebraic cardinality, with repeated roots excluded. -/
theorem complex_nthRootsFinset_card (m : ℕ) (hm : 0 < m)
    (b : ℂ) (hb : b ≠ 0) : (nthRootsFinset m b).card = m := by
  have hζ := Complex.isPrimitiveRoot_exp m (Nat.ne_zero_of_lt hm)
  rw [nthRootsFinset_def,
    Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup hb),
    hζ.card_nthRoots b, if_pos (IsAlgClosed.exists_pow_nat_eq b hm)]

/-- A power root of a target inside the corresponding power-radius
lies inside the source disk. -/
theorem power_root_mem_ball (m : ℕ) (b z : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hb : ‖b‖ < r^m) (hz : z^m = b) :
    z ∈ Metric.ball (0 : ℂ) r := by
  rw [Metric.mem_ball, dist_zero_right]
  have he : ‖z‖^m = ‖b‖ := by rw [← norm_pow, hz]
  by_contra h
  have hrz : r ≤ ‖z‖ := le_of_not_gt h
  have hp := pow_le_pow_left₀ hr hrz m
  rw [he] at hp
  exact (not_lt_of_ge hp) hb

/-- The actual local iterate fiber is exactly the image of all power
roots under the analytic chart inverse. No roots are lost outside the
chart disk and no additional roots remain inside the physical domain. -/
theorem quadratic_chart_localFiber
    (c x : ℂ) (n m : ℕ) (a : ℂ) (r : ℝ) (U : Set ℂ) (φ χ : ℂ → ℂ)
    (hm : 0 < m) (ha : a ≠ 0) (hr : 0 < r)
    (hmapχ : MapsTo χ (Metric.ball (0 : ℂ) r) U)
    (hleft : LeftInvOn χ φ U)
    (hright : RightInvOn χ φ (Metric.ball (0 : ℂ) r))
    (hform : ∀ z ∈ U, orbit c n z-orbit c n x = a*(φ z)^m)
    (w : ℂ) (hw : ‖(w-orbit c n x)/a‖ < r^m) :
    localFiber c n U w =
      (nthRootsFinset m ((w-orbit c n x)/a)).image χ := by
  have hmem (z : ℂ) :
      z ∈ localFiber c n U w ↔ z ∈ U ∧ orbit c n z = w := by
    rw [mem_localFiber, ← orbit_map_eq_iterate]
  ext z
  rw [hmem, Finset.mem_image]
  constructor
  · rintro ⟨hzU, hzw⟩
    have he := hform z hzU
    rw [hzw] at he
    have hp : (φ z)^m = (w-orbit c n x)/a := by
      apply (eq_div_iff ha).mpr
      rw [mul_comm]
      exact he.symm
    exact ⟨φ z, (mem_nthRootsFinset hm _).mpr hp, hleft hzU⟩
  · rintro ⟨q, hq, rfl⟩
    have hp : q^m = (w-orbit c n x)/a :=
      (mem_nthRootsFinset hm _).mp hq
    have hqB : q ∈ Metric.ball (0 : ℂ) r :=
      power_root_mem_ball m _ q r hr.le hw hp
    refine ⟨hmapχ hqB, ?_⟩
    have he := hform (χ q) (hmapχ hqB)
    rw [hright hqB, hp] at he
    have hc : a*((w-orbit c n x)/a) = w-orbit c n x := by
      field_simp [ha] <;> ring
    rw [hc] at he
    linear_combination he

/-- The exact local valence of every finite actual quadratic iterate.
The central target is retained separately, including when the anchor
has repeated critical encounters. The noncentral counts concern all
points in one constructed physical open neighborhood. -/
theorem quadratic_local_fiber_census (c x : ℂ) (n : ℕ) :
    ∃ (U : Set ℂ) (ε : ℝ),
      IsOpen U ∧ x ∈ U ∧ 0 < ε ∧
      localFiber c n U (orbit c n x) = {x} ∧
      ∀ w : ℂ, dist w (orbit c n x) < ε → w ≠ orbit c n x →
        (localFiber c n U w).card = 2^criticalVisits c x n := by
  obtain ⟨a, r, U, φ, χ, ha, hr, hU, hxU, hφ0, hφd,
      hmapφ, hmapχ, hleft, hright, hφa, hχa, hform⟩ :=
    quadratic_power_disk_chart c x n
  let m := 2^criticalVisits c x n
  have hm : 0 < m := by dsimp [m]; positivity
  let ε := ‖a‖*r^m
  have haN : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hε : 0 < ε := mul_pos haN (pow_pos hr m)
  have hcentral : localFiber c n U (orbit c n x) = {x} := by
    ext z
    rw [mem_localFiber, ← orbit_map_eq_iterate, Finset.mem_singleton]
    constructor
    · rintro ⟨hzU, heq⟩
      have he := hform z hzU
      rw [heq, sub_self] at he
      have hp : (φ z)^m = 0 := (mul_eq_zero.mp he.symm).resolve_left ha
      have hz0 : φ z = 0 := by
        by_contra hz0
        exact (pow_ne_zero m hz0) hp
      calc
        z = χ (φ z) := (hleft hzU).symm
        _ = χ (φ x) := congrArg χ (hz0.trans hφ0.symm)
        _ = x := hleft hxU
    · intro hz
      subst z
      exact ⟨hxU, rfl⟩
  refine ⟨U, ε, hU, hxU, hε, hcentral, ?_⟩
  intro w hw hne
  have hw' : ‖(w-orbit c n x)/a‖ < r^m := by
    rw [norm_div]
    apply (div_lt_iff₀ haN).mpr
    simpa only [ε, dist_eq_norm, mul_comm] using hw
  have hb : (w-orbit c n x)/a ≠ 0 := div_ne_zero (sub_ne_zero.mpr hne) ha
  have hroots (q : ℂ) (hq : q ∈ nthRootsFinset m ((w-orbit c n x)/a)) :
      q ∈ Metric.ball (0 : ℂ) r :=
    power_root_mem_ball m _ q r hr.le hw' ((mem_nthRootsFinset hm _).mp hq)
  have hinj : InjOn χ (↑(nthRootsFinset m ((w-orbit c n x)/a)) : Set ℂ) := by
    intro q hq t ht heq
    exact (hright (hroots q hq)).symm.trans
      ((congrArg φ heq).trans (hright (hroots t ht)))
  rw [quadratic_chart_localFiber c x n m a r U φ χ hm ha hr
      hmapχ hleft hright hform w hw',
    Finset.card_image_of_injOn hinj,
    complex_nthRootsFinset_card m hm _ hb]

end LoopsQuadraticLocalFiberCensus
