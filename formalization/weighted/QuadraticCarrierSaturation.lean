import LocalDegreeExhaustion
import QuadraticLocalNormalForm
import QuadraticEscapeFullness
import IteratedCarrierIsolation

/-!
# Actual primitive quadratic carriers are saturated pullback components

A compact invariant carrier is first placed in the genuine bounded-orbit
set using the escape potential.  A conjugacy from a quadratic filled set
then yields local saturation from actual critical itineraries.  Primitive
phase separation supplies those itineraries, so neither local degree,
neighborhood univalence, nor component saturation is an input.
-/

namespace LoopsQuadraticCarrierSaturation

open Set Function
open QuadraticEscape LoopsStationaryFiberDynamics LoopsSaturatedTelescope
open LoopsQuadraticLocalNormalForm LoopsLocalDegreeExhaustion
open LoopsQuadraticEscapeFullness LoopsIteratedCarrierIsolation LoopsTelescopeRamification

set_option maxHeartbeats 1000000

/-- Every compact set invariant under a positive quadratic return lies
in the actual filled Julia set.  The maximum of the escape potential on
the compact carrier cannot increase by the return factor. -/
theorem quadratic_compact_return_invariant_subset_filled
    (c : ℂ) (n : ℕ) (hn : 0 < n) (A : Set ℂ) (hA : IsCompact A)
    (hforward : MapsTo (orbit c n) A A) :
    A ⊆ quadraticFilled c := by
  have hpair : Continuous (fun z : ℂ => (c, z)) :=
    continuous_const.prodMk continuous_id
  have hcont : Continuous (fun z : ℂ => escape c z) := by
    change Continuous ((fun p : ℂ × ℂ => escape p.1 p.2) ∘
      (fun z : ℂ => (c, z)))
    exact escape_continuous.comp hpair
  have hp : ∀ k : ℕ, (1 : ℝ) ≤ 2^k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; nlinarith
  have hfactor : (1 : ℝ) < 2^n := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [hk, pow_succ]
    nlinarith [hp k]
  intro z hz
  obtain ⟨x, hx, hmax⟩ := hA.exists_isMaxOn ⟨z, hz⟩ hcont.continuousOn
  have hi := hmax (hforward hx)
  rw [escape_iterate] at hi
  have hx0 : escape c x = 0 := by
    nlinarith [escape_nonneg c x]
  change escape c z = 0
  have hzle := hmax hz
  rw [hx0] at hzle
  exact le_antisymm hzle (escape_nonneg c z)

/-- Compactness of the actual source and the conjugacy equation alone
place every embedded point in the ambient quadratic filled set. -/
theorem quadratic_return_conjugacy_subset_filled
    (q c : ℂ) (n : ℕ) (hn : 0 < n)
    (h : quadraticFilled q → ℂ) (hh : Continuous h)
    (hc : ∀ x, orbit c n (h x) = h (quadraticFilledMap q x)) :
    range h ⊆ quadraticFilled c := by
  letI : CompactSpace (quadraticFilled q) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact q)
  apply quadratic_compact_return_invariant_subset_filled c n hn (range h)
    (isCompact_range hh)
  rintro _ ⟨x, rfl⟩
  exact ⟨quadraticFilledMap q x, (hc x).symm⟩

/-- Matching is expressed entirely by actual preterminal visits to
zero.  The analytic neighborhoods and the ambient inverse-image
isolation are constructed, including at the critical target. -/
theorem quadratic_return_conjugacy_isolation
    (q c : ℂ) (n : ℕ) (h : quadraticFilled q → ℂ)
    (hh : Continuous h) (hi : Injective h)
    (hc : ∀ x, orbit c n (h x) = h (quadraticFilledMap q x))
    (hregular : ∀ x : quadraticFilled q, (x : ℂ) ≠ 0 →
      ∀ j < n, orbit c j (h x) ≠ 0)
    (hcritical : ∀ x : quadraticFilled q, (x : ℂ) = 0 →
      ∃ j < n, orbit c j (h x) = 0 ∧
        ∀ k < n, k ≠ j → orbit c k (h x) ≠ 0) :
    ∃ V : Set ℂ, IsOpen V ∧ range h ⊆ V ∧
      V ∩ orbit c n ⁻¹' range h = range h := by
  apply quadratic_conjugacy_local_exhaustion q (orbit c n) h
    (quadratic_orbit_continuous c n) hh hi hc
  · intro x hx
    exact quadratic_regular_local_injective c n (h x) (hregular x hx)
  · intro x hx
    obtain ⟨j, hj, hzero, hother⟩ := hcritical x hx
    exact quadratic_simple_critical_local_pair c n (h x) j hj hzero hother

/-- A primitive embedded filled quadratic, with its critical point
identified and the central phase disjoint from every intermediate
phase, is an entire actual return pullback component.  Connectedness,
critical compatibility, and ambient filled-set membership are derived. -/
theorem quadratic_primitive_conjugacy_component
    (q c : ℂ) (n : ℕ) (hn : 0 < n)
    (h0 : (0 : ℂ) ∈ quadraticFilled q)
    (h : quadraticFilled q → ℂ) (hh : Continuous h) (hi : Injective h)
    (hc : ∀ x, orbit c n (h x) = h (quadraticFilledMap q x))
    (hcenter : h ⟨0, h0⟩ = 0)
    (hphase : ∀ j, 0 < j → j < n →
      Disjoint (range h) (orbit c j '' range h)) :
    range h ⊆ quadraticFilled c ∧
      ∃ V : Set ℂ, IsOpen V ∧ range h ⊆ V ∧
        V ∩ orbit c n ⁻¹' range h = range h ∧
        range h = connectedComponentIn (orbit c n ⁻¹' range h) 0 := by
  have hzero_range : (0 : ℂ) ∈ range h := ⟨⟨0, h0⟩, hcenter⟩
  have hbetween (x : quadraticFilled q) (j : ℕ) (hj : 0 < j) (hjn : j < n) :
      orbit c j (h x) ≠ 0 := by
    intro he
    exact Set.disjoint_left.mp (hphase j hj hjn) hzero_range
      ⟨h x, mem_range_self x, he⟩
  have hregular (x : quadraticFilled q) (hx : (x : ℂ) ≠ 0) :
      ∀ j < n, orbit c j (h x) ≠ 0 := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      change h x ≠ 0
      intro he
      have hxeq : x = ⟨0, h0⟩ := hi (he.trans hcenter.symm)
      exact hx (congrArg Subtype.val hxeq)
    · exact hbetween x j (Nat.pos_of_ne_zero hj0) hj
  have hcritical (x : quadraticFilled q) (hx : (x : ℂ) = 0) :
      ∃ j < n, orbit c j (h x) = 0 ∧
        ∀ k < n, k ≠ j → orbit c k (h x) ≠ 0 := by
    have hxeq : x = ⟨0, h0⟩ := Subtype.ext hx
    refine ⟨0, hn, ?_, ?_⟩
    · change h x = 0
      rw [hxeq, hcenter]
    · intro k hk hk0
      exact hbetween x k (Nat.pos_of_ne_zero hk0) hk
  have hreg_local (x : quadraticFilled q) (hx : (x : ℂ) ≠ 0) :
      ∃ U : Set ℂ, IsOpen U ∧ h x ∈ U ∧ InjOn (orbit c n) U :=
    quadratic_regular_local_injective c n (h x) (hregular x hx)
  have hcrit_local (x : quadraticFilled q) (hx : (x : ℂ) = 0) :
      ∃ U : Set ℂ, IsOpen U ∧ h x ∈ U ∧
        (∀ z ∈ U, ∀ w ∈ U, ∀ v ∈ U,
          orbit c n z = orbit c n w → orbit c n z = orbit c n v →
          z = w ∨ z = v ∨ w = v) ∧
        (∀ z ∈ U, orbit c n z = orbit c n (h x) → z = h x) := by
    obtain ⟨j, hj, hzero, hother⟩ := hcritical x hx
    exact quadratic_simple_critical_local_pair c n (h x) j hj hzero hother
  have hconn : IsPreconnected (range h) := by
    letI : PreconnectedSpace (quadraticFilled q) :=
      isPreconnected_iff_preconnectedSpace.mp
        (quadratic_filled_connected_of_critical q h0).isPreconnected
    exact isPreconnected_range hh
  obtain ⟨V, hV, hAV, hiso⟩ :=
    quadratic_return_conjugacy_isolation q c n h hh hi hc hregular hcritical
  refine ⟨quadratic_return_conjugacy_subset_filled q c n hn h hh hc,
    V, hV, hAV, hiso, ?_⟩
  have he := quadratic_conjugacy_component q (orbit c n) h
    (quadratic_orbit_continuous c n) hh hi hc hreg_local hcrit_local hconn ⟨0, h0⟩
  rwa [hcenter] at he


/-- The same actual primitive carrier is the exact selected component
after every finite number of returns. For each fixed horizon a single
constructed open window isolates all of its earlier pullbacks. No
neighborhood uniform over every horizon is assumed or concluded. -/
theorem quadratic_primitive_conjugacy_all_returns
    (q c : ℂ) (n : ℕ) (hn : 0 < n)
    (h0 : (0 : ℂ) ∈ quadraticFilled q)
    (h : quadraticFilled q → ℂ) (hh : Continuous h) (hi : Injective h)
    (hc : ∀ x, orbit c n (h x) = h (quadraticFilledMap q x))
    (hcenter : h ⟨0, h0⟩ = 0)
    (hphase : ∀ j, 0 < j → j < n →
      Disjoint (range h) (orbit c j '' range h)) :
    (∀ k : ℕ, range h =
      connectedComponentIn (orbit c (n*k) ⁻¹' range h) 0) ∧
    (∀ H : ℕ, ∃ W : Set ℂ, IsOpen W ∧ range h ⊆ W ∧
      ∀ k ≤ H, W ∩ orbit c (n*k) ⁻¹' range h = range h) := by
  letI : CompactSpace (quadraticFilled q) :=
    isCompact_iff_compactSpace.mp (quadratic_filled_compact q)
  have hconn : IsPreconnected (range h) := by
    letI : PreconnectedSpace (quadraticFilled q) :=
      isPreconnected_iff_preconnectedSpace.mp
        (quadratic_filled_connected_of_critical q h0).isPreconnected
    exact isPreconnected_range hh
  obtain ⟨_, V, hV, _, hiso, _⟩ :=
    quadratic_primitive_conjugacy_component q c n hn h0 h hh hi hc hcenter hphase
  have hclock (k : ℕ) : (orbit c n)^[k] = orbit c (n*k) := by
    rw [orbit_map_eq_iterate, orbit_map_eq_iterate, Function.iterate_mul]
  have hz : (0 : ℂ) ∈ range h := ⟨⟨0, h0⟩, hcenter⟩
  constructor
  · intro k
    have he := iterated_preimage_component (orbit c n) V (range h)
      (quadratic_orbit_continuous c n) (isCompact_range hh).isClosed
      hconn hV hiso 0 hz k
    rw [hclock k] at he
    exact he.symm
  · intro H
    obtain ⟨W, hW, hAW, hwin⟩ := finite_horizon_isolation (orbit c n) V (range h)
      (quadratic_orbit_continuous c n) hV hiso H
    refine ⟨W, hW, hAW, ?_⟩
    intro k hk
    simpa only [hclock k] using hwin k hk

end LoopsQuadraticCarrierSaturation
