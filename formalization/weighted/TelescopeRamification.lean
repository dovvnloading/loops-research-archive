import Mathlib
import SaturatedTelescope
import QuadraticCylinderCensus
import QuadraticCriticalWindow

/-!
# Analytic multiplicity of actual quadratic orbit segments

Local order is measured by Mathlib's analyticOrderAt, not by the
number of distinct points in a fiber. Reuse the existing translated
polynomial factorization and the exact selected-return fiber census.
-/

namespace LoopsTelescopeRamification

open Filter Set
open LoopsSaturatedTelescope
open LoopsQuadraticCylinderCensus
open scoped Topology BigOperators

noncomputable section

theorem orbit_eq_returnOrbit (c x : ℂ) (n : ℕ) :
    QuadraticEscape.orbit c n x =
      LoopsQuadraticTransversality.returnOrbit c x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [QuadraticEscape.orbit, LoopsQuadraticTransversality.returnOrbit, ih]

theorem orbit_map_eq_iterate (c : ℂ) (n : ℕ) :
    QuadraticEscape.orbit c n = ((fun z : ℂ => z^2+c)^[n]) := by
  funext x
  exact (orbit_eq_returnOrbit c x n).trans
    (LoopsQuadraticTransversality.returnOrbit_eq_iterate c x n)

/-- Use the already formalized chronological count. -/
abbrev criticalVisits (c x : ℂ) (n : ℕ) : ℕ :=
  QuadraticCriticalWindow.criticalCount c x n

theorem criticalVisits_succ (c x : ℂ) (n : ℕ) :
    criticalVisits c x (n+1) = criticalVisits c x n +
      (if QuadraticEscape.orbit c n x = 0 then 1 else 0) := by
  classical
  by_cases h : QuadraticEscape.orbit c n x = 0 <;>
    simp [criticalVisits, QuadraticCriticalWindow.criticalCount, ← orbit_eq_returnOrbit, h]

theorem orbit_analytic (c : ℂ) (n : ℕ) (x : ℂ) :
    AnalyticAt ℂ (QuadraticEscape.orbit c n) x := by
  induction n with
  | zero => exact analyticAt_id
  | succ n ih =>
    change AnalyticAt ℂ (fun z => (QuadraticEscape.orbit c n z)^2+c) x
    exact (ih.pow 2).add analyticAt_const

/-- The existing algebraic unit is an entire analytic factor in
physical coordinates, nonzero at the anchor. -/
theorem orbit_ramification_factor (c x : ℂ) (n : ℕ) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧ g x ≠ 0 ∧
      ∀ z, QuadraticEscape.orbit c n z - QuadraticEscape.orbit c n x =
        (z-x)^(2^criticalVisits c x n) * g z := by
  refine ⟨fun z => (QuadraticCriticalWindow.localUnit c x n).eval (z-x), ?_, ?_, ?_⟩
  · intro z
    have ha : AnalyticAt ℂ (fun w : ℂ => w-x) z :=
      analyticAt_id.sub analyticAt_const
    simpa only [Polynomial.coe_aeval_eq_eval] using
      ha.aeval_polynomial (QuadraticCriticalWindow.localUnit c x n)
  · simpa using QuadraticCriticalWindow.localUnit_eval_zero_ne c x n
  · intro z
    have h := QuadraticCriticalWindow.local_factorization c x (z-x) n
    rw [show x+(z-x)=z by ring] at h
    simpa only [← orbit_eq_returnOrbit, criticalVisits] using h

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
  | zero => simp [criticalVisits, QuadraticCriticalWindow.criticalCount]
  | succ n ih =>
    rw [show m+(n+1) = m+n+1 by omega, criticalVisits_succ c x (m+n),
      criticalVisits_succ c (QuadraticEscape.orbit c m x) n, ih,
      quadratic_orbit_add c m n x]
    omega

theorem criticalVisits_zero_iff (c x : ℂ) (n : ℕ) :
    criticalVisits c x n = 0 ↔ ∀ j < n, QuadraticEscape.orbit c j x ≠ 0 := by
  simpa only [criticalVisits, ← orbit_eq_returnOrbit] using
    QuadraticCriticalWindow.criticalCount_eq_zero_iff c x n

/-- Injectivity on an open physical domain rules out every earlier
critical encounter, not just the starting critical point. The
intermediate image is open, so a reflected pair gives a collision. -/
theorem orbit_injOn_no_critical_visits (c : ℂ) (n : ℕ) (A : Set ℂ)
    (hA : IsOpen A) (hI : InjOn (QuadraticEscape.orbit c n) A)
    (x : ℂ) (hx : x ∈ A) :
    ∀ j < n, QuadraticEscape.orbit c j x ≠ 0 := by
  intro j hj hz
  have ho : IsOpenMap (QuadraticEscape.orbit c j) := by
    rw [orbit_map_eq_iterate]
    exact quadratic_iterate_open c j
  have hopen : IsOpen (QuadraticEscape.orbit c j '' A) := ho _ hA
  have hzero : (0 : ℂ) ∈ QuadraticEscape.orbit c j '' A := ⟨x, hx, hz⟩
  obtain ⟨t, ht, hnt, hne⟩ := QuadraticCriticalWindow.open_contains_reflected_pair
    _ hopen hzero
  obtain ⟨u, hu, hut⟩ := ht
  obtain ⟨v, hv, hvt⟩ := hnt
  let k := n-j
  have hk : j+k=n := by dsimp [k]; omega
  have hkpos : 0 < k := by dsimp [k]; omega
  have hclock (z : ℂ) : QuadraticEscape.orbit c n z =
      QuadraticEscape.orbit c k (QuadraticEscape.orbit c j z) :=
    (congrArg (fun m => QuadraticEscape.orbit c m z) hk.symm).trans
      (quadratic_orbit_add c j k z)
  have hcollision : QuadraticEscape.orbit c n u =
      QuadraticEscape.orbit c n v := by
    rw [hclock u, hclock v, hut, hvt]
    simpa only [← orbit_eq_returnOrbit] using
      QuadraticCriticalWindow.positive_iterate_even c t k hkpos
  exact hne (hut.symm.trans
    ((congrArg (QuadraticEscape.orbit c j) (hI hu hv hcollision)).trans hvt))

theorem orbit_unramified_order (c x : ℂ) (n : ℕ)
    (h : ∀ j < n, QuadraticEscape.orbit c j x ≠ 0) :
    analyticOrderAt (fun z => QuadraticEscape.orbit c n z -
      QuadraticEscape.orbit c n x) x = 1 := by
  rw [orbit_analytic_order, (criticalVisits_zero_iff c x n).mpr h]
  norm_num

/-- The designated step contributes the entire analytic multiplicity
when the physical prefix and suffix avoid zero. -/
theorem return_order_one_step (c x : ℂ) (a b : ℕ)
    (hp : ∀ j < a, QuadraticEscape.orbit c j x ≠ 0)
    (hs : ∀ j < b, QuadraticEscape.orbit c j
      (QuadraticEscape.orbit c (a+1) x) ≠ 0) :
    analyticOrderAt (fun z => QuadraticEscape.orbit c (a+1+b) z -
      QuadraticEscape.orbit c (a+1+b) x) x =
      (if QuadraticEscape.orbit c a x = 0 then (2 : ℕ) else 1) := by
  classical
  rw [orbit_analytic_order, criticalVisits_add c x (a+1) b,
    (criticalVisits_zero_iff _ _ _).mpr hs, criticalVisits_succ,
    (criticalVisits_zero_iff c x a).mpr hp]
  by_cases h : QuadraticEscape.orbit c a x = 0 <;> simp [h]

/-- The selected return's actual analytic order over a value is
two at the propagated critical value and one at all other values.
The prefix and suffix need only be injective on their open domains. -/
theorem selected_return_fiber_order (c : ℂ) (a b : ℕ) (A B D : Set ℂ)
    (hc : c ∈ D) (hA : IsOpen A) (hD : IsOpen D)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hponto : QuadraticEscape.orbit c a '' A = B)
    (hpinj : InjOn (QuadraticEscape.orbit c a) A)
    (hrinj : InjOn (QuadraticEscape.orbit c b) D)
    (v x : ℂ) (hx : x ∈ A) (hv : QuadraticEscape.orbit c (a+1+b) x = v) :
    analyticOrderAt (fun z => QuadraticEscape.orbit c (a+1+b) z - v) x =
      (if v = QuadraticEscape.orbit c b c then (2 : ℕ) else 1) := by
  classical
  have hxB : QuadraticEscape.orbit c a x ∈ B := by
    rw [← hponto]
    exact ⟨x, hx, rfl⟩
  rw [hB] at hxB
  have hxD : (QuadraticEscape.orbit c a x)^2+c ∈ D :=
    connectedComponentIn_subset ((fun w : ℂ => w^2+c) ⁻¹' D) 0 hxB
  have hvalue : v = QuadraticEscape.orbit c b ((QuadraticEscape.orbit c a x)^2+c) :=
    hv.symm.trans (quadratic_orbit_add c (a+1) b x)
  have hcrit : QuadraticEscape.orbit c a x = 0 ↔
      v = QuadraticEscape.orbit c b c := by
    constructor
    · intro h
      rw [hvalue, h]
      simp
    · intro h
      have he := hrinj hxD hc (hvalue.symm.trans h)
      have hsq : (QuadraticEscape.orbit c a x)^2 = 0 := by linear_combination he
      rw [pow_two] at hsq
      exact (mul_eq_zero.mp hsq).elim id id
  have hp := orbit_injOn_no_critical_visits c a A hA hpinj x hx
  have hs := orbit_injOn_no_critical_visits c b D hD hrinj
    (QuadraticEscape.orbit c (a+1) x) hxD
  have horder := return_order_one_step c x a b hp hs
  rw [hv] at horder
  rw [horder]
  by_cases h : QuadraticEscape.orbit c a x = 0
  · simp [h, hcrit.mp h]
  · have hvne : v ≠ QuadraticEscape.orbit c b c := fun he => h (hcrit.mpr he)
    simp [h, hvne]

theorem mem_localFiber_orbit (c : ℂ) (n : ℕ) (S : Set ℂ) (v z : ℂ) :
    z ∈ localFiber c n S v ↔ z ∈ S ∧ QuadraticEscape.orbit c n z = v := by
  rw [mem_localFiber, orbit_map_eq_iterate]

/-- The complete local fiber has total analytic multiplicity two,
including the critical value where its point cardinality is one.
No analytic degree or multiplicity constancy premise is used. -/
theorem selected_return_weighted_degree (c : ℂ) (a b : ℕ) (A B D : Set ℂ)
    (hc : c ∈ D) (hA : IsOpen A) (hD : IsOpen D)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hponto : QuadraticEscape.orbit c a '' A = B)
    (hpinj : InjOn (QuadraticEscape.orbit c a) A)
    (hrinj : InjOn (QuadraticEscape.orbit c b) D)
    (v : ℂ) (hv : v ∈ QuadraticEscape.orbit c (a+1+b) '' A) :
    (∑ z ∈ localFiber c (a+1+b) A v,
      analyticOrderNatAt (fun w => QuadraticEscape.orbit c (a+1+b) w-v) z) = 2 := by
  classical
  by_cases hvc : v = QuadraticEscape.orbit c b c
  · subst v
    obtain ⟨x, hx, huniq⟩ :=
      quadratic_return_critical_value c a b A B D hc hB hponto hpinj hrinj
    have hf : localFiber c (a+1+b) A (QuadraticEscape.orbit c b c) = {x} := by
      ext z
      rw [mem_localFiber_orbit, Finset.mem_singleton]
      constructor
      · exact huniq z
      · rintro rfl
        exact hx
    rw [hf, Finset.sum_singleton]
    have ho := selected_return_fiber_order c a b A B D hc hA hD hB
      hponto hpinj hrinj _ x hx.1 hx.2
    simp [analyticOrderNatAt, ho]
  · obtain ⟨x, y, hne, hfiber⟩ :=
      quadratic_return_noncritical_fiber c a b A B D hc hB hponto hpinj hrinj v hv hvc
    have hf : localFiber c (a+1+b) A v = {x,y} := by
      ext z
      rw [mem_localFiber_orbit, Finset.mem_insert, Finset.mem_singleton]
      change z ∈ {w | w ∈ A ∧ QuadraticEscape.orbit c (a+1+b) w = v} ↔ _
      rw [hfiber]
      simp
    have hx : x ∈ A ∧ QuadraticEscape.orbit c (a+1+b) x = v := by
      change x ∈ {w | w ∈ A ∧ QuadraticEscape.orbit c (a+1+b) w = v}
      rw [hfiber]
      simp
    have hy : y ∈ A ∧ QuadraticEscape.orbit c (a+1+b) y = v := by
      change y ∈ {w | w ∈ A ∧ QuadraticEscape.orbit c (a+1+b) w = v}
      rw [hfiber]
      simp
    have hox := selected_return_fiber_order c a b A B D hc hA hD hB
      hponto hpinj hrinj v x hx.1 hx.2
    have hoy := selected_return_fiber_order c a b A B D hc hA hD hB
      hponto hpinj hrinj v y hy.1 hy.2
    rw [hf, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
    simp [analyticOrderNatAt, hox, hoy, hvc]

end

end LoopsTelescopeRamification
