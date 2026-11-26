import QuadraticUnivalentNeighborhood
import TelescopeConformalInverse

/-!
# Local one-sheet and two-sheet geometry of actual quadratic iterates

Critical avoidance produces an injective open neighborhood. Exactly one
critical encounter produces analytic source and target coordinates in which
the actual iterate is the square map. The local fiber conclusions retain
the critical target, where the two sheets meet in a single point.
-/

namespace LoopsQuadraticLocalNormalForm

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsQuadraticUnivalentNeighborhood LoopsTelescopeConformalInverse
open LoopsQuadraticCylinderCensus

/-- A critical-free actual orbit has a one-sheet open neighborhood. -/
theorem quadratic_regular_local_injective (c : ℂ) (n : ℕ) (x : ℂ)
    (hcrit : ∀ k < n, orbit c k x ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧ InjOn (orbit c n) U := by
  have hsingle : InjOn (orbit c n) ({x} : Set ℂ) := by
    intro a ha b hb _
    exact (Set.mem_singleton_iff.mp ha).trans (Set.mem_singleton_iff.mp hb).symm
  obtain ⟨U, hU, hxU, hI⟩ := quadratic_compact_univalent_neighborhood c n {x}
    isCompact_singleton hsingle (by
      intro z hz k hk
      have hz' : z = x := Set.mem_singleton_iff.mp hz
      subst z
      exact hcrit k hk)
  exact ⟨U, hU, hxU (Set.mem_singleton x), hI⟩

/-- The unique critical encounter is isolated by the actual univalent
prefix and suffix. Both coordinates are analytic and injective on open
neighborhoods, and the displayed identity is exact on the whole source
neighborhood. The source coordinate sends the anchor to zero. -/
theorem quadratic_simple_critical_local_normal_form
    (c : ℂ) (n : ℕ) (x : ℂ) (j : ℕ)
    (hj : j < n) (hzero : orbit c j x = 0)
    (hother : ∀ k < n, k ≠ j → orbit c k x ≠ 0) :
    ∃ (U V : Set ℂ) (ψ : ℂ → ℂ),
      IsOpen U ∧ x ∈ U ∧ IsOpen V ∧ orbit c n x ∈ V ∧
      MapsTo (orbit c n) U V ∧
      InjOn (orbit c j) U ∧ AnalyticOnNhd ℂ (orbit c j) U ∧
      InjOn ψ V ∧ AnalyticOnNhd ℂ ψ V ∧
      ∀ z ∈ U, ψ (orbit c n z) = (orbit c j z)^2 := by
  let k := n - (j+1)
  have hsplit : n = j+1+k := by dsimp [k]; omega
  have hstep : orbit c (j+1) x = c := by
    change (orbit c j x)^2+c = c
    rw [hzero]
    simp
  have hclock (z : ℂ) : orbit c n z = orbit c k (orbit c (j+1) z) := by
    rw [hsplit, quadratic_orbit_add]
  have hprefix : ∀ i < j, orbit c i x ≠ 0 := by
    intro i hi
    exact hother i (by omega) (by omega)
  have hsuffix : ∀ i < k, orbit c i c ≠ 0 := by
    intro i hi
    have he : orbit c (j+1+i) x = orbit c i c := by
      rw [quadratic_orbit_add, hstep]
    rw [← he]
    exact hother (j+1+i) (by omega) (by omega)
  obtain ⟨P, hP, hxP, hIP⟩ := quadratic_regular_local_injective c j x hprefix
  obtain ⟨S, hS, hcS, hIS⟩ := quadratic_regular_local_injective c k c hsuffix
  let U := P ∩ orbit c (j+1) ⁻¹' S
  let V := orbit c k '' S
  have hU : IsOpen U := hP.inter (hS.preimage (quadratic_orbit_continuous c (j+1)))
  have hxU : x ∈ U := ⟨hxP, by change orbit c (j+1) x ∈ S; rwa [hstep]⟩
  have hopen : IsOpenMap (orbit c k) := by
    rw [orbit_map_eq_iterate]
    exact quadratic_iterate_open c k
  have hV : IsOpen V := hopen S hS
  obtain ⟨g, hgmap, hgleft, hgright, hganalytic, _⟩ :=
    orbit_conformal_inverse c k S V hS hIS rfl
  let ψ : ℂ → ℂ := fun w => g w-c
  have hmap : MapsTo (orbit c n) U V := by
    intro z hz
    exact ⟨orbit c (j+1) z, hz.2, (hclock z).symm⟩
  have hψI : InjOn ψ V := by
    intro a ha b hb hab
    have hgab : g a = g b := by
      change g a-c = g b-c at hab
      linear_combination hab
    calc
      a = orbit c k (g a) := (hgright ha).symm
      _ = orbit c k (g b) := congrArg (orbit c k) hgab
      _ = b := hgright hb
  refine ⟨U, V, ψ, hU, hxU, hV, hmap hxU, hmap,
    hIP.mono inter_subset_left, ?_, hψI, ?_, ?_⟩
  · intro z _
    exact orbit_analytic c j z
  · intro w hw
    exact (hganalytic w hw).sub analyticAt_const
  · intro z hz
    change g (orbit c n z)-c = (orbit c j z)^2
    rw [hclock z, hgleft hz.2]
    change (orbit c j z)^2+c-c = (orbit c j z)^2
    ring

/-- A single critical encounter permits at most two distinct local
preimages. At the critical target itself the local inverse fiber is
exactly the anchor, without any regular-target exception. -/
theorem quadratic_simple_critical_local_pair
    (c : ℂ) (n : ℕ) (x : ℂ) (j : ℕ)
    (hj : j < n) (hzero : orbit c j x = 0)
    (hother : ∀ k < n, k ≠ j → orbit c k x ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧
      (∀ z ∈ U, ∀ w ∈ U, ∀ v ∈ U,
        orbit c n z = orbit c n w → orbit c n z = orbit c n v →
        z = w ∨ z = v ∨ w = v) ∧
      (∀ z ∈ U, orbit c n z = orbit c n x → z = x) := by
  obtain ⟨U, V, ψ, hU, hxU, _, _, _, hI, _, _, _, hform⟩ :=
    quadratic_simple_critical_local_normal_form c n x j hj hzero hother
  have hpair (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U)
      (he : orbit c n z = orbit c n w) :
      orbit c j z = orbit c j w ∨ orbit c j z = -(orbit c j w) := by
    have hs : (orbit c j z)^2 = (orbit c j w)^2 :=
      (hform z hz).symm.trans ((congrArg ψ he).trans (hform w hw))
    exact (quadratic_eq_iff c _ _).mp (congrArg (fun t : ℂ => t+c) hs)
  refine ⟨U, hU, hxU, ?_, ?_⟩
  · intro z hz w hw v hv hzw hzv
    rcases hpair z w hz hw hzw with h | h
    · exact Or.inl (hI hz hw h)
    · rcases hpair z v hz hv hzv with h' | h'
      · exact Or.inr (Or.inl (hI hz hv h'))
      · exact Or.inr (Or.inr (hI hw hv (neg_injective (h.symm.trans h'))))
  · intro z hz he
    have hs := congrArg ψ he
    rw [hform z hz, hform x hxU, hzero] at hs
    have hzsq : orbit c j z * orbit c j z = 0 := by simpa only [pow_two, mul_zero] using hs
    have hz0 : orbit c j z = 0 := (mul_eq_zero.mp hzsq).elim id id
    exact hI hz hxU (hz0.trans hzero.symm)

end LoopsQuadraticLocalNormalForm
