import SaturatedTelescope
import QuadraticExtremalMultiplier
import StationarySeparatorTransport

/-!
# Critical-cycle avoidance for actual quadratic decoration cylinders

The phase sets are images under the genuine quadratic orbit. A first-step
collision propagates to every phase by lifting through the return image;
no injectivity of the remaining return arrows is assumed.
-/

namespace LoopsDecorationCriticalCycle
open Set QuadraticEscape LoopsSaturatedTelescope

/-- The actual phase, not an abstract cycle label. -/
def phase (c : ℂ) (P : Set ℂ) (i : ℕ) : Set ℂ :=
  orbit c i '' P

/-- The physical finite cycle union. -/
def cycleSupport (c : ℂ) (P : Set ℂ) (r : ℕ) : Set ℂ :=
  ⋃ i : Fin r, phase c P i.val

theorem phase_zero (c : ℂ) (P : Set ℂ) : phase c P 0 = P := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact hw
  · intro hz
    exact ⟨z,hz,rfl⟩

theorem phase_image (c : ℂ) (P : Set ℂ) (i j : ℕ) :
    orbit c j '' phase c P i = phase c P (i+j) := by
  ext z
  constructor
  · rintro ⟨w,⟨v,hv,rfl⟩,rfl⟩
    exact ⟨v,hv,quadratic_orbit_add c i j v⟩
  · rintro ⟨v,hv,rfl⟩
    exact ⟨orbit c i v,⟨v,hv,rfl⟩,(quadratic_orbit_add c i j v).symm⟩

/-- A genuine collision at time m persists at every later time. -/
theorem orbit_noninjective_later (c : ℂ) (P : Set ℂ) (m n : ℕ)
    (hmn : m ≤ n) (hbad : ¬ InjOn (orbit c m) P) :
    ¬ InjOn (orbit c n) P := by
  intro hinj
  apply hbad
  intro x hx y hy he
  apply hinj hx hy
  rw [show n = m+(n-m) by omega, quadratic_orbit_add, quadratic_orbit_add, he]

/-- The symmetry of an actual nontrivial critical filled set yields
a collision at the first quadratic step. -/
theorem first_step_collision_of_symmetry (c : ℂ) (P : Set ℂ)
    (hsym : ∀ z ∈ P, -z ∈ P) (hz : ∃ z ∈ P, z ≠ 0) :
    ¬ InjOn (orbit c 1) P := by
  obtain ⟨z,hz,hne⟩ := hz
  intro hi
  have he : orbit c 1 z = orbit c 1 (-z) := by
    change z^2+c = (-z)^2+c
    ring
  have h := hi hz (hsym z hz) he
  exact hne (by linear_combination (1/2 : ℂ) * h)

/-- The cycle return surjectivity alone propagates the critical
collision to phase i by time r-i+1. There is no degree-one-tail premise. -/
theorem phase_collision_by_return_tail (c : ℂ) (P : Set ℂ) (r i : ℕ)
    (hi : i ≤ r) (hreturn : phase c P r = P)
    (hbad : ¬ InjOn (orbit c 1) P) :
    ¬ InjOn (orbit c (r-i+1)) (phase c P i) := by
  intro hinj
  apply hbad
  intro x hx y hy he
  have htail : orbit c (r-i) '' phase c P i = P := by
    rw [phase_image, show i+(r-i) = r by omega, hreturn]
  obtain ⟨a,ha,hax⟩ : x ∈ orbit c (r-i) '' phase c P i := by
    rw [htail]
    exact hx
  obtain ⟨b,hb,hby⟩ : y ∈ orbit c (r-i) '' phase c P i := by
    rw [htail]
    exact hy
  have hab : orbit c (r-i+1) a = orbit c (r-i+1) b := by
    rw [quadratic_orbit_add, quadratic_orbit_add, hax, hby, he]
  have e := hinj ha hb hab
  exact hax.symm.trans (e ▸ hby)

/-- Every phase of a positive critical cycle has a collision by the
period, including phase zero. -/
theorem every_phase_collision (c : ℂ) (P : Set ℂ) (r : ℕ) (i : Fin r)
    (hreturn : phase c P r = P) (hbad : ¬ InjOn (orbit c 1) P) :
    ¬ InjOn (orbit c r) (phase c P i.val) := by
  by_cases h : i.val = 0
  · rw [h, phase_zero]
    exact orbit_noninjective_later c P 1 r (by omega) hbad
  · exact orbit_noninjective_later c (phase c P i.val) (r-i.val+1) r
      (by omega) (phase_collision_by_return_tail c P r i.val i.isLt.le hreturn hbad)

/-- The finite phase union is forward invariant as a physical set. -/
theorem cycle_forward (c : ℂ) (P : Set ℂ) (r : ℕ) (hr : 0 < r)
    (hreturn : phase c P r = P) :
    MapsTo (orbit c 1) (cycleSupport c P r) (cycleSupport c P r) := by
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  have him : orbit c 1 z ∈ phase c P (i.val+1) := by
    rw [← phase_image c P i.val 1]
    exact ⟨z,hi,rfl⟩
  apply mem_iUnion.mpr
  by_cases h : i.val+1 < r
  · exact ⟨⟨i.val+1,h⟩,him⟩
  · have e : i.val+1 = r := by omega
    rw [e,hreturn] at him
    refine ⟨⟨0,hr⟩,?_⟩
    change orbit c 1 z ∈ phase c P 0
    rwa [phase_zero]

theorem cycle_iterate_forward (c : ℂ) (P : Set ℂ) (r : ℕ) (hr : 0 < r)
    (hreturn : phase c P r = P) (n : ℕ) :
    MapsTo (orbit c n) (cycleSupport c P r) (cycleSupport c P r) := by
  intro z hz
  induction n with
  | zero => exact hz
  | succ n ih =>
    rw [quadratic_orbit_add c n 1 z]
    exact cycle_forward c P r hr hreturn ih

/-- A fixed point cannot occur in any phase if the critical phase
and its immediate image are disjoint. No pairwise-disjointness of
all the other phase sets is needed. -/
theorem fixed_point_avoids_cycle (c : ℂ) (P : Set ℂ) (r : ℕ) (a : ℂ)
    (hr : 0 < r) (hreturn : phase c P r = P)
    (hdis : Disjoint P (phase c P 1)) (ha : orbit c 1 a = a) :
    a ∉ cycleSupport c P r := by
  intro hm
  obtain ⟨i,hi⟩ := mem_iUnion.mp hm
  have hfix (n : ℕ) : orbit c n a = a := by
    induction n with
    | zero => rfl
    | succ n ih => rw [quadratic_orbit_add c n 1 a, ih, ha]
  have htail : orbit c (r-i.val) '' phase c P i.val = P := by
    rw [phase_image, show i.val+(r-i.val) = r by omega, hreturn]
  have hP : a ∈ P := by
    rw [← htail, ← hfix (r-i.val)]
    exact ⟨a,hi,rfl⟩
  have hP1 : a ∈ phase c P 1 := ⟨a,hP,ha⟩
  exact Set.disjoint_left.mp hdis hP hP1

/-- All iterated preimages of a dividing fixed point avoid the cycle. -/
theorem preperiodic_boundary_avoids_cycle (c : ℂ) (P : Set ℂ) (r : ℕ)
    (a z : ℂ) (hr : 0 < r) (hreturn : phase c P r = P)
    (hdis : Disjoint P (phase c P 1)) (ha : orbit c 1 a = a)
    (n : ℕ) (hz : orbit c n z = a) :
    z ∉ cycleSupport c P r := by
  intro hm
  have h := cycle_iterate_forward c P r hr hreturn n hm
  rw [hz] at h
  exact fixed_point_avoids_cycle c P r a hr hreturn hdis ha h

/-- A closed puzzle piece meeting a connected phase which avoids its
frontier contains the entire phase. This is a connectedness argument,
not an assumption of local connectivity of the Julia set. -/
theorem phase_contained_of_frontier_avoidance (Q S : Set ℂ)
    (hQ : IsClosed Q) (hS : IsPreconnected S)
    (hfront : Disjoint S (frontier Q)) (hmeet : (S ∩ Q).Nonempty) :
    S ⊆ Q := by
  have hcov : S ⊆ interior Q ∪ Qᶜ := by
    intro z hz
    by_cases h : z ∈ Q
    · left
      by_contra hn
      have hzf : z ∈ frontier Q := by
        rw [frontier, hQ.closure_eq]
        exact ⟨h,hn⟩
      exact Set.disjoint_left.mp hfront hz hzf
    · exact Or.inr h
  have hd : Disjoint (interior Q) Qᶜ :=
    Set.disjoint_left.mpr (fun _ hz hn => hn (interior_subset hz))
  rcases IsPreconnected.subset_or_subset isOpen_interior hQ.isOpen_compl hd hcov hS with h | h
  · exact h.trans interior_subset
  · obtain ⟨z,hz,hzQ⟩ := hmeet
    exact False.elim (h hz hzQ)

/-- Native critical-cycle exclusion: an actual closed puzzle piece
injective at time n at least the primitive period cannot meet the
cycle if its frontier avoids the cycle. -/
theorem deep_cylinder_avoids_cycle (c : ℂ) (P Q : Set ℂ) (r n : ℕ)
    (hreturn : phase c P r = P) (hbad : ¬ InjOn (orbit c 1) P)
    (hP : IsPreconnected P) (hQ : IsClosed Q)
    (hfront : Disjoint (cycleSupport c P r) (frontier Q))
    (hn : r ≤ n) (hinj : InjOn (orbit c n) Q) :
    Disjoint (cycleSupport c P r) Q := by
  rw [Set.disjoint_left]
  intro z hz hzQ
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  have hS : IsPreconnected (phase c P i.val) :=
    hP.image _ (quadratic_orbit_continuous c i.val).continuousOn
  have hsub : phase c P i.val ⊆ cycleSupport c P r := fun _ h =>
    mem_iUnion.mpr ⟨i,h⟩
  have hcontained := phase_contained_of_frontier_avoidance Q (phase c P i.val)
    hQ hS (hfront.mono_left hsub) ⟨z,hi,hzQ⟩
  exact orbit_noninjective_later c (phase c P i.val) r n hn
    (every_phase_collision c P r i hreturn hbad) (hinj.mono hcontained)

/-- The source's frontier hypothesis is supplied by its actual
preperiodic boundary points, provided only the intersection with the
physical cycle is of that form. -/
theorem deep_cylinder_avoids_cycle_of_preperiodic_frontier
    (c : ℂ) (P Q : Set ℂ) (r n : ℕ) (a : ℂ)
    (hr : 0 < r) (hreturn : phase c P r = P)
    (hdis : Disjoint P (phase c P 1)) (ha : orbit c 1 a = a)
    (hbad : ¬ InjOn (orbit c 1) P) (hP : IsPreconnected P) (hQ : IsClosed Q)
    (hfront : ∀ z ∈ frontier Q, z ∈ cycleSupport c P r →
      ∃ k : ℕ, orbit c k z = a)
    (hn : r ≤ n) (hinj : InjOn (orbit c n) Q) :
    Disjoint (cycleSupport c P r) Q := by
  apply deep_cylinder_avoids_cycle c P Q r n hreturn hbad hP hQ _ hn hinj
  rw [Set.disjoint_left]
  intro z hz hzf
  obtain ⟨k,hk⟩ := hfront z hzf hz
  exact preperiodic_boundary_avoids_cycle c P r a z hr hreturn hdis ha k hk hz

/-- Every critical orbit point belongs to the physical cycle union. -/
theorem critical_orbit_mem_cycle (c : ℂ) (P : Set ℂ) (r : ℕ)
    (hr : 0 < r) (hreturn : phase c P r = P) (hzero : 0 ∈ P) (n : ℕ) :
    orbit c n 0 ∈ cycleSupport c P r := by
  apply cycle_iterate_forward c P r hr hreturn n
  apply mem_iUnion.mpr
  refine ⟨⟨0,hr⟩,?_⟩
  change (0 : ℂ) ∈ phase c P 0
  rwa [phase_zero]

end LoopsDecorationCriticalCycle
