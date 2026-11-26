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
  exact hax.symm.trans ((congrArg (orbit c (r-i)) e).trans hby)

/-- Every phase of a positive critical cycle has a collision by the
period, including phase zero. -/
theorem every_phase_collision (c : ℂ) (P : Set ℂ) (r : ℕ) (i : Fin r)
    (hreturn : phase c P r = P) (hbad : ¬ InjOn (orbit c 1) P) :
    ¬ InjOn (orbit c r) (phase c P i.val) := by
  have hil := i.isLt
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
  have hil := i.isLt
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
  have hil := i.isLt
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

/-- All genuine complex quadratic iterates are surjective, including
time zero. The square-root existence is supplied by algebraic closure. -/
theorem orbit_surjective (c : ℂ) (n : ℕ) : Function.Surjective (orbit c n) := by
  induction n with
  | zero => intro w; exact ⟨w,rfl⟩
  | succ n ih =>
    intro w
    obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq (w-c) (n := 2) (by decide)
    obtain ⟨z,hz⟩ := ih s
    refine ⟨z,?_⟩
    change (orbit c n z)^2+c = w
    rw [hz,hs]
    ring

/-- The actual derivative vanishes exactly when the orbit has already
visited zero strictly before the specified time. -/
theorem multiplier_zero_iff_visit (c z : ℂ) (n : ℕ) :
    multiplier c z n = 0 ↔ ∃ k < n, orbit c k z = 0 := by
  induction n with
  | zero => simp [multiplier]
  | succ n ih =>
    constructor
    · intro h
      change 2 * orbit c n z * multiplier c z n = 0 at h
      rcases mul_eq_zero.mp h with h1 | h2
      · rcases mul_eq_zero.mp h1 with ht | hk
        · norm_num at ht
        · exact ⟨n,Nat.lt_succ_self _,hk⟩
      · obtain ⟨k,hk,hk0⟩ := ih.mp h2
        exact ⟨k,by omega,hk0⟩
    · rintro ⟨k,hkn,hk⟩
      change 2 * orbit c n z * multiplier c z n = 0
      by_cases he : k = n
      · subst k
        rw [hk]
        ring
      · rw [ih.mpr ⟨k,by omega,hk⟩]
        ring

/-- Exact critical VALUE set of each actual quadratic iterate, with
both inclusions and all multiplicity coincidences allowed. In
particular, no point outside the postcritical prefix is a critical value. -/
theorem critical_values_eq_postcritical_prefix (c : ℂ) (n : ℕ) :
    {w : ℂ | ∃ z : ℂ, deriv (orbit c n) z = 0 ∧ orbit c n z = w} =
      {w : ℂ | ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ orbit c k 0 = w} := by
  ext w
  constructor
  · rintro ⟨z,hz,hzw⟩
    rw [multiplier_eq_deriv] at hz
    obtain ⟨k,hkn,hk⟩ := (multiplier_zero_iff_visit c z n).mp hz
    refine ⟨n-k,by omega,by omega,?_⟩
    calc
      orbit c (n-k) 0 = orbit c (n-k) (orbit c k z) := by rw [hk]
      _ = orbit c (k+(n-k)) z := (quadratic_orbit_add c k (n-k) z).symm
      _ = w := by rw [show k+(n-k) = n by omega,hzw]
  · rintro ⟨k,hk,hkn,rfl⟩
    obtain ⟨z,hz⟩ := orbit_surjective c (n-k) 0
    refine ⟨z,?_,?_⟩
    · rw [multiplier_eq_deriv]
      exact (multiplier_zero_iff_visit c z n).mpr ⟨n-k,by omega,hz⟩
    · calc
        orbit c n z = orbit c ((n-k)+k) z := by rw [show (n-k)+k = n by omega]
        _ = orbit c k (orbit c (n-k) z) := quadratic_orbit_add c (n-k) k z
        _ = orbit c k 0 := by rw [hz]

/-- Every iterate is unramified over the complement of the actual
critical cycle. The derivative is the complex derivative of f_c^n. -/
theorem derivative_ne_zero_over_cycle_complement (c : ℂ) (P : Set ℂ) (r n : ℕ)
    (hr : 0 < r) (hreturn : phase c P r = P) (hzero : 0 ∈ P) (z : ℂ)
    (hz : orbit c n z ∉ cycleSupport c P r) :
    deriv (orbit c n) z ≠ 0 := by
  intro h
  have hv : orbit c n z ∈ {w : ℂ | ∃ z : ℂ,
      deriv (orbit c n) z = 0 ∧ orbit c n z = w} := ⟨z,h,rfl⟩
  rw [critical_values_eq_postcritical_prefix] at hv
  obtain ⟨k,_,_,hk⟩ := hv
  apply hz
  rw [← hk]
  exact critical_orbit_mem_cycle c P r hr hreturn hzero k

/-- The finite critical cycle of a compact critical set is closed. -/
theorem cycle_closed (c : ℂ) (P : Set ℂ) (r : ℕ) (hP : IsCompact P) :
    IsClosed (cycleSupport c P r) := by
  unfold cycleSupport
  exact isClosed_iUnion_of_finite fun i =>
    (hP.image (quadratic_orbit_continuous c i.val)).isClosed

/-- A deep native cylinder has an actual common open neighborhood
free of critical values of every iterate, not just of its own return.
The neighborhood is not asserted to be simply connected. -/
theorem deep_cylinder_common_unramified_neighborhood
    (c : ℂ) (P Q : Set ℂ) (r n : ℕ) (a : ℂ)
    (hr : 0 < r) (hreturn : phase c P r = P) (hzero : 0 ∈ P)
    (hdis : Disjoint P (phase c P 1)) (ha : orbit c 1 a = a)
    (hbad : ¬ InjOn (orbit c 1) P) (hP : IsCompact P)
    (hconn : IsPreconnected P) (hQ : IsClosed Q)
    (hfront : ∀ z ∈ frontier Q, z ∈ cycleSupport c P r →
      ∃ k : ℕ, orbit c k z = a)
    (hn : r ≤ n) (hinj : InjOn (orbit c n) Q) :
    ∃ U : Set ℂ, IsOpen U ∧ Q ⊆ U ∧
      ∀ m : ℕ, ∀ z : ℂ, orbit c m z ∈ U → deriv (orbit c m) z ≠ 0 := by
  have hsep := deep_cylinder_avoids_cycle_of_preperiodic_frontier
    c P Q r n a hr hreturn hdis ha hbad hconn hQ hfront hn hinj
  refine ⟨(cycleSupport c P r)ᶜ,(cycle_closed c P r hP).isOpen_compl,?_,?_⟩
  · intro z hz hC
    exact Set.disjoint_left.mp hsep hC hz
  · intro m z hz
    exact derivative_ne_zero_over_cycle_complement c P r m hr hreturn hzero z hz

/-- A uniformly bounded target gives a uniform bound on all its inverse
images at every time, even before a single-valued branch is constructed. -/
theorem inverse_orbit_bound (c z : ℂ) (n : ℕ) (R : ℝ)
    (hR : 1+‖c‖ ≤ R) (ht : ‖orbit c n z‖ ≤ R) : ‖z‖ ≤ R := by
  by_contra hn
  have hz : R < ‖z‖ := lt_of_not_ge hn
  have hlarge (m : ℕ) : R < ‖orbit c m z‖ := by
    induction m with
    | zero => exact hz
    | succ m ih =>
      let w := orbit c m z
      have hw : 1+‖c‖ < ‖w‖ := hR.trans_lt ih
      have hmul : 0 ≤ (‖w‖-1)*(‖w‖-1) := by
        simpa [pow_two] using sq_nonneg (‖w‖-1)
      have hstep := norm_step_lower c w
      change R < ‖w^2+c‖
      change R < ‖w‖ at ih
      nlinarith only [hstep,hw,hmul,ih]
  exact (not_lt_of_ge ht) (hlarge n)

/-- Compact inverse images of compact targets, with the uniform escape
bound from the actual quadratic polynomial. -/
theorem orbit_compact_preimage (c : ℂ) (n : ℕ) (K : Set ℂ)
    (hK : IsCompact K) : IsCompact (orbit c n ⁻¹' K) := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let R := max B (1+‖c‖)
  have hc : IsClosed (orbit c n ⁻¹' K) :=
    hK.isClosed.preimage (quadratic_orbit_continuous c n)
  apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hc
  intro z hz
  have hb : ‖orbit c n z‖ ≤ B := hB _ hz
  have h := inverse_orbit_bound c z n R (le_max_right _ _)
    (hb.trans (le_max_left _ _))
  simpa [Metric.mem_closedBall, dist_eq_norm] using h

end LoopsDecorationCriticalCycle
