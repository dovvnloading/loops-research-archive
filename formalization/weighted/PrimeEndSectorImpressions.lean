import PrimeEndSectorFilters
import LeastSaturatedCarrier

/-!
# Compact address spaces, sector capacity and physical side impressions

These are independent of the analytic construction of the native coordinate.
The impression covariance uses the genuine complex quadratic iterate.
-/

namespace PrimeEndSectorFilters

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- A finite-width family of contracting sectors cannot retain more
distinct angles than its sector count. The sectors need not have coherent
labels across depths, and can overlap. -/
theorem finite_sector_capacity (A : ℕ → Set X) (s : ℕ)
    (B : ℕ → Fin s → Set X) (hcover : ∀ n, A n ⊆ ⋃ j, B n j)
    (hsmall : ∀ ε > 0, ∃ n, ∀ j x y, x ∈ B n j → y ∈ B n j → dist x y < ε)
    (f : Fin (s+1) → X) (hf : ∀ i, f i ∈ ⋂ n, A n) :
    ¬ Function.Injective f := by
  classical
  intro hinj
  by_cases hs : s = 0
  · subst s
    obtain ⟨j, _⟩ := mem_iUnion.mp (hcover 0 (mem_iInter.mp (hf 0) 0))
    exact Fin.elim0 j
  · let P := (Finset.univ : Finset (Fin (s+1) × Fin (s+1))).filter
        (fun p => p.1 ≠ p.2)
    let i0 : Fin (s+1) := ⟨0, by omega⟩
    let i1 : Fin (s+1) := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by
      intro h
      have he := congrArg Fin.val h
      change (0 : ℕ) = 1 at he
      omega
    have hP : P.Nonempty := ⟨(i0,i1),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h01⟩⟩
    obtain ⟨p, hp, hmin⟩ := P.exists_min_image
      (fun p => dist (f p.1) (f p.2)) hP
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hpos : 0 < dist (f p.1) (f p.2) :=
      dist_pos.mpr (fun h => hne (hinj h))
    obtain ⟨n, hn⟩ := hsmall _ hpos
    have hlabels : ∀ i, ∃ j, f i ∈ B n j :=
      fun i => mem_iUnion.mp (hcover n (mem_iInter.mp (hf i) n))
    choose j hj using hlabels
    have hjinj : Function.Injective j := by
      intro i k he
      by_contra hik
      have hikP : (i,k) ∈ P :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hik⟩
      have hle : dist (f p.1) (f p.2) ≤ dist (f i) (f k) :=
        hmin (i,k) hikP
      have hk : f k ∈ B n (j i) := by rw [he]; exact hj k
      exact (not_lt_of_ge hle) (hn (j i) (f i) (f k) (hj i) hk)
    have hcard := Fintype.card_le_of_injective j hjinj
    simp only [Fintype.card_fin] at hcard
    omega

/-- Pointwise singleton ends imply a uniform shrinking horizon on any
compact address space when the depth-n physical cylinder depends locally
constantly on the address. No uniform analytic rate is assumed. -/
theorem compact_address_uniform_shrinking
    {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
    (Q : Ω → ℕ → Set X) (hc : ∀ ω n, IsCompact (Q ω n))
    (hnest : ∀ ω, Antitone (Q ω))
    (hsing : ∀ ω, ∃ z, (⋂ n, Q ω n) = {z})
    (hlocal : ∀ ω n, ∃ U : Set Ω, IsOpen U ∧ ω ∈ U ∧
      ∀ τ ∈ U, Q τ n = Q ω n)
    (ε : ℝ) (he : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∀ ω x, x ∈ Q ω n → ∀ y ∈ Q ω n, dist x y < ε := by
  let U : ℕ → Set Ω := fun n =>
    {ω | ∀ x ∈ Q ω n, ∀ y ∈ Q ω n, dist x y < ε}
  have ho (n : ℕ) : IsOpen (U n) := by
    rw [isOpen_iff_mem_nhds]
    intro ω hω
    obtain ⟨V, hV, hw, hEq⟩ := hlocal ω n
    apply Filter.mem_of_superset (hV.mem_nhds hw)
    intro τ hτ
    change ∀ x ∈ Q τ n, ∀ y ∈ Q τ n, dist x y < ε
    rw [hEq τ hτ]
    exact hω
  have hm : Monotone U := by
    intro i j hij ω hω x hx y hy
    exact hω x (hnest ω hij hx) y (hnest ω hij hy)
  have hcover : (univ : Set Ω) ⊆ ⋃ n, U n := by
    intro ω _
    obtain ⟨z, hz⟩ := hsing ω
    have hI : (⋂ n, Q ω n) ⊆ ball z (ε/2) := by
      rw [hz]
      intro x hx
      rw [mem_singleton_iff.mp hx]
      exact Metric.mem_ball_self (by linarith)
    obtain ⟨n, hn⟩ := compact_footprint_eventually_inside
      (Q ω) (hc ω) (hnest ω) (ball z (ε/2)) isOpen_ball hI
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    intro x hx y hy
    have h1 := Metric.mem_ball.mp (hn hx)
    have h2 := Metric.mem_ball.mp (hn hy)
    have h3 := dist_triangle x z y
    rw [dist_comm z y] at h3
    linarith
  have hd : Directed (· ⊆ ·) U := by
    intro i j
    exact ⟨max i j, hm (le_max_left i j), hm (le_max_right i j)⟩
  obtain ⟨N, hN⟩ := (isCompact_univ : IsCompact (univ : Set Ω)).elim_directed_cover
    U ho hcover hd
  refine ⟨N, ?_⟩
  intro n hn ω
  exact hm hn (hN (mem_univ ω))

/-- An actual finite prefix cylinder is open in the product topology. -/
theorem prefix_cylinder_open {Σ : Type*} [TopologicalSpace Σ] [DiscreteTopology Σ]
    (ω : ℕ → Σ) (n : ℕ) :
    IsOpen {τ : ℕ → Σ | ∀ k < n, τ k = ω k} := by
  have he : {τ : ℕ → Σ | ∀ k < n, τ k = ω k} =
      ⋂ k : Fin n, (fun τ : ℕ → Σ => τ k.val) ⁻¹' ({ω k.val} : Set Σ) := by
    ext τ
    simp only [mem_setOf_eq, mem_iInter, mem_preimage, mem_singleton_iff]
    constructor
    · intro h k
      exact h k.val k.isLt
    · intro h k hk
      exact h ⟨k,hk⟩
  rw [he]
  exact isOpen_iInter_of_finite (fun k =>
    (isOpen_discrete _).preimage (continuous_apply k.val))

/-- Uniform physical shrinking for all infinite words over a compact
discrete alphabet (in particular the binary decoration alphabet). -/
theorem finite_prefix_uniform_shrinking
    {Σ : Type*} [TopologicalSpace Σ] [DiscreteTopology Σ] [CompactSpace Σ]
    (Q : (ℕ → Σ) → ℕ → Set X) (hc : ∀ ω n, IsCompact (Q ω n))
    (hnest : ∀ ω, Antitone (Q ω))
    (hsing : ∀ ω, ∃ z, (⋂ n, Q ω n) = {z})
    (hprefix : ∀ n ω τ, (∀ k < n, τ k = ω k) → Q τ n = Q ω n)
    (ε : ℝ) (he : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∀ ω x, x ∈ Q ω n → ∀ y ∈ Q ω n, dist x y < ε := by
  apply compact_address_uniform_shrinking Q hc hnest hsing _ ε he
  intro ω n
  exact ⟨{τ | ∀ k < n, τ k = ω k}, prefix_cylinder_open ω n,
    fun _ _ => rfl, fun τ hτ => hprefix n ω τ hτ⟩

/-- A nondegenerate interval track rooted at its left endpoint is
cofinal in exactly the right-sided angular-height rectangles. -/
def rightWedge (θ ε : ℝ) : Set (ℝ × ℝ) :=
  {p | θ ≤ p.1 ∧ p.1 < θ+ε ∧ 0 < p.2 ∧ p.2 < ε}

theorem right_endpoint_filter (r H : ℕ → ℝ) (θ : ℝ)
    (hr : ∀ n, θ < r n) (hp : ∀ n, 0 < H n)
    (hrmono : Antitone r) (hhmono : Antitone H)
    (hrsmall : ∀ ε > 0, ∃ n, r n < θ+ε)
    (hhsmall : ∀ ε > 0, ∃ n, H n < ε) :
    (∀ ε > 0, ∃ n, trace (Icc θ (r n)) (H n) ⊆ rightWedge θ ε) ∧
    (∀ n, ∃ ε > 0, rightWedge θ ε ⊆ trace (Icc θ (r n)) (H n)) := by
  constructor
  · intro ε he
    obtain ⟨i, hi⟩ := hrsmall ε he
    obtain ⟨j, hj⟩ := hhsmall ε he
    refine ⟨max i j, ?_⟩
    intro p h
    exact ⟨h.1.1,
      lt_of_le_of_lt (h.1.2.trans (hrmono (le_max_left i j))) hi,
      h.2.1, lt_of_le_of_lt (h.2.2.trans (hhmono (le_max_right i j))) hj⟩
  · intro n
    have hd : 0 < r n - θ := sub_pos.mpr (hr n)
    refine ⟨min (r n-θ) (H n), lt_min hd (hp n), ?_⟩
    intro p h
    have hangle := h.2.1
    have hle := min_le_left (r n-θ) (H n)
    refine ⟨⟨h.1, by linarith⟩, h.2.2.1, ?_⟩
    exact (lt_of_lt_of_le h.2.2.2 (min_le_right _ _)).le

/-- Continuous maps commute with closure if the source closure is
compact, without requiring a global closed map. -/
theorem image_closure_eq_compact {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (S : Set X) (hc : IsCompact (closure S)) :
    f '' closure S = closure (f '' S) := by
  apply Subset.antisymm (image_closure_subset_closure_image hf)
  exact closure_minimal (image_mono subset_closure) (hc.image hf).isClosed

/-- A side impression formed from nested connected wedges with compact
closures is itself nonempty and preconnected. -/
theorem nested_impression_connected (S : ℕ → Set X)
    (ha : Antitone S) (hc : ∀ n, IsCompact (closure (S n)))
    (hne : ∀ n, (S n).Nonempty) (hp : ∀ n, IsPreconnected (S n)) :
    (⋂ n, closure (S n)).Nonempty ∧ IsPreconnected (⋂ n, closure (S n)) := by
  let K : ℕ → Set X := fun n => closure (S n)
  have hm : Antitone K := fun _ _ hij => closure_mono (ha hij)
  have hd : Directed (· ⊇ ·) K := by
    intro i j
    exact ⟨max i j, hm (le_max_left i j), hm (le_max_right i j)⟩
  exact ⟨IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      K hd (fun n => (hne n).mono subset_closure) hc (fun _ => isClosed_closure),
    LoopsLeastCarrier.directed_carrier_preconnected (K 0) (hc 0) K hc
      (fun n => (hp n).closure) (fun n => hm (Nat.zero_le n)) hd⟩

/-- Actual polynomial image covariance for side impressions: the wedge
images need only be cofinal with the target wedges, not equal at matching
integer indices. This accommodates angular-height rescaling. -/
theorem quadratic_cofinal_impression_covariance (c : ℂ) (n : ℕ)
    (S T : ℕ → Set ℂ) (ha : Antitone S)
    (hc : ∀ m, IsCompact (closure (S m)))
    (hforward : ∀ j, ∃ i, QuadraticEscape.orbit c n '' S i ⊆ T j)
    (hreverse : ∀ i, ∃ j, T j ⊆ QuadraticEscape.orbit c n '' S i) :
    QuadraticEscape.orbit c n '' (⋂ m, closure (S m)) = ⋂ m, closure (T m) := by
  let f := QuadraticEscape.orbit c n
  have hf : Continuous f := LoopsSaturatedTelescope.quadratic_orbit_continuous c n
  let K : ℕ → Set ℂ := fun m => closure (S m)
  have hm : Antitone K := fun _ _ hij => closure_mono (ha hij)
  have hd : Directed (· ⊇ ·) K := by
    intro i j
    exact ⟨max i j, hm (le_max_left i j), hm (le_max_right i j)⟩
  have hcl (m : ℕ) : f '' K m = closure (f '' S m) :=
    image_closure_eq_compact f hf (S m) (hc m)
  change f '' (⋂ m, K m) = _
  rw [LoopsLeastCarrier.directed_image_intersection f hf K hc hd]
  simp only [hcl]
  apply Subset.antisymm
  · intro x hx
    apply mem_iInter.mpr
    intro j
    obtain ⟨i, hi⟩ := hforward j
    exact closure_mono hi (mem_iInter.mp hx i)
  · intro x hx
    apply mem_iInter.mpr
    intro i
    obtain ⟨j, hj⟩ := hreverse i
    exact closure_mono hj (mem_iInter.mp hx j)

/-- A singleton target impression and a common radial landing point
force an actual preimage side impression to be a singleton. Neither
preimage-side local connectivity nor a chosen continuous inverse is
required, and covariance is proved rather than assumed. -/
theorem endpoint_impression_from_cofinal_wedges (c : ℂ) (n : ℕ)
    (S T : ℕ → Set ℂ) (z : ℂ) (ha : Antitone S)
    (hc : ∀ m, IsCompact (closure (S m)))
    (hne : ∀ m, (S m).Nonempty) (hp : ∀ m, IsPreconnected (S m))
    (hz : z ∈ ⋂ m, closure (S m))
    (hforward : ∀ j, ∃ i, QuadraticEscape.orbit c n '' S i ⊆ T j)
    (hreverse : ∀ i, ∃ j, T j ⊆ QuadraticEscape.orbit c n '' S i)
    (htarget : (⋂ m, closure (T m)) = {QuadraticEscape.orbit c n z}) :
    (⋂ m, closure (S m)) = {z} := by
  have hcov := quadratic_cofinal_impression_covariance c n S T ha hc hforward hreverse
  rw [htarget] at hcov
  have hpre := (nested_impression_connected S ha hc hne hp).2
  have hconst : ∀ w ∈ ⋂ m, closure (S m),
      QuadraticEscape.orbit c n w = QuadraticEscape.orbit c n z := by
    intro w hw
    have hmem : QuadraticEscape.orbit c n w ∈
        QuadraticEscape.orbit c n '' (⋂ m, closure (S m)) := ⟨w, hw, rfl⟩
    rw [hcov] at hmem
    exact mem_singleton_iff.mp hmem
  apply Subset.antisymm
  · intro w hw
    exact mem_singleton_iff.mpr (quadratic_iterate_connected_fiber c n
      (⋂ m, closure (S m)) hpre _ hconst hw hz)
  · intro w hw
    rw [mem_singleton_iff.mp hw]
    exact hz

end PrimeEndSectorFilters
