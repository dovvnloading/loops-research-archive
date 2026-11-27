import QuadraticRegularInverse

/-!
# A complete analytic atlas of actual quadratic inverse components

A regular fiber over one chosen target point indexes every global
pullback component exactly once.  The resulting analytic sections
enumerate every inverse point over every point of the target, with no
supplied branch family or component-exhaustion assumption.

The target is an actual simply connected open subset of the complex
plane avoiding the finite postcritical set for the indicated iterate.
No boundary access, symbolic cylinder ownership, or virtual-stage
identification is asserted.
-/

namespace LoopsQuadraticInverseBranches

open Set Function
open QuadraticEscape LoopsTelescopeRamification
open LoopsQuadraticCriticalFiberCensus LoopsQuadraticRegularInverse

noncomputable section

/-- The entire actual inverse fiber, including every complex solution. -/
def inverseFiber (c : ℂ) (n : ℕ) (y : ℂ) := {a : ℂ // orbit c n a = y}

/-- A regular fiber has exactly the global degree many distinct points. -/
theorem inverseFiber_card (c : ℂ) (n : ℕ) (y : ℂ)
    (hregular : ∀ k < n, orbit c k c ≠ y) :
    Nat.card (inverseFiber c n y) = 2^n := by
  let E : inverseFiber c n y ≃ (globalFiber c n y) :=
    { toFun := fun a => ⟨a.val, (mem_globalFiber c n y a.val).mpr
        (by simpa only [← orbit_map_eq_iterate] using a.property)⟩
      invFun := fun a => ⟨a.val,
        by simpa only [← orbit_map_eq_iterate] using
          (mem_globalFiber c n y a.val).mp a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr E]
  have hcard := (globalFiber_full_card_iff c y n).mpr
    (by simpa only [← orbit_map_eq_iterate] using hregular)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard

/-- The actual component containing an anchor inverse point. -/
def fiberComponent (c : ℂ) (n : ℕ) (V : Set ℂ) (y : ℂ) (hy : y ∈ V)
    (a : inverseFiber c n y) : ConnectedComponents ((orbit c n) ⁻¹' V) :=
  ConnectedComponents.mk ⟨a.val, by change orbit c n a.val ∈ V; rw [a.property]; exact hy⟩

private theorem component_mk_eq_iff (c : ℂ) (n : ℕ) (V : Set ℂ)
    (a b : (orbit c n) ⁻¹' V) :
    ConnectedComponents.mk a = ConnectedComponents.mk b ↔
      inverseComponent c n V a.val = inverseComponent c n V b.val := by
  rw [ConnectedComponents.coe_eq_coe]
  constructor
  · intro h
    unfold inverseComponent
    rw [connectedComponentIn_eq_image a.property,
      connectedComponentIn_eq_image b.property, h]
  · intro h
    apply Subtype.val_injective.image_injective
    simpa only [inverseComponent, connectedComponentIn_eq_image a.property,
      connectedComponentIn_eq_image b.property] using h

/-- Distinct anchor inverse points cannot name the same actual component. -/
theorem anchor_components_injective (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (y : ℂ) (hy : y ∈ V) :
    Injective (fun a : inverseFiber c n y => inverseComponent c n V a.val) := by
  intro a b hab
  have ha : orbit c n a.val ∈ V := by rw [a.property]; exact hy
  have hb : orbit c n b.val ∈ V := by rw [b.property]; exact hy
  have haC : a.val ∈ inverseComponent c n V a.val := mem_connectedComponentIn ha
  have hbC : b.val ∈ inverseComponent c n V a.val := by
    rw [hab]
    exact mem_connectedComponentIn hb
  apply Subtype.ext
  exact inverseComponent_injOn c n V hVo hVc hcrit a.val ha haC hbC
    (a.property.trans b.property.symm)

/-- Every global pullback component has a unique anchor inverse point.
The component census is constructed from surjectivity of the physical map. -/
theorem inverseComponent_unique_anchor (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (y : ℂ) (hy : y ∈ V)
    (z : ℂ) (hz : orbit c n z ∈ V) :
    ∃! a : inverseFiber c n y,
      inverseComponent c n V z = inverseComponent c n V a.val := by
  have he := inverseComponent_image c n V hVo hVc z hz
  have hyC : y ∈ orbit c n '' inverseComponent c n V z := he.symm ▸ hy
  obtain ⟨a, ha, hay⟩ := hyC
  refine ⟨⟨a, hay⟩, connectedComponentIn_eq ha, ?_⟩
  intro b hb
  apply anchor_components_injective c n V hVo hVc hcrit y hy
  exact hb.symm.trans (connectedComponentIn_eq ha)

/-- The entire anchor fiber is in bijection with the topological
connected-component quotient of the actual full pullback. -/
theorem fiberComponent_bijective (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (y : ℂ) (hy : y ∈ V) :
    Bijective (fiberComponent c n V y hy) := by
  constructor
  · intro a b hab
    apply anchor_components_injective c n V hVo hVc hcrit y hy
    exact (component_mk_eq_iff c n V _ _).mp hab
  · intro C
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe C
    obtain ⟨a, ha, _⟩ :=
      inverseComponent_unique_anchor c n V hVo hVc hcrit y hy z.val z.property
    refine ⟨a, ?_⟩
    exact (component_mk_eq_iff c n V _ _).mpr ha.symm

/-- The constructed equivalence retains the actual inverse point as
the label of its physical connected component. -/
def fiberComponentEquiv (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (y : ℂ) (hy : y ∈ V) :
    inverseFiber c n y ≃ ConnectedComponents ((orbit c n) ⁻¹' V) :=
  Equiv.ofBijective (fiberComponent c n V y hy)
    (fiberComponent_bijective c n V hVo hVc hcrit y hy)

/-- There are exactly `2^n` global inverse components.  No component
enumeration, inverse branch, or degree count is assumed. -/
theorem inverse_components_card (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (y : ℂ) (hy : y ∈ V) :
    Nat.card (ConnectedComponents ((orbit c n) ⁻¹' V)) = 2^n := by
  rw [← Nat.card_congr (fiberComponentEquiv c n V hVo hVc hcrit y hy)]
  exact inverseFiber_card c n y (fun k hk he => hcrit k hk (he.symm ▸ hy))

/-- The full ranges of different canonical analytic branches are
disjoint actual global components. -/
theorem inverseBranch_ranges_disjoint (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (y : ℂ) (hy : y ∈ V)
    (a b : inverseFiber c n y) (hab : a ≠ b) :
    Disjoint (inverseBranch c n V a.val '' V) (inverseBranch c n V b.val '' V) := by
  have ha : orbit c n a.val ∈ V := by rw [a.property]; exact hy
  have hb : orbit c n b.val ∈ V := by rw [b.property]; exact hy
  rw [inverseBranch_image c n V hVo hVc hcrit a.val ha,
    inverseBranch_image c n V hVo hVc hcrit b.val hb]
  apply Set.disjoint_left.mpr
  intro z hza hzb
  apply hab
  apply anchor_components_injective c n V hVo hVc hcrit y hy
  exact (connectedComponentIn_eq hza).trans (connectedComponentIn_eq hzb).symm

/-- At every target point, canonical branches enumerate the entire
actual inverse fiber uniquely. The label is fixed once at the anchor. -/
theorem inverseBranch_fiber_exhaustion (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (y : ℂ) (hy : y ∈ V)
    (w : ℂ) (hw : w ∈ V) (z : ℂ) :
    orbit c n z = w ↔
      ∃! a : inverseFiber c n y, inverseBranch c n V a.val w = z := by
  constructor
  · intro hzw
    have hzV : orbit c n z ∈ V := hzw.symm ▸ hw
    obtain ⟨a, hCa, _⟩ :=
      inverseComponent_unique_anchor c n V hVo hVc hcrit y hy z hzV
    have ha : orbit c n a.val ∈ V := by rw [a.property]; exact hy
    have hzC : z ∈ inverseComponent c n V a.val :=
      hCa ▸ mem_connectedComponentIn hzV
    have hbranch : inverseBranch c n V a.val w = z := by
      rw [← hzw]
      exact inverseBranch_left_inv c n V hVo hVc hcrit a.val ha hzC
    refine ⟨a, hbranch, ?_⟩
    intro b hb
    by_contra hba
    have hd := inverseBranch_ranges_disjoint c n V hVo hVc hcrit y hy b a hba
    exact Set.disjoint_left.mp hd ⟨w, hw, hb⟩ ⟨w, hw, hbranch⟩
  · rintro ⟨a, ha, _⟩
    have haV : orbit c n a.val ∈ V := by rw [a.property]; exact hy
    rw [← ha]
    exact inverseBranch_right_inv c n V hVo hVc hcrit a.val haV hw

/-- The union of all canonical analytic branch ranges is exactly
the full physical inverse image, with no omitted components. -/
theorem inverseBranch_ranges_cover (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (y : ℂ) (hy : y ∈ V) :
    (⋃ a : inverseFiber c n y, inverseBranch c n V a.val '' V) =
      (orbit c n) ⁻¹' V := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, w, hw, rfl⟩ := mem_iUnion.mp hz
    have ha : orbit c n a.val ∈ V := by rw [a.property]; exact hy
    change orbit c n (inverseBranch c n V a.val w) ∈ V
    rw [inverseBranch_right_inv c n V hVo hVc hcrit a.val ha hw]
    exact hw
  · intro hz
    obtain ⟨a, ha, _⟩ :=
      (inverseBranch_fiber_exhaustion c n V hVo hVc hcrit y hy
        (orbit c n z) hz z).mp rfl
    exact mem_iUnion.mpr ⟨a, orbit c n z, hz, ha⟩

/-- Every branch in the complete atlas is analytic on the same
entire target and normalized at its actual anchor inverse point. -/
theorem inverseBranch_atlas_analytic (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (y : ℂ) (hy : y ∈ V) :
    ∀ a : inverseFiber c n y,
      AnalyticOnNhd ℂ (inverseBranch c n V a.val) V ∧
      inverseBranch c n V a.val y = a.val := by
  intro a
  have ha : orbit c n a.val ∈ V := by rw [a.property]; exact hy
  refine ⟨inverseBranch_analytic c n V hVo hVc hcrit a.val ha, ?_⟩
  rw [← a.property]
  exact inverseBranch_anchor c n V hVo hVc hcrit a.val ha

/-- Moving the source anchor along one canonical branch preserves
the entire branch, since it selects the same physical component. -/
theorem inverseBranch_reanchor (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c n a ∈ V) (w : ℂ) (hw : w ∈ V) :
    inverseBranch c n V (inverseBranch c n V a w) = inverseBranch c n V a := by
  have hC : inverseComponent c n V a =
      inverseComponent c n V (inverseBranch c n V a w) :=
    connectedComponentIn_eq (inverseBranch_mapsTo c n V hVo hVc hcrit a ha hw)
  change invFunOn (orbit c n)
      (inverseComponent c n V (inverseBranch c n V a w)) =
    invFunOn (orbit c n) (inverseComponent c n V a)
  rw [← hC]

/-- The complete inverse fibers over any two points of the same
regular target are canonically transported by the constructed branches. -/
def fiberTransport (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (y : ℂ) (hy : y ∈ V)
    (w : ℂ) (hw : w ∈ V) : inverseFiber c n y ≃ inverseFiber c n w where
  toFun a := ⟨inverseBranch c n V a.val w,
    inverseBranch_right_inv c n V hVo hVc hcrit a.val (a.property.symm ▸ hy) hw⟩
  invFun b := ⟨inverseBranch c n V b.val y,
    inverseBranch_right_inv c n V hVo hVc hcrit b.val (b.property.symm ▸ hw) hy⟩
  left_inv a := by
    apply Subtype.ext
    change inverseBranch c n V (inverseBranch c n V a.val w) y = a.val
    rw [inverseBranch_reanchor c n V hVo hVc hcrit a.val (a.property.symm ▸ hy) w hw]
    rw [← a.property]
    exact inverseBranch_anchor c n V hVo hVc hcrit a.val (a.property.symm ▸ hy)
  right_inv b := by
    apply Subtype.ext
    change inverseBranch c n V (inverseBranch c n V b.val y) w = b.val
    rw [inverseBranch_reanchor c n V hVo hVc hcrit b.val (b.property.symm ▸ hw) y hy]
    rw [← b.property]
    exact inverseBranch_anchor c n V hVo hVc hcrit b.val (b.property.symm ▸ hw)

/-- The canonical transport is the identity when the target anchor
does not move. -/
theorem fiberTransport_self (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (y : ℂ) (hy : y ∈ V) :
    fiberTransport c n V hVo hVc hcrit y hy y hy = Equiv.refl (inverseFiber c n y) := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  change inverseBranch c n V a.val y = a.val
  rw [← a.property]
  exact inverseBranch_anchor c n V hVo hVc hcrit a.val (a.property.symm ▸ hy)

/-- Rebasing the atlas through an intermediate target has no effect.
This is an exact identity of the actual full inverse-fiber equivalences. -/
theorem fiberTransport_trans (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (y : ℂ) (hy : y ∈ V)
    (w : ℂ) (hw : w ∈ V) (v : ℂ) (hv : v ∈ V) :
    (fiberTransport c n V hVo hVc hcrit y hy w hw).trans
      (fiberTransport c n V hVo hVc hcrit w hw v hv) =
        fiberTransport c n V hVo hVc hcrit y hy v hv := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  change inverseBranch c n V (inverseBranch c n V a.val w) v =
    inverseBranch c n V a.val v
  rw [inverseBranch_reanchor c n V hVo hVc hcrit a.val (a.property.symm ▸ hy) w hw]

/-- All continuous lifts of a given map through the actual iterate.
There is no restriction to a preselected source sheet. -/
def continuousLifts {X : Type*} [TopologicalSpace X]
    (c : ℂ) (n : ℕ) (γ : C(X, ℂ)) :=
  {Γ : C(X, ℂ) // ∀ x, orbit c n (Γ x) = γ x}

/-- Evaluation at one point of the domain records an actual inverse
point, rather than a separate symbolic label. -/
def liftAnchor {X : Type*} [TopologicalSpace X]
    (c : ℂ) (n : ℕ) (γ : C(X, ℂ)) (x₀ : X) :
    continuousLifts c n γ → inverseFiber c n (γ x₀) :=
  fun Γ => ⟨Γ.val x₀, Γ.property x₀⟩

/-- The complete family of continuous lifts is classified exactly by
the actual fiber at one point of any preconnected source space. -/
theorem liftAnchor_bijective {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V)
    (γ : C(X, ℂ)) (hγ : ∀ x, γ x ∈ V) (x₀ : X) :
    Bijective (liftAnchor c n γ x₀) := by
  constructor
  · intro Γ Δ h
    have hbase : Γ.val x₀ = Δ.val x₀ := congrArg Subtype.val h
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    calc
      Γ.val x = inverseBranch c n V (Γ.val x₀) (γ x) :=
        continuous_map_lift_eq_inverse c n V hVo hVc hcrit γ Γ.val hγ
          Γ.property x₀ (Γ.val x₀) rfl x
      _ = Δ.val x :=
        (continuous_map_lift_eq_inverse c n V hVo hVc hcrit γ Δ.val hγ
          Δ.property x₀ (Γ.val x₀) hbase.symm x).symm
  · intro a
    obtain ⟨Γ, hΓ, _⟩ :=
      continuous_map_lift_exists_unique c n V hVo hVc hcrit γ hγ x₀ a.val a.property
    exact ⟨⟨Γ, hΓ.1⟩, Subtype.ext hΓ.2⟩

/-- The explicit classification equivalence for whole continuous lifts. -/
def liftFiberEquiv {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V)
    (γ : C(X, ℂ)) (hγ : ∀ x, γ x ∈ V) (x₀ : X) :
    continuousLifts c n γ ≃ inverseFiber c n (γ x₀) :=
  Equiv.ofBijective (liftAnchor c n γ x₀)
    (liftAnchor_bijective c n V hVo hVc hcrit γ hγ x₀)

/-- Every continuous map from a nonempty preconnected source into
the regular target has exactly `2^n` complete continuous lifts. -/
theorem continuous_lifts_card {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V)
    (γ : C(X, ℂ)) (hγ : ∀ x, γ x ∈ V) (x₀ : X) :
    Nat.card (continuousLifts c n γ) = 2^n := by
  rw [Nat.card_congr (liftFiberEquiv c n V hVo hVc hcrit γ hγ x₀)]
  exact inverseFiber_card c n (γ x₀)
    (fun k hk he => hcrit k hk (he.symm ▸ hγ x₀))

/-- Distinct complete continuous lifts differ at every source point.
They cannot meet and then separate or switch physical inverse sheets. -/
theorem continuous_lifts_pointwise_distinct {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V)
    (γ : C(X, ℂ)) (hγ : ∀ x, γ x ∈ V)
    (Γ Δ : continuousLifts c n γ) (hne : Γ ≠ Δ) :
    ∀ x, Γ.val x ≠ Δ.val x := by
  intro x h
  apply hne
  exact (liftAnchor_bijective c n V hVo hVc hcrit γ hγ x).1 (Subtype.ext h)

end

end LoopsQuadraticInverseBranches
