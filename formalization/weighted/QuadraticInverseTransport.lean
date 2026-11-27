import QuadraticRegularInverse

/-!
# Coherent transport of the complete physical inverse atlas

Actual prefix images determine residual-clock branches. Enlarging a
regular target preserves the normalized inverse, and a connected source
forces its same-clock target component from one anchor. The commuting
identity derives target-sheet containment in the full physical atlas.
-/

namespace LoopsQuadraticInverseTransport

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsQuadraticCylinderRamification LoopsQuadraticRegularInverse
open LoopsTelescopeConformalInverse

noncomputable section

/-- Splitting the physical clock preserves the complete selected
component, even before regularity or univalence is established. -/
theorem inverseComponent_split (c : ℂ) (p q : ℕ) (V : Set ℂ)
    (a : ℂ) (ha : orbit c (p+q) a ∈ V) :
    inverseComponent c p (inverseComponent c q V (orbit c p a)) a =
      inverseComponent c (p+q) V a := by
  have hcomp : orbit c q ∘ orbit c p = orbit c (p+q) := by
    funext z
    exact (quadratic_orbit_add c p q z).symm
  have h := component_pullback_comp (orbit c p) (orbit c q) V a
    (quadratic_orbit_continuous c p)
    (by rwa [← quadratic_orbit_add])
  rw [hcomp] at h
  exact h

/-- The prefix image is the whole residual component. -/
theorem inverseComponent_prefix_image (c : ℂ) (p q : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (a : ℂ) (ha : orbit c (p+q) a ∈ V) :
    orbit c p '' inverseComponent c (p+q) V a =
      inverseComponent c q V (orbit c p a) := by
  have h := quadratic_prefix_component_image c q p V hVo a
    (by simpa only [orbit_map_eq_iterate, Nat.add_comm] using ha)
  simpa only [inverseComponent, orbit_map_eq_iterate, Nat.add_comm] using h

/-- Every residual-clock analytic branch is the actual prefix of the
longer branch, with equality on the entire target. -/
theorem inverseBranch_prefix (c : ℂ) (p q : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < p+q, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c (p+q) a ∈ V) :
    EqOn (orbit c p ∘ inverseBranch c (p+q) V a)
      (inverseBranch c q V (orbit c p a)) V := by
  have htail : orbit c q (orbit c p a) ∈ V := by
    rwa [← quadratic_orbit_add]
  have hcritq : ∀ k < q, orbit c k c ∉ V := fun k hk => hcrit k (by omega)
  intro y hy
  have hz := inverseBranch_mapsTo c (p+q) V hVo hVc hcrit a ha hy
  have hm : orbit c p (inverseBranch c (p+q) V a y) ∈
      inverseComponent c q V (orbit c p a) := by
    rw [← inverseComponent_prefix_image c p q V hVo a ha]
    exact ⟨inverseBranch c (p+q) V a y, hz, rfl⟩
  apply inverseComponent_injOn c q V hVo hVc hcritq (orbit c p a) htail
    hm (inverseBranch_mapsTo c q V hVo hVc hcritq (orbit c p a) htail hy)
  rw [← quadratic_orbit_add,
    inverseBranch_right_inv c (p+q) V hVo hVc hcrit a ha hy,
    inverseBranch_right_inv c q V hVo hVc hcritq (orbit c p a) htail hy]

/-- A branch of a concatenated actual iterate is exactly the
composition of the suffix inverse and the corresponding prefix inverse.
The intermediate domain is the constructed full physical component. -/
theorem inverseBranch_concatenation (c : ℂ) (p q : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < p+q, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c (p+q) a ∈ V) :
    EqOn (inverseBranch c (p+q) V a)
      (inverseBranch c p (inverseComponent c q V (orbit c p a)) a ∘
        inverseBranch c q V (orbit c p a)) V := by
  let C := inverseComponent c (p+q) V a
  let D := inverseComponent c q V (orbit c p a)
  have htail : orbit c q (orbit c p a) ∈ V := by
    rwa [← quadratic_orbit_add]
  have hcritq : ∀ k < q, orbit c k c ∉ V := fun k hk => hcrit k (by omega)
  have hpi : InjOn (orbit c p) C := by
    intro x hx z hz he
    apply inverseComponent_injOn c (p+q) V hVo hVc hcrit a ha hx hz
    rw [quadratic_orbit_add, quadratic_orbit_add, he]
  have hqi : InjOn (orbit c q) D :=
    inverseComponent_injOn c q V hVo hVc hcritq (orbit c p a) htail
  have h := orbit_inverse_concatenation c p q C D V
    (inverseComponent_prefix_image c p q V hVo a ha)
    (inverseComponent_image c q V hVo hVc (orbit c p a) htail) hpi hqi
  change EqOn (Function.invFunOn (orbit c (p+q)) C)
    (Function.invFunOn (orbit c p)
      (inverseComponent c p (inverseComponent c q V (orbit c p a)) a) ∘
      Function.invFunOn (orbit c q) D) V
  rw [inverseComponent_split c p q V a ha]
  exact h

/-- Enlarging a regular target preserves its normalized analytic
branch on the retained target. Source inclusion is derived. -/
theorem inverseBranch_target_restriction (c : ℂ) (n : ℕ) (V W : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hWo : IsOpen W) (hWc : IsSimplyConnected W) (hVW : V ⊆ W)
    (hcrit : ∀ k < n, orbit c k c ∉ W) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    EqOn (inverseBranch c n V a) (inverseBranch c n W a) V := by
  have hsub : inverseComponent c n V a ⊆ inverseComponent c n W a :=
    connectedComponentIn_mono a (preimage_mono hVW)
  have h := orbit_inverse_restriction_agreement c n
    (inverseComponent c n V a) (inverseComponent c n W a) hsub
    (inverseComponent_injOn c n W hWo hWc hcrit a (hVW ha))
  rw [inverseComponent_image c n V hVo hVc a ha] at h
  exact h

/-- A regular enlargement has no extra points in a selected old sheet
over the retained target. -/
theorem inverseComponent_target_restriction (c : ℂ) (n : ℕ) (V W : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hWo : IsOpen W) (hWc : IsSimplyConnected W) (hVW : V ⊆ W)
    (hcrit : ∀ k < n, orbit c k c ∉ W) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    inverseComponent c n W a ∩ (orbit c n ⁻¹' V) =
      inverseComponent c n V a := by
  have hcritV : ∀ k < n, orbit c k c ∉ V :=
    fun k hk h => hcrit k hk (hVW h)
  have hsub : inverseComponent c n V a ⊆ inverseComponent c n W a :=
    connectedComponentIn_mono a (preimage_mono hVW)
  apply Subset.antisymm
  · intro x hx
    have he := inverseBranch_target_restriction c n V W hVo hVc
      hWo hWc hVW hcrit a ha hx.2
    rw [inverseBranch_left_inv c n W hWo hWc hcrit a (hVW ha) hx.1] at he
    exact he ▸ inverseBranch_mapsTo c n V hVo hVc hcritV a ha hx.2
  · intro x hx
    exact ⟨hsub hx, connectedComponentIn_subset (orbit c n ⁻¹' V) a hx⟩

/-- A continuous image in a full pullback belongs to the component
selected by one actual anchor. No sheet-containment premise is needed. -/
theorem connected_image_selects_component {X : Type*} [TopologicalSpace X]
    (c : ℂ) (n : ℕ) (W : Set ℂ) (S : Set X) (hS : IsPreconnected S)
    (g : X → ℂ) (hg : ContinuousOn g S)
    (hm : MapsTo (orbit c n ∘ g) S W)
    (x : X) (hx : x ∈ S) :
    MapsTo g S (inverseComponent c n W (g x)) := by
  have hc : IsPreconnected (g '' S) := hS.image g hg
  have hsub : g '' S ⊆ orbit c n ⁻¹' W := by
    rintro z ⟨y, hy, rfl⟩
    exact hm hy
  have h := hc.subset_connectedComponentIn ⟨x, hx, rfl⟩ hsub
  intro y hy
  exact h ⟨y, hy, rfl⟩

/-- The actual base image and one anchor force same-clock ownership. -/
theorem inverseBranch_reached_component (c : ℂ) (n j : ℕ) (V W : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcritV : ∀ k < n, orbit c k c ∉ V)
    (hmap : MapsTo (orbit c j) V W) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    MapsTo (orbit c j ∘ inverseBranch c n V a) V
      (inverseComponent c n W (orbit c j a)) := by
  have hcont : ContinuousOn (orbit c j ∘ inverseBranch c n V a) V :=
    (quadratic_orbit_continuous c j).continuousOn.comp
      (inverseBranch_analytic c n V hVo hVc hcritV a ha).continuousOn
      (mapsTo_univ _ _)
  have htarget : MapsTo
      (orbit c n ∘ (orbit c j ∘ inverseBranch c n V a)) V W := by
    intro y hy
    change orbit c n (orbit c j (inverseBranch c n V a y)) ∈ W
    rw [← quadratic_orbit_add, Nat.add_comm j n, quadratic_orbit_add,
      inverseBranch_right_inv c n V hVo hVc hcritV a ha hy]
    exact hmap hy
  have h := connected_image_selects_component c n W V
    hVc.isPathConnected.isConnected.isPreconnected
    (orbit c j ∘ inverseBranch c n V a) hcont htarget (orbit c n a) ha
  simpa only [Function.comp_apply,
    inverseBranch_anchor c n V hVo hVc hcritV a ha] using h

/-- A commuting lift with a constructed actual target branch.
Target-cylinder containment is a conclusion of the preceding theorem. -/
theorem inverseBranch_commuting_lift (c : ℂ) (n j : ℕ) (V W : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hWo : IsOpen W) (hWc : IsSimplyConnected W)
    (hcritV : ∀ k < n, orbit c k c ∉ V)
    (hcritW : ∀ k < n, orbit c k c ∉ W)
    (hmap : MapsTo (orbit c j) V W) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    EqOn (orbit c j ∘ inverseBranch c n V a)
      (inverseBranch c n W (orbit c j a) ∘ orbit c j) V := by
  have haW : orbit c n (orbit c j a) ∈ W := by
    rw [← quadratic_orbit_add, Nat.add_comm j n, quadratic_orbit_add]
    exact hmap ha
  intro y hy
  have hsource := inverseBranch_reached_component c n j V W hVo hVc
    hcritV hmap a ha hy
  have htarget := inverseBranch_mapsTo c n W hWo hWc hcritW
    (orbit c j a) haW (hmap hy)
  apply inverseComponent_injOn c n W hWo hWc hcritW (orbit c j a) haW
    hsource htarget
  change orbit c n (orbit c j (inverseBranch c n V a y)) =
    orbit c n (inverseBranch c n W (orbit c j a) (orbit c j y))
  rw [← quadratic_orbit_add, Nat.add_comm j n, quadratic_orbit_add,
    inverseBranch_right_inv c n V hVo hVc hcritV a ha hy,
    inverseBranch_right_inv c n W hWo hWc hcritW (orbit c j a) haW (hmap hy)]

/-- Surjectivity of the base iterate yields equality with the full
selected target cylinder, rather than only image containment. -/
theorem inverseComponent_commuting_image (c : ℂ) (n j : ℕ) (V W : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hWo : IsOpen W) (hWc : IsSimplyConnected W)
    (hcritV : ∀ k < n, orbit c k c ∉ V)
    (hcritW : ∀ k < n, orbit c k c ∉ W)
    (himage : orbit c j '' V = W) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    orbit c j '' inverseComponent c n V a =
      inverseComponent c n W (orbit c j a) := by
  have hmap : MapsTo (orbit c j) V W := by
    intro y hy
    rw [← himage]
    exact ⟨y, hy, rfl⟩
  have haW : orbit c n (orbit c j a) ∈ W := by
    rw [← quadratic_orbit_add, Nat.add_comm j n, quadratic_orbit_add]
    exact hmap ha
  rw [← inverseBranch_image c n V hVo hVc hcritV a ha, ← image_comp]
  rw [(inverseBranch_commuting_lift c n j V W hVo hVc hWo hWc
    hcritV hcritW hmap a ha).image_eq]
  rw [image_comp, himage, inverseBranch_image c n W hWo hWc hcritW
    (orbit c j a) haW]

end
end LoopsQuadraticInverseTransport
