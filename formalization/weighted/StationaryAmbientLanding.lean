import TelescopeUnivalentCollars

/-!
# Ambient restrictions land on the selected quadratic predecessor

A continuous restriction may initially live anywhere in the complex plane.
Connectedness, a single anchor, and containment of its full projected trace in
one constructed collar force the entire restriction onto the canonical inverse.
Target landing then implies source landing and convergence of every parent.
-/

namespace LoopsStationaryAmbientLanding

open Set Function Filter
open scoped Topology
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeUnivalentCollars

variable {X Y T : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace T]

/-- An anchor selects a whole pullback component for a connected ambient
restriction. The restriction need not lie in any invariant compact set. -/
theorem anchored_component_confinement (F : X → Y) (V : Set Y) (x : X)
    (S : Set T) (t₀ : T) (γ : T → X)
    (hS : IsPreconnected S) (ht₀ : t₀ ∈ S) (hγ : ContinuousOn γ S)
    (hproject : MapsTo (fun t => F (γ t)) S V)
    (hanchor : γ t₀ ∈ connectedComponentIn (F ⁻¹' V) x) :
    γ '' S ⊆ connectedComponentIn (F ⁻¹' V) x := by
  have hsub : γ '' S ⊆ F ⁻¹' V := by
    rintro z ⟨t, ht, rfl⟩
    exact hproject ht
  have hcomp := (hS.image γ hγ).subset_connectedComponentIn
    (show γ t₀ ∈ γ '' S from ⟨t₀, ht₀, rfl⟩) hsub
  have heq : connectedComponentIn (F ⁻¹' V) (γ t₀) =
      connectedComponentIn (F ⁻¹' V) x :=
    (connectedComponentIn_eq hanchor).symm
  exact heq ▸ hcomp

/-- Every point of the supplied ambient restriction agrees with the
canonical inverse; only its anchor was required to be in that component. -/
theorem anchored_lift_agrees (F : X → Y) (V : Set Y) (x : X) (g : Y → X)
    (hleft : LeftInvOn g F (connectedComponentIn (F ⁻¹' V) x))
    (S : Set T) (t₀ : T) (γ : T → X)
    (hS : IsPreconnected S) (ht₀ : t₀ ∈ S) (hγ : ContinuousOn γ S)
    (hproject : MapsTo (fun t => F (γ t)) S V)
    (hanchor : γ t₀ ∈ connectedComponentIn (F ⁻¹' V) x) :
    ∀ t ∈ S, γ t = g (F (γ t)) := by
  have hsub := anchored_component_confinement F V x S t₀ γ hS ht₀ hγ hproject hanchor
  intro t ht
  exact (hleft (hsub ⟨t, ht, rfl⟩)).symm

/-- Exact equality of the full source trace, including all repeated
projected points; no truncation or chosen endpoint is part of the conclusion. -/
theorem anchored_lift_image (F : X → Y) (V : Set Y) (x : X) (g : Y → X)
    (hleft : LeftInvOn g F (connectedComponentIn (F ⁻¹' V) x))
    (S : Set T) (t₀ : T) (γ : T → X)
    (hS : IsPreconnected S) (ht₀ : t₀ ∈ S) (hγ : ContinuousOn γ S)
    (hproject : MapsTo (fun t => F (γ t)) S V)
    (hanchor : γ t₀ ∈ connectedComponentIn (F ⁻¹' V) x) :
    γ '' S = g '' (F '' (γ '' S)) := by
  have heq := anchored_lift_agrees F V x g hleft S t₀ γ hS ht₀ hγ hproject hanchor
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨F (γ t), ⟨γ t, ⟨t, ht, rfl⟩, rfl⟩, (heq t ht).symm⟩
  · rintro ⟨y, ⟨w, ⟨t, ht, rfl⟩, rfl⟩, rfl⟩
    exact ⟨t, ht, heq t ht⟩

/-- Target convergence forces source convergence for any filter eventually
carried by the same connected anchored trace. Source landing is a conclusion. -/
theorem anchored_lift_tendsto (F : X → Y) (V : Set Y) (x : X) (g : Y → X)
    (hleft : LeftInvOn g F (connectedComponentIn (F ⁻¹' V) x))
    (S : Set T) (t₀ : T) (γ : T → X)
    (hS : IsPreconnected S) (ht₀ : t₀ ∈ S) (hγ : ContinuousOn γ S)
    (hproject : MapsTo (fun t => F (γ t)) S V)
    (hanchor : γ t₀ ∈ connectedComponentIn (F ⁻¹' V) x)
    (l : Filter T) (hmem : ∀ᶠ t in l, t ∈ S) (y : Y)
    (hg : ContinuousAt g y)
    (hlimit : Tendsto (fun t => F (γ t)) l (𝓝 y)) :
    Tendsto γ l (𝓝 (g y)) := by
  have heq := anchored_lift_agrees F V x g hleft S t₀ γ hS ht₀ hγ hproject hanchor
  have hevent : γ =ᶠ[l] (fun t => g (F (γ t))) :=
    hmem.mono (fun t ht => heq t ht)
  exact (hg.tendsto.comp hlimit).congr' hevent.symm

/-- Actual compact-core data construct one analytic collar that recognizes
every connected anchored ambient restriction over it, makes its landing
canonical, and fixes every intermediate parent limit. All target points of
the compact core, including a critical point at the terminal time, are allowed. -/
theorem selected_collar_ambient_landing (c : ℂ) (n : ℕ)
    (K W : Set ℂ) (x : ℂ) (hK : IsCompact K) (hKconn : IsPreconnected K)
    (hx : orbit c n x ∈ K) (hW : IsOpen W)
    (hCW : connectedComponentIn (orbit c n ⁻¹' K) x ⊆ W)
    (hI : InjOn (orbit c n) (connectedComponentIn (orbit c n ⁻¹' K) x))
    (hcrit : ∀ z ∈ connectedComponentIn (orbit c n ⁻¹' K) x,
      ∀ j < n, orbit c j z ≠ 0) :
    ∃ (V : Set ℂ) (g : ℂ → ℂ), IsOpen V ∧ IsPreconnected V ∧ K ⊆ V ∧
      let U := connectedComponentIn (orbit c n ⁻¹' V) x
      IsOpen U ∧ IsCompact (closure U) ∧ closure U ⊆ W ∧
        InjOn (orbit c n) (closure U) ∧ orbit c n '' U = V ∧
        MapsTo g V U ∧ LeftInvOn g (orbit c n) U ∧ RightInvOn g (orbit c n) V ∧
        AnalyticOnNhd ℂ g V ∧
        g '' K = connectedComponentIn (orbit c n ⁻¹' K) x ∧
        ∀ (S : Set T) (t₀ : T) (γ : T → ℂ),
          IsPreconnected S → t₀ ∈ S → ContinuousOn γ S →
          MapsTo (fun t => orbit c n (γ t)) S V → γ t₀ ∈ U →
          (∀ t ∈ S, γ t = g (orbit c n (γ t))) ∧
          ∀ (l : Filter T) (y : ℂ), (∀ᶠ t in l, t ∈ S) → y ∈ K →
            Tendsto (fun t => orbit c n (γ t)) l (𝓝 y) →
            Tendsto γ l (𝓝 (g y)) ∧
              g y ∈ connectedComponentIn (orbit c n ⁻¹' K) x ∧
              orbit c n (g y) = y ∧
              ∀ k : ℕ, Tendsto (fun t => orbit c k (γ t)) l (𝓝 (orbit c k (g y))) := by
  obtain ⟨V, g, hV, hVconn, hKV, hU, hUc, hUW, hUI, honto,
    hmap, hleft, hright, hana, hcore, _⟩ :=
    selected_univalent_analytic_collar c n K W x hK hKconn hx hW hCW hI hcrit
  refine ⟨V, g, hV, hVconn, hKV, hU, hUc, hUW, hUI, honto,
    hmap, hleft, hright, hana, hcore, ?_⟩
  intro S t₀ γ hS ht₀ hγ hproject hanchor
  refine ⟨anchored_lift_agrees (orbit c n) V x g hleft S t₀ γ
    hS ht₀ hγ hproject hanchor, ?_⟩
  intro l y hmem hy hlimit
  have hland := anchored_lift_tendsto (orbit c n) V x g hleft S t₀ γ
    hS ht₀ hγ hproject hanchor l hmem y (hana y (hKV hy)).continuousAt hlimit
  have hgy : g y ∈ connectedComponentIn (orbit c n ⁻¹' K) x := by
    rw [← hcore]
    exact mem_image_of_mem g hy
  exact ⟨hland, hgy, hright (hKV hy),
    fun k => (quadratic_orbit_continuous c k).continuousAt.tendsto.comp hland⟩

end LoopsStationaryAmbientLanding
