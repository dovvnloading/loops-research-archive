import QuadraticParameterInverse

/-!
# Exact open inverse components with controlled compact closures

A selected analytic inverse on a neighborhood of a compact target closure
fills the complete global open pullback component. The compact closure
prevents an additional continuation through the boundary of the inverse
source. These lemmas concern the actual quadratic iterate.
-/

namespace LoopsQuadraticInverseOpen

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeCollar
open LoopsTelescopeUnivalentCollars LoopsQuadraticParameterInverse

noncomputable section

/-- A compact critical-free injective selected component maps onto its
entire connected compact target. Surjectivity is derived from the open
collar construction, rather than imposed on the compact core. -/
theorem quadratic_compact_component_image (c : ℂ) (n : ℕ)
    (K : Set ℂ) (x : ℂ) (hK : IsCompact K) (hKconn : IsPreconnected K)
    (hx : orbit c n x ∈ K)
    (hI : InjOn (orbit c n) (connectedComponentIn (orbit c n ⁻¹' K) x))
    (hcrit : ∀ z ∈ connectedComponentIn (orbit c n ⁻¹' K) x,
      ∀ j < n, orbit c j z ≠ 0) :
    orbit c n '' connectedComponentIn (orbit c n ⁻¹' K) x = K := by
  obtain ⟨V, g, _, _, hKV, _, _, _, _, _, _, _, hright, _, hcore, _⟩ :=
    selected_univalent_analytic_collar c n K univ x hK hKconn hx
      isOpen_univ (subset_univ _) hI hcrit
  apply Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact connectedComponentIn_subset (orbit c n ⁻¹' K) x hz
  · intro y hy
    refine ⟨g y, ?_, hright (hKV hy)⟩
    rw [← hcore]
    exact ⟨y, hy, rfl⟩

/-- A nonempty connected compact target has a connected open
neighborhood whose compact closure lies in any prescribed open set. -/
theorem connected_precompact_target_neighborhood (K W : Set ℂ)
    (hK : IsCompact K) (hKconn : IsPreconnected K)
    (y : ℂ) (hy : y ∈ K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ V : Set ℂ, IsOpen V ∧ IsPreconnected V ∧ K ⊆ V ∧
      IsCompact (closure V) ∧ closure V ⊆ W := by
  obtain ⟨O, hO, hKO, hOW, hOc⟩ :=
    exists_open_between_and_isCompact_closure hK hW hKW
  let V := connectedComponentIn O y
  have hVO : V ⊆ O := connectedComponentIn_subset O y
  have hcl : closure V ⊆ closure O := closure_mono hVO
  exact ⟨V, hO.connectedComponentIn, isPreconnected_connectedComponentIn,
    hKconn.subset_connectedComponentIn hy hKO,
    hOc.of_isClosed_subset isClosed_closure hcl, hcl.trans hOW⟩

/-- An inverse defined on a neighborhood of the target closure identifies
an entire global open pullback component and keeps its closure inside the
source. No simple connectivity or boundary regularity is required. -/
theorem quadratic_inverse_open_component (c : ℂ) (n : ℕ)
    (U T V : Set ℂ) (g : ℂ → ℂ)
    (hU : IsOpen U) (hV : IsOpen V) (hVc : IsPreconnected V)
    (hVcl : IsCompact (closure V)) (hclV : closure V ⊆ T)
    (hg : ContinuousOn g T) (hmap : MapsTo g T U)
    (hleft : LeftInvOn g (orbit c n) U)
    (hright : RightInvOn g (orbit c n) T)
    (y : ℂ) (hy : y ∈ V) :
    g '' V = connectedComponentIn (orbit c n ⁻¹' V) (g y) ∧
      IsOpen (g '' V) ∧ IsPreconnected (g '' V) ∧
      IsCompact (closure (g '' V)) ∧ closure (g '' V) ⊆ U ∧
      orbit c n '' (g '' V) = V ∧
      InjOn (orbit c n) (closure (g '' V)) := by
  have hVT : V ⊆ T := subset_closure.trans hclV
  have hgc : IsCompact (g '' closure V) :=
    hVcl.image_of_continuousOn (hg.mono hclV)
  have hcl : closure (g '' V) ⊆ g '' closure V :=
    closure_minimal (image_mono subset_closure) hgc.isClosed
  have hclosedImageU : g '' closure V ⊆ U := by
    rintro z ⟨w, hw, rfl⟩
    exact hmap (hclV hw)
  have hclU : closure (g '' V) ⊆ U := hcl.trans hclosedImageU
  have hcompactComponent := quadratic_inverse_compact_component c n U (closure V) g
    hU hVcl hVc.closure (hg.mono hclV)
    (fun w hw => hmap (hclV hw)) hleft
    (fun w hw => hright (hclV hw)) y (subset_closure hy)
  have hcomponentU : connectedComponentIn (orbit c n ⁻¹' V) (g y) ⊆ U := by
    intro z hz
    have hz' := connectedComponentIn_mono (g y) (preimage_mono (subset_closure : V ⊆ closure V)) hz
    rw [← hcompactComponent] at hz'
    exact hclosedImageU hz'
  have hconn : IsPreconnected (g '' V) := hVc.image g (hg.mono hVT)
  have heq : g '' V = connectedComponentIn (orbit c n ⁻¹' V) (g y) := by
    apply Subset.antisymm
    · apply hconn.subset_connectedComponentIn ⟨y, hy, rfl⟩
      rintro z ⟨w, hw, rfl⟩
      change orbit c n (g w) ∈ V
      rwa [hright (hVT hw)]
    · intro z hz
      exact ⟨orbit c n z, connectedComponentIn_subset _ _ hz, hleft (hcomponentU hz)⟩
  refine ⟨heq, ?_, hconn,
    hgc.of_isClosed_subset isClosed_closure hcl, hclU, ?_, ?_⟩
  · rw [heq]
    exact (hV.preimage (quadratic_orbit_continuous c n)).connectedComponentIn
  · apply Subset.antisymm
    · rintro z ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      rwa [hright (hVT hv)]
    · intro z hz
      exact ⟨g z, ⟨z, hz, rfl⟩, hright (hVT hz)⟩
  · intro z hz w hw he
    calc
      z = g (orbit c n z) := (hleft (hclU hz)).symm
      _ = g (orbit c n w) := congrArg g he
      _ = w := hleft (hclU hw)

end

end LoopsQuadraticInverseOpen
