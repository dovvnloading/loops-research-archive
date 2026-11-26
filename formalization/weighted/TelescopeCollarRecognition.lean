import TelescopeRamification
import LeastSaturatedCarrier

/-!
# Actual return-domain recognition and compact pullback margins

An anchored component of an actual open quadratic pullback is a proper
surjective restriction. The one-critical saturated telescope therefore has
degree two over the *whole* target. A separate compactness theorem supplies
uniform margins for perturbations of a compact target, without any finite
component or local connectivity assumption on the compact carriers.
-/

namespace LoopsTelescopeCollar

open Set Function Filter Metric
open QuadraticEscape LoopsSaturatedTelescope LoopsQuadraticCylinderCensus
open LoopsTelescopeRamification
open scoped BigOperators Topology
noncomputable section

theorem orbit_proper (c : ℂ) (n : ℕ) : IsProperMap (orbit c n) := by
  rw [orbit_map_eq_iterate]
  exact quadratic_iterate_proper c n

theorem orbit_open (c : ℂ) (n : ℕ) : IsOpenMap (orbit c n) := by
  rw [orbit_map_eq_iterate]
  exact quadratic_iterate_open c n

/-- The whole target, not just the attained values, is covered. -/
theorem orbit_component_image (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (x : ℂ) (hx : orbit c n x ∈ V) :
    orbit c n '' connectedComponentIn (orbit c n ⁻¹' V) x = V := by
  let f := orbit c n
  let S := f ⁻¹' V
  have hp : IsProperMap f := orbit_proper c n
  have hS : IsOpen S := hVo.preimage hp.continuous
  exact localized_component_image f S V (orbit_open c n) hp.isClosedMap hS hVc
    (fun _ hz => hz) (fun _ hz => hz.2) x hx

theorem orbit_component_compact_preimage (c : ℂ) (n : ℕ) (V K : Set ℂ)
    (x : ℂ) (hVo : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V) :
    IsCompact (connectedComponentIn (orbit c n ⁻¹' V) x ∩ orbit c n ⁻¹' K) := by
  let f := orbit c n
  let C := connectedComponentIn (f ⁻¹' V) x
  have hp : IsProperMap f := orbit_proper c n
  have hrel := open_component_relative_closed (f ⁻¹' V) (hVo.preimage hp.continuous) x
  have he : C ∩ f ⁻¹' K = closure C ∩ f ⁻¹' K := by
    apply Subset.antisymm
    · intro z hz
      exact ⟨subset_closure hz.1, hz.2⟩
    · intro z hz
      exact ⟨hrel ⟨hz.1, hKV hz.2⟩, hz.2⟩
  change IsCompact (C ∩ f ⁻¹' K)
  rw [he]
  exact (hp.isCompact_preimage hK).of_isClosed_subset
    (isClosed_closure.inter (hK.isClosed.preimage hp.continuous)) (fun _ hz => hz.2)

/-- Properness in the actual subspace topologies. -/
theorem orbit_component_proper (c : ℂ) (n : ℕ) (V : Set ℂ) (x : ℂ)
    (hVo : IsOpen V) :
    IsProperMap (fun z : connectedComponentIn (orbit c n ⁻¹' V) x =>
      (⟨orbit c n z, connectedComponentIn_subset (orbit c n ⁻¹' V) x z.property⟩ : V)) := by
  let C := connectedComponentIn (orbit c n ⁻¹' V) x
  let g : C → V := fun z =>
    ⟨orbit c n z, connectedComponentIn_subset (orbit c n ⁻¹' V) x z.property⟩
  change IsProperMap g
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨((quadratic_orbit_continuous c n).comp continuous_subtype_val).subtype_mk _, ?_⟩
  intro K hK
  let L : Set ℂ := ((↑) : V → ℂ) '' K
  have hLc : IsCompact L := hK.image continuous_subtype_val
  have hLV : L ⊆ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact w.property
  have hpre : IsCompact (C ∩ orbit c n ⁻¹' L) :=
    orbit_component_compact_preimage c n V L x hVo hLc hLV
  have hsub : C ∩ orbit c n ⁻¹' L ⊆ range ((↑) : C → ℂ) := by
    rw [Subtype.range_coe]
    exact inter_subset_left
  have he : g ⁻¹' K = ((↑) : C → ℂ) ⁻¹' (C ∩ orbit c n ⁻¹' L) := by
    ext z
    change g z ∈ K ↔ (z : ℂ) ∈ C ∩ orbit c n ⁻¹' L
    constructor
    · intro hz
      exact ⟨z.property, ⟨g z, hz, rfl⟩⟩
    · rintro ⟨_, ⟨w, hw, he⟩⟩
      have he' : w = g z := Subtype.ext he
      exact he' ▸ hw
  rw [he]
  exact IsInducing.subtypeVal.isCompact_preimage' hpre hsub

/-- A saturated one-critical return is exactly the selected full
pullback, covers its whole target properly, and has constant total
analytic multiplicity two. Surjectivity of the prefix and the full
return is derived, not assumed. -/
theorem selected_saturated_return_full_degree (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    A = connectedComponentIn (orbit c (a+1+b) ⁻¹' V) x ∧
    orbit c (a+1+b) '' A = V ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ V → IsCompact (A ∩ orbit c (a+1+b) ⁻¹' K)) ∧
    ∀ v ∈ V, (∑ z ∈ localFiber c (a+1+b) A v,
      analyticOrderNatAt (fun w => orbit c (a+1+b) w-v) z) = 2 := by
  have hc : c ∈ D := by
    rw [hD]
    exact mem_connectedComponentIn hv
  have h0 : (0 : ℂ) ∈ B := by
    rw [hB]
    exact mem_connectedComponentIn (show (0 : ℂ)^2+c ∈ D by simpa using hc)
  have hDo : IsOpen D := by
    rw [hD]
    exact (hVo.preimage (quadratic_orbit_continuous c b)).connectedComponentIn
  have hq : Continuous (fun w : ℂ => w^2+c) := (continuous_id.pow 2).add continuous_const
  have hBo : IsOpen B := by
    rw [hB]
    exact (hDo.preimage hq).connectedComponentIn
  have hBc : IsPreconnected B := by
    rw [hB]
    exact isPreconnected_connectedComponentIn
  have hAo : IsOpen A := by
    rw [hA]
    exact (hBo.preimage (quadratic_orbit_continuous c a)).connectedComponentIn
  have hAp : orbit c a '' A = B := by
    rw [hA]
    exact orbit_component_image c a B hBo hBc x (by simpa [hx0] using h0)
  have hfun1 : (orbit c b ∘ (fun w : ℂ => w^2+c)) = orbit c (1+b) := by
    funext z
    exact (quadratic_orbit_add c 1 b z).symm
  have hbcomp := component_pullback_comp (fun w : ℂ => w^2+c) (orbit c b)
    V 0 hq (by simpa using hv)
  have hB' : B = connectedComponentIn (orbit c (1+b) ⁻¹' V) 0 := by
    rw [hB, hD]
    simpa only [show (0 : ℂ)^2+c=c by simp, hfun1] using hbcomp
  have hterm : orbit c (a+1+b) x ∈ V := by
    rw [quadratic_orbit_add c (a+1) b x]
    change orbit c b ((orbit c a x)^2+c) ∈ V
    simpa [hx0] using hv
  have hfun2 : (orbit c (1+b) ∘ orbit c a) = orbit c (a+1+b) := by
    funext z
    change orbit c (1+b) (orbit c a z) = orbit c (a+1+b) z
    rw [show a+1+b=a+(1+b) by omega, quadratic_orbit_add]
  have hretcomp := component_pullback_comp (orbit c a) (orbit c (1+b)) V x
    (quadratic_orbit_continuous c a) (by
      change (orbit c (1+b) ∘ orbit c a) x ∈ V
      rw [hfun2]
      exact hterm)
  have hsat : A = connectedComponentIn (orbit c (a+1+b) ⁻¹' V) x := by
    rw [hA, hB']
    simpa only [hx0, hfun2] using hretcomp
  have honto : orbit c (a+1+b) '' A = V := by
    rw [hsat]
    exact orbit_component_image c (a+1+b) V hVo hVc x hterm
  refine ⟨hsat, honto, ?_, ?_⟩
  · intro K hK hKV
    rw [hsat]
    exact orbit_component_compact_preimage c (a+1+b) V K x hVo hK hKV
  · intro v hv'
    exact selected_return_weighted_degree c a b A B D hc hAo hDo hB hAp hpinj hrinj
      v (honto.symm ▸ hv')

/-- Compact pullbacks have compact selected components, with no
local-connectivity hypothesis on the target. -/
theorem proper_component_compact (f : ℂ → ℂ) (hf : IsProperMap f)
    (K : Set ℂ) (hK : IsCompact K) (x : ℂ) (hx : f x ∈ K) :
    IsCompact (connectedComponentIn (f ⁻¹' K) x) := by
  let C := connectedComponentIn (f ⁻¹' K) x
  have hSclosed : IsClosed (f ⁻¹' K) := hK.isClosed.preimage hf.continuous
  have hclsub : closure C ⊆ f ⁻¹' K :=
    hSclosed.closure_subset_iff.mpr (connectedComponentIn_subset _ _)
  have hpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hcc : closure C ⊆ C :=
    hpre.closure.subset_connectedComponentIn (subset_closure (mem_connectedComponentIn hx)) hclsub
  have hclosed : IsClosed C := by
    rw [← (Subset.antisymm hcc subset_closure : closure C = C)]
    exact isClosed_closure
  exact (hf.isCompact_preimage hK).of_isClosed_subset hclosed
    (connectedComponentIn_subset _ _)

/-- Uniform eventual containment of a selected pullback component of
nested compact targets in every open neighborhood of the limit component. -/
theorem proper_component_eventually_subset (f : ℂ → ℂ) (hf : IsProperMap f)
    (D : ℕ → Set ℂ) (hD : ∀ n, IsCompact (D n)) (hmD : Antitone D)
    (x : ℂ) (hx : ∀ n, f x ∈ D n) (U : Set ℂ) (hU : IsOpen U)
    (hlim : connectedComponentIn (f ⁻¹' (⋂ n, D n)) x ⊆ U) :
    ∃ N : ℕ, ∀ n ≥ N, connectedComponentIn (f ⁻¹' D n) x ⊆ U := by
  let C : ℕ → Set ℂ := fun n => connectedComponentIn (f ⁻¹' D n) x
  have hc : ∀ n, IsCompact (C n) := fun n => proper_component_compact f hf (D n) (hD n) x (hx n)
  have hm : Antitone C := fun i j hij => connectedComponentIn_mono x (preimage_mono (hmD hij))
  have hd : Directed (· ⊇ ·) C := by
    intro i j
    exact ⟨max i j, hm (le_max_left i j), hm (le_max_right i j)⟩
  have hI := LoopsLeastCarrier.directed_component_intersection f (C 0) (hc 0) C D x hc
    (fun n => hm (Nat.zero_le n)) hd (fun n => mem_connectedComponentIn (hx n)) (fun _ => rfl)
  have hbad : IsCompact (C 0 ∩ Uᶜ) := (hc 0).inter_right hU.isClosed_compl
  have hempty : (C 0 ∩ Uᶜ) ∩ (⋂ n, C n) = ∅ := by
    rw [hI]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.1.2 (hlim hz.2)
  obtain ⟨N, hN⟩ := hbad.elim_directed_family_closed C (fun j => (hc j).isClosed) hempty hd
  refine ⟨N, ?_⟩
  intro n hn z hz
  by_contra hnot
  have hzbad : z ∈ (C 0 ∩ Uᶜ) ∩ C N := ⟨⟨hm (Nat.zero_le n) hz, hnot⟩, hm hn hz⟩
  rw [hN] at hzbad
  exact hzbad

/-- One uniform target margin works for arbitrary nearby targets,
not merely a predetermined nested exhaustion. -/
theorem proper_component_upper_semicontinuous (f : ℂ → ℂ) (hf : IsProperMap f)
    (K : Set ℂ) (hK : IsCompact K) (x : ℂ) (hx : f x ∈ K)
    (U : Set ℂ) (hU : IsOpen U) (hlim : connectedComponentIn (f ⁻¹' K) x ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ T : Set ℂ, T ⊆ cthickening δ K →
      connectedComponentIn (f ⁻¹' T) x ⊆ U := by
  let S : ℕ → Set ℂ := fun n => cthickening (1 / ((n : ℝ) + 1)) K
  have hc : ∀ n, IsCompact (S n) := fun _ => hK.cthickening
  have hm : Antitone S := by
    intro i j hij
    have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact cthickening_mono
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)) K
  have hI : (⋂ n, S n) = K := by
    apply Subset.antisymm
    · intro z hz
      by_contra hnot
      have hsub : K ⊆ ({z} : Set ℂ)ᶜ := by
        intro w hw he
        have heq : w = z := mem_singleton_iff.mp he
        exact hnot (heq ▸ hw)
      obtain ⟨δ, hδ, hδsub⟩ :=
        hK.exists_cthickening_subset_open isClosed_singleton.isOpen_compl hsub
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      have hz' : z ∈ cthickening δ K :=
        cthickening_mono hn.le K (mem_iInter.mp hz n)
      exact (hδsub hz') (by simp)
    · intro z hz
      exact mem_iInter.mpr fun n => self_subset_cthickening K hz
  obtain ⟨N, hN⟩ := proper_component_eventually_subset f hf S hc hm x
    (fun n => self_subset_cthickening K hx) U hU (by rwa [hI])
  exact ⟨1 / ((N : ℝ) + 1), by positivity,
    fun T hT => (connectedComponentIn_mono x (preimage_mono hT)).trans (hN N le_rfl)⟩

end
end LoopsTelescopeCollar
