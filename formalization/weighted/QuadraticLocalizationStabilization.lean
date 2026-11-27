import QuadraticEnlargementStabilization

/-!
# Increasing proper localizations and the entire future source union

The source domains may be disconnected and need not exhaust the full
quadratic inverse image. Properness identifies their connected components
with ambient pullback components. Capturing one finite inverse fiber of
the entire source union then captures every future source point over the
old target. A separate component theorem controls future mergers.
-/

namespace LoopsQuadraticLocalizationStabilization

open Set Function Classical
open LoopsQuadraticCylinderCensus LoopsQuadraticCriticalFiberCensus
open LoopsQuadraticCylinderRamification
open LoopsQuadraticEnlargementStabilization

private theorem finite_union_capture {X : Type*} (S : ℕ → Set X)
    (hmono : Monotone S) (A : Finset X) :
    (∀ a ∈ A, a ∈ ⋃ j, S j) →
      ∃ N : ℕ, ∀ m, N ≤ m → ∀ a ∈ A, a ∈ S m := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨0, ?_⟩
      intro m hm a ha
      exact (Finset.notMem_empty a ha).elim
  | @insert a A ha ih =>
      intro hA
      obtain ⟨Na, hNa⟩ := mem_iUnion.mp (hA a (Finset.mem_insert_self a A))
      obtain ⟨N, hN⟩ := ih (fun b hb => hA b (Finset.mem_insert_of_mem hb))
      refine ⟨max Na N, ?_⟩
      intro m hm b hb
      rcases Finset.mem_insert.mp hb with hba | hbA
      · subst b
        exact hmono ((le_max_left Na N).trans hm) hNa
      · exact hN m ((le_max_right Na N).trans hm) b hbA

private theorem quadratic_union_fiber_captured
    (c : ℂ) (n : ℕ) (S : ℕ → Set ℂ) (hmono : Monotone S) (y : ℂ) :
    ∃ N : ℕ, ∀ m, N ≤ m →
      localFiber c n (S m) y = localFiber c n (⋃ j, S j) y := by
  let A := localFiber c n (⋃ j, S j) y
  have hA : ∀ a ∈ A, a ∈ ⋃ j, S j := by
    intro a ha
    exact ((mem_localFiber c n (⋃ j, S j) y a).mp ha).1
  obtain ⟨N, hN⟩ := finite_union_capture S hmono A hA
  refine ⟨N, ?_⟩
  intro m hm
  ext a
  constructor
  · intro ha
    obtain ⟨haS, hay⟩ := (mem_localFiber c n (S m) y a).mp ha
    exact (mem_localFiber c n (⋃ j, S j) y a).mpr
      ⟨mem_iUnion_of_mem m haS, hay⟩
  · intro ha
    exact (mem_localFiber c n (S m) y a).mpr
      ⟨hN m hm a ha, ((mem_localFiber c n (⋃ j, S j) y a).mp ha).2⟩

/-- Exact future-source saturation at a specified stage is equivalent
to capturing the entire future source fiber over one old target point.
No source connectedness, global fiber exhaustion, regularity, or
no-merger condition is assumed. -/
theorem quadratic_proper_localization_union_iff_fiber
    (c : ℂ) (n : ℕ) (U S : ℕ → Set ℂ)
    (hUmono : Monotone U) (hUopen : ∀ m, IsOpen (U m))
    (hUconn : ∀ m, IsPreconnected (U m))
    (hSmono : Monotone S) (hSopen : ∀ m, IsOpen (S m))
    (hmap : ∀ m, MapsTo ((quad c)^[n]) (S m) (U m))
    (hproper : ∀ m, IsProperMap (fun z : S m =>
      (⟨(quad c)^[n] z, hmap m z.property⟩ : U m)))
    (m : ℕ) (y : ℂ) (hy : y ∈ U 0) :
    ((⋃ j, S j) ∩ ((quad c)^[n] ⁻¹' U m) = S m) ↔
      localFiber c n (S m) y = localFiber c n (⋃ j, S j) y := by
  let f := (quad c)^[n]
  have hf : Continuous f := (quadratic_iterate_proper c n).continuous
  have hyU : y ∈ U m := hUmono (Nat.zero_le m) hy
  constructor
  · intro hs
    ext a
    constructor
    · intro ha
      obtain ⟨haS, hay⟩ := (mem_localFiber c n (S m) y a).mp ha
      exact (mem_localFiber c n (⋃ j, S j) y a).mpr
        ⟨mem_iUnion_of_mem m haS, hay⟩
    · intro ha
      obtain ⟨haS, hay⟩ := (mem_localFiber c n (⋃ j, S j) y a).mp ha
      have haU : (quad c)^[n] a ∈ U m := by
        rw [hay]
        exact hyU
      have haOld : a ∈ S m := hs ▸ (show a ∈ (⋃ j, S j) ∩
        ((quad c)^[n] ⁻¹' U m) from ⟨haS, haU⟩)
      exact (mem_localFiber c n (S m) y a).mpr ⟨haOld, hay⟩
  · intro hF
    apply Subset.antisymm
    · intro z hz
      obtain ⟨j, hzj⟩ := mem_iUnion.mp hz.1
      let r := max j m
      have hzr : z ∈ S r := hSmono (le_max_left j m) hzj
      let D := connectedComponentIn (f ⁻¹' U m) z
      have hDr : D ⊆ connectedComponentIn (f ⁻¹' U r) z :=
        connectedComponentIn_mono z (preimage_mono (hUmono (le_max_right j m)))
      have hGr : connectedComponentIn (S r) z =
          connectedComponentIn (f ⁻¹' U r) z :=
        proper_localization_component_global f (S r) (U r) hf
          (hSopen r) (hUopen r) (hmap r) (hproper r) z hzr
      have hDS : D ⊆ S r := by
        intro a ha
        exact connectedComponentIn_subset (S r) z (hGr.symm ▸ hDr ha)
      have honto : f '' D = U m :=
        quadratic_global_component_image c n (U m) (hUopen m) (hUconn m) z hz.2
      have hyD : y ∈ f '' D := honto.symm ▸ hyU
      obtain ⟨a, haD, hay⟩ := hyD
      have haUnion : a ∈ ⋃ j, S j := mem_iUnion_of_mem r (hDS haD)
      have haF : a ∈ localFiber c n (⋃ j, S j) y :=
        (mem_localFiber c n (⋃ j, S j) y a).mpr ⟨haUnion, hay⟩
      rw [← hF] at haF
      have haS : a ∈ S m := ((mem_localFiber c n (S m) y a).mp haF).1
      have hDa : D = connectedComponentIn (f ⁻¹' U m) a :=
        connectedComponentIn_eq haD
      have hzD : z ∈ D := mem_connectedComponentIn hz.2
      have hGm : connectedComponentIn (S m) a =
          connectedComponentIn (f ⁻¹' U m) a :=
        proper_localization_component_global f (S m) (U m) hf
          (hSopen m) (hUopen m) (hmap m) (hproper m) a haS
      exact connectedComponentIn_subset (S m) a (hGm.symm ▸ (hDa ▸ hzD))
    · intro z hz
      exact ⟨mem_iUnion_of_mem m hz, hmap m hz⟩

/-- Increasing proper open localizations eventually contain every
point of their entire future source union lying over the current
target. The localizations may be empty or disconnected and need
not contain every ambient inverse component. -/
theorem quadratic_proper_localizations_eventually_saturated
    (c : ℂ) (n : ℕ) (U S : ℕ → Set ℂ)
    (hUmono : Monotone U) (hUopen : ∀ m, IsOpen (U m))
    (hUconn : ∀ m, IsPreconnected (U m))
    (hSmono : Monotone S) (hSopen : ∀ m, IsOpen (S m))
    (hmap : ∀ m, MapsTo ((quad c)^[n]) (S m) (U m))
    (hproper : ∀ m, IsProperMap (fun z : S m =>
      (⟨(quad c)^[n] z, hmap m z.property⟩ : U m)))
    (y : ℂ) (hy : y ∈ U 0) :
    ∃ N : ℕ, ∀ m, N ≤ m →
      (⋃ j, S j) ∩ ((quad c)^[n] ⁻¹' U m) = S m := by
  obtain ⟨N, hN⟩ := quadratic_union_fiber_captured c n S hSmono y
  refine ⟨N, ?_⟩
  intro m hm
  exact (quadratic_proper_localization_union_iff_fiber c n U S
    hUmono hUopen hUconn hSmono hSopen hmap hproper m y hy).mpr (hN m hm)

/-- One stage simultaneously saturates the selected future source
unions at every depth in a fixed finite quadratic horizon. -/
theorem quadratic_finite_horizon_localizations_saturated
    (c : ℂ) (H : ℕ) (U : ℕ → Set ℂ) (S : ℕ → ℕ → Set ℂ)
    (hUmono : Monotone U) (hUopen : ∀ m, IsOpen (U m))
    (hUconn : ∀ m, IsPreconnected (U m))
    (hSmono : ∀ k ≤ H, Monotone (S k))
    (hSopen : ∀ k ≤ H, ∀ m, IsOpen (S k m))
    (hmap : ∀ k ≤ H, ∀ m, MapsTo ((quad c)^[k]) (S k m) (U m))
    (hproper : ∀ k (hk : k ≤ H) m, IsProperMap (fun z : S k m =>
      (⟨(quad c)^[k] z, hmap k hk m z.property⟩ : U m)))
    (y : ℂ) (hy : y ∈ U 0) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ k, k ≤ H →
      (⋃ j, S k j) ∩ ((quad c)^[k] ⁻¹' U m) = S k m := by
  classical
  have hex : ∀ k : Fin (H+1), ∃ N : ℕ, ∀ m, N ≤ m →
      (⋃ j, S k.val j) ∩ ((quad c)^[k.val] ⁻¹' U m) = S k.val m := by
    intro k
    have hk : k.val ≤ H := by omega
    exact quadratic_proper_localizations_eventually_saturated c k.val U (S k.val)
      hUmono hUopen hUconn (hSmono k.val hk) (hSopen k.val hk)
      (hmap k.val hk) (hproper k.val hk) y hy
  choose stage hstage using hex
  let N := Finset.univ.sup stage
  refine ⟨N, ?_⟩
  intro m hm k hk
  let d : Fin (H+1) := ⟨k, by omega⟩
  have hd : stage d ≤ N := Finset.le_sup (Finset.mem_univ d)
  exact hstage d m (hd.trans hm)

/-- Complete eventual source package: no future source points enter
over the current target, and no later source component merges old
components. The two conclusions use separate finite stabilizations;
source saturation alone is not asserted to prevent mergers. -/
theorem quadratic_finite_horizon_localizations_natural
    (c : ℂ) (H : ℕ) (U : ℕ → Set ℂ) (S : ℕ → ℕ → Set ℂ)
    (hUmono : Monotone U) (hUopen : ∀ m, IsOpen (U m))
    (hUconn : ∀ m, IsPreconnected (U m))
    (hSmono : ∀ k ≤ H, Monotone (S k))
    (hSopen : ∀ k ≤ H, ∀ m, IsOpen (S k m))
    (hmap : ∀ k ≤ H, ∀ m, MapsTo ((quad c)^[k]) (S k m) (U m))
    (hproper : ∀ k (hk : k ≤ H) m, IsProperMap (fun z : S k m =>
      (⟨(quad c)^[k] z, hmap k hk m z.property⟩ : U m)))
    (y : ℂ) (hy : y ∈ U 0) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ k, k ≤ H →
      ((⋃ j, S k j) ∩ ((quad c)^[k] ⁻¹' U m) = S k m) ∧
      ∀ r, m ≤ r → ∀ x ∈ S k m,
        connectedComponentIn (S k r) x ∩ ((quad c)^[k] ⁻¹' U m) =
          connectedComponentIn (S k m) x := by
  obtain ⟨Ns, hNs⟩ := quadratic_finite_horizon_localizations_saturated
    c H U S hUmono hUopen hUconn hSmono hSopen hmap hproper y hy
  obtain ⟨Nc, hNc⟩ := quadratic_finite_horizon_tail_naturality
    c H U hUmono hUopen hUconn y hy
  refine ⟨max Ns Nc, ?_⟩
  intro m hm k hk
  refine ⟨hNs m ((le_max_left Ns Nc).trans hm) k hk, ?_⟩
  intro r hmr x hx
  have hxr : x ∈ S k r := hSmono k hk hmr hx
  have hf := (quadratic_iterate_proper c k).continuous
  rw [proper_localization_component_global ((quad c)^[k]) (S k r) (U r)
    hf (hSopen k hk r) (hUopen r) (hmap k hk r) (hproper k hk r) x hxr,
    proper_localization_component_global ((quad c)^[k]) (S k m) (U m)
      hf (hSopen k hk m) (hUopen m) (hmap k hk m) (hproper k hk m) x hx]
  exact hNc m ((le_max_right Ns Nc).trans hm) r hmr k hk x (hmap k hk m hx)

end LoopsQuadraticLocalizationStabilization
