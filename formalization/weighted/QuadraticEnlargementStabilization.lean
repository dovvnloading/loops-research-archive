import IncreasingComponentStabilization
import QuadraticEnlargementDegree
import QuadraticStableReflection

/-!
# Eventual component naturality for actual quadratic enlargements

For a fixed finite iterate horizon, an increasing sequence of connected
open targets eventually has exactly the component partition of its union.
The stage is uniform across all actual components and all prefix depths.
It is obtained from the finite actual inverse fibers, not from a declared
symbolic cylinder list or an assumed stopping certificate.
-/

namespace LoopsQuadraticEnlargementStabilization

open Set Function Classical
open LoopsIncreasingComponentStabilization
open LoopsQuadraticCylinderCensus LoopsQuadraticCriticalFiberCensus
open LoopsQuadraticCylinderRamification LoopsQuadraticComponentFiberDegree
open LoopsQuadraticStableReflection

/-- A common stage captures every final connection in the actual
inverse fibers at all depths through the supplied finite horizon.
The anchor may be postcritical. No regular-value choice is required. -/
theorem quadratic_finite_horizon_anchor_stabilization
    (c : ℂ) (H : ℕ) (U : ℕ → Set ℂ)
    (hmono : Monotone U) (hopen : ∀ m, IsOpen (U m))
    (y : ℂ) (hy : y ∈ U 0) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ k, k ≤ H → ∀ a b : ℂ,
      (quad c)^[k] a = y → (quad c)^[k] b = y →
      (b ∈ connectedComponentIn ((quad c)^[k] ⁻¹' U m) a ↔
        b ∈ connectedComponentIn ((quad c)^[k] ⁻¹' (⋃ j, U j)) a) := by
  classical
  let S : ℕ → ℕ → Set ℂ := fun k m => (quad c)^[k] ⁻¹' U m
  let A : ℕ → Finset ℂ := fun k => globalFiber c k y
  have hSm (k : ℕ) : Monotone (S k) := by
    intro i j hij z hz
    exact hmono hij hz
  have hSo (k m : ℕ) : IsOpen (S k m) :=
    (hopen m).preimage (quadratic_iterate_proper c k).continuous
  have hA (k : ℕ) : ∀ a ∈ A k, a ∈ S k 0 := by
    intro a ha
    have he : (quad c)^[k] a = y := (mem_globalFiber c k y a).mp ha
    change (quad c)^[k] a ∈ U 0
    rw [he]
    exact hy
  obtain ⟨N, hN⟩ := finite_family_anchor_relations_stabilize
    (Finset.range (H+1)) S (fun k _ => hSm k) (fun k _ => hSo k)
    A A (fun k _ => hA k)
  refine ⟨N, ?_⟩
  intro m hm k hk a b ha hb
  have he := hN m hm k (Finset.mem_range.mpr (by omega))
    a ((mem_globalFiber c k y a).mpr ha)
    b ((mem_globalFiber c k y b).mpr hb)
  have hUnion : (⋃ j, S k j) = (quad c)^[k] ⁻¹' (⋃ j, U j) := by
    ext z
    simp [S]
  rw [hUnion] at he
  exact he

/-- Every actual pullback component is eventually the restriction of
its final union component, simultaneously at all depths through H.
This quantifies over every point of every stage, not only the finite
anchor fiber used in the proof. The targets may have holes. -/
theorem quadratic_finite_horizon_component_stabilization
    (c : ℂ) (H : ℕ) (U : ℕ → Set ℂ)
    (hmono : Monotone U) (hopen : ∀ m, IsOpen (U m))
    (hconn : ∀ m, IsPreconnected (U m)) (y : ℂ) (hy : y ∈ U 0) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ k, k ≤ H → ∀ x : ℂ,
      (quad c)^[k] x ∈ U m →
      connectedComponentIn ((quad c)^[k] ⁻¹' (⋃ j, U j)) x ∩
          ((quad c)^[k] ⁻¹' U m) =
        connectedComponentIn ((quad c)^[k] ⁻¹' U m) x := by
  obtain ⟨N, hN⟩ := quadratic_finite_horizon_anchor_stabilization
    c H U hmono hopen y hy
  refine ⟨N, ?_⟩
  intro m hm k hk x hx
  let f := (quad c)^[k]
  let V : Set ℂ := ⋃ j, U j
  let C := connectedComponentIn (f ⁻¹' U m) x
  let D := connectedComponentIn (f ⁻¹' V) x
  have hUV : U m ⊆ V := fun _ hz => mem_iUnion_of_mem m hz
  have hyU : y ∈ U m := hmono (Nat.zero_le m) hy
  have hCD : C ⊆ D := connectedComponentIn_mono x (preimage_mono hUV)
  have honto : f '' C = U m :=
    quadratic_global_component_image c k (U m) (hopen m) (hconn m) x hx
  have hyC : y ∈ f '' C := honto.symm ▸ hyU
  obtain ⟨a, haC, hay⟩ := hyC
  have haD : a ∈ D := hCD haC
  have hCa : C = connectedComponentIn (f ⁻¹' U m) a :=
    connectedComponentIn_eq haC
  have hDa : D = connectedComponentIn (f ⁻¹' V) a :=
    connectedComponentIn_eq haD
  have hFiber : localFiber c k C y = localFiber c k D y := by
    ext b
    simp only [mem_localFiber]
    constructor
    · rintro ⟨hb, hby⟩
      exact ⟨hCD hb, hby⟩
    · rintro ⟨hb, hby⟩
      have hbDa : b ∈ connectedComponentIn (f ⁻¹' V) a := hDa ▸ hb
      have hbCa : b ∈ connectedComponentIn (f ⁻¹' U m) a :=
        (hN m hm k hk a b hay hby).mpr hbDa
      exact ⟨hCa.symm ▸ hbCa, hby⟩
  exact (quadratic_enlargement_no_merger_iff_fiber_eq c k (U m) V
    hUV (hopen m) (hconn m) x hx y hyU).mp hFiber

/-- After the common stage, any two later stages have the exact
restriction identity. In particular a component cannot merge later
while the anchor census appears unchanged at the union. -/
theorem quadratic_finite_horizon_tail_naturality
    (c : ℂ) (H : ℕ) (U : ℕ → Set ℂ)
    (hmono : Monotone U) (hopen : ∀ m, IsOpen (U m))
    (hconn : ∀ m, IsPreconnected (U m)) (y : ℂ) (hy : y ∈ U 0) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ r, m ≤ r → ∀ k, k ≤ H →
      ∀ x : ℂ, (quad c)^[k] x ∈ U m →
      connectedComponentIn ((quad c)^[k] ⁻¹' U r) x ∩
          ((quad c)^[k] ⁻¹' U m) =
        connectedComponentIn ((quad c)^[k] ⁻¹' U m) x := by
  obtain ⟨N, hN⟩ := quadratic_finite_horizon_component_stabilization
    c H U hmono hopen hconn y hy
  refine ⟨N, ?_⟩
  intro m hm r hmr k hk x hx
  have hstable := hN m hm k hk x hx
  apply Subset.antisymm
  · intro z hz
    rw [← hstable]
    exact ⟨connectedComponentIn_mono x
      (preimage_mono (show U r ⊆ ⋃ j, U j from
        fun _ hw => mem_iUnion_of_mem r hw)) hz.1, hz.2⟩
  · intro z hz
    exact ⟨connectedComponentIn_mono x (preimage_mono (hmono hmr)) hz,
      connectedComponentIn_subset _ _ hz⟩

/-- The same eventual stage works for every actual prefix image.
Forward image followed by restriction to the old target is exactly
the forward image of the old component, for every split k+j≤H. -/
theorem quadratic_finite_horizon_prefix_naturality
    (c : ℂ) (H : ℕ) (U : ℕ → Set ℂ)
    (hmono : Monotone U) (hopen : ∀ m, IsOpen (U m))
    (hconn : ∀ m, IsPreconnected (U m)) (y : ℂ) (hy : y ∈ U 0) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ k j, k+j ≤ H → ∀ x : ℂ,
      (quad c)^[k+j] x ∈ U m →
      ((quad c)^[j] ''
        connectedComponentIn ((quad c)^[k+j] ⁻¹' (⋃ r, U r)) x) ∩
          ((quad c)^[k] ⁻¹' U m) =
      (quad c)^[j] '' connectedComponentIn ((quad c)^[k+j] ⁻¹' U m) x := by
  obtain ⟨N, hN⟩ := quadratic_finite_horizon_component_stabilization
    c H U hmono hopen hconn y hy
  refine ⟨N, ?_⟩
  intro m hm k j hkj x hx
  have hxV : (quad c)^[k+j] x ∈ ⋃ r, U r := mem_iUnion_of_mem m hx
  rw [quadratic_prefix_component_image c k j (⋃ r, U r)
    (isOpen_iUnion hopen) x hxV,
    quadratic_prefix_component_image c k j (U m) (hopen m) x hx]
  apply hN m hm k (by omega) ((quad c)^[j] x)
  rw [← Function.iterate_add_apply]
  exact hx

/-- Stabilization preserves the intrinsic degree rank and every
distinct-point fiber over the old target, including critical values.
The conclusion is uniform in all old components, depths and target
values; the proof does not discard repeated critical orbit values. -/
theorem quadratic_finite_horizon_fiber_and_rank_stabilization
    (c : ℂ) (H : ℕ) (U : ℕ → Set ℂ)
    (hmono : Monotone U) (hopen : ∀ m, IsOpen (U m))
    (hconn : ∀ m, IsPreconnected (U m)) (y : ℂ) (hy : y ∈ U 0) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ k, k ≤ H → ∀ x : ℂ,
      (quad c)^[k] x ∈ U m →
      componentReflectionRank c (U m) k x =
          componentReflectionRank c (⋃ j, U j) k x ∧
      ∀ z ∈ U m,
        localFiber c k (connectedComponentIn ((quad c)^[k] ⁻¹' U m) x) z =
          localFiber c k
            (connectedComponentIn ((quad c)^[k] ⁻¹' (⋃ j, U j)) x) z := by
  obtain ⟨N, hN⟩ := quadratic_finite_horizon_component_stabilization
    c H U hmono hopen hconn y hy
  refine ⟨N, ?_⟩
  intro m hm k hk x hx
  have hUV : U m ⊆ ⋃ j, U j := fun _ hz => mem_iUnion_of_mem m hz
  refine ⟨quadratic_stable_reflection_rank c (U m) (⋃ j, U j) hUV H
    (hN m hm) k hk x hx, ?_⟩
  intro z hz
  exact (quadratic_enlargement_no_merger_iff_fiber_eq c k
    (U m) (⋃ j, U j) hUV (hopen m) (hconn m) x hx z hz).mpr
      (hN m hm k hk x hx)

end LoopsQuadraticEnlargementStabilization
