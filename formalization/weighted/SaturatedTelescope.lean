import Mathlib
import QuadraticEscape

/-!
# Exact connected-component recognition for finite saturated telescopes

The statement is topological: connected components are taken in the actual
ambient space, without local connectivity. The quadratic specialization uses
the existing physical orbit, not a finite component graph.
-/

namespace LoopsSaturatedTelescope

open Set

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A selected pullback component composes exactly, not merely by inclusion.
Only continuity of the first map is needed. -/
theorem component_pullback_comp (f : X → Y) (g : Y → Z) (S : Set Z)
    (x : X) (hf : Continuous f) (hx : g (f x) ∈ S) :
    connectedComponentIn (f ⁻¹' connectedComponentIn (g ⁻¹' S) (f x)) x =
      connectedComponentIn ((g ∘ f) ⁻¹' S) x := by
  apply Subset.antisymm
  · apply connectedComponentIn_mono
    intro z hz
    exact connectedComponentIn_subset _ _ hz
  · let C := connectedComponentIn ((g ∘ f) ⁻¹' S) x
    have hxC : x ∈ C := mem_connectedComponentIn hx
    have hC : IsPreconnected C := isPreconnected_connectedComponentIn
    have hsub : f '' C ⊆ g ⁻¹' S := by
      rintro y ⟨z, hz, rfl⟩
      exact connectedComponentIn_subset _ _ hz
    have hfx : f x ∈ f '' C := ⟨x, hxC, rfl⟩
    have himage : f '' C ⊆ connectedComponentIn (g ⁻¹' S) (f x) :=
      (hC.image _ hf.continuousOn).subset_connectedComponentIn hfx hsub
    exact hC.subset_connectedComponentIn hxC (fun z hz => himage ⟨z, hz, rfl⟩)

/-- Forward composition of a finite consecutive segment of stages. -/
def routeMap (F : ℕ → X → X) : ℕ → ℕ → X → X
  | _, 0 => id
  | s, n+1 => routeMap F (s+1) n ∘ F s

theorem routeMap_anchor (F : ℕ → X → X) (x : ℕ → X) (N : ℕ)
    (ha : ∀ i < N, F i (x i) = x (i+1))
    (s n : ℕ) (hbound : s+n ≤ N) :
    routeMap F s n (x s) = x (s+n) := by
  induction n generalizing s with
  | zero => simp [routeMap]
  | succ n ih =>
    change routeMap F (s+1) n (F s (x s)) = x (s+(n+1))
    rw [ha s (by omega), show s+(n+1) = s+1+n by omega]
    exact ih (s+1) (by omega)

/-- Every segment of a locally saturated chain is a globally selected
connected pullback component. The terminal set need not be locally connected. -/
theorem saturated_route_component (F : ℕ → X → X) (H : ℕ → Set X)
    (x : ℕ → X) (N : ℕ)
    (hF : ∀ i < N, Continuous (F i))
    (ha : ∀ i < N, F i (x i) = x (i+1))
    (hconn : ∀ i ≤ N, IsPreconnected (H i))
    (hm : ∀ i ≤ N, x i ∈ H i)
    (hsat : ∀ i < N, H i = connectedComponentIn (F i ⁻¹' H (i+1)) (x i))
    (s n : ℕ) (hbound : s+n ≤ N) :
    H s = connectedComponentIn (routeMap F s n ⁻¹' H (s+n)) (x s) := by
  induction n generalizing s with
  | zero =>
    change H s = connectedComponentIn (H (s+0)) (x s)
    simp only [Nat.add_zero]
    exact Subset.antisymm
      ((hconn s (by omega)).subset_connectedComponentIn (hm s (by omega)) (fun _ h => h))
      (connectedComponentIn_subset _ _)
  | succ n ih =>
    have he : s+1+n = s+(n+1) := by omega
    have htail := ih (s+1) (by omega)
    rw [he] at htail
    have hx : F s (x s) = x (s+1) := ha s (by omega)
    have hroute : routeMap F (s+1) n (F s (x s)) = x (s+(n+1)) := by
      rw [hx, ← he]
      exact routeMap_anchor F x N ha (s+1) n (by omega)
    change H s =
      connectedComponentIn ((routeMap F (s+1) n ∘ F s) ⁻¹' H (s+(n+1))) (x s)
    calc
      H s = connectedComponentIn (F s ⁻¹' H (s+1)) (x s) := hsat s (by omega)
      _ = connectedComponentIn
          (F s ⁻¹' connectedComponentIn (routeMap F (s+1) n ⁻¹' H (s+(n+1)))
            (F s (x s))) (x s) := by rw [htail, hx]
      _ = _ := component_pullback_comp (F s) (routeMap F (s+1) n)
        (H (s+(n+1))) (x s) (hF s (by omega)) (by rw [hroute]; exact hm _ hbound)

/-- Surjectivity on each chosen carrier gives exact image equality on
every segment, independently of the component-recognition hypotheses. -/
theorem routeMap_image (F : ℕ → X → X) (H : ℕ → Set X) (N : ℕ)
    (honto : ∀ i < N, F i '' H i = H (i+1))
    (s n : ℕ) (hbound : s+n ≤ N) :
    routeMap F s n '' H s = H (s+n) := by
  induction n generalizing s with
  | zero => simp [routeMap]
  | succ n ih =>
    change (routeMap F (s+1) n ∘ F s) '' H s = H (s+(n+1))
    rw [← Set.image_image, honto s (by omega), show s+(n+1) = s+1+n by omega]
    exact ih (s+1) (by omega)

theorem quadratic_orbit_continuous (c : ℂ) (n : ℕ) :
    Continuous (QuadraticEscape.orbit c n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
    change Continuous (fun z => (QuadraticEscape.orbit c n z)^2+c)
    exact (ih.pow 2).add continuous_const

theorem quadratic_orbit_add (c : ℂ) (m n : ℕ) (z : ℂ) :
    QuadraticEscape.orbit c (m+n) z =
      QuadraticEscape.orbit c n (QuadraticEscape.orbit c m z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.add_succ, QuadraticEscape.orbit, ih]

/-- Actual time of a consecutive segment, not its number of stages. -/
def routeTime (d : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | s, n+1 => d s + routeTime d (s+1) n

theorem routeMap_quadratic (c : ℂ) (d : ℕ → ℕ) (s n : ℕ) :
    routeMap (fun i => QuadraticEscape.orbit c (d i)) s n =
      QuadraticEscape.orbit c (routeTime d s n) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    funext z
    change routeMap (fun i => QuadraticEscape.orbit c (d i)) (s+1) n
      (QuadraticEscape.orbit c (d s) z) =
        QuadraticEscape.orbit c (d s + routeTime d (s+1) n) z
    rw [ih, quadratic_orbit_add]

/-- Exact global component and image recognition at every subsegment of
an actual complex quadratic orbit, allowing arbitrary stage durations. -/
theorem quadratic_segment_saturation (c : ℂ) (d : ℕ → ℕ) (H : ℕ → Set ℂ)
    (x : ℕ → ℂ) (N : ℕ)
    (ha : ∀ i < N, QuadraticEscape.orbit c (d i) (x i) = x (i+1))
    (hconn : ∀ i ≤ N, IsPreconnected (H i))
    (hm : ∀ i ≤ N, x i ∈ H i)
    (hsat : ∀ i < N, H i =
      connectedComponentIn (QuadraticEscape.orbit c (d i) ⁻¹' H (i+1)) (x i))
    (honto : ∀ i < N, QuadraticEscape.orbit c (d i) '' H i = H (i+1))
    (s n : ℕ) (hbound : s+n ≤ N) :
    H s = connectedComponentIn (QuadraticEscape.orbit c (routeTime d s n) ⁻¹'
      H (s+n)) (x s) ∧
    QuadraticEscape.orbit c (routeTime d s n) '' H s = H (s+n) := by
  have hc := saturated_route_component (fun i => QuadraticEscape.orbit c (d i))
    H x N (fun i _ => quadratic_orbit_continuous c (d i)) ha hconn hm hsat s n hbound
  have hi := routeMap_image (fun i => QuadraticEscape.orbit c (d i)) H N honto s n hbound
  rw [routeMap_quadratic] at hc hi
  exact ⟨hc, hi⟩

end LoopsSaturatedTelescope
