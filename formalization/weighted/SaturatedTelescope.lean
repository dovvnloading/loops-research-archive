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
    exact connectedComponentIn_subset (g ⁻¹' S) (f x) hz
  · let C := connectedComponentIn ((g ∘ f) ⁻¹' S) x
    have hxC : x ∈ C := mem_connectedComponentIn hx
    have hC : IsPreconnected C := isPreconnected_connectedComponentIn
    have hsub : f '' C ⊆ g ⁻¹' S := by
      rintro y ⟨z, hz, rfl⟩
      exact connectedComponentIn_subset ((g ∘ f) ⁻¹' S) x hz
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
    calc
      (routeMap F (s+1) n ∘ F s) '' H s = routeMap F (s+1) n '' (F s '' H s) := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨F s z, ⟨z, hz, rfl⟩, rfl⟩
        · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
          exact ⟨w, hw, rfl⟩
      _ = H (s+(n+1)) := by
        rw [honto s (by omega), show s+(n+1) = s+1+n by omega]
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
    change (QuadraticEscape.orbit c (m+n) z)^2+c =
      (QuadraticEscape.orbit c n (QuadraticEscape.orbit c m z))^2+c
    rw [ih]

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


/-- Actual quadratic collisions are precisely the two signs. -/
theorem quadratic_eq_iff (c z w : ℂ) :
    z^2+c = w^2+c ↔ z=w ∨ z = -w := by
  constructor
  · intro h
    have hz : (z-w)*(z+w) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with h₁ | h₂
    · exact Or.inl (sub_eq_zero.mp h₁)
    · right
      linear_combination h₂
  · rintro (rfl | h)
    · rfl
    · rw [h]
      ring

/-- A selected actual quadratic pullback component through the critical
point contains both signs of every one of its points. No local connectivity,
Jordan boundary, or fiber cardinality premise is needed. -/
theorem quadratic_critical_component_symmetric (c : ℂ) (D : Set ℂ) (hc : c ∈ D)
    (z : ℂ) (hz : z ∈ connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0) :
    -z ∈ connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0 := by
  let C := connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0
  have hzero : (0 : ℂ) ∈ C := mem_connectedComponentIn
    (show (0 : ℂ)^2+c ∈ D by simpa using hc)
  have hneg : Continuous (fun w : ℂ => -w) := continuous_id.neg
  have hsub : (fun w : ℂ => -w) '' C ⊆ (fun w : ℂ => w^2+c) ⁻¹' D := by
    rintro y ⟨w, hw, rfl⟩
    have h : w^2+c ∈ D :=
      connectedComponentIn_subset ((fun u : ℂ => u^2+c) ⁻¹' D) 0 hw
    change (-w)^2+c ∈ D
    rw [show (-w)^2+c = w^2+c by ring]
    exact h
  have h0 : (0 : ℂ) ∈ (fun w : ℂ => -w) '' C := ⟨0, hzero, neg_zero⟩
  have hpre : IsPreconnected C := isPreconnected_connectedComponentIn
  exact (hpre.image _ hneg.continuousOn).subset_connectedComponentIn h0 hsub ⟨z, hz, rfl⟩

/-- Exact return fibers across one actual critical step with injective
prefix and suffix. The second lift is constructed, not postulated.
It coincides with the first exactly at the critical point. -/
theorem quadratic_return_fiber_pair (c : ℂ) (p r : ℂ → ℂ) (A B D : Set ℂ)
    (hc : c ∈ D)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hponto : p '' A = B) (hpinj : InjOn p A) (hrinj : InjOn r D)
    (x : ℂ) (hx : x ∈ A) :
    ∃ y ∈ A, p y = -(p x) ∧ (y=x ↔ p x=0) ∧
      ∀ z ∈ A, r ((p z)^2+c) = r ((p x)^2+c) ↔ z=x ∨ z=y := by
  have hpx : p x ∈ B := by
    rw [← hponto]
    exact ⟨x, hx, rfl⟩
  have hneg : -(p x) ∈ B := by
    rw [hB] at hpx ⊢
    exact quadratic_critical_component_symmetric c D hc (p x) hpx
  have him : -(p x) ∈ p '' A := by rwa [hponto]
  obtain ⟨y, hy, hpy⟩ := him
  have hq (z : ℂ) (hz : z ∈ A) : (p z)^2+c ∈ D := by
    have hpz : p z ∈ B := by
      rw [← hponto]
      exact ⟨z, hz, rfl⟩
    rw [hB] at hpz
    exact connectedComponentIn_subset ((fun w : ℂ => w^2+c) ⁻¹' D) 0 hpz
  refine ⟨y, hy, hpy, ?_, ?_⟩
  · constructor
    · intro he
      subst y
      have hh : (2 : ℂ) * p x = 0 := by linear_combination hpy
      exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
    · intro he
      apply hpinj hy hx
      rw [hpy, he, neg_zero]
  · intro z hz
    constructor
    · intro he
      have h := hrinj (hq z hz) (hq x hx) he
      rcases (quadratic_eq_iff c (p z) (p x)).mp h with h₁ | h₂
      · exact Or.inl (hpinj hz hx h₁)
      · exact Or.inr (hpinj hz hy (h₂.trans hpy.symm))
    · intro h
      rcases h with h | h
      · subst z
        rfl
      · subst z
        exact congrArg r ((quadratic_eq_iff c (p y) (p x)).mpr (Or.inr hpy))

/-- The previous fiber construction for the archive's actual orbit,
with arbitrary physical durations before and after the critical step. -/
theorem quadratic_segment_fiber_pair (c : ℂ) (a b : ℕ) (A B D : Set ℂ)
    (hc : c ∈ D)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hponto : QuadraticEscape.orbit c a '' A = B)
    (hpinj : InjOn (QuadraticEscape.orbit c a) A)
    (hrinj : InjOn (QuadraticEscape.orbit c b) D)
    (x : ℂ) (hx : x ∈ A) :
    ∃ y ∈ A, QuadraticEscape.orbit c a y = -(QuadraticEscape.orbit c a x) ∧
      (y=x ↔ QuadraticEscape.orbit c a x=0) ∧
      ∀ z ∈ A, QuadraticEscape.orbit c (a+1+b) z =
        QuadraticEscape.orbit c (a+1+b) x ↔ z=x ∨ z=y := by
  obtain ⟨y, hy, hpy, he, hfiber⟩ := quadratic_return_fiber_pair c
    (QuadraticEscape.orbit c a) (QuadraticEscape.orbit c b) A B D
    hc hB hponto hpinj hrinj x hx
  refine ⟨y, hy, hpy, he, ?_⟩
  intro z hz
  rw [quadratic_orbit_add c (a+1) b z, quadratic_orbit_add c (a+1) b x]
  exact hfiber z hz

/-- The propagated critical value has exactly one preimage in the
selected physical return carrier. This does not assert analytic degree
or existence of the surrounding proper holomorphic domains. -/
theorem quadratic_return_critical_value (c : ℂ) (a b : ℕ) (A B D : Set ℂ)
    (hc : c ∈ D)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hponto : QuadraticEscape.orbit c a '' A = B)
    (hpinj : InjOn (QuadraticEscape.orbit c a) A)
    (hrinj : InjOn (QuadraticEscape.orbit c b) D) :
    ∃! x, x ∈ A ∧ QuadraticEscape.orbit c (a+1+b) x = QuadraticEscape.orbit c b c := by
  have hz : (0 : ℂ) ∈ B := by
    rw [hB]
    exact mem_connectedComponentIn (show (0 : ℂ)^2+c ∈ D by simpa using hc)
  rw [← hponto] at hz
  obtain ⟨x, hx, hpx⟩ := hz
  have hv : QuadraticEscape.orbit c (a+1+b) x = QuadraticEscape.orbit c b c := by
    rw [quadratic_orbit_add c (a+1) b x]
    change QuadraticEscape.orbit c b ((QuadraticEscape.orbit c a x)^2+c) = _
    rw [hpx]
    simp
  obtain ⟨y, hy, _, hye, hfiber⟩ := quadratic_segment_fiber_pair c a b A B D
    hc hB hponto hpinj hrinj x hx
  refine ⟨x, ⟨hx, hv⟩, ?_⟩
  intro z hz
  rcases (hfiber z hz.1).mp (hz.2.trans hv.symm) with h | h
  · exact h
  · exact h.trans (hye.mpr hpx)

/-- Every other attained return value has exactly two distinct preimages.
The theorem gives the complete fiber as a set of actual complex points. -/
theorem quadratic_return_noncritical_fiber (c : ℂ) (a b : ℕ) (A B D : Set ℂ)
    (hc : c ∈ D)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hponto : QuadraticEscape.orbit c a '' A = B)
    (hpinj : InjOn (QuadraticEscape.orbit c a) A)
    (hrinj : InjOn (QuadraticEscape.orbit c b) D)
    (v : ℂ) (hv : v ∈ QuadraticEscape.orbit c (a+1+b) '' A)
    (hn : v ≠ QuadraticEscape.orbit c b c) :
    ∃ x y : ℂ, x ≠ y ∧ {z | z ∈ A ∧ QuadraticEscape.orbit c (a+1+b) z = v} = {x,y} := by
  obtain ⟨x, hx, hval⟩ := hv
  obtain ⟨y, hy, _, he, hfiber⟩ := quadratic_segment_fiber_pair c a b A B D
    hc hB hponto hpinj hrinj x hx
  have hpx : QuadraticEscape.orbit c a x ≠ 0 := by
    intro h
    apply hn
    rw [← hval, quadratic_orbit_add c (a+1) b x]
    change QuadraticEscape.orbit c b ((QuadraticEscape.orbit c a x)^2+c) = _
    rw [h]
    simp
  have hxy : x ≠ y := fun h => hpx (he.mp h.symm)
  have hyval : QuadraticEscape.orbit c (a+1+b) y = v :=
    ((hfiber y hy).mpr (Or.inr rfl)).trans hval
  refine ⟨x, y, hxy, ?_⟩
  ext z
  simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro hz
    exact (hfiber z hz.1).mp (hz.2.trans hval.symm)
  · rintro (rfl | rfl)
    · exact ⟨hx, hval⟩
    · exact ⟨hy, hyval⟩

end LoopsSaturatedTelescope
