import Mathlib
import StationarySeparatorTransport

/-!
# A single-fiber exhaustion criterion for actual pullback cylinders

The localized domain is an actual open subset of the complex plane.
The relative closure condition is proved for proper restrictions, not
inferred from word labels. Component exhaustion is reduced to a census
of one target fiber. A separate global bound uses the actual iterate
polynomial and applies at every parameter and depth.
-/

namespace LoopsQuadraticCylinderCensus

open Set Function Polynomial

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A component of an open set is relatively closed, expressed using
ambient closure so that it can be used with an ambient closed map. -/
theorem open_component_relative_closed [LocallyConnectedSpace X]
    (S : Set X) (hS : IsOpen S) (x : X) :
    closure (connectedComponentIn S x) ∩ S ⊆ connectedComponentIn S x := by
  intro z hz
  have hopen : IsOpen (connectedComponentIn S z) := hS.connectedComponentIn
  obtain ⟨w, hwz, hwx⟩ := mem_closure_iff.mp hz.1 _
    hopen (mem_connectedComponentIn hz.2)
  rw [connectedComponentIn_eq hwx, ← connectedComponentIn_eq hwz]
  exact mem_connectedComponentIn hz.2

/-- Each component of a relatively closed open localization of a
continuous open closed map surjects onto the connected target.
Neither injectivity nor the number of sheets is assumed. -/
theorem localized_component_image [LocallyConnectedSpace X]
    (f : X → Y) (S : Set X) (V : Set Y)
    (hopen : IsOpenMap f) (hclosed : IsClosedMap f)
    (hS : IsOpen S) (hV : IsPreconnected V)
    (hmap : MapsTo f S V)
    (hrel : closure S ∩ f ⁻¹' V ⊆ S)
    (x : X) (hx : x ∈ S) :
    f '' connectedComponentIn S x = V := by
  let C := connectedComponentIn S x
  have hC : C ⊆ S := connectedComponentIn_subset S x
  have hCo : IsOpen C := hS.connectedComponentIn
  have hCr : closure C ∩ f ⁻¹' V ⊆ C := by
    intro z hz
    exact open_component_relative_closed S hS x
      ⟨hz.1, hrel ⟨closure_mono hC hz.1, hz.2⟩⟩
  have hi : closure (f '' C) ∩ V ⊆ f '' C := by
    intro y hy
    have hsub : closure (f '' C) ⊆ f '' closure C :=
      (hclosed _ isClosed_closure).closure_subset (image_mono subset_closure)
    obtain ⟨z, hz, rfl⟩ := hsub hy.1
    exact ⟨z, hCr ⟨hz, hy.2⟩, rfl⟩
  have hhit : (V ∩ f '' C).Nonempty :=
    ⟨f x, hmap hx, ⟨x, mem_connectedComponentIn hx, rfl⟩⟩
  change f '' C = V
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hmap (hC hz)
  · exact hV.subset_of_closure_inter_subset (hopen _ hCo) hhit hi

/-- A proper restriction is relatively closed inside the full open
pullback, even when the restriction itself is disconnected. -/
theorem proper_localization_relative_closed (f : ℂ → ℂ) (S V : Set ℂ)
    (hf : Continuous f) (hV : IsOpen V) (hm : MapsTo f S V)
    (hp : IsProperMap (fun z : S => (⟨f z, hm z.property⟩ : V))) :
    closure S ∩ f ⁻¹' V ⊆ S := by
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV (f x) hx.2
  let B := Metric.closedBall (f x) (ε/2)
  have hBV : B ⊆ V :=
    (Metric.closedBall_subset_ball (by linarith : ε/2 < ε)).trans hball
  have hclosed : IsClosed (S ∩ f ⁻¹' B) :=
    (LoopsStationarySeparatorTransport.proper_restriction_compact_preimage
      f S V hm hp B (isCompact_closedBall _ _) hBV).isClosed
  have hxb : x ∈ closure (S ∩ f ⁻¹' B) := by
    apply mem_closure_iff.mpr
    intro W hW hxW
    let N := W ∩ f ⁻¹' Metric.ball (f x) (ε/2)
    have hN : IsOpen N := hW.inter (Metric.isOpen_ball.preimage hf)
    have hxN : x ∈ N := ⟨hxW, by simpa using (half_pos hε)⟩
    obtain ⟨z, hzN, hzS⟩ := mem_closure_iff.mp hx.1 N hN hxN
    exact ⟨z, hzN.1, hzS, Metric.ball_subset_closedBall hzN.2⟩
  rw [hclosed.closure_eq] at hxb
  exact hxb.1

/-- The actual complex quadratic is an open map, including at its
critical point. -/
theorem quadratic_open (c : ℂ) : IsOpenMap (fun z : ℂ => z^2+c) := by
  exact (isOpenMap_add_right c).comp (Complex.isOpenQuotientMap_pow 2).isOpenMap

/-- The actual complex quadratic is proper. The proof is the explicit
norm bound on the inverse image of a compact set. -/
theorem quadratic_proper (c : ℂ) : IsProperMap (fun z : ℂ => z^2+c) := by
  have hf : Continuous (fun z : ℂ => z^2+c) :=
    (continuous_id.pow 2).add continuous_const
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hf, ?_⟩
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  apply (isCompact_closedBall (0 : ℂ) (max 1 (R+‖c‖))).of_isClosed_subset
    (hK.isClosed.preimage hf)
  intro z hz
  have hzR : ‖z^2+c‖ ≤ R := hR _ hz
  have ht := norm_sub_le (z^2+c) c
  have he : (z^2+c)-c = z^2 := by ring
  rw [he, norm_pow] at ht
  have hn : ‖z‖^2 ≤ R+‖c‖ := by linarith
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases hz1 : ‖z‖ ≤ 1
  · exact hz1.trans (le_max_left _ _)
  · have hh : ‖z‖ ≤ ‖z‖^2 := by
      nlinarith [mul_nonneg (norm_nonneg z) (show 0 ≤ ‖z‖-1 by linarith)]
    exact (hh.trans hn).trans (le_max_right _ _)

/-- Every actual finite iterate is an open map. -/
theorem quadratic_iterate_open (c : ℂ) (n : ℕ) :
    IsOpenMap ((fun z : ℂ => z^2+c)^[n]) := by
  induction n with
  | zero => exact IsOpenMap.id
  | succ n ih =>
    rw [Function.iterate_succ]
    exact ih.comp (quadratic_open c)

/-- Every actual finite iterate is proper. -/
theorem quadratic_iterate_proper (c : ℂ) (n : ℕ) :
    IsProperMap ((fun z : ℂ => z^2+c)^[n]) := by
  induction n with
  | zero => exact isProperMap_id
  | succ n ih =>
    rw [Function.iterate_succ]
    exact ih.comp (quadratic_proper c)

/-- A census of one fiber exhausts all localized components, provided
the declared pieces are actual components and each component reaches
that target. This does not assume a census of the whole domain. -/
theorem one_fiber_component_exhaustion {ι : Type*} (f : X → Y)
    (S : Set X) (y : Y) (a : ι → X)
    (ha : ∀ i, a i ∈ S)
    (hhit : ∀ x ∈ S, ∃ z ∈ connectedComponentIn S x, f z = y)
    (hcensus : ∀ z ∈ S, f z = y → ∃ i, z ∈ connectedComponentIn S (a i))
    (x : X) (hx : x ∈ S) :
    ∃ i, connectedComponentIn S x = connectedComponentIn S (a i) := by
  obtain ⟨z, hzx, hz⟩ := hhit x hx
  obtain ⟨i, hzi⟩ := hcensus z (connectedComponentIn_subset S x hzx) hz
  exact ⟨i, (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzi).symm⟩

/-- Localized exhaustion and unique ownership for the actual quadratic
iterate. Properness of the localization and a single-fiber census are
enough; a whole-domain covering assumption is unnecessary. -/
theorem quadratic_localized_census {ι : Type*} (c : ℂ) (n : ℕ)
    (S V : Set ℂ) (hS : IsOpen S) (hVo : IsOpen V) (hVc : IsPreconnected V)
    (hm : MapsTo ((fun z : ℂ => z^2+c)^[n]) S V)
    (hp : IsProperMap (fun z : S =>
      (⟨((fun w : ℂ => w^2+c)^[n]) z, hm z.property⟩ : V)))
    (y : ℂ) (hy : y ∈ V) (a : ι → ℂ) (ha : ∀ i, a i ∈ S)
    (hdist : Injective (fun i => connectedComponentIn S (a i)))
    (hcensus : ∀ z ∈ S, ((fun w : ℂ => w^2+c)^[n]) z = y →
      ∃ i, z ∈ connectedComponentIn S (a i))
    (x : ℂ) (hx : x ∈ S) :
    ∃! i, connectedComponentIn S x = connectedComponentIn S (a i) := by
  let f := (fun z : ℂ => z^2+c)^[n]
  have hf := quadratic_iterate_proper c n
  have hr := proper_localization_relative_closed f S V hf.continuous hVo hm hp
  have hhit (w : ℂ) (hw : w ∈ S) :
      ∃ z ∈ connectedComponentIn S w, f z = y := by
    have he := localized_component_image f S V (quadratic_iterate_open c n)
      hf.isClosedMap hS hVc hm hr w hw
    have h : y ∈ f '' connectedComponentIn S w := he.symm ▸ hy
    exact h
  obtain ⟨i, hi⟩ := one_fiber_component_exhaustion f S y a ha hhit hcensus x hx
  exact ⟨i, hi, fun j hj => hdist (hj.symm.trans hi)⟩

/-- Polynomial representing the actual spatial iterate. -/
noncomputable def iteratePolynomial (c : ℂ) : ℕ → Polynomial ℂ
  | 0 => X
  | n+1 => (iteratePolynomial c n)^2 + C c

theorem iteratePolynomial_eval (c z : ℂ) (n : ℕ) :
    (iteratePolynomial c n).eval z = ((fun w : ℂ => w^2+c)^[n]) z := by
  induction n with
  | zero => simp [iteratePolynomial]
  | succ n ih => simp [iteratePolynomial, Function.iterate_succ_apply', ih]

theorem iteratePolynomial_degree (c : ℂ) (n : ℕ) :
    (iteratePolynomial c n).natDegree = 2^n := by
  induction n with
  | zero => simp [iteratePolynomial]
  | succ n ih =>
    simp [iteratePolynomial, Polynomial.natDegree_pow, ih, pow_succ, Nat.mul_comm]

/-- A finite census of distinct points in one actual iterate fiber
never exceeds the degree. Critical values are allowed. -/
theorem quadratic_fiber_card_bound (c y : ℂ) (n : ℕ) (A : Finset ℂ)
    (hA : ∀ z ∈ A, ((fun w : ℂ => w^2+c)^[n]) z = y) :
    A.card ≤ 2^n := by
  classical
  let p := iteratePolynomial c n - C y
  have hd : p.natDegree = 2^n := by
    simp [p, Polynomial.natDegree_sub_C, iteratePolynomial_degree]
  have hp : p ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (by rw [hd]; positivity)
  have hsub : A.val ⊆ p.roots := by
    intro z hz
    apply (Polynomial.mem_roots hp).2
    change p.eval z = 0
    have hz' : z ∈ A := by simpa using hz
    simp [p, iteratePolynomial_eval, hA z hz']
  exact (Polynomial.card_le_degree_of_subset_roots hsub).trans hd.le

/-- Attaining the global degree at a single target fiber certifies
exhaustion of that fiber, with no assumed genericity of the target. -/
theorem quadratic_full_degree_census (c y : ℂ) (n : ℕ) (A : Finset ℂ)
    (hA : ∀ z ∈ A, ((fun w : ℂ => w^2+c)^[n]) z = y)
    (hcard : 2^n ≤ A.card) (z : ℂ) :
    ((fun w : ℂ => w^2+c)^[n]) z = y ↔ z ∈ A := by
  classical
  let p := iteratePolynomial c n - C y
  have hd : p.natDegree = 2^n := by
    simp [p, Polynomial.natDegree_sub_C, iteratePolynomial_degree]
  have hp : p ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (by rw [hd]; positivity)
  have hroot : p.roots = A.val :=
    Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
      (fun w hw => by simp [p, iteratePolynomial_eval, hA w hw])
      (hd.symm ▸ hcard) hp
  constructor
  · intro hz
    have h : z ∈ p.roots := (Polynomial.mem_roots hp).2 (by
      change p.eval z = 0
      simp [p, iteratePolynomial_eval, hz])
    rw [hroot] at h
    simpa using h
  · exact hA z

end LoopsQuadraticCylinderCensus
