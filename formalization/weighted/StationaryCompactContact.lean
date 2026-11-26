import StationarySeparatorTransport
import StationaryMultiInterface

/-!
# Quadratic compact bypass exclusion from exterior closure contact

The exterior need not be closed, and no accessible ray is assumed.
Compact retained test sets permit the existing logarithm construction
to work with a connected, unbounded, possibly nonclosed cut.
-/

namespace LoopsStationaryCompactContact

open Set LoopsStationarySeparatorTransport

/-- Closure contact suffices for preconnectedness of the union, without
requiring any point of the second set to lie in the first. -/
theorem preconnected_union_of_closure_contact
    {X : Type*} [TopologicalSpace X] (A B : Set X)
    (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hcontact : (A ∩ closure B).Nonempty) :
    IsPreconnected (A ∪ B) := by
  apply isPreconnected_closed_iff.mpr
  intro U V hU hV hcov hleft hright
  by_contra hnone
  have hno (z : X) (hz : z ∈ A ∪ B) (hu : z ∈ U) (hv : z ∈ V) : False :=
    hnone ⟨z, hz, hu, hv⟩
  have hsplit (T : Set X) (hT : IsPreconnected T) (hsub : T ⊆ A ∪ B) :
      T ⊆ U ∨ T ⊆ V := by
    by_cases hh : (T ∩ U).Nonempty
    · left
      intro z hz
      by_contra hn
      have hzV := (hcov (hsub hz)).resolve_left hn
      obtain ⟨w, hw, hwU, hwV⟩ := (isPreconnected_closed_iff.mp hT)
        U V hU hV (hsub.trans hcov) hh ⟨z, hz, hzV⟩
      exact hno w (hsub hw) hwU hwV
    · right
      intro z hz
      rcases hcov (hsub hz) with hzU | hzV
      · exact (hh ⟨z, hz, hzU⟩).elim
      · exact hzV
  obtain ⟨a, haA, haB⟩ := hcontact
  rcases hsplit A hA (fun _ hz => Or.inl hz) with haU | haV <;>
    rcases hsplit B hB (fun _ hz => Or.inr hz) with hbU | hbV
  · obtain ⟨z, hz, hzV⟩ := hright
    exact hno z hz (union_subset haU hbU hz) hzV
  · exact hno a (Or.inl haA) (haU haA) (closure_minimal hbV hV haB)
  · exact hno a (Or.inl haA) (closure_minimal hbU hU haB) (haV haA)
  · obtain ⟨z, hz, hzU⟩ := hleft
    exact hno z hz hzU (union_subset haV hbV hz)

/-- The image of any unbounded set under the actual quadratic map
is unbounded. No connectedness or invariance assumption is needed. -/
theorem quadratic_image_unbounded (c : ℂ) (R : Set ℂ)
    (hunb : ∀ B : ℝ, ∃ z ∈ R, B < ‖z‖) :
    ∀ B : ℝ, ∃ w ∈ (fun z : ℂ => z^2+c) '' R, B < ‖w‖ := by
  intro B
  obtain ⟨z, hz, hbig⟩ := hunb (max 1 (B + ‖c‖ + 1))
  have hz1 : 1 < ‖z‖ := (le_max_left _ _).trans_lt hbig
  have hb : B + ‖c‖ + 1 < ‖z‖ := (le_max_right _ _).trans_lt hbig
  have hsq : ‖z‖ ≤ ‖z‖^2 := by
    simpa [pow_two] using
      (mul_le_mul_of_nonneg_left (le_of_lt hz1) (norm_nonneg z))
  have htri : ‖z‖^2 ≤ ‖z^2+c‖ + ‖c‖ := by
    rw [← norm_pow]
    calc
      ‖z^2‖ = ‖(z^2+c)-c‖ := by rw [add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  exact ⟨z^2+c, ⟨z, hz, rfl⟩, by linarith⟩

/-- A closure contact between the critical continuum and an unbounded
connected exterior is enough for a logarithm on every compact retained
image test set. Reflection saturation is used on the actual sets,
not on an abstract deck model. -/
theorem quadratic_compact_contact_log (c : ℂ) (K Q R T : Set ℂ)
    (hKsym : ∀ z ∈ K, -z ∈ K)
    (hQsym : ∀ z ∈ Q, -z ∈ Q) (hzero : 0 ∈ Q)
    (hQ : IsPreconnected Q) (hR : IsPreconnected R)
    (hcontact : (Q ∩ closure R).Nonempty)
    (hdis : Disjoint R K) (hunb : ∀ B : ℝ, ∃ z ∈ R, B < ‖z‖)
    (hT : IsCompact T) (hTsub : T ⊆ (fun z : ℂ => z^2+c) '' (K \ Q)) :
    ∃ g : C(T, ℂ), ∀ w : T, Complex.exp (g w) = (w : ℂ)-c := by
  let f : ℂ → ℂ := fun z => z^2+c
  let D := f '' (Q ∪ R)
  have hf : Continuous f := (continuous_id.pow 2).add continuous_const
  have hD : IsPreconnected D :=
    (preconnected_union_of_closure_contact Q R hQ hR hcontact).image f hf.continuousOn
  have hc : c ∈ D := ⟨0, Or.inl hzero, by simp [f]⟩
  have hDu : ∀ B : ℝ, ∃ w ∈ D, B < ‖w‖ := by
    intro B
    obtain ⟨w, hw, hb⟩ := quadratic_image_unbounded c R hunb B
    obtain ⟨z, hz, he⟩ := hw
    exact ⟨w, ⟨z, Or.inr hz, he⟩, hb⟩
  have hDd : Disjoint D T := by
    rw [Set.disjoint_left]
    rintro w ⟨z, hz, rfl⟩ hw
    have hmem : f z ∈ f '' (K \ Q) := hTsub hw
    obtain ⟨y, hy, he⟩ := hmem
    rcases hz with hzQ | hzR
    · have hyQ : y ∈ f ⁻¹' (f '' Q) := ⟨z, hzQ, he.symm⟩
      rw [show f ⁻¹' (f '' Q) = Q from
        quadratic_image_preimage_symmetric c Q hQsym] at hyQ
      exact hy.2 hyQ
    · have hzK : z ∈ f ⁻¹' (f '' K) := ⟨y, hy.1, he⟩
      rw [show f ⁻¹' (f '' K) = K from
        quadratic_image_preimage_symmetric c K hKsym] at hzK
      exact Set.disjoint_left.mp hdis hzR hzK
  exact log_on_compact_avoiding_unbounded_cut T D c hT hD hc hDd hDu

/-- In particular every compact connected retained subset of the
physical carrier is confined to a single sheet in each quadratic
fiber. This rules out compact connected bypasses with no ray landing. -/
theorem quadratic_compact_contact_injOn (c : ℂ) (K Q R E : Set ℂ)
    (hKsym : ∀ z ∈ K, -z ∈ K)
    (hQsym : ∀ z ∈ Q, -z ∈ Q) (hzero : 0 ∈ Q)
    (hQ : IsPreconnected Q) (hR : IsPreconnected R)
    (hcontact : (Q ∩ closure R).Nonempty)
    (hdis : Disjoint R K) (hunb : ∀ B : ℝ, ∃ z ∈ R, B < ‖z‖)
    (hE : IsCompact E) (hEc : IsPreconnected E) (hEsub : E ⊆ K \ Q) :
    InjOn (fun z : ℂ => z^2+c) E := by
  classical
  let f : ℂ → ℂ := fun z => z^2+c
  let T : Set ℂ := f '' E
  have hf : Continuous f := (continuous_id.pow 2).add continuous_const
  obtain ⟨g,hg⟩ := quadratic_compact_contact_log c K Q R T hKsym hQsym
    hzero hQ hR hcontact hdis hunb (hE.image hf) (image_mono hEsub)
  let s : ℂ → ℂ := fun w => if h : w ∈ T then Complex.exp (g ⟨w,h⟩ / 2) else 0
  have hs : ContinuousOn s T := by
    rw [continuousOn_iff_continuous_restrict]
    have hEq : T.restrict s = fun w : T => Complex.exp (g w / 2) := by
      funext w
      simp [s,Set.restrict,w.property]
    rw [hEq]
    exact Complex.continuous_exp.comp (g.continuous.div_const 2)
  have hsection (w : ℂ) (hw : w ∈ T) : (s w)^2+c = w := by
    rw [show s w = Complex.exp (g ⟨w,hw⟩ / 2) by simp [s,hw],pow_two,← Complex.exp_add]
    rw [show g ⟨w,hw⟩ / 2 + g ⟨w,hw⟩ / 2 = g ⟨w,hw⟩ by ring, hg]
    simp
  have hne : (0 : ℂ) ∉ E := fun hz => (hEsub hz).2 hzero
  exact quadratic_injOn_of_continuous_section c E T s hEc hne
    (fun z hz => ⟨z,hz,rfl⟩) hs hsection

/-- An arbitrary connected bypass in a compact physical carrier must
accumulate on the deleted critical set. In particular a bypass with
positive clearance from that set is impossible. -/
theorem quadratic_bypass_forces_critical_contact (c : ℂ) (K Q R E : Set ℂ)
    (hK : IsCompact K) (hKsym : ∀ z ∈ K, -z ∈ K)
    (hQsym : ∀ z ∈ Q, -z ∈ Q) (hzero : 0 ∈ Q)
    (hQ : IsPreconnected Q) (hR : IsPreconnected R)
    (hcontact : (Q ∩ closure R).Nonempty)
    (hdis : Disjoint R K) (hunb : ∀ B : ℝ, ∃ z ∈ R, B < ‖z‖)
    (hEc : IsPreconnected E) (hEsub : E ⊆ K \ Q)
    (hbypass : ¬ InjOn (fun z : ℂ => z^2+c) E) :
    (closure E ∩ Q).Nonempty := by
  by_contra hn
  have hclK : closure E ⊆ K :=
    closure_minimal (fun z hz => (hEsub hz).1) hK.isClosed
  have hcl : closure E ⊆ K \ Q := by
    intro z hz
    exact ⟨hclK hz, fun hzQ => hn ⟨z,hz,hzQ⟩⟩
  have hci := quadratic_compact_contact_injOn c K Q R (closure E)
    hKsym hQsym hzero hQ hR hcontact hdis hunb
    (hK.of_isClosed_subset isClosed_closure hclK) hEc.closure hcl
  exact hbypass (fun x hx y hy he => hci (subset_closure hx) (subset_closure hy) he)

/-- In the no-accessibility setting the exact residual obstruction is
critical accumulation of a reflected component, not simply the failure
to exhibit a particular path or a particular ray. -/
theorem quadratic_reflected_component_forces_critical_contact
    (c : ℂ) (K Q R : Set ℂ) (a : ℂ)
    (hK : IsCompact K) (hKsym : ∀ z ∈ K, -z ∈ K)
    (hQsym : ∀ z ∈ Q, -z ∈ Q) (hzero : 0 ∈ Q)
    (hQ : IsPreconnected Q) (hR : IsPreconnected R)
    (hcontact : (Q ∩ closure R).Nonempty)
    (hdis : Disjoint R K) (hunb : ∀ B : ℝ, ∃ z ∈ R, B < ‖z‖)
    (ha : a ∈ K \ Q) (hb : -a ∈ connectedComponentIn (K \ Q) a) :
    (closure (connectedComponentIn (K \ Q) a) ∩ Q).Nonempty := by
  apply quadratic_bypass_forces_critical_contact c K Q R
    (connectedComponentIn (K \ Q) a) hK hKsym hQsym hzero hQ hR
    hcontact hdis hunb isPreconnected_connectedComponentIn
    (connectedComponentIn_subset _ _)
  intro hi
  have he : a = -a := hi (mem_connectedComponentIn ha) hb (by ring)
  have haz : a = 0 := by linear_combination (1/2 : ℂ) * he
  exact ha.2 (haz.symm ▸ hzero)


/-- A compact target retained away from the critical continuum has an
actual continuous quadratic inverse branch. The branch is a continuous
map on the subtype, with the full algebraic identity. -/
theorem quadratic_compact_contact_section (c : ℂ) (K Q R T : Set ℂ)
    (hKsym : ∀ z ∈ K, -z ∈ K)
    (hQsym : ∀ z ∈ Q, -z ∈ Q) (hzero : 0 ∈ Q)
    (hQ : IsPreconnected Q) (hR : IsPreconnected R)
    (hcontact : (Q ∩ closure R).Nonempty)
    (hdis : Disjoint R K) (hunb : ∀ B : ℝ, ∃ z ∈ R, B < ‖z‖)
    (hT : IsCompact T) (hTsub : T ⊆ (fun z : ℂ => z^2+c) '' (K \ Q)) :
    ∃ s : C(T, ℂ), ∀ w : T, (s w)^2+c = (w : ℂ) := by
  obtain ⟨g,hg⟩ := quadratic_compact_contact_log c K Q R T hKsym hQsym
    hzero hQ hR hcontact hdis hunb hT hTsub
  let s : C(T, ℂ) :=
    ⟨fun w => Complex.exp (g w / 2),
      Complex.continuous_exp.comp (g.continuous.div_const 2)⟩
  refine ⟨s,?_⟩
  intro w
  change (Complex.exp (g w / 2))^2+c = (w : ℂ)
  rw [pow_two,← Complex.exp_add,
    show g w / 2 + g w / 2 = g w by ring, hg]
  simp

/-- Exactly the two possible roots in a quadratic fiber, including
the degenerate critical fiber. -/
theorem quadratic_equal_roots_sign (c z w : ℂ) (h : z^2+c = w^2+c) :
    z = w ∨ z = -w := by
  have hp : (z-w)*(z+w) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hp with hsub | hadd
  · exact Or.inl (sub_eq_zero.mp hsub)
  · right
    linear_combination hadd

/-- A reference inverse branch on a compact Hausdorff base can be
modified to obey two closed, prescribed sign sets exactly when no
component of the base meets both. In particular no local connectivity
or finiteness of the component space is needed. -/
theorem quadratic_branch_extension_iff
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (c : ℂ) (w s : C(X, ℂ))
    (hroot : ∀ x, (s x)^2+c = w x)
    (hne : ∀ x, w x ≠ c)
    (P N : Set X) (hP : IsClosed P) (hN : IsClosed N) :
    (∃ t : C(X, ℂ), (∀ x, (t x)^2+c = w x) ∧
      (∀ x ∈ P, t x = s x) ∧ (∀ x ∈ N, t x = -s x)) ↔
    (∀ x ∈ P, ∀ y ∈ N, y ∉ connectedComponent x) := by
  classical
  have hsne (x : X) : s x ≠ 0 := by
    intro hz
    apply hne x
    have h := hroot x
    rw [hz] at h
    simpa using h.symm
  constructor
  · rintro ⟨t,ht,hp,hn⟩
    let A : Set X := {x | t x = s x}
    let B : Set X := {x | t x = -s x}
    have hA : IsClosed A := isClosed_eq t.continuous s.continuous
    have hB : IsClosed B := isClosed_eq t.continuous s.continuous.neg
    have hAB (x : X) : x ∈ A ∨ x ∈ B :=
      quadratic_equal_roots_sign c (t x) (s x) ((ht x).trans (hroot x).symm)
    have hd (x : X) (hx : x ∈ A) (hy : x ∈ B) : False := by
      change t x = s x at hx
      change t x = -s x at hy
      have he : s x = -s x := hx.symm.trans hy
      exact hsne x (by linear_combination (1/2 : ℂ) * he)
    have heq : Aᶜ = B := by
      ext x
      constructor
      · intro hx
        exact (hAB x).resolve_left hx
      · intro hy hx
        exact hd x hx hy
    have hAo : IsOpen A := by
      have hc : IsClosed Aᶜ := heq.symm ▸ hB
      simpa only [compl_compl] using hc.isOpen_compl
    have hAcl : IsClopen A := ⟨hA,hAo⟩
    intro x hx y hy hxy
    exact hd y (hAcl.connectedComponent_subset (show x ∈ A from hp x hx) hxy)
      (show y ∈ B from hn y hy)
  · intro h
    obtain ⟨U,hU,hPU,hUN⟩ :=
      LoopsStationaryMultiInterface.compact_clopen_separator_of_component_disjoint
        P N hP hN h
    have hfront : frontier U = ∅ := by
      rw [frontier, hU.1.closure_eq, hU.2.interior_eq, diff_self]
    let t : C(X, ℂ) :=
      ⟨U.piecewise s (fun x => -s x), by
        apply Continuous.piecewise
        · intro x hx
          have hf : False := by simpa [hfront] using hx
          exact hf.elim
        · exact s.continuous
        · exact s.continuous.neg⟩
    have hpos (x : X) (hx : x ∈ U) : t x = s x := by
      simp [t, Set.piecewise, hx]
    have hneg (x : X) (hx : x ∉ U) : t x = -s x := by
      simp [t, Set.piecewise, hx]
    refine ⟨t,?_,?_,?_⟩
    · intro x
      by_cases hx : x ∈ U
      · rw [hpos x hx, hroot x]
      · calc
          (t x)^2+c = (s x)^2+c := by rw [hneg x hx]; ring
          _ = w x := hroot x
    · exact fun x hx => hpos x (hPU hx)
    · exact fun x hx => hneg x (fun hu => Set.disjoint_left.mp hUN hu hx)

/-- Exact extension test for an already selected inverse branch on a
closed substage. Relative to any reference branch on the larger stage,
the old positive and negative sign loci must not merge in a component.
This condition is necessary and sufficient, not just a sufficient
finite approximation. -/
theorem quadratic_section_restriction_extension_iff
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (c : ℂ) (w s : C(X, ℂ))
    (hroot : ∀ x, (s x)^2+c = w x)
    (hne : ∀ x, w x ≠ c)
    (S : Set X) (hS : IsClosed S) (r : C(S, ℂ))
    (hr : ∀ x : S, (r x)^2+c = w (x : X)) :
    (∃ t : C(X, ℂ), (∀ x, (t x)^2+c = w x) ∧
      ∀ x : S, t (x : X) = r x) ↔
    (∀ x y : S, r x = s (x : X) → r y = -s (y : X) →
      (y : X) ∉ connectedComponent (x : X)) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS.isCompact
  let P : Set X := ((↑) : S → X) '' {x : S | r x = s (x : X)}
  let N : Set X := ((↑) : S → X) '' {x : S | r x = -s (x : X)}
  have hPc : IsClosed {x : S | r x = s (x : X)} :=
    isClosed_eq r.continuous (s.continuous.comp continuous_subtype_val)
  have hNc : IsClosed {x : S | r x = -s (x : X)} :=
    isClosed_eq r.continuous (s.continuous.comp continuous_subtype_val).neg
  have hP : IsClosed P := (hPc.isCompact.image continuous_subtype_val).isClosed
  have hN : IsClosed N := (hNc.isCompact.image continuous_subtype_val).isClosed
  have hext := quadratic_branch_extension_iff c w s hroot hne P N hP hN
  constructor
  · rintro ⟨t,ht,htr⟩ x y hx hy
    have htp : ∀ z ∈ P, t z = s z := by
      rintro z ⟨u,hu,rfl⟩
      exact (htr u).trans hu
    have htn : ∀ z ∈ N, t z = -s z := by
      rintro z ⟨u,hu,rfl⟩
      exact (htr u).trans hu
    exact (hext.mp ⟨t,ht,htp,htn⟩) (x : X) ⟨x,hx,rfl⟩ (y : X) ⟨y,hy,rfl⟩
  · intro h
    have hPN : ∀ x ∈ P, ∀ y ∈ N, y ∉ connectedComponent x := by
      rintro x ⟨u,hu,rfl⟩ y ⟨v,hv,rfl⟩
      exact h u v hu hv
    obtain ⟨t,ht,htp,htn⟩ := hext.mpr hPN
    refine ⟨t,ht,?_⟩
    intro x
    rcases quadratic_equal_roots_sign c (r x) (s (x : X))
      ((hr x).trans (hroot (x : X)).symm) with hx | hx
    · exact (htp (x : X) ⟨x,hx,rfl⟩).trans hx.symm
    · exact (htn (x : X) ⟨x,hx,rfl⟩).trans hx.symm


/-- A finite-component compact stage admits only finitely many inverse
branches. Values at one representative of each component determine a
branch, since the relative sign cannot change within a component. -/
theorem quadratic_section_finite_of_finite_components
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [Finite (ConnectedComponents X)]
    (c : ℂ) (w s : C(X, ℂ))
    (hroot : ∀ x, (s x)^2+c = w x)
    (hne : ∀ x, w x ≠ c) :
    Finite {r : C(X, ℂ) // ∀ x, (r x)^2+c = w x} := by
  classical
  let rep : ConnectedComponents X → X := fun q =>
    Classical.choose (ConnectedComponents.surjective_coe q)
  have hrep (q : ConnectedComponents X) : ConnectedComponents.mk (rep q) = q :=
    Classical.choose_spec (ConnectedComponents.surjective_coe q)
  let encode : {r : C(X, ℂ) // ∀ x, (r x)^2+c = w x} →
      (ConnectedComponents X → Bool) :=
    fun r q => decide (r.val (rep q) = s (rep q))
  apply Finite.of_injective encode
  intro r t h
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  let q := ConnectedComponents.mk x
  let z := rep q
  have hzq : ConnectedComponents.mk z = ConnectedComponents.mk x := hrep q
  have hxz : x ∈ connectedComponent z := ConnectedComponents.coe_eq_coe'.mp hzq.symm
  have he : decide (r.val z = s z) = decide (t.val z = s z) := congrFun h q
  have hrt : r.val z = t.val z := by
    by_cases hr : r.val z = s z
    · have ht : t.val z = s z :=
        of_decide_eq_true (he.symm.trans (decide_eq_true hr))
      exact hr.trans ht.symm
    · have ht : t.val z ≠ s z := by
        intro ht
        exact hr (of_decide_eq_true (he.trans (decide_eq_true ht)))
      have hr' := (quadratic_equal_roots_sign c (r.val z) (s z)
        ((r.property z).trans (hroot z).symm)).resolve_left hr
      have ht' := (quadratic_equal_roots_sign c (t.val z) (s z)
        ((t.property z).trans (hroot z).symm)).resolve_left ht
      exact hr'.trans ht'.symm
  by_contra hnot
  have hneg : r.val x = -t.val x :=
    (quadratic_equal_roots_sign c (r.val x) (t.val x)
      ((r.property x).trans (t.property x).symm)).resolve_left hnot
  have hP : ∀ u ∈ ({z} : Set X), r.val u = t.val u := by
    intro u hu
    rw [mem_singleton_iff.mp hu]
    exact hrt
  have hN : ∀ u ∈ ({x} : Set X), r.val u = -t.val u := by
    intro u hu
    rw [mem_singleton_iff.mp hu]
    exact hneg
  exact ((quadratic_branch_extension_iff c w t.val t.property hne
    ({z} : Set X) ({x} : Set X) isClosed_singleton isClosed_singleton).mp
      ⟨r.val,r.property,hP,hN⟩) z (by simp) x (by simp) hxz

/-- A countable inverse system of nonempty finite levels has a
compatible choice, even when restriction maps are not surjective.
Use compactness of the product of the finite discrete levels and
closed finite-horizon compatibility constraints. -/
theorem compatible_finite_system
    (A : ℕ → Type*) [∀ n, Finite (A n)]
    (hA : ∀ n, Nonempty (A n))
    (r : ∀ i j : ℕ, i ≤ j → A j → A i)
    (hcomp : ∀ (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (a : A k),
      r i j hij (r j k hjk a) = r i k (hij.trans hjk) a) :
    ∃ a : ∀ n, A n, ∀ (i j : ℕ) (hij : i ≤ j), r i j hij (a j) = a i := by
  classical
  letI : ∀ n, TopologicalSpace (A n) := fun _ => ⊥
  letI : ∀ n, DiscreteTopology (A n) := fun _ => ⟨rfl⟩
  letI : ∀ n, CompactSpace (A n) := fun _ => inferInstance
  letI : CompactSpace (∀ n, A n) := Pi.compactSpace
  let F (n : ℕ) : Set (∀ n, A n) :=
    {a | ∀ (i j : ℕ) (hij : i ≤ j), j ≤ n → r i j hij (a j) = a i}
  have hc (n : ℕ) : IsClosed (F n) := by
    have he : F n = ⋂ i : ℕ, ⋂ j : ℕ, ⋂ hij : i ≤ j, ⋂ _hjn : j ≤ n,
        {a : ∀ n, A n | r i j hij (a j) = a i} := by
      ext a
      simp [F]
    rw [he]
    refine isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun hij => isClosed_iInter fun _hjn => ?_
    have hr : Continuous (r i j hij) := continuous_of_discreteTopology
    exact isClosed_eq (hr.comp (continuous_apply j)) (continuous_apply i)
  have hn (n : ℕ) : (F n).Nonempty := by
    let a_n : A n := Classical.choice (hA n)
    let a (i : ℕ) : A i :=
      if h : i ≤ n then r i n h a_n else Classical.choice (hA i)
    refine ⟨a,?_⟩
    intro i j hij hjn
    have hin : i ≤ n := hij.trans hjn
    simp only [a, dif_pos hjn, dif_pos hin]
    exact hcomp i j n hij hjn a_n
  have hd : Directed (· ⊇ ·) F := by
    intro i j
    refine ⟨max i j,?_,?_⟩
    · intro a ha u v huv hvi
      exact ha u v huv (hvi.trans (le_max_left i j))
    · intro a ha u v huv hvj
      exact ha u v huv (hvj.trans (le_max_right i j))
  obtain ⟨a,ha⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    F hd hn (fun n => (hc n).isCompact) hc
  refine ⟨a,?_⟩
  intro i j hij
  exact (mem_iInter.mp ha j) i j hij le_rfl

/-- Compact-stage existence becomes a global continuous branch if
the stages exhaust by interiors and have finitely many components.
No surjectivity of the restriction maps is assumed. -/
theorem quadratic_global_section_of_finite_component_exhaustion
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (c : ℂ) (w : C(X, ℂ)) (hne : ∀ x, w x ≠ c)
    (T : ℕ → Set X) (hmono : Monotone T)
    (hcompact : ∀ n, IsCompact (T n))
    (hcover : ∀ x, ∃ n, x ∈ interior (T n))
    [∀ n, Finite (ConnectedComponents (T n))]
    (hbranch : ∀ n, ∃ s : C(T n, ℂ), ∀ x : T n, (s x)^2+c = w (x : X)) :
    ∃ s : C(X, ℂ), ∀ x, (s x)^2+c = w x := by
  classical
  let A (n : ℕ) := {s : C(T n, ℂ) // ∀ x : T n, (s x)^2+c = w (x : X)}
  have hA (n : ℕ) : Nonempty (A n) := by
    obtain ⟨s,hs⟩ := hbranch n
    exact ⟨⟨s,hs⟩⟩
  letI : ∀ n, CompactSpace (T n) := fun n => isCompact_iff_compactSpace.mp (hcompact n)
  letI : ∀ n, Finite (A n) := by
    intro n
    obtain ⟨s,hs⟩ := hbranch n
    let wt : C(T n, ℂ) := ⟨fun x => w (x : X), w.continuous.comp continuous_subtype_val⟩
    exact quadratic_section_finite_of_finite_components c wt s hs (fun x => hne (x : X))
  let r (i j : ℕ) (hij : i ≤ j) (a : A j) : A i :=
    ⟨⟨fun x => a.val (Set.inclusion (hmono hij) x),
       a.val.continuous.comp (continuous_inclusion (hmono hij))⟩,
     fun x => a.property (Set.inclusion (hmono hij) x)⟩
  have hcomp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (a : A k) :
      r i j hij (r j k hjk a) = r i k (hij.trans hjk) a := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    rfl
  obtain ⟨a,ha⟩ := compatible_finite_system A hA r hcomp
  let idx (x : X) : ℕ := Classical.choose (hcover x)
  have hi (x : X) : x ∈ T (idx x) := interior_subset (Classical.choose_spec (hcover x))
  let t (x : X) : ℂ := (a (idx x)).val ⟨x,hi x⟩
  have ht_eq (n : ℕ) (x : T n) : t (x : X) = (a n).val x := by
    let m := max (idx (x : X)) n
    have h1 := congrArg (fun b : A (idx (x : X)) => b.val ⟨(x : X),hi (x : X)⟩)
      (ha (idx (x : X)) m (le_max_left _ _))
    have h2 := congrArg (fun b : A n => b.val x)
      (ha n m (le_max_right _ _))
    change (a m).val ⟨(x : X),hmono (le_max_left _ _) (hi (x : X))⟩ = t (x : X) at h1
    change (a m).val ⟨(x : X),hmono (le_max_right _ _) x.property⟩ = (a n).val x at h2
    exact h1.symm.trans h2
  have ht_on (n : ℕ) : ContinuousOn t (T n) := by
    rw [continuousOn_iff_continuous_restrict]
    have he : (T n).restrict t = fun x : T n => (a n).val x := funext (ht_eq n)
    rw [he]
    exact (a n).val.continuous
  have hct : Continuous t := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨n,hn⟩ := hcover x
    exact (ht_on n x (interior_subset hn)).continuousAt (mem_interior_iff_mem_nhds.mp hn)
  refine ⟨⟨t,hct⟩,?_⟩
  intro x
  exact (a (idx x)).property ⟨x,hi x⟩

/-- In the actual quadratic target, exterior contact supplies the
compact branches; a finite-component exhaustion supplies a single
coherent branch on the whole retained image, not merely on each
compact substage. -/
theorem quadratic_global_contact_section
    (c : ℂ) (K Q R : Set ℂ)
    (hKsym : ∀ z ∈ K, -z ∈ K)
    (hQsym : ∀ z ∈ Q, -z ∈ Q) (hzero : 0 ∈ Q)
    (hQ : IsPreconnected Q) (hR : IsPreconnected R)
    (hcontact : (Q ∩ closure R).Nonempty)
    (hdis : Disjoint R K) (hunb : ∀ B : ℝ, ∃ z ∈ R, B < ‖z‖)
    (T : ℕ → Set ((fun z : ℂ => z^2+c) '' (K \ Q)))
    (hmono : Monotone T) (hcompact : ∀ n, IsCompact (T n))
    (hcover : ∀ x, ∃ n, x ∈ interior (T n))
    [∀ n, Finite (ConnectedComponents (T n))] :
    ∃ s : C((fun z : ℂ => z^2+c) '' (K \ Q), ℂ),
      ∀ w : ((fun z : ℂ => z^2+c) '' (K \ Q)), (s w)^2+c = (w : ℂ) := by
  let V : Set ℂ := (fun z : ℂ => z^2+c) '' (K \ Q)
  let w : C(V, ℂ) := ⟨Subtype.val,continuous_subtype_val⟩
  have hne (x : V) : w x ≠ c := by
    intro hx
    change (x : ℂ) = c at hx
    obtain ⟨z,hz,he⟩ := x.property
    have he' : z^2+c = c := he.trans hx
    have hmul : z*z = 0 := by linear_combination he'
    have hz0 : z = 0 := by
      rcases mul_eq_zero.mp hmul with hh | hh <;> exact hh
    exact hz.2 (hz0.symm ▸ hzero)
  have hbranch (n : ℕ) : ∃ s : C(T n, ℂ), ∀ x : T n, (s x)^2+c = w (x : V) := by
    let U : Set ℂ := ((↑) : V → ℂ) '' T n
    have hU : IsCompact U := (hcompact n).image continuous_subtype_val
    have hUV : U ⊆ V := by
      rintro _ ⟨x,hx,rfl⟩
      exact x.property
    obtain ⟨s,hs⟩ := quadratic_compact_contact_section c K Q R U
      hKsym hQsym hzero hQ hR hcontact hdis hunb hU hUV
    let inc : T n → U := fun x =>
      ⟨((x : V) : ℂ),⟨(x : V),x.property,rfl⟩⟩
    have hval : Continuous (fun x : T n => ((x : V) : ℂ)) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hinc : Continuous inc := hval.subtype_mk (fun x => ⟨(x : V),x.property,rfl⟩)
    refine ⟨⟨fun x => s (inc x),s.continuous.comp hinc⟩,?_⟩
    intro x
    exact hs (inc x)
  exact quadratic_global_section_of_finite_component_exhaustion
    c w hne T hmono hcompact hcover hbranch

/-- Full connected-set injectivity, including noncompact and non-path
connected witnesses, under the actual target's finite-component
exhaustion condition. This excludes accumulation bypasses too. -/
theorem quadratic_no_bypass_of_finite_component_exhaustion
    (c : ℂ) (K Q R E : Set ℂ)
    (hKsym : ∀ z ∈ K, -z ∈ K)
    (hQsym : ∀ z ∈ Q, -z ∈ Q) (hzero : 0 ∈ Q)
    (hQ : IsPreconnected Q) (hR : IsPreconnected R)
    (hcontact : (Q ∩ closure R).Nonempty)
    (hdis : Disjoint R K) (hunb : ∀ B : ℝ, ∃ z ∈ R, B < ‖z‖)
    (T : ℕ → Set ((fun z : ℂ => z^2+c) '' (K \ Q)))
    (hmono : Monotone T) (hcompact : ∀ n, IsCompact (T n))
    (hcover : ∀ x, ∃ n, x ∈ interior (T n))
    [∀ n, Finite (ConnectedComponents (T n))]
    (hEc : IsPreconnected E) (hEsub : E ⊆ K \ Q) :
    InjOn (fun z : ℂ => z^2+c) E := by
  classical
  let V : Set ℂ := (fun z : ℂ => z^2+c) '' (K \ Q)
  obtain ⟨s,hs⟩ := quadratic_global_contact_section c K Q R
    hKsym hQsym hzero hQ hR hcontact hdis hunb T hmono hcompact hcover
  let S : ℂ → ℂ := fun w => if h : w ∈ V then s ⟨w,h⟩ else 0
  have hS : ContinuousOn S V := by
    rw [continuousOn_iff_continuous_restrict]
    have he : V.restrict S = fun w : V => s w := by
      funext w
      simp [S,Set.restrict,w.property]
    rw [he]
    exact s.continuous
  have hsec (w : ℂ) (hw : w ∈ V) : (S w)^2+c = w := by
    rw [show S w = s ⟨w,hw⟩ by simp [S,hw]]
    exact hs ⟨w,hw⟩
  exact quadratic_injOn_of_continuous_section c E V S hEc
    (fun hz => (hEsub hz).2 hzero) (fun z hz => ⟨z,hEsub hz,rfl⟩) hS hsec

/-- Conditional full base separation with no accessible-ray
hypothesis, no local connectivity and no compact-witness limitation. -/
theorem quadratic_reflected_separator_finite_component_exhaustion
    (c : ℂ) (K Q R : Set ℂ) (a : ℂ)
    (hKsym : ∀ z ∈ K, -z ∈ K)
    (hQsym : ∀ z ∈ Q, -z ∈ Q) (hzero : 0 ∈ Q)
    (hQ : IsPreconnected Q) (hR : IsPreconnected R)
    (hcontact : (Q ∩ closure R).Nonempty)
    (hdis : Disjoint R K) (hunb : ∀ B : ℝ, ∃ z ∈ R, B < ‖z‖)
    (T : ℕ → Set ((fun z : ℂ => z^2+c) '' (K \ Q)))
    (hmono : Monotone T) (hcompact : ∀ n, IsCompact (T n))
    (hcover : ∀ x, ∃ n, x ∈ interior (T n))
    [∀ n, Finite (ConnectedComponents (T n))]
    (ha : a ∈ K \ Q) :
    -a ∉ connectedComponentIn (K \ Q) a := by
  intro hb
  have hi := quadratic_no_bypass_of_finite_component_exhaustion c K Q R
    (connectedComponentIn (K \ Q) a) hKsym hQsym hzero hQ hR hcontact hdis hunb
    T hmono hcompact hcover isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
  have he : a = -a := hi (mem_connectedComponentIn ha) hb (by ring)
  have haz : a = 0 := by linear_combination (1/2 : ℂ) * he
  exact ha.2 (haz.symm ▸ hzero)

end LoopsStationaryCompactContact
