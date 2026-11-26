import StationarySeparatorTransport
import StationaryMultiInterface
import TerminalFiberExclusion
import SaturatedTelescope

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

/-- For a compact planar set with empty interior, its exterior is
dense and unbounded. Connectedness of the exterior is a separate
fullness hypothesis. -/
theorem compact_emptyInterior_exterior_data (K : Set ℂ)
    (hK : IsCompact K) (hKi : interior K = ∅) :
    closure Kᶜ = univ ∧ Disjoint Kᶜ K ∧
      (∀ B : ℝ, ∃ z ∈ Kᶜ, B < ‖z‖) := by
  refine ⟨?_,?_,?_⟩
  · rw [closure_compl, hKi, compl_empty]
  · exact Set.disjoint_left.mpr (fun z hz hzK => hz hzK)
  · intro B
    obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
    let t : ℝ := max 0 (max M B) + 1
    have ht0 : 0 ≤ t := by
      dsimp [t]
      linarith [le_max_left (0:ℝ) (max M B)]
    have htM : M < t := by
      dsimp [t]
      linarith [le_max_left M B,le_max_right (0:ℝ) (max M B)]
    have htB : B < t := by
      dsimp [t]
      linarith [le_max_right M B,le_max_right (0:ℝ) (max M B)]
    have hnorm : ‖(t:ℂ)‖ = t := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0]
    refine ⟨(t:ℂ),?_,?_⟩
    · intro hz
      have hb := hM (t:ℂ) hz
      change ‖(t:ℂ)‖ ≤ M at hb
      rw [hnorm] at hb
      exact (not_lt_of_ge hb) htM
    · rw [hnorm]
      exact htB

/-- For a full reflection-invariant compact carrier with empty interior,
a connected quadratic bypass avoiding zero must accumulate at zero
itself, rather than merely at some point of a deleted critical set.
There is no connectedness or reflection requirement on the deletion. -/
theorem quadratic_full_emptyInterior_bypass_accumulates_zero
    (c : ℂ) (K E : Set ℂ)
    (hK : IsCompact K) (hKsym : ∀ z ∈ K, -z ∈ K)
    (hfull : IsPreconnected Kᶜ) (hKi : interior K = ∅)
    (hEc : IsPreconnected E) (hEsub : E ⊆ K) (hEzero : (0 : ℂ) ∉ E)
    (hbypass : ¬ InjOn (fun z : ℂ => z^2+c) E) :
    (0 : ℂ) ∈ closure E := by
  obtain ⟨hcl,hdis,hunb⟩ := compact_emptyInterior_exterior_data K hK hKi
  have hcontact : (({0} : Set ℂ) ∩ closure Kᶜ).Nonempty := by
    rw [hcl]
    exact ⟨0,by simp⟩
  have hsym : ∀ z ∈ ({0}:Set ℂ), -z ∈ ({0}:Set ℂ) := by
    intro z hz
    rw [mem_singleton_iff.mp hz]
    simp
  have hsub : E ⊆ K \ ({0}:Set ℂ) := by
    intro z hz
    refine ⟨hEsub hz,?_⟩
    intro hz0
    exact hEzero ((mem_singleton_iff.mp hz0) ▸ hz)
  obtain ⟨z,hzcl,hz0⟩ := quadratic_bypass_forces_critical_contact c K {0} Kᶜ E
    hK hKsym hsym (by simp) isPreconnected_singleton hfull hcontact hdis hunb
    hEc hsub hbypass
  rwa [mem_singleton_iff.mp hz0] at hzcl

/-- Under the preceding carrier hypotheses, critical-point clearance
alone rules out every connected antipodal bypass after an arbitrary
deletion. Neither compactness of a bypass nor finite-component
exhaustion of the retained image is needed. -/
theorem quadratic_full_emptyInterior_separator_critical_clearance
    (c : ℂ) (K Q : Set ℂ) (a : ℂ)
    (hK : IsCompact K) (hKsym : ∀ z ∈ K, -z ∈ K)
    (hfull : IsPreconnected Kᶜ) (hKi : interior K = ∅)
    (hzero : (0 : ℂ) ∈ Q)
    (hclear : (0 : ℂ) ∉ closure (K \ Q))
    (ha : a ∈ K \ Q) :
    -a ∉ connectedComponentIn (K \ Q) a := by
  intro hb
  let E := connectedComponentIn (K \ Q) a
  have hsub : E ⊆ K \ Q := connectedComponentIn_subset _ _
  have hEzero : (0 : ℂ) ∉ E := fun hz => (hsub hz).2 hzero
  have hbad : ¬ InjOn (fun z : ℂ => z^2+c) E := by
    intro hi
    have he : a = -a := hi (mem_connectedComponentIn ha) hb (by ring)
    have haz : a = 0 := by linear_combination (1/2 : ℂ) * he
    exact ha.2 (haz.symm ▸ hzero)
  have hcl := quadratic_full_emptyInterior_bypass_accumulates_zero c K E
    hK hKsym hfull hKi isPreconnected_connectedComponentIn
    (fun z hz => (hsub hz).1) hEzero hbad
  exact hclear (closure_mono hsub hcl)

/-- On the genuine filled Julia carrier, compactness and reflection
are supplied by the established quadratic theorems, not assumed.
Fullness, empty interior, and a relative critical neighborhood in
the deleted set are the remaining explicit geometric premises. -/
theorem quadratic_filled_separator_critical_clearance
    (c : ℂ) (Q : Set ℂ) (a : ℂ)
    (hfull : IsPreconnected (LoopsStationaryFiberDynamics.quadraticFilled c)ᶜ)
    (hKi : interior (LoopsStationaryFiberDynamics.quadraticFilled c) = ∅)
    (hzero : (0 : ℂ) ∈ Q)
    (hclear : ∃ ε : ℝ, 0 < ε ∧
      ∀ z ∈ LoopsStationaryFiberDynamics.quadraticFilled c, ‖z‖ < ε → z ∈ Q)
    (ha : a ∈ LoopsStationaryFiberDynamics.quadraticFilled c \ Q) :
    -a ∉ connectedComponentIn
      (LoopsStationaryFiberDynamics.quadraticFilled c \ Q) a := by
  let K := LoopsStationaryFiberDynamics.quadraticFilled c
  obtain ⟨ε,hε,hb⟩ := hclear
  have hsub : K \ Q ⊆ {z : ℂ | ε ≤ ‖z‖} := by
    intro z hz
    exact le_of_not_gt (fun h => hz.2 (hb z hz.1 h))
  have hclosed : IsClosed {z : ℂ | ε ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
  have hclear' : (0 : ℂ) ∉ closure (K \ Q) := by
    intro hz
    have hh := closure_minimal hsub hclosed hz
    change ε ≤ ‖(0 : ℂ)‖ at hh
    rw [norm_zero] at hh
    exact (not_lt_of_ge hh) hε
  exact quadratic_full_emptyInterior_separator_critical_clearance c K Q a
    (LoopsStationaryFiberDynamics.quadratic_filled_compact c)
    (fun z hz => (LoopsTerminalFiberExclusion.quadratic_filled_neg_mem c z).mpr hz)
    hfull hKi hzero hclear' ha

/-- A compact planar locus characterized by simultaneous uniform norm
bounds on entire functions has preconnected complement. The maximum
modulus principle excludes bounded complementary components, and a
circle larger than the carrier joins any two remaining components. -/
theorem compact_uniform_entire_locus_full (K : Set ℂ)
    (hK : IsCompact K) (F : ℕ → ℂ → ℂ) (M : ℝ)
    (hd : ∀ n, Differentiable ℂ (F n))
    (hbound : ∀ z ∈ K, ∀ n, ‖F n z‖ ≤ M)
    (hchar : ∀ z, (∀ n, ‖F n z‖ ≤ M) → z ∈ K) :
    IsPreconnected Kᶜ := by
  have hfront (x : ℂ) :
      frontier (connectedComponentIn Kᶜ x) ⊆ K := by
    intro z hz
    by_contra hzk
    have hzK : z ∈ Kᶜ := hzk
    have hzo : IsOpen (connectedComponentIn Kᶜ z) :=
      hK.isClosed.isOpen_compl.connectedComponentIn
    have hxo : IsOpen (connectedComponentIn Kᶜ x) :=
      hK.isClosed.isOpen_compl.connectedComponentIn
    have hzin := mem_connectedComponentIn hzK
    obtain ⟨u,huz,hux⟩ := (mem_closure_iff.mp hz.1) _ hzo hzin
    have heq := (connectedComponentIn_eq hux).trans (connectedComponentIn_eq huz).symm
    have hzCx : z ∈ connectedComponentIn Kᶜ x := heq.symm ▸ hzin
    apply hz.2
    rw [hxo.interior_eq]
    exact hzCx
  have hunb (x : ℂ) (hx : x ∈ Kᶜ) :
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x) := by
    intro hb
    apply hx
    apply hchar x
    intro n
    exact Complex.norm_le_of_forall_mem_frontier_norm_le hb
      (hd n).diffContOnCl (fun z hz => hbound z (hfront x hz) n)
      (subset_closure (mem_connectedComponentIn hx))
  have hcross (x : ℂ) (hx : x ∈ Kᶜ) (r : ℝ) (hr : ‖x‖ ≤ r) :
      ∃ z ∈ connectedComponentIn Kᶜ x, ‖z‖ = r := by
    have hlarge : ∃ z ∈ connectedComponentIn Kᶜ x, r < ‖z‖ := by
      by_contra! hn
      apply hunb x hx
      apply (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mpr
      refine ⟨r,?_⟩
      intro z hz
      simpa [Metric.mem_closedBall,dist_zero_right] using hn z hz
    obtain ⟨z,hz,hbig⟩ := hlarge
    exact isPreconnected_connectedComponentIn.intermediate_value
      (mem_connectedComponentIn hx) hz continuous_norm.continuousOn
      ⟨hr,hbig.le⟩
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  by_cases hne : (Kᶜ : Set ℂ).Nonempty
  · obtain ⟨x,hx⟩ := hne
    have heq : connectedComponentIn Kᶜ x = Kᶜ := by
      apply subset_antisymm (connectedComponentIn_subset _ _)
      intro y hy
      let r : ℝ := max R (max ‖x‖ ‖y‖) + 1
      have hrR : R < r := by
        dsimp [r]
        linarith [le_max_left R (max ‖x‖ ‖y‖)]
      have hrx : ‖x‖ ≤ r := by
        dsimp [r]
        linarith [le_max_left ‖x‖ ‖y‖,le_max_right R (max ‖x‖ ‖y‖)]
      have hry : ‖y‖ ≤ r := by
        dsimp [r]
        linarith [le_max_right ‖x‖ ‖y‖,le_max_right R (max ‖x‖ ‖y‖)]
      obtain ⟨v,hv,hvr⟩ := hcross x hx r hrx
      obtain ⟨w,hw,hwr⟩ := hcross y hy r hry
      have hsph : Metric.sphere (0:ℂ) r ⊆ Kᶜ := by
        intro z hz hzK
        have hzr : ‖z‖ = r := by
          simpa [Metric.mem_sphere,dist_zero_right] using hz
        have hh := hR z hzK
        change ‖z‖ ≤ R at hh
        rw [hzr] at hh
        exact (not_lt_of_ge hh) hrR
      have hvS : v ∈ Metric.sphere (0:ℂ) r := by
        simpa [Metric.mem_sphere,dist_zero_right] using hvr
      have hwS : w ∈ Metric.sphere (0:ℂ) r := by
        simpa [Metric.mem_sphere,dist_zero_right] using hwr
      have hS : IsPreconnected (Metric.sphere (0:ℂ) r) :=
        isPreconnected_sphere (by simp) (0:ℂ) r
      have hvw := hS.subset_connectedComponentIn hvS hsph hwS
      have hxy := (connectedComponentIn_eq hv).trans
        ((connectedComponentIn_eq hvw).trans (connectedComponentIn_eq hw).symm)
      exact hxy.symm ▸ mem_connectedComponentIn hy
    rw [← heq]
    exact isPreconnected_connectedComponentIn
  · have he : Kᶜ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [he]
    exact isPreconnected_empty

/-- Every actual quadratic iterate is entire, including the zeroth
iterate. -/
theorem quadratic_orbit_entire (c : ℂ) (n : ℕ) :
    Differentiable ℂ (QuadraticEscape.orbit c n) := by
  induction n with
  | zero => exact differentiable_id
  | succ n ih =>
    change Differentiable ℂ (fun z : ℂ => (QuadraticEscape.orbit c n z)^2+c)
    exact (ih.pow 2).add (differentiable_const c)

/-- The genuine bounded-orbit locus is full at every complex parameter.
This does not assume connectedness of the filled Julia set itself. -/
theorem quadratic_filled_full (c : ℂ) :
    IsPreconnected (LoopsStationaryFiberDynamics.quadraticFilled c)ᶜ := by
  apply compact_uniform_entire_locus_full
    (LoopsStationaryFiberDynamics.quadraticFilled c)
    (LoopsStationaryFiberDynamics.quadratic_filled_compact c)
    (QuadraticEscape.orbit c) (1+‖c‖) (quadratic_orbit_entire c)
  · intro z hz n
    exact QuadraticEscape.escape_zero_orbit_bound c z hz n
  · intro z hz
    exact (LoopsStationaryFiberDynamics.quadratic_filled_iff_bounded c z).mpr
      ⟨1+‖c‖,hz⟩

/-- On the genuine filled Julia set, empty interior alone forces every
connected noninjective witness avoiding zero to accumulate at zero. -/
theorem quadratic_filled_bypass_accumulates_zero (c : ℂ) (E : Set ℂ)
    (hKi : interior (LoopsStationaryFiberDynamics.quadraticFilled c) = ∅)
    (hEc : IsPreconnected E)
    (hEsub : E ⊆ LoopsStationaryFiberDynamics.quadraticFilled c)
    (hEzero : (0 : ℂ) ∉ E)
    (hbypass : ¬ InjOn (fun z : ℂ => z^2+c) E) :
    (0 : ℂ) ∈ closure E := by
  exact quadratic_full_emptyInterior_bypass_accumulates_zero c
    (LoopsStationaryFiberDynamics.quadraticFilled c) E
    (LoopsStationaryFiberDynamics.quadratic_filled_compact c)
    (fun z hz => (LoopsTerminalFiberExclusion.quadratic_filled_neg_mem c z).mpr hz)
    (quadratic_filled_full c) hKi hEc hEsub hEzero hbypass

/-- Fullness is now discharged. Relative critical clearance and empty
interior suffice for full separation on the actual filled Julia set. -/
theorem quadratic_filled_separator_of_emptyInterior_clearance
    (c : ℂ) (Q : Set ℂ) (a : ℂ)
    (hKi : interior (LoopsStationaryFiberDynamics.quadraticFilled c) = ∅)
    (hzero : (0 : ℂ) ∈ Q)
    (hclear : ∃ ε : ℝ, 0 < ε ∧
      ∀ z ∈ LoopsStationaryFiberDynamics.quadraticFilled c, ‖z‖ < ε → z ∈ Q)
    (ha : a ∈ LoopsStationaryFiberDynamics.quadraticFilled c \ Q) :
    -a ∉ connectedComponentIn
      (LoopsStationaryFiberDynamics.quadraticFilled c \ Q) a :=
  quadratic_filled_separator_critical_clearance c Q a
    (quadratic_filled_full c) hKi hzero hclear ha

/-- Every repelling periodic point belongs to the closure of the
exterior of the actual filled Julia set. A hypothetical interior disk
would bound the derivatives of every iterate by Cauchy's estimate;
the derivatives of successive periodic returns grow geometrically. -/
theorem quadratic_repelling_point_exterior_contact
    (c a : ℂ) (p : ℕ) (hper : QuadraticEscape.orbit c p a = a)
    (hmul : 1 < ‖deriv (QuadraticEscape.orbit c p) a‖) :
    a ∈ closure (LoopsStationaryFiberDynamics.quadraticFilled c)ᶜ := by
  by_contra hn
  rw [closure_compl] at hn
  have ha : a ∈ interior (LoopsStationaryFiberDynamics.quadraticFilled c) :=
    not_not.mp hn
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp isOpen_interior a ha
  have hs : 0 < r/2 := by positivity
  have hsphere : Metric.sphere a (r/2) ⊆
      LoopsStationaryFiberDynamics.quadraticFilled c := by
    intro z hz
    apply interior_subset
    apply hball
    rw [Metric.mem_sphere] at hz
    rw [Metric.mem_ball,hz]
    linarith
  have hbound (n : ℕ) : ‖deriv (QuadraticEscape.orbit c n) a‖ ≤
      (1+‖c‖)/(r/2) := by
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hs
      (quadratic_orbit_entire c n).diffContOnCl
      (fun z hz => QuadraticEscape.escape_zero_orbit_bound c z (hsphere hz) n)
  let f := QuadraticEscape.orbit c p
  let μ := deriv f a
  have hf : HasDerivAt f μ a := (quadratic_orbit_entire c p a).hasDerivAt
  have hderiv (k : ℕ) :
      HasDerivAt (QuadraticEscape.orbit c (p*k)) (μ^k) a := by
    induction k with
    | zero =>
      simpa [QuadraticEscape.orbit] using hasDerivAt_id a
    | succ k ih =>
      have houter : HasDerivAt (QuadraticEscape.orbit c (p*k)) (μ^k) (f a) := by
        rw [show f a = a from hper]
        exact ih
      have heq : QuadraticEscape.orbit c (p*(k+1)) =
          QuadraticEscape.orbit c (p*k) ∘ f := by
        funext z
        rw [Nat.mul_succ, Nat.add_comm (p*k) p,
          LoopsSaturatedTelescope.quadratic_orbit_add] <;> rfl
      rw [heq,pow_succ]
      exact houter.comp a hf
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt ((1+‖c‖)/(r/2))
    (show 1 < ‖μ‖ from hmul)
  have hb := hbound (p*k)
  rw [(hderiv k).deriv,norm_pow] at hb
  exact (not_lt_of_ge hb) hk

/-- The genuine filled Julia exterior is unbounded, independently of
whether the filled Julia set has interior. -/
theorem quadratic_filled_exterior_unbounded (c : ℂ) :
    ∀ B : ℝ, ∃ z ∈ (LoopsStationaryFiberDynamics.quadraticFilled c)ᶜ,
      B < ‖z‖ := by
  intro B
  let t : ℝ := max (1+‖c‖) B + 1
  have htM : 1+‖c‖ < t := by
    dsimp [t]
    linarith [le_max_left (1+‖c‖) B]
  have htB : B < t := by
    dsimp [t]
    linarith [le_max_right (1+‖c‖) B]
  have ht0 : 0 ≤ t := by linarith [norm_nonneg c]
  have hn : ‖(t:ℂ)‖ = t := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0]
  refine ⟨(t:ℂ),?_,?_⟩
  · intro hz
    have hb := QuadraticEscape.escape_zero_orbit_bound c (t:ℂ) hz 0
    change ‖(t:ℂ)‖ ≤ 1+‖c‖ at hb
    rw [hn] at hb
    exact (not_lt_of_ge hb) htM
  · rw [hn]
    exact htB

/-- For the actual filled carrier, a single repelling periodic point
in the symmetric connected critical set suffices to discharge all
exterior-contact hypotheses of the compact bypass theorem. -/
theorem quadratic_filled_compact_injOn_of_repelling_contact
    (c b : ℂ) (p : ℕ) (Q E : Set ℂ)
    (hQsym : ∀ z ∈ Q, -z ∈ Q) (hzero : 0 ∈ Q)
    (hQ : IsPreconnected Q) (hbQ : b ∈ Q)
    (hper : QuadraticEscape.orbit c p b = b)
    (hmul : 1 < ‖deriv (QuadraticEscape.orbit c p) b‖)
    (hE : IsCompact E) (hEc : IsPreconnected E)
    (hEsub : E ⊆ LoopsStationaryFiberDynamics.quadraticFilled c \ Q) :
    InjOn (fun z : ℂ => z^2+c) E := by
  let K := LoopsStationaryFiberDynamics.quadraticFilled c
  exact quadratic_compact_contact_injOn c K Q Kᶜ E
    (fun z hz => (LoopsTerminalFiberExclusion.quadratic_filled_neg_mem c z).mpr hz)
    hQsym hzero hQ (quadratic_filled_full c)
    ⟨b,hbQ,quadratic_repelling_point_exterior_contact c b p hper hmul⟩
    (Set.disjoint_left.mpr (fun z hz hzK => hz hzK))
    (quadratic_filled_exterior_unbounded c) hE hEc hEsub

/-- For the actual filled carrier, repelling periodic contact and
the compact finite-component exhaustion alone discharge full
connected-set separation. No global empty-interior hypothesis or
accessible ray is required for this route. -/
theorem quadratic_filled_separator_of_repelling_contact_exhaustion
    (c a b : ℂ) (p : ℕ) (Q : Set ℂ)
    (hQsym : ∀ z ∈ Q, -z ∈ Q) (hzero : 0 ∈ Q)
    (hQ : IsPreconnected Q) (hbQ : b ∈ Q)
    (hper : QuadraticEscape.orbit c p b = b)
    (hmul : 1 < ‖deriv (QuadraticEscape.orbit c p) b‖)
    (T : ℕ → Set ((fun z : ℂ => z^2+c) ''
      (LoopsStationaryFiberDynamics.quadraticFilled c \ Q)))
    (hmono : Monotone T) (hcompact : ∀ n, IsCompact (T n))
    (hcover : ∀ x, ∃ n, x ∈ interior (T n))
    [∀ n, Finite (ConnectedComponents (T n))]
    (ha : a ∈ LoopsStationaryFiberDynamics.quadraticFilled c \ Q) :
    -a ∉ connectedComponentIn
      (LoopsStationaryFiberDynamics.quadraticFilled c \ Q) a := by
  let K := LoopsStationaryFiberDynamics.quadraticFilled c
  exact quadratic_reflected_separator_finite_component_exhaustion c K Q Kᶜ a
    (fun z hz => (LoopsTerminalFiberExclusion.quadratic_filled_neg_mem c z).mpr hz)
    hQsym hzero hQ (quadratic_filled_full c)
    ⟨b,hbQ,quadratic_repelling_point_exterior_contact c b p hper hmul⟩
    (Set.disjoint_left.mpr (fun z hz hzK => hz hzK))
    (quadratic_filled_exterior_unbounded c) T hmono hcompact hcover ha

/-- On the inverse image of an open subset of a locally connected compact
model, two points of any preconnected set have a compact preconnected
envelope in that inverse image. The physical space itself need not be
locally connected; closedness and connected fibers suffice. -/
theorem compact_pair_envelope_of_monotone_model
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [LocallyConnectedSpace Y]
    (q : X → Y) (hq : Continuous q) (hsurj : Function.Surjective q)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (A : Set Y) (hA : IsClosed A)
    (E : Set X) (hEc : IsPreconnected E) (hEsub : E ⊆ q ⁻¹' Aᶜ)
    (x y : X) (hx : x ∈ E) (hy : y ∈ E) :
    ∃ B : Set X, IsCompact B ∧ IsPreconnected B ∧ B ⊆ q ⁻¹' Aᶜ ∧
      x ∈ B ∧ y ∈ B := by
  let D := connectedComponentIn Aᶜ (q x)
  have hxA : q x ∈ Aᶜ := hEsub hx
  have hxD : q x ∈ D := mem_connectedComponentIn hxA
  have hDopen : IsOpen D := hA.isOpen_compl.connectedComponentIn
  have hDconn : IsConnected D := isConnected_connectedComponentIn_iff.mpr hxA
  have hIm : IsPreconnected (q '' E) := hEc.image q hq.continuousOn
  have hImsub : q '' E ⊆ Aᶜ := by
    rintro _ ⟨z,hz,rfl⟩
    exact hEsub hz
  have hyD : q y ∈ D := hIm.subset_connectedComponentIn
    (mem_image_of_mem q hx) hImsub (mem_image_of_mem q hy)
  let M : Set Y := {q x,q y}
  have hM : IsCompact M := isCompact_singleton.insert _
  have hMD : M ⊆ D := by
    intro z hz
    change z ∈ ({q x,q y} : Set Y) at hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxD
    · exact hyD
  obtain ⟨C,hCc,hCconn,hCD,hMC⟩ :=
    LoopsTerminalFiberExclusion.compact_connected_envelope D M
      hDopen hDconn hM hMD
  refine ⟨q ⁻¹' C,(hCc.isClosed.preimage hq).isCompact,
    LoopsStationaryMonotoneGeometry.preconnected_preimage_closed_fibers
      q hq.isClosedMap hsurj hf hCconn.isPreconnected,?_,?_,?_⟩
  · intro z hz
    exact connectedComponentIn_subset Aᶜ (q x) (hCD hz)
  · exact interior_subset (hMC (by simp [M]))
  · exact interior_subset (hMC (by simp [M]))

/-- Saturation of the deleted critical set in a locally connected
monotone model removes the need for a finite-component exhaustion.
An arbitrary connected witness can be replaced, for each pair of
points, by a compact physical witness in the retained set. -/
theorem quadratic_filled_no_bypass_of_saturated_model
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [LocallyConnectedSpace Y]
    (c b : ℂ) (p : ℕ) (Q E : Set ℂ)
    (hQsym : ∀ z ∈ Q, -z ∈ Q) (hzero : 0 ∈ Q)
    (hQ : IsPreconnected Q) (hbQ : b ∈ Q)
    (hper : QuadraticEscape.orbit c p b = b)
    (hmul : 1 < ‖deriv (QuadraticEscape.orbit c p) b‖)
    (q : LoopsStationaryFiberDynamics.quadraticFilled c → Y)
    (hq : Continuous q) (hsurj : Function.Surjective q)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (A : Set Y) (hA : IsClosed A)
    (hsat : ∀ z : LoopsStationaryFiberDynamics.quadraticFilled c,
      (z:ℂ) ∈ Q ↔ q z ∈ A)
    (hEc : IsPreconnected E)
    (hEsub : E ⊆ LoopsStationaryFiberDynamics.quadraticFilled c \ Q) :
    InjOn (fun z : ℂ => z^2+c) E := by
  let K := LoopsStationaryFiberDynamics.quadraticFilled c
  letI : CompactSpace K :=
    isCompact_iff_compactSpace.mp (LoopsStationaryFiberDynamics.quadratic_filled_compact c)
  letI : PreconnectedSpace E := isPreconnected_iff_preconnectedSpace.mp hEc
  let j : E → K := fun z => ⟨(z:ℂ),(hEsub z.property).1⟩
  have hj : Continuous j :=
    continuous_subtype_val.subtype_mk (fun z => (hEsub z.property).1)
  let D : Set K := j '' (univ : Set E)
  have hD : IsPreconnected D := isPreconnected_univ.image j hj.continuousOn
  have hDsub : D ⊆ q ⁻¹' Aᶜ := by
    rintro _ ⟨z,_,rfl⟩
    intro hz
    exact (hEsub z.property).2 ((hsat (j z)).mpr hz)
  intro x hx y hy hxy
  let x' := j ⟨x,hx⟩
  let y' := j ⟨y,hy⟩
  have hxD : x' ∈ D := ⟨⟨x,hx⟩,mem_univ _,rfl⟩
  have hyD : y' ∈ D := ⟨⟨y,hy⟩,mem_univ _,rfl⟩
  obtain ⟨B,hBc,hBpre,hBsub,hxB,hyB⟩ :=
    compact_pair_envelope_of_monotone_model q hq hsurj hf A hA D hD hDsub
      x' y' hxD hyD
  let W : Set ℂ := (Subtype.val : K → ℂ) '' B
  have hWc : IsCompact W := hBc.image continuous_subtype_val
  have hWpre : IsPreconnected W :=
    hBpre.image _ continuous_subtype_val.continuousOn
  have hWsub : W ⊆ K \ Q := by
    rintro _ ⟨z,hz,rfl⟩
    refine ⟨z.property,?_⟩
    intro hzQ
    exact (hBsub hz) ((hsat z).mp hzQ)
  exact quadratic_filled_compact_injOn_of_repelling_contact c b p Q W
    hQsym hzero hQ hbQ hper hmul hWc hWpre hWsub
    ⟨x',hxB,rfl⟩ ⟨y',hyB,rfl⟩ hxy

/-- Exact full component separation on the physical filled Julia set
from a saturated deletion in a locally connected monotone model. -/
theorem quadratic_filled_separator_of_saturated_model
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [LocallyConnectedSpace Y]
    (c a b : ℂ) (p : ℕ) (Q : Set ℂ)
    (hQsym : ∀ z ∈ Q, -z ∈ Q) (hzero : 0 ∈ Q)
    (hQ : IsPreconnected Q) (hbQ : b ∈ Q)
    (hper : QuadraticEscape.orbit c p b = b)
    (hmul : 1 < ‖deriv (QuadraticEscape.orbit c p) b‖)
    (q : LoopsStationaryFiberDynamics.quadraticFilled c → Y)
    (hq : Continuous q) (hsurj : Function.Surjective q)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (A : Set Y) (hA : IsClosed A)
    (hsat : ∀ z : LoopsStationaryFiberDynamics.quadraticFilled c,
      (z:ℂ) ∈ Q ↔ q z ∈ A)
    (ha : a ∈ LoopsStationaryFiberDynamics.quadraticFilled c \ Q) :
    -a ∉ connectedComponentIn
      (LoopsStationaryFiberDynamics.quadraticFilled c \ Q) a := by
  intro hb
  have hi := quadratic_filled_no_bypass_of_saturated_model c b p Q
    (connectedComponentIn (LoopsStationaryFiberDynamics.quadraticFilled c \ Q) a)
    hQsym hzero hQ hbQ hper hmul q hq hsurj hf A hA hsat
    isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
  have he : a = -a := hi (mem_connectedComponentIn ha) hb (by ring)
  have haz : a = 0 := by linear_combination (1/2 : ℂ) * he
  exact ha.2 (haz.symm ▸ hzero)

/-- A directly testable relative-frontier condition supplies the
saturation needed by the preceding separator theorem. Singleton
fibers are required only on the boundary of the deleted set relative
to the physical filled Julia carrier. -/
theorem quadratic_filled_separator_of_frontier_singletons
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [LocallyConnectedSpace Y]
    (c a b : ℂ) (p : ℕ) (Q : Set ℂ)
    (hQc : IsClosed Q) (hQsym : ∀ z ∈ Q, -z ∈ Q) (hzero : 0 ∈ Q)
    (hQ : IsPreconnected Q) (hbQ : b ∈ Q)
    (hper : QuadraticEscape.orbit c p b = b)
    (hmul : 1 < ‖deriv (QuadraticEscape.orbit c p) b‖)
    (q : LoopsStationaryFiberDynamics.quadraticFilled c → Y)
    (hq : Continuous q) (hsurj : Function.Surjective q)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (hfront : ∀ z ∈ frontier ((Subtype.val :
      LoopsStationaryFiberDynamics.quadraticFilled c → ℂ) ⁻¹' Q),
      q ⁻¹' ({q z} : Set Y) = {z})
    (ha : a ∈ LoopsStationaryFiberDynamics.quadraticFilled c \ Q) :
    -a ∉ connectedComponentIn
      (LoopsStationaryFiberDynamics.quadraticFilled c \ Q) a := by
  let K := LoopsStationaryFiberDynamics.quadraticFilled c
  letI : CompactSpace K :=
    isCompact_iff_compactSpace.mp (LoopsStationaryFiberDynamics.quadratic_filled_compact c)
  let S : Set K := (Subtype.val : K → ℂ) ⁻¹' Q
  have hS : IsClosed S := hQc.preimage continuous_subtype_val
  have hSat : q ⁻¹' (q '' S) = S :=
    LoopsStationaryGeometricFibers.closed_carrier_saturated_of_frontier_singletons
      q hf S hS hfront
  have hA : IsClosed (q '' S) := hq.isClosedMap S hS
  have hsat (z : K) : (z:ℂ) ∈ Q ↔ q z ∈ q '' S := by
    change z ∈ S ↔ z ∈ q ⁻¹' (q '' S)
    rw [hSat]
  exact quadratic_filled_separator_of_saturated_model c a b p Q
    hQsym hzero hQ hbQ hper hmul q hq hsurj hf (q '' S) hA hsat ha

end LoopsStationaryCompactContact
