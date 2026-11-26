import StationarySeparatorTransport

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

end LoopsStationaryCompactContact
