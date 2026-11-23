import ParabolicRealSheet
import ParabolicComplexPullback
import ParabolicSegment

/-!
# A full inverse-image component for the complex polynomial

The intermediate signs select an actual open subset of the complex plane.
On this neighborhood the complete pullback of the real segment is precisely
that segment. This gives the component hypothesis in Theorem B of
Blokh, Oversteegen, Ptacek and Timorin.
-/
namespace LoopsParabolic
open Set Function
noncomputable section

private theorem interval_sheet {t e x : ℝ} {k : ℕ} (hs : Shot k t e) (hx : x ∈ Icc (-e) e) :
    sameSheet (-7/4+t) (3*(k+2)) (x:ℂ) 0 := by
  intro j hj hlt
  rw [← Complex.ofReal_zero]
  simpa only [cquad_iterate_ofReal,Complex.ofReal_re] using phase_sign_agrees hs hx hj hlt

theorem complex_segment_invariant {t e : ℝ} {k : ℕ} (hs : Shot k t e) :
    (cquad (-7/4+t))^[3*(k+2)] '' realSegment e = realSegment e := by
  ext z
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨_,return_mem hs hx,(cquad_iterate_ofReal _ _ _).symm⟩
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨x,hx,hxy⟩ := (return_image_eq hs).symm ▸ hy
    exact ⟨(x:ℂ),⟨x,hx,rfl⟩,by rw [cquad_iterate_ofReal,hxy]⟩

private theorem segment_neg {e : ℝ} {z : ℂ} (hz : z ∈ realSegment e) :
    -z ∈ realSegment e := by
  obtain ⟨x,hx,rfl⟩ := hz
  exact ⟨-x,⟨by linarith [hx.2],by linarith [hx.1]⟩,Complex.ofReal_neg _⟩

/-- Isolation in the full complex inverse image, with a specified open set. -/
theorem open_complex_isolation {t e : ℝ} {k : ℕ} (hs : Shot k t e) :
    let c := -7/4+t
    let p := 3*(k+2)
    let U := {z : ℂ | sameSheet c p z 0}
    IsOpen U ∧ realSegment e ⊆ U ∧ U ∩ ((cquad c)^[p] ⁻¹' realSegment e) = realSegment e := by
  intro c p U
  have incl : realSegment e ⊆ U := by
    rintro _ ⟨x,hx,rfl⟩
    exact interval_sheet hs hx
  refine ⟨isOpen_sameSheet _ _ _, incl, subset_antisymm ?_ ?_⟩
  · rintro z ⟨hz,hout⟩
    obtain ⟨x,hx,heq⟩ := (complex_segment_invariant hs).symm ▸ hout
    have common : sameSheet c p z x := by
      intro j hj hlt
      have h₁ := hz j hj hlt
      have h₂ := incl hx j hj hlt
      rcases mul_pos_iff.mp h₁ with h | h <;> rcases mul_pos_iff.mp h₂ with h' | h'
      · exact mul_pos h.1 h'.1
      · linarith [h.2,h'.2]
      · linarith [h.2,h'.2]
      · exact mul_pos_of_neg_of_neg h.1 h'.1
    rcases sameSheet_pullback (by dsimp [p]; omega) common heq.symm with h | h
    · exact h ▸ hx
    · exact h ▸ segment_neg hx
  · intro z hz
    exact ⟨incl hz,(complex_segment_invariant hs) ▸ (mem_image_of_mem _ hz)⟩

/-- Every interior real value has exactly two distinct preimages on the
isolating neighborhood. Both lie on the physical interval. -/
theorem interior_complex_fiber {t e w : ℝ} {k : ℕ} (hs : Shot k t e) (hw : w ∈ Ioo (-e) e) :
    let c := -7/4+t
    let p := 3*(k+2)
    ∃ x ∈ Ioo 0 e, ∀ z : ℂ, sameSheet c p z 0 →
      ((cquad c)^[p] z = (w:ℂ) ↔ z = (x:ℂ) ∨ z = -(x:ℂ)) := by
  intro c p
  obtain ⟨x,hx,hxw⟩ := (full_branches hs).2.2.2.symm ▸ (Ioo_subset_Icc_self hw)
  have hpor : 0 < p := by dsimp [p]; omega
  have h₀ : (quad c)^[p] 0 = -e := by
    simpa [c,p,hs.critical] using reflected_blocks t 0 (k+2)
  have he : (quad c)^[p] e = e :=
    (exact_period_of_shot ⟨hs.t_pos.le,hs.t_small⟩ hs.e_pos hs.e_small hs.corridor
      hs.penultimate hs.collision).1
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (by
    intro h; subst x; change (quad c)^[p] 0 = w at hxw; linarith [hw.1])
  have hxlt : x < e := lt_of_le_of_ne hx.2 (by
    intro h; subst x; change (quad c)^[p] e = w at hxw; linarith [hw.2])
  have hxc : (cquad c)^[p] (x:ℂ) = w := by rw [cquad_iterate_ofReal,hxw]
  have hxc' : (cquad c)^[p] (-(x:ℂ)) = w := by
    rw [← Complex.ofReal_neg,cquad_iterate_ofReal,← positive_iterates_even c x hpor,hxw]
  have hxs := interval_sheet hs (show x ∈ Icc (-e) e from ⟨by linarith [hs.e_pos],hx.2⟩)
  refine ⟨x,⟨hxpos,hxlt⟩,?_⟩
  intro z hz
  constructor
  · intro hzw
    apply sameSheet_pullback hpor _ (hzw.trans hxc.symm)
    intro j hj hlt
    have a := hz j hj hlt
    have b := hxs j hj hlt
    change 0 < ((cquad c)^[j] (x:ℂ)).re * ((cquad c)^[j] 0).re at b
    rcases mul_pos_iff.mp a with ha | ha <;> rcases mul_pos_iff.mp b with hb | hb
    · exact mul_pos ha.1 hb.1
    · linarith [ha.2,hb.2]
    · linarith [ha.2,hb.2]
    · exact mul_pos_of_neg_of_neg ha.1 hb.1
  · rintro (rfl | rfl)
    · exact hxc
    · exact hxc'

private theorem component_of_open_cut {X : Type*} [TopologicalSpace X]
    {A U B : Set X} {x : X} (hA : IsClosed A) (hconn : IsPreconnected A) (hx : x ∈ A)
    (hU : IsOpen U) (hcut : U ∩ B = A) : connectedComponentIn B x = A := by
  have hB : A ⊆ B := hcut ▸ inter_subset_right
  have hAU : A ⊆ U := hcut ▸ inter_subset_left
  have member := mem_connectedComponentIn (hB hx)
  refine subset_antisymm ?_ (hconn.subset_connectedComponentIn hx hB)
  intro z hz
  by_contra hnot
  let C := connectedComponentIn B x
  have hcover : C ⊆ U ∪ Aᶜ := by
    intro w hw
    by_cases h : w ∈ A
    · exact Or.inl (hAU h)
    · exact Or.inr h
  obtain ⟨w,hw,hwu,hwa⟩ := isPreconnected_connectedComponentIn U Aᶜ hU hA.isOpen_compl
    hcover ⟨x,member,hAU hx⟩ ⟨z,hz,hnot⟩
  exact hwa (hcut ▸ (show w ∈ U ∩ B from ⟨hwu,connectedComponentIn_subset _ _ hw⟩))

/-- The embedded interval is the connected component containing zero of the
entire complex preimage, and has a connected complement. -/
theorem complex_pullback_component {t e : ℝ} {k : ℕ} (hs : Shot k t e) :
    connectedComponentIn ((cquad (-7/4+t))^[3*(k+2)] ⁻¹' realSegment e) 0 = realSegment e := by
  have hi := open_complex_isolation hs
  exact component_of_open_cut (realSegment_compact e).isClosed
    (realSegment_connected hs.e_pos.le).2
    ⟨0,⟨by linarith [hs.e_pos],hs.e_pos.le⟩,Complex.ofReal_zero⟩ hi.1 hi.2.2

/-- Algebraic identification of the monic centered straightening parameter
from its exact critical portrait, whenever a straightening is supplied. -/
theorem straightening_parameter {d : ℂ} (hd : d ≠ 0)
    (h : (d^2+d)^2+d = d^2+d) : d = -2 := by
  have eqn : d^3*(d+2) = 0 := by linear_combination h
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp eqn).resolve_left (pow_ne_zero _ hd))

end
end LoopsParabolic
