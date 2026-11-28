import MarkedSlitTransport
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The left relative class crosses the left real cut

A relative homotopy in the complement of the marked slit remembers which
side of the slit a parent arc passes. A continuous logarithm about the left
endpoint, lifted along the homotopy, detects that side without regularity
or finite-length assumptions on the arc.
-/

namespace SlitLeftCrossing

open Set MarkedSlitTransport
open scoped Topology

noncomputable section

private theorem parameter_zero_or_one_or_interior (t : Parameter) :
    t = initial ∨ t = terminal ∨ t ∈ parameterInterior := by
  by_cases h0 : (t : ℝ) = 0
  · exact Or.inl (Subtype.ext h0)
  by_cases h1 : (t : ℝ) = 1
  · exact Or.inr (Or.inl (Subtype.ext h1))
  exact Or.inr (Or.inr ⟨lt_of_le_of_ne t.property.1 (Ne.symm h0),
    lt_of_le_of_ne t.property.2 h1⟩)

private theorem reference_no_zero_endpoint_log {left : ℝ} {η : Curve}
    (hη : LeftReference left η) (g : Curve)
    (hg : ∀ t, Complex.exp (g t) = η t - (left : ℂ))
    (h0 : (g initial).im = 0) (h1 : (g terminal).im = 0) : False := by
  let f : Parameter → ℝ := fun t => (g t).im
  have hfc : Continuous f := Complex.continuous_im.comp g.continuous
  have hf0 : f initial = 0 := h0
  have hf1 : f terminal = 0 := h1
  have hmle : f middle ≤ 0 := by
    by_contra hn
    have hm : 0 < f middle := lt_of_not_ge hn
    let y : ℝ := min (f middle / 2) (Real.pi / 2)
    have hy0 : 0 < y := lt_min (by positivity) (by positivity)
    have hym : y < f middle := (min_le_left _ _).trans_lt (by linarith)
    have hyp : y < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc
      (a := initial) (b := middle)
      (show initial ≤ middle by change (0 : ℝ) ≤ 1/2; norm_num)
      hfc.continuousOn (show y ∈ Icc (f initial) (f middle) by
        rw [hf0]; exact ⟨hy0.le, hym.le⟩)
    have ht0 : 0 < (t : ℝ) := by
      have htle : (0 : ℝ) ≤ t := t.property.1
      by_contra hn
      have heq : t = initial := Subtype.ext (le_antisymm (not_lt.mp hn) htle)
      rw [heq, hf0] at hft
      linarith
    have htm : (t : ℝ) < 1/2 := by
      have htlem : (t : ℝ) ≤ 1/2 := ht.2
      by_contra hn
      have heq : t = middle := Subtype.ext (le_antisymm htlem (not_lt.mp hn))
      rw [heq] at hft
      linarith
    have hs : 0 < Real.sin (f t) := by
      rw [hft]
      exact Real.sin_pos_of_pos_of_lt_pi hy0 hyp
    have he := congrArg Complex.im (hg t)
    simp only [Complex.exp_im, Complex.sub_im, Complex.ofReal_im, sub_zero] at he
    have hp : 0 < (η t).im := by
      rw [← he]
      exact mul_pos (Real.exp_pos _) hs
    exact (not_lt_of_ge hp.le) (hη.below t ht0 htm)
  have hmge : 0 ≤ f middle := by
    by_contra hn
    have hm : f middle < 0 := lt_of_not_ge hn
    let y : ℝ := -min (-f middle / 2) (Real.pi / 2)
    have hy0 : y < 0 := neg_neg_of_pos (lt_min (by linarith) (by positivity))
    have hym : f middle < y := by
      have hh := min_le_left (-f middle / 2) (Real.pi / 2)
      dsimp [y]
      linarith
    have hyp : -Real.pi < y := by
      have hh := min_le_right (-f middle / 2) (Real.pi / 2)
      dsimp [y]
      linarith [Real.pi_pos]
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc
      (a := middle) (b := terminal)
      (show middle ≤ terminal by change (1/2 : ℝ) ≤ 1; norm_num)
      hfc.continuousOn (show y ∈ Icc (f middle) (f terminal) by
        rw [hf1]; exact ⟨hym.le, hy0.le⟩)
    have htm : 1/2 < (t : ℝ) := by
      have htlem : (1/2 : ℝ) ≤ t := ht.1
      by_contra hn
      have heq : t = middle := Subtype.ext (le_antisymm (not_lt.mp hn) htlem)
      rw [heq] at hft
      linarith
    have ht1 : (t : ℝ) < 1 := by
      have htle : (t : ℝ) ≤ 1 := t.property.2
      by_contra hn
      have heq : t = terminal := Subtype.ext (le_antisymm htle (not_lt.mp hn))
      rw [heq, hf1] at hft
      linarith
    have hs : Real.sin (f t) < 0 := by
      rw [hft]
      exact Real.sin_neg_of_neg_of_neg_pi_lt hy0 hyp
    have he := congrArg Complex.im (hg t)
    simp only [Complex.exp_im, Complex.sub_im, Complex.ofReal_im, sub_zero] at he
    have hp : (η t).im < 0 := by
      rw [← he]
      exact mul_neg_of_pos_of_neg (Real.exp_pos _) hs
    exact (not_lt_of_ge (hη.above t htm ht1).le) hp
  have hm0 : (g middle).im = 0 := le_antisymm hmle hmge
  have he := congrArg Complex.re (hg middle)
  simp only [Complex.exp_re, hm0, Real.cos_zero, mul_one, Complex.sub_re,
    Complex.ofReal_re] at he
  have hp := Real.exp_pos (g middle).re
  linarith [hη.crossing_re]

/-- Every member of the actual left relative class meets the real cut
strictly to the left of the slit. The ambient domain and arc length play
no role in this homotopy invariant. -/
theorem parentLeaf_exists_left_real {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) :
    ∃ t ∈ parameterInterior, (γ t).im = 0 ∧ (γ t).re < M.left := by
  by_contra hcross
  have hLR : M.left < M.right :=
    M.left_lt_first.trans (M.first_lt_second.trans M.second_lt_right)
  have hi : M.left < (γ initial).re := M.left_lt_first.trans hγ.first_end.2.1
  have ht : M.left < (γ terminal).re := M.left_lt_first.trans hγ.last_end.2.1
  have hmem (t : Parameter) : γ t - (M.left : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases him : (γ t).im = 0
    · left
      simp only [Complex.sub_re, Complex.ofReal_re]
      rcases parameter_zero_or_one_or_interior t with rfl | rfl | hti
      · exact sub_pos.mpr hi
      · exact sub_pos.mpr ht
      · have hnlt : ¬ (γ t).re < M.left := fun h => hcross ⟨t, hti, him, h⟩
        have hright : M.right < (γ t).re := by
          by_contra hn
          exact hγ.avoids t hti ⟨him, not_lt.mp hnlt, not_lt.mp hn⟩
        exact sub_pos.mpr (hLR.trans hright)
    · right
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using him
  obtain ⟨η, hη, F, hF0, hF1, hFi, hFt, hFav⟩ := hγ.left_class
  have hFne (p : Parameter × Parameter) : F p - (M.left : ℂ) ≠ 0 := by
    intro he
    have hv : F p = (M.left : ℂ) := sub_eq_zero.mp he
    rcases parameter_zero_or_one_or_interior p.2 with hp | hp | hp
    · have he' : γ initial = (M.left : ℂ) := by
        calc
          γ initial = F (p.1,initial) := (hFi p.1).symm
          _ = F p := by rw [← hp]
          _ = _ := hv
      have hh := congrArg Complex.re he'
      simp only [Complex.ofReal_re] at hh
      linarith
    · have he' : γ terminal = (M.left : ℂ) := by
        calc
          γ terminal = F (p.1,terminal) := (hFt p.1).symm
          _ = F p := by rw [← hp]
          _ = _ := hv
      have hh := congrArg Complex.re he'
      simp only [Complex.ofReal_re] at hh
      linarith
    · apply hFav p.1 p.2 hp
      change (F p).im = 0 ∧ M.left ≤ (F p).re ∧ (F p).re ≤ M.right
      rw [hv]
      exact ⟨rfl, le_rfl, hLR.le⟩
  let H : C(Parameter × Parameter, {z : ℂ // z ≠ 0}) :=
    ⟨fun p => ⟨F p - (M.left : ℂ), hFne p⟩,
      (F.continuous.sub continuous_const).subtype_mk _⟩
  let g0 : Curve := ⟨fun t => Complex.log (γ t - (M.left : ℂ)),
    (γ.continuous.sub continuous_const).clog hmem⟩
  have hH0 (t : Parameter) : H (0,t) =
      (⟨Complex.exp (g0 t), Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) := by
    apply Subtype.ext
    change F (initial,t) - (M.left : ℂ) = Complex.exp (Complex.log (γ t - (M.left : ℂ)))
    rw [hF0, Complex.exp_log (Complex.slitPlane_ne_zero (hmem t))]
  let L := Complex.isCoveringMap_exp.liftHomotopy H g0 hH0
  have hLexp (p : Parameter × Parameter) :
      Complex.exp (L p) = F p - (M.left : ℂ) :=
    congrArg Subtype.val
      (congrFun (Complex.isCoveringMap_exp.liftHomotopy_lifts H g0 hH0) p)
  have hL0 (t : Parameter) : L (initial,t) = g0 t :=
    Complex.isCoveringMap_exp.liftHomotopy_zero H g0 hH0 t
  have hLend (t : Parameter) (hfixed : ∀ s, F (s,t) = γ t) :
      L (terminal,t) = g0 t := by
    apply Eq.trans _ (hL0 t)
    apply Complex.isCoveringMap_exp.const_of_comp
      (g := fun s : Parameter => L (s,t))
      (L.continuous.comp (continuous_id.prodMk continuous_const))
    intro s u
    apply Subtype.ext
    change Complex.exp (L (s,t)) = Complex.exp (L (u,t))
    rw [hLexp, hLexp, hfixed, hfixed]
  have hg0im (t : Parameter) (him : (γ t).im = 0)
      (hre : M.left < (γ t).re) : (g0 t).im = 0 := by
    have hz : γ t - (M.left : ℂ) = (((γ t).re - M.left : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    change (Complex.log (γ t - (M.left : ℂ))).im = 0
    rw [hz, ← Complex.ofReal_log (sub_pos.mpr hre).le]
    rfl
  let g : Curve := ⟨fun t => L (terminal,t),
    L.continuous.comp (continuous_const.prodMk continuous_id)⟩
  apply reference_no_zero_endpoint_log hη g
  · intro t
    exact (hLexp (terminal,t)).trans (by rw [hF1])
  · change (L (terminal,initial)).im = 0
    rw [hLend initial hFi]
    exact hg0im initial hγ.first_end.1 hi
  · change (L (terminal,terminal)).im = 0
    rw [hLend terminal hFt]
    exact hg0im terminal hγ.last_end.1 ht

end
end SlitLeftCrossing
