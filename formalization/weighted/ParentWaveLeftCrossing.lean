import MarkedSlitTransport
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Order.DenselyOrdered

/-!
# The left crossing of every actual parent leaf

The relative homotopy in `ParentLeaf` forces the left crossing.  The
proof lifts the homotopy through the complex square map and detects the
opposite signs at the two ends of a left reference arc.
-/

namespace ParentWaveLeftCrossing

open Set Function
open MarkedSlitTransport

private theorem parameter_cases (t : Parameter) :
    t = initial ∨ t = terminal ∨ t ∈ parameterInterior := by
  by_cases h0 : (t : ℝ) = 0
  · exact Or.inl (Subtype.ext h0)
  by_cases h1 : (t : ℝ) = 1
  · exact Or.inr (Or.inl (Subtype.ext h1))
  exact Or.inr (Or.inr ⟨lt_of_le_of_ne t.property.1 (Ne.symm h0),
    lt_of_le_of_ne t.property.2 h1⟩)

private theorem continuous_sign {X : Type*} [TopologicalSpace X]
    (S : Set X) (hS : IsPreconnected S) (f : X → ℝ)
    (hf : ContinuousOn f S) (hn : ∀ x ∈ S, f x ≠ 0)
    {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    0 < f x ↔ 0 < f y := by
  have step {x y : X} (hx : x ∈ S) (hy : y ∈ S) (hp : 0 < f x) :
      0 < f y := by
    by_contra h
    have hneg : f y < 0 := lt_of_le_of_ne (le_of_not_gt h) (hn y hy)
    obtain ⟨z,hz,he⟩ := hS.intermediate_value hy hx hf ⟨hneg.le,hp.le⟩
    exact hn z hz he
  exact ⟨step hx hy, step hy hx⟩

private theorem initial_mem_closure_first :
    initial ∈ closure (Ioo initial middle : Set Parameter) := by
  rw [closure_Ioo (by
    intro h
    have h' := congrArg (fun t : Parameter => (t : ℝ)) h
    norm_num [initial, middle] at h' : initial ≠ middle)]
  constructor
  · exact le_rfl
  · norm_num [initial,middle]

private theorem terminal_mem_closure_second :
    terminal ∈ closure (Ioo middle terminal : Set Parameter) := by
  rw [closure_Ioo (by
    intro h
    have h' := congrArg (fun t : Parameter => (t : ℝ)) h
    norm_num [middle, terminal] at h' : middle ≠ terminal)]
  constructor
  · change (1 / 2 : ℝ) ≤ 1
    norm_num
  · exact le_rfl

private theorem reference_root_signs {a : ℝ} {η : Curve}
    (hη : LeftReference a η)
    (hfirst : (η initial).im = 0 ∧ a < (η initial).re)
    (hlast : (η terminal).im = 0 ∧ a < (η terminal).re)
    (r : Parameter → ℂ) (hr : Continuous r)
    (hsq : ∀ t, r t ^ 2 = η t - (a : ℂ)) :
    ¬ ((0 < (r initial).re) ↔ (0 < (r terminal).re)) := by
  have hre (t : Parameter) :
      (r t).re ^ 2 - (r t).im ^ 2 = (η t).re-a := by
    have h := congrArg Complex.re (hsq t)
    simpa [pow_two,Complex.mul_re] using h
  have him (t : Parameter) :
      2*(r t).re*(r t).im = (η t).im := by
    have h := congrArg Complex.im (hsq t)
    simp only [pow_two,Complex.mul_im,Complex.sub_im,Complex.ofReal_im,sub_zero] at h
    nlinarith
  have hend (t : Parameter) (ht : (η t).im = 0 ∧ a < (η t).re) :
      (r t).re ≠ 0 := by
    intro h
    have hh := hre t
    rw [h] at hh
    nlinarith [sq_nonneg (r t).im]
  have hn : ∀ t ∈ parameterInterior, (r t).im ≠ 0 := by
    intro t ht he
    have hz : (η t).im = 0 := by simpa [he] using (him t).symm
    rcases lt_trichotomy (t : ℝ) (1/2) with h | h | h
    · exact (ne_of_lt (hη.below t ht.1 h)) hz
    · have hm : t = middle := Subtype.ext h
      subst t
      have hh := hre middle
      rw [he] at hh
      nlinarith [hη.crossing_re,sq_nonneg (r middle).re]
    · exact (ne_of_gt (hη.above t h ht.2)) hz
  have hpc : IsPreconnected parameterInterior := by
    change IsPreconnected (Ioo initial terminal)
    exact isPreconnected_Ioo
  have hm : middle ∈ parameterInterior := by
    change (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1
    norm_num
  have hsign (t : Parameter) (ht : t ∈ parameterInterior) :
      0 < (r t).im ↔ 0 < (r middle).im :=
    continuous_sign parameterInterior hpc (fun t => (r t).im)
      (Complex.continuous_im.comp hr).continuousOn hn ht hm
  have hfirst_ne := hend initial hfirst
  have hlast_ne := hend terminal hlast
  by_cases hp : 0 < (r middle).im
  · have hleft : ∀ t ∈ Ioo initial middle, (r t).re ≤ 0 := by
      intro t ht
      have ht' : t ∈ parameterInterior := ⟨ht.1,lt_trans ht.2 (by norm_num [middle,terminal])⟩
      have hi := (hsign t ht').mpr hp
      have hneg := hη.below t ht'.1 ht.2
      have hh := him t
      nlinarith
    have hright : ∀ t ∈ Ioo middle terminal, 0 ≤ (r t).re := by
      intro t ht
      have ht' : t ∈ parameterInterior := ⟨lt_trans (by norm_num [initial,middle]) ht.1,ht.2⟩
      have hi := (hsign t ht').mpr hp
      have hpos := hη.above t ht.1 ht'.2
      have hh := him t
      nlinarith
    have h0 : (r initial).re ≤ 0 :=
      closure_minimal hleft (isClosed_le (Complex.continuous_re.comp hr) continuous_const)
        initial_mem_closure_first
    have h1 : 0 ≤ (r terminal).re :=
      closure_minimal hright (isClosed_le continuous_const (Complex.continuous_re.comp hr))
        terminal_mem_closure_second
    have h1' : 0 < (r terminal).re := lt_of_le_of_ne h1 (Ne.symm hlast_ne)
    exact fun h => not_lt_of_ge h0 (h.mpr h1')
  · have hnmid : (r middle).im < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hn middle hm)
    have hnegative (t : Parameter) (ht : t ∈ parameterInterior) : (r t).im < 0 :=
      lt_of_le_of_ne (le_of_not_gt (fun h => hp ((hsign t ht).mp h))) (hn t ht)
    have hleft : ∀ t ∈ Ioo initial middle, 0 ≤ (r t).re := by
      intro t ht
      have ht' : t ∈ parameterInterior := ⟨ht.1,lt_trans ht.2 (by norm_num [middle,terminal])⟩
      have hi := hnegative t ht'
      have hneg := hη.below t ht'.1 ht.2
      have hh := him t
      nlinarith
    have hright : ∀ t ∈ Ioo middle terminal, (r t).re ≤ 0 := by
      intro t ht
      have ht' : t ∈ parameterInterior := ⟨lt_trans (by norm_num [initial,middle]) ht.1,ht.2⟩
      have hi := hnegative t ht'
      have hpos := hη.above t ht.1 ht'.2
      have hh := him t
      nlinarith
    have h0 : 0 ≤ (r initial).re :=
      closure_minimal hleft (isClosed_le continuous_const (Complex.continuous_re.comp hr))
        initial_mem_closure_first
    have h1 : (r terminal).re ≤ 0 :=
      closure_minimal hright (isClosed_le (Complex.continuous_re.comp hr) continuous_const)
        terminal_mem_closure_second
    have h0' : 0 < (r initial).re := lt_of_le_of_ne h0 (Ne.symm hfirst_ne)
    exact fun h => not_lt_of_ge h1 (h.mp h0')

/-- Every leaf in the actual relative left class crosses the real ray
to the left of the entire slit. The conclusion applies to arbitrary
continuous leaves, without any rectifiability assumption. -/
theorem parentLeaf_exists_left_real {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) :
    ∃ t ∈ parameterInterior, (γ t).im = 0 ∧ (γ t).re < M.left := by
  by_contra hcross
  obtain ⟨η,hη,F,hF0,hF1,hE0,hE1,havoid⟩ := hγ.left_class
  let g : Parameter × Parameter → ℂ := fun p => F p - (M.left : ℂ)
  have hg : Continuous g := F.continuous.sub continuous_const
  have hne : ∀ p, g p ≠ 0 := by
    rintro ⟨s,t⟩ he
    have hFt : F (s,t) = (M.left : ℂ) := sub_eq_zero.mp he
    rcases parameter_cases t with rfl | rfl | ht
    · rw [hE0] at hFt
      have h := congrArg Complex.re hFt
      simp only [Complex.ofReal_re] at h
      linarith [hγ.first_end.2.1,M.left_lt_first]
    · rw [hE1] at hFt
      have h := congrArg Complex.re hFt
      simp only [Complex.ofReal_re] at h
      linarith [hγ.last_end.2.1,M.left_lt_first]
    · apply havoid s t ht
      rw [hFt]
      exact ⟨by simp,le_rfl,le_of_lt (lt_trans M.left_lt_first
        (lt_trans M.first_lt_second M.second_lt_right))⟩
  letI : ContractibleSpace Parameter :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  letI : LocallyPathConnectedSpace
      ((Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) 1)) :=
    ((convex_Icc (0 : ℝ) 1).prod (convex_Icc (0 : ℝ) 1)).locallyPathConnectedSpace
  letI : LocallyPathConnectedSpace (Parameter × Parameter) :=
    (Homeomorph.Set.prod (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)).isQuotientMap.locallyPathConnectedSpace
  have hsc : IsSimplyConnected (univ : Set (Parameter × Parameter)) :=
    (Homeomorph.Set.univ (Parameter × Parameter)).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨r,hr,hsq⟩ := Complex.exists_continuousOn_pow_eq hsc isOpen_univ
    hg.continuousOn (by simpa only [mem_image,mem_univ,true_and,not_exists] using hne)
    (by decide : (2 : ℕ) ≠ 0)
  have hrc : Continuous r := continuousOn_univ.mp hr
  have re_ne_of_positive (s t : Parameter)
      (hp : M.left < (F (s,t)).re) : (r (s,t)).re ≠ 0 := by
    intro hz
    have h := congrArg Complex.re (hsq (s,t))
    change ((r (s,t))^2).re = (F (s,t)-(M.left : ℂ)).re at h
    simp [pow_two,Complex.mul_re,hz] at h
    nlinarith [sq_nonneg (r (s,t)).im]
  have hbottom : ∀ s, (r (s,initial)).re ≠ 0 := by
    intro s
    apply re_ne_of_positive
    rw [hE0]
    exact lt_trans M.left_lt_first hγ.first_end.2.1
  have htop : ∀ s, (r (s,terminal)).re ≠ 0 := by
    intro s
    apply re_ne_of_positive
    rw [hE1]
    exact lt_trans M.left_lt_first hγ.last_end.2.1
  have hleft : ∀ t, (r (initial,t)).re ≠ 0 := by
    intro t hz
    have hh := hsq (initial,t)
    change r (initial,t)^2 = F (initial,t)-(M.left : ℂ) at hh
    rw [hF0] at hh
    have him := congrArg Complex.im hh
    have hre := congrArg Complex.re hh
    simp [pow_two,Complex.mul_im,hz] at him
    simp [pow_two,Complex.mul_re,hz] at hre
    rcases parameter_cases t with rfl | rfl | ht
    · exact hbottom initial hz
    · exact htop initial hz
    · have hle : (γ t).re ≤ M.left := by nlinarith [sq_nonneg (r (initial,t)).im]
      have hlt : (γ t).re < M.left := by
        by_contra h
        have he : (γ t).re = M.left := le_antisymm hle (le_of_not_gt h)
        exact hγ.avoids t ht ⟨him.symm,he.ge,he ▸
          (lt_trans M.left_lt_first (lt_trans M.first_lt_second M.second_lt_right)).le⟩
      exact hcross ⟨t,ht,him.symm,hlt⟩
  have edge_sign (f : Parameter → ℂ) (hf : Continuous f)
      (hn : ∀ t, (f t).re ≠ 0) :
      (0 < (f initial).re) ↔ (0 < (f terminal).re) :=
    continuous_sign univ isPreconnected_univ (fun t => (f t).re)
      (Complex.continuous_re.comp hf).continuousOn (fun t _ => hn t)
      (mem_univ _) (mem_univ _)
  have hb := edge_sign (fun s => r (s,initial))
    (hrc.comp (continuous_id.prodMk continuous_const)) hbottom
  have ht := edge_sign (fun s => r (s,terminal))
    (hrc.comp (continuous_id.prodMk continuous_const)) htop
  have hl := edge_sign (fun t => r (initial,t))
    (hrc.comp (continuous_const.prodMk continuous_id)) hleft
  have href : ¬ ((0 < (r (terminal,initial)).re) ↔
      (0 < (r (terminal,terminal)).re)) := by
    apply reference_root_signs hη (r := fun t => r (terminal,t))
    · have he : η initial = γ initial := (hF1 initial).symm.trans (hE0 terminal)
      rw [he]
      exact ⟨hγ.first_end.1,lt_trans M.left_lt_first hγ.first_end.2.1⟩
    · have he : η terminal = γ terminal := (hF1 terminal).symm.trans (hE1 terminal)
      rw [he]
      exact ⟨hγ.last_end.1,lt_trans M.left_lt_first hγ.last_end.2.1⟩
    · exact hrc.comp (continuous_const.prodMk continuous_id)
    · intro t
      simpa [g,hF1] using hsq (terminal,t)
  exact href (hb.symm.trans (hl.trans ht))

end ParentWaveLeftCrossing
