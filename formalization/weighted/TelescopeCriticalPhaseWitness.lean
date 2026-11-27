import TelescopeCriticalPhase

/-!
# Physical critical encounters defeat both endpoint phase marks

Every actual one-critical return contains a target path with precisely two
critical-value encounters and two distinct complete continuous source lifts
which agree on both outer thirds of the time interval. Both source lifts
and the target path are closed loops, based at regular points. The construction is
inside the given physical return source, not a replacement squaring model.
-/

namespace LoopsTelescopeCriticalPhaseWitness

open Set Function
open QuadraticEscape LoopsSaturatedTelescope
open LoopsTelescopeDeckInvolution LoopsTelescopeCriticalPhase LoopsCriticalPhase

noncomputable section

/-- Even both marked endpoint phases do not determine the interior route
of a physical return path through its branch value. The two lifts below
agree on entire initial and final intervals, differ in between, and the
common target path encounters the propagated critical value exactly twice. -/
theorem quadratic_return_two_crossing_same_endpoints
    (c : ℂ) (a b : ℕ) (A B D : Set ℂ) (hc : c ∈ D) (hA : IsOpen A)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hponto : orbit c a '' A = B)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ∃ γ Γ₀ Γ₁ : C(unitInterval, ℂ),
      (∀ t, Γ₀ t ∈ A ∧ Γ₁ t ∈ A) ∧
      (∀ t, orbit c (a+1+b) (Γ₀ t) = γ t ∧
        orbit c (a+1+b) (Γ₁ t) = γ t) ∧
      (∀ t, ((t : ℝ) ≤ 1/3 ∨ 2/3 ≤ (t : ℝ)) → Γ₁ t = Γ₀ t) ∧
      Γ₁ 0 = Γ₀ 0 ∧ Γ₁ 1 = Γ₀ 1 ∧ Γ₁ ≠ Γ₀ ∧
      (∀ t, γ t = orbit c b c ↔ (t : ℝ) = 1/3 ∨ (t : ℝ) = 2/3) ∧
      Γ₀ 0 = Γ₀ 1 ∧ γ 0 = γ 1 ∧ γ 0 ≠ orbit c b c := by
  classical
  have h0 : (0 : ℂ) ∈ B := by
    rw [hB]
    exact mem_connectedComponentIn (by simpa using hc)
  have h0image : (0 : ℂ) ∈ orbit c a '' A := hponto.symm ▸ h0
  obtain ⟨x, hx, hx0⟩ := h0image
  obtain ⟨τ, hτan, hτmap, _, _, hτfixed, hτfiber, _, _⟩ :=
    quadratic_return_analytic_involution c a b A B D hc hA hB hponto hpinj hrinj
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hA x hx
  let δ : ℝ := ε/2
  have hδ : 0 < δ := half_pos hε
  let p : unitInterval → ℝ := fun t => δ * ((t : ℝ)-1/3) * ((t : ℝ)-2/3)
  have hp : Continuous p := by dsimp [p]; fun_prop
  let Γ₀ : C(unitInterval, ℂ) :=
    ⟨fun t => x + (p t : ℂ), continuous_const.add (Complex.continuous_ofReal.comp hp)⟩
  have hΓ₀ (t : unitInterval) : Γ₀ t ∈ A := by
    have hleft : |(t : ℝ)-1/3| ≤ 1 := abs_le.mpr ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
    have hright : |(t : ℝ)-2/3| ≤ 1 := abs_le.mpr ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
    have hbound : |p t| ≤ δ := by
      calc
        |p t| = δ * |(t : ℝ)-1/3| * |(t : ℝ)-2/3| := by
          dsimp [p]
          rw [abs_mul, abs_mul, abs_of_pos hδ]
        _ ≤ δ * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hleft hδ.le) hright
            (abs_nonneg _) (by positivity)
        _ = δ := by ring
    apply hball
    have hdist : dist (Γ₀ t) x = |p t| := by
      change dist (x + (p t : ℂ)) x = |p t|
      simp [dist_eq_norm]
    rw [Metric.mem_ball, hdist]
    exact hbound.trans_lt (by dsimp [δ]; linarith)
  have hzero (t : unitInterval) :
      Γ₀ t = x ↔ (t : ℝ) = 1/3 ∨ (t : ℝ) = 2/3 := by
    change x + (p t : ℂ) = x ↔ _
    simp [p, mul_eq_zero, ne_of_gt hδ, sub_eq_zero]
  have hprefix (t : unitInterval) : orbit c a (Γ₀ t) = 0 ↔ Γ₀ t = x := by
    constructor
    · intro hz
      exact hpinj (hΓ₀ t) hx (hz.trans hx0.symm)
    · intro hz
      rw [hz]
      exact hx0
  have hregular (t : unitInterval) :
      τ (Γ₀ t) ≠ Γ₀ t ↔ (t : ℝ) ≠ 1/3 ∧ (t : ℝ) ≠ 2/3 := by
    simpa only [not_or] using
      not_congr (((hτfixed (Γ₀ t) (hΓ₀ t)).trans (hprefix t)).trans (hzero t))
  let S : Set unitInterval := {t | (1/3 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 2/3}
  have hS : IsOpen S :=
    (isOpen_lt continuous_const continuous_subtype_val).inter
      (isOpen_lt continuous_subtype_val continuous_const)
  have hother_eq : {t | τ (Γ₀ t) ≠ Γ₀ t} \ S =
      {t | (t : ℝ) < 1/3} ∪ {t | (2/3 : ℝ) < (t : ℝ)} := by
    ext t
    simp only [mem_diff, mem_setOf_eq, mem_union, hregular]
    change ((t : ℝ) ≠ 1/3 ∧ (t : ℝ) ≠ 2/3) ∧
      ¬((1/3 : ℝ) < (t : ℝ) ∧ (t : ℝ) < 2/3) ↔ _
    constructor
    · rintro ⟨⟨hl, hr⟩, hout⟩
      rcases lt_or_gt_of_ne hl with hl | hl
      · exact Or.inl hl
      · rcases lt_or_gt_of_ne hr with hr | hr
        · exact (hout ⟨hl, hr⟩).elim
        · exact Or.inr hr
    · rintro (hl | hr)
      · refine ⟨⟨ne_of_lt hl, ne_of_lt (hl.trans (by norm_num))⟩, ?_⟩
        intro h
        exact lt_asymm hl h.1
      · refine ⟨⟨ne_of_gt ((by norm_num : (1/3 : ℝ) < 2/3).trans hr), ne_of_gt hr⟩, ?_⟩
        intro h
        exact lt_asymm hr h.2
  have hother : IsOpen ({t | τ (Γ₀ t) ≠ Γ₀ t} \ S) := by
    rw [hother_eq]
    exact (isOpen_lt continuous_subtype_val continuous_const).union
      (isOpen_lt continuous_const continuous_subtype_val)
  have hτΓ₀ : Continuous (fun t => τ (Γ₀ t)) :=
    hτan.continuousOn.comp_continuous Γ₀.continuous hΓ₀
  let Γ₁ : C(unitInterval, ℂ) :=
    ⟨phaseSelect (fun t => τ (Γ₀ t)) Γ₀ S,
      continuous_phaseSelect _ _ S hτΓ₀ Γ₀.continuous hS hother⟩
  let γ : C(unitInterval, ℂ) :=
    ⟨fun t => orbit c (a+1+b) (Γ₀ t),
      (quadratic_orbit_continuous c (a+1+b)).comp Γ₀.continuous⟩
  have hΓ₁ (t : unitInterval) : Γ₁ t ∈ A := by
    rcases phaseSelect_choice (fun t => τ (Γ₀ t)) Γ₀ S t with h | h
    · change phaseSelect _ _ S t ∈ A
      rw [h]
      exact hτmap (hΓ₀ t)
    · change phaseSelect _ _ S t ∈ A
      rw [h]
      exact hΓ₀ t
  have hlift (t : unitInterval) : orbit c (a+1+b) (Γ₁ t) = γ t := by
    change orbit c (a+1+b) (Γ₁ t) = orbit c (a+1+b) (Γ₀ t)
    apply (hτfiber (Γ₀ t) (hΓ₀ t) (Γ₁ t) (hΓ₁ t)).mpr
    rcases phaseSelect_choice (fun t => τ (Γ₀ t)) Γ₀ S t with h | h
    · exact Or.inr h
    · exact Or.inl h
  have houtside (t : unitInterval)
      (ht : (t : ℝ) ≤ 1/3 ∨ 2/3 ≤ (t : ℝ)) : Γ₁ t = Γ₀ t := by
    have htS : t ∉ S := by
      intro hs
      rcases ht with ht | ht
      · exact (not_lt_of_ge ht) hs.1
      · exact (not_lt_of_ge ht) hs.2
    exact phaseSelect_of_not_mem _ _ S htS
  let mid : unitInterval := ⟨1/2, by constructor <;> norm_num⟩
  have hmidS : mid ∈ S := by norm_num [S, mid]
  have hmidreg : τ (Γ₀ mid) ≠ Γ₀ mid := (hregular mid).mpr (by norm_num [mid])
  have hne : Γ₁ ≠ Γ₀ := by
    intro he
    have h := congrArg (fun q : C(unitInterval, ℂ) => q mid) he
    change phaseSelect (fun t => τ (Γ₀ t)) Γ₀ S mid = Γ₀ mid at h
    rw [phaseSelect_of_mem _ _ S hmidS] at h
    exact hmidreg h
  have hexact (t : unitInterval) :
      γ t = orbit c b c ↔ (t : ℝ) = 1/3 ∨ (t : ℝ) = 2/3 := by
    change orbit c (a+1+b) (Γ₀ t) = orbit c b c ↔ _
    exact ((quadratic_return_critical_value_iff c a b A B D hc hB hponto hrinj
      (Γ₀ t) (hΓ₀ t)).trans (hprefix t)).trans (hzero t)
  have hpends : p 0 = p 1 := by norm_num [p] <;> ring
  have hclosed : Γ₀ 0 = Γ₀ 1 := by
    change x + (p 0 : ℂ) = x + (p 1 : ℂ)
    rw [hpends]
  have hγclosed : γ 0 = γ 1 := congrArg (orbit c (a+1+b)) hclosed
  have hγregular : γ 0 ≠ orbit c b c := by
    intro h
    have hz := (hexact 0).mp h
    norm_num at hz
  exact ⟨γ, Γ₀, Γ₁, (fun t => ⟨hΓ₀ t, hΓ₁ t⟩),
    (fun t => ⟨rfl, hlift t⟩), houtside,
    houtside 0 (Or.inl (by norm_num)), houtside 1 (Or.inr (by norm_num)), hne,
    hexact, hclosed, hγclosed, hγregular⟩

end

end LoopsTelescopeCriticalPhaseWitness
