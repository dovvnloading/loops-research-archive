import SlitPairableCalibration
import SlitWaveLimit

/-!
# Geometric pairable parents with two proper source restrictions

Pairability is a statement about two actual temporal subarcs of the
physical parent.  Each has endpoints on the removed source slit, joining
the specified real ports, and its whole open interval lies in the source
minus that slit.  Local bank access specifies the designated lower and
upper children.  The children may make arbitrary excursions in the source;
the parent segment between them may leave it.

This is a geometric class.  It does not postulate an identification with
native ideal-boundary atoms or a canonical arc diagram.  Its supremum is
over all Borel physical parent laminations satisfying the stated temporal
conditions, with no optimizer or regular-foliation hypothesis.
-/

namespace SlitPairableWaves

open Set MeasureTheory Metric Function
open MarkedSlitTransport SlitWaveModulus SlitPotentialLength SlitPairableCalibration
open scoped Topology ENNReal NNReal

noncomputable section

/-- Access to an inner source-slit contact from the lower side. -/
def LowerAccessAt (γ : Curve) (s : Parameter) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ r : Parameter,
    (s : ℝ) - ε < (r : ℝ) → (r : ℝ) < (s : ℝ) → (γ r).im < 0

/-- Access from an inner source-slit contact to the upper side. -/
def UpperAccessAt (γ : Curve) (t : Parameter) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ r : Parameter,
    (t : ℝ) < (r : ℝ) → (r : ℝ) < (t : ℝ) + ε → 0 < (γ r).im

/-- Two designated proper temporal restrictions.  Endpoint contacts are
inside the open source and on its removed slit; the actual open subarcs
avoid that slit.  Distinct parent endpoints and distinct inner contacts
are allowed. -/
structure TemporalPair (V T J₀ J₁ : Set ℂ) (γ : Curve) (s t : Parameter) : Prop where
  first_interior : s ∈ parameterInterior
  last_interior : t ∈ parameterInterior
  ordered : s ≤ t
  initial_contact : γ initial ∈ V ∧ γ initial ∈ T ∧ γ initial ∈ J₁
  terminal_contact : γ terminal ∈ V ∧ γ terminal ∈ T ∧ γ terminal ∈ J₁
  first_contact : γ s ∈ V ∧ γ s ∈ T ∧ γ s ∈ J₀
  last_contact : γ t ∈ V ∧ γ t ∈ T ∧ γ t ∈ J₀
  first_open : ∀ r ∈ Ioo initial s, γ r ∈ V \ T
  last_open : ∀ r ∈ Ioo t terminal, γ r ∈ V \ T
  first_lower : LowerAccessAt γ s
  last_upper : UpperAccessAt γ t

/-- The region on which a common reflected source potential must be
regular.  The rest of the removed source slit, including critical and
electrode endpoints, is excluded. -/
def calibrationRegion (V T J₀ J₁ : Set ℂ) : Set ℂ :=
  {z | z ∈ V ∧ (z ∉ T ∨ z ∈ J₀ ∨ z ∈ J₁)}

theorem TemporalPair.childTraces_subset_region {V T J₀ J₁ : Set ℂ} {γ : Curve}
    {s t : Parameter} (h : TemporalPair V T J₀ J₁ γ s t) :
    childTraces γ s t ⊆ calibrationRegion V T J₀ J₁ := by
  rintro z (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
  · rcases eq_or_lt_of_le hr.1 with he | hfirst
    · subst r
      exact ⟨h.initial_contact.1, Or.inr (Or.inr h.initial_contact.2.2)⟩
    rcases lt_or_eq_of_le hr.2 with hlast | he
    · have hm := h.first_open r ⟨hfirst, hlast⟩
      exact ⟨hm.1, Or.inl hm.2⟩
    · subst r
      exact ⟨h.first_contact.1, Or.inr (Or.inl h.first_contact.2.2)⟩
  · rcases eq_or_lt_of_le hr.1 with he | hfirst
    · subst r
      exact ⟨h.last_contact.1, Or.inr (Or.inl h.last_contact.2.2)⟩
    rcases lt_or_eq_of_le hr.2 with hlast | he
    · have hm := h.last_open r ⟨hfirst, hlast⟩
      exact ⟨hm.1, Or.inl hm.2⟩
    · subst r
      exact ⟨h.terminal_contact.1, Or.inr (Or.inr h.terminal_contact.2.2)⟩

theorem TemporalPair.childTraces_subset_source {V T J₀ J₁ : Set ℂ} {γ : Curve}
    {s t : Parameter} (h : TemporalPair V T J₀ J₁ γ s t) :
    childTraces γ s t ⊆ V := fun _ hz => (h.childTraces_subset_region hz).1

/-- Physical immersion is injective on the union of the two open temporal
children because they are restrictions of the same simple parent.  This
is a theorem about their actual parametrized images. -/
theorem TemporalPair.injOn_open_children {V T J₀ J₁ : Set ℂ} {γ : Curve}
    {s t : Parameter} (h : TemporalPair V T J₀ J₁ γ s t) (hγ : Simple γ) :
    InjOn γ (Ioo initial s ∪ Ioo t terminal) := by
  apply hγ.mono
  intro r hr
  rcases hr with hr | hr
  · exact ⟨hr.1, lt_trans hr.2 h.first_interior.2⟩
  · exact ⟨lt_trans h.last_interior.1 hr.1, hr.2⟩

structure PairableLeaf (M : Marking) (D V T J₀ J₁ : Set ℂ) (γ : Curve) : Prop
    extends ParentLeaf M D γ where
  pair : ∃ s t : Parameter, TemporalPair V T J₀ J₁ γ s t

structure PairableWave (M : Marking) (D V T J₀ J₁ : Set ℂ) (Γ : Set Curve) : Prop
    extends ParentWave M D Γ where
  pair : ∀ γ ∈ Γ, ∃ s t : Parameter, TemporalPair V T J₀ J₁ γ s t

theorem PairableWave.pairable_leaf {M : Marking} {D V T J₀ J₁ : Set ℂ}
    {Γ : Set Curve} (hΓ : PairableWave M D V T J₀ J₁ Γ) {γ : Curve} (hγ : γ ∈ Γ) :
    PairableLeaf M D V T J₀ J₁ γ :=
  { hΓ.leaf γ hγ with pair := hΓ.pair γ hγ }

def width (M : Marking) (D V T J₀ J₁ : Set ℂ) : ℝ≥0∞ :=
  ⨆ (Γ : Set Curve) (_ : PairableWave M D V T J₀ J₁ Γ), modulus (traces Γ)

theorem modulus_le_width {M : Marking} {D V T J₀ J₁ : Set ℂ} {Γ : Set Curve}
    (hΓ : PairableWave M D V T J₀ J₁ Γ) :
    modulus (traces Γ) ≤ width M D V T J₀ J₁ :=
  le_iSup₂_of_le Γ hΓ le_rfl

theorem width_le_parent_width (M : Marking) (D V T J₀ J₁ : Set ℂ) :
    width M D V T J₀ J₁ ≤ SlitWaveLimit.width M D := by
  apply iSup₂_le
  intro Γ hΓ
  exact SlitWaveLimit.modulus_le_width hΓ.toParentWave

/-- One common source density calibrates every geometric pairable parent,
including parents whose middle portion leaves the source and children
which are not rectifiable. -/
theorem PairableLeaf.one_le_lineLength {M : Marking} {D V T J₀ J₁ : Set ℂ}
    {γ : Curve} (hγ : PairableLeaf M D V T J₀ J₁ γ) {u g : ℂ → ℝ} {ρ : ℂ → ℝ≥0∞}
    (hg : ∀ z ∈ calibrationRegion V T J₀ J₁, ContinuousAt g z)
    (hpos : ∀ z ∈ calibrationRegion V T J₀ J₁, 0 < g z)
    (hloc : LocalSlopeBound u g (calibrationRegion V T J₀ J₁))
    (hzero : ∀ z ∈ J₀, u z = 0) (hone : ∀ z ∈ J₁, u z = 1)
    (hρ : ∀ z ∈ calibrationRegion V T J₀ J₁,
      (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (g z) ≤ ρ z) :
    1 ≤ lineLength ρ (trace γ) := by
  obtain ⟨s, t, hp⟩ := hγ.pair
  have hsub := hp.childTraces_subset_region
  apply one_le_lineLength_of_two_subarcs hγ.simple hp.first_interior hp.last_interior
    hp.ordered (fun z hz => hg z (hsub hz)) (fun z hz => hpos z (hsub hz))
    (fun z hz => hloc z (hsub hz))
  · exact hone _ hp.initial_contact.2.2
  · exact hone _ hp.terminal_contact.2.2
  · exact hzero _ hp.first_contact.2.2
  · exact hzero _ hp.last_contact.2.2
  · exact fun z hz => hρ z (hsub hz)

theorem PairableWave.density_admissible {M : Marking} {D V T J₀ J₁ : Set ℂ}
    {Γ : Set Curve} (hΓ : PairableWave M D V T J₀ J₁ Γ)
    {u g : ℂ → ℝ} {ρ : ℂ → ℝ≥0∞} (hmeas : Measurable ρ)
    (hg : ∀ z ∈ calibrationRegion V T J₀ J₁, ContinuousAt g z)
    (hpos : ∀ z ∈ calibrationRegion V T J₀ J₁, 0 < g z)
    (hloc : LocalSlopeBound u g (calibrationRegion V T J₀ J₁))
    (hzero : ∀ z ∈ J₀, u z = 0) (hone : ∀ z ∈ J₁, u z = 1)
    (hρ : ∀ z ∈ calibrationRegion V T J₀ J₁,
      (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (g z) ≤ ρ z) :
    Admissible (traces Γ) ρ := by
  refine ⟨hmeas, ?_⟩
  rintro S ⟨γ, hγ, rfl⟩
  exact (hΓ.pairable_leaf hγ).one_le_lineLength hg hpos hloc hzero hone hρ

theorem width_le_area {M : Marking} {D V T J₀ J₁ : Set ℂ}
    {u g : ℂ → ℝ} {ρ : ℂ → ℝ≥0∞} (hmeas : Measurable ρ)
    (hg : ∀ z ∈ calibrationRegion V T J₀ J₁, ContinuousAt g z)
    (hpos : ∀ z ∈ calibrationRegion V T J₀ J₁, 0 < g z)
    (hloc : LocalSlopeBound u g (calibrationRegion V T J₀ J₁))
    (hzero : ∀ z ∈ J₀, u z = 0) (hone : ∀ z ∈ J₁, u z = 1)
    (hρ : ∀ z ∈ calibrationRegion V T J₀ J₁,
      (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (g z) ≤ ρ z) :
    width M D V T J₀ J₁ ≤ area ρ := by
  apply iSup₂_le
  intro Γ hΓ
  exact modulus_le_area (hΓ.density_admissible hmeas hg hpos hloc hzero hone hρ)

end
end SlitPairableWaves
