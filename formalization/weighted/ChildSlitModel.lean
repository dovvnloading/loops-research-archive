import MarkedSlitTransport
import SlitWaveModulus

/-!
# Complete same-bank child Waves on a six-marked slit

The two disjoint open ending intervals are literal subintervals of one
physical slit. Both endpoints approach the upper bank. The selected
relative class is defined by a fixed-endpoint homotopy in the actual
source domain minus the entire slit to a simple arc whose open interval
is in the upper half-plane. Arbitrary continuous simple leaves are allowed, including
leaves of infinite arclength and leaves which cross the real axis away
from the slit. No minimizing or maximizing family is assumed.
-/

namespace ChildSlitModel

open Set Function MeasureTheory Metric
open MarkedSlitTransport SlitWaveModulus
open scoped ENNReal NNReal Topology

noncomputable section

/-- Six strictly ordered physical cuts; the two ending intervals are
`(firstLo, firstHi)` and `(secondLo, secondHi)`. -/
@[ext] structure ChildMarking where
  left : ℝ
  firstLo : ℝ
  firstHi : ℝ
  secondLo : ℝ
  secondHi : ℝ
  right : ℝ
  left_lt_firstLo : left < firstLo
  firstLo_lt_firstHi : firstLo < firstHi
  firstHi_lt_secondLo : firstHi < secondLo
  secondLo_lt_secondHi : secondLo < secondHi
  secondHi_lt_right : secondHi < right

/-- The existing literal homotopy type only uses the outside slit cuts.
The first ending interval supplies its unused middle marking fields. -/
def ChildMarking.base (M : ChildMarking) : Marking where
  left := M.left
  first := M.firstLo
  second := M.firstHi
  right := M.right
  left_lt_first := M.left_lt_firstLo
  first_lt_second := M.firstLo_lt_firstHi
  second_lt_right := M.firstHi_lt_secondLo.trans
    (M.secondLo_lt_secondHi.trans M.secondHi_lt_right)

def ChildMarking.slit (M : ChildMarking) : Set ℂ := M.base.slit

def ChildMarking.firstEnds (M : ChildMarking) (z : ℂ) : Prop :=
  z.im = 0 ∧ M.firstLo < z.re ∧ z.re < M.firstHi

def ChildMarking.secondEnds (M : ChildMarking) (z : ℂ) : Prop :=
  z.im = 0 ∧ M.secondLo < z.re ∧ z.re < M.secondHi

def InitialUpperBank (γ : Curve) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ t : Parameter,
    0 < (t : ℝ) → (t : ℝ) < ε → 0 < (γ t).im

structure UpperReference (γ : Curve) : Prop where
  simple : Simple γ
  above : ∀ t ∈ parameterInterior, 0 < (γ t).im

/-- Every intermediate path stays in the specified physical source
domain off the full slit. This records the source relative homotopy
class even when a chosen leaf winds far away from its ending intervals. -/
def RelChildHomotopy (M : ChildMarking) (D : Set ℂ) (γ η : Curve) : Prop :=
  ∃ F : C(Parameter × Parameter, ℂ),
    (∀ t, F (initial,t) = γ t) ∧
    (∀ t, F (terminal,t) = η t) ∧
    (∀ s, F (s,initial) = γ initial) ∧
    (∀ s, F (s,terminal) = γ terminal) ∧
    ∀ s t, t ∈ parameterInterior → F (s,t) ∈ D ∧ F (s,t) ∉ M.slit

theorem RelChildHomotopy.mono {M : ChildMarking} {D E : Set ℂ} {γ η : Curve}
    (hγη : RelChildHomotopy M D γ η) (hDE : D ⊆ E) :
    RelChildHomotopy M E γ η := by
  obtain ⟨F,h0,h1,he0,he1,hF⟩ := hγη
  exact ⟨F,h0,h1,he0,he1,fun s t ht => ⟨hDE (hF s t ht).1,(hF s t ht).2⟩⟩

theorem RelChildHomotopy.forgetDomain
    {M : ChildMarking} {D : Set ℂ} {γ η : Curve}
    (hγη : RelChildHomotopy M D γ η) : RelSlitHomotopy M.base γ η := by
  obtain ⟨F,h0,h1,he0,he1,hF⟩ := hγη
  exact ⟨F,h0,h1,he0,he1,fun s t ht => (hF s t ht).2⟩

def UpperClass (M : ChildMarking) (D : Set ℂ) (γ : Curve) : Prop :=
  ∃ η : Curve, UpperReference η ∧ RelChildHomotopy M D γ η

theorem UpperClass.mono {M : ChildMarking} {D E : Set ℂ} {γ : Curve}
    (hγ : UpperClass M D γ) (hDE : D ⊆ E) : UpperClass M E γ := by
  obtain ⟨η,hη,hγη⟩ := hγ
  exact ⟨η,hη,hγη.mono hDE⟩

/-- An oriented child leaf runs from the first interval's upper bank to
the second interval's upper bank. -/
structure ChildLeaf (M : ChildMarking) (D : Set ℂ) (γ : Curve) : Prop where
  simple : Simple γ
  first_end : M.firstEnds (γ initial)
  last_end : M.secondEnds (γ terminal)
  initial_upper : InitialUpperBank γ
  terminal_upper : UpperBank γ
  inside : ∀ t ∈ parameterInterior, γ t ∈ D
  avoids : ∀ t ∈ parameterInterior, γ t ∉ M.slit
  upper_class : UpperClass M D γ

theorem ChildLeaf.mono {M : ChildMarking} {D E : Set ℂ} {γ : Curve}
    (hγ : ChildLeaf M D γ) (hDE : D ⊆ E) : ChildLeaf M E γ :=
  { hγ with
    inside := fun t ht => hDE (hγ.inside t ht)
    upper_class := hγ.upper_class.mono hDE }

/-- The geometric support is Borel. No regularity or measurable
parametrization of the leaf space is required. -/
structure ChildWave (M : ChildMarking) (D : Set ℂ) (Γ : Set Curve) : Prop where
  borel : MeasurableSet (support Γ)
  leaf : ∀ γ ∈ Γ, ChildLeaf M D γ
  disjoint : ∀ γ ∈ Γ, ∀ η ∈ Γ, γ ≠ η →
    Disjoint (interiorTrace γ) (interiorTrace η)

theorem ChildWave.mono {M : ChildMarking} {D E : Set ℂ} {Γ : Set Curve}
    (hΓ : ChildWave M D Γ) (hDE : D ⊆ E) : ChildWave M E Γ where
  borel := hΓ.borel
  leaf γ hγ := (hΓ.leaf γ hγ).mono hDE
  disjoint := hΓ.disjoint

theorem ChildWave.restrict_of_borel_support
    {M : ChildMarking} {D : Set ℂ} {Γ E : Set Curve}
    (hΓ : ChildWave M D Γ) (hE : MeasurableSet (support (Γ ∩ E))) :
    ChildWave M D (Γ ∩ E) where
  borel := hE
  leaf γ hγ := hΓ.leaf γ hγ.1
  disjoint γ hγ η hη hne := hΓ.disjoint γ hγ.1 η hη.1 hne

/-- The full marked child optimum, over all geometric Borel Waves in
the prescribed relative class. -/
def width (M : ChildMarking) (D : Set ℂ) : ℝ≥0∞ :=
  ⨆ (Γ : Set Curve) (_ : ChildWave M D Γ), modulus (traces Γ)

theorem modulus_le_width {M : ChildMarking} {D : Set ℂ} {Γ : Set Curve}
    (hΓ : ChildWave M D Γ) : modulus (traces Γ) ≤ width M D :=
  le_iSup₂_of_le Γ hΓ le_rfl

theorem width_mono (M : ChildMarking) {D E : Set ℂ} (hDE : D ⊆ E) :
    width M D ≤ width M E := by
  apply iSup₂_le
  intro Γ hΓ
  exact modulus_le_width (hΓ.mono hDE)

end
end ChildSlitModel
