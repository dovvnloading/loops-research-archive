import Mathlib

/-!
# Issue 40: native-interface proof obligations, finite algebra only

These kernel lemmas certify three implications used in the KKL repair:
(1) strict critical-state pigeonhole;
(2) finite endpoint-gate orbit repetition;
(3) positive-weight PF/WAD non-return.

They DO NOT construct the source-defined prime-end access map, show that
a Wave has an admissible positive crest, or produce the required native
dual-WAD witness. Those are separate analytic hypotheses.
-/

namespace LoopsNativeKKL

/-- With at most r+k-1 critical states, r+k visits force
two distinct visit indices to represent the same state. -/
theorem strict_critical_pigeonhole
    (r k : ℕ) (hr : 0 < r) (hk : 0 < k)
    (visit : Fin (r + k) → Fin (r + k - 1)) :
    ∃ i j, i ≠ j ∧ visit i = visit j := by
  classical
  have hcard :
      Fintype.card (Fin (r + k - 1)) <
        Fintype.card (Fin (r + k)) := by
    simp only [Fintype.card_fin]
    omega
  exact Fintype.exists_ne_map_eq_of_card_lt visit hcard

/-- Every finite endpoint path of length #endpoints+1 repeats a state.
This is only a combinatorial lemma: to turn the repetition into a
native periodic gate one must prove every step is the actual F_* map. -/
theorem finite_gate_repetition
    {E : Type*} [Fintype E]
    (path : Fin (Fintype.card E + 1) → E) :
    ∃ i j, i ≠ j ∧ path i = path j := by
  classical
  have hcard : Fintype.card E <
      Fintype.card (Fin (Fintype.card E + 1)) := by
    simp only [Fintype.card_fin]
    omega
  exact Fintype.exists_ne_map_eq_of_card_lt path hcard

/-- Applied to real iterates of any *total* endpoint map,
the same finite pigeonhole proof forces a repeat.
For a partial source-defined endpoint map, this applies only
to a verified nonterminating orbit. -/
theorem finite_gate_orbit_repetition
    {E : Type*} [Fintype E]
    (g : E → E) (start : E) :
    ∃ i j : Fin (Fintype.card E + 1),
      i ≠ j ∧ Nat.iterate g i.val start =
        Nat.iterate g j.val start := by
  exact finite_gate_repetition
    (fun i => Nat.iterate g i.val start)

/-- Positive mass cannot satisfy a nontrivial multiplicative
return inequality with expansion factor > 1. -/
theorem no_positive_scalar_return
    (mass factor : ℝ)
    (hmass : 0 < mass) (hfactor : 1 < factor)
    (hreturn : factor * mass ≤ mass) : False := by
  have hstrict : 0 < (factor - 1) * mass :=
    mul_pos (sub_pos.mpr hfactor) hmass
  nlinarith

/-- The native KKL domination direction (old value <= pullback
value) conflicts with a strict inverse-pullback contraction.
The parameter factor is the positive quantity λ_F^p > 1. -/
theorem no_self_domination
    (mass pullbackMass factor : ℝ)
    (hmass : 0 < mass) (hfactor : 1 < factor)
    (hdom : mass ≤ pullbackMass)
    (hcontract : factor * pullbackMass ≤ mass) : False := by
  have hfactor_nonneg : 0 ≤ factor := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hfactor)
  have hreturn : factor * mass ≤ mass :=
    (mul_le_mul_of_nonneg_left hdom hfactor_nonneg).trans hcontract
  exact no_positive_scalar_return mass factor hmass hfactor hreturn

/-- A nonnegative *left* PF weight pairing, with an exact expanding
eigen-identity for a particular actual edge witness d, rules out
coordinatewise self-domination under the same edge operator.
The analytic *existence* and correct orientation of the witness
are intentionally not assumed to follow from the matrix alone. -/
def pairing {E : Type*} [Fintype E]
    (weight data : E → ℝ) : ℝ :=
  ∑ i, weight i * data i

theorem no_positive_pf_witness_return
    {E : Type*} [Fintype E]
    (T : (E → ℝ) → (E → ℝ))
    (weight data : E → ℝ) (factor : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hmass : 0 < pairing weight data)
    (hfactor : 1 < factor)
    (heigen : pairing weight (T data) =
      factor * pairing weight data)
    (hreturn : ∀ i, T data i ≤ data i) : False := by
  classical
  have hp : pairing weight (T data) ≤ pairing weight data := by
    unfold pairing
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hreturn i) (hweight i)
  rw [heigen] at hp
  exact no_positive_scalar_return
    (pairing weight data) factor hmass hfactor hp

/-- The purely numerical positive-crest implication for a Wave
with two distinct singleton-atom ends: once Appendix A.1 forces
at least three atoms in the base, the number of other full atoms
is positive. This does not prove that arbitrary composite-end
Waves have positive crests. -/
theorem atomic_ends_leave_positive_crest (k : ℕ)
    (hadmissible : 2 < k) : 0 < k - 2 := by
  omega


/-- The finite *order* part of the no-touching-crest argument:
a leaf from the last left-end atom cannot end in the adjacent
first right-end atom; similarly in the opposite direction.
The four marked endpoint atoms are therefore alternating.
The final Jordan crossing obstruction is geometric, not encoded here. -/
theorem touching_end_extrema_alternate
    (cut leftFar rightFar : ℕ)
    (hcut : 2 ≤ cut)
    (hleft : leftFar + 2 ≤ cut)
    (hright : cut + 1 ≤ rightFar) :
    leftFar < cut - 1 ∧ cut - 1 < cut ∧ cut < rightFar := by
  omega

/-- If two connected end packets cover every marked atom of a full
base, the total number of atoms is at most the sum of their lengths.
With the source's strict short-end bounds this is impossible when
the total marking contains at least 24*b atoms. -/
theorem short_full_base_no_zero_atom_crest
    (b total leftEnd rightEnd : ℕ)
    (hlarge : 24 * b ≤ total)
    (hleft : leftEnd < 12 * b)
    (hright : rightEnd < 12 * b)
    (hcovered : total ≤ leftEnd + rightEnd) : False := by
  omega

/-- The q-version, after independently verifying the genuine marking
has at least one atom in each rotational limb (total ≥ q). -/
theorem long_rotation_short_full_base_positive_atom
    (b q total leftEnd rightEnd : ℕ)
    (hq : 24 * b ≤ q)
    (hmark : q ≤ total)
    (hleft : leftEnd < 12 * b)
    (hright : rightEnd < 12 * b)
    (hcovered : total ≤ leftEnd + rightEnd) : False := by
  omega

/-- The positive-gap arithmetic, separate from the topological
statement that a genuine proper-base Wave with nonempty crest
cannot have two end packets merely touching at a marked cut. -/
theorem separated_end_packets_leave_atom
    (base leftEnd rightEnd : ℕ)
    (hgap : leftEnd + rightEnd < base) :
    0 < base - (leftEnd + rightEnd) := by
  omega


/-- Exact fiber-level collision identity for a **real two-sheet covering**.
A target point is in both images iff its source representatives
coincide or are related by the nontrivial deck involution.
This is purely set-theoretic: analytic proper-path survival and
admissible Wave crest inputs are separate native hypotheses. -/
theorem two_sheet_image_intersection
    {A B : Type*} (p : A → B) (deck : A → A)
    (hdeck : ∀ x, p (deck x) = p x)
    (hfiber : ∀ x z, p x = p z → z = x ∨ z = deck x)
    (S T : Set A) :
    p '' S ∩ p '' T =
      p '' (S ∩ T) ∪ p '' (S ∩ deck ⁻¹' T) := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, ⟨z, hz, hzy⟩⟩
    rcases hfiber x z (hxy.trans hzy.symm) with hsame | hother
    · left
      refine ⟨x, ⟨hx, ?_⟩, hxy⟩
      simpa [hsame] using hz
    · right
      refine ⟨x, ⟨hx, ?_⟩, hxy⟩
      change deck x ∈ T
      simpa [hother] using hz
  · rintro (⟨x, ⟨hx, ht⟩, hxy⟩ | ⟨x, ⟨hx, ht⟩, hxy⟩)
    · exact ⟨⟨x, hx, hxy⟩, ⟨x, ht, hxy⟩⟩
    · change deck x ∈ T at ht
      exact ⟨⟨x, hx, hxy⟩, ⟨deck x, ht, (hdeck x).trans hxy⟩⟩

/-- When two source packets are disjoint, *all* target collisions
are deck pairings, not folds inside a single source packet. -/
theorem disjoint_two_sheet_collision_only_deck
    {A B : Type*} (p : A → B) (deck : A → A)
    (hdeck : ∀ x, p (deck x) = p x)
    (hfiber : ∀ x z, p x = p z → z = x ∨ z = deck x)
    (S T : Set A) (hdisj : S ∩ T = ∅) :
    p '' S ∩ p '' T = p '' (S ∩ deck ⁻¹' T) := by
  rw [two_sheet_image_intersection p deck hdeck hfiber S T, hdisj]
  simp

end LoopsNativeKKL
