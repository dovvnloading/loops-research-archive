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


/-- Integer portion of the two-winding theorem for a simple annular
inner-boundary path. The geometric Jordan-intersection argument proves
the two inequalities; Lean proves their exact finite consequence.
This does NOT formalize prime ends or the Jordan curve theorem. -/
theorem simple_annular_arc_two_windings
    (n : ℤ)
    (hpos : n < 1)
    (hneg : -2 < n) :
    n = 0 ∨ n = -1 := by
  omega

/-- WAD norms of the two winding packets are nonnegative numbers a,b.
Their exact sum is the full induced WAD norm (source A.2.2).
A packet has at least half the total norm; this says nothing about
the conformal Wave width unless an analytic Parallel Law is verified. -/
theorem two_packet_half_wad_norm (a b : ℝ) :
    (a + b) / 2 ≤ a ∨ (a + b) / 2 ≤ b := by
  rcases le_total a b with h | h
  · right
    linarith
  · left
    linarith

/-- A finite two-packet WAD norm cannot disappear into two strictly
sub-half-mass pieces. This is the contradiction form used in packet
selection arguments. -/
theorem no_two_subhalf_wad_packets
    (a b total : ℝ)
    (hsum : total = a + b)
    (ha : a < total / 2)
    (hb : b < total / 2) : False := by
  linarith


/-- A short KKL Wave has both tagged end lengths < 12*b.
If q ≥ 24*b, their combined length is strictly less than q.
The geometric missed-limb/crosscut conclusion is NOT a Lean theorem:
it requires the true source limb marking and actual short-leaf
subordination. -/
theorem short_wave_ends_miss_some_limb_arithmetic
    (b q leftEnd rightEnd : ℕ)
    (hleft : leftEnd < 12 * b)
    (hright : rightEnd < 12 * b)
    (hq : 24 * b ≤ q) :
    leftEnd + rightEnd < q := by
  omega

/-- The sharper integer threshold q ≥ 24*b-1, written without
natural-number subtraction to avoid an edge case at b=0. -/
theorem short_wave_end_count_below_rotation
    (b q leftEnd rightEnd : ℕ)
    (hleft : leftEnd < 12 * b)
    (hright : rightEnd < 12 * b)
    (hsharp : 24 * b ≤ q + 1) :
    leftEnd + rightEnd < q := by
  omega


/-- Pure integer core of the *actual marked-cut contact lemma*.
For nondegenerate integer-cut closed crest [s,t] and an OPEN
critical limb (a,b), if the closed interval intersects the open limb
then the overlap contains an entire atom (j,j+1).
Here s < b and a < t record the nonempty closed-open overlap;
validating those from the actual prime-end overlap is geometric.
This arithmetic is entirely independent of local connectivity. -/
theorem closed_crest_open_limb_has_full_atom
    (s t a b : ℤ)
    (hcrest : s < t)
    (hlimb : a < b)
    (hoverlapLeft : s < b)
    (hoverlapRight : a < t) :
    ∃ j : ℤ, s ≤ j ∧ j + 1 ≤ t ∧ a ≤ j ∧ j + 1 ≤ b := by
  by_cases h : s ≤ a
  · refine ⟨a, ?_, ?_, ?_, ?_⟩ <;> omega
  · refine ⟨s, ?_, ?_, ?_, ?_⟩ <;> omega

/-- A single marked cut at the endpoint of an OPEN limb cannot
be its only intersection with a positive closed marked crest:
the interval overlap includes a full unit atom. This variant gives
the explicit j as max of the two lower marked cuts. -/
theorem closed_open_marked_overlap_of_integer_cuts
    (s t a b : ℤ)
    (h : s < t ∧ a < b ∧ s < b ∧ a < t) :
    ∃ j : ℤ, s ≤ j ∧ j + 1 ≤ t ∧ a ≤ j ∧ j + 1 ≤ b := by
  exact closed_crest_open_limb_has_full_atom s t a b
    h.1 h.2.1 h.2.2.1 h.2.2.2


/-- The *integer-cut* form of the new native critical-root gate lemma.
For one circular lift with critical limb (a,a+r), positive overlap
s < a+r and a < t, and failure to contain the entire limb,
one of the interval's two end cuts lies STRICTLY inside the limb.
The conversion from cyclic prime-end intervals to a common lift
is a separate topological step, not established by this Lean lemma. -/
theorem partial_critical_overlap_has_internal_endpoint
    (a r s t : ℤ)
    (hr : 1 ≤ r)
    (hJ : s < t)
    (hleft : s < a + r)
    (hright : a < t)
    (hnotcontain : ¬(s ≤ a ∧ a + r ≤ t)) :
    (a < s ∧ s < a + r) ∨
    (a < t ∧ t < a + r) := by
  omega

/-- In the one-marked-atom critical limb case r=1,
overlap without containment is impossible in integer-cut geometry. -/
theorem single_atom_limb_overlap_implies_containment
    (a s t : ℤ)
    (hJ : s < t)
    (hleft : s < a + 1)
    (hright : a < t) :
    s ≤ a ∧ a + 1 ≤ t := by
  omega

/-- There are at most two interval states of any fixed length at
each internal critical marked cut: start at the cut or end there.
For r critical atoms, the total candidate state code has size
2*(r-1). One more critical visit forces repetition in the
abstract cut-side code. That this code represents the ACTUAL
F_* interval state is a separate native geometry hypothesis. -/
theorem critical_cut_side_strict_pigeonhole
    (r : ℕ)
    (visit : Fin (2 * (r - 1) + 1) → Fin (r - 1) × Bool) :
    ∃ i j, i ≠ j ∧ visit i = visit j := by
  classical
  have hcard :
      Fintype.card (Fin (r - 1) × Bool) <
        Fintype.card (Fin (2 * (r - 1) + 1)) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  exact Fintype.exists_ne_map_eq_of_card_lt visit hcard

/-- The source r≤6*b critical-limb length bound sharpens the
conditional critical transition count to at most (12*b-1)^2.
No assumption that the native critical gate is a singleton
prime end occurs in this arithmetic. -/
theorem refined_critical_visit_count_arithmetic
    (r b : ℕ)
    (hr : 1 ≤ r)
    (hb : 1 ≤ b)
    (hlimb : r ≤ 6 * b) :
    (2 * r - 1) * (12 * b - 1) ≤
      (12 * b - 1) * (12 * b - 1) := by
  have hh : 2 * r - 1 ≤ 12 * b - 1 := by omega
  exact Nat.mul_le_mul_right (12 * b - 1) hh


/-- The q-independent size bound for all short critical-cut/side
candidates: at each of r-1 internal critical cuts, two choices of
endpoint orientation and at most 12*b-1 positive short lengths.
The combinatorial bound is kernel-checked; the genuine native gate
return map's values and acyclicity are NOT formalized here. -/
theorem native_short_critical_cut_gate_capacity
    (r b : ℕ)
    (hb : 1 ≤ b)
    (hr : r ≤ 6 * b) :
    2 * (r - 1) * (12 * b - 1) ≤
      (12 * b - 2) * (12 * b - 1) := by
  have hside : 2 * (r - 1) ≤ 12 * b - 2 := by
    omega
  exact Nat.mul_le_mul_right (12 * b - 1) hside

/-- In particular, b=1 leaves at most 110 short genuine gate
input states, independently of the rotation number. -/
theorem native_b_one_gate_capacity (r : ℕ)
    (hr : r ≤ 6) :
    2 * (r - 1) * (12 * 1 - 1) ≤ 110 := by
  omega

end LoopsNativeKKL
