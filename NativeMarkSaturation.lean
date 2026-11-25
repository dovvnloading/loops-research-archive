import ImmersionMarkFinite

/-!
# Complete source-eligible finite marked action

The native-mark audit of 24 November 2026 checks 191 source-eligible
inputs: 100 open marked arcs (including ten punctured circles), 90
proper closed arcs, and the complete circle. This module verifies that
whole finite grammar using the cut-derived lift in ImmersionMarkFinite.

The open/closed distinction is essential: an image spanning exactly one
turn is punctured when open and complete when closed. Exact first
saturation times, rather than just atom-label support, are checked below.

These are contour-model theorems. Identifying this operation with the
native immersion action still uses the explicitly imported KKL
Propositions 6.5--6.6 in the written audit. The final obstruction theorem
is conditional on the stated propagation and proper-crest hypotheses;
it does not formalize KKL A.14, paths, laminations, or extremal width.

Source: research/independent_audits/native_mark_attack_20261124/NOTE.md,
Sections 5--7, and its verify.py. Prepared with OpenAI GPT-6 Astra Pro
assistance; no independent human review is asserted.
-/

namespace LoopsFormal.NativeMarkSaturation

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

open ImmersionMarkFinite (liftedCut)

/-- A lifted marked interval. Its length counts atoms, not endpoints. -/
structure MarkedArc where
  left : Nat
  length : Nat
  closed : Bool
deriving DecidableEq, Repr

/-- Exactly the grammar covered by the source-imported finite action.
The length field stores the actual positive length minus one. -/
inductive SourceInput where
  | circle
  | openArc (left : Fin 10) (lengthMinusOne : Fin 10)
  | closedArc (left : Fin 10) (lengthMinusOne : Fin 9)
deriving DecidableEq, Repr

/-- `none` is the entire circle. A closed full turn is encoded only by
`circle`, while an open full turn remains a punctured circle. -/
def realize : SourceInput → Option MarkedArc
  | .circle => none
  | .openArc s l => some ⟨s.val, l.val + 1, false⟩
  | .closedArc s l => some ⟨s.val, l.val + 1, true⟩

def advance : Option MarkedArc → Option MarkedArc
  | none => none
  | some arc =>
      let a := liftedCut arc.left
      let b := liftedCut (arc.left + arc.length)
      let width := b - a
      if 10 < width ∨ (width = 10 ∧ arc.closed = true) then none
      else some ⟨a % 10, width, arc.closed⟩

def iterate : Nat → Option MarkedArc → Option MarkedArc
  | 0, arc => arc
  | n + 1, arc => advance (iterate n arc)

/-- Exhaustive finite input list; no quotient by atom-label support. -/
def sourceInputs : List SourceInput :=
  [.circle] ++
    (List.ofFn fun s : Fin 10 =>
      List.ofFn fun l : Fin 10 => SourceInput.openArc s l).flatten ++
    (List.ofFn fun s : Fin 10 =>
      List.ofFn fun l : Fin 9 => SourceInput.closedArc s l).flatten

theorem source_grammar_has_191_distinct_inputs :
    sourceInputs.length = 191 ∧ sourceInputs.Nodup := by
  decide +kernel

/-- Distinct grammar entries represent distinct endpoint-aware states,
not merely distinct constructors with coinciding interpretations. -/
theorem source_realizations_are_distinct :
    (sourceInputs.map realize).Nodup := by
  decide +kernel

theorem source_enumeration_is_complete (input : SourceInput) :
    input ∈ sourceInputs := by
  cases input with
  | circle => decide +kernel
  | openArc s l =>
    have h : ∀ s : Fin 10, ∀ l : Fin 10,
        SourceInput.openArc s l ∈ sourceInputs := by
      decide +kernel
    exact h s l
  | closedArc s l =>
    have h : ∀ s : Fin 10, ∀ l : Fin 9,
        SourceInput.closedArc s l ∈ sourceInputs := by
      decide +kernel
    exact h s l

/-- All 100 open inputs, including the ten punctured circles. -/
theorem all_open_inputs_saturate_within_five :
    ∀ s : Fin 10, ∀ l : Fin 10,
      iterate 5 (realize (.openArc s l)) = none := by
  decide +kernel

/-- The 90 proper closed closures use the inclusive full-turn cutoff. -/
theorem all_closed_inputs_saturate_within_five :
    ∀ s : Fin 10, ∀ l : Fin 9,
      iterate 5 (realize (.closedArc s l)) = none := by
  decide +kernel

/-- The complete source-eligible grammar satisfies the five-step bound. -/
theorem all_source_inputs_saturate_within_five (input : SourceInput) :
    iterate 5 (realize input) = none := by
  cases input with
  | circle => rfl
  | openArc s l => exact all_open_inputs_saturate_within_five s l
  | closedArc s l => exact all_closed_inputs_saturate_within_five s l

/-- Same lift and atom support, but different inclusion of the endpoint. -/
theorem exact_turn_distinguishes_open_and_closed :
    advance (some ⟨2, 6, false⟩) = some ⟨5, 10, false⟩ ∧
    advance (some ⟨2, 6, true⟩) = none ∧
    advance (some ⟨3, 6, false⟩) = some ⟨6, 10, false⟩ ∧
    advance (some ⟨3, 6, true⟩) = none ∧
    advance (some ⟨8, 4, false⟩) = some ⟨5, 10, false⟩ ∧
    advance (some ⟨8, 4, true⟩) = none ∧
    advance (some ⟨9, 4, false⟩) = some ⟨6, 10, false⟩ ∧
    advance (some ⟨9, 4, true⟩) = none := by
  decide +kernel

/-- No other proper marked arc has a lifted image spanning exactly
one turn. This checks completeness of the endpoint regressions. -/
theorem exact_turn_inputs_are_exhaustive :
    ∀ s : Fin 10, ∀ l : Fin 9,
      (liftedCut (s.val + (l.val + 1)) - liftedCut s.val = 10) ↔
        (s.val, l.val + 1) ∈ [(2, 6), (3, 6), (8, 4), (9, 4)] := by
  decide +kernel

def atomClock (s : Fin 10) : Nat :=
  [2, 4, 4, 5, 4, 3, 4, 5, 4, 4][s.val]!

/-- Exact first saturation times: every earlier state is still proper,
including any punctured-circle state with full open-atom support. -/
theorem exact_open_atom_saturation_clocks :
    ∀ s : Fin 10,
      iterate (atomClock s) (realize (.openArc s 0)) = none ∧
      ∀ earlier : Fin (atomClock s),
        iterate earlier.val (realize (.openArc s 0)) ≠ none := by
  decide +kernel

theorem five_steps_remain_sharp :
    iterate 4 (realize (.openArc 3 0)) ≠ none ∧
    iterate 5 (realize (.openArc 3 0)) = none := by
  decide +kernel

/-- The supplied physical limb identification has labels 0:[K0,K2]
and 1:[K1]. This definition records that input, not its geometry. -/
def limb (k : Fin 3) : Fin 2 := if k.val = 1 then 1 else 0

def limbComponents (j : Fin 2) : List (Fin 3) :=
  (List.ofFn fun k : Fin 3 => k).filter fun k => limb k == j

def cycleNext (k : Fin 3) : Fin 3 :=
  ⟨(k.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

/-- The q=2 partition is disjoint and includes all three small-set labels. -/
theorem native_limb_partition :
    limbComponents 0 = [0, 2] ∧ limbComponents 1 = [1] ∧
    (limbComponents 0 ++ limbComponents 1).Nodup ∧
    ∀ k : Fin 3, k ∈ limbComponents 0 ∨ k ∈ limbComponents 1 := by
  decide +kernel

/-- The actual three-cycle identification, once supplied, has this
finite image table and satisfies the b=2 occupancy clause. -/
theorem native_cycle_and_limb_bound :
    (List.ofFn cycleNext) = [1, 2, 0] ∧
    ∀ j : Fin 2, (limbComponents j).length ≤ 2 := by
  decide +kernel

/-- Rotation residues in the source window |j| <= b with q=b=2. -/
def criticalWindow : List Int :=
  ([-2, -1, 0, 1, 2] : List Int).map fun j => j % 2

theorem native_window_covers_both_limbs :
    criticalWindow = [0, 1, 0, 1, 0] ∧
    ∀ j : Fin 2, (j.val : Int) ∈ criticalWindow := by
  decide +kernel

/-- Every label in the critical limb maps to a limb inside that
window. No source-hypothesis identification is inferred from the table. -/
theorem critical_component_images_stay_in_window :
    ∀ k : Fin 3, limb k = 0 →
      ((limb (cycleNext k)).val : Int) ∈ criticalWindow := by
  decide +kernel

/-- Abstract finite-horizon obstruction used in Corollary 6.1.
`P k J` stands for the stage-k descendant being a nonempty Wave whose
crest contains J. Propagation and the impossibility of a full-circle
crest are explicit premises, not claims about unformalized geometry. -/
theorem no_chain_to_saturated_crest
    (P : Nat → Option MarkedArc → Prop)
    (start : Option MarkedArc) (n : Nat)
    (hstart : P 0 start)
    (hstep : ∀ k, k < n → ∀ state, P k state → P (k + 1) (advance state))
    (hproper : ¬ P n none)
    (hsaturation : iterate n start = none) : False := by
  have hprop : ∀ k, k ≤ n → P k (iterate k start) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact hstart
    | succ k ih =>
      intro hk
      exact hstep k (by omega) (iterate k start) (ih (by omega))
  have hlast := hprop n (Nat.le_refl n)
  rw [hsaturation] at hlast
  exact hproper hlast

/-- Five successive pushes cannot satisfy those hypotheses for any
original source-eligible input. The analytic propagation premise is
precisely where the written application imports KKL A.14. -/
theorem no_source_chain_through_five
    (P : Nat → Option MarkedArc → Prop) (input : SourceInput)
    (hstart : P 0 (realize input))
    (hstep : ∀ k, k < 5 → ∀ state, P k state → P (k + 1) (advance state))
    (hproper : ¬ P 5 none) : False := by
  exact no_chain_to_saturated_crest P (realize input) 5 hstart hstep hproper
    (all_source_inputs_saturate_within_five input)

#print axioms source_grammar_has_191_distinct_inputs
#print axioms source_realizations_are_distinct
#print axioms source_enumeration_is_complete
#print axioms all_open_inputs_saturate_within_five
#print axioms all_closed_inputs_saturate_within_five
#print axioms all_source_inputs_saturate_within_five
#print axioms exact_turn_distinguishes_open_and_closed
#print axioms exact_turn_inputs_are_exhaustive
#print axioms exact_open_atom_saturation_clocks
#print axioms five_steps_remain_sharp
#print axioms native_limb_partition
#print axioms native_cycle_and_limb_bound
#print axioms native_window_covers_both_limbs
#print axioms critical_component_images_stay_in_window
#print axioms no_chain_to_saturated_crest
#print axioms no_source_chain_through_five

end LoopsFormal.NativeMarkSaturation
