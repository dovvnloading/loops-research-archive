import Period27RealKneading

/-!
# Actual real-interval realization of the period-27 Markov rows

The finite rows below are the 26-edge real Markov spine from
`results/period27_symbolic_marking.json`.  This module proves their
semantics for the actual quadratic map at the certified period-27 center:

* each source edge is an actual nondegenerate real interval;
* the quadratic is injective on it and its image is exactly the interval
  between the computed image endpoints;
* a target edge occurs in the row iff its whole interval is covered;
* every interior target point has exactly one source-edge preimage iff
  that edge occurs, and otherwise has none.

The finite endpoint permutation is checked by the Lean kernel.  Its
interpretation uses the separately proved physical orbit order and the
actual equation f_c^27(0)=0.  No identification with a native KKL tree,
external-ray automaton, clone graph, or marked width is asserted.
-/

namespace LoopsRealPeriod27.Markov

open Set
open LoopsFormal.Period27 LoopsFormal.Paper2

noncomputable section

/-- Orbit time of the vertex at a specified increasing real rank. -/
def orbitIndex (i : Fin 27) : ℕ := realIncreasingIndices.getD i.val 0

/-- The actual point in the real dynamical plane at that rank. -/
def vertex (c : ℝ) (i : Fin 27) : ℝ := iterate (quadratic c) (orbitIndex i) 0

private def nextRanks : List ℕ :=
  [26, 25, 24, 23, 22, 21, 20, 19, 18, 5, 4, 3, 2, 0,
   1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

/-- Rank of the next orbit point.  This is not assumed to describe a map:
`vertex_step` below proves that it describes the actual quadratic. -/
def nextRank (i : Fin 27) : Fin 27 :=
  ⟨nextRanks.getD i.val 0, by revert i; decide +kernel⟩

private theorem orbitIndex_lt (i : Fin 27) : orbitIndex i < 27 := by
  revert i
  decide +kernel

private theorem nextRank_index (i : Fin 27) :
    orbitIndex (nextRank i) = (orbitIndex i + 1) % 27 := by
  revert i
  decide +kernel

/-- All ranks are strictly ordered in the actual real plane, uniformly
on the independently certified parameter bracket. -/
theorem vertex_strictMono (c : ℝ) (hc : c ∈ Icc left right) :
    StrictMono (vertex c) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact physical_adjacent_order c hc i

@[simp] theorem vertex_thirteen (c : ℝ) : vertex c (13 : Fin 27) = 0 := by
  rfl

/-- The exact orbit equation, rather than an abstract cyclic labeling,
supplies the physical endpoint transition. -/
theorem vertex_step (c : ℝ) (hclose : iterate (quadratic c) 27 0 = 0)
    (i : Fin 27) : quadratic c (vertex c i) = vertex c (nextRank i) := by
  change iterate (quadratic c) (orbitIndex i + 1) 0 =
    iterate (quadratic c) (orbitIndex (nextRank i)) 0
  rw [nextRank_index]
  by_cases h : orbitIndex i = 26
  · rw [h]
    change iterate (quadratic c) 27 0 = 0
    exact hclose
  · rw [Nat.mod_eq_of_lt (show orbitIndex i + 1 < 27 by
      have hi := orbitIndex_lt i
      omega)]

/-- Closed physical source/target edge. Shared endpoints are retained;
fiber-count assertions below use target interiors to avoid double counts. -/
def edge (c : ℝ) (i : Fin 26) : Set ℝ :=
  Icc (vertex c i.castSucc) (vertex c i.succ)

def lowerRank (i : Fin 26) : Fin 27 := min (nextRank i.castSucc) (nextRank i.succ)
def upperRank (i : Fin 26) : Fin 27 := max (nextRank i.castSucc) (nextRank i.succ)

/-- Purely finite row predicate: zero-based destination edges between the
ordered endpoint ranks. -/
def RowContains (i j : Fin 26) : Prop :=
  (lowerRank i).val ≤ j.val ∧ j.val < (upperRank i).val

instance (i j : Fin 26) : Decidable (RowContains i j) := inferInstanceAs
  (Decidable ((lowerRank i).val ≤ j.val ∧ j.val < (upperRank i).val))

private theorem quadratic_strictAntiOn (c a b : ℝ) (hb : b ≤ 0) :
    StrictAntiOn (quadratic c) (Icc a b) := by
  intro x hx y hy hxy
  have hprod : 0 < (y - x) * (-(x + y)) :=
    mul_pos (sub_pos.mpr hxy) (by linarith [hy.2])
  dsimp [quadratic]
  nlinarith

private theorem quadratic_strictMonoOn (c a b : ℝ) (ha : 0 ≤ a) :
    StrictMonoOn (quadratic c) (Icc a b) := by
  intro x hx y hy hxy
  have hprod : 0 < (y - x) * (x + y) :=
    mul_pos (sub_pos.mpr hxy) (by linarith [hx.1])
  dsimp [quadratic]
  nlinarith

/-- Every real branch avoids the quadratic's critical point in its
interior. This is deduced from the physical order and the rank of zero. -/
theorem edge_one_side (c : ℝ) (hc : c ∈ Icc left right) (i : Fin 26) :
    vertex c i.succ ≤ 0 ∨ 0 ≤ vertex c i.castSucc := by
  have hv := (vertex_strictMono c hc).monotone
  by_cases hi : i.val < 13
  · left
    have h := hv (show i.succ ≤ (13 : Fin 27) by
      change i.val + 1 ≤ 13
      omega)
    simpa using h
  · right
    have h := hv (show (13 : Fin 27) ≤ i.castSucc by
      change 13 ≤ i.val
      omega)
    simpa using h

/-- The actual quadratic is injective on each physical source edge. -/
theorem quadratic_injOn_edge (c : ℝ) (hc : c ∈ Icc left right) (i : Fin 26) :
    InjOn (quadratic c) (edge c i) := by
  rcases edge_one_side c hc i with h | h
  · exact (quadratic_strictAntiOn c _ _ h).injOn
  · exact (quadratic_strictMonoOn c _ _ h).injOn

private theorem vertex_min (c : ℝ) (hc : c ∈ Icc left right) (i j : Fin 27) :
    vertex c (min i j) = min (vertex c i) (vertex c j) := by
  rcases le_total i j with h | h
  · simp [min_eq_left h, min_eq_left ((vertex_strictMono c hc).monotone h)]
  · simp [min_eq_right h, min_eq_right ((vertex_strictMono c hc).monotone h)]

private theorem vertex_max (c : ℝ) (hc : c ∈ Icc left right) (i j : Fin 27) :
    vertex c (max i j) = max (vertex c i) (vertex c j) := by
  rcases le_total i j with h | h
  · simp [max_eq_right h, max_eq_right ((vertex_strictMono c hc).monotone h)]
  · simp [max_eq_left h, max_eq_left ((vertex_strictMono c hc).monotone h)]

/-- Exact physical image of every source edge, including all interior
points; this is an interval theorem, not an endpoint sampling assertion. -/
theorem physical_edge_image (c : ℝ) (hc : c ∈ Icc left right)
    (hclose : iterate (quadratic c) 27 0 = 0) (i : Fin 26) :
    quadratic c '' edge c i =
      Icc (vertex c (lowerRank i)) (vertex c (upperRank i)) := by
  have hab : vertex c i.castSucc ≤ vertex c i.succ :=
    (vertex_strictMono c hc).monotone (by exact Fin.castSucc_le_succ i)
  have hcont : Continuous (quadratic c) := by unfold quadratic; fun_prop
  have hraw : quadratic c '' edge c i =
      Icc (min (quadratic c (vertex c i.castSucc))
               (quadratic c (vertex c i.succ)))
          (max (quadratic c (vertex c i.castSucc))
               (quadratic c (vertex c i.succ))) := by
    rcases edge_one_side c hc i with h | h
    · have hm := quadratic_strictAntiOn c _ _ h
      have ho := hm.antitoneOn (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
      simpa only [edge, min_eq_right ho, max_eq_left ho] using
        hcont.continuousOn.image_Icc_of_antitoneOn hab hm.antitoneOn
    · have hm := quadratic_strictMonoOn c _ _ h
      have ho := hm.monotoneOn (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
      simpa only [edge, min_eq_left ho, max_eq_right ho] using
        hcont.continuousOn.image_Icc_of_monotoneOn hab hm.monotoneOn
  simpa only [lowerRank, upperRank, vertex_step c hclose,
    vertex_min c hc, vertex_max c hc] using hraw

/-- Every finite row is equivalent to coverage of the whole physical
closed target edge. Both directions are proved. -/
theorem row_iff_physical_edge_covered (c : ℝ) (hc : c ∈ Icc left right)
    (hclose : iterate (quadratic c) 27 0 = 0) (i j : Fin 26) :
    RowContains i j ↔ edge c j ⊆ quadratic c '' edge c i := by
  rw [physical_edge_image c hc hclose]
  have hv := vertex_strictMono c hc
  have hj : vertex c j.castSucc ≤ vertex c j.succ :=
    hv.monotone (Fin.castSucc_le_succ j)
  constructor
  · rintro ⟨hl, hu⟩ x ⟨hxl, hxu⟩
    exact ⟨(hv.monotone (show lowerRank i ≤ j.castSucc from hl)).trans hxl,
      hxu.trans (hv.monotone (show j.succ ≤ upperRank i by
        change j.val + 1 ≤ (upperRank i).val
        omega))⟩
  · intro h
    have hl := (h (left_mem_Icc.mpr hj)).1
    have hu := (h (right_mem_Icc.mpr hj)).2
    constructor
    · by_contra hn
      have hh : j.castSucc < lowerRank i := by
        change j.val < (lowerRank i).val
        omega
      exact (not_lt_of_ge hl) (hv hh)
    · by_contra hn
      have hh : upperRank i < j.succ := by
        change (upperRank i).val < j.val + 1
        omega
      exact (not_lt_of_ge hu) (hv hh)

/-- An interior target point has a source-edge preimage exactly when the
finite row contains that target. The reverse implication excludes spurious
rows and proves zero preimages on every omitted target interior. -/
theorem row_iff_physical_preimage (c : ℝ) (hc : c ∈ Icc left right)
    (hclose : iterate (quadratic c) 27 0 = 0) (i j : Fin 26) (y : ℝ)
    (hy : y ∈ Ioo (vertex c j.castSucc) (vertex c j.succ)) :
    RowContains i j ↔ ∃ x ∈ edge c i, quadratic c x = y := by
  have hv := vertex_strictMono c hc
  constructor
  · intro h
    exact (row_iff_physical_edge_covered c hc hclose i j).mp h
      ⟨hy.1.le, hy.2.le⟩
  · rintro ⟨x, hx, hxy⟩
    have him : y ∈ quadratic c '' edge c i := ⟨x, hx, hxy⟩
    rw [physical_edge_image c hc hclose] at him
    constructor
    · by_contra hn
      have hindex : j.succ ≤ lowerRank i := by
        change j.val + 1 ≤ (lowerRank i).val
        omega
      have hh := hv.monotone hindex
      linarith [him.1, hy.2]
    · by_contra hn
      have hindex : upperRank i ≤ j.castSucc := by
        change (upperRank i).val ≤ j.val
        omega
      have hh := hv.monotone hindex
      linarith [him.2, hy.1]

/-- Each indicated real branch has exactly one preimage of every target
interior point. Thus the finite matrix entries are actual multiplicities. -/
theorem row_iff_unique_physical_preimage (c : ℝ) (hc : c ∈ Icc left right)
    (hclose : iterate (quadratic c) 27 0 = 0) (i j : Fin 26) (y : ℝ)
    (hy : y ∈ Ioo (vertex c j.castSucc) (vertex c j.succ)) :
    RowContains i j ↔ ∃! x : ℝ, x ∈ edge c i ∧ quadratic c x = y := by
  constructor
  · intro h
    obtain ⟨x, hx, hxy⟩ := (row_iff_physical_preimage c hc hclose i j y hy).mp h
    refine ⟨x, ⟨hx, hxy⟩, ?_⟩
    rintro z ⟨hz, hzy⟩
    exact quadratic_injOn_edge c hc i hz hx (hzy.trans hxy.symm)
  · rintro ⟨x, ⟨hx, hxy⟩, _⟩
    exact (row_iff_physical_preimage c hc hclose i j y hy).mpr ⟨x, hx, hxy⟩

/-- A concrete false strengthening is refuted in the physical plane:
the first source edge has no preimage of any interior point of the first
target edge. Endpoint or graph-label agreement cannot add this row. -/
theorem first_edge_omits_first_target (c : ℝ) (hc : c ∈ Icc left right)
    (hclose : iterate (quadratic c) 27 0 = 0) (y : ℝ)
    (hy : y ∈ Ioo (vertex c (0 : Fin 27)) (vertex c (1 : Fin 27))) :
    ¬ ∃ x ∈ edge c (0 : Fin 26), quadratic c x = y := by
  intro h
  have hm := (row_iff_physical_preimage c hc hclose
    (0 : Fin 26) (0 : Fin 26) y hy).mpr h
  exact (show ¬ RowContains (0 : Fin 26) (0 : Fin 26) by decide +kernel) hm

/-- Fully computed zero-based row lists, with no analytic content hidden
in their definition. -/
def markovRows : List (List ℕ) :=
  List.ofFn fun i : Fin 26 =>
    (List.range 26).filter fun j => decide ((lowerRank i).val ≤ j ∧ j < (upperRank i).val)

/-- The exact same rows as `real_interval_markov_spine.edge_destinations`
in the archived JSON certificate. -/
theorem markovRows_exact : markovRows =
    [[25], [24], [23], [22], [21], [20], [19], [18],
     [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
     [4], [3], [2], [0, 1], [0], [1, 2, 3, 4, 5],
     [6], [7], [8], [9], [10], [11], [12], [13], [14], [15], [16]] := by
  decide +kernel

/-- The parameter premises are inhabited by the independently proved
unique physical center. This theorem does not merely assume that a center
with the desired finite rows exists. -/
theorem exists_physical_center_with_markov_rows :
    ∃ c : ℝ, c ∈ Icc left right ∧ iterate (quadratic c) 27 0 = 0 ∧
      (∀ i j : Fin 26, ∀ y ∈ Ioo (vertex c j.castSucc) (vertex c j.succ),
        RowContains i j ↔ ∃! x : ℝ, x ∈ edge c i ∧ quadratic c x = y) := by
  obtain ⟨c, ⟨hl, hr, hclose, _⟩, _⟩ := exact_real_quadratic_period27
  refine ⟨c, ⟨hl.le, hr.le⟩, hclose, ?_⟩
  intro i j y hy
  exact row_iff_unique_physical_preimage c ⟨hl.le, hr.le⟩ hclose i j y hy

#print axioms vertex_step
#print axioms physical_edge_image
#print axioms row_iff_physical_edge_covered
#print axioms row_iff_unique_physical_preimage
#print axioms first_edge_omits_first_target
#print axioms markovRows_exact
#print axioms exists_physical_center_with_markov_rows

end
end LoopsRealPeriod27.Markov
