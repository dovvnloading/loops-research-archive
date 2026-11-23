import Paper2Phase
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith

/-!
# All finite inverse fibers of a realized real Markov partition

The hypotheses are one-step statements about the specified real function,
ordered real vertices, and actual interval images. No coding or finite-fiber
conclusion is assumed. The proof constructs an equivalence between every
finite inverse fiber and a finite recursively defined path type, then identifies
its cardinality with the corresponding entry of the adjacency matrix power.
The period-27 quadratic specialization is in `Period27FiniteFibers.lean`.
-/

namespace LoopsRealMarkov

open Set LoopsFormal.Paper2

noncomputable section

def openEdge {N : ℕ} (v : Fin (N + 1) → ℝ) (i : Fin N) : Set ℝ :=
  Ioo (v i.castSucc) (v i.succ)

def closedEdge {N : ℕ} (v : Fin (N + 1) → ℝ) (i : Fin N) : Set ℝ :=
  Icc (v i.castSucc) (v i.succ)

def core {N : ℕ} (v : Fin (N + 1) → ℝ) : Set ℝ :=
  Icc (v 0) (v (Fin.last N))

/-- Independently checkable one-step realization data. -/
structure System (N : ℕ) where
  vertex : Fin (N + 1) → ℝ
  f : ℝ → ℝ
  next : Fin (N + 1) → Fin (N + 1)
  row : Fin N → Fin N → Prop
  rowDecidable : DecidableRel row
  ordered : StrictMono vertex
  vertex_step : ∀ k, f (vertex k) = vertex (next k)
  image_core : ∀ i, f '' closedEdge vertex i ⊆ core vertex
  branch_injective : ∀ i, InjOn f (closedEdge vertex i)
  row_preimage : ∀ i j y, y ∈ openEdge vertex j →
    (row i j ↔ ∃ x ∈ closedEdge vertex i, f x = y)

instance {N : ℕ} (S : System N) : DecidableRel S.row := S.rowDecidable

namespace System

variable {N : ℕ} (S : System N)

/-- Different open partition edges cannot contain the same point. -/
theorem interior_index_unique (i j : Fin N) (x : ℝ)
    (hi : x ∈ openEdge S.vertex i) (hj : x ∈ openEdge S.vertex j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hle : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact h
    have hv := S.ordered.monotone hle
    exact False.elim (by dsimp [openEdge] at hi hj; linarith [hi.2, hj.1])
  · exact h
  · have hle : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      exact h
    have hv := S.ordered.monotone hle
    exact False.elim (by dsimp [openEdge] at hi hj; linarith [hj.2, hi.1])

/-- No orbit vertex is hidden inside a partition edge. -/
theorem interior_ne_vertex (i : Fin N) (x : ℝ)
    (hx : x ∈ openEdge S.vertex i) (k : Fin (N + 1)) : x ≠ S.vertex k := by
  intro heq
  by_cases hk : k ≤ i.castSucc
  · have hv := S.ordered.monotone hk
    dsimp [openEdge] at hx
    rw [heq] at hx
    linarith [hx.1]
  · have hle : i.succ ≤ k := by
      change i.val + 1 ≤ k.val
      change ¬ k.val ≤ i.val at hk
      omega
    have hv := S.ordered.monotone hle
    dsimp [openEdge] at hx
    rw [heq] at hx
    linarith [hx.2]

/-- Every nonvertex point of the closed physical core belongs to an edge
interior. The location is obtained from the greatest vertex below the point. -/
theorem exists_interior_index (x : ℝ) (hx : x ∈ core S.vertex)
    (hne : ∀ k, x ≠ S.vertex k) : ∃ i : Fin N, x ∈ openEdge S.vertex i := by
  classical
  have hleft : S.vertex 0 < x := lt_of_le_of_ne hx.1 (hne 0).symm
  let below : Finset (Fin (N + 1)) := Finset.univ.filter fun k => S.vertex k < x
  have hb : below.Nonempty := ⟨0, by simp [below, hleft]⟩
  let k := below.max' hb
  have hk : S.vertex k < x := (Finset.mem_filter.mp (below.max'_mem hb)).2
  have hkN : k.val < N := by
    have hkbound := k.isLt
    by_contra h
    have heq : k = Fin.last N := by apply Fin.ext; dsimp [Fin.last]; omega
    rw [heq] at hk
    exact (not_lt_of_ge hx.2) hk
  let i : Fin N := ⟨k.val, hkN⟩
  have hic : i.castSucc = k := by apply Fin.ext; rfl
  have hupper : x < S.vertex i.succ := by
    by_contra h
    have hs : S.vertex i.succ < x :=
      lt_of_le_of_ne (le_of_not_gt h) (hne i.succ).symm
    have hmem : i.succ ∈ below := by simp [below, hs]
    have hmax : i.succ ≤ k := below.le_max' i.succ hmem
    change k.val + 1 ≤ k.val at hmax
    omega
  exact ⟨i, by change S.vertex i.castSucc < x ∧ x < S.vertex i.succ; rw [hic]; exact ⟨hk, hupper⟩⟩

private theorem iterate_succ_left (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    iterate f (n + 1) x = iterate f n (f x) := by
  simpa only [Nat.add_comm 1 n, iterate] using iterate_add f 1 n x

/-- Actual forward iterates of vertices stay in the specified finite vertex set. -/
theorem iterate_vertex (n : ℕ) (k : Fin (N + 1)) :
    iterate S.f n (S.vertex k) = S.vertex (iterate S.next n k) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate, ih, S.vertex_step]

/-- A preimage of an interior point cannot be a source endpoint. -/
theorem preimage_interior (i j : Fin N) (x y : ℝ)
    (hx : x ∈ closedEdge S.vertex i) (hy : y ∈ openEdge S.vertex j)
    (hxy : S.f x = y) : x ∈ openEdge S.vertex i := by
  have hl : x ≠ S.vertex i.castSucc := by
    intro h
    have hvertex : y = S.vertex (S.next i.castSucc) := by rw [← hxy, h, S.vertex_step]
    exact S.interior_ne_vertex j y hy _ hvertex
  have hu : x ≠ S.vertex i.succ := by
    intro h
    have hvertex : y = S.vertex (S.next i.succ) := by rw [← hxy, h, S.vertex_step]
    exact S.interior_ne_vertex j y hy _ hvertex
  exact ⟨lt_of_le_of_ne hx.1 hl.symm, lt_of_le_of_ne hx.2 hu⟩

/-- The one-step inverse is uniquely realized in the open source edge. -/
theorem unique_interior_preimage (i j : Fin N) (y : ℝ)
    (hy : y ∈ openEdge S.vertex j) (hrow : S.row i j) :
    ∃! x : ℝ, x ∈ openEdge S.vertex i ∧ S.f x = y := by
  obtain ⟨x, hx, hxy⟩ := (S.row_preimage i j y hy).mp hrow
  refine ⟨x, ⟨S.preimage_interior i j x y hx hy hxy, hxy⟩, ?_⟩
  rintro z ⟨hz, hzy⟩
  exact S.branch_injective i ⟨hz.1.le, hz.2.le⟩ hx (hzy.trans hxy.symm)

/-- Actual n-step inverse fiber, with the source endpoint convention explicit. -/
def Fiber (n : ℕ) (i : Fin N) (y : ℝ) : Type :=
  {x : ℝ // x ∈ openEdge S.vertex i ∧ iterate S.f n x = y}

/-- Finite directed paths with specified endpoints. A successor path chooses
one allowed first edge and then a shorter path. -/
def Paths : ℕ → Fin N → Fin N → Type
  | 0, i, j => PLift (i = j)
  | n + 1, i, j => (k : {k : Fin N // S.row i k}) × Paths n k.val j

instance pathsFintype : (n : ℕ) → (i j : Fin N) → Fintype (S.Paths n i j)
  | 0, i, j => by dsimp [Paths]; infer_instance
  | n + 1, i, j => by
      change Fintype ((k : {k : Fin N // S.row i k}) × S.Paths n k.val j)
      letI (k : {k : Fin N // S.row i k}) := pathsFintype n k.val j
      infer_instance

private def liftPoint (i j : Fin N) (y : ℝ) (hy : y ∈ openEdge S.vertex j)
    (hr : S.row i j) : ℝ := Classical.choose (S.unique_interior_preimage i j y hy hr)

private theorem liftPoint_spec (i j : Fin N) (y : ℝ) (hy : y ∈ openEdge S.vertex j)
    (hr : S.row i j) :
    S.liftPoint i j y hy hr ∈ openEdge S.vertex i ∧ S.f (S.liftPoint i j y hy hr) = y :=
  (Classical.choose_spec (S.unique_interior_preimage i j y hy hr)).1

private def liftFiber (n : ℕ) (i : Fin N) (y : ℝ)
    (p : (k : {k : Fin N // S.row i k}) × S.Fiber n k.val y) : S.Fiber (n + 1) i y :=
  let h := S.liftPoint_spec i p.1.val p.2.val p.2.property.1 p.1.property
  ⟨S.liftPoint i p.1.val p.2.val p.2.property.1 p.1.property,
    h.1, by rw [iterate_succ_left, h.2]; exact p.2.property.2⟩

private theorem liftFiber_image (n : ℕ) (i : Fin N) (y : ℝ)
    (p : (k : {k : Fin N // S.row i k}) × S.Fiber n k.val y) :
    S.f (S.liftFiber n i y p).val = p.2.val :=
  (S.liftPoint_spec i p.1.val p.2.val p.2.property.1 p.1.property).2

private theorem liftFiber_injective (n : ℕ) (i : Fin N) (y : ℝ) :
    Function.Injective (S.liftFiber n i y) := by
  rintro ⟨⟨k, hk⟩, ⟨z, hz⟩⟩ ⟨⟨l, hl⟩, ⟨w, hw⟩⟩ heq
  have himage := congrArg (fun x : S.Fiber (n + 1) i y => S.f x.val) heq
  rw [S.liftFiber_image, S.liftFiber_image] at himage
  change z = w at himage
  subst w
  have hkl : k = l := S.interior_index_unique k l z hz.1 hw.1
  subst l
  rfl

/-- Every actual successor fiber has an allowed first edge and a shorter
actual fiber. The final interior target excludes every intermediate vertex. -/
theorem fiber_successor_decomposition (n : ℕ) (i j : Fin N) (y : ℝ)
    (hy : y ∈ openEdge S.vertex j) (x : S.Fiber (n + 1) i y) :
    ∃ k : Fin N, S.row i k ∧ S.f x.val ∈ openEdge S.vertex k ∧
      iterate S.f n (S.f x.val) = y := by
  have hcore : S.f x.val ∈ core S.vertex :=
    S.image_core i ⟨x.val, ⟨x.property.1.1.le, x.property.1.2.le⟩, rfl⟩
  have hfinal : iterate S.f n (S.f x.val) = y := by
    rw [← iterate_succ_left]
    exact x.property.2
  have hne : ∀ k, S.f x.val ≠ S.vertex k := by
    intro k heq
    have hvertex : y = S.vertex (iterate S.next n k) := by
      rw [← hfinal, heq, S.iterate_vertex]
    exact S.interior_ne_vertex j y hy _ hvertex
  obtain ⟨k, hk⟩ := S.exists_interior_index (S.f x.val) hcore hne
  refine ⟨k, (S.row_preimage i k (S.f x.val) hk).mpr ?_, hk, hfinal⟩
  exact ⟨x.val, ⟨x.property.1.1.le, x.property.1.2.le⟩, rfl⟩

private theorem liftFiber_surjective (n : ℕ) (i j : Fin N) (y : ℝ)
    (hy : y ∈ openEdge S.vertex j) : Function.Surjective (S.liftFiber n i y) := by
  intro x
  obtain ⟨k, hr, hk, hfinal⟩ := S.fiber_successor_decomposition n i j y hy x
  let p : (k : {k : Fin N // S.row i k}) × S.Fiber n k.val y :=
    ⟨⟨k, hr⟩, ⟨S.f x.val, hk, hfinal⟩⟩
  refine ⟨p, Subtype.ext ?_⟩
  exact S.branch_injective i
    ⟨(S.liftFiber n i y p).property.1.1.le, (S.liftFiber n i y p).property.1.2.le⟩
    ⟨x.property.1.1.le, x.property.1.2.le⟩ (S.liftFiber_image n i y p)

private def successorFiberEquiv (n : ℕ) (i j : Fin N) (y : ℝ)
    (hy : y ∈ openEdge S.vertex j) :
    ((k : {k : Fin N // S.row i k}) × S.Fiber n k.val y) ≃ S.Fiber (n + 1) i y :=
  Equiv.ofBijective (S.liftFiber n i y)
    ⟨S.liftFiber_injective n i y, S.liftFiber_surjective n i j y hy⟩

private def zeroFiberEquiv (i j : Fin N) (y : ℝ) (hy : y ∈ openEdge S.vertex j) :
    PLift (i = j) ≃ S.Fiber 0 i y where
  toFun p := ⟨y, by simpa only [p.down] using hy, rfl⟩
  invFun x := ⟨S.interior_index_unique i j x.val x.property.1
    (by have hxy : x.val = y := x.property.2; rw [hxy]; exact hy)⟩
  left_inv _ := Subsingleton.elim _ _
  right_inv x := Subtype.ext x.property.2.symm

/-- A concrete equivalence between finite model paths and actual real
preimages, quantified over every finite horizon. -/
def pathFiberEquiv (n : ℕ) (i j : Fin N) (y : ℝ)
    (hy : y ∈ openEdge S.vertex j) : S.Paths n i j ≃ S.Fiber n i y :=
  match n with
  | 0 => S.zeroFiberEquiv i j y hy
  | n + 1 =>
      (Equiv.sigmaCongrRight fun k : {k : Fin N // S.row i k} =>
        pathFiberEquiv n k.val j y hy).trans
        (S.successorFiberEquiv n i j y hy)

/-- Finiteness of each actual fiber is a consequence of the equivalence. -/
theorem physical_fiber_finite (n : ℕ) (i j : Fin N) (y : ℝ)
    (hy : y ∈ openEdge S.vertex j) : Finite (S.Fiber n i y) := by
  letI := Fintype.ofEquiv (S.Paths n i j) (S.pathFiberEquiv n i j y hy)
  infer_instance

/-- Row-source natural-valued adjacency, with actual multiplicities 0 and 1. -/
def adjacency : Matrix (Fin N) (Fin N) ℕ := fun i j => if S.row i j then 1 else 0

/-- The recursively defined finite path count is exactly a matrix-power entry. -/
theorem paths_card_eq_matrix_power (n : ℕ) (i j : Fin N) :
    Fintype.card (S.Paths n i j) = (S.adjacency ^ n) i j := by
  induction n generalizing i with
  | zero =>
      by_cases h : i = j
      · subst j
        have hc : Fintype.card (S.Paths 0 i i) = 1 := by
          haveI : Unique (S.Paths 0 i i) := ⟨⟨⟨rfl⟩⟩, fun p => by cases p; rfl⟩
          exact Fintype.card_unique
        simpa using hc
      · haveI : IsEmpty (S.Paths 0 i j) := ⟨fun p => h p.down⟩
        simp [h]
  | succ n ih =>
      change Fintype.card ((k : {k : Fin N // S.row i k}) × S.Paths n k.val j) = _
      rw [Fintype.card_sigma, pow_succ', Matrix.mul_apply]
      simp_rw [ih]
      simp only [adjacency, ite_mul, one_mul, zero_mul]
      calc
        _ = ∑ k ∈ Finset.univ.filter (S.row i), (S.adjacency ^ n) k j :=
          (Finset.sum_subtype (p := S.row i) (Finset.univ.filter (S.row i))
            (by simp) (fun k : Fin N => (S.adjacency ^ n) k j)).symm
        _ = _ := by rw [Finset.sum_filter]

/-- Main realization theorem: a matrix-power entry counts actual distinct
real preimages of every target-interior point, at every finite horizon. -/
theorem physical_fiber_card_eq_matrix_power (n : ℕ) (i j : Fin N) (y : ℝ)
    (hy : y ∈ openEdge S.vertex j) :
    Nat.card (S.Fiber n i y) = (S.adjacency ^ n) i j := by
  calc
    Nat.card (S.Fiber n i y) = Nat.card (S.Paths n i j) :=
      (Nat.card_congr (S.pathFiberEquiv n i j y hy)).symm
    _ = Fintype.card (S.Paths n i j) := Nat.card_eq_fintype_card
    _ = (S.adjacency ^ n) i j := S.paths_card_eq_matrix_power n i j

/-- The actual inverse fiber restricted to the closed physical core. This
does not include real preimages lying outside that core. -/
def CoreFiber (n : ℕ) (y : ℝ) : Type :=
  {x : ℝ // x ∈ core S.vertex ∧ iterate S.f n x = y}

private def assembleFiber (n : ℕ) (y : ℝ)
    (p : (i : Fin N) × S.Fiber n i y) : S.CoreFiber n y :=
  ⟨p.2.val,
    ⟨(S.ordered.monotone (Fin.zero_le p.1.castSucc)).trans p.2.property.1.1.le,
      p.2.property.1.2.le.trans (S.ordered.monotone (Fin.le_last p.1.succ))⟩,
    p.2.property.2⟩

/-- The source-interior fibers partition the entire core fiber. A target
interior excludes every source vertex, even at horizon zero. -/
def coreFiberPartition (n : ℕ) (j : Fin N) (y : ℝ)
    (hy : y ∈ openEdge S.vertex j) :
    ((i : Fin N) × S.Fiber n i y) ≃ S.CoreFiber n y :=
  Equiv.ofBijective (S.assembleFiber n y) ⟨by
    rintro ⟨i, ⟨x, hx⟩⟩ ⟨k, ⟨z, hz⟩⟩ heq
    have hxz := congrArg (fun p : S.CoreFiber n y => p.val) heq
    change x = z at hxz
    subst z
    have hik := S.interior_index_unique i k x hx.1 hz.1
    subst k
    rfl, by
    intro x
    have hne : ∀ k, x.val ≠ S.vertex k := by
      intro k heq
      have hvertex : y = S.vertex (iterate S.next n k) := by
        rw [← x.property.2, heq, S.iterate_vertex]
      exact S.interior_ne_vertex j y hy _ hvertex
    obtain ⟨i, hi⟩ := S.exists_interior_index x.val x.property.1 hne
    exact ⟨⟨i, ⟨x.val, hi, x.property.2⟩⟩, Subtype.ext rfl⟩⟩

/-- Finite paths with arbitrary source and fixed target are exactly the
actual inverse fiber in the closed physical core. -/
def corePathFiberEquiv (n : ℕ) (j : Fin N) (y : ℝ)
    (hy : y ∈ openEdge S.vertex j) :
    ((i : Fin N) × S.Paths n i j) ≃ S.CoreFiber n y :=
  (Equiv.sigmaCongrRight fun i : Fin N => S.pathFiberEquiv n i j y hy).trans
    (S.coreFiberPartition n j y hy)

theorem core_fiber_finite (n : ℕ) (j : Fin N) (y : ℝ)
    (hy : y ∈ openEdge S.vertex j) : Finite (S.CoreFiber n y) := by
  letI := Fintype.ofEquiv ((i : Fin N) × S.Paths n i j) (S.corePathFiberEquiv n j y hy)
  infer_instance

/-- The column sum counts all distinct preimages in the closed physical
core. It makes no assertion about preimages outside this invariant core. -/
theorem core_fiber_card_eq_matrix_column_sum (n : ℕ) (j : Fin N) (y : ℝ)
    (hy : y ∈ openEdge S.vertex j) :
    Nat.card (S.CoreFiber n y) = ∑ i : Fin N, (S.adjacency ^ n) i j := by
  calc
    Nat.card (S.CoreFiber n y) = Nat.card ((i : Fin N) × S.Paths n i j) :=
      (Nat.card_congr (S.corePathFiberEquiv n j y hy)).symm
    _ = Fintype.card ((i : Fin N) × S.Paths n i j) := Nat.card_eq_fintype_card
    _ = ∑ i : Fin N, Fintype.card (S.Paths n i j) := Fintype.card_sigma
    _ = ∑ i : Fin N, (S.adjacency ^ n) i j := by
      apply Finset.sum_congr rfl
      intro i _
      exact S.paths_card_eq_matrix_power n i j

#print axioms pathFiberEquiv
#print axioms physical_fiber_finite
#print axioms paths_card_eq_matrix_power
#print axioms physical_fiber_card_eq_matrix_power
#print axioms coreFiberPartition
#print axioms corePathFiberEquiv
#print axioms core_fiber_finite
#print axioms core_fiber_card_eq_matrix_column_sum

end System
end
end LoopsRealMarkov
