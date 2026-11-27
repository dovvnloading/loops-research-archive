import Mathlib.Topology.Path
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Independent choices at a common path endpoint

Two distinct based loops with identical images can be concatenated with
independent binary choices. For every finite length this constructs an
exactly counted family of distinct parametrized source paths over one
target path. The paths stay in the same declared source set.

The count concerns continuous paths, not homotopy classes, and places no
finiteness assumption on the entire space of lifts.
-/

namespace LoopsPathExcursionCensus

open Set Function unitInterval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable section

/-- The fixed half-time concatenation retains both complete path factors. -/
theorem trans_eq_iff {x y z : X} (α α' : Path x y) (β β' : Path y z) :
    α.trans β = α'.trans β' ↔ α = α' ∧ β = β' := by
  constructor
  · intro h
    constructor
    · apply Path.ext
      funext t
      have ht : (t : ℝ) / 2 ≤ 1 / 2 := by linarith [t.property.2]
      have he := congrArg (fun p : Path x z => p.extend ((t : ℝ) / 2)) h
      rw [Path.extend_trans_of_le_half α β ht,
        Path.extend_trans_of_le_half α' β' ht] at he
      have hscale : 2 * ((t : ℝ) / 2) = (t : ℝ) := by ring
      simpa only [hscale, Path.extend_extends'] using he
    · apply Path.ext
      funext t
      have ht : 1 / 2 ≤ ((t : ℝ) + 1) / 2 := by linarith [t.property.1]
      have he := congrArg (fun p : Path x z => p.extend (((t : ℝ) + 1) / 2)) h
      rw [Path.extend_trans_of_half_le α β ht,
        Path.extend_trans_of_half_le α' β' ht] at he
      have hscale : 2 * (((t : ℝ) + 1) / 2) - 1 = (t : ℝ) := by ring
      simpa only [hscale, Path.extend_extends'] using he
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A fixed parenthesization of a finite word of based loops. -/
def binaryConcatenation {x : X} (α β : Path x x) :
    (n : ℕ) → (Fin n → Bool) → Path x x
  | 0, _ => Path.refl x
  | n + 1, w => (if w 0 then β else α).trans
      (binaryConcatenation α β n (Fin.tail w))

/-- The identical parenthesization with just one loop at every position. -/
def repeatLoop {x : X} (α : Path x x) : ℕ → Path x x
  | 0 => Path.refl x
  | n + 1 => α.trans (repeatLoop α n)

/-- No binary word is lost by concatenation, even if the loops retrace
their images or have arbitrarily complicated individual paths. -/
theorem binaryConcatenation_injective {x : X} (α β : Path x x)
    (hne : α ≠ β) (n : ℕ) : Injective (binaryConcatenation α β n) := by
  induction n with
  | zero =>
    intro u v _
    exact Subsingleton.elim _ _
  | succ n ih =>
    intro u v h
    have hs := (trans_eq_iff (if u 0 then β else α) (if v 0 then β else α)
      (binaryConcatenation α β n (Fin.tail u))
      (binaryConcatenation α β n (Fin.tail v))).mp h
    have hhead : u 0 = v 0 := by
      cases hu : u 0 <;> cases hv : v 0 <;> simp_all
    have htail : Fin.tail u = Fin.tail v := ih hs.2
    rw [← Fin.cons_self_tail u, ← Fin.cons_self_tail v, hhead, htail]

/-- All concatenations remain in the original source set. -/
theorem binaryConcatenation_range {x : X} (α β : Path x x)
    (A : Set X) (hα : range α ⊆ A) (hβ : range β ⊆ A)
    (n : ℕ) (w : Fin n → Bool) :
    range (binaryConcatenation α β n w) ⊆ A := by
  induction n with
  | zero =>
    rintro _ ⟨t, rfl⟩
    exact hα ⟨0, α.source⟩
  | succ n ih =>
    change range ((if w 0 then β else α).trans
      (binaryConcatenation α β n (Fin.tail w))) ⊆ A
    rw [Path.trans_range]
    apply union_subset
    · cases w 0 <;> simp only [Bool.false_eq_true, if_false, if_true]
      · exact hα
      · exact hβ
    · exact ih (Fin.tail w)

/-- Identical full images of the two loops give one full target path
for every binary word of the same length. -/
theorem binaryConcatenation_map {x : X} (α β : Path x x)
    (f : X → Y) (hf : Continuous f) (hsame : α.map hf = β.map hf)
    (n : ℕ) (w : Fin n → Bool) :
    (binaryConcatenation α β n w).map hf = repeatLoop (α.map hf) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((if w 0 then β else α).trans
      (binaryConcatenation α β n (Fin.tail w))).map hf =
      (α.map hf).trans (repeatLoop (α.map hf) n)
    rw [Path.map_trans, ih]
    cases w 0 <;> simp [hsame]

/-- Every finite number of common-endpoint excursions supplies exactly
`2^n` distinct continuous source paths above one target path. This is a
finite subfamily count, and remains valid if there are further lifts. -/
theorem finite_binary_lift_family {x : X} (α β : Path x x)
    (A : Set X) (hα : range α ⊆ A) (hβ : range β ⊆ A)
    (hne : α ≠ β) (f : X → Y) (hf : Continuous f)
    (hsame : α.map hf = β.map hf) (n : ℕ) :
    ∃ γ : Path (f x) (f x), ∃ S : Finset (Path x x),
      S.card = 2 ^ n ∧ ∀ δ ∈ S, range δ ⊆ A ∧ δ.map hf = γ := by
  classical
  refine ⟨repeatLoop (α.map hf) n,
    Finset.univ.image (binaryConcatenation α β n), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (binaryConcatenation_injective α β hne n)]
    simp
  · intro δ hδ
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hδ
    exact ⟨binaryConcatenation_range α β A hα hβ n w,
      binaryConcatenation_map α β f hf hsame n w⟩

private def halfTime : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

private def leftHalf {x y : X} (δ : Path x y) : Path x (δ halfTime) where
  toFun t := δ.extend ((t : ℝ) / 2)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by
    simpa [halfTime] using δ.extend_extends' halfTime

private def rightHalf {x y : X} (δ : Path x y) : Path (δ halfTime) y where
  toFun t := δ.extend (((t : ℝ) + 1) / 2)
  continuous_toFun := by fun_prop
  source' := by
    simpa [halfTime] using δ.extend_extends' halfTime
  target' := by norm_num [Path.extend_one]

private theorem halves_trans {x y : X} (δ : Path x y) :
    (leftHalf δ).trans (rightHalf δ) = δ := by
  ext t
  rw [Path.trans_apply]
  split_ifs
  · change δ.extend (2 * (t : ℝ) / 2) = δ t
    have he : 2 * (t : ℝ) / 2 = (t : ℝ) := by ring
    rw [he, Path.extend_extends']
  · change δ.extend ((2 * (t : ℝ) - 1 + 1) / 2) = δ t
    have he : (2 * (t : ℝ) - 1 + 1) / 2 = (t : ℝ) := by ring
    rw [he, Path.extend_extends']

private theorem half_range {x y : X} (δ : Path x y) :
    range (leftHalf δ) ⊆ range δ ∧ range (rightHalf δ) ⊆ range δ := by
  have he := congrArg (fun p : Path x y => range p) (halves_trans δ)
  rw [Path.trans_range] at he
  exact ⟨fun z hz => he ▸ Or.inl hz, fun z hz => he ▸ Or.inr hz⟩

private theorem trans_midpoint {x y z : X} (α : Path x y) (β : Path y z) :
    (α.trans β) halfTime = y := by
  rw [Path.trans_apply, dif_pos (by norm_num [halfTime])]
  convert α.target using 1
  congr 1
  apply Subtype.ext
  norm_num [halfTime]

private theorem split_based_loop {x : X} (δ : Path x x)
    (hmid : δ halfTime = x) (A : Set X) (hδ : range δ ⊆ A) :
    ∃ δ₀ δ₁ : Path x x, δ₀.trans δ₁ = δ ∧
      range δ₀ ⊆ A ∧ range δ₁ ⊆ A := by
  let δ₀ : Path x x := (leftHalf δ).cast rfl hmid.symm
  let δ₁ : Path x x := (rightHalf δ).cast hmid.symm rfl
  refine ⟨δ₀, δ₁, ?_, ?_, ?_⟩
  · apply Path.ext
    funext t
    exact congrArg (fun p : Path x x => p t) (halves_trans δ)
  · exact (half_range δ).1.trans hδ
  · exact (half_range δ).2.trans hδ

/-- If the base point has only one source preimage in the declared set
and every one-excursion lift is one of the two chosen loops, every lift
of the repeated target is one complete binary concatenation. No finite
fiber assertion for the entire path space is assumed. -/
theorem binaryConcatenation_exhaustive {x : X} (α β : Path x x)
    (A : Set X) (f : X → Y) (hf : Continuous f)
    (hbase : ∀ z ∈ A, f z = f x → z = x)
    (hclass : ∀ δ : Path x x, range δ ⊆ A → δ.map hf = α.map hf →
      δ = α ∨ δ = β)
    (n : ℕ) (δ : Path x x) (hδ : range δ ⊆ A)
    (hmap : δ.map hf = repeatLoop (α.map hf) n) :
    ∃ w : Fin n → Bool, δ = binaryConcatenation α β n w := by
  induction n generalizing δ with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    apply Path.ext
    funext t
    apply hbase (δ t) (hδ (mem_range_self t))
    exact congrArg (fun p : Path (f x) (f x) => p t) hmap
  | succ n ih =>
    have hmid : δ halfTime = x := by
      apply hbase (δ halfTime) (hδ (mem_range_self halfTime))
      have he := congrArg (fun p : Path (f x) (f x) => p halfTime) hmap
      exact he.trans (trans_midpoint (α.map hf) (repeatLoop (α.map hf) n))
    obtain ⟨δ₀, δ₁, hsplit, hδ₀, hδ₁⟩ := split_based_loop δ hmid A hδ
    have himages : δ₀.map hf = α.map hf ∧
        δ₁.map hf = repeatLoop (α.map hf) n := by
      apply (trans_eq_iff _ _ _ _).mp
      rw [← Path.map_trans, hsplit]
      exact hmap
    obtain ⟨w, hw⟩ := ih δ₁ hδ₁ himages.2
    rcases hclass δ₀ hδ₀ himages.1 with he | he
    · refine ⟨Fin.cons false w, ?_⟩
      rw [← hsplit, he, hw]
      simp [binaryConcatenation]
    · refine ⟨Fin.cons true w, ?_⟩
      rw [← hsplit, he, hw]
      simp [binaryConcatenation]

/-- The exact number of all continuous based lifts is `2^n` when the
single excursion has exactly the two chosen lifts and the common
critical endpoint has a singleton source fiber. -/
theorem binary_lift_card_exact {x : X} (α β : Path x x)
    (A : Set X) (hα : range α ⊆ A) (hβ : range β ⊆ A)
    (hne : α ≠ β) (f : X → Y) (hf : Continuous f)
    (hsame : α.map hf = β.map hf)
    (hbase : ∀ z ∈ A, f z = f x → z = x)
    (hclass : ∀ δ : Path x x, range δ ⊆ A → δ.map hf = α.map hf →
      δ = α ∨ δ = β) (n : ℕ) :
    Nat.card {δ : Path x x // range δ ⊆ A ∧
      δ.map hf = repeatLoop (α.map hf) n} = 2 ^ n := by
  let E : (Fin n → Bool) → {δ : Path x x // range δ ⊆ A ∧
      δ.map hf = repeatLoop (α.map hf) n} :=
    fun w => ⟨binaryConcatenation α β n w,
      binaryConcatenation_range α β A hα hβ n w,
      binaryConcatenation_map α β f hf hsame n w⟩
  have hi : Injective E := by
    intro u v huv
    exact binaryConcatenation_injective α β hne n (congrArg Subtype.val huv)
  have hs : Surjective E := by
    intro δ
    obtain ⟨w, hw⟩ := binaryConcatenation_exhaustive α β A f hf hbase hclass
      n δ.val δ.property.1 δ.property.2
    exact ⟨w, Subtype.ext hw.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective E ⟨hi, hs⟩)]
  simp

/-- The same exact census for all continuous lifts, with no source
endpoint restrictions in the counted subtype. Their endpoints equal
the common source point because its target fiber is a singleton. -/
theorem continuous_binary_lift_card_exact {x : X} (α β : Path x x)
    (A : Set X) (hα : range α ⊆ A) (hβ : range β ⊆ A)
    (hne : α ≠ β) (f : X → Y) (hf : Continuous f)
    (hsame : α.map hf = β.map hf)
    (hbase : ∀ z ∈ A, f z = f x → z = x)
    (hclass : ∀ δ : Path x x, range δ ⊆ A → δ.map hf = α.map hf →
      δ = α ∨ δ = β) (n : ℕ) :
    Nat.card {δ : C(unitInterval, X) // range δ ⊆ A ∧
      ∀ t, f (δ t) = repeatLoop (α.map hf) n t} = 2 ^ n := by
  let γ := repeatLoop (α.map hf) n
  let P := {δ : Path x x // range δ ⊆ A ∧ δ.map hf = γ}
  let L := {δ : C(unitInterval, X) // range δ ⊆ A ∧ ∀ t, f (δ t) = γ t}
  let E : P → L := fun δ => ⟨δ.val.toContinuousMap, δ.property.1,
    fun t => congrArg (fun p : Path (f x) (f x) => p t) δ.property.2⟩
  have hi : Injective E := by
    intro u v huv
    apply Subtype.ext
    apply Path.ext
    funext t
    exact congrArg (fun δ : L => δ.val t) huv
  have hs : Surjective E := by
    intro δ
    have hzero : δ.val 0 = x := hbase _ (δ.property.1 (mem_range_self 0))
      ((δ.property.2 0).trans γ.source)
    have hone : δ.val 1 = x := hbase _ (δ.property.1 (mem_range_self 1))
      ((δ.property.2 1).trans γ.target)
    let p : Path x x := ⟨δ.val, hzero, hone⟩
    have hp : p.map hf = γ := by
      apply Path.ext
      funext t
      exact δ.property.2 t
    exact ⟨⟨p, δ.property.1, hp⟩, Subtype.ext rfl⟩
  change Nat.card L = _
  rw [← Nat.card_congr (Equiv.ofBijective E ⟨hi, hs⟩)]
  exact binary_lift_card_exact α β A hα hβ hne f hf hsame hbase hclass n

end

end LoopsPathExcursionCensus
