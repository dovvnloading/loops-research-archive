import PathExcursionCensus

/-!
# Independent excursions with distinct geometric traces

The two choices at each position may be different loops from those at
the other positions. A marker belonging only to the positive loop at
its own position recovers that position's choice from the entire source
range. Hence binary words give distinct geometric source traces, not
merely distinct parametrizations, above one complete target path.
-/

namespace LoopsPathChoiceTraceCensus

open Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable section

/-- Concatenate an indexed family of binary choices. `true` selects
the positive path at its position. -/
def choiceConcatenation {x : X} : (n : ℕ) →
    (Fin n → Path x x) → (Fin n → Path x x) → (Fin n → Bool) → Path x x
  | 0, _, _, _ => Path.refl x
  | n + 1, α, β, w => (if w 0 then α 0 else β 0).trans
      (choiceConcatenation n (Fin.tail α) (Fin.tail β) (Fin.tail w))

/-- Concatenate the fixed indexed target paths with the same timing. -/
def sequenceConcatenation {x : X} : (n : ℕ) → (Fin n → Path x x) → Path x x
  | 0, _ => Path.refl x
  | n + 1, γ => (γ 0).trans (sequenceConcatenation n (Fin.tail γ))

/-- Exact membership in the full source trace of a chosen word. -/
theorem mem_choiceConcatenation_range {x : X} (n : ℕ)
    (α β : Fin n → Path x x) (w : Fin n → Bool) (z : X) :
    z ∈ range (choiceConcatenation n α β w) ↔
      z = x ∨ ∃ i, z ∈ range ((if w i then α i else β i) : Path x x) := by
  induction n with
  | zero =>
    simpa [choiceConcatenation, Path.refl] using (eq_comm : x = z ↔ z = x)
  | succ n ih =>
    change z ∈ range ((if w 0 then α 0 else β 0).trans
      (choiceConcatenation n (Fin.tail α) (Fin.tail β) (Fin.tail w))) ↔ _
    rw [Path.trans_range, mem_union, ih]
    constructor
    · rintro (hhead | hbase | ⟨i, hi⟩)
      · exact Or.inr ⟨0, hhead⟩
      · exact Or.inl hbase
      · exact Or.inr ⟨i.succ, hi⟩
    · rintro (hbase | ⟨i, hi⟩)
      · exact Or.inr (Or.inl hbase)
      · revert hi
        refine Fin.cases (fun hi => Or.inl hi) (fun j hi => ?_) i
        exact Or.inr (Or.inr ⟨j, hi⟩)

/-- The range is the union of all chosen excursion ranges and the
base point, including the empty word case. -/
theorem choiceConcatenation_range {x : X} (n : ℕ)
    (α β : Fin n → Path x x) (w : Fin n → Bool) :
    range (choiceConcatenation n α β w) =
      {x} ∪ ⋃ i : Fin n, range ((if w i then α i else β i) : Path x x) := by
  ext z
  simpa only [mem_union, mem_singleton_iff, mem_iUnion] using
    mem_choiceConcatenation_range n α β w z

/-- Source containment persists for every complete choice word. -/
theorem choiceConcatenation_range_subset {x : X} (n : ℕ)
    (α β : Fin n → Path x x) (A : Set X) (hxA : x ∈ A)
    (hα : ∀ i, range (α i) ⊆ A) (hβ : ∀ i, range (β i) ⊆ A)
    (w : Fin n → Bool) : range (choiceConcatenation n α β w) ⊆ A := by
  intro z hz
  rcases (mem_choiceConcatenation_range n α β w z).mp hz with rfl | ⟨i, hi⟩
  · exact hxA
  · cases hw : w i <;> simp only [hw, Bool.false_eq_true, if_false, if_true] at hi
    · exact hβ i hi
    · exact hα i hi

/-- Equality of the two full target paths at each position gives one
fixed complete target path for all binary choice words. -/
theorem choiceConcatenation_map {x : X} (n : ℕ)
    (α β : Fin n → Path x x) (f : X → Y) (hf : Continuous f)
    (hsame : ∀ i, (α i).map hf = (β i).map hf) (w : Fin n → Bool) :
    (choiceConcatenation n α β w).map hf =
      sequenceConcatenation n (fun i => (α i).map hf) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((if w 0 then α 0 else β 0).trans
      (choiceConcatenation n (Fin.tail α) (Fin.tail β) (Fin.tail w))).map hf =
      ((α 0).map hf).trans
        (sequenceConcatenation n (fun i => (α i.succ).map hf))
    rw [Path.map_trans, ih (Fin.tail α) (Fin.tail β) (fun i => hsame i.succ)]
    cases w 0 <;> simp [hsame 0, Fin.tail]

/-- Every position's choice is readable from its marker in the whole
geometric source trace. Absence from the negative loop at the same
position already excludes the common base point. -/
theorem marker_mem_choice_range {x : X} (n : ℕ)
    (α β : Fin n → Path x x) (marker : Fin n → X)
    (hpositive : ∀ i j, marker j ∈ range (α i) ↔ i = j)
    (hnegative : ∀ i j, marker j ∉ range (β i))
    (w : Fin n → Bool) (j : Fin n) :
    marker j ∈ range (choiceConcatenation n α β w) ↔ w j = true := by
  have hbase : marker j ≠ x := by
    intro he
    exact hnegative j j ⟨0, (β j).source.trans he.symm⟩
  rw [mem_choiceConcatenation_range]
  constructor
  · rintro (h | ⟨i, hi⟩)
    · exact (hbase h).elim
    · by_cases hw : w i = true
      · rw [if_pos hw] at hi
        have hij := (hpositive i j).mp hi
        simpa only [hij] using hw
      · rw [if_neg hw] at hi
        exact (hnegative i j hi).elim
  · intro hw
    refine Or.inr ⟨j, ?_⟩
    rw [if_pos hw]
    exact (hpositive j j).mpr rfl

/-- Distinct binary words have distinct entire source range sets.
Consequently they cannot differ merely by a reparametrization. -/
theorem choice_range_injective {x : X} (n : ℕ)
    (α β : Fin n → Path x x) (marker : Fin n → X)
    (hpositive : ∀ i j, marker j ∈ range (α i) ↔ i = j)
    (hnegative : ∀ i j, marker j ∉ range (β i)) :
    Injective (fun w => range (choiceConcatenation n α β w)) := by
  intro u v h
  change range (choiceConcatenation n α β u) = range (choiceConcatenation n α β v) at h
  funext j
  have hh : u j = true ↔ v j = true := by
    rw [← marker_mem_choice_range n α β marker hpositive hnegative u j,
      ← marker_mem_choice_range n α β marker hpositive hnegative v j, h]
  cases hu : u j <;> cases hv : v j <;> simp_all

/-- A single target path has a family of source lifts whose complete
geometric traces encode every binary word. -/
theorem distinct_trace_lift_family {x : X} (n : ℕ)
    (α β : Fin n → Path x x) (A : Set X) (hxA : x ∈ A)
    (hα : ∀ i, range (α i) ⊆ A) (hβ : ∀ i, range (β i) ⊆ A)
    (marker : Fin n → X)
    (hpositive : ∀ i j, marker j ∈ range (α i) ↔ i = j)
    (hnegative : ∀ i j, marker j ∉ range (β i))
    (f : X → Y) (hf : Continuous f)
    (hsame : ∀ i, (α i).map hf = (β i).map hf) :
    ∃ γ : Path (f x) (f x), ∃ L : (Fin n → Bool) → Path x x,
      (∀ w t, f (L w t) = γ t) ∧
      (∀ w, range (L w) ⊆ A) ∧ Injective (fun w => range (L w)) := by
  refine ⟨sequenceConcatenation n (fun i => (α i).map hf),
    choiceConcatenation n α β, ?_, ?_, ?_⟩
  · intro w t
    exact congrArg (fun p : Path (f x) (f x) => p t)
      (choiceConcatenation_map n α β f hf hsame w)
  · exact choiceConcatenation_range_subset n α β A hxA hα hβ
  · exact choice_range_injective n α β marker hpositive hnegative

/-- There are exactly `2^n` different geometric source traces in the
constructed finite family, all realized by lifts of one target path. -/
theorem finite_distinct_trace_census {x : X} (n : ℕ)
    (α β : Fin n → Path x x) (A : Set X) (hxA : x ∈ A)
    (hα : ∀ i, range (α i) ⊆ A) (hβ : ∀ i, range (β i) ⊆ A)
    (marker : Fin n → X)
    (hpositive : ∀ i j, marker j ∈ range (α i) ↔ i = j)
    (hnegative : ∀ i j, marker j ∉ range (β i))
    (f : X → Y) (hf : Continuous f)
    (hsame : ∀ i, (α i).map hf = (β i).map hf) :
    ∃ γ : Path (f x) (f x), ∃ S : Finset (Set X), S.card = 2 ^ n ∧
      ∀ C ∈ S, C ⊆ A ∧ ∃ δ : Path x x, range δ = C ∧ ∀ t, f (δ t) = γ t := by
  classical
  obtain ⟨γ, L, hmap, hrange, hinj⟩ :=
    distinct_trace_lift_family n α β A hxA hα hβ marker hpositive hnegative f hf hsame
  refine ⟨γ, Finset.univ.image (fun w => range (L w)), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp
  · intro C hC
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨hrange w, L w, rfl, hmap w⟩

private def halfTime : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

private def leftHalf {x y : X} (δ : Path x y) : Path x (δ halfTime) where
  toFun t := δ.extend ((t : ℝ) / 2)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simpa [halfTime] using δ.extend_extends' halfTime

private def rightHalf {x y : X} (δ : Path x y) : Path (δ halfTime) y where
  toFun t := δ.extend (((t : ℝ) + 1) / 2)
  continuous_toFun := by fun_prop
  source' := by simpa [halfTime] using δ.extend_extends' halfTime
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

/-- Exhaustion of all based lifts for a position-dependent sequence
of two-lift excursions. The singleton base fiber forces each joint. -/
theorem choiceConcatenation_exhaustive {x : X} (n : ℕ)
    (α β : Fin n → Path x x) (A : Set X) (f : X → Y) (hf : Continuous f)
    (hbase : ∀ z ∈ A, f z = f x → z = x)
    (hclass : ∀ i (δ : Path x x), range δ ⊆ A → δ.map hf = (α i).map hf →
      δ = α i ∨ δ = β i)
    (δ : Path x x) (hδ : range δ ⊆ A)
    (hmap : δ.map hf = sequenceConcatenation n (fun i => (α i).map hf)) :
    ∃ w : Fin n → Bool, δ = choiceConcatenation n α β w := by
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
      exact he.trans (trans_midpoint ((α 0).map hf)
        (sequenceConcatenation n (fun i => (α i.succ).map hf)))
    obtain ⟨δ₀, δ₁, hsplit, hδ₀, hδ₁⟩ := split_based_loop δ hmid A hδ
    have himages : δ₀.map hf = (α 0).map hf ∧
        δ₁.map hf = sequenceConcatenation n (fun i => (α i.succ).map hf) := by
      apply (LoopsPathExcursionCensus.trans_eq_iff _ _ _ _).mp
      rw [← Path.map_trans, hsplit]
      exact hmap
    obtain ⟨w, hw⟩ := ih (Fin.tail α) (Fin.tail β)
      (fun i => hclass i.succ) δ₁ hδ₁ himages.2
    rcases hclass 0 δ₀ hδ₀ himages.1 with he | he
    · refine ⟨Fin.cons true w, ?_⟩
      rw [← hsplit, he, hw]
      simp [choiceConcatenation]
    · refine ⟨Fin.cons false w, ?_⟩
      rw [← hsplit, he, hw]
      simp [choiceConcatenation]

/-- Every continuous lift, without prescribed source endpoints, is
one complete binary word. Its endpoints follow from the singleton fiber. -/
theorem continuous_choiceConcatenation_exhaustive {x : X} (n : ℕ)
    (α β : Fin n → Path x x) (A : Set X) (f : X → Y) (hf : Continuous f)
    (hbase : ∀ z ∈ A, f z = f x → z = x)
    (hclass : ∀ i (δ : Path x x), range δ ⊆ A → δ.map hf = (α i).map hf →
      δ = α i ∨ δ = β i)
    (δ : C(unitInterval, X)) (hδ : range δ ⊆ A)
    (hmap : ∀ t, f (δ t) = sequenceConcatenation n (fun i => (α i).map hf) t) :
    ∃ w : Fin n → Bool, δ = (choiceConcatenation n α β w).toContinuousMap := by
  let γ := sequenceConcatenation n (fun i => (α i).map hf)
  have hzero : δ 0 = x := hbase _ (hδ (mem_range_self 0)) ((hmap 0).trans γ.source)
  have hone : δ 1 = x := hbase _ (hδ (mem_range_self 1)) ((hmap 1).trans γ.target)
  let p : Path x x := ⟨δ, hzero, hone⟩
  have hp : p.map hf = γ := by
    apply Path.ext
    funext t
    exact hmap t
  obtain ⟨w, hw⟩ := choiceConcatenation_exhaustive n α β A f hf hbase hclass p hδ hp
  exact ⟨w, congrArg Path.toContinuousMap hw⟩

/-- Exact count of all continuous lifts for separated position-wise
excursions, with no prior finiteness assumption on the lift space. -/
theorem continuous_choice_lift_card_exact {x : X} (n : ℕ)
    (α β : Fin n → Path x x) (A : Set X) (hxA : x ∈ A)
    (hα : ∀ i, range (α i) ⊆ A) (hβ : ∀ i, range (β i) ⊆ A)
    (marker : Fin n → X)
    (hpositive : ∀ i j, marker j ∈ range (α i) ↔ i = j)
    (hnegative : ∀ i j, marker j ∉ range (β i))
    (f : X → Y) (hf : Continuous f)
    (hsame : ∀ i, (α i).map hf = (β i).map hf)
    (hbase : ∀ z ∈ A, f z = f x → z = x)
    (hclass : ∀ i (δ : Path x x), range δ ⊆ A → δ.map hf = (α i).map hf →
      δ = α i ∨ δ = β i) :
    Nat.card {δ : C(unitInterval, X) // range δ ⊆ A ∧
      ∀ t, f (δ t) = sequenceConcatenation n (fun i => (α i).map hf) t} = 2 ^ n := by
  let γ := sequenceConcatenation n (fun i => (α i).map hf)
  let L := {δ : C(unitInterval, X) // range δ ⊆ A ∧ ∀ t, f (δ t) = γ t}
  let E : (Fin n → Bool) → L := fun w =>
    ⟨(choiceConcatenation n α β w).toContinuousMap,
      choiceConcatenation_range_subset n α β A hxA hα hβ w,
      fun t => congrArg (fun p : Path (f x) (f x) => p t)
        (choiceConcatenation_map n α β f hf hsame w)⟩
  have hi : Injective E := by
    intro u v huv
    apply choice_range_injective n α β marker hpositive hnegative
    exact congrArg (fun δ : L => range δ.val) huv
  have hs : Surjective E := by
    intro δ
    obtain ⟨w, hw⟩ := continuous_choiceConcatenation_exhaustive n α β A f hf
      hbase hclass δ.val δ.property.1 δ.property.2
    exact ⟨w, Subtype.ext hw.symm⟩
  change Nat.card L = _
  rw [← Nat.card_congr (Equiv.ofBijective E ⟨hi, hs⟩)]
  simp

/-- Exact count of all geometric source trace sets, not merely a
selected finite subfamily or a count of parametrizations. -/
theorem all_trace_card_exact {x : X} (n : ℕ)
    (α β : Fin n → Path x x) (A : Set X) (hxA : x ∈ A)
    (hα : ∀ i, range (α i) ⊆ A) (hβ : ∀ i, range (β i) ⊆ A)
    (marker : Fin n → X)
    (hpositive : ∀ i j, marker j ∈ range (α i) ↔ i = j)
    (hnegative : ∀ i j, marker j ∉ range (β i))
    (f : X → Y) (hf : Continuous f)
    (hsame : ∀ i, (α i).map hf = (β i).map hf)
    (hbase : ∀ z ∈ A, f z = f x → z = x)
    (hclass : ∀ i (δ : Path x x), range δ ⊆ A → δ.map hf = (α i).map hf →
      δ = α i ∨ δ = β i) :
    Nat.card {C : Set X // ∃ δ : C(unitInterval, X), range δ = C ∧ range δ ⊆ A ∧
      ∀ t, f (δ t) = sequenceConcatenation n (fun i => (α i).map hf) t} = 2 ^ n := by
  let γ := sequenceConcatenation n (fun i => (α i).map hf)
  let T := {C : Set X // ∃ δ : C(unitInterval, X), range δ = C ∧
    range δ ⊆ A ∧ ∀ t, f (δ t) = γ t}
  let E : (Fin n → Bool) → T := fun w =>
    ⟨range (choiceConcatenation n α β w),
      (choiceConcatenation n α β w).toContinuousMap, rfl,
      choiceConcatenation_range_subset n α β A hxA hα hβ w,
      fun t => congrArg (fun p : Path (f x) (f x) => p t)
        (choiceConcatenation_map n α β f hf hsame w)⟩
  have hi : Injective E := by
    intro u v huv
    exact choice_range_injective n α β marker hpositive hnegative
      (congrArg Subtype.val huv)
  have hs : Surjective E := by
    intro C
    obtain ⟨δ, hrange, hδ, hmap⟩ := C.property
    obtain ⟨w, hw⟩ := continuous_choiceConcatenation_exhaustive n α β A f hf
      hbase hclass δ hδ hmap
    refine ⟨w, Subtype.ext ?_⟩
    exact (congrArg (fun δ : C(unitInterval, X) => range δ) hw).symm.trans hrange
  change Nat.card T = _
  rw [← Nat.card_congr (Equiv.ofBijective E ⟨hi, hs⟩)]
  simp

end

end LoopsPathChoiceTraceCensus
