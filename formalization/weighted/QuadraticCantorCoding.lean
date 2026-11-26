import QuadraticCantorSplitting
import QuadraticCantorExpansion
import ExpandingBinaryCoding
import BinaryShiftCensus

/-!
# Quantitative point coding for the actual quadratic filled set

For every complex parameter of norm at least eight, an explicitly constructed
geometric partition gives a topological conjugacy of the actual bounded-orbit
set with the full one-sided binary shift. Its filled-set cylinders shrink at a
uniform exponential rate. Periodic points are counted and approximate every
bounded orbit with the same quantitative error.

These are cylinders inside the filled set, not exterior puzzle neighborhoods
or prime-end traces.
-/

namespace QuadraticCantor

open Set Function QuadraticEscape LoopsCompactBinaryCoding
open LoopsExpandingBinaryCoding LoopsBinaryShiftCensus

noncomputable section

/-- The domain is precisely the bounded-orbit set of the actual polynomial. -/
theorem filled_iff_bounded_orbit (c z : ℂ) :
    z ∈ filled c ↔ ∃ B : ℝ, ∀ n : ℕ, ‖orbit c n z‖ ≤ B :=
  escape_zero_iff_bounded c z

/-- The subtype dynamics is exactly the existing complex orbit recurrence. -/
theorem filledMap_iterate (c : ℂ) (n : ℕ) (x : filled c) :
    ((filledMap c)^[n] x : ℂ) = orbit c n (x : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (((filledMap c)^[n] x : ℂ)^2+c) = (orbit c n (x : ℂ))^2+c
    rw [ih]

theorem filledMap_periodic_iff (c : ℂ) (n : ℕ) (x : filled c) :
    (filledMap c)^[n] x = x ↔ orbit c n (x : ℂ) = (x : ℂ) := by
  rw [Subtype.ext_iff, filledMap_iterate]

/-- A common physical diameter bound for the entire filled set. -/
theorem filled_dist_bound (c : ℂ) (hc : 8 ≤ ‖c‖) (x y : filled c) :
    dist x y ≤ ‖c‖ := by
  change dist (x : ℂ) (y : ℂ) ≤ ‖c‖
  rw [dist_eq_norm]
  have hx := norm_bound hc x.property
  have hy := norm_bound hc y.property
  exact (norm_sub_le _ _).trans (by linarith)

/-- The generating physical partition gives point coding with an explicit
common-prefix estimate, not merely a surjective symbolic factor. -/
theorem filled_conjugacy_exists (c : ℂ) (hc : 8 ≤ ‖c‖) :
    ∃ h : filled c ≃ₜ (ℕ → Fin 2),
      Semiconj h (filledMap c) shift ∧
      ∀ (n : ℕ) (x y : filled c),
        (∀ k < n, h x k = h y k) → dist x y ≤ ‖c‖ / (2 : ℝ)^n := by
  letI : CompactSpace (filled c) := isCompact_iff_compactSpace.mp (filled_compact c)
  letI : Nonempty (filled c) := (filled_nonempty c).to_subtype
  obtain ⟨e, he, hexpand⟩ := expanding_two_sheet c hc
  have hstep : step e = filledMap c := funext he
  have hmetric : ∀ x y, (e x).1 = (e y).1 →
      2 * dist x y ≤ dist (step e x) (step e y) := by
    simpa only [hstep] using hexpand
  obtain ⟨h, haddress, hsemi⟩ :=
    expanding_binary_conjugacy e hmetric ‖c‖ (filled_dist_bound c hc)
  refine ⟨h, ?_, ?_⟩
  · simpa only [hstep] using hsemi
  · intro n x y hp
    apply prefix_dist_bound e hmetric ‖c‖ (filled_dist_bound c hc) n x y
    intro k hk
    simpa only [haddress] using hp k hk

/-- A selected homeomorphism whose existence is proved above. -/
def coding (c : ℂ) (hc : 8 ≤ ‖c‖) : filled c ≃ₜ (ℕ → Fin 2) :=
  (filled_conjugacy_exists c hc).choose

theorem coding_semiconj (c : ℂ) (hc : 8 ≤ ‖c‖) :
    Semiconj (coding c hc) (filledMap c) shift :=
  (filled_conjugacy_exists c hc).choose_spec.1

theorem coding_prefix_bound (c : ℂ) (hc : 8 ≤ ‖c‖)
    (n : ℕ) (x y : filled c)
    (hp : ∀ k < n, coding c hc x k = coding c hc y k) :
    dist x y ≤ ‖c‖ / (2 : ℝ)^n :=
  (filled_conjugacy_exists c hc).choose_spec.2 n x y hp

/-- Every infinite address has exactly one actual bounded-orbit point. -/
theorem unique_point_of_address (c : ℂ) (hc : 8 ≤ ‖c‖) (a : ℕ → Fin 2) :
    ∃! z : filled c, coding c hc z = a := by
  refine ⟨(coding c hc).symm a, (coding c hc).apply_symm_apply a, ?_⟩
  intro z hz
  apply (coding c hc).injective
  simpa using hz

/-- The nested cylinders for any address meet in precisely its coded point. -/
theorem physical_cylinder_intersection (c : ℂ) (hc : 8 ≤ ‖c‖)
    (a : ℕ → Fin 2) :
    (⋂ n : ℕ, {z : filled c | ∀ k < n, coding c hc z k = a k}) =
      {(coding c hc).symm a} := by
  ext z
  constructor
  · intro hz
    apply mem_singleton_iff.mpr
    apply (coding c hc).injective
    rw [(coding c hc).apply_symm_apply]
    funext k
    exact (mem_iInter.mp hz (k+1)) k (Nat.lt_succ_self k)
  · rintro rfl
    simp

/-- Every physical connected component is a single point. -/
theorem filled_totally_disconnected (c : ℂ) (hc : 8 ≤ ‖c‖) :
    IsTotallyDisconnected (filled c) := by
  apply totallyDisconnectedSpace_subtype_iff.mp
  exact (coding c hc).isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- Iterate fixed-point equations transport in both directions. -/
theorem coding_fixed_iff (c : ℂ) (hc : 8 ≤ ‖c‖) (n : ℕ) (x : filled c) :
    (filledMap c)^[n] x = x ↔ shift^[n] (coding c hc x) = coding c hc x := by
  have h := (coding_semiconj c hc).iterate_right n x
  constructor
  · intro hx
    rw [← h, hx]
  · intro hx
    apply (coding c hc).injective
    exact h.trans hx

/-- Points fixed by the n-th physical iterate correspond exactly to
binary words of length n. This counts period dividing n, not least period n. -/
theorem filled_periodic_point_count (c : ℂ) (hc : 8 ≤ ‖c‖)
    (n : ℕ) (hn : 0 < n) :
    Nat.card {x : filled c // (filledMap c)^[n] x = x} = 2^n := by
  let E : {x : filled c // (filledMap c)^[n] x = x} ≃
      {a : ℕ → Fin 2 // shift^[n] a = a} :=
    (coding c hc).toEquiv.subtypeEquiv (coding_fixed_iff c hc n)
  exact (Nat.card_congr E).trans (fixed_point_card n hn)

/-- The census counts every complex solution of the actual iterate equation.
Periodicity itself supplies boundedness, so no solutions are omitted. -/
theorem complex_periodic_point_count (c : ℂ) (hc : 8 ≤ ‖c‖)
    (n : ℕ) (hn : 0 < n) :
    Nat.card {z : ℂ // orbit c n z = z} = 2^n := by
  let E : {x : filled c // (filledMap c)^[n] x = x} ≃
      {z : ℂ // orbit c n z = z} :=
    { toFun := fun x => ⟨(x.val : ℂ), (filledMap_periodic_iff c n x.val).mp x.property⟩
      invFun := fun z =>
        ⟨⟨z.val, periodic_mem_filled hn z.property⟩,
          (filledMap_periodic_iff c n _).mpr z.property⟩
      left_inv := fun _ => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun _ => by apply Subtype.ext; rfl }
  exact (Nat.card_congr E).symm.trans (filled_periodic_point_count c hc n hn)

/-- Every positive least period occurs for the actual polynomial. -/
theorem filled_exact_period_exists (c : ℂ) (hc : 8 ≤ ‖c‖)
    (n : ℕ) (hn : 0 < n) :
    ∃ x : filled c, (filledMap c)^[n] x = x ∧
      ∀ m, 0 < m → m < n → (filledMap c)^[m] x ≠ x := by
  obtain ⟨a, ha, hleast⟩ := exact_period_exists n hn
  refine ⟨(coding c hc).symm a, ?_, ?_⟩
  · apply (coding_fixed_iff c hc n _).mpr
    simpa only [(coding c hc).apply_symm_apply] using ha
  · intro m hm hmn hx
    apply hleast m hm hmn
    simpa only [(coding c hc).apply_symm_apply] using
      (coding_fixed_iff c hc m _).mp hx

/-- Every positive least period is realized in the complex plane by a
repelling orbit of the actual quadratic polynomial. -/
theorem complex_exact_period_repelling (c : ℂ) (hc : 8 ≤ ‖c‖)
    (n : ℕ) (hn : 0 < n) :
    ∃ z : ℂ, orbit c n z = z ∧
      (∀ m, 0 < m → m < n → orbit c m z ≠ z) ∧
      1 < ‖deriv (orbit c n) z‖ := by
  obtain ⟨x, hx, hleast⟩ := filled_exact_period_exists c hc n hn
  have hp := (filledMap_periodic_iff c n x).mp hx
  refine ⟨(x : ℂ), hp, ?_, periodic_repelling hc hn hp⟩
  intro m hm hmn h
  exact hleast m hm hmn ((filledMap_periodic_iff c m x).mpr h)

/-- Repeating an initial itinerary gives a genuine periodic point with
an explicit Euclidean approximation error at every positive length. -/
theorem periodic_approximation (c : ℂ) (hc : 8 ≤ ‖c‖)
    (x : filled c) (n : ℕ) (hn : 0 < n) :
    ∃ y : filled c, (filledMap c)^[n] y = y ∧
      dist x y ≤ ‖c‖ / (2 : ℝ)^n := by
  obtain ⟨b, hb, hprefix⟩ := periodic_extension (coding c hc x) n hn
  refine ⟨(coding c hc).symm b, ?_, ?_⟩
  · apply (coding_fixed_iff c hc n _).mpr
    simpa only [(coding c hc).apply_symm_apply] using hb
  · apply coding_prefix_bound c hc n
    intro k hk
    rw [(coding c hc).apply_symm_apply]
    exact (hprefix k hk).symm

/-- Periodic points are dense in the actual bounded-orbit set. -/
theorem filled_periodic_points_dense (c : ℂ) (hc : 8 ≤ ‖c‖) :
    Dense {x : filled c | ∃ n : ℕ, 0 < n ∧ (filledMap c)^[n] x = x} := by
  have hd := periodic_points_dense.preimage (coding c hc).isOpenMap
  convert hd using 1
  ext x
  simp only [mem_setOf_eq, mem_preimage, coding_fixed_iff c hc]

end

end QuadraticCantor
