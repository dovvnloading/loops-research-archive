import CompactBinaryCoding
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative generating partitions

A compact binary splitting need not distinguish points. Expansion within
each actual branch supplies the missing metric argument: common prefixes
force exponential closeness, and the existing surjective address map
becomes a homeomorphism conjugating the dynamics with the full shift.
-/

namespace LoopsExpandingBinaryCoding

open Function Set LoopsCompactBinaryCoding

variable {X : Type*} [MetricSpace X]

/-- Expansion on one branch propagates through every common finite prefix. -/
theorem prefix_expansion (e : X ≃ₜ (Fin 2 × X))
    (hexpand : ∀ x y, (e x).1 = (e y).1 →
      2 * dist x y ≤ dist (step e x) (step e y))
    (n : ℕ) (x y : X)
    (hprefix : ∀ k < n, address e x k = address e y k) :
    (2 : ℝ)^n * dist x y ≤ dist ((step e)^[n] x) ((step e)^[n] y) := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    have hfirst : (e x).1 = (e y).1 := hprefix 0 (Nat.zero_lt_succ n)
    have htail : ∀ k < n, address e (step e x) k = address e (step e y) k := by
      intro k hk
      rw [← address_succ, ← address_succ]
      exact hprefix (k+1) (Nat.succ_lt_succ hk)
    calc
      (2 : ℝ)^(n+1) * dist x y = 2^n * (2 * dist x y) := by ring
      _ ≤ 2^n * dist (step e x) (step e y) :=
        mul_le_mul_of_nonneg_left (hexpand x y hfirst) (by positivity)
      _ ≤ dist ((step e)^[n] (step e x)) ((step e)^[n] (step e y)) :=
        ih (step e x) (step e y) htail
      _ = dist ((step e)^[n+1] x) ((step e)^[n+1] y) := by
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]

/-- A global physical diameter bound gives an explicit cylinder estimate. -/
theorem prefix_dist_bound (e : X ≃ₜ (Fin 2 × X))
    (hexpand : ∀ x y, (e x).1 = (e y).1 →
      2 * dist x y ≤ dist (step e x) (step e y))
    (D : ℝ) (hdiam : ∀ x y : X, dist x y ≤ D)
    (n : ℕ) (x y : X)
    (hprefix : ∀ k < n, address e x k = address e y k) :
    dist x y ≤ D / (2 : ℝ)^n := by
  apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr
  calc
    dist x y * (2 : ℝ)^n = (2 : ℝ)^n * dist x y := mul_comm _ _
    _ ≤ dist ((step e)^[n] x) ((step e)^[n] y) :=
      prefix_expansion e hexpand n x y hprefix
    _ ≤ D := hdiam _ _

/-- The expansion hypothesis is sufficient for point uniqueness;
compactness is not needed for this direction. -/
theorem expanding_address_injective (e : X ≃ₜ (Fin 2 × X))
    (hexpand : ∀ x y, (e x).1 = (e y).1 →
      2 * dist x y ≤ dist (step e x) (step e y))
    (D : ℝ) (hdiam : ∀ x y : X, dist x y ≤ D) :
    Injective (address e) := by
  intro x y hxy
  by_contra hne
  have hd : 0 < dist x y := dist_pos.mpr hne
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (D / dist x y)
    (by norm_num : (1 : ℝ) < 2)
  have hlarge : D < (2 : ℝ)^n * dist x y := (div_lt_iff₀ hd).mp hn
  have hsmall := (prefix_expansion e hexpand n x y
    (fun k _ => congrFun hxy k)).trans (hdiam _ _)
  exact (not_lt_of_ge hsmall) hlarge

/-- The existing compactness realization and proved metric injectivity
upgrade the binary factor to an actual topological conjugacy. -/
theorem expanding_binary_conjugacy [CompactSpace X] [Nonempty X]
    (e : X ≃ₜ (Fin 2 × X))
    (hexpand : ∀ x y, (e x).1 = (e y).1 →
      2 * dist x y ≤ dist (step e x) (step e y))
    (D : ℝ) (hdiam : ∀ x y : X, dist x y ≤ D) :
    ∃ h : X ≃ₜ (ℕ → Fin 2),
      (∀ x, h x = address e x) ∧ Semiconj h (step e) shift := by
  let E : X ≃ (ℕ → Fin 2) := Equiv.ofBijective (address e)
    ⟨expanding_address_injective e hexpand D hdiam, address_surjective e⟩
  let h : X ≃ₜ (ℕ → Fin 2) :=
    E.toHomeomorphOfContinuousClosed (address_continuous e)
      (address_continuous e).isClosedMap
  exact ⟨h, fun _ => rfl, address_semiconj e⟩

/-- Each complete address is the intersection of its finite cylinders
at exactly one point. The statement includes every infinite address. -/
theorem prefix_intersection_singleton [CompactSpace X] [Nonempty X]
    (e : X ≃ₜ (Fin 2 × X))
    (hexpand : ∀ x y, (e x).1 = (e y).1 →
      2 * dist x y ≤ dist (step e x) (step e y))
    (D : ℝ) (hdiam : ∀ x y : X, dist x y ≤ D)
    (a : ℕ → Fin 2) :
    ∃ x : X, (⋂ n, prefixCylinder e a n) = {x} := by
  obtain ⟨x, hx⟩ := address_surjective e a
  refine ⟨x, ?_⟩
  ext y
  constructor
  · intro hy
    apply mem_singleton_iff.mpr
    apply expanding_address_injective e hexpand D hdiam
    funext k
    rw [hx]
    exact (mem_iInter.mp hy (k+1)) k (Nat.lt_succ_self k)
  · rintro rfl
    apply mem_iInter.mpr
    intro n k _
    exact congrFun hx k

end LoopsExpandingBinaryCoding
