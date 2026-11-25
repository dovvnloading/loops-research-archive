import Mathlib

/-!
# Finite prefix bookkeeping for the stationary potential charge

The written analytic source is
research/independent_audits/stationary_transport_attack_20261124/PREFIX_POTENTIAL_CHARGE.md.
This file proves the finite orbit implications and quadratic weight algebra.
The compact filled sets, physical encounters, conformal energy identities
and uniform Dirichlet response calibration are separate analytic inputs.
-/

namespace LoopsStationaryPrefixCharge

open scoped BigOperators

/-- Forward orbit, with the first forward step taken before the remaining
recursive orbit. -/
def forward {K : Type*} (F : K → K) : ℕ → K → K
  | 0, x => x
  | n+1, x => forward F n (F x)

/-- Selected inverse iterates. Only the inverse identities on the
specified sets are used; the function may be extended arbitrarily outside. -/
def backward {K : Type*} (φ : K → K) : ℕ → K → K
  | 0, x => x
  | n+1, x => φ (backward φ n x)

def deepSet {K : Type*} (φ : K → K) (C : Set K) (n : ℕ) : Set K :=
  {x | ∃ y ∈ C, backward φ n y = x}

/-- Every orbit remaining in the critical set through time n lies in the
n-th selected inverse image, without any assumption of finite cardinality. -/
theorem recover_critical_stay {K : Type*} (F φ : K → K) (C : Set K)
    (hinv : ∀ x ∈ C, F x ∈ C → φ (F x) = x)
    (n : ℕ) (x : K)
    (hstay : ∀ j ≤ n, forward F j x ∈ C) :
    backward φ n (forward F n x) = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hshift : ∀ j ≤ n, forward F j (F x) ∈ C := by
      intro j hj
      exact hstay (j+1) (Nat.succ_le_succ hj)
    have h0 : x ∈ C := hstay 0 (Nat.zero_le _)
    have h1 : F x ∈ C := hstay 1 (Nat.succ_le_succ (Nat.zero_le n))
    change φ (backward φ n (forward F n (F x))) = x
    rw [ih (F x) hshift]
    exact hinv x h0 h1

/-- Disjointness from the selected inverse nest gives a bounded exit
for EVERY point of T, not only for its marked vertices. -/
theorem critical_exit {K : Type*} (F φ : K → K) (C T : Set K)
    (hinv : ∀ x ∈ C, F x ∈ C → φ (F x) = x)
    (b : ℕ) (havoid : ∀ x ∈ T, x ∉ deepSet φ C b)
    (x : K) (hx : x ∈ T) :
    ∃ j ≤ b, forward F j x ∉ C := by
  classical
  by_contra hno
  have hstay : ∀ j ≤ b, forward F j x ∈ C := by
    intro j hj
    by_contra hbad
    exact hno ⟨j, hj, hbad⟩
  exact (havoid x hx) ⟨forward F b x, hstay b le_rfl,
    recover_critical_stay F φ C hinv b x hstay⟩

/-- Iterating the inverse branch on its invariant set stays in that set. -/
theorem backward_mem {K : Type*} (φ : K → K) (C : Set K)
    (hbranch : ∀ y ∈ C, φ y ∈ C)
    (n : ℕ) (y : K) (hy : y ∈ C) :
    backward φ n y ∈ C := by
  induction n with
  | zero => exact hy
  | succ n ih => exact hbranch _ ih

/-- The first j forward steps cancel the last j selected inverse steps. -/
theorem forward_prefix_deep {K : Type*} (F φ : K → K) (C : Set K)
    (hbranch : ∀ y ∈ C, φ y ∈ C ∧ F (φ y) = y)
    (j n : ℕ) (y : K) (hy : y ∈ C) :
    forward F j (backward φ (n+j) y) = backward φ n y := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hm : backward φ (n+j) y ∈ C :=
      backward_mem φ C (fun z hz => (hbranch z hz).1) (n+j) y hy
    change forward F j (F (φ (backward φ (n+j) y))) = backward φ n y
    rw [(hbranch _ hm).2, ih]

/-- Every proper prefix of a deep encounter lies in the first inverse
image. For the analytic application C can be the closed critical limb. -/
theorem deep_prefix_first {K : Type*} (F φ : K → K) (C : Set K)
    (hbranch : ∀ y ∈ C, φ y ∈ C ∧ F (φ y) = y)
    (j n : ℕ) (hj : j < n) (y : K) (hy : y ∈ C) :
    forward F j (backward φ n y) ∈ deepSet φ C 1 := by
  let k := n-j-1
  have hn : n = k+1+j := by dsimp [k]; omega
  rw [hn, forward_prefix_deep F φ C hbranch j (k+1) y hy]
  exact ⟨backward φ k y,
    backward_mem φ C (fun z hz => (hbranch z hz).1) k y hy, rfl⟩

/-- Exact sum of the actual degrees at prefix times 0 through b. -/
theorem prefix_degree_sum (b : ℕ) :
    (∑ j ∈ Finset.range (b+1), (2 : ℝ)^j) = (2 : ℝ)^(b+1)-1 := by
  induction b with
  | zero => norm_num
  | succ b ih =>
    change (∑ j ∈ Finset.range ((b+1)+1), (2 : ℝ)^j) =
      (2 : ℝ)^((b+1)+1)-1
    rw [Finset.sum_range_succ, ih, pow_succ (2 : ℝ) (b+1)]
    ring

/-- The one-quarter energy factor, including the identity prefix j=0. -/
theorem common_prefix_energy (b : ℕ) (E : ℝ) :
    (∑ j ∈ Finset.range (b+1), (1/2 : ℝ)^2 * ((2 : ℝ)^j * E)) =
      ((2 : ℝ)^(b+1)-1)*E/4 := by
  calc
    _ = ∑ j ∈ Finset.range (b+1), (2 : ℝ)^j * (E/4) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [← Finset.sum_mul, prefix_degree_sum]; ring

/-- Each parent supplies two directional prefix indices; they may agree. -/
def pairCovered {J L : Type*} (left right : L → J) (s : J → ℝ) : Prop :=
  ∀ a, 1 ≤ s (left a) + s (right a)

/-- Constant half-weights always supply one total unit of length. -/
theorem half_pair_cover {J L : Type*} (left right : L → J) :
    pairCovered left right (fun _ => (1/2 : ℝ)) := by
  intro a
  norm_num

/-- If every index is realized by a same-index pair, every feasible
amplitude is at least one half. -/
theorem self_pair_forces_half {J L : Type*} (left right : L → J)
    (s : J → ℝ) (hc : pairCovered left right s)
    (hself : ∀ j, ∃ a, left a = j ∧ right a = j) (j : J) :
    (1/2 : ℝ) ≤ s j := by
  obtain ⟨a, hl, hr⟩ := hself j
  have h := hc a
  rw [hl, hr] at h
  linarith

/-- The uniform half choice minimizes quadratic cost in the worst-case
index set allowing every same-index pair. No analytic sharpness is claimed. -/
theorem half_minimal {J L : Type*} [Fintype J] (left right : L → J)
    (s c : J → ℝ) (hc : pairCovered left right s)
    (hself : ∀ j, ∃ a, left a = j ∧ right a = j)
    (hn : ∀ j, 0 ≤ c j) :
    (∑ j, (1/2 : ℝ)^2 * c j) ≤ ∑ j, (s j)^2 * c j := by
  apply Finset.sum_le_sum
  intro j _
  have hj := self_pair_forces_half left right s hc hself j
  have hs : (1/2 : ℝ)^2 ≤ (s j)^2 := by
    nlinarith [sq_nonneg (s j - (1/2 : ℝ))]
  exact mul_le_mul_of_nonneg_right hs (hn j)

/-- Two groups of positive cost with one encounter in each direction
give the exact series-energy lower bound for every feasible amplitude. -/
theorem series_weight_optimal (A B x y : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hxy : 1 ≤ x+y) :
    A*B/(A+B) ≤ A*x^2+B*y^2 := by
  have hsum : 0 < A+B := add_pos hA hB
  have hs : 1 ≤ (x+y)^2 := by
    nlinarith [sq_nonneg (x+y-1)]
  have hp := mul_le_mul_of_nonneg_left hs (mul_nonneg hA.le hB.le)
  have hsq := sq_nonneg (A*x-B*y)
  apply (div_le_iff₀ hsum).2
  nlinarith only [hp, hsq]

/-- The feasible optimal amplitudes attain the series-energy bound. -/
theorem series_weight_attained (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    0 ≤ B/(A+B) ∧ 0 ≤ A/(A+B) ∧
    B/(A+B)+A/(A+B) = 1 ∧
    A*(B/(A+B))^2+B*(A/(A+B))^2 = A*B/(A+B) := by
  have hp : 0 < A+B := add_pos hA hB
  have hn : A+B ≠ 0 := ne_of_gt hp
  refine ⟨div_nonneg hB.le hp.le, div_nonneg hA.le hp.le, ?_, ?_⟩
  · field_simp [hn] <;> ring
  · field_simp [hn] <;> ring

end LoopsStationaryPrefixCharge
