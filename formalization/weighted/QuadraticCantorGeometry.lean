import QuadraticEscape
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Explicit expanding branches for large quadratic parameters

All sets and estimates concern the zero locus of the actual quadratic
escape potential. For `8 ≤ ‖c‖`, the two disks about square roots of `-c`
separate this filled set, and the quadratic map expands distances by at
least two within each disk.
-/

namespace QuadraticCantor

open Set QuadraticEscape

/-- The actual bounded-orbit locus, using the constructed escape potential. -/
def filled (c : ℂ) : Set ℂ := {z | escape c z = 0}

/-- The closed disk used to label one of the two physical inverse branches. -/
def branchDisk (a : ℂ) : Set ℂ := {z | ‖z-a‖ ≤ ‖a‖ / 2}

theorem filled_forward {c z : ℂ} (hz : z ∈ filled c) : z^2+c ∈ filled c := by
  change escape c (z^2+c) = 0
  rw [escape_step, show escape c z = 0 from hz, mul_zero]

theorem filled_backward {c z : ℂ} (hz : z^2+c ∈ filled c) : z ∈ filled c := by
  change escape c z = 0
  have h : 2*escape c z = 0 := (escape_step c z).symm.trans hz
  linarith

theorem filled_step_iff (c z : ℂ) : z^2+c ∈ filled c ↔ z ∈ filled c :=
  ⟨filled_backward, filled_forward⟩

theorem escape_reflection (c z : ℂ) : escape c (-z) = escape c z := by
  have h := escape_step c (-z)
  have h' := escape_step c z
  simp only [neg_sq] at h
  linarith

theorem filled_reflection (c z : ℂ) : -z ∈ filled c ↔ z ∈ filled c := by
  simp only [filled, mem_setOf_eq, escape_reflection]

theorem exists_square_root (w : ℂ) : ∃ z : ℂ, z^2 = w := by
  refine ⟨w ^ (2⁻¹ : ℂ), ?_⟩
  exact Complex.cpow_nat_inv_pow w (by decide : (2 : ℕ) ≠ 0)

theorem exists_center (c : ℂ) : ∃ a : ℂ, a^2 = -c := exists_square_root (-c)

theorem norm_step_lower (c z : ℂ) : ‖z‖^2 ≤ ‖z^2+c‖ + ‖c‖ := by
  calc
    ‖z‖^2 = ‖(z^2+c)-c‖ := by rw [add_sub_cancel_right, norm_pow]
    _ ≤ _ := norm_sub_le _ _

/-- A first improvement of the escape-potential orbit bound. -/
theorem norm_bound_sub_one {c z : ℂ} (hc : 4 ≤ ‖c‖) (hz : z ∈ filled c) :
    ‖z‖ ≤ ‖c‖-1 := by
  have hb := escape_zero_orbit_bound c z hz 1
  simp only [orbit] at hb
  apply (sq_le_sq₀ (norm_nonneg z) (by linarith : 0 ≤ ‖c‖-1)).mp
  have hp : 0 ≤ ‖c‖ * (‖c‖-4) :=
    mul_nonneg (norm_nonneg c) (by linarith)
  nlinarith [norm_step_lower c z]

/-- Every point of the genuine filled set lies in the radius `‖c‖/2` disk.
The proof bootstraps the bound at the actual successor, without numerical
orbit sampling or a supplied escape-radius hypothesis. -/
theorem norm_bound {c z : ℂ} (hc : 8 ≤ ‖c‖) (hz : z ∈ filled c) :
    ‖z‖ ≤ ‖c‖/2 := by
  have hb := norm_bound_sub_one (c := c) (z := z^2+c) (by linarith) (filled_forward hz)
  apply (sq_le_sq₀ (norm_nonneg z) (by positivity : 0 ≤ ‖c‖/2)).mp
  have hp : 0 ≤ ‖c‖ * (‖c‖-8) :=
    mul_nonneg (norm_nonneg c) (by linarith)
  nlinarith [norm_step_lower c z]

theorem center_norm_sq {c a : ℂ} (ha : a^2 = -c) : ‖a‖^2 = ‖c‖ := by
  have h := congrArg norm ha
  simpa only [norm_pow, norm_neg] using h

theorem center_ne_zero {c a : ℂ} (hc : 8 ≤ ‖c‖) (ha : a^2 = -c) : a ≠ 0 := by
  intro hz
  have h := center_norm_sq ha
  simp only [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  linarith

theorem center_norm_ge_two {c a : ℂ} (hc : 8 ≤ ‖c‖) (ha : a^2 = -c) :
    2 ≤ ‖a‖ := by
  have h := center_norm_sq ha
  nlinarith [norm_nonneg a]

/-- The product of the two distances to the root centers is the norm
of the actual quadratic image. -/
theorem branch_distance_product {c a z : ℂ} (ha : a^2 = -c) :
    ‖z-a‖ * ‖z+a‖ = ‖z^2+c‖ := by
  rw [← norm_mul]
  congr 1
  calc
    (z-a)*(z+a) = z^2-a^2 := by ring
    _ = z^2+c := by rw [ha]; ring

/-- Every bounded point lies in one of the two explicitly separated disks. -/
theorem filled_disk_cover {c a z : ℂ} (hc : 8 ≤ ‖c‖) (ha : a^2 = -c)
    (hz : z ∈ filled c) : z ∈ branchDisk a ∨ z ∈ branchDisk (-a) := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr (center_ne_zero hc ha)
  have hs := center_norm_sq ha
  have hp : ‖z-a‖ * ‖z+a‖ ≤ ‖c‖/2 := by
    rw [branch_distance_product ha]
    exact norm_bound hc (filled_forward hz)
  have ht := norm_sub_le (z+a) (z-a)
  have he : (z+a)-(z-a) = (2 : ℂ)*a := by ring
  rw [he, norm_mul, Complex.norm_two] at ht
  by_cases h : ‖z-a‖ ≤ ‖z+a‖
  · left
    change ‖z-a‖ ≤ ‖a‖/2
    have hlarge : ‖a‖ ≤ ‖z+a‖ := by linarith
    have hm := mul_le_mul_of_nonneg_left hlarge (norm_nonneg (z-a))
    nlinarith
  · right
    change ‖z-(-a)‖ ≤ ‖-a‖/2
    simp only [sub_neg_eq_add, norm_neg]
    have hlarge : ‖a‖ ≤ ‖z-a‖ := by linarith
    have hm := mul_le_mul_of_nonneg_right hlarge (norm_nonneg (z+a))
    nlinarith

theorem branchDisk_reflection (a z : ℂ) :
    -z ∈ branchDisk (-a) ↔ z ∈ branchDisk a := by
  change ‖-z-(-a)‖ ≤ ‖-a‖/2 ↔ ‖z-a‖ ≤ ‖a‖/2
  have he : -z-(-a) = -(z-a) := by ring
  rw [he, norm_neg, norm_neg]

/-- Distinct branch labels are genuinely disjoint physical subsets. -/
theorem branchDisks_disjoint {a : ℂ} (ha : a ≠ 0) :
    Disjoint (branchDisk a) (branchDisk (-a)) := by
  apply Set.disjoint_left.mpr
  intro z hz hw
  change ‖z-a‖ ≤ ‖a‖/2 at hz
  change ‖z-(-a)‖ ≤ ‖-a‖/2 at hw
  simp only [sub_neg_eq_add, norm_neg] at hw
  have ht := norm_sub_le (z+a) (z-a)
  have he : (z+a)-(z-a) = (2 : ℂ)*a := by ring
  rw [he, norm_mul, Complex.norm_two] at ht
  have hp := norm_pos_iff.mpr ha
  linarith

theorem quadratic_fiber_iff (c z w : ℂ) :
    z^2+c = w^2+c ↔ z = w ∨ z = -w := by
  constructor
  · intro h
    have hm : (z-w)*(z+w) = 0 := by
      calc
        (z-w)*(z+w) = z^2-w^2 := by ring
        _ = 0 := sub_eq_zero.mpr (add_right_cancel h)
    rcases mul_eq_zero.mp hm with he | he
    · exact Or.inl (sub_eq_zero.mp he)
    · right
      linear_combination he
  · rintro (rfl | rfl)
    · rfl
    · simp

/-- One physical branch expands Euclidean distances by at least two. -/
theorem same_disk_expansion {c a z w : ℂ} (ha : 2 ≤ ‖a‖)
    (hz : z ∈ branchDisk a) (hw : w ∈ branchDisk a) :
    2*‖z-w‖ ≤ ‖(z^2+c)-(w^2+c)‖ := by
  change ‖z-a‖ ≤ ‖a‖/2 at hz
  change ‖w-a‖ ≤ ‖a‖/2 at hw
  have ht := norm_sub_le (z+w) ((z-a)+(w-a))
  have he : (z+w)-((z-a)+(w-a)) = (2 : ℂ)*a := by ring
  rw [he, norm_mul, Complex.norm_two] at ht
  have hsum := norm_add_le (z-a) (w-a)
  have hlower : 2 ≤ ‖z+w‖ := by linarith
  have heq : (z^2+c)-(w^2+c) = (z-w)*(z+w) := by ring
  rw [heq, norm_mul]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_right hlower (norm_nonneg (z-w))

end QuadraticCantor
