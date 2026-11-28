import Mathlib

/-!
# Reciprocal shadowing for normalized quadratic flights

The exact normalized quadratic step is `u ↦ u + a * u^2`.
In the reciprocal coordinate its error from translation is quadratic in `a`.
The estimates below require a separated partial-sum path and a small square
sum, but place no bound on the sum of the absolute values of the coefficients.
-/

namespace LoopsQuadraticReciprocalFlight

noncomputable section

def forward (a : ℕ → ℂ) (u : ℂ) : ℕ → ℂ
  | 0 => u
  | n + 1 => forward a u n + a n * (forward a u n)^2

def reciprocal (a : ℕ → ℂ) (v : ℂ) : ℕ → ℂ
  | 0 => v
  | n + 1 => reciprocal a v n - a n + (a n)^2 / (reciprocal a v n + a n)

def driver (a : ℕ → ℂ) (v : ℂ) (n : ℕ) : ℂ :=
  v - ∑ j ∈ Finset.range n, a j

def energy (a : ℕ → ℂ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ‖a j‖^2

theorem energy_nonneg (a : ℕ → ℂ) (n : ℕ) : 0 ≤ energy a n := by
  exact Finset.sum_nonneg (fun j _ => sq_nonneg ‖a j‖)

theorem energy_mono (a : ℕ → ℂ) {n N : ℕ} (hn : n ≤ N) :
    energy a n ≤ energy a N := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
    (by intro j hj hnj; exact sq_nonneg ‖a j‖)

theorem coefficient_square_le_energy (a : ℕ → ℂ) {j N : ℕ} (hj : j < N) :
    ‖a j‖^2 ≤ energy a N := by
  exact Finset.single_le_sum (fun i _ => sq_nonneg ‖a i‖)
    (Finset.mem_range.mpr hj)

theorem coefficient_le_of_energy (a : ℕ → ℂ) {δ : ℝ} (hδ : 0 < δ)
    {j N : ℕ} (hj : j < N) (hE : energy a N ≤ δ^2 / 16) :
    ‖a j‖ ≤ δ / 4 := by
  have hs := (coefficient_square_le_energy a hj).trans hE
  have hn := norm_nonneg (a j)
  nlinarith

private theorem norm_driver_le (v w a : ℂ) :
    ‖w‖ ≤ ‖v + a‖ + ‖v - w‖ + ‖a‖ := by
  calc
    ‖w‖ = ‖((v + a) - (v - w)) - a‖ := by congr 1 <;> ring
    _ ≤ ‖(v + a) - (v - w)‖ + ‖a‖ := norm_sub_le _ _
    _ ≤ ‖v + a‖ + ‖v - w‖ + ‖a‖ :=
      add_le_add_right (norm_sub_le _ _) _

private theorem error_small {δ E e : ℝ} (hδ : 0 < δ)
    (hE : E ≤ δ^2 / 16) (he : e ≤ (2 / δ) * E) : e ≤ δ / 8 := by
  calc
    e ≤ (2 / δ) * E := he
    _ ≤ (2 / δ) * (δ^2 / 16) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = δ / 8 := by field_simp [ne_of_gt hδ] <;> ring

/-- Finite reciprocal shadowing. The number of steps is unrestricted. -/
theorem reciprocal_shadow (a : ℕ → ℂ) (v : ℂ) (N : ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ n ≤ N, δ ≤ ‖driver a v n‖)
    (hE : energy a N ≤ δ^2 / 16) :
    ∀ n ≤ N,
      ‖reciprocal a v n - driver a v n‖ ≤ (2 / δ) * energy a n := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [reciprocal, driver, energy]
  | succ n ih =>
    intro hn
    have hnN : n ≤ N := by omega
    have hnlt : n < N := by omega
    have herr := ih hnN
    have hEn : energy a n ≤ δ^2 / 16 := (energy_mono a hnN).trans hE
    have hsmall := error_small hδ hEn herr
    have ha := coefficient_le_of_energy a hδ hnlt hE
    have ht := norm_driver_le (reciprocal a v n) (driver a v n) (a n)
    have hdn := hsep n hnN
    have hden : δ / 2 ≤ ‖reciprocal a v n + a n‖ := by linarith
    have hrem : ‖(a n)^2 / (reciprocal a v n + a n)‖ ≤
        (2 / δ) * ‖a n‖^2 := by
      calc
        ‖(a n)^2 / (reciprocal a v n + a n)‖ =
            ‖a n‖^2 / ‖reciprocal a v n + a n‖ := by
          rw [norm_div, norm_pow]
        _ ≤ ‖a n‖^2 / (δ / 2) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
        _ = (2 / δ) * ‖a n‖^2 := by field_simp [ne_of_gt hδ] <;> ring
    have hstep : reciprocal a v (n + 1) - driver a v (n + 1) =
        (reciprocal a v n - driver a v n) +
          (a n)^2 / (reciprocal a v n + a n) := by
      simp only [reciprocal, driver, Finset.sum_range_succ]
      ring
    rw [hstep]
    calc
      ‖(reciprocal a v n - driver a v n) +
          (a n)^2 / (reciprocal a v n + a n)‖ ≤
          ‖reciprocal a v n - driver a v n‖ +
            ‖(a n)^2 / (reciprocal a v n + a n)‖ := norm_add_le _ _
      _ ≤ (2 / δ) * energy a n + (2 / δ) * ‖a n‖^2 :=
        add_le_add herr hrem
      _ = (2 / δ) * energy a (n + 1) := by
        simp only [energy, Finset.sum_range_succ]
        ring

/-- The same hypotheses keep every reciprocal orbit point away from zero. -/
theorem reciprocal_norm_lower (a : ℕ → ℂ) (v : ℂ) (N : ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ n ≤ N, δ ≤ ‖driver a v n‖)
    (hE : energy a N ≤ δ^2 / 16) (n : ℕ) (hn : n ≤ N) :
    δ / 2 ≤ ‖reciprocal a v n‖ := by
  have he := reciprocal_shadow a v N δ hδ hsep hE n hn
  have hsmall := error_small hδ ((energy_mono a hn).trans hE) he
  have ht := norm_sub_le (reciprocal a v n) (reciprocal a v n - driver a v n)
  have hnorm : ‖driver a v n‖ ≤
      ‖reciprocal a v n‖ + ‖reciprocal a v n - driver a v n‖ := by
    have hid : reciprocal a v n - (reciprocal a v n - driver a v n) =
        driver a v n := by ring
    rwa [hid] at ht
  have hd := hsep n hn
  linarith

/-- No pole is crossed by the reciprocal step under the separation hypotheses. -/
theorem reciprocal_denominator_lower (a : ℕ → ℂ) (v : ℂ) (N : ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ n ≤ N, δ ≤ ‖driver a v n‖)
    (hE : energy a N ≤ δ^2 / 16) (n : ℕ) (hn : n < N) :
    δ / 2 ≤ ‖reciprocal a v n + a n‖ := by
  have hnN : n ≤ N := Nat.le_of_lt hn
  have he := reciprocal_shadow a v N δ hδ hsep hE n hnN
  have hsmall := error_small hδ ((energy_mono a hnN).trans hE) he
  have ha := coefficient_le_of_energy a hδ hn hE
  have ht := norm_driver_le (reciprocal a v n) (driver a v n) (a n)
  have hd := hsep n hnN
  linarith

/-- Exact coordinate change for the quadratic step; this is an identity of
the actual maps, not a truncation of their Taylor expansions. -/
theorem reciprocal_step_inverse (a v : ℂ) (hv : v ≠ 0) (hva : v + a ≠ 0) :
    (v - a + a^2 / (v + a))⁻¹ = v⁻¹ + a * (v⁻¹)^2 := by
  have hid : v - a + a^2 / (v + a) = v^2 / (v + a) := by
    field_simp [hva]
    ring
  rw [hid, inv_div]
  field_simp [hv]
  ring

/-- The reciprocal orbit is the inverse of the exact normalized quadratic
flight throughout the controlled finite interval. -/
theorem inverse_reciprocal_eq_forward (a : ℕ → ℂ) (v : ℂ) (N : ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ n ≤ N, δ ≤ ‖driver a v n‖)
    (hE : energy a N ≤ δ^2 / 16) :
    ∀ n ≤ N, (reciprocal a v n)⁻¹ = forward a v⁻¹ n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hnN : n ≤ N := by omega
    have hnlt : n < N := by omega
    have hl := reciprocal_norm_lower a v N δ hδ hsep hE n hnN
    have hd := reciprocal_denominator_lower a v N δ hδ hsep hE n hnlt
    have hv : reciprocal a v n ≠ 0 := norm_pos_iff.mp (by linarith)
    have hva : reciprocal a v n + a n ≠ 0 := norm_pos_iff.mp (by linarith)
    simpa only [reciprocal, forward, ih hnN] using
      reciprocal_step_inverse (a n) (reciprocal a v n) hv hva

/-- Explicit approximation by the reciprocal translation, hence by a
parabolic Möbius map. It uses only the square sum and the separated driver. -/
theorem forward_mobius_shadow (a : ℕ → ℂ) (v : ℂ) (N : ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ n ≤ N, δ ≤ ‖driver a v n‖)
    (hE : energy a N ≤ δ^2 / 16) (n : ℕ) (hn : n ≤ N) :
    ‖forward a v⁻¹ n - (driver a v n)⁻¹‖ ≤
      (4 / δ^3) * energy a n := by
  have herr := reciprocal_shadow a v N δ hδ hsep hE n hn
  have hl := reciprocal_norm_lower a v N δ hδ hsep hE n hn
  have hd := hsep n hn
  have hv : reciprocal a v n ≠ 0 := norm_pos_iff.mp (by linarith)
  have hw : driver a v n ≠ 0 := norm_pos_iff.mp (by linarith)
  have hprod : δ^2 / 2 ≤ ‖reciprocal a v n‖ * ‖driver a v n‖ := by
    have hmul := mul_le_mul hl hd (by positivity : (0 : ℝ) ≤ δ)
      (norm_nonneg (reciprocal a v n))
    nlinarith
  rw [← inverse_reciprocal_eq_forward a v N δ hδ hsep hE n hn]
  have hid : (reciprocal a v n)⁻¹ - (driver a v n)⁻¹ =
      (driver a v n - reciprocal a v n) /
        (reciprocal a v n * driver a v n) := by
    field_simp [hv, hw]
    ring
  rw [hid, norm_div, norm_mul, norm_sub_rev]
  calc
    ‖reciprocal a v n - driver a v n‖ /
        (‖reciprocal a v n‖ * ‖driver a v n‖) ≤
        ‖reciprocal a v n - driver a v n‖ / (δ^2 / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hprod
    _ ≤ ((2 / δ) * energy a n) / (δ^2 / 2) :=
      div_le_div_of_nonneg_right herr (by positivity)
    _ = (4 / δ^3) * energy a n := by field_simp [ne_of_gt hδ] <;> ring

end
end LoopsQuadraticReciprocalFlight
