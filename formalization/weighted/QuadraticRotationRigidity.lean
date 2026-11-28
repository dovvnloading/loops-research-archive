import Mathlib

/-!
# Rigidity of a quadratic polynomial together with the standard quarter-turn

For arbitrary complex parameters c,d, a continuous injection that intertwines
z ↦ z²+c with z ↦ z²+d and commutes with z ↦ I*z forces c=d.
For c ≠ 0 the injection is the identity. The proof generates two independent
translation laws, bounds a continuous periodic error on a fundamental square,
and uses exact polynomial growth to eliminate the error.

The MLC implication on the actual bounded-critical-orbit locus is in the
companion module `QuadraticRotationMLC`.
-/

namespace LoopsQuadraticRotationRigidity

open Set Function

noncomputable section

theorem rotation_map_neg (h : ℂ → ℂ)
    (hrot : ∀ z : ℂ, h (Complex.I * z) = Complex.I * h z) (z : ℂ) :
    h (-z) = -h z := by
  calc
    h (-z) = h (Complex.I * (Complex.I * z)) := by
      congr 1
      simp [← mul_assoc]
    _ = Complex.I * h (Complex.I * z) := hrot _
    _ = Complex.I * (Complex.I * h z) := by rw [hrot]
    _ = -h z := by simp [← mul_assoc]

theorem rotation_map_zero (h : ℂ → ℂ)
    (hrot : ∀ z : ℂ, h (Complex.I * z) = Complex.I * h z) : h 0 = 0 := by
  have hn := rotation_map_neg h hrot 0
  simp only [neg_zero] at hn
  have hz : (2 : ℂ) * h 0 = 0 := by linear_combination hn
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem quadratic_map_parameter (h : ℂ → ℂ) (c d : ℂ)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = (h z) ^ 2 + d)
    (hrot : ∀ z : ℂ, h (Complex.I * z) = Complex.I * h z) : h c = d := by
  simpa [rotation_map_zero h hrot] using hquad 0

theorem quadratic_opposite_sum (h : ℂ → ℂ) (c d : ℂ)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = (h z) ^ 2 + d)
    (hrot : ∀ z : ℂ, h (Complex.I * z) = Complex.I * h z) (t : ℂ) :
    h (t + c) + h (-t + c) = 2 * d := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq t (by norm_num : 0 < (2 : ℕ))
  have h1 := hquad z
  have h2 := hquad (Complex.I * z)
  have hi (w : ℂ) : (Complex.I * w) ^ 2 = -(w ^ 2) := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hi, hrot, hi] at h2
  rw [hz] at h1 h2
  linear_combination h1 + h2

theorem quadratic_translate (h : ℂ → ℂ) (c d : ℂ)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = (h z) ^ 2 + d)
    (hrot : ∀ z : ℂ, h (Complex.I * z) = Complex.I * h z) (z : ℂ) :
    h (z + 2 * c) = h z + 2 * d := by
  have hs := quadratic_opposite_sum h c d hquad hrot (z + c)
  rw [show z + c + c = z + 2 * c by ring,
    show -(z + c) + c = -z by ring, rotation_map_neg h hrot] at hs
  linear_combination hs

theorem quadratic_translate_rotated (h : ℂ → ℂ) (c d : ℂ)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = (h z) ^ 2 + d)
    (hrot : ∀ z : ℂ, h (Complex.I * z) = Complex.I * h z) (z : ℂ) :
    h (z + 2 * (Complex.I * c)) = h z + 2 * (Complex.I * d) := by
  let u : ℂ := -Complex.I * z
  have hu : Complex.I * u = z := by
    dsimp [u]
    simp [← mul_assoc]
  calc
    h (z + 2 * (Complex.I * c)) = h (Complex.I * (u + 2 * c)) := by
      congr 1
      rw [mul_add, hu]
      ring
    _ = Complex.I * h (u + 2 * c) := hrot _
    _ = Complex.I * h u + 2 * (Complex.I * d) := by
      rw [quadratic_translate h c d hquad hrot]
      ring
    _ = h z + 2 * (Complex.I * d) := by rw [← hrot, hu]

theorem quadratic_nat_translate (h : ℂ → ℂ) (c d : ℂ)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = (h z) ^ 2 + d)
    (hrot : ∀ z : ℂ, h (Complex.I * z) = Complex.I * h z)
    (z : ℂ) (n : ℕ) :
    h (z + (n : ℂ) * (2 * c)) = h z + (n : ℂ) * (2 * d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      h (z + ((n + 1 : ℕ) : ℂ) * (2 * c)) =
          h ((z + (n : ℂ) * (2 * c)) + 2 * c) := by
        congr 1
        push_cast
        ring
      _ = h (z + (n : ℂ) * (2 * c)) + 2 * d :=
        quadratic_translate h c d hquad hrot _
      _ = h z + (n : ℂ) * (2 * d) + 2 * d := by rw [ih]
      _ = h z + ((n + 1 : ℕ) : ℂ) * (2 * d) := by
        push_cast
        ring

theorem quadratic_nat_multiple (h : ℂ → ℂ) (c d : ℂ)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = (h z) ^ 2 + d)
    (hrot : ∀ z : ℂ, h (Complex.I * z) = Complex.I * h z) (n : ℕ) :
    h ((n : ℂ) * (2 * c)) = (n : ℂ) * (2 * d) := by
  simpa [rotation_map_zero h hrot] using
    quadratic_nat_translate h c d hquad hrot 0 n

/-- A continuous complex function with periods one and `I` is bounded.
The proof reduces each real coordinate into the closed unit square. -/
theorem norm_bounded_of_periodic_one_I (g : ℂ → ℂ)
    (hg : Continuous g) (h₁ : Periodic g 1) (hI : Periodic g Complex.I) :
    ∃ B : ℝ, ∀ z : ℂ, ‖g z‖ ≤ B := by
  let F : ℝ × ℝ → ℂ := fun p => g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
  have hF : Continuous F := by
    exact hg.comp ((Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hK : IsCompact ((Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨B, fun z => ?_⟩
  have hx : Periodic (fun x : ℝ => g ((x : ℂ) + (z.im : ℂ) * Complex.I)) 1 := by
    intro x
    change g (((x + 1 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) =
      g ((x : ℂ) + (z.im : ℂ) * Complex.I)
    calc
      g (((x + 1 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) =
          g (((x : ℂ) + (z.im : ℂ) * Complex.I) + 1) := by
            congr 1
            push_cast
            ring
      _ = _ := h₁ _
  obtain ⟨x, hxmem, hxeq⟩ := hx.exists_mem_Ico₀ (by norm_num) z.re
  have hy : Periodic (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * Complex.I)) 1 := by
    intro y
    change g ((x : ℂ) + ((y + 1 : ℝ) : ℂ) * Complex.I) =
      g ((x : ℂ) + (y : ℂ) * Complex.I)
    calc
      g ((x : ℂ) + ((y + 1 : ℝ) : ℂ) * Complex.I) =
          g (((x : ℂ) + (y : ℂ) * Complex.I) + Complex.I) := by
            congr 1
            push_cast
            ring
      _ = _ := hI _
  obtain ⟨y, hymem, hyeq⟩ := hy.exists_mem_Ico₀ (by norm_num) z.im
  have heq : g z = F (x, y) := by
    calc
      g z = g ((z.re : ℂ) + (z.im : ℂ) * Complex.I) :=
        congrArg g (Complex.re_add_im z).symm
      _ = g ((x : ℂ) + (z.im : ℂ) * Complex.I) := hxeq
      _ = F (x, y) := hyeq
  rw [heq]
  exact hB (x, y) ⟨⟨hxmem.1, hxmem.2.le⟩, ⟨hymem.1, hymem.2.le⟩⟩

/-- A fixed complex coefficient with bounded natural multiples vanishes. -/
theorem eq_zero_of_nat_mul_norm_bounded (a : ℂ) (B : ℝ)
    (h : ∀ n : ℕ, ‖(n : ℂ) * a‖ ≤ B) : a = 0 := by
  by_contra ha
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  obtain ⟨n, hn⟩ := exists_nat_gt (B / ‖a‖)
  have hgt : B < (n : ℝ) * ‖a‖ := (div_lt_iff₀ hapos).mp hn
  have hb := h n
  rw [norm_mul, Complex.norm_natCast] at hb
  exact (not_lt_of_ge hb) hgt

/-- Bounded square-indexed multiples likewise force the coefficient to vanish. -/
theorem eq_zero_of_nat_sq_mul_norm_bounded (a : ℂ) (B : ℝ)
    (h : ∀ n : ℕ, ‖(n : ℂ) ^ 2 * a‖ ≤ B) : a = 0 := by
  apply eq_zero_of_nat_mul_norm_bounded a B
  intro n
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ m =>
      simp only [Nat.cast_succ]
      nlinarith [show 0 ≤ (m : ℝ) by positivity]
  calc
    ‖(n : ℂ) * a‖ = (n : ℝ) * ‖a‖ := by
      rw [norm_mul, Complex.norm_natCast]
    _ ≤ (n : ℝ) ^ 2 * ‖a‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg a)
    _ = ‖(n : ℂ) ^ 2 * a‖ := by
      rw [norm_mul, norm_pow, Complex.norm_natCast]
    _ ≤ B := h n


theorem map_eq_id_of_bounded_deviation (h : ℂ → ℂ) (c : ℂ)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = (h z) ^ 2 + c)
    (hrot : ∀ z : ℂ, h (Complex.I * z) = Complex.I * h z)
    (hc : c ≠ 0) (B : ℝ) (hB : ∀ z : ℂ, ‖h z - z‖ ≤ B) :
    h = id := by
  funext z
  have hb : ∀ n : ℕ, ‖(n : ℂ) * (4 * c * (h z - z))‖ ≤ 2 * B := by
    intro n
    have he : (h ((z + (n : ℂ) * (2 * c)) ^ 2 + c) -
          ((z + (n : ℂ) * (2 * c)) ^ 2 + c)) -
        (h (z ^ 2 + c) - (z ^ 2 + c)) =
        (n : ℂ) * (4 * c * (h z - z)) := by
      rw [hquad, hquad, quadratic_nat_translate h c c hquad hrot]
      ring
    calc
      ‖(n : ℂ) * (4 * c * (h z - z))‖ =
          ‖(h ((z + (n : ℂ) * (2 * c)) ^ 2 + c) -
              ((z + (n : ℂ) * (2 * c)) ^ 2 + c)) -
            (h (z ^ 2 + c) - (z ^ 2 + c))‖ := congrArg norm he.symm
      _ ≤ ‖h ((z + (n : ℂ) * (2 * c)) ^ 2 + c) -
              ((z + (n : ℂ) * (2 * c)) ^ 2 + c)‖ +
            ‖h (z ^ 2 + c) - (z ^ 2 + c)‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hB _) (hB _)
      _ = 2 * B := by ring
  have hk := eq_zero_of_nat_mul_norm_bounded (4 * c * (h z - z)) (2 * B) hb
  have hnc : (4 : ℂ) * c ≠ 0 := mul_ne_zero (by norm_num) hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hk).resolve_left hnc)


theorem scaled_deviation_bounded (h : ℂ → ℂ) (c d : ℂ)
    (hcont : Continuous h)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = (h z) ^ 2 + d)
    (hrot : ∀ z : ℂ, h (Complex.I * z) = Complex.I * h z) :
    ∃ B : ℝ, ∀ z : ℂ, ‖h ((2 * c) * z) - (2 * d) * z‖ ≤ B := by
  let G : ℂ → ℂ := fun z => h ((2 * c) * z) - (2 * d) * z
  have hG : Continuous G := by
    exact (hcont.comp (continuous_const.mul continuous_id)).sub
      (continuous_const.mul continuous_id)
  have h₁ : Function.Periodic G 1 := by
    intro z
    change h ((2 * c) * (z + 1)) - (2 * d) * (z + 1) =
      h ((2 * c) * z) - (2 * d) * z
    rw [show (2 * c) * (z + 1) = (2 * c) * z + 2 * c by ring,
      quadratic_translate h c d hquad hrot]
    ring
  have hI : Function.Periodic G Complex.I := by
    intro z
    change h ((2 * c) * (z + Complex.I)) - (2 * d) * (z + Complex.I) =
      h ((2 * c) * z) - (2 * d) * z
    rw [show (2 * c) * (z + Complex.I) =
        (2 * c) * z + 2 * (Complex.I * c) by ring,
      quadratic_translate_rotated h c d hquad hrot]
    ring
  exact norm_bounded_of_periodic_one_I G hG h₁ hI

theorem parameter_eq_of_quarter_turn_conjugacy (h : ℂ → ℂ) (c d : ℂ)
    (hcont : Continuous h) (hinj : Function.Injective h)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = (h z) ^ 2 + d)
    (hrot : ∀ z : ℂ, h (Complex.I * z) = Complex.I * h z) : c = d := by
  obtain ⟨B, hB⟩ := scaled_deviation_bounded h c d hcont hquad hrot
  have hb : ∀ n : ℕ, ‖(n : ℂ) ^ 2 * (4 * d * (d - c))‖ ≤ B := by
    intro n
    have he : h ((2 * c) * (2 * c * (n : ℂ) ^ 2 + (1 / 2 : ℂ))) -
        (2 * d) * (2 * c * (n : ℂ) ^ 2 + (1 / 2 : ℂ)) =
        (n : ℂ) ^ 2 * (4 * d * (d - c)) := by
      rw [show (2 * c) * (2 * c * (n : ℂ) ^ 2 + (1 / 2 : ℂ)) =
          ((n : ℂ) * (2 * c)) ^ 2 + c by ring,
        hquad, quadratic_nat_multiple h c d hquad hrot]
      ring
    calc
      ‖(n : ℂ) ^ 2 * (4 * d * (d - c))‖ =
          ‖h ((2 * c) * (2 * c * (n : ℂ) ^ 2 + (1 / 2 : ℂ))) -
            (2 * d) * (2 * c * (n : ℂ) ^ 2 + (1 / 2 : ℂ))‖ :=
        congrArg norm he.symm
      _ ≤ B := hB _
  have hk := eq_zero_of_nat_sq_mul_norm_bounded (4 * d * (d - c)) B hb
  by_cases hd : d = 0
  · have hc : c = 0 := by
      apply hinj
      rw [quadratic_map_parameter h c d hquad hrot, rotation_map_zero h hrot, hd]
    exact hc.trans hd.symm
  · have hnd : (4 : ℂ) * d ≠ 0 := mul_ne_zero (by norm_num) hd
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hk).resolve_left hnd)).symm

theorem map_eq_id_of_quarter_turn_conjugacy (h : ℂ → ℂ) (c d : ℂ)
    (hcont : Continuous h) (hinj : Function.Injective h)
    (hquad : ∀ z : ℂ, h (z ^ 2 + c) = (h z) ^ 2 + d)
    (hrot : ∀ z : ℂ, h (Complex.I * z) = Complex.I * h z)
    (hc : c ≠ 0) : h = id := by
  have hcd := parameter_eq_of_quarter_turn_conjugacy h c d hcont hinj hquad hrot
  subst d
  obtain ⟨B, hB⟩ := scaled_deviation_bounded h c c hcont hquad hrot
  have hb : ∀ z : ℂ, ‖h z - z‖ ≤ B := by
    intro z
    have hnc : (2 : ℂ) * c ≠ 0 := mul_ne_zero (by norm_num) hc
    have he : (2 * c) * (z / (2 * c)) = z := mul_div_cancel₀ z hnc
    simpa only [he] using hB (z / (2 * c))
  exact map_eq_id_of_bounded_deviation h c hquad hrot hc B hb


end
end LoopsQuadraticRotationRigidity
