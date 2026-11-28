import Mathlib
import QuadraticEscape

/-!
# Mixed susceptibility for the actual quadratic family

The coefficient in the difference of two critical orbits is the sum of
their orbit values. Its reciprocal products give a complex series whose
ordinary convergence, together with boundedness of both critical orbits,
forces its off-diagonal value to vanish. Uniform convergence on a connected
parameter set then turns a nonzero diagonal value into rigidity.
-/

namespace QuadraticMixedSusceptibility

open Set Filter
open scoped Topology BigOperators

noncomputable section

/-- The actual bounded-critical-orbit parameter locus. -/
def mandelbrot : Set ℂ :=
  {c | ∃ B : ℝ, ∀ n : ℕ, ‖QuadraticEscape.orbit c n 0‖ ≤ B}

/-- The exact multiplier of a difference of quadratic critical orbits. -/
def factor (c d : ℂ) (n : ℕ) : ℂ :=
  QuadraticEscape.orbit c (n + 1) 0 + QuadraticEscape.orbit d (n + 1) 0

/-- Products begin at the critical value, with the empty product equal to one. -/
def product (c d : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => product c d n * factor c d n

/-- Ordinary complex partial sums; no absolute summation is imposed. -/
def partialSum (c d : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => partialSum c d n + (product c d (n + 1))⁻¹

def Nonvanishing (c d : ℂ) : Prop := ∀ n : ℕ, factor c d n ≠ 0

theorem product_ne_zero (c d : ℂ) (h : Nonvanishing c d) (n : ℕ) :
    product c d n ≠ 0 := by
  induction n with
  | zero => simp [product]
  | succ n ih => exact mul_ne_zero ih (h n)

theorem partialSum_eq_sum (c d : ℂ) (n : ℕ) :
    partialSum c d n = 1 + ∑ k ∈ Finset.range n, (product c d (k + 1))⁻¹ := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    rw [partialSum, ih, Finset.sum_range_succ]
    ring

/-- Exact finite, nonlinear parameter-difference identity. -/
theorem orbit_difference_eq (c d : ℂ) (h : Nonvanishing c d) (n : ℕ) :
    QuadraticEscape.orbit c (n + 1) 0 - QuadraticEscape.orbit d (n + 1) 0 =
      (c - d) * product c d n * partialSum c d n := by
  induction n with
  | zero => simp [QuadraticEscape.orbit, product, partialSum]
  | succ n ih =>
    calc
      QuadraticEscape.orbit c (n + 1 + 1) 0 -
          QuadraticEscape.orbit d (n + 1 + 1) 0 =
          factor c d n * (QuadraticEscape.orbit c (n + 1) 0 -
            QuadraticEscape.orbit d (n + 1) 0) + (c - d) := by
              simp only [QuadraticEscape.orbit, factor]
              ring
      _ = (c - d) * product c d (n + 1) * partialSum c d n + (c - d) := by
        rw [ih, product]
        ring
      _ = (c - d) * product c d (n + 1) * partialSum c d (n + 1) := by
        rw [partialSum, mul_add]
        simp only [mul_assoc, mul_inv_cancel₀ (product_ne_zero c d h (n + 1)),
          mul_one]

theorem normalized_difference_eq (c d : ℂ) (h : Nonvanishing c d) (n : ℕ) :
    (c - d) * partialSum c d n =
      (QuadraticEscape.orbit c (n + 1) 0 - QuadraticEscape.orbit d (n + 1) 0) *
        (product c d n)⁻¹ := by
  rw [orbit_difference_eq c d h n]
  calc
    (c - d) * partialSum c d n =
        (c - d) * partialSum c d n *
          (product c d n * (product c d n)⁻¹) := by
            rw [mul_inv_cancel₀ (product_ne_zero c d h n), mul_one]
    _ = _ := by ring

/-- Convergence of the partial sums forces their successive terms to vanish. -/
theorem reciprocal_tendsto_zero (c d L : ℂ)
    (h : Tendsto (partialSum c d) atTop (𝓝 L)) :
    Tendsto (fun n => (product c d n)⁻¹) atTop (𝓝 (0 : ℂ)) := by
  have hshift : Tendsto (fun n : ℕ => partialSum c d (n + 1)) atTop (𝓝 L) :=
    (tendsto_add_atTop_iff_nat 1).2 h
  have hterm : Tendsto (fun n : ℕ => (product c d (n + 1))⁻¹)
      atTop (𝓝 (0 : ℂ)) := by
    simpa only [partialSum, add_sub_cancel_left, sub_self] using hshift.sub h
  exact (tendsto_add_atTop_iff_nat 1).1 hterm

/-- For two distinct parameters in the actual Mandelbrot set, every
convergent ordinary mixed susceptibility series has value zero. -/
theorem limit_eq_zero_of_mem_mandelbrot (c d L : ℂ)
    (hc : c ∈ mandelbrot) (hd : d ∈ mandelbrot) (hne : c ≠ d)
    (hnon : Nonvanishing c d)
    (hsum : Tendsto (partialSum c d) atTop (𝓝 L)) : L = 0 := by
  obtain ⟨Bc, hBc⟩ := hc
  obtain ⟨Bd, hBd⟩ := hd
  have hrec := reciprocal_tendsto_zero c d L hsum
  have hzero : Tendsto (fun n : ℕ => (Bc + Bd) * ‖(product c d n)⁻¹‖)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := Bc + Bd)).mul hrec.norm
  have hbound (n : ℕ) : ‖(c - d) * partialSum c d n‖ ≤
      (Bc + Bd) * ‖(product c d n)⁻¹‖ := by
    rw [normalized_difference_eq c d hnon n, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (add_le_add (hBc (n + 1)) (hBd (n + 1)))
  have hlimit : Tendsto (fun n : ℕ => ‖(c - d) * partialSum c d n‖)
      atTop (𝓝 ‖(c - d) * L‖) :=
    ((tendsto_const_nhds (x := c - d)).mul hsum).norm
  have hle : ‖(c - d) * L‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' hlimit hzero hbound
  have heq : (c - d) * L = 0 :=
    norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hne)

theorem factor_continuous (c : ℂ) (n : ℕ) :
    Continuous (fun d : ℂ => factor c d n) := by
  have horbit : Continuous (fun d : ℂ => QuadraticEscape.orbit d (n + 1) 0) :=
    (QuadraticEscape.orbit_continuous (n + 1)).comp
      (continuous_id.prodMk continuous_const)
  exact continuous_const.add horbit

theorem product_continuous (c : ℂ) (n : ℕ) :
    Continuous (fun d : ℂ => product c d n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact ih.mul (factor_continuous c n)

/-- Every finite sum is continuous at each parameter where its factors
are nonzero, even when no ambient limit is defined. -/
theorem partialSum_continuousAt (c d : ℂ) (hnon : Nonvanishing c d) (n : ℕ) :
    ContinuousAt (fun w : ℂ => partialSum c w n) d := by
  induction n with
  | zero => exact continuousAt_const
  | succ n ih =>
    exact ih.add ((product_continuous c (n + 1)).continuousAt.inv₀
      (product_ne_zero c d hnon (n + 1)))

/-- A nonzero diagonal limit makes the parameter isolated relative to any
bounded-orbit set on which the actual mixed series converges uniformly. -/
theorem isolated_of_uniform_limit (F : Set ℂ) (c : ℂ) (L : ℂ → ℂ)
    (hFM : F ⊆ mandelbrot) (hc : c ∈ F)
    (hnon : ∀ d ∈ F, Nonvanishing c d)
    (hconv : TendstoUniformlyOn (fun n d => partialSum c d n) L atTop F)
    (hLc : L c ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ d ∈ F, dist d c < r → d = c := by
  classical
  have hpos : 0 < ‖L c‖ := norm_pos_iff.mpr hLc
  have hε : 0 < ‖L c‖ / 4 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp hconv) (‖L c‖ / 4) hε)
  obtain ⟨r, hr, hnear⟩ := (Metric.continuousAt_iff.mp
    (partialSum_continuousAt c c (hnon c hc) N)) (‖L c‖ / 4) hε
  refine ⟨r, hr, ?_⟩
  intro d hd hdist
  by_contra hne
  have hdlim : L d = 0 := limit_eq_zero_of_mem_mandelbrot c d (L d)
    (hFM hc) (hFM hd) (Ne.symm hne) (hnon d hd) (hconv.tendsto_at hd)
  have hfirst := hN N le_rfl c hc
  have hlast := hN N le_rfl d hd
  have hmiddle := hnear hdist
  rw [hdlim] at hlast
  have hmiddle' : dist (partialSum c c N) (partialSum c d N) < ‖L c‖ / 4 := by
    simpa only [dist_comm] using hmiddle
  have hlast' : dist (partialSum c d N) 0 < ‖L c‖ / 4 := by
    simpa only [dist_comm] using hlast
  have htriangle := dist_triangle4 (L c) (partialSum c c N) (partialSum c d N) 0
  rw [dist_zero_right] at htriangle
  linarith

/-- The mixed series collapses connected subsets of the actual Mandelbrot
set. Uniform convergence is only required on that subset. -/
theorem connected_set_eq_singleton (F : Set ℂ) (c : ℂ) (L : ℂ → ℂ)
    (hF : IsPreconnected F) (hFM : F ⊆ mandelbrot) (hc : c ∈ F)
    (hnon : ∀ d ∈ F, Nonvanishing c d)
    (hconv : TendstoUniformlyOn (fun n d => partialSum c d n) L atTop F)
    (hLc : L c ≠ 0) : F = {c} := by
  classical
  obtain ⟨r, hr, hisolated⟩ := isolated_of_uniform_limit F c L hFM hc hnon hconv hLc
  ext d
  constructor
  · intro hd
    change d = c
    by_contra hne
    have hcover : F ⊆ Metric.ball c r ∪ ({c} : Set ℂ)ᶜ := by
      intro z _
      by_cases hzc : z = c
      · exact Or.inl (by simpa [hzc] using hr)
      · exact Or.inr hzc
    obtain ⟨z, hz, hzball, hzc⟩ := hF _ _ Metric.isOpen_ball
      isClosed_singleton.isOpen_compl hcover
      ⟨c, hc, by simpa using hr⟩ ⟨d, hd, hne⟩
    exact hzc (hisolated z hz hzball)
  · intro hd
    have hdc : d = c := hd
    simpa only [hdc] using hc

#print axioms orbit_difference_eq
#print axioms limit_eq_zero_of_mem_mandelbrot
#print axioms connected_set_eq_singleton

end
end QuadraticMixedSusceptibility
