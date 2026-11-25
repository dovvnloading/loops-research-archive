import Mathlib

/-!
# Deck separator and retained-collision energy algebra

See SYMMETRIC_SEPARATOR.md and COLLISION_GAIN.md in the stationary
transport audit. The interval fixed-point argument uses the real
intermediate value theorem. The dendrite arc, physical model,
attachment hosts and disjoint conformal windows remain geometric inputs.
-/

namespace LoopsStationaryDeckSeparator

open Set

/-- A continuous exchange of the two interval endpoints has an
interior fixed point. No metric midpoint assumption is needed. -/
theorem swapped_interval_fixed (s : ℝ → ℝ)
    (hc : ContinuousOn s (Icc 0 1)) (h0 : s 0 = 1) (h1 : s 1 = 0) :
    ∃ t ∈ Ioo (0 : ℝ) 1, s t = t := by
  have hdiff : ContinuousOn (fun t => s t - t) (Icc 0 1) :=
    hc.sub continuous_id.continuousOn
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc'
    (by norm_num : (0 : ℝ) ≤ 1) hdiff
    (show (0 : ℝ) ∈ Icc (s 1 - 1) (s 0 - 0) by
      rw [h0, h1]
      norm_num)
  have hfix : s t = t := by linarith
  have hn0 : t ≠ 0 := by
    intro he
    rw [he, h0] at hfix
    norm_num at hfix
  have hn1 : t ≠ 1 := by
    intro he
    rw [he, h1] at hfix
    norm_num at hfix
  exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hn0),
    lt_of_le_of_ne ht.2 hn1⟩, hfix⟩

/-- Given the actual invariant arc parameterization, uniqueness of
the deck fixed point puts that point on the open arc. -/
theorem unique_fixed_point_on_arc {K : Type*}
    (s : ℝ → ℝ) (arc : ℝ → K) (deck : K → K) (c : K)
    (hc : ContinuousOn s (Icc 0 1)) (h0 : s 0 = 1) (h1 : s 1 = 0)
    (hcomm : ∀ t ∈ Icc (0 : ℝ) 1, deck (arc t) = arc (s t))
    (hunique : ∀ x, deck x = x → x = c) :
    ∃ t ∈ Ioo (0 : ℝ) 1, arc t = c := by
  obtain ⟨t, ht, hs⟩ := swapped_interval_fixed s hc h0 h1
  have h := hcomm t ⟨ht.1.le, ht.2.le⟩
  rw [hs] at h
  exact ⟨t, ht, hunique _ h⟩

/-- A connected-model separator hit lifts to the physical separator
when the entire corresponding fiber is contained in it. -/
theorem fiber_hit_lifts {K D : Type*} (m : K → D)
    (E Q : Set K) (c : D)
    (hfiber : ∀ x, m x = c → x ∈ Q) (hhit : c ∈ m '' E) :
    ∃ x ∈ E, x ∈ Q := by
  obtain ⟨x, hx, heq⟩ := hhit
  exact ⟨x, hx, hfiber x heq⟩

/-- Retraction followed by a continuous map preserves the connected
obstruction. The geometric application supplies this map by
collapsing the exterior of the selected limb to its singleton cut. -/
theorem connected_image_separator {K D : Type*}
    [TopologicalSpace K] [TopologicalSpace D]
    (r : K → D) (E Q : Set K) (P C : Set D) (a : D)
    (hcont : Continuous r) (hconn : IsConnected E)
    (hbase : ∀ S : Set D, IsConnected S → a ∈ S →
      (∃ y ∈ S, y ∈ C) → ∃ y ∈ S, y ∈ P)
    (hroot : ∃ x ∈ E, r x = a)
    (hdeep : ∃ x ∈ E, r x ∈ C)
    (hpre : ∀ x, r x ∈ P → x ∈ Q) :
    ∃ x ∈ E, x ∈ Q := by
  obtain ⟨x, hx, ha⟩ := hroot
  obtain ⟨z, hz, hc⟩ := hdeep
  have hr : a ∈ r '' E := ⟨x, hx, ha⟩
  have hd : ∃ y ∈ r '' E, y ∈ C := ⟨r z, ⟨z, hz, rfl⟩, hc⟩
  obtain ⟨y, hy, hp⟩ :=
    hbase (r '' E) (hconn.image r hcont.continuousOn) hr hd
  obtain ⟨w, hw, he⟩ := hy
  exact ⟨w, hw, hpre w (he ▸ hp)⟩

/-- Two distinct deck-related anchors cannot belong to a single base
on which the covering map is injective. -/
theorem deck_anchors_separate {K D : Type*} (f : K → D)
    (B : Set K) (x y : K) (hinj : InjOn f B)
    (hxy : x ≠ y) (heq : f x = f y) :
    ¬ (x ∈ B ∧ y ∈ B) := by
  rintro ⟨hx, hy⟩
  exact hxy (hinj hx hy heq)

/-- The finite window multiplicity of a chain with a simple or double
choice at each stage. The disjointness of the actual windows is not
implied by the Boolean list. -/
def doubleCount : List Bool → ℕ
  | [] => 0
  | false :: xs => doubleCount xs
  | true :: xs => doubleCount xs + 1

def windowCount : List Bool → ℕ
  | [] => 1
  | false :: xs => windowCount xs
  | true :: xs => 2 * windowCount xs

theorem windows_power (xs : List Bool) :
    windowCount xs = 2 ^ doubleCount xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp [windowCount, doubleCount, ih, pow_succ, Nat.mul_comm]

/-- The metric length gain is squared in the area normalization. -/
theorem energy_width_charge (W D d r : ℝ)
    (hr : 0 < r) (h : W * r^2 ≤ d * D) :
    W ≤ d * D / r^2 := by
  exact (le_div_iff₀ (by positivity : 0 < r^2)).2 h

/-- If the response fraction times the squared window multiplicity
beats the degree cost, the requested gain follows. -/
theorem weighted_gain_threshold (A S D d r eta lam : ℝ)
    (hA : 0 ≤ A) (hd : 0 < d)
    (hpart : eta*A ≤ S) (hmetric : S*r^2 ≤ d*D)
    (hgain : lam*d ≤ eta*r^2) :
    lam*A ≤ D := by
  apply le_of_mul_le_mul_right _ hd
  calc
    (lam*A)*d = (lam*d)*A := by ring
    _ ≤ (eta*r^2)*A := mul_le_mul_of_nonneg_right hgain hA
    _ = (eta*A)*r^2 := by ring
    _ ≤ S*r^2 := mul_le_mul_of_nonneg_right hpart (sq_nonneg r)
    _ ≤ d*D := hmetric
    _ = D*d := by ring

private theorem one_le_two_pow (n : ℕ) : (1 : ℝ) ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    linarith

/-- More double stages than simple stages give at least a factor two,
in the exact integer-power formulation without a negative exponent. -/
theorem majority_double_gain (h k : ℕ) (hm : h < 2*k) :
    (2 : ℝ)^h * 2 ≤ (2 : ℝ)^(2*k) := by
  have he : 2*k = (h+1) + (2*k-(h+1)) := by omega
  calc
    _ = (2 : ℝ)^(h+1) := by rw [pow_succ]
    _ = (2 : ℝ)^(h+1)*1 := by ring
    _ ≤ (2 : ℝ)^(h+1)*2^(2*k-(h+1)) :=
      mul_le_mul_of_nonneg_left (one_le_two_pow _) (by positivity)
    _ = (2 : ℝ)^(2*k) := by rw [← pow_add, ← he]

/-- With the complete-lift exception charged separately, the output
still responds if enough input width remains. -/
theorem collision_after_escape (W E S D d r V : ℝ)
    (hr : 0 < r) (hpart : W ≤ E+S)
    (hescape : E ≤ d*V) (hmetric : S*r^2 ≤ d*D) :
    W ≤ d*V + d*D/r^2 := by
  have hs := energy_width_charge S D d r hr hmetric
  linarith

/-- Exact reciprocal gap lower bound, the algebraic step after
Cauchy-Schwarz on each horizontal crossing in the planar model. -/
theorem gap_energy_lower (delta E : ℝ) (hd : 0 < delta)
    (hcross : 1 ≤ (2*delta)*E) :
    1/(2*delta) ≤ E := by
  apply (div_le_iff₀ (by positivity : 0 < 2*delta)).2
  simpa [mul_comm] using hcross

end LoopsStationaryDeckSeparator
