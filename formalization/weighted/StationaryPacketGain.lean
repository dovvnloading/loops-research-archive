import Mathlib

/-!
# Coherent packet gain and finite-width telescope

Analytic inputs in COHERENT_PACKET_GAIN.md: a uniformly charged
bad primary packet, injectivity on a fixed covering chart,
actual disjoint retained time windows, and Borel disjoint
supports. These theorems check the finite real-number accounting,
not the geometric existence of the directed packets.
-/

namespace LoopsStationaryPacketGain

open scoped BigOperators

/-- Once the area cost is r rather than the whole covering degree,
r disjoint unit-length windows give gain r. -/
theorem chart_gain (W D r : ℝ) (hr : 0 < r)
    (h : W*r^2 ≤ r*D) : r*W ≤ D := by
  apply le_of_mul_le_mul_right _ hr
  calc
    (r*W)*r = W*r^2 := by ring
    _ ≤ r*D := h
    _ = D*r := by ring

/-- A one-step mixture of single and double paths has a width excess
equal to at least the mass of the double subfamily. Additivity
of both disjoint-support partitions is an explicit assumption. -/
theorem single_double_gain (W W1 W2 D D1 D2 : ℝ)
    (hin : W = W1+W2) (hout : D = D1+D2)
    (h1 : W1 ≤ D1) (h2 : 2*W2 ≤ D2) :
    W+W2 ≤ D := by
  linarith

/-- Product of coherent stage gains for a fixed finite pattern. -/
theorem coherent_pattern_gain (w : ℕ → ℝ) (m : ℕ → ℕ)
    (hstep : ∀ j, (m j : ℝ)*w j ≤ w (j+1)) (h : ℕ) :
    (∏ j ∈ Finset.range h, (m j : ℝ))*w 0 ≤ w h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.prod_range_succ]
    have hn : 0 ≤ (m h : ℝ) := by positivity
    calc
      _ = (m h : ℝ)*((∏ j ∈ Finset.range h, (m j : ℝ))*w 0) := by ring
      _ ≤ (m h : ℝ)*w h := mul_le_mul_of_nonneg_left ih hn
      _ ≤ _ := hstep h

/-- Every nonzero count of double stages contributes at least
one extra unit of the corresponding input width. -/
theorem double_excess (k : ℕ) (W : ℝ) (hW : 0 ≤ W) :
    W + (if 0 < k then W else 0) ≤ (2 : ℝ)^k * W := by
  cases k with
  | zero => simp
  | succ k =>
    have hp : (1 : ℝ) ≤ (2 : ℝ)^k := by
      induction k with
      | zero => norm_num
      | succ k ih => rw [pow_succ]; linarith
    have hh : (2 : ℝ) ≤ (2 : ℝ)^(k+1) := by
      rw [pow_succ]; linarith
    have hg := mul_le_mul_of_nonneg_right hh hW
    simp only [Nat.zero_lt_succ, if_true]
    linarith

/-- Weighted final-output inequality for the finitely many disjoint
multiplicity classes. -/
theorem sum_pattern_gain {J : Type*} [Fintype J] (k : J → ℕ)
    (w d : J → ℝ) (h : ∀ j, (2 : ℝ)^(k j)*w j ≤ d j) :
    (∑ j, (2 : ℝ)^(k j)*w j) ≤ ∑ j, d j :=
  Finset.sum_le_sum (fun j _ => h j)

/-- The full good-family width plus the collision width is dominated
by the sum of disjoint final outputs. -/
theorem sum_collision_excess {J : Type*} [Fintype J] (k : J → ℕ)
    (w d : J → ℝ) (hn : ∀ j, 0 ≤ w j)
    (h : ∀ j, (2 : ℝ)^(k j)*w j ≤ d j) :
    (∑ j, w j) + (∑ j, if 0 < k j then w j else 0) ≤ ∑ j, d j := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  exact (double_excess (k j) (w j) (hn j)).trans (h j)

/-- Each first-bad stage has the same cost after coefficient-one
transport through the preceding good prefix. -/
theorem bounded_discard_sum (h : ℕ) (C V E : ℝ) (c : ℕ → ℝ)
    (hpart : E ≤ (2 : ℝ)^h*V + ∑ j ∈ Finset.range h, c j)
    (hc : ∀ j < h, c j ≤ C) :
    E ≤ (2 : ℝ)^h*V + (h : ℝ)*C := by
  have hs : (∑ j ∈ Finset.range h, c j) ≤
      ∑ _j ∈ Finset.range h, C := by
    apply Finset.sum_le_sum
    intro j hj
    exact hc j (Finset.mem_range.mp hj)
  simp at hs
  linarith

/-- Removing a bounded exceptional family from both the input and
the collision subfamily gives the claimed terminal response. -/
theorem collision_fraction_response (W G B E D eta : ℝ)
    (hgood : W ≤ G+E) (hcoll : eta*W ≤ B+E)
    (hout : G+B ≤ D) :
    (1+eta)*W-2*E ≤ D := by
  linarith

/-- The absolute-scale threshold converts the response into a
strictly positive relative gain (if eta and W are positive). -/
theorem response_at_scale (W D E eta : ℝ)
    (hresp : (1+eta)*W-2*E ≤ D) (hscale : 4*E ≤ eta*W) :
    (1+eta/2)*W ≤ D := by
  linarith

/-- If the allowed output has no large gain, the remaining
collision width must be small. -/
theorem no_gain_bounds_collision (W G B E D lam : ℝ)
    (hgood : W ≤ G+E) (hout : G+B ≤ D)
    (hcap : D ≤ (1+lam)*W) :
    B ≤ lam*W+E := by
  linarith

/-- The Julia-stage charge and the collision charge may overlap;
removing their union uses subadditivity, never subtraction of an
unproved additive transverse measure. -/
theorem residual_lower (W E J B S lam R V : ℝ)
    (hpart : W ≤ E+J+B+S) (hB : B ≤ lam*W+E)
    (hJ : J ≤ R) (hE : E ≤ V) :
    (1-lam)*W-2*V-R ≤ S := by
  linarith

/-- Finite ordered contact labels with distinct endpoints have
a genuine transition. The closed-set gap extraction is a separate
topological argument in AUXILIARY_GAP_RESPONSE.md. -/
theorem some_contact_transition {L : Type*} (a : ℕ → L) (n : ℕ)
    (h : a 0 ≠ a n) :
    ∃ j < n, a j ≠ a (j+1) := by
  classical
  by_contra hn
  have he : ∀ j < n, a j = a (j+1) := by
    intro j hj
    by_contra hne
    exact hn ⟨j, hj, hne⟩
  have hall : ∀ j ≤ n, a j = a 0 := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hj' : j < n := by omega
      exact (he j hj').symm.trans (ih (Nat.le_of_lt hj'))
  exact h (hall n le_rfl).symm

/-- Two disjoint time windows allow series accounting even when
their outputs overlap. The width/metric construction supplies
the stated series premise. -/
theorem series_excess_bound (w P B : ℝ)
    (hw : 0 ≤ w) (hP : 0 ≤ P) (hB : 0 < B)
    (hseries : w*(P+B) ≤ P*B) :
    w+w^2/B ≤ P := by
  have hwp : w ≤ P := by
    apply le_of_mul_le_mul_right _ hB
    nlinarith [mul_nonneg hw hP]
  have hs := mul_le_mul_of_nonneg_left hwp hw
  have hd : w^2/B ≤ P-w := by
    apply (div_le_iff₀ hB).2
    nlinarith
  linarith

/-- A positive-width auxiliary fraction gives a quadratic
response with only a bounded sum of auxiliary output widths.
The actual disjoint support addition is explicit in hadd. -/
theorem auxiliary_fraction_response (W G w P B D E eta K : ℝ)
    (hW : 0 < W) (heta : 0 ≤ eta) (hK : 0 < K)
    (hB : 0 < B) (hP : 0 ≤ P)
    (hfrac : eta*W ≤ w) (hcap : B ≤ K*W)
    (hgood : W ≤ G+E) (hadd : G-w+P ≤ D)
    (hseries : w*(P+B) ≤ P*B) :
    W-E+eta^2*W/K ≤ D := by
  have h0 : 0 ≤ eta*W := mul_nonneg heta hW.le
  have hw : 0 ≤ w := h0.trans hfrac
  have hs : (eta*W)^2 ≤ w^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hfrac)
      (add_nonneg hw h0)]
  have hn : 0 ≤ eta^2*W/K := by positivity
  have hm := mul_le_mul_of_nonneg_left hcap hn
  have he : (eta^2*W/K)*(K*W) = (eta*W)^2 := by
    field_simp [ne_of_gt hK] <;> ring
  have hd : eta^2*W/K ≤ w^2/B := by
    apply (le_div_iff₀ hB).2
    rw [he] at hm
    exact hm.trans hs
  have hp := series_excess_bound w P B hw hP hB hseries
  linarith

/-- No large gain forces an upper bound on the actual auxiliary
fraction, once its output containers have the stated budget. -/
theorem no_gain_bounds_auxiliary_fraction (W E D eta K lam : ℝ)
    (hresponse : W-E+eta^2*W/K ≤ D)
    (hcap : D ≤ (1+lam)*W) :
    eta^2*W/K ≤ lam*W+E := by
  linarith

/-- A sufficiently small absolute discard leaves half of the
quadratic auxiliary gain. -/
theorem auxiliary_response_at_scale (W E D eta K : ℝ)
    (hK : 0 < K)
    (hresponse : W-E+eta^2*W/K ≤ D)
    (hscale : E ≤ eta^2*W/(2*K)) :
    (1+eta^2/(2*K))*W ≤ D := by
  have he : eta^2*W/K = 2*(eta^2*W/(2*K)) := by
    field_simp [ne_of_gt hK] <;> ring
  have hf : (1+eta^2/(2*K))*W = W+eta^2*W/(2*K) := by ring
  rw [he] at hresponse
  rw [hf]
  linarith

end LoopsStationaryPacketGain
