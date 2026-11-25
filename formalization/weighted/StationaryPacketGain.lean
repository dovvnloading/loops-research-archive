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

/-- If every backward critical step either remains critical or has a
different raw auxiliary window, terminal criticality gives the entire
critical itinerary or at least one auxiliary. The geometry producing
hstep is the suffix-anchor argument, not a theorem of this finite layer. -/
theorem suffix_backward_or_auxiliary {L : Type*} (a : ℕ → L)
    (c : L) (aux : ℕ → Prop) (n : ℕ) (hlast : a n = c)
    (hstep : ∀ j < n, a (j+1) = c → a j = c ∨ aux j) :
    (∀ j ≤ n, a j = c) ∨ ∃ j < n, aux j := by
  classical
  by_cases hex : ∃ j < n, aux j
  · exact Or.inr hex
  · left
    have hb : ∀ k ≤ n, a (n-k) = c := by
      intro k
      induction k with
      | zero => intro _; simpa using hlast
      | succ k ih =>
        intro hk
        have hk' : k ≤ n := by omega
        have hi : n-(k+1) < n := by omega
        have heq : n-(k+1)+1 = n-k := by omega
        have hc : a (n-(k+1)+1) = c := by
          rw [heq]
          exact ih hk'
        rcases hstep (n-(k+1)) hi hc with hp | ha
        · exact hp
        · exact False.elim (hex ⟨_, hi, ha⟩)
    intro j hj
    have heq : n-(n-j) = j := by omega
    simpa only [heq] using hb (n-j) (by omega)

/-- Explicit positive strict-response parameter when at least half of
the input has a separate physical auxiliary window. The series premise
and bounded output budget are supplied by the written proof. -/
theorem suffix_series_strict_response (W G w P B D E N : ℝ)
    (hW : 0 < W) (hN : 0 < N) (hB : 0 < B) (hP : 0 ≤ P)
    (hfrac : W/2 ≤ w) (hcap : B ≤ (2*N)*W)
    (hgood : W ≤ G+E) (hadd : G-w+P ≤ D)
    (hseries : w*(P+B) ≤ P*B) (hscale : E ≤ W/(64*N)) :
    W+W/(64*N) < D := by
  have hK : 0 < 2*N := by positivity
  have hf : (1/2 : ℝ)*W ≤ w := by linarith
  have hr := auxiliary_fraction_response W G w P B D E (1/2) (2*N)
    hW (by norm_num) hK hB hP hf hcap hgood hadd hseries
  have he : (1/2 : ℝ)^2*W/(2*N) = 8*(W/(64*N)) := by
    field_simp [ne_of_gt hN] <;> ring
  rw [he] at hr
  have hp : 0 < W/(64*N) := by positivity
  linarith

/-- The double and over-critical source classes share a common
injective primary output. A half-width cap for the over-critical
part then gives the mixed three-quarter cap. -/
theorem precritical_mixed_cap (Z wD wO D O M L E : ℝ)
    (hZ : Z ≤ wD+wO+E) (hD : wD ≤ D/2) (hO : wO ≤ O)
    (hP : D+O ≤ M) (hOC : O ≤ M/2+L) :
    Z ≤ 3*M/4+L/2+E := by
  linarith

/-- A three-quarter terminal cap on the excluded orientation
class leaves a positive auxiliary fraction after small losses. -/
theorem precritical_auxiliary_fraction (W w Z E Ez lam : ℝ)
    (hW : 0 ≤ W)
    (hpart : W ≤ w+Z+E)
    (hcap : Z ≤ 3*(1+lam)*W/4+Ez)
    (hscale : E+Ez ≤ W/16) (hlam : lam*W ≤ W/16) :
    W/8 ≤ w := by
  have hc : Z ≤ 3*W/4 + 3*(lam*W)/4 + Ez := by
    nlinarith only [hcap]
  linarith

/-- Strict integrated response with one-eighth auxiliary fraction.
The actual precritical exclusion and separator/suffix windows
remain premises of the analytic proof. -/
theorem precritical_integrated_strict_response (W G w P B D E N : ℝ)
    (hW : 0 < W) (hN : 0 < N) (hB : 0 < B) (hP : 0 ≤ P)
    (hfrac : W/8 ≤ w) (hcap : B ≤ (2*N)*W)
    (hgood : W ≤ G+E) (hadd : G-w+P ≤ D)
    (hseries : w*(P+B) ≤ P*B) (hscale : E ≤ W/(512*N)) :
    W+W/(512*N) < D := by
  have hK : 0 < 2*N := by positivity
  have hf : (1/8 : ℝ)*W ≤ w := by linarith
  have hr := auxiliary_fraction_response W G w P B D E (1/8) (2*N)
    hW (by norm_num) hK hB hP hf hcap hgood hadd hseries
  have he : (1/8 : ℝ)^2*W/(2*N) = 4*(W/(512*N)) := by
    field_simp [ne_of_gt hN] <;> ring
  rw [he] at hr
  have hp : 0 < W/(512*N) := by positivity
  linarith

/-- A pair of opposite quadrilateral width bounds, each dominating
half of the surviving source width, bounds that source width by two.
The actual four-electrode construction is the written Shift argument. -/
theorem reciprocal_half_width_bound (W x y : ℝ) (hW : 0 ≤ W)
    (hx : W/2 ≤ x) (hy : W/2 ≤ y) (hxy : x*y ≤ 1) :
    W ≤ 2 := by
  have hhalf : 0 ≤ W/2 := by linarith
  have hx0 : 0 ≤ x := hhalf.trans hx
  have hp : (W/2)*(W/2) ≤ x*y :=
    mul_le_mul hx hy hhalf hx0
  by_contra! hn
  have hpos : 0 < W+2 := by linarith
  nlinarith [mul_pos (sub_pos.mpr hn) hpos]

/-- A series response on a subfamily of the whole primary-good
ambient lamination bounds its squared width in terms of the ambient
allowance. The whole primary support addition is explicit. -/
theorem ambient_auxiliary_mass_cap (W G w P B D E M : ℝ)
    (hw : 0 ≤ w) (hP : 0 ≤ P) (hB : 0 < B)
    (hgood : W ≤ G+E) (hadd : G-w+P ≤ D)
    (hseries : w*(P+B) ≤ P*B) (hcap : D ≤ M) :
    w^2 ≤ B*(M-W+E) := by
  have hs := series_excess_bound w P B hw hP hB hseries
  have hd : w^2/B ≤ M-W+E := by linarith
  simpa [mul_comm] using (div_le_iff₀ hB).mp hd

/-- Collect the two double/precritical charges and one over-critical
charge without using width additivity between different outputs. -/
theorem ambient_defect_bookkeeping (s E H C d K a Ea R Q2 QN : ℝ)
    (hpart : s ≤ E+H*(2*C+d)+(4*C+d+Q2)+K*a+
      (2*C+Q2)+(4*C+d+Q2)+Ea+4*R+QN) :
    s ≤ E+(2*H+10)*C+K*a+Ea+4*R+(H+2)*d+3*Q2+QN := by
  nlinarith only [hpart]

/-- Alternating fixed electrodes give reciprocal quadrilateral
width bounds. Their finite consequence: one packet is small. -/
theorem alternating_pair_small (x y : ℝ) (h : x*y ≤ 1) :
    x ≤ 1 ∨ y ≤ 1 := by
  by_cases hx : x ≤ 1
  · exact Or.inl hx
  · right
    by_contra! hy
    have hx' : 1 < x := lt_of_not_ge hx
    nlinarith [mul_pos (sub_pos.mpr hx') (sub_pos.mpr hy)]

/-- Retaining the largest phase loses at most the width outside
any specified compatible sector phase. Maximality of the chosen
phase is an explicit premise, not a claim of image coincidence. -/
theorem phase_deficit_le_outside (total best compatible outside : ℝ)
    (hsum : total = compatible+outside) (hbest : compatible ≤ best) :
    total-best ≤ outside := by
  linarith

/-- The two explicit absolute-scale tests in the ambient estimate
force a positive phase deficit if the geometric response is absent.
All widths and bounds in this algebra are supplied by the written
packet assembly and series arguments. -/
theorem ambient_phase_deficit (W E B Delta sigma delta : ℝ)
    (hscale : E+B ≤ delta*W/4) (hB : 0 ≤ B)
    (hs : 2*delta*W ≤ sigma*W)
    (hbad : delta*W/2 < E+Delta ∨ sigma*W/4 < E+Delta+B) :
    delta*W/4 < Delta := by
  rcases hbad with h | h
  · linarith
  · linarith

/-- Exact mass accounting for changing one phase in an optimal
configuration. The actual Borel gained/lost parent sets are supplied
by CRITICAL_PHASE_LOCALIZATION. -/
theorem phase_exchange_balance (covered gain loss after : ℝ)
    (hchange : after = covered+gain-loss) (hopt : after ≤ covered) :
    gain ≤ loss := by
  linarith

/-- A configuration covering a fixed candidate selection cannot
have greater uncovered width if the covered width is optimized. -/
theorem optimized_phase_deficit_le_fixed (W best fixed : ℝ)
    (h : fixed ≤ best) : W-best ≤ W-fixed := by
  linarith

/-- A bounded set of signed-probe failures may be removed from the
upper median half before applying reciprocal quadrilateral widths.
The geometric ordering and the two half-width bounds are separate
inputs supplied by ANCHORED_PHASE_FREE_RESPONSE. -/
theorem median_reciprocal_loss (g L x y : ℝ)
    (hL : 0 ≤ L) (hx : g/2 ≤ x) (hy : g/2-L ≤ y)
    (hxy : x*y ≤ 1) :
    g ≤ 2+2*L := by
  by_contra! hn
  have ha : 1 < x := by linarith
  have hb : 1 < y := by linarith
  nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)]

/-- Collect the phase-free defects. Every square-root allowance
comes from actual distinct raw windows against the whole primary
packet, not a singleton output or a disjoint auxiliary-image sum. -/
theorem anchored_defect_bookkeeping
    (s E H C K Ea R Q2 QK QN : ℝ)
    (hpart : s ≤ E+2*(4*K+24*K*C+2*QK)+
       2*(2*C+Q2)+2*(4*C+2*Q2)+H*(2*C+Q2)+Ea+4*R+QN) :
    s ≤ E+8*K+(48*K+12+2*H)*C+Ea+4*R+
       4*QK+(H+6)*Q2+QN := by
  nlinarith only [hpart]

/-- If the absolute and series charges are each at most one fourth
of the proposed nonshort mass fraction, that fraction is impossible. -/
theorem anchored_nonshort_fraction_excluded (W s B Q sigma : ℝ)
    (hW : 0 < W) (hsigma : 0 < sigma)
    (hfrac : sigma*W ≤ s) (hpart : s ≤ B+Q)
    (hB : B ≤ sigma*W/4) (hQ : Q ≤ sigma*W/4) :
    False := by
  nlinarith [mul_pos hsigma hW]

end LoopsStationaryPacketGain
