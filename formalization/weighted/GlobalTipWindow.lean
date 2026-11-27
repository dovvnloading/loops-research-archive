import GlobalTipIsolation

/-!
# Actual restrictive intervals and the complete tip itinerary

The parameter domain below is defined by the genuine real map and a
forward-invariant critical interval. It uses no collision equation and
no root locator. Its endpoint version consists entirely of orbit
inequalities. The map on each intermediate phase keeps the stated
strict sign, so every return to the critical interval has the full
physical itinerary used by the global isolation certificate.
-/

namespace LoopsGlobalTip

open Set Function
open LoopsRealPeriod27 LoopsDepthThreeReal

noncomputable section

/-- The actual real quadratic map. -/
def realQuadratic (c z : ℝ) : ℝ := z ^ 2 + c

/-- The critical interval uses the actual first return of zero. -/
def criticalInterval (p : ℕ) (c : ℝ) : Set ℝ :=
  Icc (-polynomial p c) (polynomial p c)

/-- An actual invariant central-return interval, with strict
intermediate separation from zero. No collision or seed occurs here.
Pairwise phase disjointness and a canonical copy identification are
not part of this definition. -/
structure RestrictiveWindow (p : ℕ) (c : ℝ) : Prop where
  positive : 0 < polynomial p c
  first : ∀ z ∈ criticalInterval p c, realQuadratic c z < 0
  middle : ∀ j, 2 ≤ j → j < p → ∀ z ∈ criticalInterval p c,
    0 < (realQuadratic c)^[j] z
  invariant : MapsTo ((realQuadratic c)^[p])
    (criticalInterval p c) (criticalInterval p c)

/-- The six returns selecting the archive's inner period-three tip. -/
def ReturnSigns (p : ℕ) (c : ℝ) : Prop :=
  0 < polynomial p c ∧ polynomial (2*p) c < 0 ∧
    polynomial (3*p) c < 0 ∧ 0 < polynomial (4*p) c ∧
    polynomial (5*p) c < 0 ∧ 0 < polynomial (6*p) c

/-- Critical-orbit polynomials and genuine function iteration agree. -/
theorem polynomial_eq_real_iterate (c : ℝ) (n : ℕ) :
    polynomial n c = (realQuadratic c)^[n] 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [polynomial_succ, Function.iterate_succ_apply']
    rw [← ih]
    rfl

/-- Exact time addition for the actual critical orbit. -/
theorem polynomial_time_add (c : ℝ) (m n : ℕ) :
    polynomial (m+n) c = (realQuadratic c)^[n] (polynomial m c) := by
  rw [polynomial_eq_real_iterate, polynomial_eq_real_iterate,
    Nat.add_comm m n, Function.iterate_add_apply]

/-- Every complete return of the critical point stays in the same
actual interval, at every depth. -/
theorem restrictive_returns_mem {p : ℕ} {c : ℝ}
    (h : RestrictiveWindow p c) (k : ℕ) :
    polynomial (k*p) c ∈ criticalInterval p c := by
  induction k with
  | zero =>
    simp only [Nat.zero_mul]
    change 0 ∈ Icc (-polynomial p c) (polynomial p c)
    exact ⟨by linarith [h.positive], h.positive.le⟩
  | succ k ih =>
    rw [Nat.succ_mul, polynomial_time_add]
    exact h.invariant ih

/-- The first intermediate phase of every return is strictly negative. -/
theorem restrictive_first_phase {p : ℕ} {c : ℝ}
    (h : RestrictiveWindow p c) (k : ℕ) :
    polynomial (k*p+1) c < 0 := by
  rw [polynomial_time_add]
  simpa only [Function.iterate_one] using h.first _ (restrictive_returns_mem h k)

/-- Every later intermediate phase is strictly positive, uniformly
over all returns and not just over the first six. -/
theorem restrictive_middle_phase {p : ℕ} {c : ℝ}
    (h : RestrictiveWindow p c) (k j : ℕ) (hj : 2 ≤ j) (hjp : j < p) :
    0 < polynomial (k*p+j) c := by
  rw [polynomial_time_add]
  exact h.middle j hj hjp _ (restrictive_returns_mem h k)

private theorem polynomial_nonneg_of_parameter_nonneg {c : ℝ}
    (hc : 0 ≤ c) (n : ℕ) : 0 ≤ polynomial n c := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [polynomial_succ]
    exact add_nonneg (sq_nonneg _) hc

private theorem polynomial_ge_neg_parameter {c : ℝ} (hc : c ≤ -2)
    (n : ℕ) : -c ≤ polynomial (n+2) c := by
  have hc0 : c ≤ 0 := by linarith
  have hcc : 0 ≤ c * (c+2) :=
    mul_nonneg_of_nonpos_of_nonpos hc0 (by linarith)
  induction n with
  | zero =>
    norm_num [polynomial_succ, LoopsRealPeriod27.polynomial,
      LoopsRealPeriod27.state, LoopsRealPeriod27.realIter,
      LoopsRealPeriod27.next]
    nlinarith
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, polynomial_succ]
    have hsq : (-c)^2 ≤ polynomial (n+2) c ^ 2 :=
      pow_le_pow_left₀ (by linarith) ih 2
    nlinarith

/-- A negative critical-orbit value after time one forces the actual
real parameter into (-2,0). No collision equation is needed. -/
theorem negative_orbit_parameter_bounds {c : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hnegative : polynomial n c < 0) : c ∈ Ioo (-2) 0 := by
  constructor
  · by_contra hc
    have hle : c ≤ -2 := le_of_not_gt hc
    have hbound := polynomial_ge_neg_parameter hle (n-2)
    rw [Nat.sub_add_cancel hn] at hbound
    linarith
  · by_contra hc
    have hbound := polynomial_nonneg_of_parameter_nonneg (le_of_not_gt hc) n
    linarith

/-- The signed return hypothesis automatically supplies the global
closed parameter interval required by the exhaustive certificate. -/
theorem returnSigns_parameter_bounds {p : ℕ} {c : ℝ}
    (hp : 0 < p) (h : ReturnSigns p c) : c ∈ Icc (-2) 0 := by
  have hb := negative_orbit_parameter_bounds (n := 3*p) (by omega) h.2.2.1
  exact ⟨hb.1.le, hb.2.le⟩

/-- Finite endpoint tests for the entire critical interval. They
do not assume the signs at interior points of any phase. -/
structure EndpointWindow (p : ℕ) (c : ℝ) : Prop where
  positive : 0 < polynomial p c
  first : polynomial (p+1) c < 0
  middle : ∀ j, 2 ≤ j → j < p → 0 < polynomial (p+j) c
  invariant : -polynomial p c ≤ polynomial (2*p) c

private theorem quadratic_mono_nonneg (c : ℝ) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) : realQuadratic c x ≤ realQuadratic c y := by
  simpa only [realQuadratic, add_comm c] using
    add_le_add_right (pow_le_pow_left₀ hx hxy 2) c

private theorem quadratic_antitone_nonpos (c : ℝ) {x y : ℝ}
    (hxy : x ≤ y) (hy : y ≤ 0) : realQuadratic c y ≤ realQuadratic c x := by
  have hs := pow_le_pow_left₀ (neg_nonneg.mpr hy) (neg_le_neg hxy) 2
  simpa only [realQuadratic, neg_sq, add_comm c] using add_le_add_right hs c

private theorem first_phase_bounds {p : ℕ} {c z : ℝ}
    (hd : 0 < polynomial p c) (hz : z ∈ criticalInterval p c) :
    realQuadratic c z ∈ Icc c (polynomial (p+1) c) := by
  have hza : |z| ≤ polynomial p c := abs_le.mpr hz
  have hsq : z^2 ≤ polynomial p c ^ 2 := sq_le_sq.mpr (by
    simpa only [abs_of_pos hd] using hza)
  rw [polynomial_succ]
  exact ⟨by dsimp [realQuadratic]; nlinarith [sq_nonneg z],
    by simpa only [realQuadratic, add_comm c] using add_le_add_right hsq c⟩

/-- All intermediate interval images are bounded by their actual
endpoint orbits. This controls the whole real interval, not just
the finite critical orbit. -/
theorem endpoint_window_phase_bounds {p : ℕ} {c z : ℝ}
    (h : EndpointWindow p c) (hz : z ∈ criticalInterval p c)
    (j : ℕ) (hj : 2 ≤ j) (hjp : j ≤ p) :
    (realQuadratic c)^[j] z ∈
      Icc (polynomial (p+j) c) (polynomial j c) := by
  have hfirst := first_phase_bounds h.positive hz
  have hfirst0 : realQuadratic c z ≤ 0 := hfirst.2.trans h.first.le
  have htwo : (realQuadratic c)^[2] z ∈
      Icc (polynomial (p+2) c) (polynomial 2 c) := by
    have hl := quadratic_antitone_nonpos c hfirst.2 h.first.le
    have hu := quadratic_antitone_nonpos c hfirst.1 hfirst0
    have hc : polynomial 1 c = c := by
      rw [polynomial_succ]
      change (0 : ℝ)^2+c=c
      ring
    have hp2 : polynomial (p+2) c = realQuadratic c (polynomial (p+1) c) := by
      rw [show p+2 = (p+1)+1 by omega, polynomial_succ]
      rfl
    have h2 : polynomial 2 c = realQuadratic c c := by
      calc
        polynomial 2 c = polynomial 1 c ^ 2 + c := polynomial_succ 1 c
        _ = realQuadratic c c := by rw [hc]; rfl
    rw [hp2, h2]
    change realQuadratic c (realQuadratic c z) ∈ Icc _ _
    exact ⟨hl, hu⟩
  have hall : ∀ k : ℕ, k+2 ≤ p → (realQuadratic c)^[k+2] z ∈
      Icc (polynomial (p+(k+2)) c) (polynomial (k+2) c) := by
    intro k
    induction k with
    | zero => exact fun _ => htwo
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hpos := h.middle (k+2) (by omega) (by omega)
      have hl := quadratic_mono_nonneg c hpos.le hprev.1
      have hy : 0 ≤ (realQuadratic c)^[k+2] z := hpos.le.trans hprev.1
      have hu := quadratic_mono_nonneg c hy hprev.2
      rw [show k+1+2 = (k+2)+1 by omega,
        Function.iterate_succ_apply', show p+((k+2)+1) = (p+(k+2))+1 by omega,
        polynomial_succ, polynomial_succ]
      exact ⟨hl, hu⟩
  have hout := hall (j-2) (by omega)
  simpa only [Nat.sub_add_cancel hj] using hout

/-- The finite endpoint conditions construct a genuine invariant
critical interval with all strict phase separations. -/
theorem endpointWindow_restrictive {p : ℕ} {c : ℝ}
    (hp : 2 ≤ p) (h : EndpointWindow p c) : RestrictiveWindow p c := by
  refine ⟨h.positive, ?_, ?_, ?_⟩
  · intro z hz
    exact (first_phase_bounds h.positive hz).2.trans_lt h.first
  · intro j hj hjp z hz
    exact (h.middle j hj hjp).trans_le
      (endpoint_window_phase_bounds h hz j hj hjp.le).1
  · intro z hz
    have hb := endpoint_window_phase_bounds h hz p hp le_rfl
    change -polynomial p c ≤ (realQuadratic c)^[p] z ∧
      (realQuadratic c)^[p] z ≤ polynomial p c
    exact ⟨h.invariant.trans (by simpa only [two_mul] using hb.1), hb.2⟩

/-- The endpoint tests are necessary as well: evaluate the actual
interval images at the endpoint `x_p`. -/
theorem restrictiveWindow_endpointWindow {p : ℕ} {c : ℝ}
    (h : RestrictiveWindow p c) : EndpointWindow p c := by
  have hd : polynomial p c ∈ criticalInterval p c :=
    ⟨by linarith [h.positive], le_rfl⟩
  refine ⟨h.positive, ?_, ?_, ?_⟩
  · rw [polynomial_time_add]
    simpa only [Function.iterate_one] using h.first _ hd
  · intro j hj hjp
    rw [polynomial_time_add]
    exact h.middle j hj hjp _ hd
  · rw [two_mul, polynomial_time_add]
    exact (h.invariant hd).1

/-- For every period at least two, finitely many endpoint inequalities
characterize the whole invariant central-return interval exactly. -/
theorem restrictiveWindow_iff_endpointWindow {p : ℕ} {c : ℝ}
    (hp : 2 ≤ p) : RestrictiveWindow p c ↔ EndpointWindow p c :=
  ⟨restrictiveWindow_endpointWindow, endpointWindow_restrictive hp⟩

/-- The full physical word includes the six return signs. -/
theorem hasSigns_returnSigns {p : ℕ} {c : ℝ} (hp : 0 < p)
    (h : HasSigns p c) : ReturnSigns p c := by
  have h1 := h p (by omega) (by omega)
  have h2 := h (2*p) (by omega) (by omega)
  have h3 := h (3*p) (by omega) (by omega)
  have h4 := h (4*p) (by omega) (by omega)
  have h5 := h (5*p) (by omega) (by omega)
  have h6 := h (6*p) (by omega) le_rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [requiredPositive, Nat.div_self hp] using h1
  · simpa [requiredPositive, Nat.ne_of_gt hp] using h2
  · simpa [requiredPositive, Nat.ne_of_gt hp] using h3
  · simpa [requiredPositive, Nat.ne_of_gt hp] using h4
  · simpa [requiredPositive, Nat.ne_of_gt hp] using h5
  · simpa [requiredPositive, Nat.ne_of_gt hp] using h6

/-- The exhaustive domain is obtained from the actual signed orbit;
it is not an additional parameter-window assumption. -/
theorem hasSigns_parameter_bounds {p : ℕ} {c : ℝ} (hp : 0 < p)
    (h : HasSigns p c) : c ∈ Icc (-2) 0 :=
  returnSigns_parameter_bounds hp (hasSigns_returnSigns hp h)

/-- A signed orbit and the single invariant endpoint inequality
provide every finite endpoint condition for the physical interval. -/
theorem hasSigns_endpointWindow {p : ℕ} {c : ℝ} (hp : 2 ≤ p)
    (h : HasSigns p c) (hinvariant : 0 ≤ polynomial p c + polynomial (2*p) c) :
    EndpointWindow p c := by
  refine ⟨(hasSigns_returnSigns (by omega) h).1, ?_, ?_, by linarith⟩
  · have hs := h (p+1) (by omega) (by omega)
    have hsign : requiredPositive p (p+1) = false := by
      simp [requiredPositive, Nat.mod_eq_of_lt (show 1 < p by omega)]
    simpa only [hsign, Bool.false_eq_true, ↓reduceIte] using hs
  · intro j hj hjp
    have hs := h (p+j) (by omega) (by omega)
    have hsign : requiredPositive p (p+j) = true := by
      simp [requiredPositive, Nat.mod_eq_of_lt hjp,
        show j ≠ 0 by omega, show j ≠ 1 by omega]
    simpa only [hsign, ↓reduceIte] using hs

/-- A box certificate's signed orbit and invariant endpoint estimate
construct the genuine real restrictive interval at its actual root. -/
theorem hasSigns_restrictiveWindow {p : ℕ} {c : ℝ} (hp : 2 ≤ p)
    (h : HasSigns p c) (hinvariant : 0 ≤ polynomial p c + polynomial (2*p) c) :
    RestrictiveWindow p c :=
  endpointWindow_restrictive hp (hasSigns_endpointWindow hp h hinvariant)

private theorem returnSigns_at {p : ℕ} {c : ℝ} (h : ReturnSigns p c)
    (k : ℕ) (hk : 1 ≤ k) (hk6 : k ≤ 6) :
    if k = 1 ∨ k = 4 ∨ k = 6 then 0 < polynomial (k*p) c
    else polynomial (k*p) c < 0 := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
  interval_cases k <;> simp_all

/-- The geometric restrictive interval and its six returns force
the complete physical kneading word. Consequently global signed
root isolation applies to every parameter in this entire domain. -/
theorem restrictiveWindow_hasSigns {p : ℕ} {c : ℝ} (hp : 2 ≤ p)
    (hw : RestrictiveWindow p c) (hr : ReturnSigns p c) : HasSigns p c := by
  intro j hj hj6
  have hp0 : 0 < p := by omega
  have hmod : j % p < p := Nat.mod_lt j hp0
  have hdecomp : j = (j/p)*p + j%p := by
    simpa only [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div j p).symm
  by_cases hz : j % p = 0
  · have heq : j = (j/p)*p := by simpa only [hz, Nat.add_zero] using hdecomp
    have hk : 1 ≤ j/p := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hk0
      have hj0 : j = 0 := by simpa only [hk0, Nat.zero_mul] using heq
      omega
    have hk6 : j/p ≤ 6 := Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using hj6)
    have hs := returnSigns_at hr (j/p) hk hk6
    unfold requiredPositive
    rw [if_pos hz]
    by_cases ht : j/p = 1 ∨ j/p = 4 ∨ j/p = 6
    · simp only [ht, decide_true, ↓reduceIte] at hs ⊢
      rw [heq]
      exact hs
    · simp only [ht, decide_false, Bool.false_eq_true, ↓reduceIte] at hs ⊢
      rw [heq]
      exact hs
  · by_cases ho : j % p = 1
    · have hs := restrictive_first_phase hw (j/p)
      have heq : j = (j/p)*p+1 := by simpa only [ho] using hdecomp
      have hsign : requiredPositive p j = false := by simp [requiredPositive, ho]
      simp only [hsign, Bool.false_eq_true, ↓reduceIte]
      rw [heq]
      exact hs
    · have hs := restrictive_middle_phase hw (j/p) (j%p) (by omega) hmod
      have hsign : requiredPositive p j = true := by simp [requiredPositive, hz, ho]
      simp only [hsign, ↓reduceIte]
      rw [hdecomp]
      exact hs

end
end LoopsGlobalTip
