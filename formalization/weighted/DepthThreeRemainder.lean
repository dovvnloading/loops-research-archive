import DepthThreeReal
import QuadraticEscape

/-!
# Whole-disk error bounds for the actual quadratic iterates

The integer recurrence used in the depth-three certificates controls every
complex point of the closed disk. The proof starts at the exact first
quadratic step and propagates the full nonlinear remainder; no sampling or
truncation of the higher powers is involved.
-/

namespace LoopsDepthThreeRemainder

open LoopsFormal.Period27 LoopsFormal.DepthThree LoopsDepthThreeReal

noncomputable section

/-- The residual of the actual complex iterate after its constant and
quadratic terms have been removed. -/
def remainder (c : ℝ) (j : Nat) (z : ℂ) : ℂ :=
  QuadraticEscape.orbit (c : ℂ) j z -
    (LoopsRealPeriod27.polynomial j c : ℂ) -
    (quadraticCoefficient j c : ℂ) * z ^ 2

theorem critical_orbit_cast (c : ℝ) (j : Nat) :
    QuadraticEscape.orbit (c : ℂ) j 0 =
      (LoopsRealPeriod27.polynomial j c : ℂ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [QuadraticEscape.orbit, ih, polynomial_succ]
      push_cast <;> rfl

theorem remainder_one (c : ℝ) (z : ℂ) : remainder c 1 z = 0 := by
  norm_num [remainder, QuadraticEscape.orbit, quadraticCoefficient,
    LoopsRealPeriod27.polynomial, LoopsRealPeriod27.state,
    LoopsRealPeriod27.realIter, LoopsRealPeriod27.next]

/-- Exact nonlinear identity, retaining every term of degree four and
above. It holds throughout the complex plane. -/
theorem remainder_recurrence (c : ℝ) (j : Nat) (hj : 0 < j) (z : ℂ) :
    remainder c (j + 1) z =
      2 * (LoopsRealPeriod27.polynomial j c : ℂ) * remainder c j z +
        ((quadraticCoefficient j c : ℂ) * z ^ 2 + remainder c j z) ^ 2 := by
  simp only [remainder, QuadraticEscape.orbit, polynomial_succ,
    quadraticCoefficient, if_neg (Nat.ne_of_gt hj)]
  push_cast
  ring

/-- One full complex disk step. The quadratic-square term includes the
cross term and the square of the previous error. -/
theorem remainder_step_norm (c : ℝ) (j : Nat) (hj : 0 < j)
    (z : ℂ) (R t : ℝ) (hz : ‖z‖ ≤ R) (ht : ‖remainder c j z‖ ≤ t) :
    ‖remainder c (j + 1) z‖ ≤
      2 * |LoopsRealPeriod27.polynomial j c| * t +
        (|quadraticCoefficient j c| * R ^ 2 + t) ^ 2 := by
  have hinner : ‖(quadraticCoefficient j c : ℂ) * z ^ 2 + remainder c j z‖ ≤
      |quadraticCoefficient j c| * R ^ 2 + t := by
    calc
      _ ≤ ‖(quadraticCoefficient j c : ℂ) * z ^ 2‖ + ‖remainder c j z‖ :=
        norm_add_le _ _
      _ = |quadraticCoefficient j c| * ‖z‖ ^ 2 + ‖remainder c j z‖ := by
        simp [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg z) hz 2) (abs_nonneg _)) ht
  rw [remainder_recurrence c j hj z]
  calc
    _ ≤ ‖2 * (LoopsRealPeriod27.polynomial j c : ℂ) * remainder c j z‖ +
        ‖((quadraticCoefficient j c : ℂ) * z ^ 2 + remainder c j z) ^ 2‖ :=
      norm_add_le _ _
    _ = 2 * |LoopsRealPeriod27.polynomial j c| * ‖remainder c j z‖ +
        ‖(quadraticCoefficient j c : ℂ) * z ^ 2 + remainder c j z‖ ^ 2 := by
      simp [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left ht (by positivity))
      (pow_le_pow_left₀ (norm_nonneg _) hinner 2)

private theorem scale_pos {S : Int} (hS : 0 < S) : 0 < (S : ℝ) := by
  exact_mod_cast hS

theorem abs_enclosed {S : Int} (hS : 0 < S)
    {b : Bounds} {x : ℝ} (hx : RealEnclosed S b x) :
    |x| ≤ (absHi b : ℝ) / (S : ℝ) := by
  have hlo : -(b.lo : ℝ) ≤ (absHi b : ℝ) := by
    exact_mod_cast (le_max_left (-b.lo) b.hi)
  have hhi : (b.hi : ℝ) ≤ (absHi b : ℝ) := by
    exact_mod_cast (le_max_right (-b.lo) b.hi)
  have habs : |x * (S : ℝ)| ≤ (absHi b : ℝ) := by
    apply abs_le.mpr
    exact ⟨by linarith [hx.1], hx.2.trans hhi⟩
  rw [abs_mul, abs_of_pos (scale_pos hS)] at habs
  exact (le_div_iff₀ (scale_pos hS)).mpr habs

/-- The integer upper product bounds the product of the two represented
real grid values, with signed Euclidean rounding. -/
theorem upperProduct_sound {S : Int} (hS : 0 < S) (a b : Int) :
    ((a : ℝ) / (S : ℝ)) * ((b : ℝ) / (S : ℝ)) ≤
      (upperProduct S a b : ℝ) / (S : ℝ) := by
  have hi := signed_ceil_rounds_outward (a * b) S hS
  have hcast : (a : ℝ) * (b : ℝ) ≤
      (upperProduct S a b : ℝ) * (S : ℝ) := by
    simpa only [upperProduct, ceilDiv, floorDiv,
      if_neg (not_lt.mpr hS.le), Int.cast_mul] using
      (show ((a * b : Int) : ℝ) ≤
        ((-((-(a * b)) / S) : Int) : ℝ) * (S : ℝ) by exact_mod_cast hi)
  have hdiv := (div_le_iff₀ (scale_pos hS)).mpr hcast
  have hdiv2 := (div_le_div_iff_of_pos_right (scale_pos hS)).mpr hdiv
  convert hdiv2 using 1 <;> field_simp [ne_of_gt (scale_pos hS)] <;> ring

/-- The rational squared radius is rounded upwards, even when the
ratio is not a dyadic grid point. -/
theorem radius_squared_sound {S : Int} (hS : 0 < S)
    (r : Ratio) (hr : r.den ≠ 0) :
    ((r.num : ℝ) / (r.den : ℝ)) ^ 2 ≤
      (radiusSquaredUpper S r : ℝ) / (S : ℝ) := by
  have hd : 0 < r.den * r.den := by nlinarith [sq_pos_of_ne_zero hr]
  have hdr : (r.den : ℝ) ≠ 0 := by exact_mod_cast hr
  have hceil := signed_ceil_rounds_outward (r.num * r.num * S) (r.den * r.den) hd
  have hcast : (r.num : ℝ) ^ 2 * (S : ℝ) ≤
      (radiusSquaredUpper S r : ℝ) * (r.den : ℝ) ^ 2 := by
    simpa only [radiusSquaredUpper, ceilDiv, floorDiv,
      if_neg (not_lt.mpr hd.le), Int.cast_mul, pow_two] using
      (show ((r.num * r.num * S : Int) : ℝ) ≤
        ((-((-(r.num * r.num * S)) / (r.den * r.den)) : Int) : ℝ) *
          ((r.den * r.den : Int) : ℝ) by exact_mod_cast hceil)
  rw [div_pow]
  exact (div_le_div_iff₀ (sq_pos_of_ne_zero hdr) (scale_pos hS)).mpr hcast

/-- One integer `errorStep` bounds the actual complex residual at the
next time, using a sound row from the actual parameter interval. -/
theorem errorStep_sound {S : Int} (hS : 0 < S) (c : ℝ)
    (j : Nat) (hj : 0 < j) (row : TraceRow)
    (hrow : RealRowEnclosed S row j c)
    (z : ℂ) (R : ℝ) (hz : ‖z‖ ≤ R) (rr t : Int)
    (hrr : R ^ 2 ≤ (rr : ℝ) / (S : ℝ))
    (ht : ‖remainder c j z‖ ≤ (t : ℝ) / (S : ℝ)) :
    ‖remainder c (j + 1) z‖ ≤ (errorStep S rr row t : ℝ) / (S : ℝ) := by
  let X : ℝ := (absHi row.orbit : ℝ) / (S : ℝ)
  let A : ℝ := (absHi row.quadratic : ℝ) / (S : ℝ)
  let T : ℝ := (t : ℝ) / (S : ℝ)
  let V : Int := upperProduct S (absHi row.quadratic) rr + t
  have hx : |LoopsRealPeriod27.polynomial j c| ≤ X := abs_enclosed hS hrow.1
  have ha : |quadraticCoefficient j c| ≤ A := abs_enclosed hS hrow.2.2
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  have hT : 0 ≤ T := (norm_nonneg _).trans ht
  have hinner : |quadraticCoefficient j c| * R ^ 2 + T ≤ (V : ℝ) / (S : ℝ) := by
    have hp := upperProduct_sound hS (absHi row.quadratic) rr
    have hprod : |quadraticCoefficient j c| * R ^ 2 ≤
        A * ((rr : ℝ) / (S : ℝ)) :=
      (mul_le_mul_of_nonneg_right ha (sq_nonneg R)).trans
        (mul_le_mul_of_nonneg_left hrr hA)
    dsimp only [V]
    push_cast
    rw [add_div]
    exact add_le_add (hprod.trans hp) le_rfl
  have hfirst : 2 * |LoopsRealPeriod27.polynomial j c| * T ≤
      (upperProduct S (2 * absHi row.orbit) t : ℝ) / (S : ℝ) := by
    have hp := upperProduct_sound hS (2 * absHi row.orbit) t
    have hprod : 2 * |LoopsRealPeriod27.polynomial j c| * T ≤ 2 * X * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by norm_num)) hT
    apply hprod.trans
    convert hp using 1 <;> push_cast <;> ring
  have hsecond : (|quadraticCoefficient j c| * R ^ 2 + T) ^ 2 ≤
      (upperProduct S V V : ℝ) / (S : ℝ) := by
    have hs : (|quadraticCoefficient j c| * R ^ 2 + T) ^ 2 ≤
        ((V : ℝ) / (S : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hinner 2
    exact hs.trans (by simpa only [pow_two] using upperProduct_sound hS V V)
  have hstep := remainder_step_norm c j hj z R T hz ht
  apply hstep.trans
  change 2 * |LoopsRealPeriod27.polynomial j c| * T +
    (|quadraticCoefficient j c| * R ^ 2 + T) ^ 2 ≤
      ((upperProduct S (2 * absHi row.orbit) t + upperProduct S V V : Int) : ℝ) /
        (S : ℝ)
  push_cast
  rw [add_div]
  exact add_le_add hfirst hsecond

private theorem rowAt_take (rows : List TraceRow) (n k : Nat) (hk : k < n) :
    rowAt (rows.take n) k = rowAt rows k := by
  induction n generalizing rows k with
  | zero => omega
  | succ n ih =>
      cases rows with
      | nil => rfl
      | cons row rows =>
          cases k with
          | zero => rfl
          | succ k =>
              change rowAt (rows.take n) k = rowAt rows k
              exact ih rows k (by omega)

private theorem rowAt_drop_one (rows : List TraceRow) (k : Nat) :
    rowAt (rows.drop 1) k = rowAt rows (k + 1) := by
  cases rows <;> rfl

/-- Simultaneous interpretation of every integer error in a finite
tail. The row hypotheses refer to actual orbit and Taylor coefficients. -/
theorem errorTail_sound {S : Int} (hS : 0 < S)
    (c : ℝ) (z : ℂ) (R : ℝ) (hz : ‖z‖ ≤ R) (rr : Int)
    (hrr : R ^ 2 ≤ (rr : ℝ) / (S : ℝ))
    (rows : List TraceRow) (j : Nat) (hj : 0 < j) (t : Int)
    (hrows : ∀ k < rows.length, RealRowEnclosed S (rowAt rows k) (j + k) c)
    (ht : ‖remainder c j z‖ ≤ (t : ℝ) / (S : ℝ)) :
    ∀ k < rows.length, ‖remainder c (j + k + 1) z‖ ≤
      (errorAt (errorTail S rr rows t) k : ℝ) / (S : ℝ) := by
  induction rows generalizing j t with
  | nil => intro k hk; simp at hk
  | cons row rows ih =>
      have hrow : RealRowEnclosed S row j c := by
        simpa [rowAt] using hrows 0 (by simp)
      have hstep := errorStep_sound hS c j hj row hrow z R hz rr t hrr ht
      have htail : ∀ k < rows.length,
          RealRowEnclosed S (rowAt rows k) (j + 1 + k) c := by
        intro k hk
        have hh := hrows (k + 1) (by simpa using Nat.succ_lt_succ hk)
        change RealRowEnclosed S (rowAt rows k) (j + (k + 1)) c at hh
        convert hh using 1 <;> omega
      intro k hk
      cases k with
      | zero => simpa [errorTail, errorAt] using hstep
      | succ k =>
          have hrec := ih (j + 1) (by omega) (errorStep S rr row t) htail hstep
            k (by simpa using hk)
          change ‖remainder c (j + (k + 1) + 1) z‖ ≤
            (errorAt (errorTail S rr rows (errorStep S rr row t)) k : ℝ) / (S : ℝ)
          convert hrec using 1 <;> omega

private theorem rowTrace_length (S : Int) (C : Bounds) (n j : Nat) (row : TraceRow) :
    (rowTrace S C n j row).length = n + 1 := by
  induction n generalizing j row with
  | zero => rfl
  | succ n ih => simp [rowTrace, ih]

/-- The archived integer `errors` list bounds the remainder of every
actual complex iterate through the requested horizon, uniformly on the
entire closed rational disk and the entire real parameter chart. -/
theorem errors_sound {S : Int} (hS : 0 < S)
    {C : Bounds} {c : ℝ} (hc : RealEnclosed S C c)
    (N n : Nat) (hn : n ≤ N) (r : Ratio) (hr : r.den ≠ 0)
    (z : ℂ) (hz : ‖z‖ ≤ (r.num : ℝ) / (r.den : ℝ))
    (j : Nat) (hj : 1 ≤ j) (hjn : j ≤ n) :
    ‖remainder c j z‖ ≤
      (errorAt (errors S (trace S C N) r n) j : ℝ) / (S : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hrr := radius_squared_sound hS r hr
  let rows := ((trace S C N).drop 1).take (n - 1)
  have hlength : rows.length = n - 1 := by
    simp only [rows, List.length_take, List.length_drop, trace, rowTrace_length]
    omega
  have hrows : ∀ k < rows.length, RealRowEnclosed S (rowAt rows k) (1 + k) c := by
    intro k hk
    have hkn : k < n - 1 := by simpa only [hlength] using hk
    have heq : rowAt rows k = rowAt (trace S C N) (k + 1) := by
      dsimp only [rows]
      rw [rowAt_take _ _ _ hkn, rowAt_drop_one]
    rw [heq]
    convert trace_enclosed hS hc N (k + 1) (by omega) using 1 <;> omega
  have hstart : ‖remainder c 1 z‖ ≤ ((0 : Int) : ℝ) / (S : ℝ) := by
    simp [remainder_one]
  have hall := errorTail_sound hS c z _ hz (radiusSquaredUpper S r) hrr
    rows 1 (by omega) 0 hrows hstart
  cases j with
  | zero => omega
  | succ j =>
      cases j with
      | zero => simpa [errors, hn0, errorAt] using hstart
      | succ k =>
          have hk : k < rows.length := by rw [hlength]; omega
          have hh := hall k hk
          change ‖remainder c (k + 1 + 1) z‖ ≤ _
          simpa [errors, hn0, errorAt, rows, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hh

theorem absLo_enclosed {S : Int} (hS : 0 < S)
    {b : Bounds} {x : ℝ} (hx : RealEnclosed S b x) :
    (absLo b : ℝ) / (S : ℝ) ≤ |x| := by
  have h := (realEnclosed_iff hS b x).mp hx
  unfold absLo
  split_ifs
  · exact h.1.trans (le_abs_self x)
  · simpa only [Int.cast_neg, neg_div] using
      (neg_le_neg h.2).trans (neg_le_abs x)
  · simp

private theorem positive_gap_real {S : Int} (hS : 0 < S)
    (row : TraceRow) (t : Int) (r : Ratio) (hr : 0 < r.den)
    (hgap : 0 < gapNumerator S row t r) :
    (absHi row.orbit : ℝ) / (S : ℝ) + (t : ℝ) / (S : ℝ) +
        (r.num : ℝ) / (r.den : ℝ) <
      (absLo row.quadratic : ℝ) / (S : ℝ) *
        ((r.num : ℝ) / (r.den : ℝ)) ^ 2 := by
  have hs := scale_pos hS
  have hd : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast hr
  have hg : (0 : ℝ) <
      (absLo row.quadratic : ℝ) * (r.num : ℝ) * (r.num : ℝ) -
      ((absHi row.orbit : ℝ) + (t : ℝ)) * (r.den : ℝ) * (r.den : ℝ) -
      (S : ℝ) * (r.num : ℝ) * (r.den : ℝ) := by
    exact_mod_cast hgap
  have hl : ((absHi row.orbit : ℝ) / (S : ℝ) + (t : ℝ) / (S : ℝ) +
        (r.num : ℝ) / (r.den : ℝ)) * ((S : ℝ) * (r.den : ℝ) ^ 2) =
      ((absHi row.orbit : ℝ) + (t : ℝ)) * (r.den : ℝ) ^ 2 +
        (S : ℝ) * (r.num : ℝ) * (r.den : ℝ) := by
    field_simp [hs.ne', hd.ne']
    <;> ring
  have hh : ((absLo row.quadratic : ℝ) / (S : ℝ) *
        ((r.num : ℝ) / (r.den : ℝ)) ^ 2) * ((S : ℝ) * (r.den : ℝ) ^ 2) =
      (absLo row.quadratic : ℝ) * (r.num : ℝ) ^ 2 := by
    field_simp [hs.ne', hd.ne']
    <;> ring
  apply (mul_lt_mul_iff_left₀ (mul_pos hs (sq_pos_of_pos hd))).mp
  rw [hl, hh]
  nlinarith [hg]

/-- A positive finite disk margin gives the actual strict comparison
with the quadratic monomial on every point of the boundary circle. -/
theorem positive_margin_quadratic_comparison {S : Int} (hS : 0 < S)
    (c : ℝ) (j : Nat) (row : TraceRow) (hrow : RealRowEnclosed S row j c)
    (t : Int) (r : Ratio) (hr : 0 < r.den)
    (hgap : 0 < gapNumerator S row t r)
    (z : ℂ) (hz : ‖z‖ = (r.num : ℝ) / (r.den : ℝ))
    (ht : ‖remainder c j z‖ ≤ (t : ℝ) / (S : ℝ)) :
    ‖QuadraticEscape.orbit (c : ℂ) j z -
        (quadraticCoefficient j c : ℂ) * z ^ 2‖ +
        (r.num : ℝ) / (r.den : ℝ) <
      ‖(quadraticCoefficient j c : ℂ) * z ^ 2‖ := by
  have hx := abs_enclosed hS hrow.1
  have ha := absLo_enclosed hS hrow.2.2
  have hg := positive_gap_real hS row t r hr hgap
  have hdiff : ‖QuadraticEscape.orbit (c : ℂ) j z -
        (quadraticCoefficient j c : ℂ) * z ^ 2‖ ≤
      (absHi row.orbit : ℝ) / (S : ℝ) + (t : ℝ) / (S : ℝ) := by
    have heq : QuadraticEscape.orbit (c : ℂ) j z -
        (quadraticCoefficient j c : ℂ) * z ^ 2 =
        (LoopsRealPeriod27.polynomial j c : ℂ) + remainder c j z := by
      unfold remainder
      ring
    rw [heq]
    calc
      _ ≤ ‖(LoopsRealPeriod27.polynomial j c : ℂ)‖ + ‖remainder c j z‖ :=
        norm_add_le _ _
      _ ≤ _ := add_le_add (by simpa using hx) ht
  have hquad : (absLo row.quadratic : ℝ) / (S : ℝ) *
        ((r.num : ℝ) / (r.den : ℝ)) ^ 2 ≤
      ‖(quadraticCoefficient j c : ℂ) * z ^ 2‖ := by
    rw [norm_mul, norm_pow, hz]
    simpa using mul_le_mul_of_nonneg_right ha
      (sq_nonneg ((r.num : ℝ) / (r.den : ℝ)))
  exact lt_of_le_of_lt (add_le_add_right hdiff _)
    (lt_of_lt_of_le hg hquad)

/-- Consequently the actual image of the boundary avoids the entire
closed target disk of the same radius. -/
theorem positive_margin_boundary_escape {S : Int} (hS : 0 < S)
    (c : ℝ) (j : Nat) (row : TraceRow) (hrow : RealRowEnclosed S row j c)
    (t : Int) (r : Ratio) (hr : 0 < r.den)
    (hgap : 0 < gapNumerator S row t r)
    (z : ℂ) (hz : ‖z‖ = (r.num : ℝ) / (r.den : ℝ))
    (ht : ‖remainder c j z‖ ≤ (t : ℝ) / (S : ℝ)) :
    (r.num : ℝ) / (r.den : ℝ) < ‖QuadraticEscape.orbit (c : ℂ) j z‖ := by
  have h := positive_margin_quadratic_comparison hS c j row hrow t r hr hgap z hz ht
  have htri := norm_sub_le (QuadraticEscape.orbit (c : ℂ) j z)
    (QuadraticEscape.orbit (c : ℂ) j z - (quadraticCoefficient j c : ℂ) * z ^ 2)
  rw [sub_sub_cancel] at htri
  linarith

end

end LoopsDepthThreeRemainder
