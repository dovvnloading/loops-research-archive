import TwoLevelReference
import TwoLevelPerturbation

/-!
# Exact fibers through a second return

The reference itinerary separates every intermediate phase from its negative.
Consequently a perturbed composition cannot acquire a new sign collision at
an intermediate time. The conclusion concerns the entire complex input disk.
-/

namespace TwoLevelCollisions

open Set Function
open NearTwoShooting LimitingCrestQuadraticReturn

noncomputable section

private theorem separated_from_negative {u v : ℂ} {x : ℝ}
    (hx : (7/5 : ℝ) ≤ |x|)
    (hu : ‖u-(x : ℂ)‖ ≤ 1/5) (hv : ‖v-(x : ℂ)‖ ≤ 1/5) :
    u ≠ -v := by
  intro heq
  have hur := (Complex.abs_re_le_norm (u-(x : ℂ))).trans hu
  have hvr := (Complex.abs_re_le_norm (v-(x : ℂ))).trans hv
  simp only [Complex.sub_re, Complex.ofReal_re] at hur hvr
  have hreal := congrArg Complex.re heq
  simp only [Complex.neg_re] at hreal
  have hxb : |x| ≤ (1/5 : ℝ) := by
    rw [abs_le]
    have hu' := abs_le.mp hur
    have hv' := abs_le.mp hvr
    constructor <;> linarith [hu'.1, hu'.2, hv'.1, hv'.2]
  linarith only [hx, hxb]

/-- The only fibers of a whole second return are the original sign pairs.
The hypothesis concerns one step on a fixed large disk; the result concerns
the complete q-fold composition on the actual second-return input scale. -/
theorem iterate_signed_collision (H : ℂ → ℂ) {q : ℕ} (hq : 17 ≤ q)
    {a b c : ℝ} (h : SharpChart q a b) (hc : c ∈ Icc a b)
    (ε : ℝ) (hε : 0 ≤ ε) (hbudget : ε*(5 : ℝ)^q ≤ 1/10)
    (hclose : ∀ v : ℂ, ‖v‖ ≤ 12/5 → ‖H v-quadraticMap c v‖ ≤ ε)
    (hcollision : ∀ {u v : ℂ}, ‖u‖ ≤ 12/5 → ‖v‖ ≤ 12/5 →
      (H u = H v ↔ u = v ∨ u = -v))
    {z w : ℂ} (hz : ‖z‖ ≤ 14*scale q) (hw : ‖w‖ ≤ 14*scale q) :
    (H^[q]) z = (H^[q]) w ↔ z = w ∨ z = -w := by
  have hband := TwoLevelReference.chart_parameter_band hq h hc
  have hbound (v : ℂ) (hv : ‖v‖ ≤ 14*scale q) (n : ℕ) (hn : n ≤ q) :
      ‖(H^[n]) v‖ ≤ 12/5 :=
    (TwoLevelPerturbation.iterate_stability H c v q ε hε hbudget hclose
      (fun m hm => TwoLevelPerturbation.reference_disk_orbit c hband q hq hv m hm)
      n hn).2
  have hzR : ‖z‖ ≤ 12/5 := by simpa using hbound z hz 0 (by omega)
  have hwR : ‖w‖ ≤ 12/5 := by simpa using hbound w hw 0 (by omega)
  have hphase (n : ℕ) (hn : 1 ≤ n) (hnq : n < q) :
      (H^[n]) z ≠ -((H^[n]) w) := by
    apply separated_from_negative (TwoLevelReference.chart_phase_abs hq h hc hn hnq)
    · exact TwoLevelPerturbation.perturbed_phase_displacement
        H c hband q hq ε hε hbudget hclose hz n hn hnq.le
    · exact TwoLevelPerturbation.perturbed_phase_displacement
        H c hband q hq ε hε hbudget hclose hw n hn hnq.le
  constructor
  · intro heq
    have hcancel : ∀ n : ℕ, n ≤ q → 1 ≤ n →
        (H^[n]) z = (H^[n]) w → H z = H w := by
      intro n
      induction n with
      | zero => intro _ hn _; omega
      | succ n ih =>
        intro hnq hn he
        by_cases hn0 : n = 0
        · subst n
          simpa using he
        · have hn1 : 1 ≤ n := by omega
          rw [iterate_succ_apply', iterate_succ_apply'] at he
          rcases (hcollision (hbound z hz n (by omega))
            (hbound w hw n (by omega))).mp he with hsame | hnegative
          · exact ih (by omega) hn1 hsame
          · exact False.elim (hphase n hn1 (by omega) hnegative)
    exact (hcollision hzR hwR).mp (hcancel q le_rfl (by omega) heq)
  · rintro (heq | heq)
    · rw [heq]
    · have hsame := (hcollision hzR hwR).mpr (Or.inr heq)
      have hq1 : q = (q-1)+1 := by omega
      rw [hq1, iterate_succ_apply, iterate_succ_apply, hsame]

end
end TwoLevelCollisions
