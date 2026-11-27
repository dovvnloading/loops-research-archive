import QuadraticLocalDeckRigidity

/-!
# Continuous inverse obstruction at actual quadratic ramification

At a point with at least one preterminal critical encounter, no single
continuous inverse branch into the constructed local source exists over
any full punctured target disk. This is a topological obstruction, proved
without assuming an analytic candidate inverse or a chosen external marking.
-/

namespace LoopsQuadraticLocalInverseObstruction

open Set Function
open QuadraticEscape LoopsTelescopeRamification
open LoopsQuadraticLocalDeckAction LoopsPowerMapRigidity

namespace PowerChart

variable {f : ℂ → ℂ} {x : ℂ} {m : ℕ} (C : PowerChart f x m)

/-- Every local degree greater than one obstructs a continuous inverse on every full
punctured target disk. The source chart is fixed, but the target radius
is arbitrary and the putative inverse need not be analytic. -/
theorem ramified_no_continuous_section (hm : 1 < m)
    (ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ S : ℂ → ℂ,
      ContinuousOn S (Metric.ball (f x) ε \ {f x}) ∧
      MapsTo S (Metric.ball (f x) ε \ {f x}) C.source ∧
      ∀ w ∈ Metric.ball (f x) ε \ {f x}, f (S w) = w := by
  rintro ⟨S, hS, hmap, hright⟩
  have ha : 0 < ‖C.a‖ := norm_pos_iff.mpr C.a_ne_zero
  let R : ℝ := ε / ‖C.a‖
  have hR : 0 < R := div_pos hε ha
  let L : ℂ → ℂ := fun w => f x + C.a*w
  have hL : MapsTo L (Metric.ball (0 : ℂ) R \ {0})
      (Metric.ball (f x) ε \ {f x}) := by
    intro w hw
    have hwN : ‖w‖ < ε/‖C.a‖ := by
      simpa only [Metric.mem_ball, dist_zero_right, R] using hw.1
    refine ⟨?_, ?_⟩
    · change dist (f x + C.a*w) (f x) < ε
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul]
      exact (lt_div_iff₀' ha).mp hwN
    · intro he
      have he' : f x + C.a*w = f x := Set.mem_singleton_iff.mp he
      have hp : C.a*w = 0 := by linear_combination he'
      have hw0 : w = 0 := (mul_eq_zero.mp hp).resolve_left C.a_ne_zero
      exact hw.2 (Set.mem_singleton_iff.mpr hw0)
  let s : ℂ → ℂ := fun w => C.coord (S (L w))
  have hs : ContinuousOn s (Metric.ball (0 : ℂ) R \ {0}) := by
    have hLc : Continuous L := continuous_const.add (continuous_const.mul continuous_id)
    exact C.coord_analytic.continuousOn.comp
      (hS.comp hLc.continuousOn hL) (fun w hw => hmap (hL hw))
  have hp (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) R \ {0}) : (s w)^m = w := by
    apply mul_left_cancel₀ C.a_ne_zero
    calc
      C.a * (s w)^m = f (S (L w)) - f x :=
        (C.normal_form _ (hmap (hL hw))).symm
      _ = C.a*w := by rw [hright _ (hL hw)]; dsimp [L]; ring
  exact power_no_continuous_section m hm R hR ⟨s, hs, hp⟩

end PowerChart

/-- Every actual ramified quadratic iterate has a physical source
neighborhood on which a continuous choice of one inverse over a full
punctured target neighborhood is impossible. Criticality is expressed
by the actual orbit count, and no cover or monodromy hypothesis is assumed. -/
theorem quadratic_critical_local_no_continuous_section
    (c x : ℂ) (n : ℕ) (hcrit : 0 < criticalVisits c x n) :
    ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧
      ∀ ε : ℝ, 0 < ε →
        ¬ ∃ S : ℂ → ℂ,
          ContinuousOn S (Metric.ball (orbit c n x) ε \ {orbit c n x}) ∧
          MapsTo S (Metric.ball (orbit c n x) ε \ {orbit c n x}) U ∧
          ∀ w ∈ Metric.ball (orbit c n x) ε \ {orbit c n x}, orbit c n (S w) = w := by
  obtain ⟨C⟩ := exists_quadratic_powerChart c x n
  have hdegree : 1 < 2^criticalVisits c x n := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcrit)
    rw [hk, pow_succ]
    have : 0 < (2 : ℕ)^k := by positivity
    omega
  exact ⟨C.source, C.isOpen_source, C.mem_source,
    fun ε hε => C.ramified_no_continuous_section hdegree ε hε⟩

end LoopsQuadraticLocalInverseObstruction
