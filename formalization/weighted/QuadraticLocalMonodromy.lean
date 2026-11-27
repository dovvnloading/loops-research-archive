import QuadraticLocalDeckAction

/-!
# Constructive local monodromy of actual quadratic iterates

A full turn around the local critical value has an explicit continuous
lift in the physical source chart. Every continuous lift with the same
initial point agrees with this one, and its endpoint is the primitive
cyclic sheet action. At nonnegative integer times the lift returns precisely at
multiples of the actual local multiplicity.
-/

namespace LoopsQuadraticLocalMonodromy

open Set Function Polynomial
open LoopsQuadraticLocalDeckAction
open QuadraticEscape LoopsTelescopeRamification

/-- A fractional turn in the degree-m source coordinate. -/
noncomputable def circularPhase (m : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (2*Real.pi*Complex.I*(t : ℂ)/(m : ℂ))

theorem circularPhase_continuous (m : ℕ) : Continuous (circularPhase m) := by
  exact Complex.continuous_exp.comp
    ((continuous_const.mul Complex.continuous_ofReal).div_const (m : ℂ))

theorem circularPhase_norm (m : ℕ) (t : ℝ) : ‖circularPhase m t‖ = 1 := by
  simp [circularPhase, Complex.norm_exp, Complex.div_re, Complex.mul_re, Complex.mul_im]

theorem circularPhase_ne_zero (m : ℕ) (t : ℝ) : circularPhase m t ≠ 0 :=
  Complex.exp_ne_zero _

theorem circularPhase_zero (m : ℕ) : circularPhase m 0 = 1 := by
  simp [circularPhase]

/-- Taking the local power turns a fractional source turn into one
whole target turn, with no choice of a logarithm along the loop. -/
theorem circularPhase_pow (m : ℕ) (hm : 0 < m) (t : ℝ) :
    (circularPhase m t)^m = Complex.exp (2*Real.pi*Complex.I*(t : ℂ)) := by
  unfold circularPhase
  rw [← Complex.exp_nat_mul]
  congr 1
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hm
  field_simp [hmC]

end LoopsQuadraticLocalMonodromy

namespace LoopsQuadraticLocalDeckAction.PowerChart

open Set Function Polynomial
open LoopsQuadraticLocalMonodromy

variable {f : ℂ → ℂ} {x : ℂ} {m : ℕ} (C : PowerChart f x m)

/-- The explicit physical lift of circular motion around the branch value. -/
noncomputable def circularLift (z : ℂ) (t : ℝ) : ℂ :=
  C.inv (circularPhase m t * C.coord z)

theorem circularLift_coordinate_mem (z : ℂ) (hz : z ∈ C.source) (t : ℝ) :
    circularPhase m t * C.coord z ∈ Metric.ball (0 : ℂ) C.r := by
  simpa only [Metric.mem_ball, dist_zero_right, norm_mul,
    circularPhase_norm, one_mul] using C.coord_mapsTo hz

/-- The entire lifted trajectory stays in the one constructed source,
for arbitrary real time and for any number of completed turns. -/
theorem circularLift_mem (z : ℂ) (hz : z ∈ C.source) (t : ℝ) :
    C.circularLift z t ∈ C.source :=
  C.inv_mapsTo (C.circularLift_coordinate_mem z hz t)

theorem circularLift_coord (z : ℂ) (hz : z ∈ C.source) (t : ℝ) :
    C.coord (C.circularLift z t) = circularPhase m t * C.coord z :=
  C.right_inv (C.circularLift_coordinate_mem z hz t)

/-- The formula defines a continuous lift on all real times. -/
theorem circularLift_continuous (z : ℂ) (hz : z ∈ C.source) :
    Continuous (C.circularLift z) :=
  C.inv_analytic.continuousOn.comp_continuous
    ((circularPhase_continuous m).mul continuous_const)
    (C.circularLift_coordinate_mem z hz)

theorem circularLift_zero (z : ℂ) (hz : z ∈ C.source) :
    C.circularLift z 0 = z := by
  simpa only [circularLift, circularPhase_zero, one_mul] using C.left_inv hz

/-- A single target turn lifts to the primitive local sheet generator. -/
theorem circularLift_one (z : ℂ) :
    C.circularLift z 1 = C.deck C.phaseGenerator z := by
  simp only [circularLift, circularPhase, Complex.ofReal_one, mul_one,
    LoopsQuadraticLocalDeckAction.PowerChart.deck,
    LoopsQuadraticLocalDeckAction.PowerChart.phaseGenerator]

/-- Exact image of the constructed trajectory under the original map.
Its target is the Euclidean circle about f(x) through f(z). -/
theorem circularLift_image (z : ℂ) (hz : z ∈ C.source) (t : ℝ) :
    f (C.circularLift z t) =
      f x + (f z-f x) * Complex.exp (2*Real.pi*Complex.I*(t : ℂ)) := by
  have he := C.normal_form (C.circularLift z t) (C.circularLift_mem z hz t)
  rw [C.circularLift_coord z hz t, mul_pow,
    circularPhase_pow m C.degree_pos t] at he
  rw [C.normal_form z hz]
  linear_combination he

/-- A noncentral starting point remains off the branch anchor throughout
the lift; the denominator used for sheet comparison never vanishes. -/
theorem circularLift_ne_center (z : ℂ) (hz : z ∈ C.source)
    (hzx : z ≠ x) (t : ℝ) : C.circularLift z t ≠ x := by
  intro he
  have hp := C.circularLift_coord z hz t
  rw [he, C.coord_center] at hp
  have hz0 : C.coord z ≠ 0 := fun h => hzx ((C.coord_eq_zero_iff z hz).mp h)
  exact mul_ne_zero (circularPhase_ne_zero m t) hz0 hp.symm

/-- The projected circular path avoids the branch value at every real
time when its initial point is noncentral. -/
theorem circularLift_image_ne_center (z : ℂ) (hz : z ∈ C.source)
    (hzx : z ≠ x) (t : ℝ) : f (C.circularLift z t) ≠ f x := by
  intro he
  have hp := C.normal_form (C.circularLift z t) (C.circularLift_mem z hz t)
  rw [he, sub_self, C.circularLift_coord z hz t] at hp
  have hz0 : C.coord z ≠ 0 := fun h => hzx ((C.coord_eq_zero_iff z hz).mp h)
  exact mul_ne_zero C.a_ne_zero
    (pow_ne_zero m (mul_ne_zero (circularPhase_ne_zero m t) hz0)) hp.symm

/-- Any continuous lift staying in this physical source and beginning at
the same noncentral point is the explicit lift throughout the unit interval.
No differentiability, injectivity, or preassigned sheet label is assumed. -/
theorem circularLift_unique (z : ℂ) (hz : z ∈ C.source) (hzx : z ≠ x)
    (γ : ℝ → ℂ) (hγ : ContinuousOn γ (Icc 0 1))
    (hmap : MapsTo γ (Icc 0 1) C.source)
    (hstart : γ 0 = z)
    (himage : ∀ t ∈ Icc (0 : ℝ) 1, f (γ t) =
      f x + (f z-f x) * Complex.exp (2*Real.pi*Complex.I*(t : ℂ))) :
    EqOn γ (C.circularLift z) (Icc 0 1) := by
  let q : ℝ → ℂ := fun t => C.coord (γ t) / (circularPhase m t * C.coord z)
  have hz0 : C.coord z ≠ 0 := fun h => hzx ((C.coord_eq_zero_iff z hz).mp h)
  have hden (t : ℝ) : circularPhase m t * C.coord z ≠ 0 :=
    mul_ne_zero (circularPhase_ne_zero m t) hz0
  have hqcont : ContinuousOn q (Icc 0 1) :=
    (C.coord_analytic.continuousOn.comp hγ hmap).div
      (((circularPhase_continuous m).mul continuous_const).continuousOn)
      (fun t _ => hden t)
  have hqpow (t : ℝ) (ht : t ∈ Icc 0 1) : (q t)^m = 1 := by
    have hp : (C.coord (γ t))^m = (circularPhase m t * C.coord z)^m := by
      apply mul_left_cancel₀ C.a_ne_zero
      rw [← C.circularLift_coord z hz t,
        ← C.normal_form (γ t) (hmap ht),
        ← C.normal_form (C.circularLift z t) (C.circularLift_mem z hz t),
        himage t ht, C.circularLift_image z hz t]
    dsimp [q]
    rw [div_pow, hp, div_self (pow_ne_zero m (hden t))]
  have hsub : q '' Icc 0 1 ⊆ (↑(nthRootsFinset m (1 : ℂ)) : Set ℂ) := by
    rintro _ ⟨t, ht, rfl⟩
    exact (mem_nthRootsFinset C.degree_pos _).mpr (hqpow t ht)
  have hfin : (q '' Icc 0 1).Finite := (Finset.finite_toSet _).subset hsub
  have hconn : IsPreconnected (q '' Icc 0 1) := isPreconnected_Icc.image q hqcont
  have hsingle : (q '' Icc 0 1).Subsingleton := Set.not_nontrivial_iff.mp
    (fun h => (hconn.infinite_of_nontrivial h) hfin)
  have hq0 : q 0 = 1 := by
    dsimp [q]
    rw [hstart, circularPhase_zero, one_mul, div_self hz0]
  intro t ht
  apply C.coord_injOn (hmap ht) (C.circularLift_mem z hz t)
  have hqt : q t = 1 := (hsingle ⟨t, ht, rfl⟩
    ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩).trans hq0
  rw [C.circularLift_coord z hz t]
  have he := (div_eq_iff (hden t)).mp hqt
  simpa only [one_mul] using he

/-- Each completed target turn applies one additional generator to the
physical source point. -/
theorem circularLift_nat (z : ℂ) (hz : z ∈ C.source) (k : ℕ) :
    C.circularLift z (k : ℝ) = (C.deck C.phaseGenerator)^[k] z := by
  have hp : circularPhase m (k : ℝ) = C.phaseGenerator^k := by
    unfold circularPhase LoopsQuadraticLocalDeckAction.PowerChart.phaseGenerator
    rw [← Complex.exp_nat_mul]
    congr 1
    simp only [Complex.ofReal_natCast]
    ring
  rw [C.deck_iterate C.phaseGenerator z C.phaseGenerator_primitive.pow_eq_one hz k]
  simp only [circularLift, hp, LoopsQuadraticLocalDeckAction.PowerChart.deck]

/-- The actual lifted circular motion returns to a noncentral point
precisely after a multiple of its local degree many full turns. -/
theorem circularLift_nat_eq_self_iff (z : ℂ) (hz : z ∈ C.source)
    (hzx : z ≠ x) (k : ℕ) :
    C.circularLift z (k : ℝ) = z ↔ m ∣ k := by
  rw [C.circularLift_nat z hz k]
  exact C.generator_period_iff z hz hzx k

/-- A single turn really changes the selected inverse point whenever
the local degree exceeds one. -/
theorem circularLift_one_ne (hm : 1 < m) (z : ℂ) (hz : z ∈ C.source)
    (hzx : z ≠ x) : C.circularLift z 1 ≠ z := by
  rw [C.circularLift_one z]
  intro he
  rcases (C.deck_fixed_iff C.phaseGenerator z
    C.phaseGenerator_primitive.pow_eq_one hz).mp he with h | h
  · exact C.phaseGenerator_primitive.ne_one hm h
  · exact hzx h

end LoopsQuadraticLocalDeckAction.PowerChart

namespace LoopsQuadraticLocalMonodromy

open Set Function
open LoopsQuadraticLocalDeckAction
open QuadraticEscape LoopsTelescopeRamification

/-- Every finite actual quadratic iterate has a local chart with
constructive, uniquely lifted circular monodromy. Repeated critical
encounters determine the exact number of turns required to return. -/
theorem quadratic_local_circular_monodromy (c x : ℂ) (n : ℕ) :
    ∃ C : PowerChart (orbit c n) x (2^criticalVisits c x n),
      ∀ z ∈ C.source, z ≠ x →
        orbit c n z ≠ orbit c n x ∧ Continuous (C.circularLift z) ∧
        (∀ t : ℝ, C.circularLift z t ∈ C.source ∧
          orbit c n (C.circularLift z t) = orbit c n x +
            (orbit c n z-orbit c n x) * Complex.exp (2*Real.pi*Complex.I*(t : ℂ))) ∧
        C.circularLift z 0 = z ∧
        C.circularLift z 1 = C.deck C.phaseGenerator z ∧
        (∀ k : ℕ, C.circularLift z (k : ℝ) = z ↔ 2^criticalVisits c x n ∣ k) := by
  obtain ⟨C⟩ := exists_quadratic_powerChart c x n
  refine ⟨C, ?_⟩
  intro z hz hzx
  have hnon := C.circularLift_image_ne_center z hz hzx 0
  rw [C.circularLift_zero z hz] at hnon
  exact ⟨hnon, C.circularLift_continuous z hz,
    fun t => ⟨C.circularLift_mem z hz t, C.circularLift_image z hz t⟩,
    C.circularLift_zero z hz, C.circularLift_one z,
    C.circularLift_nat_eq_self_iff z hz hzx⟩

end LoopsQuadraticLocalMonodromy
