import QuadraticParameterUnivalence
import TelescopeConformalInverse

/-!
# Quantitative parameter stability of actual quadratic inverse branches

Explicit finite recurrences control parameter changes in the physical
orbit. Combined with the compact divided-difference lower bound, they
give one inverse perturbation estimate on all nearby parameter fibers.
-/

namespace LoopsQuadraticParameterDistortion

open Set Function
open QuadraticEscape LoopsQuadraticParameterUnivalence

noncomputable section

/-- A uniform radius for actual iterates on parameter and phase balls. -/
def orbitRadius (C R : ℝ) : ℕ → ℝ
  | 0 => R
  | n+1 => orbitRadius C R n ^ 2 + C

/-- A finite parameter-sensitivity majorant on the same balls. -/
def parameterSensitivity (C R : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => 2 * orbitRadius C R n * parameterSensitivity C R n + 1

theorem orbitRadius_nonneg (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (n : ℕ) :
    0 ≤ orbitRadius C R n := by
  induction n with
  | zero => exact hR
  | succ n ih =>
    exact add_nonneg (sq_nonneg _) hC

theorem parameterSensitivity_nonneg (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (n : ℕ) : 0 ≤ parameterSensitivity C R n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hr := orbitRadius_nonneg C R hC hR n
    change 0 ≤ 2 * orbitRadius C R n * parameterSensitivity C R n + 1
    positivity

/-- No dynamical assumption is needed for this finite orbit radius. -/
theorem orbit_norm_le_radius (C R : ℝ) (d z : ℂ)
    (hd : ‖d‖ ≤ C) (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖orbit d n z‖ ≤ orbitRadius C R n := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    calc
      ‖orbit d (n+1) z‖ ≤ ‖(orbit d n z)^2‖ + ‖d‖ := norm_add_le _ _
      _ = ‖orbit d n z‖^2 + ‖d‖ := by rw [norm_pow]
      _ ≤ orbitRadius C R n ^ 2 + C :=
        add_le_add (pow_le_pow_left₀ (norm_nonneg _) ih 2) hd
      _ = orbitRadius C R (n+1) := rfl

/-- The actual parameter dependence has an explicit uniform Lipschitz
majorant at every finite time, on every bounded phase and parameter ball. -/
theorem orbit_parameter_distortion (C R : ℝ) (d e z : ℂ)
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hd : ‖d‖ ≤ C) (he : ‖e‖ ≤ C) (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖orbit d n z - orbit e n z‖ ≤ parameterSensitivity C R n * ‖d-e‖ := by
  induction n with
  | zero => simp [orbit, parameterSensitivity]
  | succ n ih =>
    have hr := orbitRadius_nonneg C R hC hR n
    have hsum : ‖orbit d n z + orbit e n z‖ ≤ 2 * orbitRadius C R n := by
      have h := norm_add_le (orbit d n z) (orbit e n z)
      have hd' := orbit_norm_le_radius C R d z hd hz n
      have he' := orbit_norm_le_radius C R e z he hz n
      linarith
    have hid : orbit d (n+1) z - orbit e (n+1) z =
        (orbit d n z + orbit e n z) * (orbit d n z - orbit e n z) + (d-e) := by
      simp only [orbit]
      ring
    rw [hid]
    calc
      ‖(orbit d n z + orbit e n z) * (orbit d n z - orbit e n z) + (d-e)‖
          ≤ ‖(orbit d n z + orbit e n z) * (orbit d n z - orbit e n z)‖
            + ‖d-e‖ := norm_add_le _ _
      _ = ‖orbit d n z + orbit e n z‖ * ‖orbit d n z - orbit e n z‖
            + ‖d-e‖ := by rw [norm_mul]
      _ ≤ (2 * orbitRadius C R n) *
            (parameterSensitivity C R n * ‖d-e‖) + ‖d-e‖ :=
        add_le_add_right (mul_le_mul hsum ih (norm_nonneg _) (by positivity)) _
      _ = parameterSensitivity C R (n+1) * ‖d-e‖ := by
        simp only [parameterSensitivity]
        ring

/-- A spatial inverse-distance bound and the explicit parameter majorant
control inverses at different parameters and different target values.
Each target is allowed to belong to its own actual image domain. -/
theorem orbit_inverse_joint_bound (C R δ : ℝ) (n : ℕ) (U : Set ℂ)
    (d e y v : ℂ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hd : ‖d‖ ≤ C) (he : ‖e‖ ≤ C)
    (hU : ∀ z ∈ U, ‖z‖ ≤ R)
    (hsep : ∀ z ∈ U, ∀ w ∈ U,
      δ * ‖z-w‖ ≤ ‖orbit d n z - orbit d n w‖)
    (hy : y ∈ orbit d n '' U) (hv : v ∈ orbit e n '' U) :
    δ * ‖invFunOn (orbit d n) U y - invFunOn (orbit e n) U v‖ ≤
      ‖y-v‖ + parameterSensitivity C R n * ‖d-e‖ := by
  let x := invFunOn (orbit d n) U y
  let w := invFunOn (orbit e n) U v
  have honto_d : SurjOn (orbit d n) U (orbit d n '' U) := fun _ h => h
  have honto_e : SurjOn (orbit e n) U (orbit e n '' U) := fun _ h => h
  have hx : x ∈ U := honto_d.mapsTo_invFunOn hy
  have hw : w ∈ U := honto_e.mapsTo_invFunOn hv
  have hxd : orbit d n x = y := honto_d.rightInvOn_invFunOn hy
  have hwe : orbit e n w = v := honto_e.rightInvOn_invFunOn hv
  change δ * ‖x-w‖ ≤ _
  calc
    δ * ‖x-w‖ ≤ ‖orbit d n x - orbit d n w‖ := hsep x hx w hw
    _ = ‖(y-v) + (v-orbit d n w)‖ := by rw [hxd]; congr 1; ring
    _ ≤ ‖y-v‖ + ‖v-orbit d n w‖ := norm_add_le _ _
    _ = ‖y-v‖ + ‖orbit e n w-orbit d n w‖ := by rw [hwe]
    _ ≤ ‖y-v‖ + parameterSensitivity C R n * ‖e-d‖ :=
      add_le_add_left (orbit_parameter_distortion C R e d w hC hR he hd (hU w hw) n) _
    _ = ‖y-v‖ + parameterSensitivity C R n * ‖d-e‖ := by rw [norm_sub_rev e d]

/-- Compact actual univalent data produce one common positive spatial
constant and one finite parameter constant for the whole nearby inverse
family, while keeping the source closure in any prescribed open ambient set. -/
theorem quadratic_compact_inverse_uniform_bound
    (c : ℂ) (n : ℕ) (K W : Set ℂ)
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hI : InjOn (orbit c n) K)
    (hcrit : ∀ z ∈ K, ∀ j < n, orbit c j z ≠ 0) :
    ∃ (P U : Set ℂ) (δ S : ℝ),
      IsOpen P ∧ c ∈ P ∧ IsOpen U ∧ K ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ W ∧ 0 < δ ∧ 0 ≤ S ∧
      (∀ d ∈ P, InjOn (orbit d n) (closure U)) ∧
      ∀ d ∈ P, ∀ e ∈ P, ∀ y ∈ orbit d n '' U, ∀ v ∈ orbit e n '' U,
        δ * ‖invFunOn (orbit d n) U y - invFunOn (orbit e n) U v‖ ≤
          ‖y-v‖ + S * ‖d-e‖ := by
  obtain ⟨P, U, hP, hcP, hU, hKU, hUc, hUW, δ, hδ, hfam⟩ :=
    quadratic_parameter_univalent_neighborhood_within c n K W hK hW hKW hI hcrit
  obtain ⟨R, hR⟩ := (hUc.image continuous_norm).bddAbove
  let R' : ℝ := max 0 R
  have hR' : 0 ≤ R' := le_max_left _ _
  have hphase : ∀ z ∈ U, ‖z‖ ≤ R' := by
    intro z hz
    exact (hR ⟨z, subset_closure hz, rfl⟩).trans (le_max_right _ _)
  let C : ℝ := ‖c‖ + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let P' := P ∩ Metric.ball c 1
  have hcP' : c ∈ P' := ⟨hcP, by simp⟩
  have hparam : ∀ d ∈ P', ‖d‖ ≤ C := by
    intro d hd
    have hdist : ‖d-c‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hd.2
    have hnorm := norm_add_le (d-c) c
    rw [sub_add_cancel] at hnorm
    dsimp [C]
    linarith
  refine ⟨P', U, δ, parameterSensitivity C R' n,
    hP.inter Metric.isOpen_ball, hcP', hU, hKU, hUc, hUW, hδ,
    parameterSensitivity_nonneg C R' hC hR' n,
    fun d hd => (hfam d hd.1).1, ?_⟩
  intro d hd e he y hy v hv
  apply orbit_inverse_joint_bound C R' δ n U d e y v hC hR'
    (hparam d hd) (hparam e he) hphase
  · intro z hz w hw
    exact (hfam d hd.1).2.2 z (subset_closure hz) w (subset_closure hw)
  · exact hy
  · exact hv

end

end LoopsQuadraticParameterDistortion
