import TelescopeUnivalentCollars

/-!
# Parameter-stable univalent neighborhoods of actual quadratic compacta

The divided difference of the physical quadratic iterate stays away from
zero on a common parameter and phase neighborhood of a compact univalent
core with no preterminal critical encounter. The resulting inverse-distance
bound is uniform over that parameter neighborhood.
-/

namespace LoopsQuadraticParameterUnivalence

open Set QuadraticEscape LoopsTelescopeRamification
open scoped Topology

/-- The polynomial divided difference, including its values on the diagonal. -/
noncomputable def orbitDividedDifference (c x y : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => (orbit c n x + orbit c n y) * orbitDividedDifference c x y n

/-- Exact factorization of the difference of two actual orbit values. -/
theorem orbit_sub_eq_mul_dividedDifference (c x y : ℂ) (n : ℕ) :
    orbit c n x - orbit c n y =
      (x-y) * orbitDividedDifference c x y n := by
  induction n with
  | zero => simp [orbit, orbitDividedDifference]
  | succ n ih =>
    calc
      orbit c (n+1) x - orbit c (n+1) y =
          (orbit c n x - orbit c n y) * (orbit c n x + orbit c n y) := by
        simp only [orbit]
        ring
      _ = (x-y) * orbitDividedDifference c x y (n+1) := by
        rw [ih]
        simp only [orbitDividedDifference]
        ring

/-- On the diagonal every preterminal critical encounter is excluded. -/
theorem orbitDividedDifference_diagonal_ne_zero (c x : ℂ) (n : ℕ)
    (hcrit : ∀ j < n, orbit c j x ≠ 0) :
    orbitDividedDifference c x x n ≠ 0 := by
  induction n with
  | zero => simp [orbitDividedDifference]
  | succ n ih =>
    change (orbit c n x + orbit c n x) * orbitDividedDifference c x x n ≠ 0
    apply mul_ne_zero
    · intro h
      apply hcrit n (Nat.lt_succ_self n)
      linear_combination (1/2 : ℂ) * h
    · exact ih (fun j hj => hcrit j (Nat.lt_succ_of_lt hj))

/-- Compact-core injectivity handles distinct points, and critical avoidance
handles the diagonal. No lower bound is included among the hypotheses. -/
theorem orbitDividedDifference_ne_zero (c : ℂ) (n : ℕ) (C : Set ℂ)
    (hI : InjOn (orbit c n) C)
    (hcrit : ∀ z ∈ C, ∀ j < n, orbit c j z ≠ 0)
    (x y : ℂ) (hx : x ∈ C) (hy : y ∈ C) :
    orbitDividedDifference c x y n ≠ 0 := by
  intro hzero
  have hdiff := orbit_sub_eq_mul_dividedDifference c x y n
  rw [hzero, mul_zero] at hdiff
  have hxy : x = y := hI hx hy (sub_eq_zero.mp hdiff)
  subst y
  exact orbitDividedDifference_diagonal_ne_zero c x n (hcrit x hx) hzero

/-- Joint continuity includes the parameter and both phase variables. -/
theorem orbitDividedDifference_continuous (n : ℕ) :
    Continuous (fun p : ℂ × (ℂ × ℂ) =>
      orbitDividedDifference p.1 p.2.1 p.2.2 n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hx : Continuous (fun p : ℂ × (ℂ × ℂ) => orbit p.1 n p.2.1) :=
      (orbit_continuous n).comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have hy : Continuous (fun p : ℂ × (ℂ × ℂ) => orbit p.1 n p.2.2) :=
      (orbit_continuous n).comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
    exact (hx.add hy).mul ih

/-- One phase neighborhood works for all parameters in an open neighborhood
of the base parameter, with a common positive inverse-distance constant.
The compact core may be disconnected or empty, and the time may be zero. -/
theorem quadratic_parameter_univalent_neighborhood (c : ℂ) (n : ℕ) (C : Set ℂ)
    (hC : IsCompact C) (hI : InjOn (orbit c n) C)
    (hcrit : ∀ z ∈ C, ∀ j < n, orbit c j z ≠ 0) :
    ∃ P U : Set ℂ, IsOpen P ∧ c ∈ P ∧ IsOpen U ∧ C ⊆ U ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ P,
        InjOn (orbit d n) U ∧
        ∀ z ∈ U, ∀ w ∈ U,
          δ * ‖z-w‖ ≤ ‖orbit d n z - orbit d n w‖ := by
  have hnorm : Continuous (fun p : ℂ × ℂ =>
      ‖orbitDividedDifference c p.1 p.2 n‖) :=
    ((orbitDividedDifference_continuous n).comp
      (continuous_const.prodMk continuous_id)).norm
  obtain ⟨m, hm, hbound⟩ := (hC.prod hC).exists_forall_le' hnorm.continuousOn
    (a := (0 : ℝ))
    (fun p hp => norm_pos_iff.mpr
      (orbitDividedDifference_ne_zero c n C hI hcrit p.1 p.2 hp.1 hp.2))
  let O : Set (ℂ × (ℂ × ℂ)) :=
    {p | m/2 < ‖orbitDividedDifference p.1 p.2.1 p.2.2 n‖}
  have hO : IsOpen O :=
    isOpen_lt continuous_const (orbitDividedDifference_continuous n).norm
  have hbase : ({c} : Set ℂ) ×ˢ (C ×ˢ C) ⊆ O := by
    intro p hp
    have hpc : p.1 = c := Set.mem_singleton_iff.mp hp.1
    change m/2 < ‖orbitDividedDifference p.1 p.2.1 p.2.2 n‖
    rw [hpc]
    exact lt_of_lt_of_le (by linarith) (hbound p.2 hp.2)
  obtain ⟨P, Q, hP, hQ, hcP, hCQ, hPQ⟩ :=
    generalized_tube_lemma isCompact_singleton (hC.prod hC) hO hbase
  obtain ⟨A, B, hA, hB, hCA, hCB, hAB⟩ :=
    generalized_tube_lemma hC hC hQ hCQ
  let U := A ∩ B
  refine ⟨P, U, hP, hcP (by simp), hA.inter hB,
    fun z hz => ⟨hCA hz, hCB hz⟩, m/2, by positivity, ?_⟩
  intro d hd
  have hdifference : ∀ z ∈ U, ∀ w ∈ U,
      m/2 < ‖orbitDividedDifference d z w n‖ := by
    intro z hz w hw
    exact hPQ ⟨hd, hAB ⟨hz.1, hw.2⟩⟩
  refine ⟨?_, ?_⟩
  · intro z hz w hw heq
    have hnonzero : orbitDividedDifference d z w n ≠ 0 :=
      norm_pos_iff.mp (lt_trans (by positivity) (hdifference z hz w hw))
    have hmul : (z-w) * orbitDividedDifference d z w n = 0 := by
      rw [← orbit_sub_eq_mul_dividedDifference, heq, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hnonzero)
  · intro z hz w hw
    calc
      m/2 * ‖z-w‖ ≤ ‖orbitDividedDifference d z w n‖ * ‖z-w‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt (hdifference z hz w hw)) (norm_nonneg _)
      _ = ‖orbit d n z - orbit d n w‖ := by
        rw [orbit_sub_eq_mul_dividedDifference, norm_mul]
        ring

/-- The common phase neighborhood can have compact closure inside any
prescribed open ambient neighborhood. Uniform injectivity, critical
avoidance, and the inverse-distance bound hold on the entire closure. -/
theorem quadratic_parameter_univalent_neighborhood_within
    (c : ℂ) (n : ℕ) (C W : Set ℂ)
    (hC : IsCompact C) (hW : IsOpen W) (hCW : C ⊆ W)
    (hI : InjOn (orbit c n) C)
    (hcrit : ∀ z ∈ C, ∀ j < n, orbit c j z ≠ 0) :
    ∃ P U : Set ℂ, IsOpen P ∧ c ∈ P ∧ IsOpen U ∧ C ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ W ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ P,
        InjOn (orbit d n) (closure U) ∧
        (∀ z ∈ closure U, ∀ j < n, orbit d j z ≠ 0) ∧
        ∀ z ∈ closure U, ∀ w ∈ closure U,
          δ * ‖z-w‖ ≤ ‖orbit d n z - orbit d n w‖ := by
  obtain ⟨P, A, hP, hcP, hA, hCA, δ, hδ, hfamily⟩ :=
    quadratic_parameter_univalent_neighborhood c n C hC hI hcrit
  obtain ⟨U, hU, hCU, hUA, hUc⟩ :=
    exists_open_between_and_isCompact_closure hC (hA.inter hW)
      (show C ⊆ A ∩ W from fun z hz => ⟨hCA hz, hCW hz⟩)
  have hclosureA : closure U ⊆ A := fun z hz => (hUA hz).1
  refine ⟨P, U, hP, hcP, hU, hCU, hUc,
    fun z hz => (hUA hz).2, δ, hδ, ?_⟩
  intro d hd
  refine ⟨(hfamily d hd).1.mono hclosureA, ?_, ?_⟩
  · intro z hz
    exact orbit_injOn_no_critical_visits d n A hA (hfamily d hd).1 z (hclosureA hz)
  · intro z hz w hw
    exact (hfamily d hd).2 z (hclosureA hz) w (hclosureA hw)

end LoopsQuadraticParameterUnivalence
