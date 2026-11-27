import QuadraticCantorSplitting
import QuadraticCantorExpansion

/-!
# Quantitative shadowing of separated quadratic orbits

A sign choice for each square root gives finite backward shadows of a
reference orbit separated from zero. Nested compact sets then give one
actual orbit shadowing at every time. Boundedness of the reference orbit
puts the shadow in the genuine bounded-orbit set of the new parameter.
-/

namespace QuadraticCantor

open Set QuadraticEscape

noncomputable section

/-- Of the two square roots, one gives an inverse error at most half
the target error whenever the reference point has norm at least two. -/
theorem quadratic_preimage_near (x w : ℂ) (hx : 2 ≤ ‖x‖) :
    ∃ z : ℂ, z^2 = w ∧ 2 * ‖z-x‖ ≤ ‖w-x^2‖ := by
  obtain ⟨u, hu⟩ := exists_square_root w
  have choose_sign : ∃ z : ℂ, z^2 = w ∧ ‖z-x‖ ≤ ‖z+x‖ := by
    by_cases h : ‖u-x‖ ≤ ‖u+x‖
    · exact ⟨u, hu, h⟩
    · refine ⟨-u, by simpa only [neg_sq] using hu, ?_⟩
      have h₁ : -u-x = -(u+x) := by ring
      have h₂ : -u+x = -(u-x) := by ring
      rw [h₁, h₂, norm_neg, norm_neg]
      exact le_of_lt (lt_of_not_ge h)
  obtain ⟨z, hz, hnear⟩ := choose_sign
  have hsum : 2 * ‖x‖ ≤ ‖z+x‖ + ‖z-x‖ := by
    have ht := norm_sub_le (z+x) (z-x)
    have he : (z+x)-(z-x) = (2 : ℂ)*x := by ring
    simpa only [he, norm_mul, Complex.norm_two] using ht
  have hdenom : 2 ≤ ‖z+x‖ := by linarith
  have hfactor : ‖z-x‖ * ‖z+x‖ = ‖w-x^2‖ := by
    rw [← norm_mul]
    congr 1
    calc
      (z-x)*(z+x) = z^2-x^2 := by ring
      _ = w-x^2 := by rw [hz]
  refine ⟨z, hz, ?_⟩
  calc
    2 * ‖z-x‖ = ‖z-x‖ * 2 := mul_comm _ _
    _ ≤ ‖z-x‖ * ‖z+x‖ :=
      mul_le_mul_of_nonneg_left hdenom (norm_nonneg _)
    _ = ‖w-x^2‖ := hfactor

/-- Every finite segment of a separated reference orbit has an actual
backward lift for the new parameter with the same uniform error budget.
The new parameter need not itself satisfy a large-parameter hypothesis. -/
theorem finite_orbit_shadow (c d z : ℂ)
    (hsep : ∀ n : ℕ, 2 ≤ ‖orbit c n z‖) (N : ℕ) :
    ∃ w : ℂ, ∀ n ≤ N, ‖orbit d n w-orbit c n z‖ ≤ ‖d-c‖ := by
  induction N generalizing z with
  | zero =>
    refine ⟨z, ?_⟩
    intro n hn
    have hn0 : n = 0 := by omega
    subst n
    simp only [orbit, sub_self, norm_zero]
    exact norm_nonneg _
  | succ N ih =>
    have hsep' : ∀ n : ℕ, 2 ≤ ‖orbit c n (z^2+c)‖ := by
      intro n
      rw [orbit_shift]
      exact hsep (n+1)
    obtain ⟨v, hv⟩ := ih (z^2+c) hsep'
    obtain ⟨w, hw, hdist⟩ := quadratic_preimage_near z (v-d) (hsep 0)
    have hstep : w^2+d = v := by rw [hw, sub_add_cancel]
    have hbase : ‖w-z‖ ≤ ‖d-c‖ := by
      have hzero : ‖v-(z^2+c)‖ ≤ ‖d-c‖ := hv 0 (Nat.zero_le _)
      have herr : ‖v-d-z^2‖ ≤ 2*‖d-c‖ := by
        calc
          ‖v-d-z^2‖ = ‖(v-(z^2+c))+(c-d)‖ := by congr 1; ring
          _ ≤ ‖v-(z^2+c)‖ + ‖c-d‖ := norm_add_le _ _
          _ ≤ 2*‖d-c‖ := by rw [norm_sub_rev c d]; linarith
      linarith
    refine ⟨w, ?_⟩
    intro n hn
    cases n with
    | zero => exact hbase
    | succ n =>
      rw [← orbit_shift, hstep, ← orbit_shift]
      exact hv n (by omega)

/-- Finite shadows have a common compact initial-point bound. Taking
their nested intersection supplies a shadow for every iterate, with no
unproved coherence assumption on the choices of finite inverse roots. -/
theorem infinite_orbit_shadow (c d z : ℂ)
    (hsep : ∀ n : ℕ, 2 ≤ ‖orbit c n z‖) :
    ∃ w : ℂ, ∀ n : ℕ, ‖orbit d n w-orbit c n z‖ ≤ ‖d-c‖ := by
  let S : ℕ → Set ℂ := fun N =>
    {w | ∀ n ≤ N, ‖orbit d n w-orbit c n z‖ ≤ ‖d-c‖}
  have hclosed (N : ℕ) : IsClosed (S N) := by
    have he : S N = ⋂ n : Fin (N+1),
        {w : ℂ | ‖orbit d n.val w-orbit c n.val z‖ ≤ ‖d-c‖} := by
      ext w
      simp only [S, mem_setOf_eq, mem_iInter]
      constructor
      · intro hw n
        exact hw n.val (by omega)
      · intro hw n hn
        exact hw ⟨n, by omega⟩
    rw [he]
    apply isClosed_iInter
    intro n
    have ho : Continuous (fun w : ℂ => orbit d n.val w) :=
      (orbit_continuous n.val).comp (continuous_const.prodMk continuous_id)
    exact isClosed_le (ho.sub continuous_const).norm continuous_const
  have hcompact (N : ℕ) : IsCompact (S N) := by
    apply (isCompact_closedBall z ‖d-c‖).of_isClosed_subset (hclosed N)
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hw 0 (Nat.zero_le _)
  have hnonempty (N : ℕ) : (S N).Nonempty :=
    finite_orbit_shadow c d z hsep N
  have hdirected : Directed (· ⊇ ·) S := by
    intro m n
    refine ⟨max m n, ?_, ?_⟩
    · intro w hw k hk
      exact hw k (hk.trans (le_max_left _ _))
    · intro w hw k hk
      exact hw k (hk.trans (le_max_right _ _))
  obtain ⟨w, hw⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      S hdirected hnonempty hcompact hclosed
  exact ⟨w, fun n => (mem_iInter.mp hw n) n le_rfl⟩

/-- A bounded separated reference orbit is shadowed by an orbit in the
genuine filled set of every new parameter. The error is uniform for all
forward times and is at most the distance between the parameters. -/
theorem filled_orbit_shadow (c d z : ℂ) (hz : z ∈ filled c)
    (hsep : ∀ n : ℕ, 2 ≤ ‖orbit c n z‖) :
    ∃ w : ℂ, w ∈ filled d ∧
      ∀ n : ℕ, ‖orbit d n w-orbit c n z‖ ≤ ‖d-c‖ := by
  obtain ⟨w, hw⟩ := infinite_orbit_shadow c d z hsep
  refine ⟨w, ?_, hw⟩
  apply (escape_zero_iff_bounded d w).mpr
  refine ⟨‖d-c‖+(1+‖c‖), ?_⟩
  intro n
  calc
    ‖orbit d n w‖ ≤ ‖orbit d n w-orbit c n z‖ + ‖orbit c n z‖ :=
      by
        simpa only [sub_add_cancel] using
          (norm_add_le (orbit d n w-orbit c n z) (orbit c n z))
    _ ≤ ‖d-c‖+(1+‖c‖) :=
      add_le_add (hw n) (escape_zero_orbit_bound c z hz n)

/-- Every actual bounded orbit at a parameter of norm at least eight
has a uniformly close bounded shadow at any other complex parameter. -/
theorem large_parameter_orbit_shadow (c d z : ℂ) (hc : 8 ≤ ‖c‖)
    (hz : z ∈ filled c) :
    ∃ w : ℂ, w ∈ filled d ∧
      ∀ n : ℕ, ‖orbit d n w-orbit c n z‖ ≤ ‖d-c‖ := by
  exact filled_orbit_shadow c d z hz
    (fun n => filled_norm_ge_two hc (filled_iterate hz n))

end

end QuadraticCantor
