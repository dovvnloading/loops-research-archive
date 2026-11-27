import QuadraticCantorSplitting
import QuadraticCantorExpansion
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Parameter-dependent shadow radii for actual quadratic filled sets

The inverse-root estimate retains the norm of the reference point. An
orbit uniformly separated from zero by a number `s > 1` consequently
has shadows of radius `‖d-c‖ / (s-1)`. For the large-parameter filled
sets, proved orbit geometry supplies `s = sqrt (‖c‖/2)`.
-/

namespace QuadraticCantor

open Set QuadraticEscape

noncomputable section

/-- A sign choice retains the full reference norm in the inverse-root
estimate. The assertion also covers the zero reference point. -/
theorem quadratic_preimage_norm_control (x w : ℂ) :
    ∃ z : ℂ, z^2 = w ∧ ‖x‖ * ‖z-x‖ ≤ ‖w-x^2‖ := by
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
  have hdenom : ‖x‖ ≤ ‖z+x‖ := by linarith
  have hfactor : ‖z-x‖ * ‖z+x‖ = ‖w-x^2‖ := by
    rw [← norm_mul]
    congr 1
    calc
      (z-x)*(z+x) = z^2-x^2 := by ring
      _ = w-x^2 := by rw [hz]
  refine ⟨z, hz, ?_⟩
  calc
    ‖x‖ * ‖z-x‖ = ‖z-x‖ * ‖x‖ := mul_comm _ _
    _ ≤ ‖z-x‖ * ‖z+x‖ :=
      mul_le_mul_of_nonneg_left hdenom (norm_nonneg _)
    _ = ‖w-x^2‖ := hfactor

/-- A fixed error budget is preserved by every finite backward lift
when the reference separation pays for the parameter perturbation. -/
theorem finite_orbit_shadow_budget (c d z : ℂ) (s r : ℝ)
    (hs : 1 < s) (hr : 0 ≤ r)
    (hsep : ∀ n : ℕ, s ≤ ‖orbit c n z‖)
    (hbudget : ‖d-c‖ ≤ (s-1)*r) (N : ℕ) :
    ∃ w : ℂ, ∀ n ≤ N, ‖orbit d n w-orbit c n z‖ ≤ r := by
  induction N generalizing z with
  | zero =>
    refine ⟨z, ?_⟩
    intro n hn
    have hn0 : n = 0 := by omega
    subst n
    simpa only [orbit, sub_self, norm_zero] using hr
  | succ N ih =>
    have hsep' : ∀ n : ℕ, s ≤ ‖orbit c n (z^2+c)‖ := by
      intro n
      rw [orbit_shift]
      exact hsep (n+1)
    obtain ⟨v, hv⟩ := ih (z^2+c) hsep'
    obtain ⟨w, hw, hdist⟩ := quadratic_preimage_norm_control z (v-d)
    have hstep : w^2+d = v := by rw [hw, sub_add_cancel]
    have hbase : ‖w-z‖ ≤ r := by
      have hzero : ‖v-(z^2+c)‖ ≤ r := hv 0 (Nat.zero_le _)
      have herr : ‖v-d-z^2‖ ≤ s*r := by
        calc
          ‖v-d-z^2‖ = ‖(v-(z^2+c))+(c-d)‖ := by congr 1; ring
          _ ≤ ‖v-(z^2+c)‖ + ‖c-d‖ := norm_add_le _ _
          _ ≤ r + (s-1)*r := by
            rw [norm_sub_rev c d]
            exact add_le_add hzero hbudget
          _ = s*r := by ring
      have hscale : s*‖w-z‖ ≤ s*r :=
        (mul_le_mul_of_nonneg_right (hsep 0) (norm_nonneg _)).trans
          (hdist.trans herr)
      exact (mul_le_mul_iff_right₀ (by linarith : 0 < s)).mp hscale
    refine ⟨w, ?_⟩
    intro n hn
    cases n with
    | zero => exact hbase
    | succ n =>
      rw [← orbit_shift, hstep, ← orbit_shift]
      exact hv n (by omega)

/-- A single point realizes the error budget simultaneously at every
time; the compactness argument does not assume compatible finite roots. -/
theorem infinite_orbit_shadow_budget (c d z : ℂ) (s r : ℝ)
    (hs : 1 < s) (hr : 0 ≤ r)
    (hsep : ∀ n : ℕ, s ≤ ‖orbit c n z‖)
    (hbudget : ‖d-c‖ ≤ (s-1)*r) :
    ∃ w : ℂ, ∀ n : ℕ, ‖orbit d n w-orbit c n z‖ ≤ r := by
  let S : ℕ → Set ℂ := fun N =>
    {w | ∀ n ≤ N, ‖orbit d n w-orbit c n z‖ ≤ r}
  have hclosed (N : ℕ) : IsClosed (S N) := by
    have he : S N = ⋂ n : Fin (N+1),
        {w : ℂ | ‖orbit d n.val w-orbit c n.val z‖ ≤ r} := by
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
    apply (isCompact_closedBall z r).of_isClosed_subset (hclosed N)
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hw 0 (Nat.zero_le _)
  have hnonempty (N : ℕ) : (S N).Nonempty :=
    finite_orbit_shadow_budget c d z s r hs hr hsep hbudget N
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

/-- The shadow belongs to the actual new filled set, with an explicit
uniform radius paid for by the reference orbit's separation. -/
theorem filled_orbit_shadow_budget (c d z : ℂ) (s r : ℝ)
    (hs : 1 < s) (hr : 0 ≤ r) (hz : z ∈ filled c)
    (hsep : ∀ n : ℕ, s ≤ ‖orbit c n z‖)
    (hbudget : ‖d-c‖ ≤ (s-1)*r) :
    ∃ w : ℂ, w ∈ filled d ∧
      ∀ n : ℕ, ‖orbit d n w-orbit c n z‖ ≤ r := by
  obtain ⟨w, hw⟩ := infinite_orbit_shadow_budget c d z s r hs hr hsep hbudget
  refine ⟨w, ?_, hw⟩
  apply (escape_zero_iff_bounded d w).mpr
  refine ⟨r+(1+‖c‖), ?_⟩
  intro n
  calc
    ‖orbit d n w‖ ≤ ‖orbit d n w-orbit c n z‖ + ‖orbit c n z‖ := by
      simpa only [sub_add_cancel] using
        (norm_add_le (orbit d n w-orbit c n z) (orbit c n z))
    _ ≤ r+(1+‖c‖) :=
      add_le_add (hw n) (escape_zero_orbit_bound c z hz n)

/-- Separation by `s > 1` gives the explicit all-time shadow radius
`‖d-c‖/(s-1)` at every new parameter. -/
theorem separated_filled_orbit_shadow (c d z : ℂ) (s : ℝ)
    (hs : 1 < s) (hz : z ∈ filled c)
    (hsep : ∀ n : ℕ, s ≤ ‖orbit c n z‖) :
    ∃ w : ℂ, w ∈ filled d ∧
      ∀ n : ℕ, ‖orbit d n w-orbit c n z‖ ≤ ‖d-c‖/(s-1) := by
  have hspos : 0 < s-1 := by linarith
  apply filled_orbit_shadow_budget c d z s (‖d-c‖/(s-1)) hs
    (div_nonneg (norm_nonneg _) hspos.le) hz hsep
  rw [mul_div_cancel₀ _ hspos.ne']

/-- The proved large-parameter orbit geometry supplies the actual
square-root separation scale without an additional expansion premise. -/
theorem filled_norm_sqrt_parameter {c z : ℂ} (hc : 8 ≤ ‖c‖)
    (hz : z ∈ filled c) : Real.sqrt (‖c‖/2) ≤ ‖z‖ := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity : 0 ≤ ‖c‖/2)]
  exact filled_norm_sq_lower hc hz

private theorem parameter_separation_ge_two {c : ℂ} (hc : 8 ≤ ‖c‖) :
    2 ≤ Real.sqrt (‖c‖/2) := by
  apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity : 0 ≤ ‖c‖/2)]
  nlinarith

/-- Stronger actual-orbit shadowing retains the parameter's square-root
scale; its coefficient decreases as the reference parameter grows. -/
theorem large_parameter_orbit_shadow_radius (c d z : ℂ)
    (hc : 8 ≤ ‖c‖) (hz : z ∈ filled c) :
    ∃ w : ℂ, w ∈ filled d ∧
      ∀ n : ℕ, ‖orbit d n w-orbit c n z‖ ≤
        ‖d-c‖/(Real.sqrt (‖c‖/2)-1) := by
  apply separated_filled_orbit_shadow c d z (Real.sqrt (‖c‖/2))
    (by linarith [parameter_separation_ge_two hc]) hz
  intro n
  exact filled_norm_sqrt_parameter hc (filled_iterate hz n)

/-- Uniform physical separation on both filled sets gives a Hausdorff
bound with the same explicit reciprocal separation coefficient. -/
theorem filled_hausdorff_of_uniform_separation (c d : ℂ) (s : ℝ)
    (hs : 1 < s) (hc : ∀ z ∈ filled c, s ≤ ‖z‖)
    (hd : ∀ z ∈ filled d, s ≤ ‖z‖) :
    Metric.hausdorffDist (filled c) (filled d) ≤ ‖d-c‖/(s-1) := by
  apply Metric.hausdorffDist_le_of_mem_dist
    (div_nonneg (norm_nonneg _) (by linarith : 0 ≤ s-1))
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := separated_filled_orbit_shadow c d x s hs hx
      (fun n => hc _ (filled_iterate hx n))
    refine ⟨y, hy, ?_⟩
    simpa only [orbit, dist_eq_norm, norm_sub_rev] using hxy 0
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := separated_filled_orbit_shadow d c y s hs hy
      (fun n => hd _ (filled_iterate hy n))
    refine ⟨x, hx, ?_⟩
    simpa only [orbit, dist_eq_norm, norm_sub_rev] using hyx 0

/-- The Hausdorff Lipschitz constant improves with the smaller of the
two actual square-root parameter scales, with no smallness assumption
on the distance between the parameters. -/
theorem filled_hausdorff_radius (c d : ℂ)
    (hc : 8 ≤ ‖c‖) (hd : 8 ≤ ‖d‖) :
    Metric.hausdorffDist (filled c) (filled d) ≤
      ‖d-c‖ / (min (Real.sqrt (‖c‖/2)) (Real.sqrt (‖d‖/2))-1) := by
  apply filled_hausdorff_of_uniform_separation c d
    (min (Real.sqrt (‖c‖/2)) (Real.sqrt (‖d‖/2)))
  · have hmin : 2 ≤ min (Real.sqrt (‖c‖/2)) (Real.sqrt (‖d‖/2)) :=
      le_min (parameter_separation_ge_two hc) (parameter_separation_ge_two hd)
    linarith
  · intro z hz
    exact (min_le_left _ _).trans (filled_norm_sqrt_parameter hc hz)
  · intro z hz
    exact (min_le_right _ _).trans (filled_norm_sqrt_parameter hd hz)

/-- The actual filled-set map has arbitrarily small Lipschitz constants
uniformly outside a sufficiently large parameter disk. The explicit
threshold is `max 8 (2 * (1 + ε⁻¹)^2)`. -/
theorem filled_hausdorff_small_lipschitz_at_infinity (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 8 ≤ R ∧ ∀ c d : ℂ, R ≤ ‖c‖ → R ≤ ‖d‖ →
      Metric.hausdorffDist (filled c) (filled d) ≤ ε*‖d-c‖ := by
  let s : ℝ := 1+ε⁻¹
  let R : ℝ := max 8 (2*s^2)
  have hs : 1 < s := by
    have hi : 0 < ε⁻¹ := inv_pos.mpr hε
    dsimp [s]
    linarith
  have hR : 8 ≤ R := le_max_left _ _
  have hRscale : 2*s^2 ≤ R := le_max_right _ _
  refine ⟨R, hR, ?_⟩
  intro c d hc hd
  have hsep : ∀ p : ℂ, R ≤ ‖p‖ → ∀ z ∈ filled p, s ≤ ‖z‖ := by
    intro p hp z hz
    apply (sq_le_sq₀ (by linarith : 0 ≤ s) (norm_nonneg _)).mp
    have hb := filled_norm_sq_lower (hR.trans hp) hz
    linarith
  have hb := filled_hausdorff_of_uniform_separation c d s hs
    (hsep c hc) (hsep d hd)
  have he : s-1 = ε⁻¹ := by dsimp [s]; ring
  simpa only [he, div_inv_eq_mul, mul_comm] using hb

end

end QuadraticCantor
