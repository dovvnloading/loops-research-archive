import QuadraticOrbitShadowing
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Quantitative structural stability of actual quadratic filled sets

Whole-orbit shadows are unique in a fixed small tube around a separated
orbit. Compactness of the closed shadow relation makes the resulting
bijection a homeomorphism. The conjugacy and its displacement bound hold
for the actual quadratic iterates, at every forward time.
-/

namespace QuadraticCantor

open Set Function QuadraticEscape

noncomputable section

/-- Two orbits of the same quadratic cannot stay within distance one
of the same reference orbit of norm at least two unless they coincide. -/
theorem orbit_shadow_unique (c d x y z : ℂ) (ε : ℝ) (hε : ε ≤ 1)
    (hsep : ∀ n : ℕ, 2 ≤ ‖orbit c n x‖)
    (hy : ∀ n : ℕ, ‖orbit d n y - orbit c n x‖ ≤ ε)
    (hz : ∀ n : ℕ, ‖orbit d n z - orbit c n x‖ ≤ ε) : y = z := by
  have hsum (n : ℕ) : 2 ≤ ‖orbit d n y + orbit d n z‖ := by
    let X := orbit c n x
    let Y := orbit d n y
    let Z := orbit d n z
    have hXY : ‖X-Y‖ ≤ ε := by simpa only [norm_sub_rev] using hy n
    have hXZ : ‖X-Z‖ ≤ ε := by simpa only [norm_sub_rev] using hz n
    have htriangle : 2 * ‖X‖ ≤ ‖X-Y‖ + ‖Y+Z‖ + ‖X-Z‖ := by
      calc
        2 * ‖X‖ = ‖(X-Y)+(Y+Z)+(X-Z)‖ := by
          rw [show (X-Y)+(Y+Z)+(X-Z) = (2 : ℂ)*X by ring,
            norm_mul, Complex.norm_two]
        _ ≤ ‖(X-Y)+(Y+Z)‖ + ‖X-Z‖ := norm_add_le _ _
        _ ≤ ‖X-Y‖ + ‖Y+Z‖ + ‖X-Z‖ :=
          add_le_add_right (norm_add_le _ _) _
    have hX : 2 ≤ ‖X‖ := hsep n
    change 2 ≤ ‖Y+Z‖
    linarith
  have hstep (n : ℕ) :
      2 * ‖orbit d n y-orbit d n z‖ ≤
        ‖orbit d (n+1) y-orbit d (n+1) z‖ := by
    have he : orbit d (n+1) y-orbit d (n+1) z =
        (orbit d n y-orbit d n z)*(orbit d n y+orbit d n z) := by
      simp only [orbit]
      ring
    rw [he, norm_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hsum n)
      (norm_nonneg (orbit d n y-orbit d n z))
  have hgrow (n : ℕ) :
      (2 : ℝ)^n * ‖y-z‖ ≤ ‖orbit d n y-orbit d n z‖ := by
    induction n with
    | zero => simp only [pow_zero, one_mul, orbit, le_refl]
    | succ n ih =>
      calc
        (2 : ℝ)^(n+1)*‖y-z‖ = 2*((2 : ℝ)^n*‖y-z‖) := by
          rw [pow_succ]
          ring
        _ ≤ 2*‖orbit d n y-orbit d n z‖ := by linarith
        _ ≤ _ := hstep n
  have hbound (n : ℕ) : ‖orbit d n y-orbit d n z‖ ≤ 2*ε := by
    calc
      ‖orbit d n y-orbit d n z‖ =
          ‖(orbit d n y-orbit c n x)+(orbit c n x-orbit d n z)‖ := by
            congr 1
            ring
      _ ≤ ‖orbit d n y-orbit c n x‖ + ‖orbit c n x-orbit d n z‖ :=
        norm_add_le _ _
      _ ≤ 2*ε := by
        rw [norm_sub_rev (orbit c n x) (orbit d n z)]
        linarith [hy n, hz n]
  by_contra hne
  have hpos : 0 < ‖y-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2*ε/‖y-z‖)
    (by norm_num : (1 : ℝ) < 2)
  have hlarge : 2*ε < (2 : ℝ)^n*‖y-z‖ := (div_lt_iff₀ hpos).mp hn
  exact (not_lt_of_ge ((hgrow n).trans (hbound n))) hlarge

/-- The genuine filled sets satisfy a global Lipschitz Hausdorff bound
throughout the proved large-parameter regime. No smallness hypothesis
on the parameter difference is needed for this setwise estimate. -/
theorem filled_hausdorff_lipschitz (c d : ℂ)
    (hc : 8 ≤ ‖c‖) (hd : 8 ≤ ‖d‖) :
    Metric.hausdorffDist (filled c) (filled d) ≤ ‖d-c‖ := by
  apply Metric.hausdorffDist_le_of_mem_dist (norm_nonneg _) 
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := large_parameter_orbit_shadow c d x hc hx
    refine ⟨y, hy, ?_⟩
    simpa only [orbit, dist_eq_norm, norm_sub_rev] using hxy 0
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := large_parameter_orbit_shadow d c y hd hy
    refine ⟨x, hx, ?_⟩
    simpa only [orbit, dist_eq_norm, norm_sub_rev] using hyx 0

/-- The all-time shadow relation is closed in the product of the actual
filled Julia sets. This provides continuity without choosing symbolic
labels coherently as the parameter varies. -/
theorem orbit_shadow_relation_closed (c d : ℂ) :
    IsClosed {p : filled c × filled d |
      ∀ n : ℕ, ‖orbit d n p.2-orbit c n p.1‖ ≤ ‖d-c‖} := by
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro n
  have hc : Continuous (fun p : filled c × filled d => orbit c n p.1) :=
    (orbit_continuous n).comp
      (continuous_const.prodMk (continuous_subtype_val.comp continuous_fst))
  have hd : Continuous (fun p : filled c × filled d => orbit d n p.2) :=
    (orbit_continuous n).comp
      (continuous_const.prodMk (continuous_subtype_val.comp continuous_snd))
  exact isClosed_le (hd.sub hc).norm continuous_const

/-- Nearby large-parameter quadratics have a genuine near-identity
topological conjugacy. Its displacement is bounded by the parameter
distance simultaneously along every actual forward iterate. -/
theorem filled_structural_conjugacy (c d : ℂ)
    (hc : 8 ≤ ‖c‖) (hd : 8 ≤ ‖d‖) (hclose : ‖d-c‖ ≤ 1) :
    ∃ h : filled c ≃ₜ filled d,
      Semiconj h (filledMap c) (filledMap d) ∧
      ∀ (x : filled c) (n : ℕ),
        ‖orbit d n (h x)-orbit c n x‖ ≤ ‖d-c‖ := by
  letI : CompactSpace (filled c) := isCompact_iff_compactSpace.mp (filled_compact c)
  letI : CompactSpace (filled d) := isCompact_iff_compactSpace.mp (filled_compact d)
  let R : Set (filled c × filled d) :=
    {p | ∀ n : ℕ, ‖orbit d n p.2-orbit c n p.1‖ ≤ ‖d-c‖}
  have hR : IsClosed R := orbit_shadow_relation_closed c d
  letI : CompactSpace R := isCompact_iff_compactSpace.mp hR.isCompact
  let f : R → filled c := fun p => p.val.1
  let g : R → filled d := fun p => p.val.2
  have hf : Continuous f := continuous_fst.comp continuous_subtype_val
  have hg : Continuous g := continuous_snd.comp continuous_subtype_val
  have hfb : Bijective f := by
    constructor
    · intro p q hpq
      have hfirst : p.val.1 = q.val.1 := hpq
      have hsecond : (p.val.2 : ℂ) = q.val.2 := by
        apply orbit_shadow_unique c d p.val.1 p.val.2 q.val.2 ‖d-c‖ hclose
        · intro n
          exact filled_norm_ge_two hc (filled_iterate p.val.1.property n)
        · exact p.property
        · intro n
          rw [hfirst]
          exact q.property n
      exact Subtype.ext (Prod.ext hfirst (Subtype.ext hsecond))
    · intro x
      obtain ⟨y, hy, hxy⟩ := large_parameter_orbit_shadow c d x hc x.property
      exact ⟨⟨(x, ⟨y, hy⟩), hxy⟩, rfl⟩
  have hgb : Bijective g := by
    constructor
    · intro p q hpq
      have hsecond : p.val.2 = q.val.2 := hpq
      have hfirst : (p.val.1 : ℂ) = q.val.1 := by
        apply orbit_shadow_unique d c p.val.2 p.val.1 q.val.1 ‖d-c‖ hclose
        · intro n
          exact filled_norm_ge_two hd (filled_iterate p.val.2.property n)
        · intro n
          rw [norm_sub_rev]
          exact p.property n
        · intro n
          rw [norm_sub_rev, hsecond]
          exact q.property n
      exact Subtype.ext (Prod.ext (Subtype.ext hfirst) hsecond)
    · intro y
      obtain ⟨x, hx, hyx⟩ := large_parameter_orbit_shadow d c y hd y.property
      have hxy : ∀ n : ℕ, ‖orbit d n y-orbit c n x‖ ≤ ‖d-c‖ := by
        intro n
        simpa only [norm_sub_rev] using hyx n
      exact ⟨⟨(⟨x, hx⟩, y), hxy⟩, rfl⟩
  let F : R ≃ₜ filled c :=
    (Equiv.ofBijective f hfb).toHomeomorphOfContinuousClosed hf hf.isClosedMap
  let G : R ≃ₜ filled d :=
    (Equiv.ofBijective g hgb).toHomeomorphOfContinuousClosed hg hg.isClosedMap
  let h : filled c ≃ₜ filled d := F.symm.trans G
  have hshadow (x : filled c) (n : ℕ) :
      ‖orbit d n (h x)-orbit c n x‖ ≤ ‖d-c‖ := by
    have hfirst : (F.symm x).val.1 = x := F.apply_symm_apply x
    change ‖orbit d n ((F.symm x).val.2)-orbit c n x‖ ≤ ‖d-c‖
    have hp := (F.symm x).property n
    rw [hfirst] at hp
    exact hp
  refine ⟨h, ?_, hshadow⟩
  intro x
  apply Subtype.ext
  apply orbit_shadow_unique c d (filledMap c x) (h (filledMap c x))
    (filledMap d (h x)) ‖d-c‖ hclose
  · intro n
    exact filled_norm_ge_two hc (filled_iterate (filledMap c x).property n)
  · exact hshadow (filledMap c x)
  · intro n
    change ‖orbit d n ((h x : ℂ)^2+d)-orbit c n ((x : ℂ)^2+c)‖ ≤ ‖d-c‖
    rw [orbit_shift, orbit_shift]
    exact hshadow x (n+1)

/-- In particular, the entire actual filled sets can be conjugated
with pointwise displacement at most the parameter distance. -/
theorem filled_near_identity_conjugacy (c d : ℂ)
    (hc : 8 ≤ ‖c‖) (hd : 8 ≤ ‖d‖) (hclose : ‖d-c‖ ≤ 1) :
    ∃ h : filled c ≃ₜ filled d,
      Semiconj h (filledMap c) (filledMap d) ∧
      ∀ x : filled c, ‖(h x : ℂ)-(x : ℂ)‖ ≤ ‖d-c‖ := by
  obtain ⟨h, hsemi, hbound⟩ := filled_structural_conjugacy c d hc hd hclose
  exact ⟨h, hsemi, fun x => hbound x 0⟩

end

end QuadraticCantor
