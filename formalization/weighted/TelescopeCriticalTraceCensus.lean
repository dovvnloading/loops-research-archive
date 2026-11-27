import TelescopeCriticalExcursions
import CriticalRayGeometry
import PathChoiceTraceCensus

/-!
# Geometrically distinct lifts through the actual critical value

Distinct small central ray directions give independently recoverable
markers. Transport by the actual analytic prefix inverse preserves those
markers. Thus one target path has exponentially many different complete
source traces, not merely different parametrizations of the same trace.
This is a statement about continuous paths, not a transverse-width claim.
-/

namespace LoopsTelescopeCriticalTraceCensus

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeConformalInverse LoopsTelescopeCollar
open LoopsCriticalRayGeometry LoopsPathChoiceTraceCensus
open LoopsTelescopeCriticalExcursions

noncomputable section

/-- In every actual selected one-critical return, for every finite `n`
one target path has exactly `2^n` continuous physical lifts and exactly
`2^n` different geometric source traces. These counts exhaust all lifts
in the complete selected source, without an assumed endpoint condition
or prior finiteness of either counted type. -/
theorem quadratic_return_critical_trace_card_exact
    (c : ℂ) (a b : ℕ) (A B D V : Set ℂ) (x : ℂ)
    (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (_hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ∀ n : ℕ, ∃ γ : C(unitInterval, ℂ),
      (∀ t, γ t ∈ V) ∧ γ 0 = orbit c b c ∧ γ 1 = orbit c b c ∧
      Nat.card {L : C(unitInterval, ℂ) // range L ⊆ A ∧
        ∀ t, orbit c (a+1+b) (L t) = γ t} = 2 ^ n ∧
      Nat.card {K : Set ℂ // ∃ L : C(unitInterval, ℂ),
        range L = K ∧ range L ⊆ A ∧
        ∀ t, orbit c (a+1+b) (L t) = γ t} = 2 ^ n := by
  classical
  have hcD : c ∈ D := by rw [hD]; exact mem_connectedComponentIn hv
  have h0B : (0 : ℂ) ∈ B := by
    rw [hB]
    exact mem_connectedComponentIn (by simpa using hcD)
  have hxA : x ∈ A := by
    rw [hA]
    exact mem_connectedComponentIn (by simpa [hx0] using h0B)
  have hDo : IsOpen D := by
    rw [hD]
    exact (hVo.preimage (quadratic_orbit_continuous c b)).connectedComponentIn
  have hBo : IsOpen B := by
    rw [hB]
    exact (hDo.preimage ((continuous_id.pow 2).add continuous_const)).connectedComponentIn
  have hAo : IsOpen A := by
    rw [hA]
    exact (hBo.preimage (quadratic_orbit_continuous c a)).connectedComponentIn
  have hBc : IsPreconnected B := by rw [hB]; exact isPreconnected_connectedComponentIn
  have hAp : orbit c a '' A = B := by
    rw [hA]
    exact orbit_component_image c a B hBo hBc x (by simpa [hx0] using h0B)
  obtain ⟨g, hgmap, hgleft, hgright, hga, _⟩ :=
    orbit_conformal_inverse c a A B hAo hpinj hAp
  have hg0 : g 0 = x := by rw [← hx0]; exact hgleft hxA
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp hBo 0 h0B
  let r : ℝ := ε / 2
  have hr : 0 < r := half_pos hε
  have hsmall (z : ℂ) (hz : ‖z‖ ≤ r) : z ∈ B := by
    apply hεB
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hz (by dsimp [r]; linarith)
  have hxval : orbit c (a+1+b) x = orbit c b c := by
    rw [quadratic_orbit_add c (a+1) b]
    change orbit c b ((orbit c a x)^2+c) = _
    simp [hx0]
  have hmap : MapsTo (orbit c (a+1+b)) A V := by
    intro z hz
    have hp : orbit c a z ∈ B := hAp ▸ mem_image_of_mem _ hz
    rw [hB] at hp
    have hq : (orbit c a z)^2+c ∈ D :=
      connectedComponentIn_subset ((fun w : ℂ => w^2+c) ⁻¹' D) 0 hp
    rw [hD] at hq
    have hs : orbit c b ((orbit c a z)^2+c) ∈ V :=
      connectedComponentIn_subset (orbit c b ⁻¹' V) c hq
    simpa only [quadratic_orbit_add, orbit] using hs
  intro n
  have heB (i : Fin n) (t : unitInterval) : excursion r i t ∈ B :=
    hsmall _ (excursion_norm_le hr i t)
  have hnB (i : Fin n) (t : unitInterval) : -(excursion r i t) ∈ B :=
    hsmall _ (neg_excursion_norm_le hr i t)
  have hmB (i : Fin n) : marker r i ∈ B := hsmall _ (marker_norm_le hr i)
  let α : Fin n → Path x x := fun i =>
    { toFun := fun t => g (excursion r i t)
      continuous_toFun := hga.continuousOn.comp_continuous (excursion_continuous r i) (heB i)
      source' := by simpa using hg0
      target' := by simpa using hg0 }
  let β : Fin n → Path x x := fun i =>
    { toFun := fun t => g (-(excursion r i t))
      continuous_toFun := hga.continuousOn.comp_continuous (excursion_continuous r i).neg (hnB i)
      source' := by simpa using hg0
      target' := by simpa using hg0 }
  let M : Fin n → ℂ := fun i => g (marker r i)
  have hα (i : Fin n) : range (α i) ⊆ A := by
    rintro _ ⟨t, rfl⟩
    exact hgmap (heB i t)
  have hβ (i : Fin n) : range (β i) ⊆ A := by
    rintro _ ⟨t, rfl⟩
    exact hgmap (hnB i t)
  have hpositive (i j : Fin n) : M j ∈ range (α i) ↔ i = j := by
    constructor
    · rintro ⟨t, ht⟩
      apply (marker_mem_excursion_range_iff hr i j).mp
      refine ⟨t, ?_⟩
      have hp := congrArg (orbit c a) ht
      change orbit c a (g (excursion r i t)) = orbit c a (g (marker r j)) at hp
      simpa only [hgright (heB i t), hgright (hmB j)] using hp
    · rintro rfl
      exact ⟨midpoint, by dsimp [α, M]; rw [excursion_midpoint]⟩
  have hnegative (i j : Fin n) : M j ∉ range (β i) := by
    rintro ⟨t, ht⟩
    apply marker_not_mem_neg_excursion_range hr i j
    refine ⟨t, ?_⟩
    have hp := congrArg (orbit c a) ht
    change orbit c a (g (-(excursion r i t))) = orbit c a (g (marker r j)) at hp
    simpa only [hgright (hnB i t), hgright (hmB j)] using hp
  let F := orbit c (a+1+b)
  have hF : Continuous F := quadratic_orbit_continuous c (a+1+b)
  have hsame (i : Fin n) : (α i).map hF = (β i).map hF := by
    apply Path.ext
    funext t
    change orbit c (a+1+b) (g (excursion r i t)) =
      orbit c (a+1+b) (g (-(excursion r i t)))
    rw [quadratic_orbit_add c (a+1) b, quadratic_orbit_add c (a+1) b]
    change orbit c b ((orbit c a (g (excursion r i t)))^2+c) =
      orbit c b ((orbit c a (g (-(excursion r i t))))^2+c)
    rw [hgright (heB i t), hgright (hnB i t), neg_sq]
  have hbase (z : ℂ) (hz : z ∈ A) (he : F z = F x) : z = x := by
    have hp : orbit c a z ∈ B := hAp ▸ mem_image_of_mem _ hz
    rw [hB] at hp
    have hq : (orbit c a z)^2+c ∈ D :=
      connectedComponentIn_subset ((fun w : ℂ => w^2+c) ⁻¹' D) 0 hp
    change orbit c (a+1+b) z = orbit c (a+1+b) x at he
    rw [hxval] at he
    have hs : orbit c b ((orbit c a z)^2+c) = orbit c b c := by
      simpa only [quadratic_orbit_add, orbit] using he
    have hsq := hrinj hq hcD hs
    have hp0 : orbit c a z = 0 :=
      eq_zero_of_pow_eq_zero (n := 2) (by linear_combination hsq)
    exact hpinj hz hxA (hp0.trans hx0.symm)
  have hclass (i : Fin n) (δ : Path x x) (hδ : range δ ⊆ A)
      (hδmap : δ.map hF = (α i).map hF) : δ = α i ∨ δ = β i := by
    let p : unitInterval → ℂ := fun t => orbit c a (δ t)
    have hpc : Continuous p := (quadratic_orbit_continuous c a).comp δ.continuous
    have hsquare (t : unitInterval) : p t ^ 2 = excursion r i t ^ 2 := by
      have hpB : p t ∈ B := hAp ▸ mem_image_of_mem _ (hδ (mem_range_self t))
      rw [hB] at hpB
      have hpD : (p t)^2+c ∈ D :=
        connectedComponentIn_subset ((fun w : ℂ => w^2+c) ⁻¹' D) 0 hpB
      have hqB := heB i t
      rw [hB] at hqB
      have hqD : (excursion r i t)^2+c ∈ D :=
        connectedComponentIn_subset ((fun w : ℂ => w^2+c) ⁻¹' D) 0 hqB
      have he := congrArg (fun q : Path (F x) (F x) => q t) hδmap
      change orbit c (a+1+b) (δ t) = orbit c (a+1+b) (g (excursion r i t)) at he
      rw [quadratic_orbit_add c (a+1) b, quadratic_orbit_add c (a+1) b] at he
      change orbit c b ((p t)^2+c) =
        orbit c b ((orbit c a (g (excursion r i t)))^2+c) at he
      rw [hgright (heB i t)] at he
      exact add_right_cancel (hrinj hpD hqD he)
    have hnonzero (t : unitInterval) (ht : t ∈ Ioo (0 : unitInterval) 1) :
        excursion r i t ≠ 0 := by
      intro hz
      rcases (excursion_eq_zero_iff hr i t).mp hz with hz | hz
      · exact (ne_of_gt ht.1) hz
      · exact (ne_of_lt ht.2) hz
    have hext (Q : Path x x) (hQA : range Q ⊆ A)
        (hQ : ∀ t ∈ Ioo (0 : unitInterval) 1, p t = orbit c a (Q t)) : δ = Q := by
      apply Path.ext
      funext t
      by_cases ht0 : t = 0
      · simp [ht0]
      by_cases ht1 : t = 1
      · simp [ht1]
      apply hpinj (hδ (mem_range_self t)) (hQA (mem_range_self t))
      exact hQ t ⟨lt_of_le_of_ne (show (0 : unitInterval) ≤ t from bot_le) (Ne.symm ht0),
        lt_of_le_of_ne (show t ≤ (1 : unitInterval) from le_top) ht1⟩
    rcases continuous_square_root_interior_choice p (excursion r i) hpc
        (excursion_continuous r i) hnonzero hsquare with hp | hp
    · exact Or.inl (hext (α i) (hα i) (fun t ht =>
        (hp ht).trans (hgright (heB i t)).symm))
    · exact Or.inr (hext (β i) (hβ i) (fun t ht =>
        (hp ht).trans (hgright (hnB i t)).symm))
  let γ := sequenceConcatenation n (fun i => (α i).map hF)
  let L := choiceConcatenation n α β (fun _ => false)
  have hLA : range L ⊆ A :=
    choiceConcatenation_range_subset n α β A hxA hα hβ (fun _ => false)
  have hL (t : unitInterval) : F (L t) = γ t :=
    congrArg (fun q : Path (F x) (F x) => q t)
      (choiceConcatenation_map n α β F hF hsame (fun _ => false))
  have hγV (t : unitInterval) : γ t ∈ V := by
    rw [← hL t]
    exact hmap (hLA (mem_range_self t))
  refine ⟨γ.toContinuousMap, hγV, γ.source.trans hxval, γ.target.trans hxval, ?_, ?_⟩
  · exact continuous_choice_lift_card_exact n α β A hxA hα hβ M
      hpositive hnegative F hF hsame hbase hclass
  · exact all_trace_card_exact n α β A hxA hα hβ M
      hpositive hnegative F hF hsame hbase hclass

/-- Even for one fixed physical degree-two return, no finite constant
bounds the number of geometric lifts of all continuous target paths
allowed to visit the critical value. A proposed bound is defeated by
one explicitly constructed finite excursion path; no limiting path or
infinite family is needed. -/
theorem quadratic_return_unbounded_critical_trace_count
    (c : ℂ) (a b : ℕ) (A B D V : Set ℂ) (x : ℂ)
    (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ∀ M : ℕ, ∃ γ : C(unitInterval, ℂ),
      (∀ t, γ t ∈ V) ∧ γ 0 = orbit c b c ∧ γ 1 = orbit c b c ∧
      M < Nat.card {K : Set ℂ // ∃ L : C(unitInterval, ℂ),
        range L = K ∧ range L ⊆ A ∧
        ∀ t, orbit c (a+1+b) (L t) = γ t} := by
  intro M
  obtain ⟨γ, hγV, hγ0, hγ1, _, hcount⟩ :=
    quadratic_return_critical_trace_card_exact c a b A B D V x hx0
      hVo hVc hv hD hB hA hpinj hrinj M
  refine ⟨γ, hγV, hγ0, hγ1, ?_⟩
  rw [hcount]
  exact M.lt_two_pow_self

end

end LoopsTelescopeCriticalTraceCensus
