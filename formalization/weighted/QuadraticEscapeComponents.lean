import QuadraticEscapeBranches
import FiniteComponentTree
import ComponentDoubling

/-!
# Exact components of actual quadratic escape sublevels

The component count is determined by the first doubled height reaching
the critical escape height. All finite inverse sheets are constructed,
and the final coordinate is the actual polynomial iterate.
-/

namespace LoopsQuadraticEscapeTree

open Set QuadraticEscape LoopsQuadraticEscapeFullness
open LoopsFiniteComponentTree
open LoopsComponentDoubling LoopsStationaryFiberDynamics

set_option maxHeartbeats 1000000

/-- Iterate the constructed binary splitting through any finite
subcritical horizon. The resulting finite labels partition the actual
sublevel, and their common coordinate is the genuine iterate. -/
theorem sublevel_iterated_split (c : ℂ) (t : ℝ) (n : ℕ)
    (ht : 0 ≤ t)
    (hbelow : ∀ k < n, (2 : ℝ)^k*t < escape c 0) :
    ∃ e : sublevel c t ≃ₜ (Fin (2^n) × sublevel c ((2 : ℝ)^n*t)),
      ∀ z, ((e z).2 : ℂ) = orbit c n (z : ℂ) := by
  induction n generalizing t with
  | zero =>
    simp only [pow_zero, one_mul]
    let e : sublevel c t ≃ₜ (Fin 1 × sublevel c t) :=
      { toFun := fun z => (0, z)
        invFun := Prod.snd
        left_inv := fun _ => rfl
        right_inv := by
          rintro ⟨i, z⟩
          exact Prod.ext (Subsingleton.elim _ _) rfl
        continuous_toFun := continuous_const.prodMk continuous_id
        continuous_invFun := continuous_snd }
    exact ⟨e, fun _ => rfl⟩
  | succ n ih =>
    have hcrit : t < escape c 0 := by
      simpa using hbelow 0 (Nat.zero_lt_succ n)
    obtain ⟨e₀, he₀⟩ := sublevel_split c t ht hcrit
    have htail : ∀ k < n, (2 : ℝ)^k*(2*t) < escape c 0 := by
      intro k hk
      have h := hbelow (k+1) (Nat.succ_lt_succ hk)
      calc
        (2 : ℝ)^k*(2*t) = 2^(k+1)*t := by ring
        _ < escape c 0 := h
    obtain ⟨e₁, he₁⟩ := ih (2*t) (by positivity) htail
    have hheight : (2 : ℝ)^n*(2*t) = 2^(n+1)*t := by ring
    let top : sublevel c ((2 : ℝ)^n*(2*t)) ≃ₜ
        sublevel c ((2 : ℝ)^(n+1)*t) :=
      Homeomorph.setCongr (congrArg (sublevel c) hheight)
    have hcard : 2*(2^n) = 2^(n+1) := by
      rw [pow_succ, Nat.mul_comm]
    let labels : (Fin 2 × Fin (2^n)) ≃ₜ Fin (2^(n+1)) :=
      (finProdFinEquiv.trans (finCongr hcard)).toHomeomorphOfDiscrete
    let e : sublevel c t ≃ₜ
        (Fin (2^(n+1)) × sublevel c ((2 : ℝ)^(n+1)*t)) :=
      ((e₀.trans ((Homeomorph.refl (Fin 2)).prodCongr e₁)).trans
        (Homeomorph.prodAssoc (Fin 2) (Fin (2^n))
          (sublevel c ((2 : ℝ)^n*(2*t)))).symm).trans
        (labels.prodCongr top)
    refine ⟨e, ?_⟩
    intro z
    change ((e₁ (e₀ z).2).2 : ℂ) = orbit c (n+1) (z : ℂ)
    rw [he₁, he₀, orbit_shift]

/-- At the first critical-height crossing, the constructed labels are
exactly the connected components. This includes equality at the top
height, rather than assuming a regular equipotential. -/
theorem sublevel_component_census (c : ℂ) (t : ℝ) (n : ℕ)
    (ht : 0 ≤ t)
    (hbelow : ∀ k < n, (2 : ℝ)^k*t < escape c 0)
    (htop : escape c 0 ≤ (2 : ℝ)^n*t) :
    ∃ e : sublevel c t ≃ₜ (Fin (2^n) × sublevel c ((2 : ℝ)^n*t)),
      (∀ z, ((e z).2 : ℂ) = orbit c n (z : ℂ)) ∧
      (∀ x : sublevel c t,
        connectedComponent x = {z | (e z).1 = (e x).1}) ∧
      Nat.card (ConnectedComponents (sublevel c t)) = 2^n := by
  have hconn := quadratic_escape_sublevel_connected_of_critical c
    ((2 : ℝ)^n*t) htop
  letI : PreconnectedSpace (sublevel c ((2 : ℝ)^n*t)) :=
    isPreconnected_iff_preconnectedSpace.mp hconn.isPreconnected
  letI : Nonempty (sublevel c ((2 : ℝ)^n*t)) := ⟨⟨0, htop⟩⟩
  obtain ⟨e, he⟩ := sublevel_iterated_split c t n ht hbelow
  exact ⟨e, he, component_eq_label_fiber e, component_count e⟩

/-- Every component maps homeomorphically onto the common connected
top sublevel under the actual n-th iterate. In particular the iterate
has degree one on each of these compact components. -/
theorem sublevel_component_iterate_homeomorph (c : ℂ) (t : ℝ) (n : ℕ)
    (ht : 0 ≤ t)
    (hbelow : ∀ k < n, (2 : ℝ)^k*t < escape c 0)
    (htop : escape c 0 ≤ (2 : ℝ)^n*t) (x : sublevel c t) :
    ∃ e : connectedComponent x ≃ₜ sublevel c ((2 : ℝ)^n*t),
      ∀ z, (e z : ℂ) = orbit c n (z.val : ℂ) := by
  have hconn := quadratic_escape_sublevel_connected_of_critical c
    ((2 : ℝ)^n*t) htop
  letI : PreconnectedSpace (sublevel c ((2 : ℝ)^n*t)) :=
    isPreconnected_iff_preconnectedSpace.mp hconn.isPreconnected
  obtain ⟨e, he⟩ := sublevel_iterated_split c t n ht hbelow
  exact ⟨componentHomeomorph e x, fun z => he z.val⟩

/-- Every strictly positive height has a first critical-height
crossing; no supplied finite horizon is needed for the component count. -/
theorem positive_sublevel_exact_components (c : ℂ) (t : ℝ) (ht : 0 < t) :
    ∃ n : ℕ, (∀ k < n, (2 : ℝ)^k*t < escape c 0) ∧
      escape c 0 ≤ (2 : ℝ)^n*t ∧
      Nat.card (ConnectedComponents (sublevel c t)) = 2^n := by
  classical
  have hex : ∃ n : ℕ, escape c 0 ≤ (2 : ℝ)^n*t := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (escape c 0 / t)
      (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, ((div_lt_iff₀ ht).mp hn).le⟩
  let n := Nat.find hex
  have htop : escape c 0 ≤ (2 : ℝ)^n*t := Nat.find_spec hex
  have hbelow : ∀ k < n, (2 : ℝ)^k*t < escape c 0 := by
    intro k hk
    exact lt_of_not_ge (Nat.find_min hex hk)
  obtain ⟨_, _, _, hcount⟩ := sublevel_component_census c t n ht.le hbelow htop
  exact ⟨n, hbelow, htop, hcount⟩

/-- At the critical dyadic heights the exact component counts are
1, 2, 4, and so on, for every parameter with escaping critical point. -/
theorem critical_dyadic_component_count (c : ℂ) (hc : 0 < escape c 0) (n : ℕ) :
    Nat.card (ConnectedComponents
      (sublevel c (escape c 0 / (2 : ℝ)^n))) = 2^n := by
  have hp : 0 < (2 : ℝ)^n := pow_pos (by norm_num) n
  have ht : 0 ≤ escape c 0 / (2 : ℝ)^n := le_of_lt (div_pos hc hp)
  have hbelow : ∀ k < n,
      (2 : ℝ)^k*(escape c 0 / (2 : ℝ)^n) < escape c 0 := by
    intro k hk
    have hpow : (2 : ℝ)^k < (2 : ℝ)^n := by
      exact pow_lt_pow_right₀ (by norm_num) hk
    rw [← mul_div_assoc, div_lt_iff₀ hp]
    nlinarith
  have htop : escape c 0 ≤
      (2 : ℝ)^n*(escape c 0 / (2 : ℝ)^n) := by
    have he : (2 : ℝ)^n*(escape c 0 / (2 : ℝ)^n) = escape c 0 := by
      field_simp
    rw [he]
  obtain ⟨_, _, _, hcount⟩ := sublevel_component_census c
    (escape c 0 / (2 : ℝ)^n) n ht hbelow htop
  exact hcount

/-- Component complexity is unbounded as positive levels approach an
escaping critical orbit's zero set. This is an exact theorem for every
such complex parameter, with no numerical sampling. -/
theorem sublevel_component_counts_unbounded (c : ℂ) (hc : 0 < escape c 0)
    (N : ℕ) :
    ∃ t > 0, N < Nat.card (ConnectedComponents (sublevel c t)) := by
  refine ⟨escape c 0 / (2 : ℝ)^N, div_pos hc (pow_pos (by norm_num) N), ?_⟩
  rw [critical_dyadic_component_count c hc N]
  exact Nat.lt_two_pow_self N

/-- The actual polynomial sends a sublevel to its doubled-height target. -/
def sublevelMap (c : ℂ) (t : ℝ) : sublevel c t → sublevel c (2*t) :=
  fun z => ⟨(z : ℂ)^2+c, by
    change escape c ((z : ℂ)^2+c) ≤ 2*t
    rw [escape_step]
    have hz : escape c (z : ℂ) ≤ t := z.property
    linarith⟩

/-- Each parent component has exactly two child components, and the
second coordinate of this exact census is induced by the actual map. -/
theorem sublevel_component_parent_census (c : ℂ) (t : ℝ)
    (ht : 0 ≤ t) (hcrit : t < escape c 0) :
    ∃ E : ConnectedComponents (sublevel c t) ≃
        (Fin 2 × ConnectedComponents (sublevel c (2*t))),
      ∀ z, (E (ConnectedComponents.mk z)).2 =
        ConnectedComponents.mk (sublevelMap c t z) := by
  obtain ⟨e, he⟩ := sublevel_split c t ht hcrit
  refine ⟨productComponentEquiv e, ?_⟩
  intro z
  change ConnectedComponents.mk (e z).2 = ConnectedComponents.mk (sublevelMap c t z)
  congr 1
  exact Subtype.ext (he z)

/-- The actual quadratic map restricts to a homeomorphism from each
child component onto its actual parent, including disconnected targets. -/
theorem sublevel_component_parent_homeomorph (c : ℂ) (t : ℝ)
    (ht : 0 ≤ t) (hcrit : t < escape c 0) (x : sublevel c t) :
    ∃ e : connectedComponent x ≃ₜ connectedComponent (sublevelMap c t x),
      ∀ z, (e z).val = sublevelMap c t z.val := by
  obtain ⟨e, he⟩ := sublevel_split c t ht hcrit
  have hp : (e x).2 = sublevelMap c t x := Subtype.ext (he x)
  let parent : connectedComponent (e x).2 ≃ₜ
      connectedComponent (sublevelMap c t x) :=
    Homeomorph.setCongr (congrArg connectedComponent hp)
  refine ⟨(productComponentHomeomorph e x).trans parent, ?_⟩
  intro z
  change (e z.val).2 = sublevelMap c t z.val
  exact Subtype.ext (he z.val)

/-- A fixed point gives a point in every nonnegative sublevel, for
every complex parameter. No bounded critical-orbit premise is required. -/
theorem sublevel_nonempty (c : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (sublevel c t).Nonempty := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (1-4*c) (by decide : 0 < (2 : ℕ))
  let z : ℂ := (1+s)/2
  have hz : z^2+c = z := by
    dsimp [z]
    linear_combination (1/4 : ℂ) * hs
  have hg : escape c z = 0 := by
    have he := escape_step c z
    rw [hz] at he
    linarith
  refine ⟨z, ?_⟩
  change escape c z ≤ t
  rw [hg]
  exact ht

/-- The zero sublevel is the repository's actual bounded-orbit set. -/
theorem sublevel_zero_eq_filled (c : ℂ) : sublevel c 0 = quadraticFilled c := by
  ext z
  change escape c z ≤ 0 ↔ escape c z = 0
  exact ⟨fun h => le_antisymm h (escape_nonneg c z), fun h => h.le⟩

/-- Escaping critical orbit forces infinitely many connected components
of the genuine filled Julia set. The proof does not assert that these
components are singletons. -/
theorem escaping_filled_components_infinite (c : ℂ) (hc : 0 < escape c 0) :
    Infinite (ConnectedComponents (quadraticFilled c)) := by
  rw [← sublevel_zero_eq_filled c]
  obtain ⟨z, hz⟩ := sublevel_nonempty c 0 le_rfl
  letI : Nonempty (sublevel c 0) := ⟨⟨z, hz⟩⟩
  obtain ⟨e, _⟩ := sublevel_split c 0 le_rfl hc
  have e₀ : sublevel c 0 ≃ₜ (Fin 2 × sublevel c 0) := by
    simpa only [mul_zero] using e
  exact self_double_components_infinite e₀

end LoopsQuadraticEscapeTree
