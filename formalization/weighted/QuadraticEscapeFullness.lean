import StationaryFiberDynamics
import QuadraticCriticalFiberCensus
import LeastSaturatedCarrier
import Mathlib.Analysis.Complex.AbsMax

/-!
# Fullness of actual quadratic escape sublevels

The maximum modulus principle is applied to finite holomorphic iterates,
then the established uniform escape-potential convergence transfers
the frontier bound to their limit. No local connectivity is required.
-/

namespace LoopsQuadraticEscapeFullness

set_option maxHeartbeats 1000000

open Set Bornology Filter Topology
open LoopsStationaryGeometricFibers LoopsQuadraticCylinderCensus LoopsQuadraticCriticalFiberCensus
open QuadraticEscape LoopsStationaryFiberDynamics
open LoopsFormal.ProtectedCarriers LoopsStationaryMonotoneGeometry

/-- Finite iterates remain entire even when both the parameter and
the initial point depend holomorphically on a complex variable. -/
theorem orbit_pair_differentiable (a b : ℂ → ℂ)
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b) (n : ℕ) :
    Differentiable ℂ (fun z => orbit (a z) n (b z)) := by
  induction n with
  | zero => exact hb
  | succ n ih =>
    change Differentiable ℂ (fun z => (orbit (a z) n (b z))^2 + a z)
    exact (ih.pow 2).add ha

/-- A bounded set inherits an escape-potential upper bound from its
frontier. This is a theorem about the genuine limiting orbit potential,
including nonconstant entire parameter families. -/
theorem escape_pair_frontier_bound (a b : ℂ → ℂ)
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b)
    (U : Set ℂ) (hU : IsBounded U) (t : ℝ)
    (ht : ∀ w ∈ frontier U, escape (a w) (b w) ≤ t)
    {z : ℂ} (hz : z ∈ U) : escape (a z) (b z) ≤ t := by
  by_contra! hgt
  let ε : ℝ := (escape (a z) (b z) - t) / 3
  have he : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, _, hC⟩ :=
    (hU.isCompact_closure.image ha.continuous).isBounded.subset_closedBall_lt 0 0
  have hparam (w : ℂ) (hw : w ∈ closure U) : ‖a w‖ ≤ C := by
    have hh : a w ∈ Metric.closedBall (0 : ℂ) C := hC ⟨w, hw, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hh
  obtain ⟨N, hN⟩ := escape_uniform C ε he
  obtain ⟨w, hw, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm hU
    ⟨z, hz⟩ (orbit_pair_differentiable a b ha hb N).diffContOnCl
  have hn : ‖orbit (a z) N (b z)‖ ≤ ‖orbit (a w) N (b w)‖ :=
    hmax (subset_closure hz)
  have hs : size (orbit (a z) N (b z)) ≤ size (orbit (a w) N (b w)) :=
    max_le_max le_rfl hn
  have hl : logSize (orbit (a z) N (b z)) ≤ logSize (orbit (a w) N (b w)) :=
    Real.log_le_log (size_pos _) hs
  have hap : approx (a z) (b z) N ≤ approx (a w) (b w) N :=
    mul_le_mul_of_nonneg_left hl (weight_pos N).le
  have hzerr := (abs_lt.mp (hN N le_rfl (a z) (b z)
    (hparam z (subset_closure hz)))).1
  have hwerr := (abs_lt.mp (hN N le_rfl (a w) (b w)
    (hparam w (frontier_subset_closure hw)))).2
  have hwt := ht w hw
  dsimp [ε] at hzerr hwerr
  linarith

/-- A complementary component of a closed plane set has frontier
contained in that set. The ambient plane is locally connected; the
closed set itself need not be locally connected. -/
theorem frontier_complement_component_subset {S : Set ℂ}
    (hS : IsClosed S) (z : ℂ) :
    frontier (connectedComponentIn Sᶜ z) ⊆ S := by
  intro w hw
  by_contra hnot
  change w ∈ closure (connectedComponentIn Sᶜ z) ∧
    w ∉ interior (connectedComponentIn Sᶜ z) at hw
  have hwV : w ∈ connectedComponentIn Sᶜ w := mem_connectedComponentIn hnot
  have hV : IsOpen (connectedComponentIn Sᶜ w) :=
    hS.isOpen_compl.connectedComponentIn
  obtain ⟨v, hvV, hvU⟩ := mem_closure_iff.mp hw.1 _ hV hwV
  have he : connectedComponentIn Sᶜ z = connectedComponentIn Sᶜ w :=
    (connectedComponentIn_eq hvU).trans (connectedComponentIn_eq hvV).symm
  have hU : IsOpen (connectedComponentIn Sᶜ z) :=
    hS.isOpen_compl.connectedComponentIn
  apply hw.2
  rw [hU.interior_eq, he]
  exact hwV

/-- Every closed sublevel of the actual escape potential along an
entire pair has no bounded complementary component. -/
theorem escape_pair_sublevel_full (a b : ℂ → ℂ)
    (ha : Differentiable ℂ a) (hb : Differentiable ℂ b) (t : ℝ) :
    planarFill {z : ℂ | escape (a z) (b z) ≤ t} =
      {z : ℂ | escape (a z) (b z) ≤ t} := by
  let S : Set ℂ := {z : ℂ | escape (a z) (b z) ≤ t}
  have hp : Continuous (fun z : ℂ => (a z, b z)) :=
    ha.continuous.prodMk hb.continuous
  have hc : Continuous (fun z : ℂ => escape (a z) (b z)) := by
    change Continuous ((fun x : ℂ × ℂ => escape x.1 x.2) ∘
      (fun z : ℂ => (a z, b z)))
    exact escape_continuous.comp hp
  have hS : IsClosed S := isClosed_le hc continuous_const
  change planarFill S = S
  apply Subset.antisymm _ (planarFill_extensive S)
  intro z hz
  by_cases h : z ∈ S
  · exact h
  · change IsBounded (connectedComponentIn Sᶜ z) at hz
    exact escape_pair_frontier_bound a b ha hb _ hz t
      (fun w hw => frontier_complement_component_subset hS z hw)
      (mem_connectedComponentIn (show z ∈ Sᶜ from h))

/-- Fullness at every real escape level of a fixed actual quadratic. -/
theorem quadratic_escape_sublevel_full (c : ℂ) (t : ℝ) :
    planarFill {z : ℂ | escape c z ≤ t} = {z : ℂ | escape c z ≤ t} := by
  exact escape_pair_sublevel_full (fun _ => c) id (differentiable_const c) differentiable_id t

/-- Fullness also holds in the parameter plane for the archive's
critical-value normalization of the quadratic parameter potential. -/
theorem quadratic_parameter_sublevel_full (t : ℝ) :
    planarFill {c : ℂ | parameterEscape c ≤ t} =
      {c : ℂ | parameterEscape c ≤ t} := by
  exact escape_pair_sublevel_full id id differentiable_id differentiable_id t

/-- The actual bounded-orbit filled Julia set is full at every parameter. -/
theorem quadratic_filled_full (c : ℂ) :
    planarFill (quadraticFilled c) = quadraticFilled c := by
  have he : {z : ℂ | escape c z ≤ 0} = quadraticFilled c := by
    ext z
    change escape c z ≤ 0 ↔ escape c z = 0
    exact ⟨fun h => le_antisymm h (escape_nonneg c z), fun h => h.le⟩
  rw [← he]
  exact quadratic_escape_sublevel_full c 0

/-- There is only one complementary component of the actual filled set. -/
theorem quadratic_filled_connected_complement (c : ℂ) :
    IsConnected (quadraticFilled c)ᶜ := by
  obtain ⟨z, hz, _, he, _⟩ :=
    planarFill_exterior (quadratic_filled_compact c).isBounded
  rw [quadratic_filled_full c] at he
  rw [he]
  exact isConnected_connectedComponentIn_iff.mpr hz

/-- Every compact physical subcarrier of an empty-interior filled
quadratic set is full and has connected complement. Only the empty
interior premise remains; ambient fullness is now derived. -/
theorem quadratic_filled_compact_subcarrier_full (c : ℂ) (A : Set ℂ)
    (hA : IsCompact A) (hsub : A ⊆ quadraticFilled c)
    (he : interior (quadraticFilled c) = ∅) :
    planarFill A = A ∧ IsConnected Aᶜ :=
  compact_subset_full_of_full_empty_interior (quadraticFilled c) A hA hsub
    (quadratic_filled_full c) he


/-- Explicit finite-iterate outer approximants. The error term is essential:
the uncorrected finite sublevels need not be nested. -/
noncomputable def escapeOuter (c : ℂ) (t : ℝ) (n : ℕ) : Set ℂ :=
  {z | approx c z n ≤ t + weight n * Real.log (1+‖c‖)}

theorem escape_outer_zero (c : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    escapeOuter c t 0 = Metric.closedBall 0 (Real.exp (t+Real.log (1+‖c‖))) := by
  have hL : 0 ≤ Real.log (1+‖c‖) := Real.log_nonneg (by linarith [norm_nonneg c])
  have hR : 1 ≤ Real.exp (t+Real.log (1+‖c‖)) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (add_nonneg ht hL)
  ext z
  change approx c z 0 ≤ t + weight 0 * Real.log (1+‖c‖) ↔
    z ∈ Metric.closedBall 0 (Real.exp (t+Real.log (1+‖c‖)))
  rw [Metric.mem_closedBall, dist_zero_right]
  simp only [approx, orbit, weight, pow_zero, one_mul]
  change Real.log (size z) ≤ t+Real.log (1+‖c‖) ↔
    ‖z‖ ≤ Real.exp (t+Real.log (1+‖c‖))
  rw [Real.log_le_iff_le_exp (size_pos z)]
  exact ⟨fun h => (norm_le_size z).trans h, fun h => max_le hR h⟩

/-- The finite approximants obey the exact quadratic pullback relation. -/
theorem escape_outer_succ (c : ℂ) (t : ℝ) (n : ℕ) :
    escapeOuter c t (n+1) = (fun z : ℂ => z^2+c) ⁻¹' escapeOuter c (2*t) n := by
  ext z
  change approx c z (n+1) ≤ t+weight (n+1)*Real.log (1+‖c‖) ↔
    approx c (z^2+c) n ≤ 2*t+weight n*Real.log (1+‖c‖)
  have hscale : weight n * Real.log (1+‖c‖) =
      2*(weight (n+1)*Real.log (1+‖c‖)) := by rw [weight_succ]; ring
  rw [approx_shift, hscale]
  constructor <;> intro h <;> linarith

theorem escape_outer_antitone (c : ℂ) (t : ℝ) : Antitone (escapeOuter c t) := by
  apply antitone_nat_of_succ_le
  intro n z hz
  change approx c z (n+1) ≤ t+weight (n+1)*Real.log (1+‖c‖) at hz
  change approx c z n ≤ t+weight n*Real.log (1+‖c‖)
  have h := (abs_le.mp (approx_step c z (le_refl ‖c‖) n)).1
  have he : weight n * Real.log (1+‖c‖) =
      2*(weight (n+1)*Real.log (1+‖c‖)) := by rw [weight_succ]; ring
  rw [he]
  linarith

theorem escape_outer_contains_sublevel (c : ℂ) (t : ℝ) (n : ℕ) {z : ℂ}
    (hz : escape c z ≤ t) : z ∈ escapeOuter c t n := by
  have h := (abs_le.mp (escape_error c z (le_refl ‖c‖) n)).2
  change approx c z n ≤ t+weight n*Real.log (1+‖c‖)
  linarith

theorem escape_outer_iInter (c : ℂ) (t : ℝ) :
    (⋂ n : ℕ, escapeOuter c t n) = {z : ℂ | escape c z ≤ t} := by
  ext z
  constructor
  · intro hz
    change escape c z ≤ t
    have hlim : Tendsto (fun n : ℕ => t+weight n*Real.log (1+‖c‖))
        atTop (𝓝 t) := by
      simpa using (tendsto_const_nhds (x := t)).add
        (weight_tendsto.mul (tendsto_const_nhds (x := Real.log (1+‖c‖))))
    exact le_of_tendsto_of_tendsto' (escape_tendsto c z) hlim
      (fun n => mem_iInter.mp hz n)
  · intro hz
    exact mem_iInter.mpr (fun n => escape_outer_contains_sublevel c t n hz)

/-- A preconnected set containing the critical value has preconnected
full inverse image under the actual quadratic. -/
theorem quadratic_critical_preimage_preconnected (c : ℂ) (S : Set ℂ)
    (hs : IsPreconnected S) (hc : c ∈ S) :
    IsPreconnected ((fun z : ℂ => z^2+c) ⁻¹' S) := by
  refine critical_preimage_preconnected (fun z : ℂ => z^2+c) (fun z : ℂ => -z)
    (quadratic_proper c).isClosedMap continuous_neg (quadratic_surjective c)
    ?_ ?_ S hs 0 (by simp) ?_
  · intro z
    ring
  · intro x z hx
    change x^2+c = z^2+c at hx
    have he : (z-x)*(z+x)=0 := by
      calc
        _ = (z^2+c)-(x^2+c) := by ring
        _ = 0 := by rw [hx, sub_self]
    rcases mul_eq_zero.mp he with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by linear_combination h)
  · simpa using hc

theorem escape_outer_compact (c : ℂ) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    IsCompact (escapeOuter c t n) := by
  induction n generalizing t with
  | zero =>
    rw [escape_outer_zero c t ht]
    exact isCompact_closedBall _ _
  | succ n ih =>
    rw [escape_outer_succ]
    exact (quadratic_proper c).isCompact_preimage (ih (2*t) (by linarith))

theorem escape_outer_preconnected (c : ℂ) (n : ℕ) (t : ℝ)
    (ht : escape c 0 ≤ t) : IsPreconnected (escapeOuter c t n) := by
  induction n generalizing t with
  | zero =>
    rw [escape_outer_zero c t ((escape_nonneg c 0).trans ht)]
    exact (convex_closedBall (0 : ℂ) _).isPreconnected
  | succ n ih =>
    rw [escape_outer_succ]
    have ht0 : 0 ≤ t := (escape_nonneg c 0).trans ht
    apply quadratic_critical_preimage_preconnected c
    · exact ih (2*t) (by linarith)
    · apply escape_outer_contains_sublevel c (2*t) n
      change parameterEscape c ≤ 2*t
      rw [parameterEscape_critical]
      linarith

theorem quadratic_escape_sublevel_compact (c : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    IsCompact {z : ℂ | escape c z ≤ t} := by
  rw [← escape_outer_iInter c t]
  exact (escape_outer_compact c 0 t ht).of_isClosed_subset
    (isClosed_iInter (fun n => (escape_outer_compact c n t ht).isClosed))
    (iInter_subset (escapeOuter c t) 0)

/-- A dynamical escape sublevel at or above the critical escape height
is connected. This includes the limiting critical level, not just regular
positive levels. -/
theorem quadratic_escape_sublevel_connected_of_critical (c : ℂ) (t : ℝ)
    (ht : escape c 0 ≤ t) : IsConnected {z : ℂ | escape c z ≤ t} := by
  refine ⟨⟨0, ht⟩, ?_⟩
  rw [← escape_outer_iInter c t]
  have hmono := escape_outer_antitone c t
  have ht0 : 0 ≤ t := (escape_nonneg c 0).trans ht
  exact LoopsLeastCarrier.directed_carrier_preconnected (escapeOuter c t 0)
    (escape_outer_compact c 0 t ht0) (escapeOuter c t)
    (fun n => escape_outer_compact c n t ht0)
    (fun n => escape_outer_preconnected c n t ht)
    (fun n => hmono (Nat.zero_le n))
    (fun i j => ⟨max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩)

/-- The actual filled quadratic set is connected if its critical orbit is
bounded; no topological hypothesis on the filled set is supplied. -/
theorem quadratic_filled_connected_of_critical (c : ℂ) (h0 : (0 : ℂ) ∈ quadraticFilled c) :
    IsConnected (quadraticFilled c) := by
  have he : {z : ℂ | escape c z ≤ 0} = quadraticFilled c := by
    ext z
    change escape c z ≤ 0 ↔ escape c z = 0
    exact ⟨fun h => le_antisymm h (escape_nonneg c z), fun h => h.le⟩
  rw [← he]
  change escape c 0 = 0 at h0
  exact quadratic_escape_sublevel_connected_of_critical c 0 h0.le

end LoopsQuadraticEscapeFullness
