import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Certified parameter of the limiting four-push crest

The limiting quadratic is Q(k,x) = 1-k*x^2. The signed critical relation
Q(k)^[6](0) + Q(k)^[3](0) has exactly one zero in the stated rational
interval. The derivative and orbit bounds below hold throughout the
interval; no numerical root or assumed parameter is used.
-/

namespace LoopsLimitingCrestParameter

open Set Function

noncomputable section

def Q (k x : ℝ) : ℝ := 1 - k*x^2

def criticalOrbit (k : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => Q k (criticalOrbit k n)

def criticalSlope (k : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => -(criticalOrbit k n)^2 - 2*k*criticalOrbit k n*criticalSlope k n

def relation (k : ℝ) : ℝ := criticalOrbit k 6 + criticalOrbit k 3

def parameterInterval : Set ℝ := Icc (17903/10000) (17904/10000)

theorem criticalOrbit_eq_iterate (k : ℝ) (n : ℕ) :
    criticalOrbit k n = (Q k)^[n] 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [criticalOrbit, Function.iterate_succ_apply', ih]

theorem criticalOrbit_hasDerivAt (n : ℕ) (k : ℝ) :
    HasDerivAt (fun t : ℝ => criticalOrbit t n) (criticalSlope k n) k := by
  induction n with
  | zero => simpa [criticalOrbit, criticalSlope] using (hasDerivAt_const k (0 : ℝ))
  | succ n ih =>
      have h := (hasDerivAt_const k (1 : ℝ)).sub ((hasDerivAt_id k).mul (ih.pow 2))
      change HasDerivAt ((fun _ : ℝ => 1) - id * (fun t : ℝ => criticalOrbit t n)^2)
        (criticalSlope k (n+1)) k
      apply h.congr_deriv
      simp only [criticalSlope, Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, Pi.pow_apply]
      ring

theorem relation_hasDerivAt (k : ℝ) :
    HasDerivAt relation (criticalSlope k 6 + criticalSlope k 3) k := by
  exact (criticalOrbit_hasDerivAt 6 k).add (criticalOrbit_hasDerivAt 3 k)

private abbrev Box := ℝ × ℝ
private def InBox (x : ℝ) (I : Box) : Prop := I.1 ≤ x ∧ x ≤ I.2
private def addBox (I J : Box) : Box := (I.1+J.1, I.2+J.2)
private def negBox (I : Box) : Box := (-I.2, -I.1)
private def mulBox (I J : Box) : Box :=
  (min (min (I.1*J.1) (I.1*J.2)) (min (I.2*J.1) (I.2*J.2)),
   max (max (I.1*J.1) (I.1*J.2)) (max (I.2*J.1) (I.2*J.2)))

private theorem fixed_mul_bounds {a x l u L U : ℝ}
    (hx : l ≤ x ∧ x ≤ u)
    (hl : L ≤ a*l) (hu : L ≤ a*u)
    (Hl : a*l ≤ U) (Hu : a*u ≤ U) : L ≤ a*x ∧ a*x ≤ U := by
  rcases le_total 0 a with ha | ha
  · exact ⟨hl.trans (mul_le_mul_of_nonneg_left hx.1 ha),
      (mul_le_mul_of_nonneg_left hx.2 ha).trans Hu⟩
  · exact ⟨hu.trans (mul_le_mul_of_nonpos_left hx.2 ha),
      (mul_le_mul_of_nonpos_left hx.1 ha).trans Hl⟩

private theorem mul_sound {x y : ℝ} {I J : Box}
    (hx : InBox x I) (hy : InBox y J) : InBox (x*y) (mulBox I J) := by
  have hc1 : InBox (J.1*x) (mulBox I J) := by
    apply fixed_mul_bounds hx
    · simpa only [mulBox, mul_comm] using
        ((min_le_left _ _).trans (min_le_left _ _) : (mulBox I J).1 ≤ I.1*J.1)
    · simpa only [mulBox, mul_comm] using
        ((min_le_right _ _).trans (min_le_left _ _) : (mulBox I J).1 ≤ I.2*J.1)
    · simpa only [mulBox, mul_comm] using
        ((le_max_left _ _).trans (le_max_left _ _) : I.1*J.1 ≤ (mulBox I J).2)
    · simpa only [mulBox, mul_comm] using
        ((le_max_left _ _).trans (le_max_right _ _) : I.2*J.1 ≤ (mulBox I J).2)
  have hc2 : InBox (J.2*x) (mulBox I J) := by
    apply fixed_mul_bounds hx
    · simpa only [mulBox, mul_comm] using
        ((min_le_left _ _).trans (min_le_right _ _) : (mulBox I J).1 ≤ I.1*J.2)
    · simpa only [mulBox, mul_comm] using
        ((min_le_right _ _).trans (min_le_right _ _) : (mulBox I J).1 ≤ I.2*J.2)
    · simpa only [mulBox, mul_comm] using
        ((le_max_right _ _).trans (le_max_left _ _) : I.1*J.2 ≤ (mulBox I J).2)
    · simpa only [mulBox, mul_comm] using
        ((le_max_right _ _).trans (le_max_right _ _) : I.2*J.2 ≤ (mulBox I J).2)
  exact fixed_mul_bounds hy
    (by simpa only [mulBox, mul_comm] using hc1.1)
    (by simpa only [mulBox, mul_comm] using hc2.1)
    (by simpa only [mulBox, mul_comm] using hc1.2)
    (by simpa only [mulBox, mul_comm] using hc2.2)

private theorem add_sound {x y : ℝ} {I J : Box}
    (hx : InBox x I) (hy : InBox y J) : InBox (x+y) (addBox I J) :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

private theorem neg_sound {x : ℝ} {I : Box}
    (hx : InBox x I) : InBox (-x) (negBox I) :=
  ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

private theorem widen {x : ℝ} {I J : Box}
    (hx : InBox x I) (h : J.1 ≤ I.1 ∧ I.2 ≤ J.2) : InBox x J :=
  ⟨h.1.trans hx.1, hx.2.trans h.2⟩

private def orbitBox (K X : Box) : Box :=
  addBox (1,1) (negBox (mulBox K (mulBox X X)))

private def slopeBox (K X D : Box) : Box :=
  negBox (addBox (mulBox X X) (mulBox (2,2) (mulBox K (mulBox X D))))

private theorem orbit_step {k : ℝ} {n : ℕ} {K X : Box}
    (hk : InBox k K) (hx : InBox (criticalOrbit k n) X) :
    InBox (criticalOrbit k (n+1)) (orbitBox K X) := by
  have h := add_sound (show InBox (1 : ℝ) (1,1) from ⟨le_rfl,le_rfl⟩)
    (neg_sound (mul_sound hk (mul_sound hx hx)))
  simpa only [criticalOrbit, Q, pow_two, sub_eq_add_neg, orbitBox] using h

private theorem slope_step {k : ℝ} {n : ℕ} {K X D : Box}
    (hk : InBox k K) (hx : InBox (criticalOrbit k n) X)
    (hd : InBox (criticalSlope k n) D) :
    InBox (criticalSlope k (n+1)) (slopeBox K X D) := by
  have h := neg_sound (add_sound (mul_sound hx hx)
    (mul_sound (show InBox (2 : ℝ) (2,2) from ⟨le_rfl,le_rfl⟩)
      (mul_sound hk (mul_sound hx hd))))
  have he : criticalSlope k (n+1) =
      -(criticalOrbit k n*criticalOrbit k n + 2*(k*(criticalOrbit k n*criticalSlope k n))) := by
    simp only [criticalSlope]
    ring
  rw [he]
  exact h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem interval_certificate {k : ℝ} (hk : k ∈ parameterInterval) :
    InBox (criticalOrbit k 3) (-118521/1000000, -118174/1000000) ∧
    InBox (criticalOrbit k 4) (974849/1000000, 974999/1000000) ∧
    InBox (criticalSlope k 3) (-3454997/1000000, -3454322/1000000) ∧
    InBox (criticalSlope k 6) (10054961/1000000, 10110824/1000000) := by
  have hK : InBox k (17903/10000,17904/10000) := hk
  have h0 : InBox (criticalOrbit k 0) (0,0) := by norm_num [InBox, criticalOrbit]
  have d0 : InBox (criticalSlope k 0) (0,0) := by norm_num [InBox, criticalSlope]
  have h1 : InBox (criticalOrbit k 1) (1,1) := by norm_num [InBox, criticalOrbit, Q]
  have d1 : InBox (criticalSlope k 1) (0,0) := by
    norm_num [InBox, criticalSlope, criticalOrbit]
  have h2 : InBox (criticalOrbit k 2) (-790400/1000000,-790300/1000000) := by
    apply widen (orbit_step hK h1)
    norm_num [orbitBox, addBox, negBox, mulBox]
  have d2 : InBox (criticalSlope k 2) (-1,-1) := by
    apply widen (slope_step hK h1 d1)
    norm_num [slopeBox, addBox, negBox, mulBox]
  have h3 : InBox (criticalOrbit k 3) (-118521/1000000,-118174/1000000) := by
    apply widen (orbit_step hK h2)
    norm_num [orbitBox, addBox, negBox, mulBox]
  have d3 : InBox (criticalSlope k 3) (-3454997/1000000,-3454322/1000000) := by
    apply widen (slope_step hK h2 d2)
    norm_num [slopeBox, addBox, negBox, mulBox]
  have h4 : InBox (criticalOrbit k 4) (974849/1000000,974999/1000000) := by
    apply widen (orbit_step hK h3)
    norm_num [orbitBox, addBox, negBox, mulBox]
  have d4 : InBox (criticalSlope k 4) (-1480348/1000000,-1475605/1000000) := by
    apply widen (slope_step hK h3 d3)
    norm_num [slopeBox, addBox, negBox, mulBox]
  have h5 : InBox (criticalOrbit k 5) (-701996/1000000,-701376/1000000) := by
    apply widen (orbit_step hK h4)
    norm_num [orbitBox, addBox, negBox, mulBox]
  have d5 : InBox (criticalSlope k 5) (4200041/1000000,4217974/1000000) := by
    apply widen (slope_step hK h4 d4)
    norm_num [slopeBox, addBox, negBox, mulBox]
  have d6 : InBox (criticalSlope k 6) (10054961/1000000,10110824/1000000) := by
    apply widen (slope_step hK h5 d5)
    norm_num [slopeBox, addBox, negBox, mulBox]
  exact ⟨h3,h4,d3,d6⟩

/-- Rational geometric bounds valid for every parameter of the isolator. -/
theorem parameter_orbit_bounds {k : ℝ} (hk : k ∈ parameterInterval) :
    -(119/1000) < criticalOrbit k 3 ∧ criticalOrbit k 3 < -(118/1000) ∧
    9748/10000 < criticalOrbit k 4 ∧ criticalOrbit k 4 < 9751/10000 := by
  obtain ⟨h3,h4,_,_⟩ := interval_certificate hk
  dsimp [InBox] at h3 h4
  constructor
  · linarith [h3.1]
  constructor
  · linarith [h3.2]
  constructor
  · linarith [h4.1]
  · linarith [h4.2]

/-- The signed relation crosses transversely with a uniform margin. -/
theorem relation_slope_gt_six {k : ℝ} (hk : k ∈ parameterInterval) :
    6 < criticalSlope k 6 + criticalSlope k 3 := by
  obtain ⟨_,_,d3,d6⟩ := interval_certificate hk
  dsimp [InBox] at d3 d6
  linarith [d3.1,d6.1]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem relation_endpoint_signs :
    relation (17903/10000) < 0 ∧ 0 < relation (17904/10000) := by
  norm_num [relation, criticalOrbit, Q]

theorem relation_strictMonoOn : StrictMonoOn relation parameterInterval := by
  apply strictMonoOn_of_hasDerivWithinAt_pos
    (convex_Icc (17903/10000 : ℝ) (17904/10000))
    (Continuous.continuousOn (continuous_iff_continuousAt.mpr
      (fun k => (relation_hasDerivAt k).continuousAt)))
    (fun k _ => (relation_hasDerivAt k).hasDerivWithinAt)
  intro k hk
  have h := relation_slope_gt_six (interior_subset hk)
  linarith

/-- An actual real parameter is constructed by IVT and is unique on the
entire rational interval, not only among tested rational parameters. -/
theorem exists_unique_limiting_parameter :
    ∃! k : ℝ, k ∈ parameterInterval ∧ relation k = 0 := by
  have hc : ContinuousOn relation (Icc (17903/10000 : ℝ) (17904/10000)) :=
    (continuous_iff_continuousAt.mpr (fun k => (relation_hasDerivAt k).continuousAt)).continuousOn
  obtain ⟨k,hk,hzero⟩ :=
    (intermediate_value_Icc (by norm_num : (17903/10000 : ℝ) ≤ 17904/10000) hc)
      ⟨relation_endpoint_signs.1.le, relation_endpoint_signs.2.le⟩
  refine ⟨k,⟨hk,hzero⟩,?_⟩
  intro t ht
  exact relation_strictMonoOn.injOn ht.1 hk (ht.2.trans hzero.symm)

/-- The root is strictly interior and has the signed orbit geometry
needed by the limiting crest gate. -/
theorem limiting_parameter_geometry {k : ℝ}
    (hk : k ∈ parameterInterval) (hzero : relation k = 0) :
    17903/10000 < k ∧ k < 17904/10000 ∧
    criticalOrbit k 3 < 0 ∧ 0 < criticalOrbit k 6 ∧
    9748/10000 < criticalOrbit k 4 ∧ criticalOrbit k 4 < 9751/10000 := by
  have hs := relation_endpoint_signs
  have hg := parameter_orbit_bounds hk
  have hl : 17903/10000 < k := by
    apply lt_of_le_of_ne hk.1
    intro he
    have hz : relation (17903/10000) = 0 := by rw [he,hzero]
    linarith [hs.1]
  have hu : k < 17904/10000 := by
    apply lt_of_le_of_ne hk.2
    intro he
    have hz : relation (17904/10000) = 0 := by rw [← he,hzero]
    linarith [hs.2]
  have h3 : criticalOrbit k 3 < 0 := by linarith [hg.2.1]
  have h6 : 0 < criticalOrbit k 6 := by dsimp [relation] at hzero; linarith
  exact ⟨hl,hu,h3,h6,hg.2.2.1,hg.2.2.2⟩

end

end LoopsLimitingCrestParameter
