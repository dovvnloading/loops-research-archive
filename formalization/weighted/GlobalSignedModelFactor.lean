import LimitingCrestParameter

/-!
# The factored signed relation on the full local coefficient interval

These rational model estimates support the global physical exclusion.
The model and its local root are already archived; no model novelty is
claimed. Factoring out the third return prevents a small-center error
from being divided by an arbitrarily small critical value.
-/

namespace GlobalSignedModelFactor

open Set Function LoopsLimitingCrestParameter

noncomputable section

def modelFactor (k : ℝ) : ℝ :=
  k^3*(-criticalOrbit k 3)*(1+criticalOrbit k 4)*
    (-(criticalOrbit k 2+criticalOrbit k 5))

private def factorSlope (k : ℝ) : ℝ :=
  ((3*k^2*(-criticalOrbit k 3)+k^3*(-criticalSlope k 3))*(1+criticalOrbit k 4)+
    k^3*(-criticalOrbit k 3)*criticalSlope k 4)*(-(criticalOrbit k 2+criticalOrbit k 5))+
    k^3*(-criticalOrbit k 3)*(1+criticalOrbit k 4)*
      (-(criticalSlope k 2+criticalSlope k 5))

private theorem factor_hasDerivAt (k : ℝ) :
    HasDerivAt modelFactor (factorSlope k) k := by
  have h := ((((hasDerivAt_id k).pow 3).mul
    (criticalOrbit_hasDerivAt 3 k).neg).mul
    ((hasDerivAt_const k (1 : ℝ)).add (criticalOrbit_hasDerivAt 4 k))).mul
    ((criticalOrbit_hasDerivAt 2 k).add (criticalOrbit_hasDerivAt 5 k)).neg
  change HasDerivAt modelFactor _ k at h
  apply h.congr_deriv
  simp only [factorSlope,id_eq,Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.neg_apply,
    Nat.cast_ofNat,Nat.reduceSub,zero_add,one_mul,mul_one]

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


set_option maxHeartbeats 1000000 in
private theorem broad_orbit_certificate {k : ℝ}
    (hk : k ∈ Icc (357/200 : ℝ) (359/200)) :
    InBox (criticalOrbit k 2) (-795/1000,-785/1000) ∧
    InBox (criticalOrbit k 3) (-14/100,-9/100) ∧
    InBox (criticalOrbit k 4) (96/100,99/100) ∧
    InBox (criticalOrbit k 5) (-77/100,-64/100) ∧
    InBox (criticalSlope k 2) (-1,-1) ∧
    InBox (criticalSlope k 3) (-36/10,-33/10) ∧
    InBox (criticalSlope k 4) (-19/10,-1) ∧
    InBox (criticalSlope k 5) (24/10,6) := by
  have hK : InBox k (357/200,359/200) := hk
  have h1 : InBox (criticalOrbit k 1) (1,1) := by norm_num [InBox,criticalOrbit,Q]
  have d1 : InBox (criticalSlope k 1) (0,0) := by
    norm_num [InBox,criticalSlope,criticalOrbit]
  have h2 : InBox (criticalOrbit k 2) (-795/1000,-785/1000) := by
    apply widen (orbit_step hK h1)
    norm_num [orbitBox,addBox,negBox,mulBox]
  have d2 : InBox (criticalSlope k 2) (-1,-1) := by
    apply widen (slope_step hK h1 d1)
    norm_num [slopeBox,addBox,negBox,mulBox]
  have h3 : InBox (criticalOrbit k 3) (-14/100,-9/100) := by
    apply widen (orbit_step hK h2)
    norm_num [orbitBox,addBox,negBox,mulBox]
  have d3 : InBox (criticalSlope k 3) (-36/10,-33/10) := by
    apply widen (slope_step hK h2 d2)
    norm_num [slopeBox,addBox,negBox,mulBox]
  have h4 : InBox (criticalOrbit k 4) (96/100,99/100) := by
    apply widen (orbit_step hK h3)
    norm_num [orbitBox,addBox,negBox,mulBox]
  have d4 : InBox (criticalSlope k 4) (-19/10,-1) := by
    apply widen (slope_step hK h3 d3)
    norm_num [slopeBox,addBox,negBox,mulBox]
  have h5 : InBox (criticalOrbit k 5) (-77/100,-64/100) := by
    apply widen (orbit_step hK h4)
    norm_num [orbitBox,addBox,negBox,mulBox]
  have d5 : InBox (criticalSlope k 5) (24/10,6) := by
    apply widen (slope_step hK h4 d4)
    norm_num [slopeBox,addBox,negBox,mulBox]
  exact ⟨h2,h3,h4,h5,d2,d3,d4,d5⟩

set_option maxHeartbeats 1000000 in
private theorem factor_slope_positive {k : ℝ}
    (hk : k ∈ Icc (357/200 : ℝ) (359/200)) : 0 < factorSlope k := by
  obtain ⟨h2,h3,h4,h5,d2,d3,d4,d5⟩ := broad_orbit_certificate hk
  have hK : InBox k (357/200,359/200) := hk
  have hK2 := mul_sound hK hK
  have hK3 := mul_sound hK2 hK
  have hthree : InBox (3 : ℝ) (3,3) := ⟨le_rfl,le_rfl⟩
  have hone : InBox (1 : ℝ) (1,1) := ⟨le_rfl,le_rfl⟩
  have hA := add_sound
    (mul_sound (mul_sound hthree hK2) (neg_sound h3))
    (mul_sound hK3 (neg_sound d3))
  have hB := add_sound (mul_sound hA (add_sound hone h4))
    (mul_sound (mul_sound hK3 (neg_sound h3)) d4)
  have hC := add_sound (mul_sound hB (neg_sound (add_sound h2 h5)))
    (mul_sound (mul_sound (mul_sound hK3 (neg_sound h3)) (add_sound hone h4))
      (neg_sound (add_sound d2 d5)))
  have hbound : InBox (factorSlope k) (40,100) := by
    apply widen (x := factorSlope k) (by
      convert hC using 1 <;> simp only [factorSlope,pow_succ,pow_zero] <;> ring)
    norm_num [addBox,negBox,mulBox]
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ)<40) hbound.1

/-- The factored relation is strictly increasing throughout the broader
signed coefficient interval, not only inside the narrow root isolator. -/
theorem modelFactor_strictMonoOn :
    StrictMonoOn modelFactor (Icc (357/200 : ℝ) (359/200)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    (Continuous.continuousOn (continuous_iff_continuousAt.mpr
      (fun k => (factor_hasDerivAt k).continuousAt)))
    (fun k _ => (factor_hasDerivAt k).hasDerivWithinAt)
  intro k hk
  exact factor_slope_positive (interior_subset hk)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem modelFactor_endpoint_margins :
    modelFactor (17903/10000) < 2-1/1000 ∧
      2+1/1000 < modelFactor (17904/10000) := by
  norm_num [modelFactor,criticalOrbit,Q]

/-- A quantitative full-factor comparison locates every candidate in
exactly the archived narrow coefficient isolator. -/
theorem modelFactor_near_two_implies_narrow {k : ℝ}
    (hk : k ∈ Icc (357/200 : ℝ) (359/200))
    (herr : |modelFactor k-2|<1/1000) :
    k ∈ Ioo (17903/10000 : ℝ) (17904/10000) := by
  have hsmall := abs_lt.mp herr
  constructor
  · by_contra! hle
    have hm := modelFactor_strictMonoOn.monotoneOn hk (by norm_num) hle
    have he := modelFactor_endpoint_margins.1
    linarith [hsmall.1]
  · by_contra! hle
    have hm := modelFactor_strictMonoOn.monotoneOn (by norm_num) hk hle
    have he := modelFactor_endpoint_margins.2
    linarith [hsmall.2]

end
end GlobalSignedModelFactor
