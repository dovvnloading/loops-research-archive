import CriticalReturnRelationStability

/-!
# Finite-difference stability of the signed six-return relation

This module supplies the composition estimate used for the actual
restrictive family.  The error must be small in both the parameter and
the spatial variable.  A uniform map error alone would not imply the
strict parameter ordering proved here.
-/

namespace GlobalSignedRelationStability

open Set Function LoopsLimitingCrestParameter LimitingCrestPerturbation

noncomputable section

/-- The normalized signed collision functional of a real return map. -/
def signedRelation (H : ℝ → ℝ) : ℝ := H^[6] 0+H^[3] 0

private def differenceCoefficient : ℕ → ℝ
  | 0 => 0
  | n+1 => 5*differenceCoefficient n+
      22*(2+6*errorCoefficient n)*errorCoefficient n+
      200+600*errorCoefficient n

private theorem errorCoefficient_nonneg (n : ℕ) : 0≤errorCoefficient n := by
  induction n with
  | zero => norm_num [errorCoefficient]
  | succ n ih => simp only [errorCoefficient]; positivity

private theorem differenceCoefficient_nonneg (n : ℕ) :
    0≤differenceCoefficient n := by
  induction n with
  | zero => norm_num [differenceCoefficient]
  | succ n ih =>
    have h := errorCoefficient_nonneg n
    simp only [differenceCoefficient]
    positivity

private theorem unit_square {x : ℝ} (hx : x∈Icc (-1 : ℝ) 1) : x^2≤1 := by
  simpa using sq_le_sq' hx.1 hx.2

private theorem unit_sum {x y : ℝ}
    (hx : x∈Icc (-1 : ℝ) 1) (hy : y∈Icc (-1 : ℝ) 1) : |x+y|≤2 := by
  have hx' := abs_le.mpr hx
  have hy' := abs_le.mpr hy
  linarith [abs_add_le x y]

private theorem quadratic_mapsTo {k : ℝ} (hk : k∈Icc (0 : ℝ) 2) :
    MapsTo (Q k) (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) := by
  intro x hx
  have h0 := mul_nonneg hk.1 (sq_nonneg x)
  have h2 := mul_le_mul_of_nonneg_left (unit_square hx) hk.1
  change -1≤1-k*x^2 ∧ 1-k*x^2≤1
  constructor <;> nlinarith only [h0,h2,hk.2]

private theorem iterate_mem_unit (H : ℝ → ℝ)
    (hH : MapsTo H (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)) (n : ℕ) :
    H^[n] 0∈Icc (-1 : ℝ) 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hH ih

private theorem quadratic_lipschitz {k x y : ℝ}
    (hk : k∈Icc (0 : ℝ) 2)
    (hx : x∈Icc (-1 : ℝ) 1) (hy : y∈Icc (-1 : ℝ) 1) :
    |Q k x-Q k y|≤4*|x-y| := by
  have hkabs : |k|≤2 := abs_le.mpr ⟨by linarith [hk.1],hk.2⟩
  have hcoef : |k| * |x+y|≤4 := by
    have h := mul_le_mul hkabs (unit_sum hx hy) (abs_nonneg (x+y))
      (by norm_num : (0 : ℝ)≤2)
    norm_num at h
    exact h
  have hid : Q k x-Q k y= -k*(x+y)*(x-y) := by unfold Q; ring
  rw [hid,abs_mul,abs_mul,abs_neg]
  exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg (x-y))

private theorem quadratic_parameter {a b y : ℝ} (hy : y∈Icc (-1 : ℝ) 1) :
    |Q a y-Q b y|≤|a-b| := by
  have hid : Q a y-Q b y= -(a-b)*y^2 := by unfold Q; ring
  rw [hid,abs_mul,abs_neg,abs_of_nonneg (sq_nonneg y)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (unit_square hy) (abs_nonneg (a-b))

private theorem quadratic_joint {a b x y : ℝ}
    (ha : a∈Icc (0 : ℝ) 2)
    (hx : x∈Icc (-1 : ℝ) 1) (hy : y∈Icc (-1 : ℝ) 1) :
    |Q a x-Q b y|≤4*|x-y|+|a-b| := by
  calc
    _=|(Q a x-Q a y)+(Q a y-Q b y)| := by congr 1; ring
    _≤|Q a x-Q a y|+|Q a y-Q b y| := abs_add_le _ _
    _≤4*|x-y|+|a-b| :=
      add_le_add (quadratic_lipschitz ha hx hy) (quadratic_parameter hy)

private theorem remainder_joint {H G : ℝ → ℝ} {a b t x y : ℝ}
    (hparameter : ∀ z∈Icc (-1 : ℝ) 1,
      |(H z-Q a z)-(G z-Q b z)|≤200*t*|a-b|)
    (hspatial : ∀ z∈Icc (-1 : ℝ) 1, ∀ w∈Icc (-1 : ℝ) 1,
      |(H z-Q a z)-(H w-Q a w)|≤300*t*|z-w|)
    (hx : x∈Icc (-1 : ℝ) 1) (hy : y∈Icc (-1 : ℝ) 1) :
    |(H x-Q a x)-(G y-Q b y)|≤300*t*|x-y|+200*t*|a-b| := by
  calc
    _=|((H x-Q a x)-(H y-Q a y))+((H y-Q a y)-(G y-Q b y))| := by
      congr 1; ring
    _≤|(H x-Q a x)-(H y-Q a y)|+|(H y-Q a y)-(G y-Q b y)| :=
      abs_add_le _ _
    _≤300*t*|x-y|+200*t*|a-b| :=
      add_le_add (hspatial x hx y hy) (hparameter y hy)

private theorem actual_joint {H G : ℝ → ℝ} {a b t x y : ℝ}
    (ha : a∈Icc (0 : ℝ) 2) (ht : 0≤t) (htsmall : t≤1/300)
    (hparameter : ∀ z∈Icc (-1 : ℝ) 1,
      |(H z-Q a z)-(G z-Q b z)|≤200*t*|a-b|)
    (hspatial : ∀ z∈Icc (-1 : ℝ) 1, ∀ w∈Icc (-1 : ℝ) 1,
      |(H z-Q a z)-(H w-Q a w)|≤300*t*|z-w|)
    (hx : x∈Icc (-1 : ℝ) 1) (hy : y∈Icc (-1 : ℝ) 1) :
    |H x-G y|≤5*|x-y|+2*|a-b| := by
  have hR := remainder_joint hparameter hspatial hx hy
  have hQ := quadratic_joint ha hx hy (b := b)
  have hsp := mul_le_mul_of_nonneg_right
    (show 300*t≤1 by linarith) (abs_nonneg (x-y))
  have hpa := mul_le_mul_of_nonneg_right
    (show 200*t≤1 by linarith) (abs_nonneg (a-b))
  calc
    _=|(Q a x-Q b y)+((H x-Q a x)-(G y-Q b y))| := by congr 1; ring
    _≤|Q a x-Q b y|+|(H x-Q a x)-(G y-Q b y)| := abs_add_le _ _
    _≤5*|x-y|+2*|a-b| := by linarith only [hR,hQ,hsp,hpa]

private theorem model_orbit_difference {a b : ℝ}
    (ha : a∈Icc (0 : ℝ) 2) (hb : b∈Icc (0 : ℝ) 2) (n : ℕ) :
    |(Q a)^[n] 0-(Q b)^[n] 0|≤errorCoefficient n*|a-b| := by
  induction n with
  | zero => simp [errorCoefficient]
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    have h := quadratic_joint (b := b) ha
      (iterate_mem_unit (Q a) (quadratic_mapsTo ha) n)
      (iterate_mem_unit (Q b) (quadratic_mapsTo hb) n)
    have hm := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ)≤5)
    have hnonneg := abs_nonneg ((Q a)^[n] 0-(Q b)^[n] 0)
    simp only [errorCoefficient]
    nlinarith only [h,hm,hnonneg]

private theorem actual_orbit_difference {H G : ℝ → ℝ} {a b t : ℝ}
    (ha : a∈Icc (0 : ℝ) 2) (ht : 0≤t) (htsmall : t≤1/300)
    (hH : MapsTo H (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1))
    (hG : MapsTo G (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1))
    (hparameter : ∀ z∈Icc (-1 : ℝ) 1,
      |(H z-Q a z)-(G z-Q b z)|≤200*t*|a-b|)
    (hspatial : ∀ z∈Icc (-1 : ℝ) 1, ∀ w∈Icc (-1 : ℝ) 1,
      |(H z-Q a z)-(H w-Q a w)|≤300*t*|z-w|) (n : ℕ) :
    |H^[n] 0-G^[n] 0|≤2*errorCoefficient n*|a-b| := by
  induction n with
  | zero => simp [errorCoefficient]
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    have h := actual_joint ha ht htsmall hparameter hspatial
      (iterate_mem_unit H hH n) (iterate_mem_unit G hG n)
    have hm := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ)≤5)
    simp only [errorCoefficient]
    nlinarith only [h,hm]

private theorem orbit_error_uniform {G : ℝ → ℝ} {b t : ℝ}
    (hb : b∈Icc (0 : ℝ) 2) (ht : 0≤t)
    (hG : MapsTo G (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1))
    (hclose : ∀ z∈Icc (-1 : ℝ) 1, |G z-Q b z|≤22*t) (n : ℕ) :
    |G^[n] 0-(Q b)^[n] 0|≤22*errorCoefficient n*t := by
  induction n with
  | zero => simp [errorCoefficient]
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    have hR := hclose _ (iterate_mem_unit G hG n)
    have hQ := quadratic_lipschitz hb (iterate_mem_unit G hG n)
      (iterate_mem_unit (Q b) (quadratic_mapsTo hb) n)
    have hm := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ)≤5)
    have hnonneg := abs_nonneg (G^[n] 0-(Q b)^[n] 0)
    calc
      _=|(G (G^[n] 0)-Q b (G^[n] 0))+
        (Q b (G^[n] 0)-Q b ((Q b)^[n] 0))| := by congr 1; ring
      _≤|G (G^[n] 0)-Q b (G^[n] 0)|+
        |Q b (G^[n] 0)-Q b ((Q b)^[n] 0)| := abs_add_le _ _
      _≤22*errorCoefficient (n+1)*t := by
        simp only [errorCoefficient]
        nlinarith only [hR,hQ,hm,hnonneg]

private theorem quadratic_secant_coefficient {a b x y u v C : ℝ}
    (hb : b∈Icc (0 : ℝ) 2) (hC : 0≤C)
    (hx : x∈Icc (-1 : ℝ) 1) (hu : u∈Icc (-1 : ℝ) 1)
    (hxy : |x-y|≤2*C*|a-b|) (huv : |u-v|≤C*|a-b|) :
    |a*(x+u)-b*(y+v)|≤(2+6*C)*|a-b| := by
  have hbabs : |b|≤2 := abs_le.mpr ⟨by linarith [hb.1],hb.2⟩
  have hsum : |(x-y)+(u-v)|≤3*C*|a-b| := by
    linarith [abs_add_le (x-y) (u-v)]
  have h1 := mul_le_mul_of_nonneg_left (unit_sum hx hu) (abs_nonneg (a-b))
  have h2 := mul_le_mul hbabs hsum (abs_nonneg ((x-y)+(u-v)))
    (by norm_num : (0 : ℝ)≤2)
  calc
    _=|(a-b)*(x+u)+b*((x-y)+(u-v))| := by congr 1; ring
    _≤|(a-b)*(x+u)|+|b*((x-y)+(u-v))| := abs_add_le _ _
    _≤(2+6*C)*|a-b| := by
      simp only [abs_mul]
      nlinarith only [h1,h2]

private theorem orbit_error_difference {H G : ℝ → ℝ} {a b t : ℝ}
    (ha : a∈Icc (0 : ℝ) 2) (hb : b∈Icc (0 : ℝ) 2)
    (ht : 0≤t) (htsmall : t≤1/300)
    (hH : MapsTo H (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1))
    (hG : MapsTo G (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1))
    (hclose : ∀ z∈Icc (-1 : ℝ) 1, |G z-Q b z|≤22*t)
    (hparameter : ∀ z∈Icc (-1 : ℝ) 1,
      |(H z-Q a z)-(G z-Q b z)|≤200*t*|a-b|)
    (hspatial : ∀ z∈Icc (-1 : ℝ) 1, ∀ w∈Icc (-1 : ℝ) 1,
      |(H z-Q a z)-(H w-Q a w)|≤300*t*|z-w|) (n : ℕ) :
    |(H^[n] 0-(Q a)^[n] 0)-(G^[n] 0-(Q b)^[n] 0)|≤
      differenceCoefficient n*t*|a-b| := by
  induction n with
  | zero => simp [differenceCoefficient]
  | succ n ih =>
    let x := H^[n] 0
    let y := G^[n] 0
    let u := (Q a)^[n] 0
    let v := (Q b)^[n] 0
    let C := errorCoefficient n
    let D := differenceCoefficient n
    have hx : x∈Icc (-1 : ℝ) 1 := iterate_mem_unit H hH n
    have hy : y∈Icc (-1 : ℝ) 1 := iterate_mem_unit G hG n
    have hu : u∈Icc (-1 : ℝ) 1 := iterate_mem_unit (Q a) (quadratic_mapsTo ha) n
    have hv : v∈Icc (-1 : ℝ) 1 := iterate_mem_unit (Q b) (quadratic_mapsTo hb) n
    have hC : 0≤C := errorCoefficient_nonneg n
    have hD : 0≤D := differenceCoefficient_nonneg n
    have hxy : |x-y|≤2*C*|a-b| :=
      actual_orbit_difference ha ht htsmall hH hG hparameter hspatial n
    have huv : |u-v|≤C*|a-b| := model_orbit_difference ha hb n
    have hyerror : |y-v|≤22*C*t := orbit_error_uniform hb ht hG hclose n
    have hcoef := quadratic_secant_coefficient hb hC hx hu hxy huv
    have haabs : |a|≤2 := abs_le.mpr ⟨by linarith [ha.1],ha.2⟩
    have hfirstcoef : |-a*(x+u)|≤5 := by
      rw [abs_mul,abs_neg]
      have h := mul_le_mul haabs (unit_sum hx hu) (abs_nonneg (x+u))
        (by norm_num : (0 : ℝ)≤2)
      linarith only [h]
    change |(x-u)-(y-v)|≤D*t*|a-b| at ih
    have hfirst := mul_le_mul hfirstcoef ih (abs_nonneg ((x-u)-(y-v)))
      (by norm_num : (0 : ℝ)≤5)
    have hsecond := mul_le_mul hcoef hyerror (abs_nonneg (y-v))
      (show 0≤(2+6*C)*|a-b| by positivity)
    have hR := remainder_joint hparameter hspatial hx hy
    have hRxy := mul_le_mul_of_nonneg_left hxy (show 0≤300*t by positivity)
    have hid : (H x-Q a u)-(G y-Q b v)=
        (-a*(x+u))*((x-u)-(y-v))-
          (a*(x+u)-b*(y+v))*(y-v)+((H x-Q a x)-(G y-Q b y)) := by
      unfold Q
      ring
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',
      Function.iterate_succ_apply',Function.iterate_succ_apply']
    change |(H x-Q a u)-(G y-Q b v)|≤differenceCoefficient (n+1)*t*|a-b|
    rw [hid]
    calc
      _≤|(-a*(x+u))*((x-u)-(y-v))-(a*(x+u)-b*(y+v))*(y-v)|+
          |(H x-Q a x)-(G y-Q b y)| := abs_add_le _ _
      _≤(|(-a*(x+u))*((x-u)-(y-v))|+
          |(a*(x+u)-b*(y+v))*(y-v)|)+|(H x-Q a x)-(G y-Q b y)| :=
        add_le_add (abs_sub _ _) le_rfl
      _≤differenceCoefficient (n+1)*t*|a-b| := by
        simp only [abs_mul] at hfirst hsecond ⊢
        change _≤(5*D+22*(2+6*C)*C+200+600*C)*t*|a-b|
        nlinarith only [hfirst,hsecond,hR,hRxy]

/-- Two-parameter and spatial remainder bounds propagate through the
literal six-plus-three iterate functional. -/
theorem signed_relation_error_lipschitz {H G : ℝ → ℝ} {a b t : ℝ}
    (ha : a∈Icc (0 : ℝ) 2) (hb : b∈Icc (0 : ℝ) 2)
    (ht : 0≤t) (htsmall : t≤1/300)
    (hH : MapsTo H (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1))
    (hG : MapsTo G (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1))
    (hclose : ∀ z∈Icc (-1 : ℝ) 1, |G z-Q b z|≤22*t)
    (hparameter : ∀ z∈Icc (-1 : ℝ) 1,
      |(H z-Q a z)-(G z-Q b z)|≤200*t*|a-b|)
    (hspatial : ∀ z∈Icc (-1 : ℝ) 1, ∀ w∈Icc (-1 : ℝ) 1,
      |(H z-Q a z)-(H w-Q a w)|≤300*t*|z-w|) :
    |(signedRelation H-relation a)-(signedRelation G-relation b)|≤
      110000000*t*|a-b| := by
  have h6 := orbit_error_difference ha hb ht htsmall hH hG hclose hparameter hspatial 6
  have h3 := orbit_error_difference ha hb ht htsmall hH hG hclose hparameter hspatial 3
  rw [show differenceCoefficient 6=103595496 by
    norm_num [differenceCoefficient,errorCoefficient]] at h6
  rw [show differenceCoefficient 3=18696 by
    norm_num [differenceCoefficient,errorCoefficient]] at h3
  have hid : (signedRelation H-relation a)-(signedRelation G-relation b)=
      ((H^[6] 0-(Q a)^[6] 0)-(G^[6] 0-(Q b)^[6] 0))+
        ((H^[3] 0-(Q a)^[3] 0)-(G^[3] 0-(Q b)^[3] 0)) := by
    simp only [signedRelation,relation,criticalOrbit_eq_iterate]
    ring
  rw [hid]
  have htabs : 0≤t*|a-b| := mul_nonneg ht (abs_nonneg (a-b))
  calc
    _≤|(H^[6] 0-(Q a)^[6] 0)-(G^[6] 0-(Q b)^[6] 0)|+
      |(H^[3] 0-(Q a)^[3] 0)-(G^[3] 0-(Q b)^[3] 0)| := abs_add_le _ _
    _≤110000000*t*|a-b| := by nlinarith only [h6,h3,htabs]

private theorem relation_secant_gt_six {a b : ℝ}
    (ha : a∈parameterInterval) (hb : b∈parameterInterval) (hab : a<b) :
    6*(b-a)<relation b-relation a := by
  have hd (t : ℝ) : HasDerivAt (fun s => relation s-6*s)
      (criticalSlope t 6+criticalSlope t 3-6) t := by
    convert (relation_hasDerivAt t).sub ((hasDerivAt_id t).const_mul (6 : ℝ)) using 1
    all_goals first | rfl | simp
  have hcont : Continuous (fun t => relation t-6*t) :=
    continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hm : StrictMonoOn (fun t => relation t-6*t) parameterInterval := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hcont.continuousOn
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    have h := relation_slope_gt_six (interior_subset ht)
    linarith only [h]
  have h := hm ha hb hab
  linarith only [h]

/-- The model transverse margin survives an explicit two-variable
remainder budget.  The resulting order is an order of the actual maps. -/
theorem signed_relation_secant_gt_five {H G : ℝ → ℝ} {a b t : ℝ}
    (ha : a∈parameterInterval) (hb : b∈parameterInterval) (hab : a<b)
    (ht : 0≤t) (htsmall : 110000000*t≤1)
    (hH : MapsTo H (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1))
    (hG : MapsTo G (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1))
    (hclose : ∀ z∈Icc (-1 : ℝ) 1, |G z-Q b z|≤22*t)
    (hparameter : ∀ z∈Icc (-1 : ℝ) 1,
      |(H z-Q a z)-(G z-Q b z)|≤200*t*|a-b|)
    (hspatial : ∀ z∈Icc (-1 : ℝ) 1, ∀ w∈Icc (-1 : ℝ) 1,
      |(H z-Q a z)-(H w-Q a w)|≤300*t*|z-w|) :
    5*(b-a)<signedRelation G-signedRelation H := by
  have ha02 : a∈Icc (0 : ℝ) 2 := by
    constructor <;> linarith [ha.1,ha.2]
  have hb02 : b∈Icc (0 : ℝ) 2 := by
    constructor <;> linarith [hb.1,hb.2]
  have he := signed_relation_error_lipschitz ha02 hb02 ht
    (show t≤1/300 by linarith) hH hG hclose hparameter hspatial
  have hbound := mul_le_mul_of_nonneg_right htsmall (sub_nonneg.mpr hab.le)
  rw [abs_of_neg (sub_neg.mpr hab)] at he
  have herr := (abs_le.mp he).2
  have hmodel := relation_secant_gt_six ha hb hab
  nlinarith only [herr,hmodel,hbound]

end
end GlobalSignedRelationStability
