import ActualCrestQuarticScale
import ActualCrestSignedDrift

/-!
# The correlated parameter displacement forced by the quartic profile

The actual signed relation is expanded about the quadratic orbit at its
own quadratic coefficient. Its response to the proved quartic term is
retained through all six returns, with a complete second-order error.
The signed relation and a certified secant slope then force the actual
parameter displacement to lie in a narrow interval proportional to the
same quartic coefficient.
-/

namespace ActualCrestQuarticRelation

open Set Function
open LimitingCrest LimitingCrestQuadraticReturn LoopsLimitingCrestParameter
open NearTwoShooting NearTwoTip GlobalCrestSourceGates
open ActualCrestQuartic ActualCrestQuarticScale ActualCrestSignedDrift

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The exact first variation of the quadratic critical orbit in the
quartic direction, with its quadratic coefficient fixed. -/
def quarticResponse (k : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => -2*k*criticalOrbit k n*quarticResponse k n+(criticalOrbit k n)^4

/- The finite interval arithmetic below reuses the elementary private
box engine from LimitingCrestParameter; the additional response boxes
certify the correlation needed for the actual, rather than model, tip. -/
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

private def responseBox (K X B : Box) : Box :=
  addBox (negBox (mulBox (2,2) (mulBox K (mulBox X B))))
    (mulBox (mulBox X X) (mulBox X X))

private theorem response_step {k : ℝ} {n : ℕ} {K X B : Box}
    (hk : InBox k K) (hx : InBox (criticalOrbit k n) X)
    (hb : InBox (quarticResponse k n) B) :
    InBox (quarticResponse k (n+1)) (responseBox K X B) := by
  have h := add_sound
    (neg_sound (mul_sound (show InBox (2 : ℝ) (2,2) from ⟨le_rfl,le_rfl⟩)
      (mul_sound hk (mul_sound hx hb))))
    (mul_sound (mul_sound hx hx) (mul_sound hx hx))
  have he : quarticResponse k (n+1) =
      -(2*(k*(criticalOrbit k n*quarticResponse k n)))+
        (criticalOrbit k n*criticalOrbit k n)*(criticalOrbit k n*criticalOrbit k n) := by
    simp only [quarticResponse]
    ring
  rw [he]
  exact h

private theorem interval_certificate {k : ℝ} (hk : k ∈ parameterInterval) :
    (∀ n : ℕ, n ≤ 6 → |criticalOrbit k n| ≤ 1) ∧
    (6599/1000 : ℝ) < criticalSlope k 6+criticalSlope k 3 ∧
    criticalSlope k 6+criticalSlope k 3 < (6657/1000 : ℝ) ∧
    quarticResponse k 6+quarticResponse k 3 ∈ Icc (-6265/1000 : ℝ) (-6211/1000) := by
  have hK : InBox k (17903/10000,17904/10000) := hk
  have h0 : InBox (criticalOrbit k 0) (0,0) := by norm_num [InBox,criticalOrbit]
  have d0 : InBox (criticalSlope k 0) (0,0) := by norm_num [InBox,criticalSlope]
  have b0 : InBox (quarticResponse k 0) (0,0) := by norm_num [InBox,quarticResponse]
  have h1 : InBox (criticalOrbit k 1) (1,1) := by norm_num [InBox,criticalOrbit,Q]
  have d1 : InBox (criticalSlope k 1) (0,0) := by
    norm_num [InBox,criticalSlope,criticalOrbit]
  have b1 : InBox (quarticResponse k 1) (0,0) := by
    norm_num [InBox,quarticResponse,criticalOrbit]
  have h2 : InBox (criticalOrbit k 2) (-790400/1000000,-790300/1000000) := by
    apply widen (orbit_step hK h1)
    norm_num [orbitBox,addBox,negBox,mulBox]
  have d2 : InBox (criticalSlope k 2) (-1,-1) := by
    apply widen (slope_step hK h1 d1)
    norm_num [slopeBox,addBox,negBox,mulBox]
  have b2 : InBox (quarticResponse k 2) (1,1) := by
    apply widen (response_step hK h1 b1)
    norm_num [responseBox,addBox,negBox,mulBox]
  have h3 : InBox (criticalOrbit k 3) (-118521/1000000,-118174/1000000) := by
    apply widen (orbit_step hK h2)
    norm_num [orbitBox,addBox,negBox,mulBox]
  have d3 : InBox (criticalSlope k 3) (-3454997/1000000,-3454322/1000000) := by
    apply widen (slope_step hK h2 d2)
    norm_num [slopeBox,addBox,negBox,mulBox]
  have b3 : InBox (quarticResponse k 3) (3219840/1000000,3220555/1000000) := by
    apply widen (response_step hK h2 b2)
    norm_num [responseBox,addBox,negBox,mulBox]
  have h4 : InBox (criticalOrbit k 4) (974849/1000000,974999/1000000) := by
    apply widen (orbit_step hK h3)
    norm_num [orbitBox,addBox,negBox,mulBox]
  have d4 : InBox (criticalSlope k 4) (-1480348/1000000,-1475605/1000000) := by
    apply widen (slope_step hK h3 d3)
    norm_num [slopeBox,addBox,negBox,mulBox]
  have b4 : InBox (quarticResponse k 4) (1362618/1000000,1367001/1000000) := by
    apply widen (response_step hK h3 b3)
    norm_num [responseBox,addBox,negBox,mulBox]
  have h5 : InBox (criticalOrbit k 5) (-701996/1000000,-701376/1000000) := by
    apply widen (orbit_step hK h4)
    norm_num [orbitBox,addBox,negBox,mulBox]
  have d5 : InBox (criticalSlope k 5) (4200041/1000000,4217974/1000000) := by
    apply widen (slope_step hK h4 d4)
    norm_num [slopeBox,addBox,negBox,mulBox]
  have b5 : InBox (quarticResponse k 5) (-3869451/1000000,-3852594/1000000) := by
    apply widen (response_step hK h4 b4)
    norm_num [responseBox,addBox,negBox,mulBox]
  have h6 : InBox (criticalOrbit k 6) (117693/1000000,119301/1000000) := by
    apply widen (orbit_step hK h5)
    norm_num [orbitBox,addBox,negBox,mulBox]
  have d6 : InBox (criticalSlope k 6) (10054961/1000000,10110824/1000000) := by
    apply widen (slope_step hK h5 d5)
    norm_num [slopeBox,addBox,negBox,mulBox]
  have b6 : InBox (quarticResponse k 6) (-9484674/1000000,-9432349/1000000) := by
    apply widen (response_step hK h5 b5)
    norm_num [responseBox,addBox,negBox,mulBox]
  dsimp only [InBox] at h0 h1 h2 h3 h4 h5 h6 d3 d6 b3 b6
  refine ⟨?_,?_,?_,?_⟩
  · intro n hn
    interval_cases n <;> rw [abs_le] <;> constructor <;>
      linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2]
  · linarith [d3.1,d6.1]
  · linarith [d3.2,d6.2]
  · constructor <;> linarith [b3.1,b3.2,b6.1,b6.2]

/-- A convenient rational budget at the fixed eventual threshold. -/
theorem scale_small_hundred {p : ℕ} (hp : 100 ≤ p) :
    scale p ≤ 1/(10 : ℝ)^40 := by
  have h : scale p ≤ scale 100 :=
    pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) ≤ 1) hp
  have h100 : scale 100 ≤ 1/(10 : ℝ)^40 := by norm_num [scale]
  exact h.trans h100

private def realQuarticError (c : ℝ) (p : ℕ) (x : ℝ) : ℝ :=
  actualMap c p x-(1-kappa p c*x^2+normalizedQuartic c p*x^4)

private theorem real_quartic_error {p : ℕ} (hp : 17 ≤ p) {c x : ℝ}
    (hc : ActualTip p c) (hx : |x| ≤ 3/2) :
    |realQuarticError c p x| ≤ 400*(scale p)^2 := by
  have h := normalized_quartic_error hp hc
    (show ‖(x : ℂ)‖ ≤ (3/2 : ℝ) by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using hx)
  have hr := (Complex.abs_re_le_norm
    (normalizedReturn c p (x : ℂ)-
      (complexMap (kappa p c) (x : ℂ)+(normalizedQuartic c p : ℂ)*(x : ℂ)^4))).trans h
  simpa [realQuarticError,actualMap,complexMap] using hr

private theorem fourth_difference_bound {x y : ℝ}
    (hx : |x| ≤ 3/2) (hy : |y| ≤ 1) :
    |x^4-y^4| ≤ 10*|x-y| := by
  have hs : |x+y| ≤ (5/2 : ℝ) := (abs_add x y).trans (by linarith)
  have hx2 := pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hy2 := pow_le_pow_left₀ (abs_nonneg y) hy 2
  have ht : |x^2+y^2| ≤ 4 := by
    rw [abs_of_nonneg (add_nonneg (sq_nonneg x) (sq_nonneg y))]
    simpa only [sq_abs] using (show |x|^2+|y|^2 ≤ (4 : ℝ) by nlinarith)
  calc
    |x^4-y^4| = (|x-y| *|x+y|)*|x^2+y^2| := by
      rw [← abs_mul,← abs_mul]
      congr 1
      ring
    _ ≤ (|x-y| *(5/2))*4 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs (abs_nonneg _)) ht
        (abs_nonneg _) (by positivity)
    _ = 10*|x-y| := by ring

private theorem actual_orbit_difference {p : ℕ} (hp : 100 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {n : ℕ} (hn : n ≤ 6) :
    |actualOrbit c p 0 n-criticalOrbit (kappa p c) n| ≤ (10 : ℝ)^(n+2)*scale p := by
  let k := kappa p c
  let b := normalizedQuartic c p
  let q := scale p
  have hq : 0 < q := scale_pos p
  have hqsmall : q ≤ 1/(10 : ℝ)^40 := scale_small_hundred hp
  have hk : |k| ≤ 2 := by
    have hk : k ∈ parameterInterval := hc.2.2.2.1
    rw [abs_le]
    constructor <;> linarith [hk.1,hk.2]
  have hb : 0 ≤ b ∧ b ≤ 7*q := by
    have h := normalized_quartic_scale_bounds (by omega : 17 ≤ p) hc
    dsimp only [b,q]
    exact ⟨by linarith [scale_pos p],h.2.le⟩
  have hu := (interval_certificate hc.2.2.2.1).1
  have hall : ∀ m : ℕ, m ≤ 6 →
      |actualOrbit c p 0 m-criticalOrbit k m| ≤ (10 : ℝ)^(m+2)*q := by
    intro m
    induction m with
    | zero => intro hm; simp only [actualOrbit,criticalOrbit,sub_self,abs_zero]; positivity
    | succ m ih =>
      intro hm
      let x := actualOrbit c p 0 m
      let u := criticalOrbit k m
      have hdiff : |x-u| ≤ (10 : ℝ)^(m+2)*q := ih (by omega)
      have hu1 : |u| ≤ 1 := hu m (by omega)
      have hpower : (10 : ℝ)^(m+2) ≤ (10 : ℝ)^8 :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hcoarse : |x-u| ≤ (10 : ℝ)^8*q :=
        hdiff.trans (mul_le_mul_of_nonneg_right hpower hq.le)
      have hx : |x| ≤ (3/2 : ℝ) := by
        have hs : |x| ≤ |x-u|+|u| := by
          calc
            |x| = |(x-u)+u| := by rw [sub_add_cancel]
            _ ≤ _ := abs_add _ _
        norm_num at hqsmall hcoarse
        linarith
      have hcoeff : |-k*(x+u)| ≤ 5 := by
        rw [abs_mul,abs_neg]
        have hs : |x+u| ≤ (5/2 : ℝ) := (abs_add x u).trans (by linarith)
        exact (mul_le_mul hk hs (abs_nonneg _) (by norm_num)).trans (by norm_num)
      have hx4 : |x|^4 ≤ (6 : ℝ) :=
        (pow_le_pow_left₀ (abs_nonneg x) hx 4).trans (by norm_num)
      have hterm : |b*x^4| ≤ 42*q := by
        rw [abs_mul,abs_of_nonneg hb.1,abs_pow]
        calc
          b*|x|^4 ≤ (7*q)*6 :=
            mul_le_mul hb.2 hx4 (by positivity) (by positivity)
          _ = 42*q := by ring
      have herr := real_quartic_error (by omega : 17 ≤ p) hc hx
      change |realQuarticError c p x| ≤ 400*q^2 at herr
      have herror : |realQuarticError c p x| ≤ q := by
        have hsmall : q ≤ 1/400 := by norm_num at hqsmall; linarith
        have hs := mul_le_mul_of_nonneg_right hsmall hq.le
        nlinarith only [herr,hs]
      have hid : actualOrbit c p 0 (m+1)-criticalOrbit k (m+1) =
          (-k*(x+u))*(x-u)+b*x^4+realQuarticError c p x := by
        change actualMap c p x-(1-k*u^2) = _
        dsimp only [realQuarticError,b,k]
        ring
      rw [hid]
      have habs : |(-k*(x+u))*(x-u)+b*x^4+realQuarticError c p x| ≤
          5*((10 : ℝ)^(m+2)*q)+43*q := by
        calc
          _ ≤ |(-k*(x+u))*(x-u)+b*x^4|+|realQuarticError c p x| := abs_add _ _
          _ ≤ |(-k*(x+u))*(x-u)|+|b*x^4|+|realQuarticError c p x| :=
            add_le_add_right (abs_add _ _) _
          _ ≤ 5*((10 : ℝ)^(m+2)*q)+42*q+q := by
            rw [abs_mul]
            exact add_le_add (add_le_add
              (mul_le_mul hcoeff hdiff (abs_nonneg _) (by norm_num)) hterm) herror
          _ = _ := by ring
      have hmin : (100 : ℝ) ≤ (10 : ℝ)^(m+2) := by
        have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10)
          (show 2 ≤ m+2 by omega)
        norm_num at h
        exact h
      have hmcoeff : 5*(10 : ℝ)^(m+2)+43 ≤ 10*(10 : ℝ)^(m+2) := by linarith
      have hmprod := mul_le_mul_of_nonneg_right hmcoeff hq.le
      have he : (10 : ℝ)^(m+1+2) = 10*(10 : ℝ)^(m+2) := by
        rw [show m+1+2 = (m+2)+1 by omega,pow_succ]
        ring
      rw [he]
      nlinarith only [habs,hmprod]
  exact hall n hn

private def responseRemainder (c : ℝ) (p n : ℕ) : ℝ :=
  actualOrbit c p 0 n-criticalOrbit (kappa p c) n-
    quarticResponse (kappa p c) n*normalizedQuartic c p

private theorem response_step_error {p : ℕ} (hp : 100 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {n : ℕ} (hn : n ≤ 5) :
    |responseRemainder c p (n+1)| ≤
      4*|responseRemainder c p n|+(10 : ℝ)^17*(scale p)^2 := by
  let k := kappa p c
  let b := normalizedQuartic c p
  let q := scale p
  let x := actualOrbit c p 0 n
  let u := criticalOrbit k n
  have hq : 0 < q := scale_pos p
  have hqsmall : q ≤ 1/(10 : ℝ)^40 := scale_small_hundred hp
  have hk : |k| ≤ 2 := by
    have hk : k ∈ parameterInterval := hc.2.2.2.1
    rw [abs_le]
    constructor <;> linarith [hk.1,hk.2]
  have hb : 0 ≤ b ∧ b ≤ 7*q := by
    have h := normalized_quartic_scale_bounds (by omega : 17 ≤ p) hc
    exact ⟨by dsimp only [b]; linarith [scale_pos p],h.2.le⟩
  have hu : |u| ≤ 1 := (interval_certificate hc.2.2.2.1).1 n (by omega)
  have hdiff : |x-u| ≤ (10 : ℝ)^(n+2)*q := actual_orbit_difference hp hc (by omega)
  have hpower : (10 : ℝ)^(n+2) ≤ (10 : ℝ)^8 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hcoarse : |x-u| ≤ (10 : ℝ)^8*q :=
    hdiff.trans (mul_le_mul_of_nonneg_right hpower hq.le)
  have hx : |x| ≤ (3/2 : ℝ) := by
    have hs : |x| ≤ |x-u|+|u| := by
      calc
        |x| = |(x-u)+u| := by rw [sub_add_cancel]
        _ ≤ _ := abs_add _ _
    norm_num at hqsmall hcoarse
    linarith
  have hcoef : |-2*k*u| ≤ 4 := by
    calc
      |-2*k*u| = (2*|k|)*|u| := by norm_num [abs_mul]
      _ ≤ (2*2)*1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hu
          (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hquadratic : |-k*(x-u)^2| ≤ 2*((10 : ℝ)^8*q)^2 := by
    rw [abs_mul,abs_neg,abs_pow]
    exact mul_le_mul hk (pow_le_pow_left₀ (abs_nonneg _) hcoarse 2)
      (sq_nonneg _) (by norm_num)
  have hfourth := fourth_difference_bound hx hu
  have hquartic : |b*(x^4-u^4)| ≤ (7*q)*(10*((10 : ℝ)^8*q)) := by
    rw [abs_mul,abs_of_nonneg hb.1]
    exact mul_le_mul hb.2
      (hfourth.trans (mul_le_mul_of_nonneg_left hcoarse (by norm_num)))
      (abs_nonneg _) (by positivity)
  have herr := real_quartic_error (by omega : 17 ≤ p) hc hx
  change |realQuarticError c p x| ≤ 400*q^2 at herr
  have hid : responseRemainder c p (n+1) =
      (-2*k*u)*responseRemainder c p n-k*(x-u)^2+
        b*(x^4-u^4)+realQuarticError c p x := by
    change actualMap c p x-(1-k*u^2)-(-2*k*u*quarticResponse k n+u^4)*b =
      (-2*k*u)*(x-u-quarticResponse k n*b)-k*(x-u)^2+
        b*(x^4-u^4)+(actualMap c p x-(1-k*x^2+b*x^4))
    ring
  rw [hid]
  calc
    _ ≤ |(-2*k*u)*responseRemainder c p n-k*(x-u)^2+b*(x^4-u^4)|+
        |realQuarticError c p x| := abs_add _ _
    _ ≤ |(-2*k*u)*responseRemainder c p n-k*(x-u)^2|+
        |b*(x^4-u^4)|+|realQuarticError c p x| := add_le_add_right (abs_add _ _) _
    _ ≤ (|(-2*k*u)*responseRemainder c p n|+|-k*(x-u)^2|)+
        |b*(x^4-u^4)|+|realQuarticError c p x| := by
      have h : |(-2*k*u)*responseRemainder c p n-k*(x-u)^2| ≤
          |(-2*k*u)*responseRemainder c p n|+|-k*(x-u)^2| := by
        simpa only [neg_mul,abs_neg] using
          abs_sub ((-2*k*u)*responseRemainder c p n) (k*(x-u)^2)
      exact add_le_add_right (add_le_add_right h _) _
    _ ≤ (4*|responseRemainder c p n|+2*((10 : ℝ)^8*q)^2)+
        (7*q)*(10*((10 : ℝ)^8*q))+400*q^2 := by
      rw [abs_mul]
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)) hquadratic) hquartic) herr
    _ ≤ 4*|responseRemainder c p n|+(10 : ℝ)^17*q^2 := by
      nlinarith only [sq_nonneg q]

private theorem response_remainder_bound {p : ℕ} (hp : 100 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {n : ℕ} (hn : n ≤ 6) :
    |responseRemainder c p n| ≤ (10 : ℝ)^(n+20)*(scale p)^2 := by
  have hall : ∀ m : ℕ, m ≤ 6 →
      |responseRemainder c p m| ≤ (10 : ℝ)^(m+20)*(scale p)^2 := by
    intro m
    induction m with
    | zero =>
      intro hm
      simp only [responseRemainder,actualOrbit,criticalOrbit,quarticResponse,
        sub_self,zero_mul,sub_zero,abs_zero]
      positivity
    | succ m ih =>
      intro hm
      have he := response_step_error hp hc (show m ≤ 5 by omega)
      have hprev := ih (by omega)
      have hmin : (10 : ℝ)^20 ≤ (10 : ℝ)^(m+20) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hcoeff : 4*(10 : ℝ)^(m+20)+(10 : ℝ)^17 ≤
          10*(10 : ℝ)^(m+20) := by nlinarith only [hmin]
      have hprod := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (scale p))
      have hprevprod := mul_le_mul_of_nonneg_left hprev (by norm_num : (0 : ℝ) ≤ 4)
      rw [show m+1+20 = (m+20)+1 by omega,pow_succ]
      nlinarith only [he,hprevprod,hprod]
  exact hall n hn

private theorem actual_relation_zero {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    actualOrbit c p 0 6+actualOrbit c p 0 3 = 0 := by
  have hs := CriticalReturnRelationStability.actual_signed_relation_scale c p hc.2.1.ne'
  have h6 := actualOrbit_cast c (0 : ℝ) p 6
  have h3 := actualOrbit_cast c (0 : ℝ) p 3
  simp only [Complex.ofReal_zero] at h6 h3
  rw [←h6,←h3] at hs
  simp only [Complex.ofReal_re] at hs
  rw [hc.2.2.2.2.1] at hs
  exact (mul_eq_zero.mp hs.symm).resolve_left hc.2.1.ne'

/-- The complete actual signed relation has the first-order quartic
response of its own quadratic orbit, with an explicit second-order
budget. The two appearances of the quartic coefficient are identical. -/
theorem actual_quartic_relation_error {p : ℕ} (hp : 100 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    |relation (kappa p c)+normalizedQuartic c p*
      (quarticResponse (kappa p c) 6+quarticResponse (kappa p c) 3)| ≤
        (10 : ℝ)^27*(scale p)^2 := by
  have h6 := response_remainder_bound hp hc (show 6 ≤ 6 from le_rfl)
  have h3 := response_remainder_bound hp hc (show 3 ≤ 6 by norm_num)
  have hsum := (abs_add (responseRemainder c p 6) (responseRemainder c p 3)).trans
    (add_le_add h6 h3)
  have hid : responseRemainder c p 6+responseRemainder c p 3 =
      -(relation (kappa p c)+normalizedQuartic c p*
        (quarticResponse (kappa p c) 6+quarticResponse (kappa p c) 3)) := by
    have hz := actual_relation_zero hc
    dsimp only [responseRemainder,relation]
    nlinarith only [hz]
  rw [hid,abs_neg] at hsum
  nlinarith only [hsum,sq_nonneg (scale p)]

private theorem relation_secant_bounds {k k₀ : ℝ}
    (hk : k ∈ parameterInterval) (hk₀ : k₀ ∈ parameterInterval)
    (hzero : relation k₀ = 0) (hkk₀ : k₀ < k) :
    (6599/1000 : ℝ)*(k-k₀) < relation k ∧
      relation k < (6657/1000 : ℝ)*(k-k₀) := by
  have hdL (t : ℝ) : HasDerivAt (fun s => relation s-(6599/1000)*s)
      (criticalSlope t 6+criticalSlope t 3-(6599/1000)) t := by
    convert (relation_hasDerivAt t).sub
      ((hasDerivAt_id t).const_mul (6599/1000 : ℝ)) using 1
    all_goals first | rfl | simp
  have hdU (t : ℝ) : HasDerivAt (fun s => (6657/1000)*s-relation s)
      ((6657/1000)-(criticalSlope t 6+criticalSlope t 3)) t := by
    convert ((hasDerivAt_id t).const_mul (6657/1000 : ℝ)).sub
      (relation_hasDerivAt t) using 1
    all_goals first | rfl | simp
  have hcL : Continuous (fun t => relation t-(6599/1000)*t) :=
    continuous_iff_continuousAt.mpr (fun t => (hdL t).continuousAt)
  have hcU : Continuous (fun t => (6657/1000)*t-relation t) :=
    continuous_iff_continuousAt.mpr (fun t => (hdU t).continuousAt)
  have hmL : StrictMonoOn (fun t => relation t-(6599/1000)*t) parameterInterval := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hcL.continuousOn
      (fun t _ => (hdL t).hasDerivWithinAt)
    intro t ht
    have h := (interval_certificate (interior_subset ht)).2.1
    linarith only [h]
  have hmU : StrictMonoOn (fun t => (6657/1000)*t-relation t) parameterInterval := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hcU.continuousOn
      (fun t _ => (hdU t).hasDerivWithinAt)
    intro t ht
    have h := (interval_certificate (interior_subset ht)).2.2.1
    linarith only [h]
  have hL := hmL hk₀ hk hkk₀
  have hU := hmU hk₀ hk hkk₀
  change relation k₀-(6599/1000)*k₀ < relation k-(6599/1000)*k at hL
  change (6657/1000)*k₀-relation k₀ < (6657/1000)*k-relation k at hU
  rw [hzero] at hL hU
  constructor <;> linarith only [hL,hU]

/-- The actual signed-tip relation forces the quadratic and quartic
coefficients to move together. This narrow correlation is stronger than
independent bounds for their two errors. -/
theorem actual_quartic_parameter_correlation {p : ℕ} (hp : 100 ≤ p) {c k₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0) :
    (93/100 : ℝ)*normalizedQuartic c p < kappa p c-k₀ ∧
      kappa p c-k₀ < (95/100 : ℝ)*normalizedQuartic c p := by
  have hβ := normalized_quartic_scale_bounds (by omega : 17 ≤ p) hc
  have hq := scale_pos p
  have hβpos : 0 < normalizedQuartic c p := by linarith [hβ.1]
  have he := actual_quartic_relation_error hp hc
  have hsmall := scale_small_hundred hp
  have hprod := mul_le_mul_of_nonneg_right hsmall hq.le
  have herror : (10 : ℝ)^27*(scale p)^2 ≤ normalizedQuartic c p/1000 := by
    norm_num at hprod
    nlinarith only [hprod,hβ.1,hq]
  have he' := abs_le.mp (he.trans herror)
  have hresp := (interval_certificate hc.2.2.2.1).2.2.2
  have hlo := mul_le_mul_of_nonneg_left hresp.1 hβpos.le
  have hhi := mul_le_mul_of_nonneg_left hresp.2 hβpos.le
  have hrelation : (6210/1000 : ℝ)*normalizedQuartic c p ≤ relation (kappa p c) ∧
      relation (kappa p c) ≤ (6266/1000 : ℝ)*normalizedQuartic c p := by
    constructor <;> linarith only [he'.1,he'.2,hlo,hhi]
  have hgt := actual_coefficient_gt_limit (by omega : 17 ≤ p) hc hk₀ hroot
  have hsec := relation_secant_bounds hc.2.2.2.1 hk₀ hroot hgt
  constructor <;> nlinarith only [hrelation.1,hrelation.2,hsec.1,hsec.2,hβpos]

end
end ActualCrestQuarticRelation


