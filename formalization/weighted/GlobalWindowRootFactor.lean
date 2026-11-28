import GlobalWindowSecant
import GlobalSignedModelFactor

/-!
# A center-free equation for actual signed roots on the global window

The exact even secants factor the signed sixth-versus-third relation.
The nonzero third return is canceled algebraically before estimating any
error.  The resulting scalar is uniformly close to the factored model
on the entire invariant real return interval.
-/

namespace GlobalWindowRootFactor

open Set Function NearTwoShooting LimitingCrestQuadraticReturn
open GlobalRestrictiveWindow GlobalWindowSignedChart GlobalWindowSecant
open LoopsLimitingCrestParameter GlobalSignedModelFactor

noncomputable section

def returnOrbit (c : ℝ) (p n : ℕ) : ℝ := (realReturn c p)^[n] 0

theorem returnOrbit_succ (c : ℝ) (p n : ℕ) :
    returnOrbit c p (n+1)=realReturn c p (returnOrbit c p n) :=
  Function.iterate_succ_apply' (realReturn c p) n 0

def actualFactor (c : ℝ) (p : ℕ) : ℝ :=
  realSecant c p (returnOrbit c p 3) 0 *
    realSecant c p (returnOrbit c p 4) 1 *
    realSecant c p (returnOrbit c p 5) (returnOrbit c p 2) *
    (-returnOrbit c p 3)*(1+returnOrbit c p 4)*
    (-(returnOrbit c p 2+returnOrbit c p 5))

theorem returnOrbit_eq {c : ℝ} {p : ℕ} (hd : criticalValue c p≠0) (n : ℕ) :
    returnOrbit c p n=criticalValue c (n*p)/criticalValue c p :=
  realReturn_iterate_zero hd n

theorem returnOrbit_mem {c : ℝ} {p : ℕ} (h : PositiveRestrictiveReturn c p) (n : ℕ) :
    returnOrbit c p n∈Icc (-1 : ℝ) 1 :=
  (realReturn_mapsTo h).iterate n (by norm_num)

/-- The strict third-return sign removes the center factor exactly.
There is no division of an approximation error by a small return. -/
theorem actualFactor_eq_two {c : ℝ} {p : ℕ} (hp : 17≤p)
    (h : PositiveRestrictiveReturn c p)
    (hthird : criticalValue c (3*p)<0)
    (hroot : criticalValue c (6*p)+criticalValue c (3*p)=0) :
    actualFactor c p=2 := by
  let a := returnOrbit c p 2
  let v := returnOrbit c p 3
  let w := returnOrbit c p 4
  let b := returnOrbit c p 5
  let r := returnOrbit c p 6
  let A := realSecant c p v 0
  let B := realSecant c p w 1
  let C := realSecant c p b a
  have hv : v<0 := by
    dsimp [v]
    rw [returnOrbit_eq h.return_pos.ne']
    exact div_neg_of_neg_of_pos hthird h.return_pos
  have hr : r+v=0 := by
    dsimp [r,v]
    rw [returnOrbit_eq h.return_pos.ne',returnOrbit_eq h.return_pos.ne',
      ← add_div,hroot,zero_div]
  have hF1 : realReturn c p 1=a := by
    change realReturn c p 1=realReturn c p (realReturn c p 0)
    rw [realReturn_zero h.return_pos.ne']
  have h1 : w-1= -A*v^2 := by
    have he := realReturn_difference (by omega : 0<p) h.return_pos.ne' v 0
    rw [realReturn_zero h.return_pos.ne'] at he
    change w-1= -A*(v^2-0^2) at he
    simpa only [zero_pow (by decide : 2≠0),sub_zero] using he
  have h2 : b-a= -B*(w^2-1) := by
    have he := realReturn_difference (by omega : 0<p) h.return_pos.ne' w 1
    rw [hF1] at he
    change b-a= -B*(w^2-1^2) at he
    simpa only [one_pow] using he
  have h3 : r-v= -C*(b^2-a^2) :=
    realReturn_difference (by omega : 0<p) h.return_pos.ne' b a
  have h45 : b-a=A*B*v^2*(1+w) := by
    calc
      _= -B*(w^2-1) := h2
      _= (-B*(w+1))*(w-1) := by ring
      _= (-B*(w+1))*(-A*v^2) := by rw [h1]
      _= _ := by ring
  have h63 : r-v= -A*B*C*v^2*(1+w)*(a+b) := by
    calc
      _= -C*(b^2-a^2) := h3
      _= (-C*(b+a))*(b-a) := by ring
      _= (-C*(b+a))*(A*B*v^2*(1+w)) := by rw [h45]
      _= _ := by ring
  have hmul : (A*B*C*(-v)*(1+w)*(-(a+b)))*v=2*v := by
    calc
      _= -(r-v) := by rw [h63]; ring
      _=2*v := by linarith only [hr]
  exact mul_right_cancel₀ hv.ne hmul

private theorem model_mem {k : ℝ} (hk : k∈Icc (0 : ℝ) 2) (n : ℕ) :
    criticalOrbit k n∈Icc (-1 : ℝ) 1 := by
  induction n with
  | zero => norm_num [criticalOrbit]
  | succ n ih =>
    have hs : (criticalOrbit k n)^2≤1 := by
      simpa only [one_pow] using sq_le_sq' ih.1 ih.2
    have hprod := mul_le_mul_of_nonneg_left hs hk.1
    have hnonneg := mul_nonneg hk.1 (sq_nonneg (criticalOrbit k n))
    change -1≤1-k*(criticalOrbit k n)^2 ∧ 1-k*(criticalOrbit k n)^2≤1
    constructor <;> nlinarith only [hprod,hnonneg,hk.2]

private theorem model_lipschitz {k x y : ℝ}
    (hk : k∈Icc (0 : ℝ) 2)
    (hx : x∈Icc (-1 : ℝ) 1) (hy : y∈Icc (-1 : ℝ) 1) :
    |Q k x-Q k y|≤4*|x-y| := by
  have hsum : |x+y|≤2 := by apply abs_le.mpr; constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
  have hid : Q k x-Q k y= -k*(x-y)*(x+y) := by unfold Q; ring
  rw [hid,abs_mul,abs_mul,abs_neg,abs_of_nonneg hk.1]
  have hmul := mul_le_mul hk.2 hsum (abs_nonneg (x+y)) (by norm_num : (0 : ℝ)≤2)
  have hm := mul_le_mul_of_nonneg_right hmul (abs_nonneg (x-y))
  nlinarith only [hm]

private theorem orbit_error_bounds {c : ℝ} {p : ℕ} (hp : 17≤p)
    (h : PositiveRestrictiveReturn c p) (hk : kappa p c∈Icc (0 : ℝ) 2) :
    |returnOrbit c p 2-criticalOrbit (kappa p c) 2|≤22*scale p ∧
    |returnOrbit c p 3-criticalOrbit (kappa p c) 3|≤110*scale p ∧
    |returnOrbit c p 4-criticalOrbit (kappa p c) 4|≤462*scale p ∧
    |returnOrbit c p 5-criticalOrbit (kappa p c) 5|≤1870*scale p := by
  have step (n : ℕ) :
      |returnOrbit c p (n+1)-criticalOrbit (kappa p c) (n+1)|≤
        22*scale p+4*|returnOrbit c p n-criticalOrbit (kappa p c) n| := by
    rw [returnOrbit_succ,criticalOrbit]
    have herr := realReturn_error hp h (returnOrbit_mem h n)
    have hlip := model_lipschitz hk (returnOrbit_mem h n) (model_mem hk n)
    have htri := abs_sub_le (realReturn c p (returnOrbit c p n))
      (Q (kappa p c) (returnOrbit c p n))
      (Q (kappa p c) (criticalOrbit (kappa p c) n))
    change |realReturn c p (returnOrbit c p n)-Q (kappa p c) (returnOrbit c p n)|≤_ at herr
    change |realReturn c p (returnOrbit c p n)-Q (kappa p c) (criticalOrbit (kappa p c) n)|≤_
    linarith only [herr,hlip,htri]
  have h1 : returnOrbit c p 1=criticalOrbit (kappa p c) 1 := by
    change realReturn c p 0=Q (kappa p c) 0
    rw [realReturn_zero h.return_pos.ne']
    simp [Q]
  have h2 := step 1
  rw [h1,sub_self,abs_zero] at h2
  have h3 := step 2
  have h4 := step 3
  have h5 := step 4
  refine ⟨by linarith only [h2],by linarith only [h2,h3],
    by linarith only [h2,h3,h4],by linarith only [h2,h3,h4,h5]⟩

private theorem product_error {a b c d E F B C : ℝ}
    (he : |a-c|≤E) (hf : |b-d|≤F) (hb : |b|≤B) (hc : |c|≤C)
    (hE : 0≤E) (hF : 0≤F) :
    |a*b-c*d|≤B*E+C*F := by
  have hid : a*b-c*d=(a-c)*b+c*(b-d) := by ring
  rw [hid]
  calc
    _≤|(a-c)*b| + |c*(b-d)| := abs_add_le _ _
    _=|b| * |a-c| + |c| * |b-d| := by rw [abs_mul,abs_mul]; ring
    _≤B*E+C*F := add_le_add
      (mul_le_mul hb he (abs_nonneg _) ((abs_nonneg b).trans hb))
      (mul_le_mul hc hf (abs_nonneg _) ((abs_nonneg c).trans hc))

private theorem abs_product_bound {a b A B : ℝ} (ha : |a|≤A) (hb : |b|≤B) :
    |a*b|≤A*B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg a).trans ha)

/-- The canceled scalar relation is uniformly close to its model
throughout the global physical class in the coefficient chart. -/
theorem actualFactor_model_error {c : ℝ} {p : ℕ} (hp : 17≤p)
    (h : PositiveRestrictiveReturn c p) (hk : kappa p c∈Icc (0 : ℝ) 2) :
    |actualFactor c p-modelFactor (kappa p c)|≤50000*scale p := by
  let k := kappa p c
  let v := returnOrbit c p 3
  let w := returnOrbit c p 4
  let a := returnOrbit c p 2
  let b := returnOrbit c p 5
  let A := realSecant c p v 0
  let B := realSecant c p w 1
  let C := realSecant c p b a
  let vm := criticalOrbit k 3
  let wm := criticalOrbit k 4
  let am := criticalOrbit k 2
  let bm := criticalOrbit k 5
  have hq0 := (scale_pos p).le
  have hq := scale_small hp
  have hkabs : |k|≤2 := by rw [abs_of_nonneg hk.1]; exact hk.2
  have hv : |v|≤1 := abs_le.mpr (returnOrbit_mem h 3)
  have hw : |w|≤1 := abs_le.mpr (returnOrbit_mem h 4)
  have ha : |a|≤1 := abs_le.mpr (returnOrbit_mem h 2)
  have hb : |b|≤1 := abs_le.mpr (returnOrbit_mem h 5)
  have hvm : |vm|≤1 := abs_le.mpr (model_mem hk 3)
  have hwm : |wm|≤1 := abs_le.mpr (model_mem hk 4)
  have haerr := realSecant_error hp h (returnOrbit_mem h 3) (show (0 : ℝ)∈Icc (-1 : ℝ) 1 by norm_num)
  have hberr := realSecant_error hp h (returnOrbit_mem h 4) (show (1 : ℝ)∈Icc (-1 : ℝ) 1 by norm_num)
  have hcerr := realSecant_error hp h (returnOrbit_mem h 5) (returnOrbit_mem h 2)
  change |A-k|≤43*scale p at haerr
  change |B-k|≤43*scale p at hberr
  change |C-k|≤43*scale p at hcerr
  have hAb : |A|≤201/100 := by
    have ht := abs_sub_le A k 0
    simp only [sub_zero] at ht
    linarith
  have hBb : |B|≤201/100 := by
    have ht := abs_sub_le B k 0
    simp only [sub_zero] at ht
    linarith
  have hCb : |C|≤201/100 := by
    have ht := abs_sub_le C k 0
    simp only [sub_zero] at ht
    linarith
  have hABerr : |A*B-k*k|≤173*scale p := by
    have he := product_error haerr hberr hBb hkabs
      (by positivity : 0≤43*scale p) (by positivity : 0≤43*scale p)
    nlinarith only [he,hq0]
  have hkk : |k*k|≤4 := by
    have hm := abs_product_bound hkabs hkabs
    norm_num at hm
    rw [abs_of_nonneg (mul_nonneg hk.1 hk.1)]
    exact hm
  have hABCerr : |A*B*C-k^3|≤561*scale p := by
    have he := product_error hABerr hcerr hCb hkk
      (by positivity : 0≤173*scale p) (by positivity : 0≤43*scale p)
    have hnorm : k*k*k=k^3 := by ring
    rw [hnorm] at he
    nlinarith only [he,hq0]
  have hk3 : |k^3|≤8 := by
    have hm := abs_product_bound hkk hkabs
    rw [show k*k*k=k^3 by ring] at hm
    norm_num at hm
    simpa only [abs_pow] using hm
  obtain ⟨hae,hve,hwe,hbe⟩ := orbit_error_bounds hp h hk
  change |a-am|≤22*scale p at hae
  change |v-vm|≤110*scale p at hve
  change |w-wm|≤462*scale p at hwe
  change |b-bm|≤1870*scale p at hbe
  have hve' : |(-v)-(-vm)|≤110*scale p := by
    rw [show (-v)-(-vm)= -(v-vm) by ring,abs_neg]
    exact hve
  have hwe' : |(1+w)-(1+wm)|≤462*scale p := by
    rw [show (1+w)-(1+wm)=w-wm by ring]
    exact hwe
  have hsum : |(-(a+b))-(-(am+bm))|≤1892*scale p := by
    have ht := abs_add_le (a-am) (b-bm)
    have hid : (a-am)+(b-bm)=(a+b)-(am+bm) := by ring
    rw [hid] at ht
    have hneg : (-(a+b))-(-(am+bm))= -((a+b)-(am+bm)) := by ring
    rw [hneg,abs_neg]
    linarith only [ht,hae,hbe]
  have hvb : |-v|≤1 := by simpa only [abs_neg] using hv
  have hvmb : |-vm|≤1 := by simpa only [abs_neg] using hvm
  have hwplus : |1+w|≤2 := by
    have ht := abs_add_le (1 : ℝ) w
    norm_num only [abs_one] at ht
    linarith
  have hwmplus : |1+wm|≤2 := by
    have ht := abs_add_le (1 : ℝ) wm
    norm_num only [abs_one] at ht
    linarith
  have hsumb : |-(a+b)|≤2 := by rw [abs_neg]; linarith [abs_add_le a b]
  have hkv : |k^3*(-vm)|≤8 := by simpa only [mul_one] using abs_product_bound hk3 hvmb
  have hkvw : |k^3*(-vm)*(1+wm)|≤16 := by
    have hm := abs_product_bound hkv hwmplus
    norm_num at hm
    simpa only [abs_mul,abs_pow,abs_neg] using hm
  have hfirst : |A*B*C*(-v)-k^3*(-vm)|≤1441*scale p := by
    have he := product_error hABCerr hve' hvb hk3
      (by positivity : 0≤561*scale p) (by positivity : 0≤110*scale p)
    nlinarith only [he]
  have hsecond : |A*B*C*(-v)*(1+w)-k^3*(-vm)*(1+wm)|≤6578*scale p := by
    have he := product_error hfirst hwe' hwplus hkv
      (by positivity : 0≤1441*scale p) (by positivity : 0≤462*scale p)
    nlinarith only [he]
  have hthird := product_error hsecond hsum hsumb hkvw
    (by positivity : 0≤6578*scale p) (by positivity : 0≤1892*scale p)
  change |A*B*C*(-v)*(1+w)*(-(a+b))-k^3*(-vm)*(1+wm)*(-(am+bm))|≤50000*scale p
  nlinarith only [hthird,hq0]

theorem signed_root_model_error {c : ℝ} {p : ℕ} (hp : 17≤p)
    (h : PositiveRestrictiveReturn c p) (hk : kappa p c∈Icc (0 : ℝ) 2)
    (hthird : criticalValue c (3*p)<0)
    (hroot : criticalValue c (6*p)+criticalValue c (3*p)=0) :
    |modelFactor (kappa p c)-2|≤50000*scale p := by
  have he := actualFactor_model_error hp h hk
  rw [actualFactor_eq_two hp h hthird hroot,abs_sub_comm] at he
  exact he

end
end GlobalWindowRootFactor
