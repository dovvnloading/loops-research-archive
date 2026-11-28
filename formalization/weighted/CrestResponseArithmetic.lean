import CrestResponseConstants
import CrestResponseLinearization

/-!
# The signed response of the terminal collision equations

A rational finite-difference certificate for the five endpoint equations.
The parameter and quartic displacement remain correlated throughout the
calculation.  The theorem is later applied to the literal normalized return.
-/

namespace CrestResponseArithmetic

open CrestResponseConstants CrestResponseLinearization

noncomputable section

structure Coordinates where
  k : ℝ
  t : ℝ
  y : ℝ
  x : ℝ
  v : ℝ
  r : ℝ

def Centered (a : Coordinates) : Prop :=
  |a.k-kRef| ≤ 1/10^20 ∧ |a.t-tRef| ≤ 1/10^20 ∧
  |a.y-yRef| ≤ 1/10^20 ∧ |a.x-xRef| ≤ 1/10^20 ∧
  |a.v-vRef| ≤ 1/10^20 ∧ |a.r-rRef| ≤ 1/10^20

def DifferenceBounds (q : ℝ) (a o : Coordinates) : Prop :=
  |a.k-o.k| ≤ 10^10*q ∧ |a.t-o.t| ≤ 10^10*q ∧
  |a.y-o.y| ≤ 10^10*q ∧ |a.x-o.x| ≤ 10^10*q ∧
  |a.v-o.v| ≤ 10^10*q ∧ |a.r-o.r| ≤ 10^10*q

def ModelEquations (o : Coordinates) : Prop :=
  2-o.k*o.t^2 = 0 ∧
  1+o.k*o.y^2-o.t = 0 ∧
  1-o.k*(o.x^2-o.v^2) = 0 ∧
  2*o.k*o.x*o.v-o.y = 0 ∧
  (o.x-3/4)^2+o.v^2-o.r^2 = 0

def ActualEquations (q b : ℝ) (a : Coordinates) : Prop :=
  |2-a.k*a.t^2+b*a.t^4| ≤ 400*q^2 ∧
  |1+a.k*a.y^2+b*a.y^4-a.t| ≤ 400*q^2 ∧
  |1-a.k*(a.x^2-a.v^2)+b*(a.x^4-6*a.x^2*a.v^2+a.v^4)| ≤ 400*q^2 ∧
  |2*a.k*a.x*a.v-4*b*a.x*a.v*(a.x^2-a.v^2)-a.y| ≤ 400*q^2 ∧
  (a.x-3/4)^2+a.v^2-a.r^2 = 0

private def equation₁ {q : ℝ} (K B T : Jet q) : Jet q :=
  ((Jet.const q 2).sub (K.mul T.sq)).add (B.mul T.sq.sq)

private def equation₂ {q : ℝ} (K B T Y : Jet q) : Jet q :=
  (((Jet.const q 1).add (K.mul Y.sq)).add (B.mul Y.sq.sq)).sub T

private def equation₃ {q : ℝ} (K B X V : Jet q) : Jet q :=
  ((Jet.const q 1).sub (K.mul (X.sq.sub V.sq))).add
    (B.mul ((X.sq.sq.sub ((Jet.const q 6).mul (X.sq.mul V.sq))).add V.sq.sq))

private def equation₄ {q : ℝ} (K B Y X V : Jet q) : Jet q :=
  (((Jet.const q 2).mul ((K.mul X).mul V)).sub
    ((Jet.const q 4).mul (((B.mul X).mul V).mul (X.sq.sub V.sq)))).sub Y

private def equation₅ {q : ℝ} (X V R : Jet q) : Jet q :=
  (((X.sub (Jet.const q (3/4))).sq).add V.sq).sub R.sq

private def weight₅ : ℝ := -1/(2*rRef)
private def weight₃ : ℝ :=
  weight₅*(xRef*(xRef-3/4)-vRef^2)/(kRef*(xRef^2+vRef^2))
private def weight₄ : ℝ :=
  -weight₅*vRef*(2*xRef-3/4)/(kRef*(xRef^2+vRef^2))
private def weight₂ : ℝ := weight₄/(2*kRef*yRef)
private def weight₁ : ℝ := -weight₂/(2*kRef*tRef)

private def parameterCoefficient : ℝ :=
  -weight₁*tRef^2+weight₂*yRef^2-
    weight₃*(xRef^2-vRef^2)+weight₄*(2*xRef*vRef)

private def quarticCoefficient : ℝ :=
  weight₁*tRef^4+weight₂*yRef^4+
    weight₃*(xRef^4-6*xRef^2*vRef^2+vRef^4)-
      weight₄*(4*xRef*vRef*(xRef^2-vRef^2))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem weight_certificate :
    |weight₁| ≤ 10 ∧ |weight₂| ≤ 10 ∧ |weight₃| ≤ 10 ∧
    |weight₄| ≤ 10 ∧ |weight₅| ≤ 10 ∧
    2087/10000 ≤ parameterCoefficient ∧ parameterCoefficient ≤ 2088/10000 ∧
    -(222/1000) ≤ quarticCoefficient ∧ quarticCoefficient ≤ -(2219/10000) := by
  norm_num [weight₁,weight₂,weight₃,weight₄,weight₅,parameterCoefficient,
    quarticCoefficient,kRef,tRef,yRef,xRef,vRef,rRef]

private theorem weighted_error {q L w : ℝ} (hq : 0 ≤ q)
    (hw : |w| ≤ 10) (hL : |L| ≤ q/10^6) :
    |w*L| ≤ q/100000 := by
  rw [abs_mul]
  have h := mul_le_mul hw hL (abs_nonneg L) (by norm_num : (0 : ℝ) ≤ 10)
  nlinarith only [h]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- The positive sign survives the correlated displacement of the actual
parameter: the maximal radius moves between two and three percent of the
quartic coefficient.  All hypotheses below are finite scalar estimates. -/
theorem endpoint_response_certificate {q b : ℝ} {a o : Coordinates}
    (hq : 0 ≤ q) (hqsmall : q ≤ 1/10^60)
    (hb : 3*q < b ∧ b < 7*q)
    (hcorrelation : (93/100)*b < a.k-o.k ∧ a.k-o.k < (95/100)*b)
    (ha : Centered a) (ho : Centered o) (hd : DifferenceBounds q a o)
    (hmodel : ModelEquations o) (hactual : ActualEquations q b a) :
    b/50 < a.r-o.r ∧ a.r-o.r < 3*b/100 := by
  rcases ha with ⟨hak,hat,hay,hax,hav,har⟩
  rcases ho with ⟨hok,hot,hoy,hox,hov,hor⟩
  rcases hd with ⟨hdk,hdt,hdy,hdx,hdv,hdr⟩
  rcases hmodel with ⟨hm₁,hm₂,hm₃,hm₄,hm₅⟩
  rcases hactual with ⟨ha₁,ha₂,ha₃,ha₄,ha₅⟩
  have hb0 : 0 < b := by linarith only [hb.1,hq]
  have hbabs : |b| ≤ 7*q := by rw [abs_of_pos hb0]; exact hb.2.le
  have hbsmall : |b| ≤ 1/10^20 := by
    linarith only [hbabs,hqsmall]
  let K := Jet.coordinate q a.k o.k kRef (1/10^20) (10^10) hak hok hdk
  let T := Jet.coordinate q a.t o.t tRef (1/10^20) (10^10) hat hot hdt
  let Y := Jet.coordinate q a.y o.y yRef (1/10^20) (10^10) hay hoy hdy
  let X := Jet.coordinate q a.x o.x xRef (1/10^20) (10^10) hax hox hdx
  let V := Jet.coordinate q a.v o.v vRef (1/10^20) (10^10) hav hov hdv
  let R := Jet.coordinate q a.r o.r rRef (1/10^20) (10^10) har hor hdr
  let B := Jet.coordinate q b 0 0 (1/10^20) 7 (by simpa using hbsmall)
    (by norm_num) (by simpa using hbabs)
  let E₁ := equation₁ K B T
  let E₂ := equation₂ K B T Y
  let E₃ := equation₃ K B X V
  let E₄ := equation₄ K B Y X V
  let E₅ := equation₅ X V R
  have hsmall : 400*q^2 ≤ (1/10^10)*q := by
    have h := mul_le_mul_of_nonneg_right hqsmall hq
    nlinarith only [h,hq]
  have hzero₁ : E₁.base = 0 := by
    dsimp [E₁,equation₁,K,B,T,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,Jet.sq,Jet.const]
    nlinarith only [hm₁]
  have hzero₂ : E₂.base = 0 := by
    dsimp [E₂,equation₂,K,B,T,Y,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,Jet.sq,Jet.const]
    nlinarith only [hm₂]
  have hzero₃ : E₃.base = 0 := by
    dsimp [E₃,equation₃,K,B,X,V,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,Jet.sq,Jet.const]
    nlinarith only [hm₃]
  have hzero₄ : E₄.base = 0 := by
    dsimp [E₄,equation₄,K,B,Y,X,V,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,Jet.sq,Jet.const]
    nlinarith only [hm₄]
  have hzero₅ : E₅.base = 0 := by
    dsimp [E₅,equation₅,X,V,R,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,Jet.sq,Jet.const]
    nlinarith only [hm₅]
  have hvalue₁ : |E₁.value| ≤ (1/10^10)*q := by
    apply le_trans _ hsmall
    convert ha₁ using 1 <;>
      dsimp [E₁,equation₁,K,B,T,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,Jet.sq,Jet.const]
      <;> congr 1 <;> ring
  have hvalue₂ : |E₂.value| ≤ (1/10^10)*q := by
    apply le_trans _ hsmall
    convert ha₂ using 1 <;>
      dsimp [E₂,equation₂,K,B,T,Y,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,Jet.sq,Jet.const]
      <;> congr 1 <;> ring
  have hvalue₃ : |E₃.value| ≤ (1/10^10)*q := by
    apply le_trans _ hsmall
    convert ha₃ using 1 <;>
      dsimp [E₃,equation₃,K,B,X,V,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,Jet.sq,Jet.const]
      <;> congr 1 <;> ring
  have hvalue₄ : |E₄.value| ≤ (1/10^10)*q := by
    apply le_trans _ hsmall
    convert ha₄ using 1 <;>
      dsimp [E₄,equation₄,K,B,Y,X,V,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,Jet.sq,Jet.const]
      <;> congr 1 <;> ring
  have hvalue₅ : |E₅.value| ≤ (1/10^10)*q := by
    have hv : E₅.value = 0 := by
      dsimp [E₅,equation₅,X,V,R,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,Jet.sq,Jet.const]
      nlinarith only [ha₅]
    rw [hv,abs_zero]
    positivity
  have he₁ : 1/10^10+E₁.error ≤ (1/10^6 : ℝ) := by
    norm_num [E₁,equation₁,K,B,T,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,
      Jet.sq,Jet.const,kRef,tRef]
  have he₂ : 1/10^10+E₂.error ≤ (1/10^6 : ℝ) := by
    norm_num [E₂,equation₂,K,B,T,Y,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,
      Jet.sq,Jet.const,kRef,tRef,yRef]
  have he₃ : 1/10^10+E₃.error ≤ (1/10^6 : ℝ) := by
    norm_num [E₃,equation₃,K,B,X,V,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,
      Jet.sq,Jet.const,kRef,xRef,vRef]
  have he₄ : 1/10^10+E₄.error ≤ (1/10^6 : ℝ) := by
    norm_num [E₄,equation₄,K,B,Y,X,V,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,
      Jet.sq,Jet.const,kRef,yRef,xRef,vRef]
  have he₅ : 1/10^10+E₅.error ≤ (1/10^6 : ℝ) := by
    norm_num [E₅,equation₅,X,V,R,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,
      Jet.sq,Jet.const,xRef,vRef,rRef]
  have hL₁ : |E₁.linear| ≤ q/10^6 := by
    have h := (E₁.linear_bound hzero₁ hvalue₁).trans (mul_le_mul_of_nonneg_right he₁ hq)
    nlinarith only [h]
  have hL₂ : |E₂.linear| ≤ q/10^6 := by
    have h := (E₂.linear_bound hzero₂ hvalue₂).trans (mul_le_mul_of_nonneg_right he₂ hq)
    nlinarith only [h]
  have hL₃ : |E₃.linear| ≤ q/10^6 := by
    have h := (E₃.linear_bound hzero₃ hvalue₃).trans (mul_le_mul_of_nonneg_right he₃ hq)
    nlinarith only [h]
  have hL₄ : |E₄.linear| ≤ q/10^6 := by
    have h := (E₄.linear_bound hzero₄ hvalue₄).trans (mul_le_mul_of_nonneg_right he₄ hq)
    nlinarith only [h]
  have hL₅ : |E₅.linear| ≤ q/10^6 := by
    have h := (E₅.linear_bound hzero₅ hvalue₅).trans (mul_le_mul_of_nonneg_right he₅ hq)
    nlinarith only [h]
  obtain ⟨hw₁,hw₂,hw₃,hw₄,hw₅,hPkL,hPkU,hPbL,hPbU⟩ := weight_certificate
  have hW₁ := weighted_error hq hw₁ hL₁
  have hW₂ := weighted_error hq hw₂ hL₂
  have hW₃ := weighted_error hq hw₃ hL₃
  have hW₄ := weighted_error hq hw₄ hL₄
  have hW₅ := weighted_error hq hw₅ hL₅
  have hid : weight₁*E₁.linear+weight₂*E₂.linear+weight₃*E₃.linear+
      weight₄*E₄.linear+weight₅*E₅.linear =
        a.r-o.r+parameterCoefficient*(a.k-o.k)+quarticCoefficient*b := by
    norm_num [E₁,E₂,E₃,E₄,E₅,equation₁,equation₂,equation₃,equation₄,equation₅,
      K,B,T,Y,X,V,R,Jet.coordinate,Jet.add,Jet.sub,Jet.neg,Jet.mul,Jet.sq,Jet.const,
      parameterCoefficient,quarticCoefficient,weight₁,weight₂,weight₃,weight₄,weight₅,
      kRef,tRef,yRef,xRef,vRef,rRef]
    <;> ring
  have hsum : |a.r-o.r+parameterCoefficient*(a.k-o.k)+quarticCoefficient*b| ≤
      q/20000 := by
    rw [← hid]
    calc
      _ ≤ (|(weight₁*E₁.linear+weight₂*E₂.linear)+weight₃*E₃.linear|+
          |weight₄*E₄.linear|)+|weight₅*E₅.linear| :=
        (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
      _ ≤ ((|weight₁*E₁.linear+weight₂*E₂.linear|+|weight₃*E₃.linear|)+
          |weight₄*E₄.linear|)+|weight₅*E₅.linear| := by
        exact add_le_add_right (add_le_add_right (abs_add_le _ _) _) _
      _ ≤ (((|weight₁*E₁.linear|+|weight₂*E₂.linear|)+|weight₃*E₃.linear|)+
          |weight₄*E₄.linear|)+|weight₅*E₅.linear| := by
        exact add_le_add_right (add_le_add_right (add_le_add_right (abs_add_le _ _) _) _) _
      _ ≤ q/20000 := by linarith only [hW₁,hW₂,hW₃,hW₄,hW₅]
  have hdelta0 : 0 ≤ a.k-o.k := by nlinarith only [hcorrelation.1,hb0]
  have hPk0 : 0 ≤ parameterCoefficient := by linarith only [hPkL]
  have hkProdL := mul_le_mul hPkL hcorrelation.1.le
    (show 0 ≤ (93/100 : ℝ)*b by positivity) hPk0
  have hkProdU := mul_le_mul hPkU hcorrelation.2.le hdelta0 (by norm_num : (0 : ℝ) ≤ 2088/10000)
  have hbProdL := mul_le_mul_of_nonneg_right hPbL hb0.le
  have hbProdU := mul_le_mul_of_nonneg_right hPbU hb0.le
  constructor
  · nlinarith only [(abs_le.mp hsum).1,hkProdU,hbProdU,hb.1,hq]
  · nlinarith only [(abs_le.mp hsum).2,hkProdL,hbProdL,hb.1,hq]

end
end CrestResponseArithmetic
