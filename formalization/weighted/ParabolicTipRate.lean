import ParabolicChannel
import Mathlib.Analysis.Real.Sqrt

/-! The time spent traversing the period-three parabolic channel is of order
t⁻¹ᐟ².  The estimates use the true iterates up to the prescribed flight time. -/
namespace LoopsParabolic
open Set Function
noncomputable section

private theorem channel_root : ∃ a ∈ Icc (1/20:ℝ) (3/50), cubic a = 0 := by
  have hc : Continuous cubic := by unfold cubic; fun_prop
  exact intermediate_value_Icc (by norm_num) hc.continuousOn
    (show (0:ℝ) ∈ Icc (cubic (1/20)) (cubic (3/50)) by constructor <;> norm_num [cubic])

/-- Quantitative normal-form bounds around the actual fixed point of H₀. -/
theorem channel_quadratic_step {t y a : ℝ} (ht : t ∈ Icc 0 (1/100:ℝ))
    (hy : y ∈ Icc 0 cap) (ha : a ∈ Icc (1/20:ℝ) (3/50)) (root : cubic a=0) :
    t/2+(y-a)^2 ≤ H t y-y ∧ H t y-y ≤ 10*t+20*(y-a)^2 := by
  obtain ⟨ty,ty'⟩ := ht
  obtain ⟨ay,ay'⟩ := ha
  obtain ⟨yy,yy'⟩ := hy
  unfold cap at yy'
  have ys := sq_le_sq' (show -(2/5:ℝ) ≤ y by linarith) yy'
  have asq := sq_le_sq' (show -(3/50:ℝ) ≤ a by linarith) ay'
  have ya := mul_le_mul yy' ay' (by linarith) (by norm_num)
  let M := 18+4*(y+a)-8*(y^2+y*a+a^2)
  have ml : 14 ≤ M := by dsimp [M]; linarith only [ys,asq,ya,yy,ay]
  have mh : M ≤ 22 := by dsimp [M]; linarith only [yy',ay',sq_nonneg y,sq_nonneg a,mul_nonneg yy (show 0≤a by linarith)]
  have cfac : cubic y=(y-a)*M := by
    calc cubic y = cubic y-cubic a := by rw [root,sub_zero]
         _ = _ := by dsimp [cubic,M]; ring
  let W := 7-4*y^2-4*y
  have wl : 4 ≤ W := by dsimp [W]; linarith only [ys,yy']
  have wh : W ≤ 7 := by dsimp [W]; linarith only [yy,sq_nonneg y]
  have ml2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤14) ml 2
  have mh2 := pow_le_pow_left₀ (by linarith : 0≤M) mh 2
  have l := mul_le_mul wl ml2 (by norm_num) (by linarith)
  have h := mul_le_mul wh mh2 (sq_nonneg M) (by norm_num)
  have l' := mul_le_mul_of_nonneg_right l (sq_nonneg (y-a))
  have h' := mul_le_mul_of_nonneg_right h (sq_nonneg (y-a))
  have iden : H 0 y-y = (W*M^2)*(y-a)^2/256 := by
    rw [parabolic_identity,cfac]; dsimp [W]; ring
  let A := 7/4-y^2
  let B := A^2-7/4
  let C := (A-t)^2-(7/4-t)
  have al : 3/2 ≤ A-t := by dsimp [A]; linarith only [ys,ty']
  have al' : 3/2 ≤ A := by linarith only [al,ty]
  have ah : A ≤ 7/4 := by dsimp [A]; linarith only [sq_nonneg y]
  have ah' : A-t ≤ 7/4 := by linarith only [ah,ty]
  have bl : 1/2 ≤ B := by dsimp [B]; linarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/2) al' 2]
  have cl : 1/2 ≤ C := by dsimp [C]; linarith only [ty,pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/2) al 2]
  have bh : B ≤ 3/2 := by dsimp [B]; linarith only [pow_le_pow_left₀ (by linarith : 0≤A) ah 2]
  have ch : C ≤ 3/2 := by dsimp [C]; linarith only [ty',pow_le_pow_left₀ (by linarith : 0≤A-t) ah' 2]
  have ll := mul_le_mul (show (3:ℝ)/2 ≤ 2*A-1-t by linarith)
    (show (1:ℝ)≤B+C by linarith) (by norm_num) (by linarith)
  have hh := mul_le_mul (show 2*A-1-t≤(5:ℝ)/2 by linarith)
    (show B+C≤(3:ℝ) by linarith) (by linarith) (by norm_num)
  have diff : H t y-H 0 y=t*((2*A-1-t)*(B+C)-1) := by dsimp [H,A,B,C]; ring
  have dl := mul_le_mul_of_nonneg_left (show (1:ℝ)/2 ≤ (2*A-1-t)*(B+C)-1 by linarith) ty
  have dh := mul_le_mul_of_nonneg_left (show (2*A-1-t)*(B+C)-1 ≤ 10 by linarith) ty
  constructor <;> linarith only [l',h',sq_nonneg (y-a),iden,diff,dl,dh]

private def ramp (a b y : ℝ) := min (2*b) (max 0 (y-a+b))

/-- A clipped coordinate gains at most 15t in one physical step, even if
the step starts outside the bottleneck. -/
private theorem ramp_step {a b t y : ℝ} (hb : 0 < b) (hb' : b ≤ 1/20)
    (bt : b^2≤t/4) (ht : t ∈ Icc 0 (1/100:ℝ)) (hy : y ∈ Icc 0 cap)
    (ha : a ∈ Icc (1/20:ℝ) (3/50)) (root : cubic a=0) :
    ramp a b (H t y) ≤ ramp a b y + 15*t := by
  have edge : a-b ∈ Icc 0 cap :=
    ⟨by linarith [ha.1],by unfold cap; linarith [ha.2]⟩
  by_cases below : y ≤ a-b
  · have cmp := channel_mono ht hy edge below
    have up := (channel_quadratic_step ht edge ha root).2
    have zero : ramp a b y=0 := by
      unfold ramp; rw [max_eq_left (by linarith),min_eq_right (by linarith)]
    rw [zero]
    apply (min_le_right _ _).trans
    exact max_le (by linarith [ht.1]) (by nlinarith)
  by_cases above : a+b ≤ y
  · have top : ramp a b y=2*b := by
      unfold ramp; rw [max_eq_right (by linarith),min_eq_left (by linarith)]
    rw [top]
    exact (min_le_left _ _).trans (by linarith [ht.1])
  have middle : ramp a b y=y-a+b := by
    unfold ramp; rw [max_eq_right (by linarith),min_eq_right (by linarith)]
  have sym := sq_le_sq' (by linarith : -b ≤ y-a) (by linarith : y-a≤b)
  have up := (channel_quadratic_step ht hy ha root).2
  rw [middle]
  apply (min_le_right _ _).trans
  exact max_le (by linarith [ht.1]) (by linarith)

private def coord (b x : ℝ) := x/(b+|x|)

private theorem coord_range {b x : ℝ} (hb : 0<b) : coord b x ∈ Icc (-1:ℝ) 1 := by
  have h : 0 < b+|x| := by linarith [abs_nonneg x]
  exact ⟨(le_div_iff₀ h).mpr (by linarith [neg_abs_le x]),
    (div_le_iff₀ h).mpr (by linarith [le_abs_self x])⟩

/-- The compact coordinate gains at least sqrt(t)/5 in every channel step. -/
private theorem coord_step {b x y : ℝ} (hb : 0<b) (hx : b+|x|≤1)
    (hd : b^2/2+x^2≤y-x) : b/5 ≤ coord b y-coord b x := by
  have dpos : 0 ≤ y-x := by nlinarith [sq_nonneg b,sq_nonneg x]
  have bx : 0 < b+|x| := by linarith [abs_nonneg x]
  have by' : 0 < b+|y| := by linarith [abs_nonneg y]
  have ab : |y| ≤ |x|+(y-x) := by
    have h := abs_add_le x (y-x)
    rw [abs_of_nonneg dpos,show x+(y-x)=y by ring] at h
    exact h
  have e := mul_le_mul_of_nonneg_left (show b+|y| ≤ (b+|x|)+(y-x) by linarith) bx.le
  have f := mul_le_mul_of_nonneg_right hx dpos
  have afsq := sq_abs x
  have denom : (b+|x|)*(b+|y|) ≤ 5*(y-x) := by
    nlinarith only [e,f,hd,afsq,sq_nonneg (b-|x|),sq_nonneg x]
  have cross : 0 ≤ y*|x|-x*|y| := by
    by_cases x0 : 0 ≤ x
    · rw [abs_of_nonneg x0,abs_of_nonneg (by linarith : 0≤y)]; ring_nf; exact le_rfl
    by_cases y0 : y ≤ 0
    · rw [abs_of_nonpos (le_of_not_ge x0),abs_of_nonpos y0]; ring_nf; exact le_rfl
    · rw [abs_of_nonpos (le_of_not_ge x0),abs_of_nonneg (le_of_not_ge y0)]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge x0) (le_of_not_ge y0)]
  have ds : (coord b y-coord b x)*((b+|x|)*(b+|y|)) =
      y*(b+|x|)-x*(b+|y|) := by
    unfold coord
    field_simp [bx.ne',by'.ne']
  apply (mul_le_mul_iff_left₀ (mul_pos bx by')).mp
  rw [ds]
  nlinarith only [mul_le_mul_of_nonneg_left denom hb.le,cross]

/-- Two-sided inverse-square passage law, with explicit constants. The
hypotheses only specify that the *true* reflected orbit stays in the
corridor through time k and has reached 7/20 there. -/
theorem channel_inverse_square {t : ℝ} {k : ℕ} (ht : 0<t) (ht' : t≤1/100)
    (stay : ∀ j≤k, (H t)^[j] 0 ∈ Icc 0 cap)
    (reached : 7/20 ≤ (H t)^[k] 0) :
    1/225 ≤ (k:ℝ)^2*t ∧ (k:ℝ)^2*t ≤ 100 := by
  obtain ⟨a,ha,root⟩ := channel_root
  let b := Real.sqrt t
  have hb : 0<b := Real.sqrt_pos.mpr ht
  have bt : b^2=t := Real.sq_sqrt ht.le
  have hb' : b≤1/10 := by nlinarith [sq_nonneg (b-1/10)]
  have window : t ∈ Icc 0 (1/100:ℝ) := ⟨ht.le,by linarith⟩
  let Y : ℕ → ℝ := fun j => (H t)^[j] 0
  have first : Y 0=0 := rfl
  have succ (j : ℕ) : Y (j+1)=H t (Y j) := Function.iterate_succ_apply' (H t) j 0
  have init : ramp a (b/2) (Y 0)=0 := by
    unfold ramp
    rw [first,max_eq_left (by linarith [ha.1]),min_eq_right (by linarith)]
  have go (j : ℕ) (hj : j≤k) :
      ramp a (b/2) (Y j) ≤ (j:ℝ)*15*t ∧
      (j:ℝ)*b/5 ≤ coord b (Y j-a)-coord b (-a) := by
    induction j with
    | zero => rw [init,first]; simp
    | succ j ih =>
      obtain ⟨rl,cl⟩ := ih (Nat.le_of_succ_le hj)
      have hy := stay j (Nat.le_of_succ_le hj)
      change Y j ∈ Icc 0 cap at hy
      have r := ramp_step (b:=b/2) (by linarith) (by linarith) (by nlinarith only [bt]) window hy ha root
      have dl := (channel_quadratic_step window hy ha root).1
      have hx : b+|Y j-a|≤1 := by
        have hy' := hy.2
        unfold cap at hy'
        cases le_total 0 (Y j-a) with
        | inl h => rw [abs_of_nonneg h]; linarith [ha.1]
        | inr h => rw [abs_of_nonpos h]; linarith [ha.2,hy.1]
      have c := coord_step (x:=Y j-a) (y:=H t (Y j)-a) hb hx (by linarith)
      rw [succ]
      push_cast
      exact ⟨by linarith,by linarith⟩
  have fin : ramp a (b/2) (Y k)=2*(b/2) := by
    change 7/20 ≤ Y k at reached
    unfold ramp
    rw [max_eq_right (by linarith [ha.2]),min_eq_left (by linarith [ha.2])]
  obtain ⟨r,c⟩ := go k (le_refl _)
  rw [fin] at r
  have lo : 1/15 ≤ (k:ℝ)*b := by
    apply (mul_le_mul_iff_left₀ hb).mp
    rw [←bt] at r
    nlinarith only [r]
  have hi : (k:ℝ)*b ≤ 10 := by
    linarith [(coord_range (x:=Y k-a) hb).2,(coord_range (x:= -a) hb).1]
  have lo2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/15) lo 2
  have hi2 := pow_le_pow_left₀ (by positivity : 0≤(k:ℝ)*b) hi 2
  rw [mul_pow, bt] at lo2 hi2
  exact ⟨by linarith,by linarith⟩

#print axioms channel_inverse_square
end
end LoopsParabolic
