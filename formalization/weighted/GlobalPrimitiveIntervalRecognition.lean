import GlobalRestrictiveWindow

/-!
# Recognition from an arbitrary physical restrictive interval

The supplied symmetric interval may have any positive radius and the
parameter is unrestricted.  Its complete physical phase itinerary and
invariance force the real parameter range.  A positive fourth return then
forces invariance of the canonical interval determined by the critical
value itself.
-/

namespace GlobalPrimitiveIntervalRecognition

open Set Function
open LimitingCrestQuadraticReturn NearTwoShooting GlobalRestrictiveWindow

noncomputable section

structure PositiveReturnInterval (c : ℝ) (p : ℕ) (r : ℝ) : Prop where
  radius_pos : 0 < r
  negative_first : ∀ x ∈ Icc (-r) r, realMap c x < 0
  positive_phases : ∀ j : ℕ, 2 ≤ j → j < p →
    ∀ x ∈ Icc (-r) r, 0 < (realMap c)^[j] x
  invariant : MapsTo ((realMap c)^[p]) (Icc (-r) r) (Icc (-r) r)

theorem PositiveReturnInterval.zero_mem {c r : ℝ} {p : ℕ}
    (h : PositiveReturnInterval c p r) : (0 : ℝ) ∈ Icc (-r) r := by
  constructor <;> linarith [h.radius_pos]

theorem PositiveReturnInterval.critical_return_mem {c r : ℝ} {p : ℕ}
    (h : PositiveReturnInterval c p r) : criticalValue c p ∈ Icc (-r) r :=
  h.invariant h.zero_mem

/-- The full invariant physical interval forces the parameter range;
no prior near-endpoint or real-window assumption is used. -/
theorem PositiveReturnInterval.parameter_band {c r : ℝ} {p : ℕ}
    (hp : 3 ≤ p) (h : PositiveReturnInterval c p r) :
    c ∈ Icc (-2 : ℝ) (-1) := by
  have hcneg : c<0 := by
    have hn := h.negative_first 0 h.zero_mem
    simpa only [realMap,zero_pow (by decide : 2≠0),zero_add] using hn
  have hquad : 0<c^2+c := by
    have hp2 := h.positive_phases 2 (by omega) (by omega) 0 h.zero_mem
    change 0<(0^2+c)^2+c at hp2
    norm_num at hp2
    exact hp2
  have hcupper : c < -1 := by
    by_contra hupper
    have hm := mul_nonpos_of_nonpos_of_nonneg hcneg.le
      (show 0≤c+1 by linarith)
    nlinarith only [hm,hquad]
  have hclower : -2 ≤ c := by
    by_contra hlower
    have hcsmall : c < -2 := by linarith
    have hcplus : c+2<0 := by linarith
    have hm := mul_pos_of_neg_of_neg hcneg hcplus
    have hbase : -c ≤ c^2+c := by nlinarith only [hm]
    have horbit : ∀ j : ℕ, 2 ≤ j → -c ≤ criticalValue c j := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => simpa only [criticalValue_two] using hbase
      | succ n hn ih =>
        have hs := pow_le_pow_left₀ (show 0 ≤ -c by linarith) ih 2
        rw [criticalValue_step]
        nlinarith only [hs,hbase]
    have hd := horbit p (by omega)
    have hsq := pow_le_pow_left₀ (show 0 ≤ -c by linarith) hd 2
    have hfirst := h.negative_first (criticalValue c p) h.critical_return_mem
    dsimp [realMap] at hfirst
    nlinarith only [hsq,hquad,hfirst]
  exact ⟨hclower,hcupper.le⟩

/-- Every return on the supplied interval reverses order in the square
of the input.  The proof uses all intermediate physical branch signs. -/
theorem PositiveReturnInterval.return_order {c r x y : ℝ} {p : ℕ}
    (hp : 2 ≤ p) (h : PositiveReturnInterval c p r)
    (hx : x ∈ Icc (-r) r) (hy : y ∈ Icc (-r) r) (hxy : x^2 ≤ y^2) :
    (realMap c)^[p] y ≤ (realMap c)^[p] x := by
  have hfirst : realMap c x ≤ realMap c y := by
    dsimp [realMap]
    linarith only [hxy]
  have hnegx := h.negative_first x hx
  have hnegy := h.negative_first y hy
  have hstep : ∀ j : ℕ, 2 ≤ j → j ≤ p →
      (realMap c)^[j] y ≤ (realMap c)^[j] x := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro hjp
      have hm := mul_nonneg (sub_nonneg.mpr hfirst)
        (show 0 ≤ -realMap c x-realMap c y by linarith only [hnegx,hnegy])
      change (realMap c y)^2+c ≤ (realMap c x)^2+c
      nlinarith only [hm]
    | succ n hn ih =>
      intro hnp
      have hprev := ih (by omega)
      have hpos := h.positive_phases n hn (by omega) y hy
      have hsq := pow_le_pow_left₀ hpos.le hprev 2
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      change ((realMap c)^[n] y)^2+c ≤ ((realMap c)^[n] x)^2+c
      exact add_le_add hsq le_rfl
  exact hstep p hp le_rfl

private theorem critical_block (c : ℝ) (p n : ℕ) :
    (realMap c)^[p] (criticalValue c (n*p)) = criticalValue c ((n+1)*p) := by
  change (realMap c)^[p] ((realMap c)^[n*p] 0) = (realMap c)^[((n+1)*p)] 0
  rw [← Function.iterate_add_apply,show p+n*p=(n+1)*p by ring]

/-- If the fourth critical return is positive, the image of the positive
critical endpoint cannot cross the negative critical endpoint. -/
theorem PositiveReturnInterval.endpoint_lower {c r : ℝ} {p : ℕ}
    (hp : 2 ≤ p) (h : PositiveReturnInterval c p r)
    (hd : 0 < criticalValue c p) (hfourth : 0 < criticalValue c (4*p)) :
    -criticalValue c p ≤ (realMap c)^[p] (criticalValue c p) := by
  have hdmem := h.critical_return_mem
  have h2 : (realMap c)^[p] (criticalValue c p)=criticalValue c (2*p) := by
    simpa only [one_mul] using critical_block c p 1
  have h3 : (realMap c)^[p] (criticalValue c (2*p))=criticalValue c (3*p) := by
    simpa only [show (2 : ℕ)+1=3 by omega] using critical_block c p 2
  have h4 : (realMap c)^[p] (criticalValue c (3*p))=criticalValue c (4*p) := by
    simpa only [show (3 : ℕ)+1=4 by omega] using critical_block c p 3
  have h2mem : criticalValue c (2*p) ∈ Icc (-r) r := by
    rw [← h2]
    exact h.invariant hdmem
  have h3mem : criticalValue c (3*p) ∈ Icc (-r) r := by
    rw [← h3]
    exact h.invariant h2mem
  rw [h2]
  by_contra hbad
  have h2neg : criticalValue c (2*p) < -criticalValue c p := by linarith
  have hs2 : (criticalValue c p)^2 ≤ (criticalValue c (2*p))^2 := by
    have hs := pow_le_pow_left₀ hd.le
      (show criticalValue c p ≤ -criticalValue c (2*p) by linarith) 2
    nlinarith only [hs]
  have ho3 := h.return_order hp hdmem h2mem hs2
  rw [h2,h3] at ho3
  have h3neg : criticalValue c (3*p) < -criticalValue c p := ho3.trans_lt h2neg
  have hs3 : (criticalValue c p)^2 ≤ (criticalValue c (3*p))^2 := by
    have hs := pow_le_pow_left₀ hd.le
      (show criticalValue c p ≤ -criticalValue c (3*p) by linarith) 2
    nlinarith only [hs]
  have ho4 := h.return_order hp hdmem h3mem hs3
  rw [h2,h4] at ho4
  linarith only [ho4,h2neg,hd,hfourth]

/-- Recognition of the canonical critical-return interval from any
literal positive-itinerary invariant interval.  Neither a parameter
window nor the critical-return radius is assumed. -/
theorem recognize_canonical_return {c r : ℝ} {p : ℕ}
    (hp : 3 ≤ p) (h : PositiveReturnInterval c p r)
    (hd : 0 < criticalValue c p) (hfourth : 0 < criticalValue c (4*p)) :
    PositiveRestrictiveReturn c p := by
  have hdmem := h.critical_return_mem
  have hsubset : returnInterval c p ⊆ Icc (-r) r := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2,hdmem.2]
  have hend := h.endpoint_lower (by omega) hd hfourth
  refine {
    parameter_band := h.parameter_band hp
    return_pos := hd
    negative_first := fun x hx => h.negative_first x (hsubset hx)
    positive_phases := fun j hj hjp x hx => h.positive_phases j hj hjp x (hsubset hx)
    invariant := ?_ }
  intro x hx
  have hxmem := hsubset hx
  have hup := h.return_order (by omega) h.zero_mem hxmem (by simpa using sq_nonneg x)
  have hsquare : x^2 ≤ (criticalValue c p)^2 := by
    have hm := mul_nonneg
      (show 0 ≤ criticalValue c p-x by linarith [hx.2])
      (show 0 ≤ criticalValue c p+x by linarith [hx.1])
    nlinarith only [hm]
  have hlo := h.return_order (by omega) hxmem hdmem hsquare
  change (realMap c)^[p] x ≤ criticalValue c p at hup
  exact ⟨hend.trans hlo,hup⟩

end
end GlobalPrimitiveIntervalRecognition
