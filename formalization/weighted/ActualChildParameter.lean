import GlobalPrimitiveTipUniqueness
import TwoLevelPerturbation

/-!
# Identification with the archive's selected parameter

The chart below is the literal signed chart in section 1 of
`research/tip_family_theorem/THEOREM.md`: its coefficient is the finite
product of the critical derivatives, and the signed equation is kept
separate from chart membership.  The converse to the physical recognition
theorem is proved here from the complete quadratic iterates.  In particular,
no invariant interval is inserted into the definition of the archive chart.

This is a parameter-identification bridge for the child-width limit.  It
does not identify the chart with an entire maximal primitive component.
-/

namespace ActualChildParameter

open Set Function
open LimitingCrestQuadraticReturn NearTwoShooting NearTwoTip
open GlobalRestrictiveWindow GlobalPrimitiveTipUniqueness

noncomputable section

/-- The product from the archive, with indices `j+1 = 1,...,p-1`. -/
def archiveCoefficient (p : ℕ) (c : ℝ) : ℝ :=
  ∏ j ∈ Finset.range (p-1), 2*criticalValue c (j+1)

def archiveTau (p : ℕ) (c : ℝ) : ℝ :=
  archiveCoefficient p c * criticalValue c p

theorem archiveCoefficient_eq (p : ℕ) (c : ℝ) :
    archiveCoefficient p c = quadraticCoefficient c (p-1) := by
  have h (n : ℕ) : (∏ j ∈ Finset.range n, 2*criticalValue c (j+1)) =
      quadraticCoefficient c n := by
    induction n with
    | zero => simp [quadraticCoefficient]
    | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      change quadraticCoefficient c n*(2*criticalValue c (n+1)) =
        2*criticalValue c (n+1)*quadraticCoefficient c n
      ring
  exact h (p-1)

theorem archiveTau_eq (p : ℕ) (c : ℝ) : archiveTau p c = -kappa p c := by
  rw [archiveTau, archiveCoefficient_eq]
  unfold kappa
  ring

/-- Exactly the large-period signed kneading subchart in the archive.
The collision equation is deliberately absent from this predicate. -/
structure ArchivedChart (p : ℕ) (c : ℝ) : Prop where
  parameter_lower : 14*scale p < c+2
  parameter_upper : c+2 < 16*scale p
  return_small : |criticalValue c p| < 14*scale p
  tau_range : archiveTau p c ∈ Ioo (-2 : ℝ) (1/4)
  first_neg : criticalValue c 1 < 0
  positive_prefix : ∀ j : ℕ, 2 ≤ j → j ≤ p → 0 < criticalValue c j
  return_pos : 0 < criticalValue c p
  second_neg : criticalValue c (2*p) < 0
  third_neg : criticalValue c (3*p) < 0
  fourth_pos : 0 < criticalValue c (4*p)
  fifth_neg : criticalValue c (5*p) < 0
  sixth_pos : 0 < criticalValue c (6*p)

/-- The archive's selection equation on its independently specified chart. -/
def ArchivedSelectedTip (p : ℕ) (c : ℝ) : Prop :=
  ArchivedChart p c ∧ criticalValue c (6*p)+criticalValue c (3*p)=0

private theorem complex_iterate_real (c x : ℝ) (n : ℕ) :
    (quadraticMap c)^[n] (x : ℂ) = (((realMap c)^[n] x : ℝ) : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [quadraticMap, realMap, Complex.ofReal_add, Complex.ofReal_pow]

private theorem real_displacement (c : ℝ) (n : ℕ) (r x : ℝ)
    (hn : 1 ≤ n) (hr : 0 ≤ r)
    (hc : ∀ j : ℕ, j ≤ n → |criticalValue c j| ≤ 2)
    (hscale : (4 : ℝ)^n*r^2 ≤ 1) (hx : |x| ≤ r) :
    |(realMap c)^[n] x-criticalValue c n| ≤ (4 : ℝ)^n*r^2/3 := by
  have he : n-1+1=n := by omega
  have h := TwoLevelPerturbation.orbit_displacement c (n-1) r (x : ℂ) hr
    (fun j hj => hc j (by omega)) (by simpa only [he] using hscale)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx)
  rw [he, complex_iterate_real, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

private theorem critical_deficit {c : ℝ} (hc : -2 ≤ c) :
    ∀ j : ℕ, 2 ≤ j →
      2-criticalValue c j ≤ 3*(4 : ℝ)^(j-2)*(c+2) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    rw [criticalValue_two]
    norm_num
    nlinarith [sq_nonneg (c+2)]
  | succ n hn ih =>
    have hpow : (4 : ℝ)^(n+1-2) = 4*(4 : ℝ)^(n-2) := by
      rw [show n+1-2=(n-2)+1 by omega, pow_succ]
      ring
    have hm := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 4)
    rw [criticalValue_step, hpow]
    nlinarith only [hm, sq_nonneg (criticalValue c n-2), hc]

private theorem critical_phase_lower {p j : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p))
    (hj : 2 ≤ j) (hjp : j < p) : 17/16 ≤ criticalValue c j := by
  have hdef := critical_deficit hc.1 j hj
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
    (show j-2 ≤ p-3 by omega)
  have heps : 0 ≤ c+2 := by linarith [hc.1]
  have hmul := mul_le_mul_of_nonneg_right hpow heps
  have hupper := mul_le_mul_of_nonneg_left
    (show c+2 ≤ 20*scale p by linarith [hc.2])
    (show (0 : ℝ) ≤ (4 : ℝ)^(p-3) by positivity)
  have hid : (4 : ℝ)^p*scale p=1 := by
    simpa only [mul_comm] using TwoLevelPerturbation.scale_mul_power p
  have hpowp : (4 : ℝ)^p=(4 : ℝ)^(p-3)*64 := by
    calc
      (4 : ℝ)^p=(4 : ℝ)^((p-3)+3) := by congr 1; omega
      _=(4 : ℝ)^(p-3)*64 := by rw [pow_add]; norm_num
  rw [hpowp] at hid
  nlinarith only [hdef, hmul, hupper, hid]

private theorem return_order_of_phases {c r x y : ℝ} {p : ℕ}
    (hp : 2 ≤ p)
    (hfirst : ∀ z : ℝ, |z| ≤ r → realMap c z < 0)
    (hphase : ∀ j : ℕ, 2 ≤ j → j < p →
      ∀ z : ℝ, |z| ≤ r → 0 < (realMap c)^[j] z)
    (hx : |x| ≤ r) (hy : |y| ≤ r) (hxy : x^2 ≤ y^2) :
    (realMap c)^[p] y ≤ (realMap c)^[p] x := by
  have hfirstorder : realMap c x ≤ realMap c y := by
    dsimp [realMap]
    linarith only [hxy]
  have hnegx := hfirst x hx
  have hnegy := hfirst y hy
  have hstep : ∀ j : ℕ, 2 ≤ j → j ≤ p →
      (realMap c)^[j] y ≤ (realMap c)^[j] x := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro hjp
      have hm := mul_nonneg (sub_nonneg.mpr hfirstorder)
        (show 0 ≤ -realMap c x-realMap c y by linarith only [hnegx,hnegy])
      change (realMap c y)^2+c ≤ (realMap c x)^2+c
      nlinarith only [hm]
    | succ n hn ih =>
      intro hnp
      have hprev := ih (by omega)
      have hpos := hphase n hn (by omega) y hy
      have hsq := pow_le_pow_left₀ hpos.le hprev 2
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change ((realMap c)^[n] y)^2+c ≤ ((realMap c)^[n] x)^2+c
      exact add_le_add hsq le_rfl
  exact hstep p hp le_rfl

private theorem critical_block (c : ℝ) (p n : ℕ) :
    (realMap c)^[p] (criticalValue c (n*p)) = criticalValue c ((n+1)*p) := by
  change (realMap c)^[p] ((realMap c)^[n*p] 0)=(realMap c)^[((n+1)*p)] 0
  rw [← Function.iterate_add_apply, show p+n*p=(n+1)*p by ring]

/-- A small positive critical return and positive fourth return force a
literal invariant interval.  The wider interval is used only to prove
order for the second and third returns; invariance is a conclusion. -/
private theorem restrictive_of_small_fourth {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p))
    (hd : 0 < criticalValue c p) (hsmall : criticalValue c p ≤ 14*scale p)
    (hfourth : 0 < criticalValue c (4*p)) : PositiveRestrictiveReturn c p := by
  let d : ℝ := criticalValue c p
  let r : ℝ := 200*d
  let S : ℝ := (4 : ℝ)^p
  have hd0 : 0 < d := hd
  have hq := scale_small hp
  have hband := parameter_band hp hc
  have hcrit (j : ℕ) : |criticalValue c j| ≤ 2 :=
    TwoLevelPerturbation.critical_orbit_bound c
      ⟨hband.1, by linarith [hband.2]⟩ j
  have hS : 0 < S := by dsimp [S]; positivity
  have hid : S*scale p=1 := by
    simpa only [S, mul_comm] using TwoLevelPerturbation.scale_mul_power p
  have hSd : S*d ≤ 14 := by
    have hm := mul_le_mul_of_nonneg_left hsmall hS.le
    change S*d ≤ S*(14*scale p) at hm
    nlinarith only [hm, hid]
  have hr : 0 < r := by dsimp [r]; positivity
  have hrsmall : r ≤ 1/100 := by
    dsimp [r,d]
    linarith only [hsmall, hq]
  have hscale : S*r^2 ≤ 1 := by
    have hsq := pow_le_pow_left₀ hd0.le hsmall 2
    have hm := mul_le_mul_of_nonneg_left hsq hS.le
    have he : S*(14*scale p)^2=196*scale p := by
      calc
        S*(14*scale p)^2=196*(S*scale p)*scale p := by ring
        _=196*scale p := by rw [hid]; ring
    rw [he] at hm
    dsimp [r]
    nlinarith only [hm, hq]
  have hscale_of_le {s : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) : S*s^2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hsr 2) hS.le).trans hscale
  have hfirst (x : ℝ) (hx : |x| ≤ r) : realMap c x < 0 := by
    have habs : |x| ≤ 1/100 := hx.trans hrsmall
    have hsq : x^2 ≤ (1/100 : ℝ)^2 :=
      sq_le_sq' (abs_le.mp habs).1 (abs_le.mp habs).2
    dsimp [realMap]
    nlinarith only [hsq, hband.2]
  have hphase (j : ℕ) (hj : 2 ≤ j) (hjp : j < p)
      (x : ℝ) (hx : |x| ≤ r) : 0 < (realMap c)^[j] x := by
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hjp.le
    have ht : (4 : ℝ)^j*r^2 ≤ S*r^2 :=
      mul_le_mul_of_nonneg_right hpow (sq_nonneg r)
    have he := real_displacement c j r x (by omega) hr.le
      (fun n _ => hcrit n) (ht.trans hscale) hx
    have helo := (abs_le.mp he).1
    have hlo := critical_phase_lower hp hc hj hjp
    linarith only [helo, hlo, ht, hscale]
  have hdmem : |d| ≤ r := by rw [abs_of_pos hd0]; dsimp [r]; linarith
  have hzero : |(0 : ℝ)| ≤ r := by simpa using hr.le
  have h2eq : (realMap c)^[p] d=criticalValue c (2*p) := by
    simpa only [one_mul] using critical_block c p 1
  have h3eq : (realMap c)^[p] (criticalValue c (2*p))=criticalValue c (3*p) := by
    simpa only [show (2 : ℕ)+1=3 by omega] using critical_block c p 2
  have h4eq : (realMap c)^[p] (criticalValue c (3*p))=criticalValue c (4*p) := by
    simpa only [show (3 : ℕ)+1=4 by omega] using critical_block c p 3
  have hSd2 : S*d^2 ≤ 14*d := by
    have hm := mul_le_mul_of_nonneg_right hSd hd0.le
    nlinarith only [hm]
  have h2bound : |criticalValue c (2*p)| ≤ 6*d := by
    have he := real_displacement c p d d (by omega) hd0.le (fun j _ => hcrit j)
      (hscale_of_le hd0.le (by dsimp [r]; linarith)) (by rw [abs_of_pos hd0])
    rw [h2eq] at he
    change |criticalValue c (2*p)-d| ≤ S*d^2/3 at he
    have habs := abs_le.mp he
    apply abs_le.mpr
    constructor <;> nlinarith only [habs.1, habs.2, hSd2, hd0]
  have h3bound : |criticalValue c (3*p)| ≤ 169*d := by
    have he := real_displacement c p (6*d) (criticalValue c (2*p))
      (by omega) (by positivity) (fun j _ => hcrit j)
      (hscale_of_le (by positivity) (by dsimp [r]; linarith)) h2bound
    rw [h3eq] at he
    change |criticalValue c (3*p)-d| ≤ S*(6*d)^2/3 at he
    have habs := abs_le.mp he
    apply abs_le.mpr
    constructor <;> nlinarith only [habs.1, habs.2, hSd2, hd0]
  have h2mem : |criticalValue c (2*p)| ≤ r :=
    h2bound.trans (by dsimp [r]; linarith)
  have h3mem : |criticalValue c (3*p)| ≤ r :=
    h3bound.trans (by dsimp [r]; linarith)
  have hend : -d ≤ criticalValue c (2*p) := by
    by_contra hbad
    have h2neg : criticalValue c (2*p) < -d := by linarith
    have hs2 : d^2 ≤ (criticalValue c (2*p))^2 := by
      have hs := pow_le_pow_left₀ hd0.le
        (show d ≤ -criticalValue c (2*p) by linarith) 2
      nlinarith only [hs]
    have ho3 := return_order_of_phases (by omega : 2 ≤ p)
      hfirst hphase hdmem h2mem hs2
    rw [h2eq, h3eq] at ho3
    have h3neg : criticalValue c (3*p) < -d := ho3.trans_lt h2neg
    have hs3 : d^2 ≤ (criticalValue c (3*p))^2 := by
      have hs := pow_le_pow_left₀ hd0.le
        (show d ≤ -criticalValue c (3*p) by linarith) 2
      nlinarith only [hs]
    have ho4 := return_order_of_phases (by omega : 2 ≤ p)
      hfirst hphase hdmem h3mem hs3
    rw [h2eq, h4eq] at ho4
    linarith only [ho4, h2neg, hd0, hfourth]
  have hmem {x : ℝ} (hx : x ∈ returnInterval c p) : |x| ≤ r :=
    (abs_le.mpr hx).trans (by dsimp [r,d]; linarith only [hd])
  refine {
    parameter_band := ⟨hc.1, by linarith [hband.2]⟩
    return_pos := hd
    negative_first := fun x hx => hfirst x (hmem hx)
    positive_phases := fun j hj hjp x hx => hphase j hj hjp x (hmem hx)
    invariant := ?_ }
  intro x hx
  have hxabs : |x| ≤ d := abs_le.mpr hx
  have hsquare : x^2 ≤ d^2 := sq_le_sq' hx.1 hx.2
  have hup := return_order_of_phases (by omega : 2 ≤ p)
    hfirst hphase hzero (hmem hx) (by simpa using sq_nonneg x)
  have hlo := return_order_of_phases (by omega : 2 ≤ p)
    hfirst hphase (hmem hx) hdmem hsquare
  rw [h2eq] at hlo
  change (realMap c)^[p] x ≤ d at hup
  exact ⟨hend.trans hlo, hup⟩

/-- Every member of the literal archive chart has the required whole
physical restrictive interval; chart membership does not assume it. -/
theorem ArchivedChart.restrictive_interval {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ArchivedChart p c) : PositiveRestrictiveReturn c p := by
  have hq0 := scale_pos p
  have hband : c ∈ Icc (-2 : ℝ) (-2+20*scale p) := by
    constructor <;> linarith [hc.parameter_lower, hc.parameter_upper]
  have hsmall : criticalValue c p ≤ 14*scale p :=
    (le_abs_self _).trans hc.return_small.le
  exact restrictive_of_small_fourth hp hband hc.return_pos hsmall hc.fourth_pos

/-- The archive selection satisfies the parameter-free physical predicate. -/
theorem archivedSelectedTip_physical {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ArchivedSelectedTip p c) : PhysicalSignedTip p c := by
  have h := hc.1.restrictive_interval hp
  refine ⟨⟨criticalValue c p, ?_⟩, hc.1.return_pos, hc.1.second_neg,
    hc.1.third_neg, hc.1.fourth_pos, hc.1.fifth_neg, hc.2⟩
  exact ⟨h.return_pos, h.negative_first, h.positive_phases, h.invariant⟩

/-- Conversely, every archived quantitative actual tip lies in the exact
signed chart specified by the source theorem. -/
theorem actualTip_archivedSelectedTip {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : ArchivedSelectedTip p c := by
  have hphy := actual_tip_physical hp hc
  have h := hphy.canonical_interval hp
  have hpar := h.sharp_parameter_bounds hp
  have hk := hc.2.2.2.1
  refine ⟨{
    parameter_lower := hpar.1
    parameter_upper := hpar.2
    return_small := ?_
    tau_range := ?_
    first_neg := ?_
    positive_prefix := h.critical_prefix
    return_pos := hphy.return_pos
    second_neg := hphy.second_neg
    third_neg := hphy.third_neg
    fourth_pos := hphy.fourth_pos
    fifth_neg := hphy.fifth_neg
    sixth_pos := ?_ }, hphy.signed_relation⟩
  · rw [abs_of_pos h.return_pos]
    exact h.return_scale hp
  · rw [archiveTau_eq]
    constructor <;> linarith [hk.1, hk.2]
  · have he : criticalValue c 1=c := by
      norm_num [criticalValue, Function.iterate_succ_apply']
    rw [he]
    linarith [h.parameter_band.2]
  · linarith [hphy.signed_relation, hphy.third_neg]

/-- Exact equivalence with the archive selection, in both directions. -/
theorem archivedSelectedTip_iff_actualTip {p : ℕ} (hp : 17 ≤ p) {c : ℝ} :
    ArchivedSelectedTip p c ↔ ActualTip p c := by
  constructor
  · intro hc
    exact (physical_signed_tip_iff_actual_tip hp).mp (archivedSelectedTip_physical hp hc)
  · exact actualTip_archivedSelectedTip hp

theorem exists_unique_archivedSelectedTip (p : ℕ) (hp : 17 ≤ p) :
    ∃! c : ℝ, ArchivedSelectedTip p c := by
  obtain ⟨c, hc, huniq⟩ := exists_unique_physical_signed_tip p hp
  refine ⟨c, (archivedSelectedTip_iff_actualTip hp).mpr
    ((physical_signed_tip_iff_actual_tip hp).mp hc), ?_⟩
  intro a ha
  exact huniq a (archivedSelectedTip_physical hp ha)

/-- The unique root selected by the archive's literal signed chart. -/
def canonicalParameter (p : ℕ) (hp : 17 ≤ p) : ℝ :=
  (exists_unique_archivedSelectedTip p hp).exists.choose

theorem canonicalParameter_spec (p : ℕ) (hp : 17 ≤ p) :
    ArchivedSelectedTip p (canonicalParameter p hp) :=
  (exists_unique_archivedSelectedTip p hp).exists.choose_spec

theorem canonicalParameter_actual (p : ℕ) (hp : 17 ≤ p) :
    ActualTip p (canonicalParameter p hp) :=
  (archivedSelectedTip_iff_actualTip hp).mp (canonicalParameter_spec p hp)

/-- No arbitrary actual-tip choice remains in the canonical child family. -/
theorem actualTip_iff_eq_canonicalParameter {p : ℕ} (hp : 17 ≤ p) {c : ℝ} :
    ActualTip p c ↔ c=canonicalParameter p hp := by
  constructor
  · intro hc
    exact physical_signed_tip_unique hp (actual_tip_physical hp hc)
      (actual_tip_physical hp (canonicalParameter_actual p hp))
  · intro hc
    rw [hc]
    exact canonicalParameter_actual p hp

end

end ActualChildParameter
