import GlobalWindowThickness
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The complete positive-return shooting parameter

The critical return, including the zero endpoint, parametrizes the entire
rectangle needed by the global restrictive-window argument.  Its inverse
parameter estimate is uniform before any interval invariance is assumed.
-/

namespace GlobalWindowShooting

open Set Function NearTwoInverse NearTwoShooting

noncomputable section

private theorem terminal_band {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) : d ∈ Icc (0 : ℝ) 2 := by
  have hq := scale_small hp
  exact ⟨hd.1,by linarith [hd.2]⟩

private theorem small_parameter_band {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p)) :
    c ∈ Icc (-2 : ℝ) (-2+1/10000) := by
  have hq := scale_small hp
  exact ⟨hc.1,by linarith [hc.2]⟩

private theorem parameter_budget {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p)) :
    ((p-2 : ℕ) : ℝ)*(c+2) ≤ 1/10000 := by
  have hq := horizon_scale_small hp
  have hn : ((p-2 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 2
  have hm := mul_le_mul_of_nonneg_right hn (show 0 ≤ c+2 by linarith [hc.1])
  have hm' := mul_le_mul_of_nonneg_left
    (show c+2 ≤ 20*scale p by linarith [hc.2])
    (show (0 : ℝ) ≤ p by positivity)
  nlinarith only [hm,hm',hq]

private theorem chebyshev_back_lt_two {d : ℝ} (hd : d < 2) (n : ℕ) :
    back (-2) n d < 2 := by
  induction n with
  | zero => exact hd
  | succ n ih =>
    rw [back_succ,B]
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).mpr (by nlinarith)

/-- The shooting equation has exactly one parameter for every terminal
return between zero and the global upper return bound. -/
theorem unique_shooting_parameter {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) :
    ∃! c : ℝ, c ∈ Icc (-2 : ℝ) (-2+20*scale p) ∧
      shooting (p-2) d c = 0 := by
  have hq := scale_small hp
  have hleft : 0 < shooting (p-2) d (-2) := by
    have hback := chebyshev_back_lt_two (show d<2 by linarith [hd.2]) (p-2)
    dsimp [shooting]
    linarith only [hback]
  have hright : shooting (p-2) d (-2+20*scale p)<0 := by
    have hz := shooting_right_neg hp
      (show (0 : ℝ) ∈ Icc (0 : ℝ) (12*scale p) from
        ⟨le_rfl,mul_nonneg (by norm_num) (scale_pos p).le⟩)
    have hmono := back_mono_initial (-2+20*scale p) (p-2) hd.1
    dsimp [shooting] at hz ⊢
    linarith only [hz,hmono]
  have hab : (-2 : ℝ) ≤ -2+20*scale p := by linarith [scale_pos p]
  obtain ⟨c,hc,hz⟩ := intermediate_value_Icc' hab
    (continuous_shooting (p-2) d).continuousOn
    (show (0 : ℝ) ∈ Icc (shooting (p-2) d (-2+20*scale p))
      (shooting (p-2) d (-2)) from ⟨hright.le,hleft.le⟩)
  refine ⟨c,⟨hc,hz⟩,?_⟩
  intro x hx
  exact (shooting_strictAnti (p-2) (terminal_band hp hd)).injOn
    (parameter_band hp hx.1) (parameter_band hp hc) (hx.2.trans hz.symm)

def selectedParameter (p : ℕ) (d : ℝ) : ℝ :=
  if h : ∃ c : ℝ, c ∈ Icc (-2 : ℝ) (-2+20*scale p) ∧
      shooting (p-2) d c = 0 then Classical.choose h else -2

theorem selectedParameter_spec {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) :
    selectedParameter p d ∈ Icc (-2 : ℝ) (-2+20*scale p) ∧
      shooting (p-2) d (selectedParameter p d)=0 := by
  have hex := (unique_shooting_parameter hp hd).exists
  simp only [selectedParameter,dif_pos hex]
  exact Classical.choose_spec hex

theorem eq_selectedParameter {p : ℕ} (hp : 17 ≤ p) {c d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p))
    (hc : c ∈ Icc (-2 : ℝ) (-2+20*scale p))
    (hs : shooting (p-2) d c=0) : c=selectedParameter p d := by
  have hsel := selectedParameter_spec hp hd
  exact (shooting_strictAnti (p-2) (terminal_band hp hd)).injOn
    (parameter_band hp hc) (parameter_band hp hsel.1) (hs.trans hsel.2.symm)

private theorem back_strictMono_initial {c : ℝ}
    (hc : c ∈ Icc (-2 : ℝ) (-49/25)) (n : ℕ) :
    StrictMonoOn (back c n) (Icc (0 : ℝ) 2) := by
  induction n with
  | zero => intro x hx y hy hxy; exact hxy
  | succ n ih =>
    intro x hx y hy hxy
    rw [back_succ,back_succ]
    unfold B
    exact Real.sqrt_lt_sqrt
      (by linarith [(back_bounds hc hx n).1,hc.2])
      (sub_lt_sub_right (ih hx hy hxy) c)

theorem selectedParameter_strictAntiOn {p : ℕ} (hp : 17 ≤ p) :
    StrictAntiOn (selectedParameter p) (Icc (0 : ℝ) (14*scale p)) := by
  intro d hd e he hde
  have hcd := selectedParameter_spec hp hd
  have hce := selectedParameter_spec hp he
  have hback := back_strictMono_initial (parameter_band hp hcd.1) (p-2)
    (terminal_band hp hd) (terminal_band hp he) hde
  have hnegative : shooting (p-2) e (selectedParameter p d)<0 := by
    have hz := hcd.2
    dsimp [shooting] at hz ⊢
    linarith only [hback,hz]
  by_contra hfail
  have hle : selectedParameter p d ≤ selectedParameter p e := le_of_not_gt hfail
  have hmono := (shooting_strictAnti (p-2) (terminal_band hp he)).antitoneOn
    (parameter_band hp hcd.1) (parameter_band hp hce.1) hle
  rw [hce.2] at hmono
  linarith only [hmono,hnegative]

/-- An inverse Lipschitz estimate for the critical-return coordinate on
the whole shooting rectangle. -/
theorem selectedParameter_comparison {p : ℕ} (hp : 17 ≤ p) {d e : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p))
    (he : e ∈ Icc (0 : ℝ) (14*scale p)) :
    (9/100 : ℝ)*4^p*|selectedParameter p d-selectedParameter p e| ≤ |d-e| := by
  have hc := selectedParameter_spec hp hd
  have ha := selectedParameter_spec hp he
  exact GlobalWindowThickness.shooting_parameter_comparison hp
    (small_parameter_band hp ha.1) (small_parameter_band hp hc.1)
    (parameter_budget hp hc.1) (terminal_band hp hd) (terminal_band hp he)
    ha.2 hc.2

theorem selectedParameter_lipschitz {p : ℕ} (hp : 17 ≤ p) {d e : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p))
    (he : e ∈ Icc (0 : ℝ) (14*scale p)) :
    |selectedParameter p d-selectedParameter p e| ≤ 12*scale p*|d-e| := by
  have h := selectedParameter_comparison hp hd he
  have hmul := mul_le_mul_of_nonneg_right h (scale_pos p).le
  have hpow : (4 : ℝ)^p*scale p=1 := by
    unfold scale
    rw [← mul_pow]
    norm_num
  have hid : ((9/100 : ℝ)*4^p*|selectedParameter p d-selectedParameter p e|)*scale p=
      (9/100 : ℝ)*|selectedParameter p d-selectedParameter p e| := by
    calc
      _ = (9/100 : ℝ)*|selectedParameter p d-selectedParameter p e| * (4^p*scale p) := by ring
      _ = _ := by rw [hpow]; ring
  rw [hid] at hmul
  have hnonneg := mul_nonneg (scale_pos p).le (abs_nonneg (d-e))
  nlinarith only [hmul,hnonneg]

theorem continuousOn_selectedParameter {p : ℕ} (hp : 17 ≤ p) :
    ContinuousOn (selectedParameter p) (Icc (0 : ℝ) (14*scale p)) := by
  have hLip : LipschitzOnWith ⟨12*scale p,mul_nonneg (by norm_num) (scale_pos p).le⟩
      (selectedParameter p) (Icc (0 : ℝ) (14*scale p)) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro d hd e he
    simpa only [Real.dist_eq,NNReal.coe_mk] using selectedParameter_lipschitz hp hd he
  exact hLip.continuousOn

end
end GlobalWindowShooting
