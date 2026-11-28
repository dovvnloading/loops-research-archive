import GlobalShootingParameter
import GlobalRestrictiveConverse
import GlobalWindowBoundaryProduct
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The complete positive restrictive parameter window

The endpoint condition is reduced to an exact inverse secant equation.
Its right side is a contraction on the entire terminal interval, so there
is one boundary and no hidden disconnected portion of the physical class.
-/

namespace GlobalWindowBoundary

open Set Function NearTwoInverse NearTwoShooting
open LimitingCrestQuadraticReturn GlobalRestrictiveWindow
open GlobalWindowShooting GlobalWindowBoundaryProduct

noncomputable section

/-- The exact endpoint equation in the actual critical-return coordinate. -/
def boundaryMap (p : ℕ) (d : ℝ) : ℝ :=
  8*scale p / endpointProduct (selectedParameter p d) p d

private theorem selected_band {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) :
    selectedParameter p d ∈ Icc (-2 : ℝ) (-2+20*scale p) :=
  (selectedParameter_spec hp hd).1

/-- The exact boundary map preserves a strictly smaller interior interval. -/
theorem boundaryMap_bounds {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) :
    8*scale p ≤ boundaryMap p d ∧
      boundaryMap p d ≤ (40/3 : ℝ)*scale p := by
  have hP := endpointProduct_bounds hp (selected_band hp hd) hd
  have hP0 : 0 < endpointProduct (selectedParameter p d) p d := by linarith [hP.1]
  have hq := scale_pos p
  unfold boundaryMap
  constructor
  · apply (le_div_iff₀ hP0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hP.2 (by positivity : 0 ≤ 8*scale p)]
  · apply (div_le_iff₀ hP0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hP.1
      (by positivity : 0 ≤ (40/3 : ℝ)*scale p)]

private theorem parameter_nonexpanding {p : ℕ} (hp : 17 ≤ p) {d e : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p))
    (he : e ∈ Icc (0 : ℝ) (14*scale p)) :
    |selectedParameter p d-selectedParameter p e| ≤ |d-e| := by
  have h := selectedParameter_comparison hp hd he
  have hq := scale_small hp
  have hq0 := scale_pos p
  have hm := mul_le_mul_of_nonneg_right h hq0.le
  have hid : (4 : ℝ)^p*scale p=1 := by
    unfold scale
    rw [← mul_pow]
    norm_num
  have hm' : (9/100 : ℝ)*|selectedParameter p d-selectedParameter p e| ≤
      |d-e| * scale p := by
    calc
      _ = ((9/100 : ℝ)*4^p*|selectedParameter p d-selectedParameter p e|)*scale p := by
        calc
          _ = ((9/100 : ℝ)*|selectedParameter p d-selectedParameter p e|)*
              ((4 : ℝ)^p*scale p) := by rw [hid]; ring
          _ = _ := by ring
      _ ≤ _ := hm
  have hsmall := mul_le_mul_of_nonneg_left hq (abs_nonneg (d-e))
  nlinarith only [hm',hsmall,abs_nonneg (d-e)]

/-- A uniform contraction controls the entire boundary equation, including
both ends of the possible critical-return range. -/
theorem boundaryMap_contraction {p : ℕ} (hp : 17 ≤ p) {d e : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p))
    (he : e ∈ Icc (0 : ℝ) (14*scale p)) :
    |boundaryMap p d-boundaryMap p e| ≤ (1/2 : ℝ)*|d-e| := by
  let P := endpointProduct (selectedParameter p d) p d
  let Q := endpointProduct (selectedParameter p e) p e
  have hP : 3/5 ≤ P ∧ P ≤ 1 := endpointProduct_bounds hp (selected_band hp hd) hd
  have hQ : 3/5 ≤ Q ∧ Q ≤ 1 := endpointProduct_bounds hp (selected_band hp he) he
  have hP0 : 0 < P := by linarith [hP.1]
  have hQ0 : 0 < Q := by linarith [hQ.1]
  have hprod : (9/25 : ℝ) ≤ P*Q := by
    have h := mul_le_mul hP.1 hQ.1 (by norm_num : (0 : ℝ) ≤ 3/5) hP0.le
    norm_num at h ⊢
    exact h
  have hdiff := endpointProduct_lipschitz hp
    (selected_band hp hd) (selected_band hp he) hd he
  have hpar := parameter_nonexpanding hp hd he
  have hdiff' : |P-Q| ≤ 4*(p : ℝ)*|d-e| := by
    have hm := mul_le_mul_of_nonneg_left hpar (by positivity : 0 ≤ 2*(p : ℝ))
    change |P-Q| ≤ _ at hdiff
    nlinarith only [hdiff,hm]
  have hq0 := scale_pos p
  have hid : (boundaryMap p d-boundaryMap p e)*P*Q=8*scale p*(Q-P) := by
    dsimp [boundaryMap,P,Q]
    field_simp [ne_of_gt hP0,ne_of_gt hQ0]
    <;> ring
  have habs := congrArg abs hid
  rw [abs_mul,abs_mul,abs_of_pos hP0,abs_of_pos hQ0,
    abs_mul,abs_of_pos (by positivity : 0 < 8*scale p),abs_sub_comm Q P] at habs
  have hleft := mul_le_mul_of_nonneg_left hprod
    (abs_nonneg (boundaryMap p d-boundaryMap p e))
  have hright := mul_le_mul_of_nonneg_left hdiff' (by positivity : 0 ≤ 8*scale p)
  have hbudget := horizon_scale_small hp
  have hcoef : (32 : ℝ)*(p : ℝ)*scale p ≤ 9/50 := by nlinarith only [hbudget]
  have hlast := mul_le_mul_of_nonneg_right hcoef (abs_nonneg (d-e))
  nlinarith only [habs,hleft,hright,hlast]

theorem boundaryMap_continuousOn {p : ℕ} (hp : 17 ≤ p) :
    ContinuousOn (boundaryMap p) (Icc (0 : ℝ) (14*scale p)) := by
  have h : LipschitzOnWith (1/2 : ℝ≥0) (boundaryMap p)
      (Icc (0 : ℝ) (14*scale p)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro d hd e he
    simpa only [Real.dist_eq,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
      using boundaryMap_contraction hp hd he
  exact h.continuousOn

/-- There is exactly one complete physical boundary scale. -/
theorem exists_unique_boundary_scale {p : ℕ} (hp : 17 ≤ p) :
    ∃! D : ℝ, D ∈ Icc (0 : ℝ) (14*scale p) ∧ boundaryMap p D=D := by
  have hq0 := scale_pos p
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (14*scale p) := ⟨le_rfl,by positivity⟩
  have hright : 14*scale p ∈ Icc (0 : ℝ) (14*scale p) := ⟨by positivity,le_rfl⟩
  have hlo := (boundaryMap_bounds hp hzero).1
  have hhi := (boundaryMap_bounds hp hright).2
  obtain ⟨D,hD,hz⟩ := intermediate_value_Icc' (by positivity : (0 : ℝ) ≤ 14*scale p)
    ((boundaryMap_continuousOn hp).sub continuousOn_id)
    (show (0 : ℝ) ∈ Icc
      (boundaryMap p (14*scale p)-14*scale p) (boundaryMap p 0-0) by
      constructor <;> linarith)
  have hfix : boundaryMap p D=D := by linarith only [hz]
  refine ⟨D,⟨hD,hfix⟩,?_⟩
  intro E hE
  have h := boundaryMap_contraction hp hE.1 hD
  rw [hE.2,hfix] at h
  have hz' : |E-D|=0 := by linarith [abs_nonneg (E-D)]
  exact sub_eq_zero.mp (abs_eq_zero.mp hz')

theorem boundary_scale_bounds {p : ℕ} (hp : 17 ≤ p) {D : ℝ}
    (hD : D ∈ Icc (0 : ℝ) (14*scale p)) (hfix : boundaryMap p D=D) :
    D ∈ Icc (8*scale p) ((40/3 : ℝ)*scale p) := by
  have h := boundaryMap_bounds hp hD
  rwa [hfix] at h

private theorem scale_shift {p : ℕ} (hp : 1 ≤ p) :
    (4 : ℝ)^(p-1)*(4*scale p)=1 := by
  have hid : (4 : ℝ)^p*scale p=1 := by
    unfold scale
    rw [← mul_pow]
    norm_num
  have hpower : (4 : ℝ)^p=(4 : ℝ)^(p-1)*4 := by
    rw [← pow_succ,Nat.sub_add_cancel hp]
  rw [hpower] at hid
  nlinarith only [hid]

/-- The normalized scalar inequality is exactly physical endpoint
invariance; it is not an approximation by a limiting quadratic map. -/
theorem endpoint_inequality_iff {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p)) (hd0 : 0 < d) :
    d^2 ≤ back (selectedParameter p d) (p-1) d-
      back (selectedParameter p d) (p-1) (-d) ↔ d ≤ boundaryMap p d := by
  let P := endpointProduct (selectedParameter p d) p d
  let Δ := back (selectedParameter p d) (p-1) d-
    back (selectedParameter p d) (p-1) (-d)
  have hP := endpointProduct_bounds hp (selected_band hp hd) hd
  have hP0 : 0 < P := by dsimp [P]; linarith [hP.1]
  have hid := endpointProduct_identity hp (selected_band hp hd) hd
  change Δ*4^(p-1)*P=2*d at hid
  have hm := congrArg (fun x : ℝ => x*(4*scale p)) hid
  have hscale := scale_shift (by omega : 1 ≤ p)
  have hdisplacement : Δ*P=8*scale p*d := by
    calc
      Δ*P = Δ*P*((4 : ℝ)^(p-1)*(4*scale p)) := by rw [hscale]; ring
      _ = (Δ*4^(p-1)*P)*(4*scale p) := by ring
      _ = (2*d)*(4*scale p) := hm
      _ = 8*scale p*d := by ring
  change d^2 ≤ Δ ↔ d ≤ 8*scale p/P
  rw [le_div_iff₀ hP0]
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_right h hP0.le
    have hmul' : d*(d*P) ≤ d*(8*scale p) := by
      nlinarith only [hmul,hdisplacement]
    exact (mul_le_mul_iff_right₀ hd0).mp hmul'
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h hd0.le
    have hmul' : d^2*P ≤ Δ*P := by nlinarith only [hmul,hdisplacement]
    exact (mul_le_mul_iff_left₀ hP0).mp hmul'

/-- The invariant side of the unique boundary is the entire initial
terminal interval; there are no additional admissible pieces. -/
theorem boundary_inequality_iff {p : ℕ} (hp : 17 ≤ p) {d D : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (14*scale p))
    (hD : D ∈ Icc (0 : ℝ) (14*scale p)) (hfix : boundaryMap p D=D) :
    d ≤ boundaryMap p d ↔ d ≤ D := by
  have h := boundaryMap_contraction hp hd hD
  rw [hfix] at h
  constructor
  · intro hle
    by_contra! hlt
    rw [abs_of_pos (sub_pos.mpr hlt)] at h
    have hup := (abs_le.mp h).2
    linarith
  · intro hle
    rw [abs_of_nonpos (sub_nonpos.mpr hle)] at h
    have hlo := (abs_le.mp h).1
    linarith

/-- The global physical class is one half-open parameter interval.  Its
endpoints are derived from the full return dynamics, not supplied as a chart. -/
theorem complete_restrictive_window {p : ℕ} (hp : 17 ≤ p) :
    ∃ D : ℝ, D ∈ Icc (8*scale p) ((40/3 : ℝ)*scale p) ∧
      boundaryMap p D=D ∧
      {c : ℝ | PositiveRestrictiveReturn c p} =
        Ico (selectedParameter p D) (selectedParameter p 0) := by
  obtain ⟨D,⟨hD,hfix⟩,_⟩ := exists_unique_boundary_scale hp
  have hb := boundary_scale_bounds hp hD hfix
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity : 0 < 8*scale p) hb.1
  have hsubset : Icc (0 : ℝ) D ⊆ Icc (0 : ℝ) (14*scale p) :=
    Icc_subset_Icc le_rfl hD.2
  have himage : {c : ℝ | PositiveRestrictiveReturn c p} =
      selectedParameter p '' Ioc (0 : ℝ) D := by
    ext c
    constructor
    · intro hc
      let d := criticalValue c p
      have hd : d ∈ Icc (0 : ℝ) (14*scale p) :=
        ⟨hc.return_pos.le,(hc.return_scale hp).le⟩
      have hspec := selectedParameter_spec hp hd
      have hcband : c ∈ Icc (-2 : ℝ) (-2+20*scale p) :=
        ⟨hc.parameter_band.1,(hc.parameter_upper hp).le⟩
      have hseq : selectedParameter p d=c := by
        obtain ⟨a,ha,hunique⟩ := GlobalWindowShooting.unique_shooting_parameter hp hd
        exact (hunique _ hspec).trans (hunique _ ⟨hcband,hc.shooting_identity hp⟩).symm
      have hend := (restrictive_iff_endpoint hp hcband hc.return_pos hd.2
        (hc.shooting_identity hp)).mp hc
      change d^2 ≤ back c (p-1) d-back c (p-1) (-d) at hend
      rw [← hseq] at hend
      have hle := (endpoint_inequality_iff hp hd hc.return_pos).mp hend
      exact ⟨d,⟨hc.return_pos,(boundary_inequality_iff hp hd hD hfix).mp hle⟩,hseq⟩
    · rintro ⟨d,hd,rfl⟩
      have hdb : d ∈ Icc (0 : ℝ) (14*scale p) := ⟨hd.1.le,hd.2.trans hD.2⟩
      have hspec := selectedParameter_spec hp hdb
      apply (restrictive_iff_endpoint hp hspec.1 hd.1 hdb.2 hspec.2).mpr
      exact (endpoint_inequality_iff hp hdb hd.1).mpr
        ((boundary_inequality_iff hp hdb hD hfix).mpr hd.2)
  refine ⟨D,hb,hfix,himage.trans ?_⟩
  exact ContinuousOn.image_Ioc_of_strictAntiOn hD0.le
    ((continuousOn_selectedParameter hp).mono hsubset)
    ((selectedParameter_strictAntiOn hp).mono hsubset)

end
end GlobalWindowBoundary
