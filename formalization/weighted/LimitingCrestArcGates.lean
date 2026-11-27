import LimitingCrestGeometry
import LimitingCrestParameter

/-!
# Complete real endpoint gates and complex support bounds for the model

The inequalities are the normalized analytic predicates of `other_gates`
and `whole_disk_four` in
`research/independent_audits/crest_transport_asymptotics_20261116/verify.py`. They concern the
polynomial `1-κ*z^2`. No KKL access or proper-path interpretation is made.
-/

namespace LimitingCrest
open Set Function
open LoopsLimitingCrestParameter
noncomputable section

def realOrbit (κ x : ℝ) : ℕ → ℝ
  | 0 => x
  | n+1 => realMap κ (realOrbit κ x n)

theorem realOrbit_eq_iterate (κ x : ℝ) (n : ℕ) :
    realOrbit κ x n = (realMap κ)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [realOrbit, Function.iterate_succ_apply', ih]

/-- Multiplication by -κ conjugates the normalized model to z²-κ. -/
theorem monic_conjugacy (κ x : ℝ) :
    (-κ*x)^2-κ = -κ*realMap κ x := by dsimp [realMap]; ring

theorem monic_iterate_conjugacy (κ : ℝ) (n : ℕ) :
    (fun x : ℝ => x^2-κ)^[n] 0 = -κ*criticalOrbit κ n := by
  induction n with
  | zero => simp [criticalOrbit]
  | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      exact monic_conjugacy κ (criticalOrbit κ n)

/-- The near-1.79 relation is the renormalized period-three tip relation
under τ=-κ. It is not the physical period-three parameter. -/
theorem monic_relation_equivalence {κ : ℝ} (hk : κ ≠ 0) :
    relation κ = 0 ↔
      (fun x : ℝ => x^2-κ)^[6] 0 + (fun x : ℝ => x^2-κ)^[3] 0 = 0 := by
  rw [monic_iterate_conjugacy,monic_iterate_conjugacy]
  have he : -κ*criticalOrbit κ 6 + -κ*criticalOrbit κ 3 = -κ*relation κ := by
    dsimp [relation]; ring
  rw [he,mul_eq_zero]
  simp only [neg_eq_zero, hk, false_or]

def qEndpoint (s : ℝ) := -(3/4 : ℝ)+s
def wEndpoint (s : ℝ) := -(3/4 : ℝ)-s
def initialDisk : Set ℂ := {z | ‖z+(3/4 : ℂ)‖ ≤ (133/2000 : ℝ)}

private theorem step_sq {κ x a b l u : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000))
    (hx : a ≤ x^2 ∧ x^2 ≤ b) (ha : 0 ≤ a)
    (hl : l ≤ 1-(17904/10000)*b) (hu : 1-(17903/10000)*a ≤ u) :
    realMap κ x ∈ Icc l u := by
  have hlow := mul_le_mul hk.1 hx.1 ha (by linarith [hk.1])
  have hupp := mul_le_mul hk.2 hx.2 (sq_nonneg x) (by norm_num)
  dsimp [realMap]
  constructor <;> linarith

private theorem step_pos {κ x a b l u : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000))
    (hx : x ∈ Icc a b) (ha : 0 ≤ a)
    (hl : l ≤ 1-(17904/10000)*b^2) (hu : 1-(17903/10000)*a^2 ≤ u) :
    realMap κ x ∈ Icc l u :=
  step_sq hk ⟨pow_le_pow_left₀ ha hx.1 2,
    pow_le_pow_left₀ (ha.trans hx.1) hx.2 2⟩ (sq_nonneg a) hl hu

private theorem step_neg {κ x a b l u : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000))
    (hx : x ∈ Icc a b) (hb : b ≤ 0)
    (hl : l ≤ 1-(17904/10000)*a^2) (hu : 1-(17903/10000)*b^2 ≤ u) :
    realMap κ x ∈ Icc l u := by
  have hs : b^2 ≤ x^2 ∧ x^2 ≤ a^2 := by
    constructor
    · simpa only [neg_sq] using
        pow_le_pow_left₀ (neg_nonneg.mpr hb) (neg_le_neg hx.2) 2
    · simpa only [neg_sq] using
        pow_le_pow_left₀ (neg_nonneg.mpr (hx.2.trans hb)) (neg_le_neg hx.1) 2
  exact step_sq hk hs (sq_nonneg b) hl hu

structure EndpointBounds (κ s : ℝ) : Prop where
  q1 : realOrbit κ (qEndpoint s) 1 ∈ Icc (153756/1000000) (163622/1000000)
  q2 : realOrbit κ (qEndpoint s) 2 ∈ Icc (952067/1000000) (957676/1000000)
  q3 : realOrbit κ (qEndpoint s) 3 ∈ Icc (-642054/1000000) (-622784/1000000)
  q4 : realOrbit κ (qEndpoint s) 4 ∈ Icc (261937/1000000) (305615/1000000)
  w1 : realOrbit κ (wEndpoint s) 1 ∈ Icc (-193610/1000000) (-181877/1000000)
  w2 : realOrbit κ (wEndpoint s) 2 ∈ Icc (932887/1000000) (940779/1000000)
  w3 : realOrbit κ (wEndpoint s) 3 ∈ Icc (-584621/1000000) (-558058/1000000)
  w4 : realOrbit κ (wEndpoint s) 4 ∈ Icc (388074/1000000) (442450/1000000)

set_option maxHeartbeats 800000 in
theorem endpoint_orbit_bounds {κ s : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000))
    (hs : s ∈ Icc (1/16) (133/2000)) : EndpointBounds κ s := by
  have q0 : qEndpoint s ∈ Icc (-6875/10000) (-6835/10000) := by
    dsimp [qEndpoint]; constructor <;> linarith [hs.1,hs.2]
  have w0 : wEndpoint s ∈ Icc (-8165/10000) (-8125/10000) := by
    dsimp [wEndpoint]; constructor <;> linarith [hs.1,hs.2]
  have q1 : realOrbit κ (qEndpoint s) 1 ∈ Icc (153756/1000000) (163622/1000000) :=
    step_neg hk q0 (by norm_num) (by norm_num) (by norm_num)
  have q2 : realOrbit κ (qEndpoint s) 2 ∈ Icc (952067/1000000) (957676/1000000) :=
    step_pos hk q1 (by norm_num) (by norm_num) (by norm_num)
  have q3 : realOrbit κ (qEndpoint s) 3 ∈ Icc (-642054/1000000) (-622784/1000000) :=
    step_pos hk q2 (by norm_num) (by norm_num) (by norm_num)
  have q4 : realOrbit κ (qEndpoint s) 4 ∈ Icc (261937/1000000) (305615/1000000) :=
    step_neg hk q3 (by norm_num) (by norm_num) (by norm_num)
  have w1 : realOrbit κ (wEndpoint s) 1 ∈ Icc (-193610/1000000) (-181877/1000000) :=
    step_neg hk w0 (by norm_num) (by norm_num) (by norm_num)
  have w2 : realOrbit κ (wEndpoint s) 2 ∈ Icc (932887/1000000) (940779/1000000) :=
    step_neg hk w1 (by norm_num) (by norm_num) (by norm_num)
  have w3 : realOrbit κ (wEndpoint s) 3 ∈ Icc (-584621/1000000) (-558058/1000000) :=
    step_pos hk w2 (by norm_num) (by norm_num) (by norm_num)
  have w4 : realOrbit κ (wEndpoint s) 4 ∈ Icc (388074/1000000) (442450/1000000) :=
    step_neg hk w3 (by norm_num) (by norm_num) (by norm_num)
  exact ⟨q1,q2,q3,q4,w1,w2,w3,w4⟩

/-- The model's positive fixed point is unique on the whole positive axis. -/
theorem positive_fixed_point {κ : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000)) :
    ∃! α : ℝ, 0 < α ∧ realMap κ α = α := by
  let g : ℝ → ℝ := fun x => realMap κ x-x
  have hl : 0 < g (518/1000) := by dsimp [g,realMap]; nlinarith [hk.2]
  have hu : g (519/1000) < 0 := by dsimp [g,realMap]; nlinarith [hk.1]
  have hc : Continuous g := by dsimp [g,realMap]; fun_prop
  obtain ⟨α,hα,hzero⟩ := intermediate_value_Icc'
    (by norm_num : (518/1000 : ℝ) ≤ 519/1000) hc.continuousOn ⟨hu.le,hl.le⟩
  have he : realMap κ α = α := sub_eq_zero.mp hzero
  have hapos : 0 < α := by linarith [hα.1]
  refine ⟨α,⟨hapos,he⟩,?_⟩
  rintro β ⟨hβpos,hβfix⟩
  have hk0 : 0 < κ := by linarith [hk.1]
  have hfactor : (β-α)*(κ*(β+α)+1)=0 := by
    dsimp [realMap] at he hβfix
    nlinarith [he,hβfix]
  have hpos : 0 < κ*(β+α)+1 := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hpos))

theorem positive_fixed_point_bracket {κ α : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000))
    (hα : 0 < α) (hfix : realMap κ α = α) :
    α ∈ Ioo (518/1000 : ℝ) (519/1000) := by
  have hk0 : 0 < κ := by linarith [hk.1]
  have hf : κ*α^2+α=1 := by dsimp [realMap] at hfix; linarith
  constructor
  · by_contra hh
    have hle : α ≤ (518/1000 : ℝ) := le_of_not_gt hh
    have hs := pow_le_pow_left₀ hα.le hle 2
    have hm := mul_le_mul hk.2 hs (sq_nonneg α) (by norm_num)
    nlinarith only [hf,hle,hm]
  · by_contra hh
    have hle : (519/1000 : ℝ) ≤ α := le_of_not_gt hh
    have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 519/1000) hle 2
    have hm := mul_le_mul hk.1 hs (by norm_num) hk0.le
    nlinarith only [hf,hle,hm]

/-- These are exactly the real cut tests in the source's `other_gates`:
the initial endpoints, both first and second images, and the retained
q-side third and fourth images. They are not finite prime-end labels. -/
def EndpointGates (κ s α : ℝ) : Prop :=
  qEndpoint s ∈ Ioo (criticalOrbit κ 5) (-α) ∧
  wEndpoint s ∈ Ioo (-criticalOrbit κ 4) (criticalOrbit κ 2) ∧
  realOrbit κ (qEndpoint s) 1 ∈ Ioo (criticalOrbit κ 6) α ∧
  realOrbit κ (wEndpoint s) 1 ∈ Ioo (-α) (criticalOrbit κ 3) ∧
  realOrbit κ (qEndpoint s) 2 ∈ Ioo (-criticalOrbit κ 2) (criticalOrbit κ 4) ∧
  realOrbit κ (wEndpoint s) 2 ∈ Ioo (-criticalOrbit κ 2) (criticalOrbit κ 4) ∧
  realOrbit κ (qEndpoint s) 3 ∈ Ioo (criticalOrbit κ 5) (-α) ∧
  realOrbit κ (qEndpoint s) 4 ∈ Ioo (criticalOrbit κ 6) α

theorem complete_endpoint_gates {κ s α : ℝ}
    (hk : κ ∈ parameterInterval) (hz : relation κ = 0)
    (hs : s ∈ Icc (1/16) (133/2000))
    (hα : 0 < α) (hfix : realMap κ α = α) : EndpointGates κ s α := by
  have e := endpoint_orbit_bounds hk hs
  have a := positive_fixed_point_bracket hk hα hfix
  obtain ⟨h3l,h3u,h4l,h4u⟩ := parameter_orbit_bounds hk
  have h4 : criticalOrbit κ 4 ∈ Icc (9748/10000) (9751/10000) := ⟨h4l.le,h4u.le⟩
  have h5 : criticalOrbit κ 5 ∈ Icc (-703/1000) (-700/1000) :=
    step_pos hk h4 (by norm_num) (by norm_num) (by norm_num)
  have h2 : criticalOrbit κ 2 = 1-κ := by norm_num [criticalOrbit,Q]
  have h6 : criticalOrbit κ 6 = -criticalOrbit κ 3 := by dsimp [relation] at hz; linarith
  dsimp [EndpointGates,qEndpoint,wEndpoint]
  rw [h2,h6]
  rcases e with ⟨q1,q2,q3,q4,w1,w2,_,_⟩
  rcases a with ⟨al,au⟩
  rcases h5 with ⟨h5l,h5u⟩
  rcases hk with ⟨kl,ku⟩
  rcases hs with ⟨sl,su⟩
  rcases q1 with ⟨q1l,q1u⟩; rcases q2 with ⟨q2l,q2u⟩
  rcases q3 with ⟨q3l,q3u⟩; rcases q4 with ⟨q4l,q4u⟩
  rcases w1 with ⟨w1l,w1u⟩; rcases w2 with ⟨w2l,w2u⟩
  dsimp [qEndpoint,wEndpoint] at q1l q1u q2l q2u q3l q3u q4l q4u w1l w1u w2l w2u
  repeat' constructor <;> linarith

private theorem disk_step {κ a r A : ℝ} {z : ℂ}
    (hk : 0 ≤ κ) (hr : 0 ≤ r) (ha : |a| ≤ A) (hz : ‖z-(a:ℂ)‖ ≤ r) :
    ‖complexMap κ z-(realMap κ a : ℂ)‖ ≤ κ*r*(r+2*A) := by
  have hid : complexMap κ z-(realMap κ a : ℂ) =
      -(κ:ℂ)*(z-(a:ℂ))*(z+(a:ℂ)) := by
    simp only [complexMap,realMap,Complex.ofReal_sub,Complex.ofReal_one,
      Complex.ofReal_mul,Complex.ofReal_pow]
    ring
  have hsum : ‖z+(a:ℂ)‖ ≤ r+2*A := by
    calc
      ‖z+(a:ℂ)‖ = ‖(z-(a:ℂ))+((a:ℂ)+(a:ℂ))‖ := by congr 1; ring
      _ ≤ ‖z-(a:ℂ)‖+(‖(a:ℂ)‖+‖(a:ℂ)‖) :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ r+2*A := by simp only [Complex.norm_real,Real.norm_eq_abs]; linarith
  rw [hid,norm_mul,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hk]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hz hk) hsum (norm_nonneg _)
    (mul_nonneg hk hr)

private theorem center_bounds {κ : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000)) :
    realOrbit κ (-3/4) 1 ∈ Icc (-71/10000) (-7043/1000000) ∧
    realOrbit κ (-3/4) 2 ∈ Icc (999909/1000000) (999912/1000000) ∧
    realOrbit κ (-3/4) 3 ∈ Icc (-790085/1000000) (-789974/1000000) ∧
    realOrbit κ (-3/4) 4 ∈ Icc (-117630/1000000) (-117252/1000000) := by
  have h0 : (-3/4 : ℝ) ∈ Icc (-3/4) (-3/4) := ⟨le_rfl,le_rfl⟩
  have h1 : realOrbit κ (-3/4) 1 ∈ Icc (-71/10000) (-7043/1000000) :=
    step_neg hk h0 (by norm_num) (by norm_num) (by norm_num)
  have h2 : realOrbit κ (-3/4) 2 ∈ Icc (999909/1000000) (999912/1000000) :=
    step_neg hk h1 (by norm_num) (by norm_num) (by norm_num)
  have h3 : realOrbit κ (-3/4) 3 ∈ Icc (-790085/1000000) (-789974/1000000) :=
    step_pos hk h2 (by norm_num) (by norm_num) (by norm_num)
  have h4 : realOrbit κ (-3/4) 4 ∈ Icc (-117630/1000000) (-117252/1000000) :=
    step_neg hk h3 (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h1,h2,h3,h4⟩

/-- All three intermediate disk centers retain the real central selector. -/
theorem central_selector_bounds {κ : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000))
    {n : ℕ} (hn : n ∈ Icc 1 3) :
    realOrbit κ (-3/4) n ∈ Ioo (-1) 1 := by
  obtain ⟨c1,c2,c3,_⟩ := center_bounds hk
  rcases hn with ⟨hnl,hnu⟩
  interval_cases n <;> constructor <;> linarith [c1.1,c1.2,c2.1,c2.2,c3.1,c3.2]

private theorem disk_consequences {z : ℂ} {a r A : ℝ}
    (hz : ‖z-(a:ℂ)‖ ≤ r) (ha : |a| ≤ A) :
    ‖z‖ ≤ r+A ∧ a-r ≤ z.re ∧ z.re ≤ a+r := by
  have hre := (Complex.abs_re_le_norm (z-(a:ℂ))).trans hz
  have hre' : |z.re-a| ≤ r := by simpa using hre
  have hnorm : ‖z‖ ≤ r+A := by
    calc
      ‖z‖ = ‖(z-(a:ℂ))+(a:ℂ)‖ := by congr 1; ring
      _ ≤ ‖z-(a:ℂ)‖+‖(a:ℂ)‖ := norm_add_le _ _
      _ ≤ r+A := by simpa only [Complex.norm_real,Real.norm_eq_abs] using add_le_add hz ha
  exact ⟨hnorm,by linarith [(abs_le.mp hre').1],by linarith [(abs_le.mp hre').2]⟩

/-- The entire closed input disk and all four images stay in the common
disk of radius 23/20. The complete second and third images have opposite
strict real-part signs. This is a whole-support estimate, not sampling. -/
set_option maxHeartbeats 800000 in
theorem whole_support_bounds {κ : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000)) {z : ℂ}
    (hz : z ∈ initialDisk) :
    (∀ n : ℕ, n ≤ 4 → ‖(complexMap κ)^[n] z‖ < (23/20 : ℝ)) ∧
    0 < ((complexMap κ)^[2] z).re ∧ ((complexMap κ)^[3] z).re < 0 := by
  have hk0 : 0 ≤ κ := by linarith [hk.1]
  obtain ⟨c1,c2,c3,c4⟩ := center_bounds hk
  have a0 : |(-3/4 : ℝ)| ≤ 3/4 := by norm_num
  have a1 : |realOrbit κ (-3/4) 1| ≤ 71/10000 := by rw [abs_le]; constructor <;> linarith [c1.1,c1.2]
  have a2 : |realOrbit κ (-3/4) 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [c2.1,c2.2]
  have a3 : |realOrbit κ (-3/4) 3| ≤ 791/1000 := by rw [abs_le]; constructor <;> linarith [c3.1,c3.2]
  have a4 : |realOrbit κ (-3/4) 4| ≤ 119/1000 := by rw [abs_le]; constructor <;> linarith [c4.1,c4.2]
  have d0 : ‖z-((-3/4 : ℝ):ℂ)‖ ≤ (133/2000 : ℝ) := by simpa [initialDisk] using hz
  have d1 : ‖(complexMap κ)^[1] z-(realOrbit κ (-3/4) 1 : ℂ)‖ ≤ (187/1000 : ℝ) := by
    have h := disk_step hk0 (by norm_num) a0 d0
    have hK := mul_le_mul_of_nonneg_right hk.2 (by norm_num : (0 : ℝ) ≤ (133/2000)*((133/2000)+2*(3/4)))
    change ‖complexMap κ z-(realMap κ (-3/4):ℂ)‖ ≤ _
    nlinarith only [h,hK]
  have d2 : ‖(complexMap κ)^[2] z-(realOrbit κ (-3/4) 2 : ℂ)‖ ≤ (68/1000 : ℝ) := by
    have h := disk_step hk0 (by norm_num) a1 d1
    have hK := mul_le_mul_of_nonneg_right hk.2 (by norm_num : (0 : ℝ) ≤ (187/1000)*((187/1000)+2*(71/10000)))
    change ‖complexMap κ ((complexMap κ)^[1] z)-(realMap κ (realOrbit κ (-3/4) 1):ℂ)‖ ≤ _
    nlinarith only [h,hK]
  have d3 : ‖(complexMap κ)^[3] z-(realOrbit κ (-3/4) 3 : ℂ)‖ ≤ (252/1000 : ℝ) := by
    have h := disk_step hk0 (by norm_num) a2 d2
    have hK := mul_le_mul_of_nonneg_right hk.2 (by norm_num : (0 : ℝ) ≤ (68/1000)*((68/1000)+2*1))
    change ‖complexMap κ ((complexMap κ)^[2] z)-(realMap κ (realOrbit κ (-3/4) 2):ℂ)‖ ≤ _
    nlinarith only [h,hK]
  have d4 : ‖(complexMap κ)^[4] z-(realOrbit κ (-3/4) 4 : ℂ)‖ ≤ (83/100 : ℝ) := by
    have h := disk_step hk0 (by norm_num) a3 d3
    have hK := mul_le_mul_of_nonneg_right hk.2 (by norm_num : (0 : ℝ) ≤ (252/1000)*((252/1000)+2*(791/1000)))
    change ‖complexMap κ ((complexMap κ)^[3] z)-(realMap κ (realOrbit κ (-3/4) 3):ℂ)‖ ≤ _
    nlinarith only [h,hK]
  have b0 := disk_consequences d0 a0
  have b1 := disk_consequences d1 a1
  have b2 := disk_consequences d2 a2
  have b3 := disk_consequences d3 a3
  have b4 := disk_consequences d4 a4
  refine ⟨?_,by linarith [b2.2.1,c2.1],by linarith [b3.2.2,c3.2]⟩
  intro n hn
  interval_cases n
  · exact lt_of_le_of_lt b0.1 (by norm_num)
  · exact lt_of_le_of_lt b1.1 (by norm_num)
  · exact lt_of_le_of_lt b2.1 (by norm_num)
  · exact lt_of_le_of_lt b3.1 (by norm_num)
  · exact lt_of_le_of_lt b4.1 (by norm_num)

/-- The deck alternative z=-w is excluded on either strict half-plane. -/
theorem complexMap_injOn_half_planes {κ : ℝ} (hk : κ ≠ 0) :
    InjOn (complexMap κ) {z : ℂ | z.re < 0} ∧
    InjOn (complexMap κ) {z : ℂ | 0 < z.re} := by
  have collision {z w : ℂ} (he : complexMap κ z = complexMap κ w) :
      z=w ∨ z=-w := by
    have hkC : (κ : ℂ) ≠ 0 := by exact_mod_cast hk
    have hm : (κ:ℂ)*(z^2-w^2)=0 := by
      dsimp [complexMap] at he
      linear_combination -he
    have hs := (mul_eq_zero.mp hm).resolve_left hkC
    have hf : (z-w)*(z+w)=0 := by calc
      _ = z^2-w^2 := by ring
      _ = 0 := hs
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  constructor
  · intro z hz w hw he
    change z.re < 0 at hz
    change w.re < 0 at hw
    rcases collision he with h | h
    · exact h
    · have hr := congrArg Complex.re h
      simp only [Complex.neg_re] at hr
      exact (by linarith : False).elim
  · intro z hz w hw he
    change 0 < z.re at hz
    change 0 < w.re at hw
    rcases collision he with h | h
    · exact h
    · have hr := congrArg Complex.re h
      simp only [Complex.neg_re] at hr
      exact (by linarith : False).elim

theorem complete_support_injectivity {κ : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000)) :
    InjOn (complexMap κ) initialDisk ∧
    InjOn (complexMap κ) ((complexMap κ)^[2] '' initialDisk) ∧
    InjOn (complexMap κ) ((complexMap κ)^[3] '' initialDisk) := by
  have hi := complexMap_injOn_half_planes (show κ ≠ 0 by linarith [hk.1])
  refine ⟨hi.1.mono ?_,hi.2.mono ?_,hi.1.mono ?_⟩
  · intro z hz
    have hd : ‖z-((-3/4 : ℝ):ℂ)‖ ≤ (133/2000 : ℝ) := by simpa [initialDisk] using hz
    have h := disk_consequences hd (show |(-3/4 : ℝ)| ≤ 3/4 by norm_num)
    change z.re < 0
    linarith [h.2.2]
  · rintro z ⟨w,hw,rfl⟩
    exact (whole_support_bounds hk hw).2.1
  · rintro z ⟨w,hw,rfl⟩
    exact (whole_support_bounds hk hw).2.2

/-- Restricting the first image to its positive-real side makes all four
model pushes injective. The strict angular crossing test identifies the
selected q-side circle arcs with this subset. -/
theorem selected_side_fourfold_injective {κ : ℝ}
    (hk : κ ∈ Icc (17903/10000) (17904/10000)) :
    InjOn ((complexMap κ)^[4])
      {z : ℂ | z ∈ initialDisk ∧ 0 < (complexMap κ z).re} := by
  have hd := complete_support_injectivity hk
  have hp := (complexMap_injOn_half_planes (show κ ≠ 0 by linarith [hk.1])).2
  intro z hz w hw he
  have h3 : (complexMap κ)^[3] z = (complexMap κ)^[3] w :=
    hd.2.2 ⟨z,hz.1,rfl⟩ ⟨w,hw.1,rfl⟩ he
  have h2 : (complexMap κ)^[2] z = (complexMap κ)^[2] w :=
    hd.2.1 ⟨z,hz.1,rfl⟩ ⟨w,hw.1,rfl⟩ h3
  have h1 : complexMap κ z = complexMap κ w := hp hz.2 hw.2 h2
  exact hd.1 hz.1 hw.1 h1

end
end LimitingCrest
