import AnnularVariationalResponse
import AnnularResponseClock
import Mathlib.Data.List.Range
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Terminal independence for arbitrarily welded annular chains

Layers are listed from the observed boundary to the terminal boundary.
Each layer eliminates its entire distal trace after an arbitrary linear
welding. The comparison radius depends only on the product of the squared
collar radii. Terminal loads and weldings need no common comparison bound.

The infinite-depth conclusion uses a vanishing product, equivalently the
divergence of accumulated positive logarithmic lengths. It does not require
summability of the individual attenuation factors. These chain theorems are
applications of the nonlinear variational contraction theorem.
-/

namespace AnnularWeldedChain

open Filter
open scoped Topology ENNReal BigOperators
open AnnularModeContraction AnnularVariationalResponse AnnularResponseClock

noncomputable section

/-- One collar, followed on its distal side by an arbitrary linear welding. -/
structure Layer (ι : Type*) where
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  radius_lt_one : radius < 1
  attenuation : ι → ℝ
  attenuation_nonneg : ∀ i, 0 ≤ attenuation i
  attenuation_le : ∀ i, attenuation i ≤ radius
  welding : Trace ι →ₗ[ℝ] Trace ι

def Layer.apply {ι : Type*} (l : Layer ι) (B : Load ι) : Load ι :=
  responseLoad l.attenuation (weld l.welding B)

/-- The head of the list is the layer nearest the observed boundary. -/
def chain {ι : Type*} : List (Layer ι) → Load ι → Load ι
  | [], B => B
  | l :: ls, B => l.apply (chain ls B)

def chainProduct {ι : Type*} : List (Layer ι) → ℝ
  | [] => 1
  | l :: ls => l.radius ^ 2 * chainProduct ls

theorem chainProduct_nonneg {ι : Type*} (ls : List (Layer ι)) :
    0 ≤ chainProduct ls := by
  induction ls with
  | nil => norm_num [chainProduct]
  | cons l ls ih => exact mul_nonneg (sq_nonneg l.radius) ih

theorem chainProduct_le_one {ι : Type*} (ls : List (Layer ι)) :
    chainProduct ls ≤ 1 := by
  induction ls with
  | nil => simp [chainProduct]
  | cons l ls ih =>
    have hr : l.radius ^ 2 < 1 := by
      have := one_sub_sq_pos l.radius_nonneg l.radius_lt_one
      linarith
    calc
      chainProduct (l :: ls) ≤ l.radius ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ ≤ 1 := by nlinarith

theorem chainProduct_lt_one {ι : Type*} (ls : List (Layer ι))
    (hne : ls ≠ []) : chainProduct ls < 1 := by
  cases ls with
  | nil => exact (hne rfl).elim
  | cons l ls =>
    have hr : l.radius ^ 2 < 1 := by
      have := one_sub_sq_pos l.radius_nonneg l.radius_lt_one
      linarith
    calc
      chainProduct (l :: ls) ≤ l.radius ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (chainProduct_le_one ls) (sq_nonneg _)
      _ < 1 := by nlinarith

private theorem radiusStep_fromProjective {r t : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    radiusStep r (fromProjective t) = fromProjective (r ^ 2 * t) := by
  have ha := fromProjective_one_le ht0 ht1
  calc
    radiusStep r (fromProjective t) =
        fromProjective (projective (radiusStep r (fromProjective t))) :=
      (fromProjective_projective (radiusStep_one_le hr0 hr1 ha)).symm
    _ = fromProjective (r ^ 2 * projective (fromProjective t)) := by
      congr 1
      exact radiusStep_crossRatio hr0 hr1 ha
    _ = fromProjective (r ^ 2 * t) := by rw [projective_fromProjective ht0 ht1]

/-- Every pair of terminal loads becomes comparable after a nonempty chain.
The bound is independent of both terminal loads and of every welding. -/
theorem chain_universal_comparison {ι : Type*} (ls : List (Layer ι)) :
    ls ≠ [] → ∀ B D : Load ι,
      Comparable (fromProjective (chainProduct ls)) (chain ls B) (chain ls D) := by
  induction ls with
  | nil => intro hne; exact (hne rfl).elim
  | cons l ls ih =>
    intro _ B D
    cases ls with
    | nil =>
      simpa only [chain, Layer.apply, chainProduct, mul_one, fromProjective,
        upperFactor, responseLoad] using
        universal_response_comparison l.attenuation_nonneg l.attenuation_le
          l.radius_nonneg l.radius_lt_one (weld l.welding B) (weld l.welding D)
    | cons k ks =>
      have hp0 := chainProduct_nonneg (k :: ks)
      have hp1 := chainProduct_lt_one (k :: ks) (by simp)
      have hc := welded_response_contraction l.attenuation_nonneg l.attenuation_le
        l.radius_nonneg l.radius_lt_one (fromProjective_one_le hp0 hp1)
        l.welding (ih (by simp) B D)
      rw [radiusStep_fromProjective l.radius_nonneg l.radius_lt_one hp0 hp1] at hc
      exact hc

theorem chain_append {ι : Type*} (ls ks : List (Layer ι)) (B : Load ι) :
    chain (ls ++ ks) B = chain ls (chain ks B) := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [List.cons_append, chain, ih]

/-- A common outer prefix erases arbitrary differences in the remaining chains. -/
theorem common_prefix_comparison {ι : Type*}
    (ls ks js : List (Layer ι)) (hne : ls ≠ []) (B D : Load ι) :
    Comparable (fromProjective (chainProduct ls))
      (chain (ls ++ ks) B) (chain (ls ++ js) D) := by
  rw [chain_append, chain_append]
  exact chain_universal_comparison ls hne _ _

def prefixLayers {ι : Type*} (layers : ℕ → Layer ι) (n : ℕ) : List (Layer ι) :=
  (List.range n).map layers

theorem prefixLayers_zero {ι : Type*} (layers : ℕ → Layer ι) :
    prefixLayers layers 0 = [] := rfl

theorem prefixLayers_snoc {ι : Type*} (layers : ℕ → Layer ι) (n : ℕ) :
    prefixLayers layers (n + 1) = prefixLayers layers n ++ [layers n] := by
  simp only [prefixLayers, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem prefixLayers_cons {ι : Type*} (layers : ℕ → Layer ι) (n : ℕ) :
    prefixLayers layers (n + 1) =
      layers 0 :: prefixLayers (fun i => layers (i + 1)) n := by
  simp only [prefixLayers, List.range_succ_eq_map, List.map_cons, List.map_map,
    Function.comp_def, Nat.succ_eq_add_one]

theorem prefixLayers_nonempty {ι : Type*} (layers : ℕ → Layer ι)
    {n : ℕ} (hn : 0 < n) : prefixLayers layers n ≠ [] := by
  cases n with
  | zero => omega
  | succ n => simp only [Nat.succ_eq_add_one, prefixLayers_cons, List.cons_ne_nil, not_false_eq_true]

theorem prefixLayers_append {ι : Type*} (layers : ℕ → Layer ι) (n k : ℕ) :
    prefixLayers layers (n + k) =
      prefixLayers layers n ++ prefixLayers (fun i => layers (n + i)) k := by
  induction k with
  | zero => simp only [Nat.add_zero, prefixLayers_zero, List.append_nil]
  | succ k ih =>
    rw [Nat.succ_eq_add_one, ← Nat.add_assoc, prefixLayers_snoc, ih,
      prefixLayers_snoc, List.append_assoc]

theorem prefixLayers_product {ι : Type*} (layers : ℕ → Layer ι) (n : ℕ) :
    chainProduct (prefixLayers layers n) = prefixProduct (fun i => (layers i).radius) n := by
  induction n generalizing layers with
  | zero => rfl
  | succ n ih =>
    rw [Nat.succ_eq_add_one, prefixLayers_cons, chainProduct, ih]
    simp only [prefixProduct, Finset.prod_range_succ']
    exact mul_comm _ _

theorem prefix_universal_comparison {ι : Type*} (layers : ℕ → Layer ι)
    {n : ℕ} (hn : 0 < n) (B D : Load ι) :
    Comparable (fromProjective (prefixProduct (fun i => (layers i).radius) n))
      (chain (prefixLayers layers n) B) (chain (prefixLayers layers n) D) := by
  rw [← prefixLayers_product]
  exact chain_universal_comparison _ (prefixLayers_nonempty layers hn) B D

/-- The first collar gives a finite cap at every finite-energy observed trace. -/
def outerCap {ι : Type*} (layers : ℕ → Layer ι) (u : Trace ι) : ℝ≥0∞ :=
  ENNReal.ofReal (upperFactor (layers 0).radius) * traceMass u

theorem outerCap_ne_top {ι : Type*} (layers : ℕ → Layer ι) {u : Trace ι}
    (hu : traceMass u ≠ ∞) : outerCap layers u ≠ ∞ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu

theorem prefix_le_outerCap {ι : Type*} (layers : ℕ → Layer ι)
    (n : ℕ) (B : Load ι) (u : Trace ι) :
    chain (prefixLayers layers (n + 1)) B u ≤ outerCap layers u := by
  rw [prefixLayers_cons]
  exact response_upper (layers 0).attenuation_nonneg (layers 0).attenuation_le
    (layers 0).radius_nonneg (layers 0).radius_lt_one _ _

private theorem comparable_abs_sub_toReal {ι : Type*}
    {a : ℝ} (ha : 1 ≤ a) {B D : Trace ι → ℝ≥0∞} (h : Comparable a B D)
    (u : Trace ι) {C : ℝ≥0∞} (hC : C ≠ ∞) (hB : B u ≤ C) (hD : D u ≤ C) :
    |(B u).toReal - (D u).toReal| ≤ (a ^ 2 - 1) * C.toReal := by
  have hBt : B u ≠ ∞ := ne_top_of_le_ne_top hC hB
  have hDt : D u ≠ ∞ := ne_top_of_le_ne_top hC hD
  have hBC := ENNReal.toReal_mono hC hB
  have hDC := ENNReal.toReal_mono hC hD
  have hBD := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDt) (h.2 u)
  have hDB := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBt) (h.1 u)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg a)] at hBD hDB
  have ha2 : 0 ≤ a ^ 2 - 1 := by nlinarith
  have hBC' := mul_le_mul_of_nonneg_left hBC ha2
  have hDC' := mul_le_mul_of_nonneg_left hDC ha2
  apply abs_le.mpr
  constructor <;> nlinarith

/-- A quantitative error determined by the shared outer prefix. -/
def prefixError {ι : Type*} (layers : ℕ → Layer ι) (u : Trace ι) (n : ℕ) : ℝ :=
  ((fromProjective (prefixProduct (fun i => (layers i).radius) (n + 1))) ^ 2 - 1) *
    (outerCap layers u).toReal

theorem prefixError_tendsto_zero {ι : Type*} (layers : ℕ → Layer ι) (u : Trace ι)
    (hp : Tendsto (prefixProduct (fun i => (layers i).radius)) atTop (𝓝 0)) :
    Tendsto (prefixError layers u) atTop (𝓝 0) := by
  have hrad := fromProjective_tendsto_one (hp.comp (tendsto_add_atTop_nat 1))
  have h := ((hrad.pow 2).sub tendsto_const_nhds).mul_const (outerCap layers u).toReal
  have hvalue : Tendsto (prefixError layers u) atTop
      (𝓝 (((1 : ℝ) ^ 2 - 1) * (outerCap layers u).toReal)) := by
    refine Filter.Tendsto.congr (fun n => ?_) h
    simp only [prefixError, Function.comp_apply, Pi.pow_apply, Pi.sub_apply, Pi.mul_apply]
  simpa only [one_pow, sub_self, zero_mul] using hvalue

/-- Two different depths and arbitrary terminal loads are close as soon as
they share a sufficiently deep outer prefix. -/
theorem common_depth_error {ι : Type*} (layers : ℕ → Layer ι) (u : Trace ι)
    (hu : traceMass u ≠ ∞) (n m N : ℕ) (hNn : N ≤ n) (hNm : N ≤ m)
    (B D : Load ι) :
    |(chain (prefixLayers layers (n + 1)) B u).toReal -
      (chain (prefixLayers layers (m + 1)) D u).toReal| ≤ prefixError layers u N := by
  have hn : n + 1 = (N + 1) + (n - N) := by omega
  have hm : m + 1 = (N + 1) + (m - N) := by omega
  have hc : Comparable
      (fromProjective (prefixProduct (fun i => (layers i).radius) (N + 1)))
      (chain (prefixLayers layers (n + 1)) B)
      (chain (prefixLayers layers (m + 1)) D) := by
    rw [hn, hm, prefixLayers_append, prefixLayers_append, ← prefixLayers_product]
    exact common_prefix_comparison _ _ _ (prefixLayers_nonempty layers (by omega)) B D
  exact comparable_abs_sub_toReal
    (fromProjective_one_le (prefixProduct_nonneg _ _)
      (prefixProduct_lt_one _ (fun i => (layers i).radius_nonneg)
        (fun i => (layers i).radius_lt_one) (by omega)))
    hc u (outerCap_ne_top layers hu)
    (prefix_le_outerCap layers n B u) (prefix_le_outerCap layers m D u)

/-- Distal data may change at every truncation depth, with no common bound. -/
theorem terminal_difference_tendsto_zero {ι : Type*} (layers : ℕ → Layer ι)
    (hp : Tendsto (prefixProduct (fun i => (layers i).radius)) atTop (𝓝 0))
    (B D : ℕ → Load ι) (u : Trace ι) (hu : traceMass u ≠ ∞) :
    Tendsto (fun n =>
      |(chain (prefixLayers layers (n + 1)) (B n) u).toReal -
        (chain (prefixLayers layers (n + 1)) (D n) u).toReal|) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (prefixError_tendsto_zero layers u hp)
  · intro n; exact abs_nonneg _
  · intro n; exact common_depth_error layers u hu n n n le_rfl le_rfl (B n) (D n)

/-- The actual response energies form a Cauchy sequence, even when terminal
loads vary without a common bound. This uses different-depth comparison. -/
theorem response_cauchy {ι : Type*} (layers : ℕ → Layer ι)
    (hp : Tendsto (prefixProduct (fun i => (layers i).radius)) atTop (𝓝 0))
    (B : ℕ → Load ι) (u : Trace ι) (hu : traceMass u ≠ ∞) :
    CauchySeq (fun n => (chain (prefixLayers layers (n + 1)) (B n) u).toReal) := by
  apply cauchySeq_of_le_tendsto_0 (prefixError layers u)
  · intro n m N hNn hNm
    simpa only [Real.dist_eq] using common_depth_error layers u hu n m N hNn hNm (B n) (B m)
  · exact prefixError_tendsto_zero layers u hp

def zeroLoad (ι : Type*) : Load ι where
  energy := fun _ => 0
  zero := rfl
  homogeneous := by intros; simp

/-- A single infinite-depth value exists and is independent of every choice
of terminal load at every finite truncation. -/
theorem exists_terminal_independent_limit {ι : Type*} (layers : ℕ → Layer ι)
    (hp : Tendsto (prefixProduct (fun i => (layers i).radius)) atTop (𝓝 0))
    (u : Trace ι) (hu : traceMass u ≠ ∞) :
    ∃ E : ℝ, ∀ B : ℕ → Load ι,
      Tendsto (fun n => (chain (prefixLayers layers (n + 1)) (B n) u).toReal)
        atTop (𝓝 E) := by
  obtain ⟨E, hE⟩ := cauchySeq_tendsto_of_complete
    (response_cauchy layers hp (fun _ => zeroLoad ι) u hu)
  refine ⟨E, fun B => ?_⟩
  have habs := terminal_difference_tendsto_zero layers hp B (fun _ => zeroLoad ι) u hu
  have hneg : Tendsto (fun n =>
      - |(chain (prefixLayers layers (n + 1)) (B n) u).toReal -
        (chain (prefixLayers layers (n + 1)) (zeroLoad ι) u).toReal|)
      atTop (𝓝 0) := by
    have h := habs.neg
    rw [neg_zero] at h
    refine Filter.Tendsto.congr (fun n => ?_) h
    simp only [Pi.neg_apply]
  have hdiff : Tendsto (fun n =>
      (chain (prefixLayers layers (n + 1)) (B n) u).toReal -
        (chain (prefixLayers layers (n + 1)) (zeroLoad ι) u).toReal)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hneg habs
    · intro n; exact neg_abs_le _
    · intro n; exact le_abs_self _
  have hsum : Tendsto
      (fun n => (chain (prefixLayers layers (n + 1)) (B n) u).toReal)
      atTop (𝓝 ((0 : ℝ) + E)) := by
    refine Filter.Tendsto.congr (fun n => ?_) (hdiff.add hE)
    simp only [Pi.add_apply, sub_add_cancel]
  simpa only [zero_add] using hsum

/-- Divergence of accumulated positive logarithmic length suffices. Neither
the statement nor its proof uses summability of individual attenuations. -/
theorem divergent_length_terminal_independent_limit {ι : Type*}
    (layers : ℕ → Layer ι) (L : ℕ → ℝ)
    (hr : ∀ i, (layers i).radius = Real.exp (-L i))
    (hdiv : Tendsto (totalLength L) atTop atTop)
    (u : Trace ι) (hu : traceMass u ≠ ∞) :
    ∃ E : ℝ, ∀ B : ℕ → Load ι,
      Tendsto (fun n => (chain (prefixLayers layers (n + 1)) (B n) u).toReal)
        atTop (𝓝 E) := by
  apply exists_terminal_independent_limit layers _ u hu
  have hfun : (fun i => (layers i).radius) = fun i => Real.exp (-L i) := funext hr
  rw [hfun]
  exact exponential_product_tendsto_zero L hdiv

end

end AnnularWeldedChain
