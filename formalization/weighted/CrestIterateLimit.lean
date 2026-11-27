import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith

/-!
# Uniform finite-composition control with proved domain containment

The limiting orbit has a compact range strictly inside the approximation
disk. Uniform convergence then forces the actual orbit into that disk
before the next map estimate is used. This avoids postulating the domain
containment that the crest endpoint argument needs to establish.
-/

namespace CrestIterateLimit

open Set Function Filter
open scoped Topology

noncomputable section

theorem eventually_in_disk {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α]
    {F : ℕ → α → ℂ} {f : α → ℂ} {R : ℝ}
    (hf : Continuous f) (hR : ∀ x, ‖f x‖ < R)
    (hconv : TendstoUniformly F f atTop) :
    ∀ᶠ n in atTop, ∀ x, ‖F n x‖ ≤ R := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    hf.norm.continuousOn
  have hε : 0 < R - ‖f x‖ := sub_pos.mpr (hR x)
  filter_upwards [(Metric.tendstoUniformly_iff.mp hconv) (R - ‖f x‖) hε] with n hn
  intro y
  have hdist := hn y
  rw [dist_eq_norm, norm_sub_rev] at hdist
  have hmax : ‖f y‖ ≤ ‖f x‖ := hx (mem_univ y)
  have hnorm : ‖F n y‖ ≤ ‖F n y-f y‖ + ‖f y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (F n y-f y) (f y)
  linarith

theorem compose_uniformly {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α]
    {H : ℕ → ℂ → ℂ} {Q : ℂ → ℂ}
    {Z : ℕ → α → ℂ} {z : α → ℂ} {R : ℝ}
    (hz : Continuous z) (hR : ∀ x, ‖z x‖ < R)
    (hZ : TendstoUniformly Z z atTop)
    (hH : TendstoUniformlyOn H Q atTop {w : ℂ | ‖w‖ ≤ R})
    (hQ : ∀ v w : ℂ, ‖v‖ ≤ R → ‖w‖ ≤ R →
      ‖Q v-Q w‖ ≤ 5*‖v-w‖) :
    TendstoUniformly (fun n x => H n (Z n x)) (fun x => Q (z x)) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he : 0 < ε/6 := by positivity
  filter_upwards [eventually_in_disk hz hR hZ,
    (Metric.tendstoUniformly_iff.mp hZ) (ε/6) he,
    (Metric.tendstoUniformlyOn_iff.mp hH) (ε/6) he] with n hn hzn hhn
  intro x
  have hd := hzn x
  rw [dist_eq_norm, norm_sub_rev] at hd
  have he := hhn (Z n x) (hn x)
  rw [dist_eq_norm, norm_sub_rev] at he
  have hl := hQ (Z n x) (z x) (hn x) (hR x).le
  have ht : ‖H n (Z n x)-Q (z x)‖ ≤
      ‖H n (Z n x)-Q (Z n x)‖ + ‖Q (Z n x)-Q (z x)‖ := by
    simpa only [dist_eq_norm] using
      dist_triangle (H n (Z n x)) (Q (Z n x)) (Q (z x))
  rw [dist_eq_norm, norm_sub_rev]
  linarith

/-- Every finite iterate converges uniformly, and actual intermediate
domain containment follows from the reference orbit and compactness. -/
theorem finite_iterates_uniformly {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α]
    {H : ℕ → ℂ → ℂ} {Q : ℂ → ℂ}
    {Z : ℕ → α → ℂ} {z : α → ℂ} {R : ℝ} (N : ℕ)
    (hz : Continuous z) (hcont : Continuous Q)
    (hR : ∀ m ≤ N, ∀ x, ‖(Q^[m]) (z x)‖ < R)
    (hZ : TendstoUniformly Z z atTop)
    (hH : TendstoUniformlyOn H Q atTop {w : ℂ | ‖w‖ ≤ R})
    (hQ : ∀ v w : ℂ, ‖v‖ ≤ R → ‖w‖ ≤ R →
      ‖Q v-Q w‖ ≤ 5*‖v-w‖) :
    ∀ m ≤ N, TendstoUniformly (fun n x => ((H n)^[m]) (Z n x))
      (fun x => (Q^[m]) (z x)) atTop ∧
      ∀ᶠ n in atTop, ∀ x, ‖((H n)^[m]) (Z n x)‖ ≤ R := by
  intro m
  induction m with
  | zero =>
    intro hm
    simpa using And.intro hZ (eventually_in_disk hz (hR 0 hm) hZ)
  | succ m ih =>
    intro hm
    have hold := (ih (by omega)).1
    have hc : Continuous (fun x => (Q^[m]) (z x)) := (hcont.iterate m).comp hz
    have hnew := compose_uniformly hc (hR m (by omega)) hold hH hQ
    have hc' : Continuous (fun x => (Q^[m+1]) (z x)) :=
      (hcont.iterate (m+1)).comp hz
    have hnew' : TendstoUniformly (fun n x => ((H n)^[m+1]) (Z n x))
        (fun x => (Q^[m+1]) (z x)) atTop := by
      simpa only [iterate_succ_apply'] using hnew
    exact ⟨hnew', eventually_in_disk hc' (hR (m+1) hm) hnew'⟩

end
end CrestIterateLimit
