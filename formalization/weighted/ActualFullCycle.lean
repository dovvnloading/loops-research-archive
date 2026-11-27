import UniformThreeReturnRenormalization
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# The full physical cycle behind the three return phases

Separation of the three p-step phases does not by itself give a cycle of
length 3p for the original polynomial. The missing intermediate times
are excluded by a first-return statement on their common physical parent.
The same argument separates all physical phases of every trapped core.
-/

namespace ActualFullCycle

open Set Function
open LimitingCrestQuadraticReturn ThreeReturnDomain ThreeReturnCollar
open ThreeReturnPhysical ThreeReturnParent ThreeReturnRealization
open UniformThreeReturn UniformThreeReturnRenormalization
open FiniteThreeReturnCollars ThreeReturnEstimates NearTwoTip NearTwoShooting
open LimitingCrest

noncomputable section

/-- The parent first-return rule promotes the two separated positive
p-step phases to separation from the target at every time before 3p. -/
theorem three_phase_target_no_early_contact {X : Type*} (f : X → X)
    (S V P : Set X) (p : ℕ) (hVP : V ⊆ P)
    (hphase : ∀ q : ℕ, q ≤ 2 → f^[q*p] '' S ⊆ P)
    (hfirst : ∀ r : ℕ, 0 < r → r < p → Disjoint P (f^[r] '' P))
    (hV1 : Disjoint V (f^[p] '' S))
    (hV2 : Disjoint V (f^[2*p] '' S)) :
    ∀ k : ℕ, 0 < k → k < 3*p → Disjoint V (f^[k] '' S) := by
  have hrem (q r : ℕ) (hq : q ≤ 2) (hr : 0 < r) (hrp : r < p) :
      Disjoint V (f^[q*p+r] '' S) := by
    apply disjoint_left.mpr
    rintro z hz ⟨w, hw, rfl⟩
    apply disjoint_left.mp (hfirst r hr hrp) (hVP hz)
    refine ⟨f^[q*p] w, hphase q hq ⟨w, hw, rfl⟩, ?_⟩
    rw [← iterate_add_apply, Nat.add_comm]
  intro k hk hk3
  by_cases hk1 : k < p
  · simpa using hrem 0 k (by omega) hk hk1
  by_cases hkp : k = p
  · simpa only [hkp] using hV1
  by_cases hk2 : k < 2*p
  · have he : 1*p+(k-p) = k := by omega
    simpa only [he] using hrem 1 (k-p) (by omega) (by omega) (by omega)
  by_cases hk2p : k = 2*p
  · simpa only [hk2p] using hV2
  have he : 2*p+(k-2*p) = k := by omega
  simpa only [he] using hrem 2 (k-2*p) (by omega) (by omega) (by omega)

/-- A first-return parent excludes every intermediate physical time,
while the three supplied return phases exclude the two positive multiples
of p. No invariance of the open source domain is assumed. -/
theorem three_phase_no_early_contact {X : Type*} (f : X → X)
    (S P : Set X) (p : ℕ) (_hp : 0 < p)
    (hphase : ∀ q : ℕ, q ≤ 2 → f^[q*p] '' S ⊆ P)
    (hfirst : ∀ r : ℕ, 0 < r → r < p → Disjoint P (f^[r] '' P))
    (hS1 : Disjoint S (f^[p] '' S))
    (hS2 : Disjoint S (f^[2*p] '' S)) :
    ∀ k : ℕ, 0 < k → k < 3*p → Disjoint S (f^[k] '' S) :=
  three_phase_target_no_early_contact f S S P p
    (by simpa using hphase 0 (by omega)) hphase hfirst hS1 hS2

/-- No early self-contact of the source identifies the exact period
of any actual return-fixed point in that source. -/
theorem exact_period_of_no_early_contact {X : Type*} (f : X → X)
    (S : Set X) (N : ℕ) (hN : 0 < N)
    (hcontact : ∀ k : ℕ, 0 < k → k < N → Disjoint S (f^[k] '' S))
    (a : X) (ha : a ∈ S) (hfixed : f^[N] a = a) :
    minimalPeriod f a = N := by
  have hper : IsPeriodicPt f N a := hfixed
  have hle := hper.minimalPeriod_le hN
  apply le_antisymm hle
  by_contra h
  have hlt : minimalPeriod f a < N := by omega
  have hpos := hper.minimalPeriod_pos hN
  exact disjoint_left.mp (hcontact (minimalPeriod f a) hpos hlt) ha
    ⟨a, ha, iterate_minimalPeriod⟩

/-- Forward invariance under the complete return promotes absence of
source self-contact to pairwise disjointness of every physical phase.
This applies to the filled core, without incorrectly assuming that the
open polynomial-like source is itself forward invariant. -/
theorem full_cycle_disjoint_of_no_early_contact {X : Type*} (f : X → X)
    (S K : Set X) (N : ℕ) (hKS : K ⊆ S)
    (hreturn : MapsTo (f^[N]) K K)
    (hcontact : ∀ k : ℕ, 0 < k → k < N → Disjoint S (f^[k] '' S))
    (i j : ℕ) (hi : i < N) (hj : j < N) (hij : i ≠ j) :
    Disjoint (f^[i] '' K) (f^[j] '' K) := by
  suffices hordered : ∀ a b : ℕ, a < b → b < N →
      Disjoint (f^[a] '' K) (f^[b] '' K) by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hordered i j h hj
    · exact (hordered j i h hi).symm
  intro i j hij hj
  apply disjoint_left.mpr
  rintro z ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
  have hshift := congrArg (f^[N-j]) he
  have heq : f^[N-j+i] a = f^[N] b := by
    simpa only [← iterate_add_apply, Nat.sub_add_cancel hj.le] using hshift.symm
  have hk0 : 0 < N-j+i := by omega
  have hkN : N-j+i < N := by omega
  exact disjoint_left.mp (hcontact (N-j+i) hk0 hkN) (hKS (hreturn hb))
    ⟨a, hKS ha, heq⟩

/-- Separating the target from every early source image separates the
complete open cycle, although the return maps the source onto a larger
target. This does not assume forward invariance of the source. -/
theorem full_open_cycle_disjoint {X : Type*} (f : X → X)
    (S V : Set X) (N : ℕ) (hreturn : MapsTo (f^[N]) S V)
    (hcontact : ∀ k : ℕ, 0 < k → k < N → Disjoint V (f^[k] '' S))
    (i j : ℕ) (hi : i < N) (hj : j < N) (hij : i ≠ j) :
    Disjoint (f^[i] '' S) (f^[j] '' S) := by
  suffices hordered : ∀ a b : ℕ, a < b → b < N →
      Disjoint (f^[a] '' S) (f^[b] '' S) by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hordered i j h hj
    · exact (hordered j i h hi).symm
  intro i j hij hj
  apply disjoint_left.mpr
  rintro z ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
  have hshift := congrArg (f^[N-j]) he
  have heq : f^[N-j+i] a = f^[N] b := by
    simpa only [← iterate_add_apply, Nat.sub_add_cancel hj.le] using hshift.symm
  exact disjoint_left.mp (hcontact (N-j+i) (by omega) (by omega)) (hreturn hb)
    ⟨a, ha, heq⟩

/-- The already established whole-disk phase estimates separate the
target disk from both positive return-phase images of the canonical source.
This is stronger than pairwise separation of the three source phases. -/
theorem selected_target_phase_disjoint {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    Disjoint (Metric.ball (0 : ℂ) (1/6)) (normalizedReturn c p '' source c p) ∧
      Disjoint (Metric.ball (0 : ℂ) (1/6))
        ((normalizedReturn c p)^[2] '' source c p) := by
  have hcanonical := selected_canonical_collar hp hc
  have hsub : source c p ⊆ Metric.ball (0 : ℂ) (1/6) := by
    intro z hz
    have hn : ‖z‖ < 3/20 := by
      simpa using hcanonical.closure_inside (subset_closure hz)
    simpa using (show ‖z‖ < 1/6 by linarith)
  suffices hball : Disjoint (Metric.ball (0 : ℂ) (1/6))
        (normalizedReturn c p '' Metric.ball 0 (1/6)) ∧
      Disjoint (Metric.ball (0 : ℂ) (1/6))
        ((normalizedReturn c p)^[2] '' Metric.ball 0 (1/6)) by
    exact ⟨hball.1.mono_right (image_mono hsub),
      hball.2.mono_right (image_mono hsub)⟩
  rcases hc with ⟨hp16, hc⟩ | ⟨hp17, hc⟩
  · have hz0 : ‖(0 : ℂ)‖ ≤ 1/6 := by norm_num
    have h := separated_phase_images (normalizedReturn c p)
      (criticalValue c (2*p)/criticalValue c p)
      (by simpa only [neg_div] using (finite_phase_bounds hp hp16 hc hz0).2.2)
      (fun z hz => ⟨(finite_phase_bounds hp hp16 hc hz).1,
        (finite_phase_bounds hp hp16 hc hz).2.1⟩)
    exact ⟨h.1, h.2.1⟩
  · have h := separated_phase_images (normalizedReturn c p) (1-kappa p c)
      (by
        have hk := hc.2.2.2.1
        change 17903/10000 ≤ kappa p c ∧ kappa p c ≤ 17904/10000 at hk
        constructor <;> linarith)
      (by
        intro z hz
        have hb := actual_phase_bounds hp17 hc hz
        exact ⟨by linarith [hb.1], hb.2.1⟩)
    exact ⟨h.1, h.2.1⟩

/-- The physical target disk has no contact with either positive
p-step source phase, at the literal physical scale. -/
theorem actual_target_phase_disjoint {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    Disjoint (physicalTarget c p)
        (((quadraticMap c)^[p]) '' physicalSource c p) ∧
      Disjoint (physicalTarget c p)
        (((quadraticMap c)^[2*p]) '' physicalSource c p) := by
  have hd := (selected_critical_data hp hc).1
  have hnorm := selected_target_phase_disjoint hp hc
  have htransfer (q : ℕ)
      (hsep : Disjoint (Metric.ball (0 : ℂ) (1/6))
        ((normalizedReturn c p)^[q] '' source c p)) :
      Disjoint (physicalTarget c p)
        (((quadraticMap c)^[q*p]) '' physicalSource c p) := by
    apply disjoint_left.mpr
    rintro z hz ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    have hvalue : ‖((quadraticMap c)^[q*p]) ((criticalValue c p : ℂ)*u)‖ <
        criticalValue c p/6 := by simpa [physicalTarget] using hz
    rw [← normalized_iterate_scale c p hd.ne' q u, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd] at hvalue
    have hsmall : ‖((normalizedReturn c p)^[q]) u‖ < 1/6 := by nlinarith
    exact disjoint_left.mp hsep (by simpa using hsmall) ⟨u, hu, rfl⟩
  exact ⟨by simpa using htransfer 1 (by simpa using hnorm.1),
    htransfer 2 hnorm.2⟩

/-- The actual signed critical endpoint belongs to the canonical
physical source and is fixed by the complete 3p-th polynomial iterate.
The parameter is the same one used by the constructed collar. -/
theorem actual_signed_tip_mem_and_fixed {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c) :
    -(((quadraticMap c)^[3*p]) 0) ∈ physicalSource c p ∧
      ((quadraticMap c)^[3*p]) (-(((quadraticMap c)^[3*p]) 0)) =
        -(((quadraticMap c)^[3*p]) 0) := by
  have hcollar := selected_uniform_collar hp hc
  have hcanonical := hcollar.toCanonicalCollar
  have hd := hcanonical.scale_pos.ne'
  have htrace := critical_signed_orbit c p (by omega) hd hcollar.critical_relation
  have htrap := critical_orbit_trapped c p (by omega) hcanonical
    hcollar.critical_relation (@selected_collision_iff p hp c hc)
  have hscale : (criticalValue c p : ℂ) * threeReturn c p 0 =
      ((quadraticMap c)^[3*p]) 0 := by
    simpa only [mul_zero, threeReturn] using normalized_iterate_scale c p hd 3 (0 : ℂ)
  have htip : (criticalValue c p : ℂ) * (-threeReturn c p 0) =
      -(((quadraticMap c)^[3*p]) 0) := by rw [mul_neg, hscale]
  refine ⟨⟨-threeReturn c p 0, htrap.2.1, htip⟩, ?_⟩
  calc
    ((quadraticMap c)^[3*p]) (-(((quadraticMap c)^[3*p]) 0)) =
        ((quadraticMap c)^[3*p]) ((criticalValue c p : ℂ) * (-threeReturn c p 0)) :=
      congrArg ((quadraticMap c)^[3*p]) htip.symm
    _ = (criticalValue c p : ℂ) * threeReturn c p (-threeReturn c p 0) :=
      (normalized_iterate_scale c p hd 3 (-threeReturn c p 0)).symm
    _ = (criticalValue c p : ℂ) * (-threeReturn c p 0) := by rw [htrace.2]
    _ = -(((quadraticMap c)^[3*p]) 0) := htip

/-- With intermediate times excluded on the literal physical parent,
the entire canonical source has no return contact before time 3p. -/
theorem actual_source_no_early_contact {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c)
    (hfirst : ∀ r : ℕ, 0 < r → r < p →
      Disjoint (physicalParentSource c p)
        (((quadraticMap c)^[r]) '' physicalParentSource c p)) :
    ∀ k : ℕ, 0 < k → k < 3*p →
      Disjoint (physicalSource c p) (((quadraticMap c)^[k]) '' physicalSource c p) := by
  have hphysical := selected_physical_renormalization hp hc
  exact three_phase_no_early_contact (quadraticMap c) (physicalSource c p)
    (physicalParentSource c p) p (by omega) hphysical.parent.physical_phase_subset
    hfirst hphysical.physical_phase_disjoint.1 hphysical.physical_phase_disjoint.2.1

/-- The signed endpoint has exact period 3p for the original quadratic,
not only period three for a p-th return map. -/
theorem actual_signed_tip_minimalPeriod {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c)
    (hfirst : ∀ r : ℕ, 0 < r → r < p →
      Disjoint (physicalParentSource c p)
        (((quadraticMap c)^[r]) '' physicalParentSource c p)) :
    minimalPeriod (quadraticMap c) (-(((quadraticMap c)^[3*p]) 0)) = 3*p := by
  have htip := actual_signed_tip_mem_and_fixed hp hc
  exact exact_period_of_no_early_contact (quadraticMap c) (physicalSource c p)
    (3*p) (by omega) (actual_source_no_early_contact hp hc hfirst) _ htip.1 htip.2

/-- Every pair of distinct physical phase domains before the complete
return is disjoint. The source is the full canonical open component,
with no further shrinking or replacement by a finite orbit. -/
theorem actual_full_open_cycle_disjoint {p : ℕ} (hp : 3 ≤ p) {c : ℝ}
    (hc : SelectedParameter p c)
    (hfirst : ∀ r : ℕ, 0 < r → r < p →
      Disjoint (physicalParentSource c p)
        (((quadraticMap c)^[r]) '' physicalParentSource c p))
    (i j : ℕ) (hi : i < 3*p) (hj : j < 3*p) (hij : i ≠ j) :
    Disjoint (((quadraticMap c)^[i]) '' physicalSource c p)
      (((quadraticMap c)^[j]) '' physicalSource c p) := by
  have hphysical := selected_physical_renormalization hp hc
  have hsep := actual_target_phase_disjoint hp hc
  have hcontact := three_phase_target_no_early_contact (quadraticMap c)
    (physicalSource c p) (physicalTarget c p) (physicalParentSource c p) p
    (fun _ hz => hphysical.target_closure_in_parent (subset_closure hz))
    hphysical.parent.physical_phase_subset hfirst hsep.1 hsep.2
  apply full_open_cycle_disjoint (quadraticMap c) (physicalSource c p)
    (physicalTarget c p) (3*p) ?_ hcontact i j hi hj hij
  intro z hz
  rw [← physical_return_image hphysical.collar.toCanonicalCollar]
  exact ⟨z, hz, rfl⟩

end
end ActualFullCycle
