import GlobalCrestClassification
import ThreeReturnParent

/-!
# The actual fourth terminal image

The two-sided third-return gate forces the fourth image into the precise
real target interval from the source construction. This completes the real
cut algebra attached to the global radial classification; it does not
identify ideal-boundary markings or proper path classes.
-/

namespace GlobalCrestFinalCut

open Set Function LimitingCrestQuadraticReturn NearTwoTip
open GlobalCrestCrossing GlobalCrestEstimates GlobalCrestClassification
open GlobalCrestSourceGates

noncomputable section

/-- The fourth terminal image is real and lies strictly between the
actual second and fifth critical returns. -/
def fourthTerminalGate {p : ℕ} {c : ℝ} (F : Family p c) (s : ℝ) : Prop :=
  (((normalizedReturn c p)^[4]) (point F s)).im = 0 ∧
    (((normalizedReturn c p)^[4]) (point F s)).re ∈
      Ioo (((normalizedReturn c p)^[2]) 0).re
        (((normalizedReturn c p)^[5]) 0).re

/-- Every retained actual terminal point satisfies the source's final
target cut. Evenness and strict order give exact endpoint images. -/
theorem actual_fourth_terminal_gate {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (1/8)) (hg : terminalGate F s) :
    fourthTerminalGate F s := by
  let H := normalizedReturn c p
  let t := terminal F s
  let a := ((H^[4]) 0).re
  have ha : 0 < a ∧ a < 1 := actual_fourth_critical_bounds hp hc
  have ht : -1 < t ∧ t < -a := hg
  have haD : a ∈ Icc (0 : ℝ) (3/2) := ⟨ha.1.le,by linarith [ha.2]⟩
  have htD : -t ∈ Icc (0 : ℝ) (3/2) := by
    constructor <;> linarith [ht.1,ht.2,ha.1]
  have h1D : (1 : ℝ) ∈ Icc (0 : ℝ) (3/2) := by constructor <;> norm_num
  have hanti := actual_return_real_strictAnti hp hc
  have hlo := hanti htD h1D (show -t < 1 by linarith [ht.1])
  have hup := hanti haD htD (show a < -t by linarith [ht.2])
  have hthree : (H^[3]) (point F s) = (t : ℂ) := by
    apply Complex.ext
    · rfl
    · change (((normalizedReturn c p)^[3]) (point F s)).im = 0
      simpa only [point,radiusProjection_eq hs] using
        F.third_real (by omega) ⟨s,hs⟩
  have hfourth : (H^[4]) (point F s) = H (t : ℂ) := by
    change H ((H^[3]) (point F s)) = _
    rw [hthree]
  have heven : H ((-t : ℝ) : ℂ) = H (t : ℂ) := by
    rw [Complex.ofReal_neg]
    exact ThreeReturnDomain.normalized_return_even c p (by omega) (t : ℂ)
  have hcritical : (H^[4]) 0 = (a : ℂ) := by
    apply Complex.ext
    · rfl
    · change (((normalizedReturn c p)^[4]) 0).im = 0
      have he := actualOrbit_cast c 0 p 4
      simp only [Complex.ofReal_zero] at he
      rw [← he]
      simp only [Complex.ofReal_im]
  have hfirst : H (1 : ℂ) = (H^[2]) 0 := by
    change normalizedReturn c p 1 =
      normalizedReturn c p (normalizedReturn c p 0)
    rw [ThreeReturnParent.normalized_return_zero c p hc.2.1.ne']
  have hfifth : H (a : ℂ) = (H^[5]) 0 := by
    change H (a : ℂ) = H ((H^[4]) 0)
    rw [hcritical]
  change (H ((-t : ℝ) : ℂ)).re > (H (1 : ℂ)).re at hlo
  change (H ((-t : ℝ) : ℂ)).re < (H (a : ℂ)).re at hup
  rw [heven,hfirst] at hlo
  rw [heven,hfifth] at hup
  change ((H^[4]) (point F s)).im = 0 ∧
    ((H^[4]) (point F s)).re ∈ Ioo ((H^[2]) 0).re ((H^[5]) 0).re
  rw [hfourth]
  exact ⟨GlobalCrestCrossing.normalizedReturn_real c t p,hlo,hup⟩

/-- The eight actual q/w tests, both terminal cuts, and the final
fourth-image target cut select the same single initial parent interval. -/
theorem actual_complete_cut_classification {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    ∃ α ∈ Ioo (518/1000 : ℝ) (519/1000),
      normalizedReturn c p (α : ℂ) = (α : ℂ) ∧
      ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000),
        terminal F r = -1 ∧
        StrictAntiOn (terminal F) (Icc (1/16 : ℝ) (1/8)) ∧
        (∀ s ∈ Icc (1/16 : ℝ) (1/8), terminal F s = -1 ↔ s = r) ∧
        Icc (1/16 : ℝ) (parentOuter p) ∩
          {s | ActualEndpointGates c p s α ∧ terminalGate F s ∧
            fourthTerminalGate F s} = Ico (1/16) r := by
  obtain ⟨α,hα,hfixed,r,hr,hzero,hanti,hunique,_,hset,_⟩ :=
    actual_complete_parent_classification hp hc F
  refine ⟨α,hα,hfixed,r,hr,hzero,hanti,hunique,?_⟩
  ext s
  constructor
  · rintro ⟨hs,hq,ht,_⟩
    have hm : s ∈ Icc (1/16 : ℝ) (parentOuter p) ∩
        {s | ActualEndpointGates c p s α ∧ terminalGate F s} := ⟨hs,hq,ht⟩
    rwa [hset] at hm
  · intro hs
    have hm : s ∈ Icc (1/16 : ℝ) (parentOuter p) ∩
        {s | ActualEndpointGates c p s α ∧ terminalGate F s} := by
      rwa [hset]
    exact ⟨hm.1,hm.2.1,hm.2.2,actual_fourth_terminal_gate hp hc F
      ⟨hm.1.1,hm.1.2.trans (parentOuter_bounds hp).2⟩ hm.2.2⟩

end
end GlobalCrestFinalCut
