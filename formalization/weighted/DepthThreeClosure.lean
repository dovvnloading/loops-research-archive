import DepthThreeReal
import DepthThreeRemainder
import DepthThreeGrid
import DepthThreeWidthGrid

/-!
# The remaining twenty-six finite depth-three arithmetic packets

This theorem combines the exhaustively checked grid with its real and
complex interpretation. The conclusion is finite: it does not construct
straightenings, KKL ideal markings, or a uniform infinite-depth bound.
-/

namespace LoopsDepthThreeClosure

open LoopsFormal.Period27 LoopsFormal.DepthThree LoopsFormal.DepthThreeGrid
open LoopsDepthThreeReal LoopsDepthThreeRemainder

noncomputable section

/-- Every missing triple has its own concrete integer packet, complete
finite geometry and width certificates, and a unique actual real root of
the critical collision polynomial in the strict certified chart. -/
theorem remaining_twenty_six_closed (p q r : Nat)
    (hp : p ∈ ([3, 4, 5] : List Nat))
    (hq : q ∈ ([3, 4, 5] : List Nat))
    (hr : r ∈ ([3, 4, 5] : List Nat))
    (hnew : (p, q, r) ≠ (3, 3, 3)) :
    ∃ P ∈ remainingPackets, ∃ w : WidthWitness,
      P.p = p ∧ P.q = q ∧ P.r = r ∧
      RootCertificate gridScale (p * q * r) P.parameter ∧
      GeometryCertificate gridScale P ∧ WidthCertificate gridScale P w ∧
      ∃! c : ℝ, (P.parameter.lo : ℝ) / (gridScale : ℝ) < c ∧
        c < (P.parameter.hi : ℝ) / (gridScale : ℝ) ∧
        collisionPolynomial (p * q * r) c = 0 := by
  obtain ⟨P, hP, hpp, hpq, hpr, hroot, hgeom⟩ :=
    remainingComplete p q r hp hq hr hnew
  have hgrid : P ∈ gridPackets := by
    change P ∈ packet333 :: remainingPackets
    exact List.mem_cons.mpr (Or.inr hP)
  obtain ⟨w, hw⟩ := every_grid_packet_has_width_certificate P hgrid
  exact ⟨P, hP, w, hpp, hpq, hpr, hroot, hgeom, hw,
    certified_unique_real_root hroot⟩

/-- The same validated construction includes the archived `(3,3,3)`
control, so the whole 27-element Cartesian product is covered. -/
theorem complete_depth_three_grid (p q r : Nat)
    (hp : p ∈ ([3, 4, 5] : List Nat))
    (hq : q ∈ ([3, 4, 5] : List Nat))
    (hr : r ∈ ([3, 4, 5] : List Nat)) :
    ∃ P ∈ gridPackets, ∃ w : WidthWitness,
      P.p = p ∧ P.q = q ∧ P.r = r ∧
      GeometryCertificate gridScale P ∧ WidthCertificate gridScale P w ∧
      ∃! c : ℝ, (P.parameter.lo : ℝ) / (gridScale : ℝ) < c ∧
        c < (P.parameter.hi : ℝ) / (gridScale : ℝ) ∧
        collisionPolynomial (p * q * r) c = 0 := by
  obtain ⟨P, hP, hpp, hpq, hpr⟩ := gridComplete p q r hp hq hr
  obtain ⟨hroot, hgeom⟩ := allGridCertificates P hP
  obtain ⟨w, hw⟩ := every_grid_packet_has_width_certificate P hP
  rw [hpp, hpq, hpr] at hroot
  exact ⟨P, hP, w, hpp, hpq, hpr, hgeom, hw, certified_unique_real_root hroot⟩

/-- The finite errors of each grid packet control the actual iterate
through every requested positive time, at every parameter in its closed
chart and every point of the whole complex disk. -/
theorem grid_packet_disk_remainder (P : Packet) (hP : P ∈ gridPackets)
    (c : ℝ)
    (hc : (P.parameter.lo : ℝ) / (gridScale : ℝ) ≤ c ∧
      c ≤ (P.parameter.hi : ℝ) / (gridScale : ℝ))
    (n : Nat) (hn : n ≤ 6 * (P.p * P.q * P.r))
    (r : Ratio) (hr : r.den ≠ 0) (z : ℂ)
    (hz : ‖z‖ ≤ (r.num : ℝ) / (r.den : ℝ))
    (j : Nat) (hj : 1 ≤ j) (hjn : j ≤ n) :
    ‖remainder c j z‖ ≤
      (errorAt (errors gridScale
        (trace gridScale P.parameter (6 * (P.p * P.q * P.r))) r n) j : ℝ) /
          (gridScale : ℝ) := by
  have hS := (allGridCertificates P hP).1.1
  exact errors_sound hS ((realEnclosed_iff hS P.parameter c).mpr hc)
    (6 * (P.p * P.q * P.r)) n hn r hr z hz j hj hjn

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 1024 in
/-- All three certified return circles satisfy the actual strict
quadratic comparison, uniformly for every real parameter in the chart.
The intervals and error bounds are constructed by the finite grid. -/
theorem grid_packet_boundary_comparison (P : Packet) (hP : P ∈ gridPackets)
    (c : ℝ)
    (hc : (P.parameter.lo : ℝ) / (gridScale : ℝ) ≤ c ∧
      c ≤ (P.parameter.hi : ℝ) / (gridScale : ℝ))
    (j : Nat) (r : Ratio)
    (hjr : (j, r) ∈ [(P.p, P.radius1), (P.p * P.q, P.radius2),
      (P.p * P.q * P.r, P.radius3)])
    (z : ℂ) (hz : ‖z‖ = (r.num : ℝ) / (r.den : ℝ)) :
    ‖QuadraticEscape.orbit (c : ℂ) j z -
        (quadraticCoefficient j c : ℂ) * z ^ 2‖ +
        (r.num : ℝ) / (r.den : ℝ) <
      ‖(quadraticCoefficient j c : ℂ) * z ^ 2‖ := by
  have hS := (allGridCertificates P hP).1.1
  let N := 6 * (P.p * P.q * P.r)
  let rows := trace gridScale P.parameter N
  have hg := (allGridCertificates P hP).2
  simp only [GeometryCertificate, geometryCheck, positiveRatio,
    Bool.and_eq_true, decide_eq_true_eq] at hg
  have hperiods : 3 ≤ P.p ∧ 3 ≤ P.q ∧ 3 ≤ P.r := by
    clear_except hg
    tauto
  have hdata :
      (0 < P.radius1.den ∧
        0 < gapNumerator gridScale (rowAt rows P.p)
          (errorAt (errors gridScale rows P.radius1 P.p) P.p) P.radius1) ∧
      (0 < P.radius2.den ∧
        0 < gapNumerator gridScale (rowAt rows (P.p * P.q))
          (errorAt (errors gridScale rows P.radius2 (P.p * P.q)) (P.p * P.q))
          P.radius2) ∧
      (0 < P.radius3.den ∧
        0 < gapNumerator gridScale (rowAt rows (P.p * P.q * P.r))
          (errorAt (errors gridScale rows P.radius3 (P.p * P.q * P.r))
            (P.p * P.q * P.r)) P.radius3) := by
    dsimp only [rows, N]
    clear_except hg
    tauto
  have hp : 0 < P.p := by omega
  have hq : 0 < P.q := by omega
  have hr : 0 < P.r := by omega
  have h12 : P.p ≤ P.p * P.q := Nat.le_mul_of_pos_right P.p hq
  have h23 : P.p * P.q ≤ P.p * P.q * P.r := Nat.le_mul_of_pos_right _ hr
  have h3N : P.p * P.q * P.r ≤ N := by dsimp [N]; omega
  have close (k : Nat) (s : Ratio) (hk : 0 < k) (hkN : k ≤ N)
      (hs : 0 < s.den)
      (hgap : 0 < gapNumerator gridScale (rowAt rows k)
        (errorAt (errors gridScale rows s k) k) s)
      (w : ℂ) (hw : ‖w‖ = (s.num : ℝ) / (s.den : ℝ)) :
      ‖QuadraticEscape.orbit (c : ℂ) k w -
          (quadraticCoefficient k c : ℂ) * w ^ 2‖ +
          (s.num : ℝ) / (s.den : ℝ) <
        ‖(quadraticCoefficient k c : ℂ) * w ^ 2‖ := by
    have hparam := (realEnclosed_iff hS P.parameter c).mpr hc
    have hrow := trace_enclosed hS hparam N k hkN
    have herr := errors_sound hS hparam N k hkN s (ne_of_gt hs) w hw.le k hk le_rfl
    exact positive_margin_quadratic_comparison hS c k (rowAt rows k) hrow
      (errorAt (errors gridScale rows s k) k) s hs hgap w hw herr
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hjr
  rcases hjr with heq | heq | heq
  · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact close P.p P.radius1 hp (h12.trans (h23.trans h3N))
      hdata.1.1 hdata.1.2 z hz
  · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact close (P.p * P.q) P.radius2 (Nat.mul_pos hp hq) (h23.trans h3N)
      hdata.2.1.1 hdata.2.1.2 z hz
  · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact close (P.p * P.q * P.r) P.radius3 (Nat.mul_pos (Nat.mul_pos hp hq) hr)
      h3N hdata.2.2.1 hdata.2.2.2 z hz

end

end LoopsDepthThreeClosure
