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

end

end LoopsDepthThreeClosure
