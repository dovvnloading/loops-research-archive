import QuadraticParameterInverse

/-!
# Finite-time holomorphic transport of actual quadratic compact cores

The parameter varies over an actual disk. The transported core has the
same terminal image under the specified finite iterate, and each lift is
the unique one in the common source neighborhood. This is a finite-time
lifting statement, with no all-time conjugacy conclusion.
-/

namespace LoopsQuadraticParameterMotion

open Set Function Metric
open QuadraticEscape LoopsTelescopeRamification LoopsQuadraticParameterInverse

noncomputable section

/-- A compact injective critical-free core has a normalized holomorphic
motion on a parameter disk, obtained by uniquely lifting its fixed
terminal image through the actual nearby quadratic iterates. -/
theorem quadratic_compact_finite_time_motion
    (c : ℂ) (n : ℕ) (C W : Set ℂ)
    (hC : IsCompact C) (hW : IsOpen W) (hCW : C ⊆ W)
    (hI : InjOn (orbit c n) C)
    (hcrit : ∀ z ∈ C, ∀ j < n, orbit c j z ≠ 0) :
    ∃ (r : ℝ) (U : Set ℂ) (h : ℂ → ℂ → ℂ),
      0 < r ∧ IsOpen U ∧ C ⊆ U ∧ IsCompact (closure U) ∧ closure U ⊆ W ∧
      AnalyticOnNhd ℂ (fun p : ℂ × ℂ => h p.1 p.2) (ball c r ×ˢ C) ∧
      (∀ z ∈ C, h c z = z) ∧
      (∀ d ∈ ball c r, MapsTo (h d) C U ∧ InjOn (h d) C) ∧
      (∀ d ∈ ball c r, ∀ z ∈ C, orbit d n (h d z) = orbit c n z) ∧
      (∀ d ∈ ball c r, ∀ z ∈ C, ∀ w ∈ U,
        orbit d n w = orbit c n z ↔ w = h d z) ∧
      ∀ d ∈ ball c r, ∀ z ∈ C, AnalyticAt ℂ (fun e => h e z) d := by
  obtain ⟨P, U, V, g, hP, hcP, hU, hCU, hUc, hUW,
      hV, hCV, hga, hbranch, hcore, hder⟩ :=
    quadratic_compact_parameter_inverse_family c n C W hC hW hCW hI hcrit
  obtain ⟨r, hr, hrP⟩ := Metric.mem_nhds_iff.mp (hP.mem_nhds hcP)
  let h : ℂ → ℂ → ℂ := fun d z => g d (orbit c n z)
  have hterminal (z : ℂ) (hz : z ∈ C) : orbit c n z ∈ V := hCV ⟨z, hz, rfl⟩
  have hlift (d : ℂ) (hd : d ∈ ball c r) (z : ℂ) (hz : z ∈ C) :
      orbit d n (h d z) = orbit c n z :=
    (hbranch d (hrP hd)).2.2 (hterminal z hz)
  refine ⟨r, U, h, hr, hU, hCU, hUc, hUW, ?_, ?_, ?_, hlift, ?_, ?_⟩
  · intro p hp
    have horbit : AnalyticAt ℂ (fun q : ℂ × ℂ => orbit c n q.2) p :=
      (orbit_analytic c n p.2).comp analyticAt_snd
    have hpair : AnalyticAt ℂ (fun q : ℂ × ℂ => (q.1, orbit c n q.2)) p :=
      analyticAt_fst.prodMk horbit
    exact (hga (p.1, orbit c n p.2) ⟨hrP hp.1, hterminal p.2 hp.2⟩).comp hpair
  · intro z hz
    exact (hbranch c hcP).2.1 (hCU hz)
  · intro d hd
    refine ⟨fun z hz => (hbranch d (hrP hd)).1 (hterminal z hz), ?_⟩
    intro z hz w hw heq
    apply hI hz hw
    calc
      orbit c n z = orbit d n (h d z) := (hlift d hd z hz).symm
      _ = orbit d n (h d w) := congrArg (orbit d n) heq
      _ = orbit c n w := hlift d hd w hw
  · intro d hd z hz w hw
    constructor
    · intro heq
      calc
        w = g d (orbit d n w) := ((hbranch d (hrP hd)).2.1 hw).symm
        _ = h d z := by rw [heq]
    · intro heq
      rw [heq]
      exact hlift d hd z hz
  · intro d hd z hz
    have hpair : AnalyticAt ℂ (fun e : ℂ => (e, orbit c n z)) d :=
      analyticAt_id.prodMk analyticAt_const
    exact (hga (d, orbit c n z) ⟨hrP hd, hterminal z hz⟩).comp hpair

/-- If the original compact core is connected and nonempty, its motion
is the complete global pullback component of the fixed terminal compact,
through the transported anchor, at every nearby parameter. -/
theorem quadratic_compact_motion_component
    (c : ℂ) (n : ℕ) (C W : Set ℂ) (x : ℂ)
    (hC : IsCompact C) (hconn : IsPreconnected C) (hx : x ∈ C)
    (hW : IsOpen W) (hCW : C ⊆ W)
    (hI : InjOn (orbit c n) C)
    (hcrit : ∀ z ∈ C, ∀ j < n, orbit c j z ≠ 0) :
    ∃ (r : ℝ) (U : Set ℂ) (h : ℂ → ℂ → ℂ),
      0 < r ∧ IsOpen U ∧ C ⊆ U ∧ IsCompact (closure U) ∧ closure U ⊆ W ∧
      (∀ z ∈ C, h c z = z) ∧
      (∀ d ∈ ball c r, ∀ z ∈ C, AnalyticAt ℂ (fun e => h e z) d) ∧
      ∀ d ∈ ball c r,
        InjOn (h d) C ∧
        h d '' C = connectedComponentIn (orbit d n ⁻¹' (orbit c n '' C)) (h d x) := by
  obtain ⟨P, U, V, g, hP, hcP, hU, hCU, hUc, hUW,
      hV, hCV, hga, hbranch, hcore, hder⟩ :=
    quadratic_compact_parameter_inverse_family c n C W hC hW hCW hI hcrit
  obtain ⟨r, hr, hrP⟩ := Metric.mem_nhds_iff.mp (hP.mem_nhds hcP)
  let h : ℂ → ℂ → ℂ := fun d z => g d (orbit c n z)
  have hterminal (z : ℂ) (hz : z ∈ C) : orbit c n z ∈ V := hCV ⟨z, hz, rfl⟩
  refine ⟨r, U, h, hr, hU, hCU, hUc, hUW,
    fun z hz => (hbranch c hcP).2.1 (hCU hz), ?_, ?_⟩
  · intro d hd z hz
    exact (hga (d, orbit c n z) ⟨hrP hd, hterminal z hz⟩).comp d
      (analyticAt_id.prodMk analyticAt_const)
  · intro d hd
    refine ⟨?_, ?_⟩
    · intro z hz w hw heq
      apply hI hz hw
      have hz' := (hbranch d (hrP hd)).2.2 (hterminal z hz)
      have hw' := (hbranch d (hrP hd)).2.2 (hterminal w hw)
      exact hz'.symm.trans ((congrArg (orbit d n) heq).trans hw')
    · have hcomponent := quadratic_inverse_family_compact_component n P U V g hU hga
        hbranch d (hrP hd) (orbit c n '' C)
        (hC.image (LoopsSaturatedTelescope.quadratic_orbit_continuous c n))
        (hconn.image (orbit c n)
          (LoopsSaturatedTelescope.quadratic_orbit_continuous c n).continuousOn)
        hCV (orbit c n x) ⟨x, hx, rfl⟩
      simpa only [h, Set.image_image, Function.comp_def] using hcomponent

end

end LoopsQuadraticParameterMotion
