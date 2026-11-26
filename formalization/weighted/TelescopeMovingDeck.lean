import TelescopeParameterReturn
import TelescopeDeckInvolution

/-!
# A jointly analytic deck involution on the moving actual return domain

Compact one-critical data construct an open connected total domain in
parameter and phase. A single jointly analytic involution pairs every
complete physical return fiber, including the moving critical point.
-/

namespace LoopsTelescopeMovingDeck

open Set Function Filter
open scoped Topology BigOperators
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeCollar LoopsTelescopeUnivalentCollars
open LoopsQuadraticCylinderCensus LoopsQuadraticParameterInverse
open LoopsQuadraticCriticalTrapping LoopsQuadraticInverseOpen
open LoopsTelescopeDeckInvolution

noncomputable section

/-- The total space of selected actual return components. -/
def movingReturnDomain (n : ℕ) (P V : Set ℂ) (ξ : ℂ → ℂ) : Set (ℂ × ℂ) :=
  {p | p.1 ∈ P ∧ p.2 ∈ connectedComponentIn (orbit p.1 n ⁻¹' V) (ξ p.1)}

private theorem total_domain_preconnected (n : ℕ) (P V : Set ℂ) (ξ : ℂ → ℂ)
    (c : ℂ) (hc : c ∈ P) (hP : IsPreconnected P) (hξ : ContinuousOn ξ P)
    (hanchor : ∀ d ∈ P, orbit d n (ξ d) ∈ V) :
    IsPreconnected (movingReturnDomain n P V ξ) := by
  let G := (fun d : ℂ => (d, ξ d)) '' P
  have hG : IsPreconnected G := hP.image _ (continuousOn_id.prodMk hξ)
  have hGsub : G ⊆ movingReturnDomain n P V ξ := by
    rintro p ⟨d, hd, rfl⟩
    exact ⟨hd, mem_connectedComponentIn (hanchor d hd)⟩
  apply isPreconnected_of_forall (c, ξ c)
  intro p hp
  let C := connectedComponentIn (orbit p.1 n ⁻¹' V) (ξ p.1)
  let T := ({p.1} : Set ℂ) ×ˢ C
  have hT : IsPreconnected T := isPreconnected_singleton.prod isPreconnected_connectedComponentIn
  have hTsub : T ⊆ movingReturnDomain n P V ξ := by
    rintro ⟨d,z⟩ ⟨hd,hz⟩
    have he : d = p.1 := mem_singleton_iff.mp hd
    subst d
    exact ⟨hp.1,hz⟩
  have hmeet : (G ∩ T).Nonempty := by
    refine ⟨(p.1,ξ p.1), ⟨p.1,hp.1,rfl⟩, ?_⟩
    exact ⟨by simp, mem_connectedComponentIn (hanchor p.1 hp.1)⟩
  refine ⟨G ∪ T, union_subset hGsub hTsub, ?_, ?_, hG.union' hmeet hT⟩
  · exact Or.inl ⟨c,hc,rfl⟩
  · exact Or.inr ⟨by simp, hp.2⟩

/-- Compact actual one-critical data give one jointly analytic involution
on the open connected total space of the moving full return components.
The unique fixed point is the analytic moving critical anchor, and every
fiber of the actual return is exactly one involution orbit. The same
construction retains properness, compact closures, and analytic degree two. -/
theorem quadratic_parameter_return_deck_family
    (c : ℂ) (a b : ℕ) (K A0 B0 D0 WA WD : Set ℂ) (x : ℂ)
    (hK : IsCompact K) (hKconn : IsPreconnected K)
    (hx0 : orbit c a x = 0) (hv : orbit c b c ∈ K)
    (hD0 : D0 = connectedComponentIn (orbit c b ⁻¹' K) c)
    (hB0 : B0 = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D0) 0)
    (hA0 : A0 = connectedComponentIn (orbit c a ⁻¹' B0) x)
    (hWA : IsOpen WA) (hAWA : A0 ⊆ WA)
    (hWD : IsOpen WD) (hDWD : D0 ⊆ WD)
    (hpinj : InjOn (orbit c a) A0)
    (hpcrit : ∀ z ∈ A0, ∀ j < a, orbit c j z ≠ 0)
    (hrinj : InjOn (orbit c b) D0)
    (hrcrit : ∀ z ∈ D0, ∀ j < b, orbit c j z ≠ 0) :
    ∃ (P V : Set ℂ) (ξ : ℂ → ℂ) (τ : ℂ × ℂ → ℂ),
      IsOpen P ∧ c ∈ P ∧ IsPreconnected P ∧
      IsOpen V ∧ IsPreconnected V ∧ K ⊆ V ∧ IsCompact (closure V) ∧
      AnalyticOnNhd ℂ ξ P ∧ ξ c = x ∧
      IsOpen (movingReturnDomain (a+1+b) P V ξ) ∧
      IsPreconnected (movingReturnDomain (a+1+b) P V ξ) ∧
      AnalyticOnNhd ℂ τ (movingReturnDomain (a+1+b) P V ξ) ∧
      ∀ d ∈ P, orbit d a (ξ d) = 0 ∧ orbit d b d ∈ V ∧
        let A := connectedComponentIn (orbit d (a+1+b) ⁻¹' V) (ξ d)
        ξ d ∈ A ∧ IsOpen A ∧ IsCompact (closure A) ∧ closure A ⊆ WA ∧
        orbit d (a+1+b) '' A = V ∧
        (∃ hmap : MapsTo (orbit d (a+1+b)) A V,
          IsProperMap (MapsTo.restrict (orbit d (a+1+b)) A V hmap)) ∧
        (∀ v ∈ V, (∑ z ∈ localFiber d (a+1+b) A v,
          analyticOrderNatAt (fun w => orbit d (a+1+b) w-v) z) = 2) ∧
        (∀ z ∈ A, τ (d,z) ∈ A ∧ τ (d,τ (d,z)) = z ∧
          orbit d a (τ (d,z)) = -(orbit d a z) ∧
          (τ (d,z) = z ↔ z = ξ d)) ∧
        (∀ z ∈ A, ∀ w ∈ A,
          orbit d (a+1+b) w = orbit d (a+1+b) z ↔ w=z ∨ w=τ (d,z)) ∧
        HasDerivAt (fun z => τ (d,z)) (-1) (ξ d) := by
  have hcD0 : c ∈ D0 := by
    rw [hD0]
    exact mem_connectedComponentIn hv
  have hD0conn : IsPreconnected D0 := by
    rw [hD0]
    exact isPreconnected_connectedComponentIn
  have hD0compact : IsCompact D0 := by
    rw [hD0]
    exact proper_component_compact (orbit c b) (orbit_proper c b) K hK c hv
  have h0B0 : (0 : ℂ) ∈ B0 := by
    rw [hB0]
    exact mem_connectedComponentIn (by simpa using hcD0)
  have hB0conn : IsPreconnected B0 := by
    rw [hB0]
    exact isPreconnected_connectedComponentIn
  have hB0compact : IsCompact B0 := by
    rw [hB0]
    exact proper_component_compact (fun w : ℂ => w^2+c) (orbit_proper c 1)
      D0 hD0compact 0 (by simpa using hcD0)
  have hxB0 : orbit c a x ∈ B0 := hx0.symm ▸ h0B0
  have hxA0 : x ∈ A0 := by
    rw [hA0]
    exact mem_connectedComponentIn hxB0
  have hA0compact : IsCompact A0 := by
    rw [hA0]
    exact proper_component_compact (orbit c a) (orbit_proper c a)
      B0 hB0compact x hxB0
  have hpimage : orbit c a '' A0 = B0 := by
    rw [hA0]
    exact quadratic_compact_component_image c a B0 x hB0compact hB0conn hxB0
      (hA0 ▸ hpinj) (hA0 ▸ hpcrit)
  have hsimage : orbit c b '' D0 = K := by
    rw [hD0]
    exact quadratic_compact_component_image c b K c hK hKconn hv
      (hD0 ▸ hrinj) (hD0 ▸ hrcrit)
  obtain ⟨Pp, Up, Vp, gp, hPp, hcPp, hUp, hAUp, hUpcompact, hUpWA,
      hVp, hpVp, hgpa, hgpbranch, hgpbase, hgpder⟩ :=
    quadratic_compact_parameter_inverse_family c a A0 WA hA0compact hWA hAWA
      hpinj hpcrit
  have hB0Vp : B0 ⊆ Vp := by
    rw [← hpimage]
    exact hpVp
  have h0Vp : (0 : ℂ) ∈ Vp := hB0Vp h0B0
  have hB0full : B0 = (fun w : ℂ => w^2+c) ⁻¹' D0 := by
    rw [hB0]
    exact quadratic_critical_component_eq_preimage c D0 hD0conn hcD0
  obtain ⟨Pt, Vt, hPt, hcPt, hVt, hD0Vt, htrap⟩ :=
    quadratic_full_preimage_parameter_neighborhood c D0 Vp hD0compact hVp
      (by rw [← hB0full]; exact hB0Vp)
  obtain ⟨Ps, Us, Vs, gs, hPs, hcPs, hUs, hDUs, hUscompact, hUsambient,
      hVs, hsVs, hgsa, hgsbranch, hgsbase, hgsder⟩ :=
    quadratic_compact_parameter_inverse_family c b D0 (WD ∩ Vt) hD0compact
      (hWD.inter hVt) (fun z hz => ⟨hDWD hz, hD0Vt hz⟩) hrinj hrcrit
  have hKVs : K ⊆ Vs := by
    rw [← hsimage]
    exact hsVs
  obtain ⟨V, hV, hVconn, hKV, hVcompact, hclV⟩ :=
    connected_precompact_target_neighborhood K Vs hK hKconn (orbit c b c) hv
      hVs hKVs
  have hcriticalContinuous : Continuous (fun d : ℂ => orbit d b d) :=
    (orbit_continuous b).comp (continuous_id.prodMk continuous_id)
  let P0 : Set ℂ := Pp ∩ (Pt ∩ (Ps ∩ (Us ∩ (fun d : ℂ => orbit d b d) ⁻¹' V)))
  have hP0 : IsOpen P0 :=
    hPp.inter (hPt.inter (hPs.inter (hUs.inter (hV.preimage hcriticalContinuous))))
  have hcP0 : c ∈ P0 := ⟨hcPp, hcPt, hcPs, hDUs hcD0, hKV hv⟩
  let P := connectedComponentIn P0 c
  have hP : IsOpen P := hP0.connectedComponentIn
  have hcP : c ∈ P := mem_connectedComponentIn hcP0
  have hPP0 : P ⊆ P0 := connectedComponentIn_subset P0 c
  have hPconn : IsPreconnected P := isPreconnected_connectedComponentIn
  let ξ : ℂ → ℂ := fun d => gp d 0
  have hξ : AnalyticOnNhd ℂ ξ P := by
    intro d hd
    have hd := hPP0 hd
    exact (hgpa (d, 0) ⟨hd.1, h0Vp⟩).comp
      (f := fun e : ℂ => (e, (0 : ℂ))) (x := d)
      (analyticAt_id.prod analyticAt_const)
  have hξc : ξ c = x := by
    change gp c 0 = x
    rw [← hx0]
    exact (hgpbranch c hcPp).2.1 (hAUp hxA0)
  have hfamily (d : ℂ) (hd : d ∈ P) :
      orbit d a (ξ d) = 0 ∧ orbit d b d ∈ V ∧
        let D := connectedComponentIn (orbit d b ⁻¹' V) d
        let B := connectedComponentIn ((fun w : ℂ => w^2+d) ⁻¹' D) 0
        let A := connectedComponentIn (orbit d a ⁻¹' B) (ξ d)
        IsOpen A ∧ IsOpen B ∧ IsOpen D ∧
        IsCompact (closure A) ∧ closure A ⊆ WA ∧
        IsCompact (closure B) ∧ IsCompact (closure D) ∧ closure D ⊆ WD ∧
        B = (fun w : ℂ => w^2+d) ⁻¹' D ∧
        InjOn (orbit d a) (closure A) ∧ InjOn (orbit d b) (closure D) ∧
        A = connectedComponentIn (orbit d (a+1+b) ⁻¹' V) (ξ d) ∧
        orbit d (a+1+b) '' A = V ∧
        (∃ hmap : MapsTo (orbit d (a+1+b)) A V,
          IsProperMap (MapsTo.restrict (orbit d (a+1+b)) A V hmap)) ∧
        (∀ L : Set ℂ, IsCompact L → L ⊆ V →
          IsCompact (A ∩ orbit d (a+1+b) ⁻¹' L)) ∧
        (∀ v ∈ V, (∑ z ∈ localFiber d (a+1+b) A v,
          analyticOrderNatAt (fun w => orbit d (a+1+b) w-v) z) = 2) ∧
        A = gp d '' B ∧ D = gs d '' V ∧
        closure A ⊆ Up ∧ closure D ⊆ Us ∧ closure B ⊆ Vp := by
    have hd := hPP0 hd
    have hdp : d ∈ Pp := hd.1
    have hdt : d ∈ Pt := hd.2.1
    have hds : d ∈ Ps := hd.2.2.1
    have hdUs : d ∈ Us := hd.2.2.2.1
    have hdV : orbit d b d ∈ V := hd.2.2.2.2
    have hξzero : orbit d a (ξ d) = 0 := (hgpbranch d hdp).2.2 h0Vp
    refine ⟨hξzero, hdV, ?_⟩
    let D := connectedComponentIn (orbit d b ⁻¹' V) d
    let B := connectedComponentIn ((fun w : ℂ => w^2+d) ⁻¹' D) 0
    let A := connectedComponentIn (orbit d a ⁻¹' B) (ξ d)
    have hgscont : ContinuousOn (gs d) Vs := by
      intro y hy
      have hsana : AnalyticAt ℂ (gs d) y :=
        (hgsa (d, y) ⟨hds, hy⟩).comp
          (f := fun w : ℂ => (d, w)) (x := y)
          (analyticAt_const.prod analyticAt_id)
      exact hsana.continuousAt.continuousWithinAt
    have hanchor : gs d (orbit d b d) = d := (hgsbranch d hds).2.1 hdUs
    obtain ⟨hDimage, hDopen, hDconn, hDcompact, hDclosure, hDonto, hDI⟩ :=
      quadratic_inverse_open_component d b Us Vs V (gs d) hUs hV hVconn
        hVcompact hclV hgscont (hgsbranch d hds).1
        (hgsbranch d hds).2.1 (hgsbranch d hds).2.2 (orbit d b d) hdV
    have hDimage' : gs d '' V = D := by
      simpa only [D, hanchor] using hDimage
    have hDo : IsOpen D := by simpa only [hDimage'] using hDopen
    have hDc : IsCompact (closure D) := by simpa only [hDimage'] using hDcompact
    have hDclUs : closure D ⊆ Us := by simpa only [hDimage'] using hDclosure
    have hDinj : InjOn (orbit d b) (closure D) := by
      simpa only [hDimage'] using hDI
    have hDWD : closure D ⊆ WD := fun z hz =>
      (hUsambient (subset_closure (hDclUs hz))).1
    have hDVt : closure D ⊆ Vt := fun z hz =>
      (hUsambient (subset_closure (hDclUs hz))).2
    have hdD : d ∈ D := mem_connectedComponentIn hdV
    have hDpreconn : IsPreconnected D := isPreconnected_connectedComponentIn
    have hBfull : B = (fun w : ℂ => w^2+d) ⁻¹' D :=
      quadratic_critical_component_eq_preimage d D hDpreconn hdD
    have hqproper : IsProperMap (fun w : ℂ => w^2+d) := orbit_proper d 1
    have hBo : IsOpen B := (hDo.preimage hqproper.continuous).connectedComponentIn
    have hBconn : IsPreconnected B := isPreconnected_connectedComponentIn
    have h0B : (0 : ℂ) ∈ B := mem_connectedComponentIn (by simpa using hdD)
    have hBclpre : closure B ⊆ (fun w : ℂ => w^2+d) ⁻¹' closure D := by
      apply closure_minimal _ (isClosed_closure.preimage hqproper.continuous)
      intro z hz
      exact subset_closure (connectedComponentIn_subset
        ((fun w : ℂ => w^2+d) ⁻¹' D) 0 hz)
    have hBc : IsCompact (closure B) :=
      (hqproper.isCompact_preimage hDc).of_isClosed_subset isClosed_closure hBclpre
    have hBclVp : closure B ⊆ Vp := fun z hz => htrap d hdt (hDVt (hBclpre hz))
    have hgpcont : ContinuousOn (gp d) Vp := by
      intro y hy
      have hpana : AnalyticAt ℂ (gp d) y :=
        (hgpa (d, y) ⟨hdp, hy⟩).comp
          (f := fun w : ℂ => (d, w)) (x := y)
          (analyticAt_const.prod analyticAt_id)
      exact hpana.continuousAt.continuousWithinAt
    obtain ⟨hAimage, hAopen, hAconn, hAcompact, hAclosure, hAonto, hAI⟩ :=
      quadratic_inverse_open_component d a Up Vp B (gp d) hUp hBo hBconn
        hBc hBclVp hgpcont (hgpbranch d hdp).1
        (hgpbranch d hdp).2.1 (hgpbranch d hdp).2.2 0 h0B
    have hAimage' : gp d '' B = A := hAimage
    have hAo : IsOpen A := by simpa only [hAimage'] using hAopen
    have hAc : IsCompact (closure A) := by simpa only [hAimage'] using hAcompact
    have hAclUp : closure A ⊆ Up := by simpa only [hAimage'] using hAclosure
    have hAinj : InjOn (orbit d a) (closure A) := by
      simpa only [hAimage'] using hAI
    have hAWA' : closure A ⊆ WA := fun z hz =>
      hUpWA (subset_closure (hAclUp hz))
    obtain ⟨hsat, honto, hproper, hdegree⟩ :=
      selected_saturated_return_full_degree d a b A B D V (ξ d) hξzero hV hVconn
        hdV rfl rfl rfl (hAinj.mono subset_closure) (hDinj.mono subset_closure)
    have hproperMap : ∃ hmap : MapsTo (orbit d (a+1+b)) A V,
        IsProperMap (MapsTo.restrict (orbit d (a+1+b)) A V hmap) := by
      rw [hsat]
      refine ⟨fun z hz =>
        connectedComponentIn_subset (orbit d (a+1+b) ⁻¹' V) (ξ d) hz, ?_⟩
      exact orbit_component_proper d (a+1+b) V (ξ d) hV
    exact ⟨hAo, hBo, hDo, hAc, hAWA', hBc, hDc, hDWD, hBfull,
      hAinj, hDinj, hsat, honto, hproperMap, hproper, hdegree,
      hAimage'.symm, hDimage'.symm, hAclUp, hDclUs, hBclVp⟩
  let D (d : ℂ) := connectedComponentIn (orbit d b ⁻¹' V) d
  let B (d : ℂ) := connectedComponentIn ((fun w : ℂ => w^2+d) ⁻¹' D d) 0
  let A (d : ℂ) := connectedComponentIn (orbit d a ⁻¹' B d) (ξ d)
  let τ : ℂ × ℂ → ℂ := fun p => gp p.1 (-(orbit p.1 a p.2))
  have hanchor (d : ℂ) (hd : d ∈ P) : orbit d (a+1+b) (ξ d) ∈ V := by
    have hzero := (hfamily d hd).1
    have he : orbit d (a+1) (ξ d) = d := by
      change (orbit d a (ξ d))^2+d = d
      rw [hzero]
      ring
    rw [quadratic_orbit_add, he]
    exact (hfamily d hd).2.1
  have hdesc (d : ℂ) (hd : d ∈ P) (z : ℂ) :
      z ∈ connectedComponentIn (orbit d (a+1+b) ⁻¹' V) (ξ d) ↔
        z ∈ Up ∧ orbit d (a+1) z ∈ Us ∧ orbit d (a+1+b) z ∈ V := by
    obtain ⟨hzero, hdV, hAo, hBo, hDo, hAc, hAWA', hBc, hDc, hDWD',
      hBfull, hAinj, hDinj, hsat, honto, hproper, hcompact, hdegree,
      hAimage, hDimage, hAclUp, hDclUs, hBclVp⟩ := hfamily d hd
    have hdp := (hPP0 hd).1
    have hds := (hPP0 hd).2.2.1
    rw [← hsat]
    constructor
    · intro hz
      have hu : orbit d a z ∈ B d := connectedComponentIn_subset _ _ hz
      have hw : orbit d (a+1) z ∈ D d := by
        change (orbit d a z)^2+d ∈ D d
        rw [hBfull] at hu
        exact hu
      refine ⟨hAclUp (subset_closure hz), hDclUs (subset_closure hw), ?_⟩
      rw [quadratic_orbit_add]
      exact connectedComponentIn_subset _ _ hw
    · rintro ⟨hzUp, hwUs, hvV⟩
      have hwD : orbit d (a+1) z ∈ D d := by
        rw [hDimage]
        refine ⟨orbit d (a+1+b) z, hvV, ?_⟩
        rw [quadratic_orbit_add]
        exact (hgsbranch d hds).2.1 hwUs
      have huB : orbit d a z ∈ B d := by
        rw [hBfull]
        exact hwD
      rw [hAimage]
      exact ⟨orbit d a z, huB, (hgpbranch d hdp).2.1 hzUp⟩
  have htotalEq : movingReturnDomain (a+1+b) P V ξ =
      Prod.fst ⁻¹' P ∩ (Prod.snd ⁻¹' Up ∩
        ((fun p : ℂ × ℂ => orbit p.1 (a+1) p.2) ⁻¹' Us ∩
          (fun p : ℂ × ℂ => orbit p.1 (a+1+b) p.2) ⁻¹' V)) := by
    ext p
    change (p.1 ∈ P ∧ _) ↔ p.1 ∈ P ∧ _
    constructor
    · intro hp
      exact ⟨hp.1, (hdesc p.1 hp.1 p.2).mp hp.2⟩
    · intro hp
      exact ⟨hp.1, (hdesc p.1 hp.1 p.2).mpr hp.2⟩
  have htotalOpen : IsOpen (movingReturnDomain (a+1+b) P V ξ) := by
    rw [htotalEq]
    exact (hP.preimage continuous_fst).inter
      ((hUp.preimage continuous_snd).inter
        ((hUs.preimage (orbit_continuous (a+1))).inter
          (hV.preimage (orbit_continuous (a+1+b)))))
  have htotalConn : IsPreconnected (movingReturnDomain (a+1+b) P V ξ) :=
    total_domain_preconnected (a+1+b) P V ξ c hcP hPconn hξ.continuousOn hanchor
  have htauAnalytic : AnalyticOnNhd ℂ τ (movingReturnDomain (a+1+b) P V ξ) := by
    intro p hp
    obtain ⟨hzero, hdV, hAo, hBo, hDo, hAc, hAWA', hBc, hDc, hDWD',
      hBfull, hAinj, hDinj, hsat, honto, hproper, hcompact, hdegree,
      hAimage, hDimage, hAclUp, hDclUs, hBclVp⟩ := hfamily p.1 hp.1
    have hzA : p.2 ∈ A p.1 := by rw [hsat]; exact hp.2
    have hu : orbit p.1 a p.2 ∈ B p.1 := connectedComponentIn_subset _ _ hzA
    have hdc : p.1 ∈ D p.1 := mem_connectedComponentIn hdV
    have hneg : -(orbit p.1 a p.2) ∈ B p.1 :=
      quadratic_critical_component_symmetric p.1 (D p.1) hdc _ hu
    have hnegVp := hBclVp (subset_closure hneg)
    have hOrbit : AnalyticAt ℂ (fun q : ℂ × ℂ => orbit q.1 a q.2) p :=
      (quadratic_skew_analytic a p).snd
    exact (hgpa (p.1, -(orbit p.1 a p.2)) ⟨(hPP0 hp.1).1, hnegVp⟩).comp
      (f := fun q : ℂ × ℂ => (q.1, -(orbit q.1 a q.2))) (x := p)
      (analyticAt_fst.prod hOrbit.neg)
  refine ⟨P, V, ξ, τ, hP, hcP, hPconn, hV, hVconn, hKV, hVcompact,
    hξ, hξc, htotalOpen, htotalConn, htauAnalytic, ?_⟩
  intro d hd
  obtain ⟨hzero, hdV, hAo, hBo, hDo, hAc, hAWA', hBc, hDc, hDWD',
    hBfull, hAinj, hDinj, hsat, honto, hproper, hcompact, hdegree,
    hAimage, hDimage, hAclUp, hDclUs, hBclVp⟩ := hfamily d hd
  refine ⟨hzero, hdV, ?_⟩
  have hdD : d ∈ D d := mem_connectedComponentIn hdV
  have h0B : (0 : ℂ) ∈ B d := mem_connectedComponentIn (by simpa using hdD)
  have hxiA : ξ d ∈ A d := mem_connectedComponentIn (by rwa [hzero])
  have hponto : orbit d a '' A d = B d :=
    orbit_component_image d a (B d) hBo isPreconnected_connectedComponentIn
      (ξ d) (by rwa [hzero])
  obtain ⟨τ0, hτ0an, hτ0map, hτ0sq, hτ0prefix, hτ0fixed, hτ0fiber,
    hτ0deriv, hτ0crit⟩ := quadratic_return_analytic_involution d a b (A d) (B d)
      (D d) hdD hAo rfl hponto (hAinj.mono subset_closure) (hDinj.mono subset_closure)
  have hmatch (z : ℂ) (hz : z ∈ A d) : τ (d,z) = τ0 z := by
    have he := (hgpbranch d (hPP0 hd).1).2.1
      (hAclUp (subset_closure (hτ0map hz)))
    rw [hτ0prefix z hz] at he
    exact he
  have hderiv : HasDerivAt (fun z => τ (d,z)) (-1) (ξ d) :=
    (hτ0crit (ξ d) hxiA hzero).congr_of_eventuallyEq
      ((hAo.mem_nhds hxiA).mono fun z hz => hmatch z hz)
  rw [← hsat]
  refine ⟨hxiA, hAo, hAc, hAWA', honto, hproper, hdegree, ?_, ?_, hderiv⟩
  · intro z hz
    have hτz : τ (d,z) ∈ A d := (hmatch z hz).symm ▸ hτ0map hz
    refine ⟨hτz, ?_, ?_, ?_⟩
    · rw [hmatch _ hτz, hmatch z hz]
      exact hτ0sq z hz
    · rw [hmatch z hz]
      exact hτ0prefix z hz
    · rw [hmatch z hz, hτ0fixed z hz]
      constructor
      · intro he
        exact hAinj (subset_closure hz) (subset_closure hxiA) (he.trans hzero.symm)
      · intro he
        rwa [he]
  · intro z hz w hw
    rw [hmatch z hz]
    exact hτ0fiber z hz w hw

end
end LoopsTelescopeMovingDeck
