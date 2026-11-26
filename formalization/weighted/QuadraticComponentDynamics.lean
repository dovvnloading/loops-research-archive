import QuadraticComponentConjugacy
import BinaryShiftPeriodic
import BinaryShiftExactness

/-!
# Periodic dynamics of actual escaping quadratic components

The coherent component conjugacy transports exact periodic counts and
density from the binary shift to the physical connected-component quotient.
The periodic objects counted here are components, not selected points.
-/

namespace LoopsQuadraticEscapeTree

open Set Function QuadraticEscape LoopsStationaryFiberDynamics
open LoopsCompactBinaryCoding LoopsBinaryShiftPeriodic
open LoopsBinaryShiftExactness

private theorem periodic_iff_of_equiv {X : Type*} (f : X → X)
    (E : X ≃ (ℕ → Fin 2)) (hE : Semiconj E f shift) (x : X) (n : ℕ) :
    IsPeriodicPt f n x ↔ IsPeriodicPt shift n (E x) := by
  constructor
  · intro h
    exact h.map hE
  · intro h
    apply E.injective
    rw [(hE.iterate_right n) x]
    exact h.eq

private def periodicEquiv {X : Type*} (f : X → X)
    (E : X ≃ (ℕ → Fin 2)) (hE : Semiconj E f shift) (n : ℕ) :
    {x : X // IsPeriodicPt f n x} ≃
      {a : ℕ → Fin 2 // IsPeriodicPt shift n a} where
  toFun x := ⟨E x.val, (periodic_iff_of_equiv f E hE x.val n).mp x.property⟩
  invFun a := ⟨E.symm a.val, (periodic_iff_of_equiv f E hE (E.symm a.val) n).mpr
    (by simpa using a.property)⟩
  left_inv x := by apply Subtype.ext; exact E.symm_apply_apply x.val
  right_inv a := by apply Subtype.ext; exact E.apply_symm_apply a.val

/-- There are precisely `2^n` actual filled-set components returned to
themselves by the `n`-th quadratic iterate, for every positive `n`.
Components of smaller period dividing `n` are included in this count. -/
theorem quadratic_component_periodic_card (c : ℂ) (hc : 0 < escape c 0)
    (n : ℕ) (hn : 0 < n) :
    Nat.card {q : ConnectedComponents (quadraticFilled c) //
      IsPeriodicPt (quadraticComponentMap c) n q} = 2^n := by
  obtain ⟨E,hE⟩ := filled_component_conjugacy c hc
  rw [Nat.card_congr (periodicEquiv (quadraticComponentMap c) E.toEquiv hE n)]
  exact shift_periodic_card n hn

/-- Every positive integer occurs as a minimal period of an actual
filled-set component. The conclusion makes no assertion about individual
periodic points inside that component. -/
theorem quadratic_component_has_exact_period (c : ℂ) (hc : 0 < escape c 0)
    (n : ℕ) (hn : 0 < n) :
    ∃ q : ConnectedComponents (quadraticFilled c),
      minimalPeriod (quadraticComponentMap c) q = n := by
  obtain ⟨E,hE⟩ := filled_component_conjugacy c hc
  obtain ⟨a,ha⟩ := shift_has_exact_period n hn
  let q := E.symm a
  have hqa : E q = a := E.apply_symm_apply a
  have hperiod : IsPeriodicPt shift n a := by
    rw [← ha]
    exact isPeriodicPt_minimalPeriod shift a
  have hq : IsPeriodicPt (quadraticComponentMap c) n q :=
    (periodic_iff_of_equiv _ E.toEquiv hE q n).mpr (by rwa [hqa])
  refine ⟨q, Nat.le_antisymm (hq.minimalPeriod_le hn) ?_⟩
  have hpos := hq.minimalPeriod_pos hn
  have hother := (periodic_iff_of_equiv _ E.toEquiv hE q
    (minimalPeriod (quadraticComponentMap c) q)).mp
    (isPeriodicPt_minimalPeriod _ q)
  rw [hqa] at hother
  have hle := hother.minimalPeriod_le hpos
  rwa [ha] at hle

/-- Periodic components are dense in the actual component quotient.
Density is in the quotient topology; this statement does not replace a
component by a point or presume singleton components. -/
theorem quadratic_periodic_components_dense (c : ℂ) (hc : 0 < escape c 0) :
    Dense (periodicPts (quadraticComponentMap c)) := by
  obtain ⟨E,hE⟩ := filled_component_conjugacy c hc
  apply dense_iff_inter_open.mpr
  intro U hU hne
  have hEU : IsOpen (E '' U) := E.isOpenMap U hU
  obtain ⟨a,ha,hap⟩ := shift_periodic_dense.inter_open_nonempty (E '' U) hEU
    (hne.image E)
  obtain ⟨q,hq,rfl⟩ := ha
  obtain ⟨n,hn,hpn⟩ := mem_periodicPts.mp hap
  refine ⟨q,hq,mk_mem_periodicPts hn ?_⟩
  exact (periodic_iff_of_equiv _ E.toEquiv hE q n).mpr hpn

/-- Every nonempty open family of actual components eventually maps onto
the entire component space under every later iterate. -/
theorem quadratic_component_open_eventually_onto (c : ℂ) (hc : 0 < escape c 0)
    (U : Set (ConnectedComponents (quadraticFilled c)))
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ N : ℕ, ∀ n ≥ N, ((quadraticComponentMap c)^[n]) '' U = univ := by
  obtain ⟨E,hE⟩ := filled_component_conjugacy c hc
  exact conjugate_open_eventually_onto (quadraticComponentMap c) E hE U hU hne

/-- The actual component action has the mixing conclusion, even when
only the source family is open and the target family is merely nonempty. -/
theorem quadratic_component_eventual_intersection (c : ℂ) (hc : 0 < escape c 0)
    (U V : Set (ConnectedComponents (quadraticFilled c)))
    (hU : IsOpen U) (hneU : U.Nonempty) (hneV : V.Nonempty) :
    ∃ N : ℕ, ∀ n ≥ N, (((quadraticComponentMap c)^[n]) '' U ∩ V).Nonempty := by
  obtain ⟨E,hE⟩ := filled_component_conjugacy c hc
  exact conjugate_eventual_intersection (quadraticComponentMap c) E hE
    U V hU hneU hneV

end LoopsQuadraticEscapeTree
