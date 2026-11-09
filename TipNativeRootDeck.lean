import TipRootedNativeKL

/-!
Actual original G-stage KL W seam anchors and their one-deck translates
on the remaining **genuine** finite xi/eta J-sides.

Kernel scope: exact finite rational inequalities. The infinite deck
monodromy, source prime-end convergence, and holomorphic covering escape
are proved in the companion research note, NOT formalized here.
-/

namespace LoopsFormal.TipNativeRootDeck

open LoopsFormal.TipRootedNativeKL

/-- Each authentic anchor is strictly inside its original W open gluing seam. -/
theorem all_source_anchor_angles_strict_in_W_seams :
    ∀ i : Fin 4, ∀ e : Fin 2,
      lower i * 112 < coarse i e * 192 ∧
      coarse i e * 192 < upper i * 112 :=
  all_eight_in_original_W_open_seams

/-- Actual source angular representatives are strictly between 0 and 1. -/
theorem own_seam_anchors_between_zero_and_one :
    ∀ i : Fin 4, ∀ e : Fin 2,
      0 < coarse i e ∧ coarse i e < 112 := by
  decide +kernel

/-- After subtracting one full native deck turn, each anchor lies
strictly on the ORIGINAL xi_i ideal side, not on its gluing interval.
The inequality is equivalent to (coarse/112)-1 < lower/192. -/
theorem negative_unit_deck_is_on_original_xi :
    ∀ i : Fin 4, ∀ e : Fin 2,
      coarse i e * 192 < (lower i + 192) * 112 := by
  decide +kernel

/-- After adding one full native deck turn, each anchor lies
strictly on the ORIGINAL eta_i ideal side, not on its gluing interval.
The inequality is upper/192 < (coarse/112)+1. -/
theorem positive_unit_deck_is_on_original_eta :
    ∀ i : Fin 4, ∀ e : Fin 2,
      upper i * 112 < (coarse i e + 112) * 192 := by
  decide +kernel

/-- Two separately authenticated source rays in each W tile supply
two distinct K9 prime-end labels before deck translation. -/
theorem two_distinct_fine_anchors_per_original_tile :
    ∀ i : Fin 4,
      fine i ⟨0, by decide⟩ ≠ fine i ⟨1, by decide⟩ :=
  one_tile_cannot_determine_fine_prime_end

/-- The known source 8=>4 cyclic incidence is retained by the cohort. -/
theorem original_adjacent_W_tile_pairing :
    ∀ i : Fin 4,
      fine i ⟨1, by decide⟩ = fine (nextTile i) ⟨0, by decide⟩ :=
  fine_end_pairs_across_adjacent_tiles

#print axioms all_source_anchor_angles_strict_in_W_seams
#print axioms negative_unit_deck_is_on_original_xi
#print axioms positive_unit_deck_is_on_original_eta

end LoopsFormal.TipNativeRootDeck
