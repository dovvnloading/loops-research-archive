import TipNativeFiniteJTrichotomy

/-!
Only source finite original W boundary endpoint-angle incidences, vertex
count and O/J wrapping endpoint **count** are kernel-verified. This does
not formalize the analytic KL prime-end boundary, Kahn holomorphic cover
or source naturality/properness theorem.
-/

namespace LoopsFormal.TipNativeFullBoundaryTypes

open LoopsFormal.TipRootedNativeKL

/-- Source's four genuine KL W adjacent-tile J-vertex ray pairs,
in its precise cyclic `eta_i cup xi_(i+1)` convention; last wraps. -/
def originalVertexPairs : List (Nat × Nat) :=
  [(upper ⟨0, by decide⟩, lower ⟨1, by decide⟩),
   (upper ⟨1, by decide⟩, lower ⟨2, by decide⟩),
   (upper ⟨2, by decide⟩, lower ⟨3, by decide⟩),
   (upper ⟨3, by decide⟩, lower ⟨0, by decide⟩)]

theorem exact_original_J_vertex_endpoint_angles :
    originalVertexPairs =
      [(43, 53), (55, 137), (139, 149), (151, 41)] := by
  decide +kernel

theorem four_original_source_vertices :
    originalVertexPairs.length = 4 ∧ originalVertexPairs.Nodup := by
  decide +kernel

/-- Two actual source O/J wrapping joints per universal-cover tile. -/
def sourceWrappingJointPairs : List (Nat × Nat) :=
  (List.range 4).flatMap (fun i => [(i,0), (i,1)])

theorem exactly_eight_original_O_J_wrapping_joint_indices :
    sourceWrappingJointPairs.length = 8 ∧
    sourceWrappingJointPairs.Nodup := by
  decide +kernel

/-- Finite source boundary incidence identity is cyclic on 4 original W
tiles, so the J-vertex after tile 3 meets the xi endpoint of tile 0. -/
theorem cyclic_original_vertex_incidence :
    ∀ i : Fin 4,
      nextTile (nextTile (nextTile (nextTile i))) = i := by
  decide +kernel

#print axioms exact_original_J_vertex_endpoint_angles
#print axioms four_original_source_vertices
#print axioms exactly_eight_original_O_J_wrapping_joint_indices
#print axioms cyclic_original_vertex_incidence

end LoopsFormal.TipNativeFullBoundaryTypes
