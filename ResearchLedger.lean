import Std

/-!
# Source-ledger dependency and conditional-hypothesis audit

Generated from the canonical `ledger.json` source lock.
Run `python code/verify_lean_frontier_sync.py` after any ledger edit.

This encodes the status *reported by the research ledger*, NOT a proof of
the 465 mathematical statements. In particular, `.ledgerProved` is a
documentary status and may carry open hypothesis references. Hypotheses
are kept distinct from ordinary dependencies to prevent promotion of a
conditional theorem to an unconditional one.

Nodes are ordered topologically across BOTH dependencies and explicit
hypotheses. Backward-only edges provide a kernel-checked acyclicity
certificate for the mirrored source graph.
-/

namespace LoopsFormal.ResearchLedger

inductive Status where
  | sourceImported
  | ledgerProved
  | openGoal
  deriving BEq, DecidableEq, Inhabited, Repr

structure Claim where
  id : String
  status : Status
  deps : List Nat
  assumptions : List Nat
  deriving Inhabited, Repr

/-- Canonical 2026-07-27 ledger statuses, dependency edges, and
    separately recorded conditional hypothesis edges. -/
def claims : Array Claim := #[
  ⟨"YOCCOZ", .sourceImported, [], []⟩,
  ⟨"BLOT_ROOT", .sourceImported, [], []⟩,
  ⟨"BLOT_NONPARABOLIC_LIMIT_MODULUS_COLLAPSE", .sourceImported, [], []⟩,
  ⟨"FATOU_PARABOLIC_BASIN_CRITICAL_CYCLE", .sourceImported, [], []⟩,
  ⟨"CHERAGHI_SHISHIKURA_QG_MLC", .sourceImported, [], []⟩,
  ⟨"LEVIN_EXPONENTIAL_RENORMALIZATION_MLC", .sourceImported, [], []⟩,
  ⟨"LEVIN_FAST_SMALL_ROTATION_MLC", .sourceImported, [], []⟩,
  ⟨"LEVIN_THEOREM7_SATELLITE_MLC", .sourceImported, [], []⟩,
  ⟨"ELEPHANT_EYES_APRIORI_BOUNDS", .sourceImported, [], []⟩,
  ⟨"KKL_TRANSLATION", .sourceImported, [], []⟩,
  ⟨"KKL_THICK_THIN", .sourceImported, [], []⟩,
  ⟨"KKL_WAD_SUPPORT", .sourceImported, [], []⟩,
  ⟨"KKL_VALUE_CONTRACTION", .sourceImported, [], []⟩,
  ⟨"KKL_OCCUPANCY_TRICHOTOMY", .sourceImported, [], []⟩,
  ⟨"KKL_PARABOLIC_TAME_AMPLIFICATION", .sourceImported, [], []⟩,
  ⟨"KKL_IDEAL_PULLBACK_NATIVE", .sourceImported, [], []⟩,
  ⟨"ALEXANDER_DUALITY_COMPACTA", .sourceImported, [], []⟩,
  ⟨"DL_TRANSITIONAL_PERIPHERAL", .sourceImported, [], []⟩,
  ⟨"DL_TILE_SCALING", .sourceImported, [], []⟩,
  ⟨"LYUBICH_PRINCIPAL_RETURN_MAP", .sourceImported, [], []⟩,
  ⟨"KL_DECORATION_ESCAPE_PUZZLE", .sourceImported, [], []⟩,
  ⟨"KKL_NATIVE_TERMINAL_HUBBARD_TREE", .sourceImported, [], []⟩,
  ⟨"PERIODICALLY_REPELLING_FILLED_JULIA_EMPTY_INTERIOR", .sourceImported, [], []⟩,
  ⟨"PQL_SAME_FILLED_CONTINUUM_QUADRATIC_LIKE_RESTRICTION", .sourceImported, [], []⟩,
  ⟨"DOUADY_HUBBARD_CONNECTED_QUADRATIC_LIKE_STRAIGHTENING", .sourceImported, [], []⟩,
  ⟨"KIWI_MONOTONE_MODEL_FINITE_ORBIT_INJECTIVITY", .sourceImported, [], []⟩,
  ⟨"DOUADY_HUBBARD_QL_EXTERNAL_PRIME_END_EXACTNESS", .sourceImported, [], []⟩,
  ⟨"KKL_FIXED_END_IMMERSION_DECOMPOSITION", .sourceImported, [], []⟩,
  ⟨"KL06_EXTREMAL_WIDTH_SERIES_HOLOMORPHIC_RULES", .sourceImported, [], []⟩,
  ⟨"DL23_ANNULAR_WAVE_BUFFER_EXTRACTION", .sourceImported, [], []⟩,
  ⟨"KKL_LAMINATION_PUSHFORWARD_DEGREE_BOUND", .sourceImported, [], []⟩,
  ⟨"KKL_WAVE_PUSHFORWARD_STATED", .sourceImported, [], []⟩,
  ⟨"DL_NATIVE_RECTIFIABLE_RELATIVE_DISCARD_BOUND", .sourceImported, [], []⟩,
  ⟨"KKL_PRIMITIVE_ROTATION_LIMB_CYCLE_DATA", .sourceImported, [], []⟩,
  ⟨"KKL_TYPED_VALUE_INCIDENCE", .ledgerProved, [], []⟩,
  ⟨"KKL_PRINTED_CLONE_EQUATION_NO_GO", .ledgerProved, [], []⟩,
  ⟨"KKL_CLONE_EIGEN", .ledgerProved, [], []⟩,
  ⟨"REGIME_PARTITION", .ledgerProved, [], []⟩,
  ⟨"UNMARKED_NO_GO", .ledgerProved, [1], []⟩,
  ⟨"BACKWARD_RECORD", .ledgerProved, [], []⟩,
  ⟨"MARKING_QUOTIENT_NO_GO", .ledgerProved, [], []⟩,
  ⟨"TRANSLATION_ORBIT_TYPES", .ledgerProved, [], []⟩,
  ⟨"RELATIVE_TAIL_CONTROL", .ledgerProved, [9], []⟩,
  ⟨"CONE_REDUCTION", .ledgerProved, [], []⟩,
  ⟨"HOMOGENEOUS_LYAPUNOV_REDUCTION", .ledgerProved, [], []⟩,
  ⟨"ERROR_STABLE_LYAPUNOV_REDUCTION", .ledgerProved, [], []⟩,
  ⟨"FORWARD_CONTRACTION_REDUCTION", .ledgerProved, [], []⟩,
  ⟨"GROUPED_BLOCK_CONTRACTION_REDUCTION", .ledgerProved, [46], []⟩,
  ⟨"PRIME_END_RETURN", .ledgerProved, [], []⟩,
  ⟨"CRITICAL_VALUE_PULLBACK", .ledgerProved, [], []⟩,
  ⟨"FULLIFICATION", .ledgerProved, [], []⟩,
  ⟨"GLOBAL_DEGREE_NO_GO", .ledgerProved, [48, 49], []⟩,
  ⟨"DEGREE_TWO_FACTORIZATION", .ledgerProved, [], []⟩,
  ⟨"QUADRATIC_PULLBACK_DICHOTOMY", .ledgerProved, [49], []⟩,
  ⟨"STAGEWISE_FACTORIZATION", .ledgerProved, [53, 52], []⟩,
  ⟨"QL_RETURN_FACTORIZATION", .ledgerProved, [52], []⟩,
  ⟨"FINITE_HORIZON_TRUNCATION", .ledgerProved, [], []⟩,
  ⟨"STAGE_FORWARD_CLOSURE", .ledgerProved, [], []⟩,
  ⟨"RELATIVE_COVER_LIFT", .ledgerProved, [], []⟩,
  ⟨"TOPOLOGY_WIDTH_NO_GO", .ledgerProved, [], []⟩,
  ⟨"INFLATION_MODULUS_MONOTONICITY", .ledgerProved, [], []⟩,
  ⟨"FINITE_LOCAL_SATURATION", .ledgerProved, [53, 52], []⟩,
  ⟨"CONNECTED_EXTERIOR_CALIBRATION", .ledgerProved, [60], []⟩,
  ⟨"WAD_CORRIDOR_SANDWICH", .ledgerProved, [9, 10], []⟩,
  ⟨"COMPLEXITY_COORDINATE_NO_GO", .ledgerProved, [], []⟩,
  ⟨"HARMONIC_LINEAR_NO_GO", .ledgerProved, [], []⟩,
  ⟨"BOUNDED_FANOUT_BOTTLENECK", .ledgerProved, [], []⟩,
  ⟨"ORBIT_PACKING", .ledgerProved, [11], []⟩,
  ⟨"TRANSLATION_DENSITY_IDENTITY", .ledgerProved, [9], []⟩,
  ⟨"SQRT_ERROR_ABSORPTION", .ledgerProved, [], []⟩,
  ⟨"CONDITIONAL_NEUTRAL_CORRIDOR_ABSORPTION", .ledgerProved, [18, 69], []⟩,
  ⟨"COMMON_WIDTH_BRIDGE", .ledgerProved, [], []⟩,
  ⟨"REPLICATION_AMORTIZATION", .ledgerProved, [63], []⟩,
  ⟨"CONGESTION_AMORTIZATION", .ledgerProved, [63], []⟩,
  ⟨"TREE_NERVE_FULLNESS", .ledgerProved, [], []⟩,
  ⟨"TREE_HULL_COMPLEXITY", .ledgerProved, [74], []⟩,
  ⟨"VIRTUAL_LIMB_TREE_BOUND", .ledgerProved, [], []⟩,
  ⟨"VIRTUAL_BRANCH_QUANTIFIER_ASSEMBLY", .ledgerProved, [], []⟩,
  ⟨"ABSTRACT_SECTION4_STATIC_TRICHOTOMY", .ledgerProved, [76], []⟩,
  ⟨"LOCALIZED_CRITICAL_ENCOUNTER_DEGREE", .ledgerProved, [52], []⟩,
  ⟨"LINEAR_MARKING_DENSITY_ABSORPTION", .ledgerProved, [], []⟩,
  ⟨"TAME_VALUE_OBSTRUCTION", .ledgerProved, [], []⟩,
  ⟨"CONDITIONAL_VIRTUAL_TAME_TRANSFER", .ledgerProved, [14, 12, 79, 80, 81], []⟩,
  ⟨"ROTATION_RELABEL_NO_GO", .ledgerProved, [], []⟩,
  ⟨"KKL_WAVE_ATOMIC_SOURCE_OCCURRENCE_MANIFEST", .ledgerProved, [], []⟩,
  ⟨"KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR", .openGoal, [84], []⟩,
  ⟨"FINITE_HORIZON_WAVE_BOUND", .ledgerProved, [], [85]⟩,
  ⟨"DEGREE_TWO_FAST_FORWARD_NO_GO", .ledgerProved, [], []⟩,
  ⟨"N1_PREPRUNING_BOREL_WAVE_ATLAS", .ledgerProved, [], []⟩,
  ⟨"N1_BOREL_RECTIFIABLE_CORE_REDUCTION", .ledgerProved, [88], []⟩,
  ⟨"DL_RELATIVE_DISCARD_FAMILY_BOUND", .ledgerProved, [89, 32], []⟩,
  ⟨"BOREL_WIDTH_ENVELOPE_PRUNING", .ledgerProved, [], []⟩,
  ⟨"KKL_STATIONARY_ONE_RETAINED_CHAIN", .ledgerProved, [], []⟩,
  ⟨"STANDARD_BOREL_ORDERED_WAVE_REALIZATION", .ledgerProved, [88, 90, 91, 92], []⟩,
  ⟨"KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION_ANALYTIC", .ledgerProved, [90, 91, 93, 92], []⟩,
  ⟨"KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION", .ledgerProved, [94], []⟩,
  ⟨"KKL_STATIONARY_MAXIMAL_ONE_SIDED_WINDOW_REDUCTION", .ledgerProved, [], []⟩,
  ⟨"KKL_STATIONARY_CRITICAL_LIMB_INVERSE_BRANCH", .ledgerProved, [33], []⟩,
  ⟨"KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN", .ledgerProved, [21, 33, 97], []⟩,
  ⟨"KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN", .ledgerProved, [21, 97, 98], []⟩,
  ⟨"KKL_STATIONARY_PROOF_USED_PREDECESSOR_SELECTION", .openGoal, [99, 98], []⟩,
  ⟨"FINITE_MARKED_TREE_TERMINAL_PRUNING", .ledgerProved, [], []⟩,
  ⟨"KKL_STATIONARY_SELECTED_ALPHA_PREDECESSOR_CHAIN", .ledgerProved, [97], []⟩,
  ⟨"KKL_STATIONARY_SELECTED_ENDPOINT_CYCLE_AVOIDANCE", .ledgerProved, [33, 102], []⟩,
  ⟨"KKL_STATIONARY_TERMINAL_CRITICAL_LIMB_INVERSE_SHEETS", .ledgerProved, [33, 97, 102], []⟩,
  ⟨"PERIODICALLY_REPELLING_PQL_FILLED_JULIA_EMPTY_INTERIOR", .ledgerProved, [22, 23], []⟩,
  ⟨"KKL_STATIONARY_LC_TERMINAL_SHEET_MCI", .ledgerProved, [101, 21, 99, 103, 104, 105], []⟩,
  ⟨"KKL_STATIONARY_MODEL_TERMINAL_SHEET_INCIDENCE", .ledgerProved, [101, 21, 104], []⟩,
  ⟨"KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT", .openGoal, [21, 107, 99], []⟩,
  ⟨"KKL_STATIONARY_SELECTED_PREDECESSOR_MARKED_COMPONENT_INCIDENCE", .openGoal, [99, 21, 106, 107, 108], []⟩,
  ⟨"KKL_STATIONARY_CRITICAL_LIMB_ORBIT_DISTINCTNESS", .ledgerProved, [21, 33], []⟩,
  ⟨"KKL_STATIONARY_SELECTED_PREDECESSOR_CONTINUUM_SATURATION", .ledgerProved, [21, 33, 99], []⟩,
  ⟨"KKL_STATIONARY_LINE1598_TREE_DISJOINTNESS_REDUCTION", .ledgerProved, [110, 111, 99], [109]⟩,
  ⟨"KKL_STATIONARY_INCOMING_WINDOW_ANCHOR", .openGoal, [96, 99, 100, 109, 112], []⟩,
  ⟨"PQL_STRICT_SYNCHRONIZED_CHAIN_RECONSTRUCTION", .ledgerProved, [], []⟩,
  ⟨"PQL_SEGMENTED_OCCURRENCE_RECONSTRUCTION", .ledgerProved, [114], []⟩,
  ⟨"PQL_ITERATE_FILLED_GRAPH_NATURALITY", .ledgerProved, [23], []⟩,
  ⟨"KKL_STATIONARY_FINITE_EMBEDDED_COLLAR_NATURALITY", .ledgerProved, [116], []⟩,
  ⟨"KKL_STATIONARY_TWO_OCCURRENCE_BINDER", .openGoal, [113, 92, 115, 117], []⟩,
  ⟨"KKL_STATIONARY_RETAINED_PORTION_REALIZATION", .openGoal, [118], []⟩,
  ⟨"KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION", .openGoal, [21, 98, 102, 104], []⟩,
  ⟨"KKL_STATIONARY_MARKED_ACCESS_ITINERARY", .openGoal, [116, 98, 120], []⟩,
  ⟨"KKL_STATIONARY_FINAL_COMPONENT_REALIZATION", .ledgerProved, [116, 55, 98], []⟩,
  ⟨"KKL_STATIONARY_DEGREE_TWO_CORRECTION", .ledgerProved, [122], []⟩,
  ⟨"KKL_STATIONARY_SELECTED_CORRIDOR_CONFINEMENT", .openGoal, [119, 121, 123], []⟩,
  ⟨"KKL_STATIONARY_SELECTED_COLLAR_DECK_NONCOLLISION", .openGoal, [121, 124, 123], []⟩,
  ⟨"KKL_STATIONARY_TWO_SIDED_WAVE_NONCOLLISION", .openGoal, [119, 121, 124, 125, 123], []⟩,
  ⟨"KKL_STATIONARY_POINTWISE_TWO_PATH_BREAK", .openGoal, [126], []⟩,
  ⟨"KKL_STATIONARY_FINAL_FIXED_COMPONENT_EXIT", .openGoal, [122, 121, 127], []⟩,
  ⟨"KKL_STATIONARY_TYPED_BOUNDED_DEGREE_PUSHFORWARD", .openGoal, [128, 123, 30], []⟩,
  ⟨"KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR", .openGoal, [95, 127, 128, 129], []⟩,
  ⟨"KKL_PARABOLIC_WAVE_AMPLIFICATION", .openGoal, [85, 130], []⟩,
  ⟨"FINITE_HORIZON_KKL_WAVE_REDUCTION", .ledgerProved, [56, 57, 58, 86, 87], [131]⟩,
  ⟨"FINITE_INVERSE_TREE_FAN_SATURATION", .ledgerProved, [53, 79], []⟩,
  ⟨"FORWARD_HULL_COMPONENT_NO_GO", .ledgerProved, [], []⟩,
  ⟨"SATURATED_SEED_FOREST", .ledgerProved, [50, 53], []⟩,
  ⟨"ROOT_PULLBACK_FOREST_EQUIVALENCE", .ledgerProved, [135, 53], []⟩,
  ⟨"CRITICAL_VALUE_CORRIDOR_CRITERION", .ledgerProved, [136, 53], []⟩,
  ⟨"FINITE_OBSTACLE_FORWARD_CLOSURE", .ledgerProved, [135, 57], []⟩,
  ⟨"FINITE_FAN_RIBBON_PULLBACK", .ledgerProved, [135, 133], []⟩,
  ⟨"ENDPOINT_BIRTH_ACCOUNTING", .ledgerProved, [139], []⟩,
  ⟨"LOCAL_CARRIER_EQUALITY_NO_BIRTH", .ledgerProved, [139, 140], []⟩,
  ⟨"ATTACHMENT_SUPPORT_REDUCTION", .ledgerProved, [15, 140, 141], []⟩,
  ⟨"CORRIDOR_ATTACHMENT_TRANSPORT", .ledgerProved, [137, 142], []⟩,
  ⟨"UNIVALENT_CARRIER_PAIR_TRANSPORT", .ledgerProved, [137, 143], []⟩,
  ⟨"ATTACHMENT_FREE_ANCHOR_UNDERDETERMINATION", .ledgerProved, [], []⟩,
  ⟨"FINITE_ATTACHMENT_ORBIT_CLOSURE", .ledgerProved, [142, 143], []⟩,
  ⟨"INTERFACE_PROOF_USE_INVENTORY", .ledgerProved, [], []⟩,
  ⟨"HORIZON_FIRST_INVENTORY_AUDIT", .ledgerProved, [147], []⟩,
  ⟨"RESOLVED_FINITE_WAVE_HORIZON_COMPILER", .ledgerProved, [148], []⟩,
  ⟨"KKL_NATIVE_WAVE_HORIZON_CONTROL", .ledgerProved, [149], [85]⟩,
  ⟨"RETURN_PATH_LANGUAGE", .ledgerProved, [], []⟩,
  ⟨"FORWARD_COHERENT_COMPLEMENT_PAIR", .ledgerProved, [49, 57], []⟩,
  ⟨"PRIME_END_MARKING_ACTION_CRITERION", .ledgerProved, [48], []⟩,
  ⟨"MARKED_PAIR_ENLARGEMENT_NATURALITY", .ledgerProved, [153], []⟩,
  ⟨"RETURN_BASE_UNDERDETERMINATION", .ledgerProved, [], []⟩,
  ⟨"NATIVE_PRINCIPAL_NEST_RETURN_ATLAS", .ledgerProved, [19, 48], []⟩,
  ⟨"ISOTOPY_CLASS_RETURN_UNDERDETERMINATION", .ledgerProved, [], []⟩,
  ⟨"FIRST_DECORATION_SCALE_ESCAPE_ATLAS", .ledgerProved, [20, 48], []⟩,
  ⟨"CRITICAL_BASE_CYCLE_EXCLUSION", .ledgerProved, [20, 158], []⟩,
  ⟨"DECORATION_FAN_GROWTH", .ledgerProved, [20], []⟩,
  ⟨"NATIVE_HUBBARD_SUBTREE_FUNCTORIALITY", .ledgerProved, [21], []⟩,
  ⟨"TERMINAL_CYCLE_HUBBARD_ANCHOR", .ledgerProved, [21, 161, 159], []⟩,
  ⟨"TERMINAL_NATIVE_HUBBARD_CARRIER_FULLNESS", .ledgerProved, [162, 105], []⟩,
  ⟨"TERMINAL_LC_NATIVE_HUBBARD_CARRIER_PROPER", .ledgerProved, [21, 162], []⟩,
  ⟨"TERMINAL_RELATIVE_COVER_SUBGROUP_ALIGNMENT", .ledgerProved, [163, 20], []⟩,
  ⟨"TERMINAL_K1_EXTERIOR_PUZZLE_VERTEX_CANDIDATE_SET", .ledgerProved, [159, 20], []⟩,
  ⟨"TERMINAL_K1_TO_K0_PATH_PUZZLE_VERTEX_CANDIDATES", .ledgerProved, [166, 162], []⟩,
  ⟨"PUZZLE_VERTEX_EXTERIOR_COMPONENT_INJECTIVITY", .ledgerProved, [20], []⟩,
  ⟨"TERMINAL_K1_UNIQUE_PUZZLE_VERTEX_ANCHOR", .ledgerProved, [166, 167, 168], []⟩,
  ⟨"KL_TILE_INTERIOR_HOMOGENEOUS_TRACE", .ledgerProved, [20], []⟩,
  ⟨"TERMINAL_ANCHOR_COMPACT_HALF_COLLARS", .ledgerProved, [169, 170], []⟩,
  ⟨"TERMINAL_PROPER_ACCESS_CHANNEL_ATLAS", .ledgerProved, [165, 171], []⟩,
  ⟨"KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY", .ledgerProved, [20], []⟩,
  ⟨"DIRECT_DECORATION_PULLBACK_COMPACTIFICATION", .ledgerProved, [20, 158, 159], []⟩,
  ⟨"DIRECT_DECORATION_BIGRADED_KL_STAGE_GRID", .ledgerProved, [158, 174, 173], []⟩,
  ⟨"FINITE_GRID_AND_TERMINAL_KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY", .ledgerProved, [173, 175, 159], []⟩,
  ⟨"TERMINAL_LOCAL_CHANNEL_TO_KL_WELDING", .ledgerProved, [165, 172, 176], []⟩,
  ⟨"TERMINAL_KL_FINITE_SIDE_REFINEMENT", .ledgerProved, [177, 176], []⟩,
  ⟨"TERMINAL_FINAL_ROOT_COVER_OBSTACLE_DECOMPOSITION", .ledgerProved, [163, 165], []⟩,
  ⟨"TERMINAL_CERTIFIED_CHANNEL_FINAL_ROOT_STABILITY", .ledgerProved, [172, 177, 179], []⟩,
  ⟨"TERMINAL_OUTER_SEAM_DECK_NORMALIZATION", .ledgerProved, [165, 20], []⟩,
  ⟨"TERMINAL_SEAM_LIFT_END_PROPERNESS", .ledgerProved, [181, 165], []⟩,
  ⟨"TERMINAL_KL_FINITE_ENDPOINT_FIVE_WAY_CLASSIFICATION", .ledgerProved, [182, 176], []⟩,
  ⟨"DENSE_ONE_GATE_HAIR_ACCESS_NO_GO", .ledgerProved, [16], []⟩,
  ⟨"TERMINAL_ACCESS_SURVIVAL_EQUIVALENCE", .ledgerProved, [165, 171, 172, 178, 180], []⟩,
  ⟨"TERMINAL_FORWARD_INVARIANT_CARRIER_DENSE_OBSTACLE_NO_GO", .ledgerProved, [26, 23, 105, 185, 164], []⟩,
  ⟨"TERMINAL_KL_ORDERED_MULTICURVE_OVERFLOW", .ledgerProved, [], []⟩,
  ⟨"TERMINAL_KL_SUBMULTICURVE_OVERFLOW_TRANSFER", .ledgerProved, [20, 187], []⟩,
  ⟨"KKL_FIXED_END_ACCESS_TYPE_OBSTRUCTION", .ledgerProved, [27], []⟩,
  ⟨"KKL_ACCESS_SEEDED_MAXIMAL_LIFT_MEASURABILITY", .ledgerProved, [], []⟩,
  ⟨"KKL_BROAD_WAVE_PUSHFORWARD_COUNTEREXAMPLE", .ledgerProved, [28], []⟩,
  ⟨"KKL_STATIONARY_EXACT_OCCURRENCE_SERIES_CONDUCTANCE", .ledgerProved, [28], []⟩,
  ⟨"KKL_WAVE_PUSHFORWARD_UNIFORM_PACKET_CONSTANT", .openGoal, [29, 191], []⟩,
  ⟨"KKL_STATIONARY_CONDITIONAL_PAIRED_WAVE_RESPONSE_ALGEBRA", .ledgerProved, [192], [193]⟩,
  ⟨"KKL_FIXED_END_WAD_SPLIT_FINITE_SELECTOR", .ledgerProved, [27], []⟩,
  ⟨"KKL_STATIONARY_SURVIVOR_PARTITION_AND_POINTWISE_SWITCH", .ledgerProved, [92, 115], []⟩,
  ⟨"KKL_STATIONARY_ABSTRACT_FINITE_ROUTE_EXIT_SCHEMA", .ledgerProved, [196, 187], []⟩,
  ⟨"KKL_STATIONARY_CONDITIONAL_VERTICAL_PACKET_CHARGE", .ledgerProved, [196], []⟩,
  ⟨"KKL_STATIONARY_COLLAR_EXIT_OVERFLOW", .ledgerProved, [117, 187], []⟩,
  ⟨"KAHN_QUALITATIVE_COLLAR_VERTICAL_CHARGE_NO_GO", .ledgerProved, [], []⟩,
  ⟨"KKL_STATIONARY_QUANTITATIVE_DEFECT_BOUND", .openGoal, [115, 199, 123], []⟩,
  ⟨"KKL_STATIONARY_QSDB_SUFFICIENCY", .ledgerProved, [123], [201]⟩,
  ⟨"KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION", .openGoal, [21, 102, 98], []⟩,
  ⟨"KKL_STATIONARY_MONOTONE_FULL_LIFT_IMPLIES_MCI", .ledgerProved, [107, 104], [203]⟩,
  ⟨"KKL_STATIONARY_SMALL_JULIA_POINT_COLLAPSE_OBSTRUCTION", .ledgerProved, [21, 23, 105, 24, 25], []⟩,
  ⟨"KKL_STATIONARY_LC_LINE1598_REPAIR", .ledgerProved, [106, 112], []⟩,
  ⟨"KKL_STATIONARY_OFF_BY_ONE_PASS_THROUGH_REDUCTION", .ledgerProved, [], [127]⟩,
  ⟨"PQL_RAW_UNTAGGED_PATH_IMAGE_COLLISION", .ledgerProved, [], []⟩,
  ⟨"PQL_WAVE_TO_WAVE_UNTAGGED_PATH_IMAGE_COLLISION", .ledgerProved, [208], []⟩,
  ⟨"TERMINAL_WAVE_CREST_TO_KL_WIDTH_CONDITIONAL", .ledgerProved, [187, 20], []⟩,
  ⟨"FINITE_EXACT_CANTOR_ENCODING_OBSTRUCTION", .ledgerProved, [], []⟩,
  ⟨"FINITE_QUOTIENT_OBSERVABILITY_CRITERION", .ledgerProved, [], []⟩,
  ⟨"NESTED_FULL_PACKET_NONSEPARATION", .ledgerProved, [16], []⟩,
  ⟨"DIRECT_DECORATION_FULL_FIBERS", .ledgerProved, [174], []⟩,
  ⟨"DIRECT_DECORATION_GLOBAL_NONSEPARATION", .ledgerProved, [214, 213], []⟩,
  ⟨"DIRECT_DECORATION_GAP_CELL_ATLAS", .ledgerProved, [174], []⟩,
  ⟨"DIRECT_DECORATION_FINITE_PACKET_REPLACEMENT", .ledgerProved, [215, 216, 213], []⟩,
  ⟨"PROPER_PROTECTED_IMPRESSION_EXPOSURE", .ledgerProved, [], []⟩,
  ⟨"PROTECTED_REGULATED_CONNECTOR_REALIZATION", .ledgerProved, [], []⟩,
  ⟨"PROTECTED_FREE_COMPONENT_CRITERION", .ledgerProved, [219], []⟩,
  ⟨"DIRECT_DECORATION_FINITE_PROTECTED_CARRIER", .ledgerProved, [217, 218, 220, 219], []⟩,
  ⟨"PULLBACK_GAP_ENLARGEMENT_NATURALITY", .ledgerProved, [174], []⟩,
  ⟨"CRITICAL_CUT_POINTWISE_CONSERVATION", .ledgerProved, [], []⟩,
  ⟨"PROPER_COMMUTING_SQUARE_DEGREE_LAW", .ledgerProved, [], []⟩,
  ⟨"LOCAL_OFF_CRITICAL_CYLINDER_SQUARE", .ledgerProved, [], []⟩,
  ⟨"RETIMED_FINITE_CYLINDER_PAIR", .ledgerProved, [174], []⟩,
  ⟨"CRITICALITY_LOCATION_SWAP_NO_GO", .ledgerProved, [], []⟩,
  ⟨"CRITICAL_TIME_SHEAR_NO_GO", .ledgerProved, [], []⟩,
  ⟨"STAGEWISE_CRITICAL_WORD_LADDER", .ledgerProved, [224], []⟩,
  ⟨"QUADRATIC_JORDAN_BASE_CHANGE_DICHOTOMY", .ledgerProved, [], []⟩,
  ⟨"PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER", .ledgerProved, [230], []⟩,
  ⟨"FINITE_PLANAR_TELESCOPE_IDENTITY", .ledgerProved, [231, 223], []⟩,
  ⟨"PLANAR_END_COLLAPSE_NO_GO", .ledgerProved, [174], []⟩,
  ⟨"NORMALIZED_RETIMED_GERM_CONSTANCY", .ledgerProved, [226], []⟩,
  ⟨"NORMALIZED_END_DIRECT_LIMIT", .ledgerProved, [234], []⟩,
  ⟨"DEPTH_GRADED_CYLINDER_MATERIALIZATION", .ledgerProved, [226], []⟩,
  ⟨"FINITE_ELECTRODE_RESPONSE", .ledgerProved, [], []⟩,
  ⟨"END_CHART_OBSERVABLE_INVARIANCE", .ledgerProved, [235, 237], []⟩,
  ⟨"SERIAL_EXHAUSTION_RESISTANCE_BOUND", .ledgerProved, [], []⟩,
  ⟨"SCALAR_NECK_TRACE_MODE_NO_GO", .ledgerProved, [], []⟩,
  ⟨"FULL_TRACE_RECTANGLE_DTN", .ledgerProved, [], []⟩,
  ⟨"TRACE_RESPONSE_SEMIGROUP", .ledgerProved, [241], []⟩,
  ⟨"EQUIPOTENTIAL_COLLAPSE_CRITERION", .ledgerProved, [241], []⟩,
  ⟨"SHORTED_EQUIPOTENTIAL_NODAL_RESPONSE", .ledgerProved, [243, 242], []⟩,
  ⟨"TRACE_RENORMALIZED_NECK_ESTIMATE", .ledgerProved, [241], []⟩,
  ⟨"END_TRACE_RESPONSE_COMPACTIFICATION", .ledgerProved, [245], []⟩,
  ⟨"HILBERT_TRACE_GLUE_CALCULUS", .ledgerProved, [], []⟩,
  ⟨"TRACE_STABLE_STRICT_TRANSITION_TRANSFER", .ledgerProved, [245, 247], []⟩,
  ⟨"PULLED_EQUIPOTENTIAL_SERIAL_RECTANGLE_NO_GO", .ledgerProved, [174], []⟩,
  ⟨"ACTIVE_INACTIVE_PHYSICAL_CELL", .ledgerProved, [], []⟩,
  ⟨"ATTACHMENT_ARC_OPEN_ATOM_REFINEMENT", .ledgerProved, [], []⟩,
  ⟨"REGULAR_INTERFACE_FIBER_PRODUCT_RESPONSE", .ledgerProved, [], []⟩,
  ⟨"FINITE_TAME_CONTACT_OVERLAY_RESPONSE", .ledgerProved, [252], []⟩,
  ⟨"INFIMUM_PUSHFORWARD_FUNCTORIALITY", .ledgerProved, [], []⟩,
  ⟨"CLOSED_FORM_PUSHFORWARD_NO_GO", .ledgerProved, [254], []⟩,
  ⟨"FIXED_STANDARD_NECK_MULTIPORT_COMPACTIFICATION", .ledgerProved, [245, 247], []⟩,
  ⟨"QUADRATIC_PRIMITIVE_ROOT_PARABOLIC_NONDEGENERACY", .ledgerProved, [3], []⟩,
  ⟨"FIXED_MODULUS_AMBIENT_END_NO_GO", .ledgerProved, [], []⟩,
  ⟨"SERIAL_ANNULUS_SINGLETON_BRIDGE", .ledgerProved, [], []⟩,
  ⟨"MULTIPORT_TRACE_GAUGE_AND_STRICTNESS_NO_GO", .ledgerProved, [241], []⟩,
  ⟨"WOT_WELDING_ALGEBRA_NO_GO", .ledgerProved, [], []⟩,
  ⟨"DYADIC_BOTTCHER_EXTERNAL_TRACE_ISOMETRY", .ledgerProved, [174], []⟩,
  ⟨"BINARY_DIRECT_DECORATION_NESTED_SEPARATOR_CALCULUS", .ledgerProved, [174, 252, 253], []⟩,
  ⟨"FIXED_BLOCK_BINARY_CONTACT_AUTOMATON", .ledgerProved, [20, 174, 263], []⟩,
  ⟨"FIXED_KKL_PAIR_STATE_MOMENT_FACTORIZATION", .ledgerProved, [12, 34], []⟩,
  ⟨"FINITE_LINEAR_LABEL_MARKING_ENUMERATOR", .ledgerProved, [], []⟩,
  ⟨"PULL_PUSH_WELDING_WORD_COMPOSITION_NO_GO", .ledgerProved, [], []⟩,
  ⟨"DEGREE_ONE_ANNULUS_IMMERSION_INJECTIVITY_NO_GO", .ledgerProved, [], []⟩,
  ⟨"KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO", .ledgerProved, [], []⟩,
  ⟨"PSI_QL_GLOBAL_INJECTIVITY_NO_GO", .ledgerProved, [], []⟩,
  ⟨"KL_LOCALIZATION_SUBGROUP_REFLECTION_CRITERION", .ledgerProved, [20], []⟩,
  ⟨"KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION", .ledgerProved, [20], []⟩,
  ⟨"KL_CANONICAL_LOCALIZATION_FORCED_COLLISION", .ledgerProved, [271, 272], []⟩,
  ⟨"KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION", .ledgerProved, [271, 273], []⟩,
  ⟨"KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT", .ledgerProved, [273, 274], []⟩,
  ⟨"RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY", .ledgerProved, [274, 275], []⟩,
  ⟨"CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO", .ledgerProved, [274, 173, 276], []⟩,
  ⟨"TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION", .ledgerProved, [20], []⟩,
  ⟨"EMBEDDED_DISK_ACCESSIBLE_FOOTPRINT_THEOREM", .ledgerProved, [15], []⟩,
  ⟨"FINITE_HORIZON_KAHN_COLLAR_EMBEDDING", .ledgerProved, [20, 272, 278, 279], []⟩,
  ⟨"CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION", .ledgerProved, [274, 275, 276, 277, 280], []⟩,
  ⟨"FULL_KL_PSEUDOPIECE_MAXIMAL_LIFT_PROPERNESS", .ledgerProved, [281, 173, 15], []⟩,
  ⟨"PARAMETRIZED_PULLBACK_KKL_EXHAUSTION_NO_GO", .ledgerProved, [281, 282, 15], []⟩,
  ⟨"FINITE_BINDER_PROOF_USE_LEDGER_COMPILER", .ledgerProved, [147, 283], []⟩,
  ⟨"KKL_BOUNDED_VISITS_ARITHMETIC_AFTER_GROWTH", .ledgerProved, [], [85]⟩,
  ⟨"KKL_NATIVE_WAVE_WANDERERS_QUERY_SCHEMA_BOUNDARY_MAP", .openGoal, [284, 84, 15, 283], []⟩,
  ⟨"KKL_WANDERERS_THEOREM_COMPLETE_REPAIR", .openGoal, [286], []⟩,
  ⟨"KKL_LOCALIZED_WANDERERS_ROUTE_REALIZATION_CERTIFICATE", .openGoal, [286], []⟩,
  ⟨"KKL_LOCALIZED_WANDERERS_APPLICATION_REDUCTION", .ledgerProved, [84], [287, 288]⟩,
  ⟨"ONE_DIMENSIONAL_CYLINDER_STAGE_COLLAPSE_NO_GO", .ledgerProved, [175], []⟩,
  ⟨"DIRECT_DECORATION_COMPONENT_ADDRESS_FINITE_PHASE_SKELETON", .ledgerProved, [174, 175], []⟩,
  ⟨"CARRIER_ACCESS_TO_KL_MULTICURVE_BRIDGE", .ledgerProved, [175, 176], []⟩,
  ⟨"TERMINAL_ANCHOR_NOT_SMALL_JULIA_VERTEX", .ledgerProved, [169, 162, 20], []⟩,
  ⟨"DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER", .openGoal, [148, 147, 283, 284, 286], []⟩,
  ⟨"TERMINAL_LOCAL_KL_KKL_ALIGNMENT_RECORD", .ledgerProved, [169, 165, 181], [294]⟩,
  ⟨"TERMINAL_SEAM_NORMALIZED_PATH_LIFT", .ledgerProved, [295, 165, 181], []⟩,
  ⟨"TERMINAL_ANCHOR_COLLAR_OR_RESTRICTION_OBSTRUCTION", .ledgerProved, [295, 169, 293, 171, 165, 296, 182, 183, 172, 179, 176, 283], []⟩,
  ⟨"NONPROPER_LABEL_HULL_PULLBACK_NO_GO", .ledgerProved, [], []⟩,
  ⟨"GENERAL_ANNULUS_IMMERSION_LOWER_STRIP_NO_GO", .ledgerProved, [], []⟩,
  ⟨"COMMON_COORDINATE_NESTED_ANNULUS_OUTER_CAP", .ledgerProved, [278, 173, 279], []⟩,
  ⟨"END_BLOWUP_PROJECTION_NO_GO", .ledgerProved, [233], []⟩,
  ⟨"FIXED_ITERATE_END_FIBER_EXTENSION", .ledgerProved, [], []⟩,
  ⟨"FINITE_CYLINDER_COMMUTING_ITERATE_LIFT", .ledgerProved, [], []⟩,
  ⟨"FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS", .ledgerProved, [], []⟩,
  ⟨"INTERIOR_PULLBACK_COMPONENT_FORCING", .ledgerProved, [303, 304], []⟩,
  ⟨"FUTURE_OBSERVABLE_COMPACTIFICATION", .ledgerProved, [], []⟩,
  ⟨"FUTURE_FAITHFUL_END_TOPOLOGY", .ledgerProved, [306], []⟩,
  ⟨"VIRTUAL_PROOF_USE_TRACE_SELECTOR", .ledgerProved, [307], []⟩,
  ⟨"DEMAND_CLOSED_RETURN_ATLAS_COMPILER", .ledgerProved, [151], []⟩,
  ⟨"RETURN_ATLAS_ENLARGEMENT_NATURALITY", .ledgerProved, [309], []⟩,
  ⟨"FINITE_GEOMETRIC_SATURATION", .ledgerProved, [], []⟩,
  ⟨"CONNECTED_CARRIER_NO_MINIMUM", .ledgerProved, [], []⟩,
  ⟨"QUADRATIC_PROTECTED_ACCESS_COLLISION", .ledgerProved, [137, 311], []⟩,
  ⟨"AUGMENTED_ATOM_COMMON_DOMAIN", .ledgerProved, [16, 220], []⟩,
  ⟨"AUGMENTED_PACKET_CLOSURE_AUDIT", .ledgerProved, [], []⟩,
  ⟨"CELLWISE_PACKET_PORT_CERTIFICATE", .ledgerProved, [315, 314], []⟩,
  ⟨"PARALLEL_REPLICATION_CRITERION", .ledgerProved, [], []⟩,
  ⟨"TOPOLOGY_REPLICATION_NO_GO", .ledgerProved, [65], []⟩,
  ⟨"CONDITIONAL_TREE_REPLICATION_CALIBRATION", .ledgerProved, [75, 63, 317, 73], []⟩,
  ⟨"DISCOUNTED_DUHAMEL", .ledgerProved, [], []⟩,
  ⟨"DISCOUNTED_ENTROPY_ABSORPTION", .ledgerProved, [320], []⟩,
  ⟨"ENTROPY_THRESHOLD_NO_GO", .ledgerProved, [320], []⟩,
  ⟨"CHART_CYCLE_OBSTRUCTION", .ledgerProved, [], []⟩,
  ⟨"RESPONSE_GLUE_CALCULUS", .ledgerProved, [], []⟩,
  ⟨"PORT_FUTURE_CLOSURE_NO_GO", .ledgerProved, [237], []⟩,
  ⟨"WAD_DOMINATION_RESPONSE", .ledgerProved, [324], []⟩,
  ⟨"FIXED_BLOCK_SPECTRAL_COMPARISON", .ledgerProved, [237, 324], []⟩,
  ⟨"VALUE_RESPONSE_NO_GO", .ledgerProved, [], []⟩,
  ⟨"VALUE_FEATURE_ROWSPACE", .ledgerProved, [], []⟩,
  ⟨"PRIMITIVE_VALUE_AFFINE_CONTRACTION", .ledgerProved, [12, 34], []⟩,
  ⟨"CLONED_VALUE_BLOCK_CONTRACTION", .ledgerProved, [12, 34, 36], []⟩,
  ⟨"PRIMITIVE_INTEGER_ENTROPY_GAP", .ledgerProved, [], []⟩,
  ⟨"VARIABLE_CLONE_BLOCK_CONTRACTION", .ledgerProved, [12, 34, 36, 332], []⟩,
  ⟨"PERTURBED_CLONE_CONTRACTION", .ledgerProved, [36, 332], []⟩,
  ⟨"BOUNDED_ENTROPY_EIGENCONE", .ledgerProved, [36, 332], []⟩,
  ⟨"UNBOUNDED_DIMENSION_ENTROPY_NO_GO", .ledgerProved, [], []⟩,
  ⟨"EXACT_CORRIDOR_CLONE_CRITERION", .ledgerProved, [], []⟩,
  ⟨"ENDPOINT_DEFECT_ABSORPTION", .ledgerProved, [337], []⟩,
  ⟨"FINITE_CORRIDOR_CLONE_UNION", .ledgerProved, [337], []⟩,
  ⟨"CROSS_SECTION_DAG_EQUIVALENCE", .ledgerProved, [], []⟩,
  ⟨"CLONE_STRONG_CONNECTIVITY", .ledgerProved, [], []⟩,
  ⟨"ROBUST_CLONE_PRIMITIVITY", .ledgerProved, [341], []⟩,
  ⟨"PRIMITIVE_BASE_CLONE_NO_GO", .ledgerProved, [], []⟩,
  ⟨"FINITE_STATE_CORRIDOR_CERTIFICATE", .ledgerProved, [337, 338, 339, 340, 342], []⟩,
  ⟨"FINITE_STATE_CORRIDOR_VALUE_COROLLARY", .ledgerProved, [344, 12, 34, 333], []⟩,
  ⟨"FRAMED_RETURN_SPECTRAL_INVARIANCE", .ledgerProved, [], []⟩,
  ⟨"PERMUTATION_COCYCLE_GAUGE", .ledgerProved, [], []⟩,
  ⟨"IRREDUCIBLE_TRANSFER_ENTROPY_DICHOTOMY", .ledgerProved, [], []⟩,
  ⟨"ZERO_ENTROPY_SHEAR_NORMAL_FORM", .ledgerProved, [348], []⟩,
  ⟨"DEFECT_RUN_DECOMPOSITION", .ledgerProved, [347], []⟩,
  ⟨"ZERO_ENTROPY_SHEAR_NO_GO", .ledgerProved, [], []⟩,
  ⟨"BOOLEAN_SUPPORT_FUNCTOR", .ledgerProved, [], []⟩,
  ⟨"SUPPORT_AUTOMATON_PUMPING", .ledgerProved, [352], []⟩,
  ⟨"BOUNDED_BRANCH_SUPPORT_WITNESS", .ledgerProved, [353, 348, 346], []⟩,
  ⟨"FUTURE_EQUIVALENCE_AUTOMATON", .ledgerProved, [], []⟩,
  ⟨"FINITE_HORIZON_LANGUAGE_NO_GO", .ledgerProved, [355], []⟩,
  ⟨"BOUNDED_MEMORY_AUTOMATON", .ledgerProved, [355], []⟩,
  ⟨"COUNTER_SAFE_PUMPING", .ledgerProved, [], []⟩,
  ⟨"MEMORY_PROJECTION_PUMPING_NO_GO", .ledgerProved, [358, 356], []⟩,
  ⟨"ADDITIVE_COUNTER_MEMORY_NO_GO", .ledgerProved, [356], []⟩,
  ⟨"REVERSE_WORD_STACK_MODEL", .ledgerProved, [355], []⟩,
  ⟨"DISCRETE_SIDE_DATA_COMPACTNESS_NO_GO", .ledgerProved, [], []⟩,
  ⟨"COUNTABLE_FOLLOWER_STONE_COMPACTIFICATION", .ledgerProved, [], []⟩,
  ⟨"SOURCE_FUTURE_QUOTIENT", .ledgerProved, [355], []⟩,
  ⟨"MARKOV_SIGNATURE_AUTOMATON", .ledgerProved, [364], []⟩,
  ⟨"WAD_TRANSPORT_QUOTIENT_CRITERION", .ledgerProved, [], []⟩,
  ⟨"WAD_FUTURE_OBSERVABILITY", .ledgerProved, [], []⟩,
  ⟨"PURE_CORRIDOR_MACRO", .ledgerProved, [], []⟩,
  ⟨"COUNTER_STACK_SAFE_LOOP", .ledgerProved, [358], []⟩,
  ⟨"H3_SYMBOLIC_SIDE_COMPACTNESS", .ledgerProved, [306], []⟩,
  ⟨"MAPPING_TELESCOPE", .openGoal, [231, 58, 57], []⟩,
  ⟨"FINITE_HORIZON_ASSEMBLY", .openGoal, [371, 232, 153, 154], []⟩,
  ⟨"H1_FINITE_HORIZON_INFLATION", .openGoal, [48, 49, 50, 51, 52, 54, 371, 55, 56, 57, 58, 372, 59, 60, 61], []⟩,
  ⟨"H1_CELL_TREE_EXTRACTION", .openGoal, [74, 318], []⟩,
  ⟨"H1_ANALYTIC_ACCESS_REALIZATION", .openGoal, [374, 373, 9, 75, 317, 73], []⟩,
  ⟨"H1_MARKED_CONSTRUCTION", .openGoal, [37, 40, 41, 42, 373, 67, 75, 317, 318, 319, 374, 375], []⟩,
  ⟨"KKL_STATIONARY_TWO_PULLBACK_PASS_THROUGH", .openGoal, [126, 207, 120], []⟩,
  ⟨"KKL_STATIONARY_FINAL_PASS_THROUGH_PATH_EXTRACTION", .openGoal, [126, 377, 122], []⟩,
  ⟨"KKL_STATIONARY_FINAL_INCIDENCE_REFINEMENT", .openGoal, [126, 377, 122, 123, 378, 294], []⟩,
  ⟨"KKL_STATIONARY_NESTED_INCIDENCE_ORDER", .openGoal, [379], []⟩,
  ⟨"KKL_STATIONARY_FIXED_PAIR_PROPER_RESTRICTION", .openGoal, [379, 380, 294, 283], []⟩,
  ⟨"TERMINAL_STATIONARY_RESTRICTION_KL_PUZZLE_SELECTOR", .openGoal, [381, 169, 165, 296], []⟩,
  ⟨"TERMINAL_WAVE_KL_CONNECTING_SUBFAMILY", .openGoal, [294, 169, 188, 381, 382], []⟩,
  ⟨"TERMINAL_WAVE_CREST_TO_KL_SKIPPING_BINDER", .openGoal, [383, 169, 165, 296, 180, 210], []⟩,
  ⟨"TERMINAL_KL_SUBMULTICURVE_BINDER_SELECTOR", .openGoal, [383, 384, 188, 294], []⟩,
  ⟨"TERMINAL_TAGGED_ENDPOINT_ACCESS_MATCH", .openGoal, [169, 296, 183, 294], []⟩,
  ⟨"WAVE_TO_KL_ADDRESS_ACCESS_SELECTOR", .openGoal, [291, 292, 176, 295, 177, 180, 186, 383, 385, 386, 297, 294], []⟩,
  ⟨"DIRECT_DECORATION_CANONICAL_KL_STAGE_ALIGNMENT", .openGoal, [294, 175, 290, 387, 281, 174, 173], []⟩,
  ⟨"DIRECT_DECORATION_RELATION_PROPER_PATH_END_INTERVAL_CLASSIFICATION", .openGoal, [388, 282, 283, 15, 276, 173, 298, 153], []⟩,
  ⟨"DIRECT_DECORATION_CANONICAL_KL_RELATION_PROPER_END_RESPONSE", .openGoal, [389, 34, 328, 329, 326, 325, 247], []⟩,
  ⟨"DIRECT_DECORATION_OUTER_CAP_FOOTPRINT", .openGoal, [273, 274, 275, 276, 277, 281, 173, 299, 390], []⟩,
  ⟨"DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH", .openGoal, [389, 274, 222, 154, 310], []⟩,
  ⟨"DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION", .openGoal, [273, 274, 275, 298, 173, 277, 281, 391, 392], []⟩,
  ⟨"DIRECT_DECORATION_ALL_DEPTH_CONTACT_CLOSURE", .openGoal, [174, 250, 251, 263, 264, 266, 273, 274, 393], []⟩,
  ⟨"FINITE_LIVE_COMMON_REFINEMENT_FRONTIER", .openGoal, [394, 255], []⟩,
  ⟨"DIRECT_DECORATION_TRACE_WELDING_COMPACTNESS", .openGoal, [174, 394, 252, 256, 261, 262, 267], []⟩,
  ⟨"DIRECT_DECORATION_TRACE_COLLAR_REALIZATION", .openGoal, [174, 170, 222, 239, 241, 249, 250, 251, 252, 258, 259, 260, 394, 395, 396, 266, 267], []⟩,
  ⟨"END_PLUMBING_TRACE_RESPONSE_CONTROL", .openGoal, [237, 239, 240, 241, 242, 243, 245, 246, 247, 248, 256, 259, 260, 261, 397, 394, 395, 396], []⟩,
  ⟨"H2_RESPONSE_REALIZATION", .openGoal, [375, 324, 237, 325, 326, 327, 71, 18, 63, 398], []⟩,
  ⟨"H2_VIRTUAL_CORE_COCYCLE_REALIZATION", .openGoal, [374, 375, 373, 346, 34], []⟩,
  ⟨"H2_UNIFORM_CORE_WAD_DIMENSION", .openGoal, [400, 366, 367, 336], []⟩,
  ⟨"H2_VIRTUAL_CORRIDOR_GRAPH_REALIZATION", .openGoal, [375, 400, 401, 34, 9, 337, 338, 339, 340, 342, 343, 344, 336], []⟩,
  ⟨"H2_VIRTUAL_CLONE_REALIZATION", .openGoal, [402, 34, 35, 36, 332, 333, 334, 335, 336, 326], []⟩,
  ⟨"H2_UNIFORM_COUNTER_FOLLOWER", .openGoal, [374, 375, 373, 400, 355, 356, 357, 358, 359, 360, 361, 369], []⟩,
  ⟨"H2_MEMORY_SAFE_PUMPING_COMPILATION", .openGoal, [404, 359, 368, 369], []⟩,
  ⟨"H2_VIRTUAL_SUPPORT_AUTOMATON", .openGoal, [374, 375, 373, 404, 401, 405, 364, 365, 366, 367, 368, 369, 346, 352, 353, 354, 349, 351, 34, 400], []⟩,
  ⟨"H2_VIRTUAL_TRANSFER_TRICHOTOMY", .openGoal, [375, 406, 403, 347, 348, 349, 350, 351, 330, 70], []⟩,
  ⟨"H2_VALUE_FEATURE_REALIZATION", .openGoal, [12, 326, 328, 329, 330, 331, 333, 403, 407, 399], []⟩,
  ⟨"H2_CALIBRATION", .openGoal, [376, 62, 63, 18, 71, 399, 408, 64, 65, 66], []⟩,
  ⟨"H2_CHART_CYCLE_EXPANSION", .openGoal, [399, 323], []⟩,
  ⟨"H2_FORWARD_CONTRACTION_CALIBRATION", .openGoal, [46, 47, 409, 323, 410], []⟩,
  ⟨"H2_CONE_CALIBRATION", .openGoal, [43, 44, 45, 46, 409, 411, 65, 66, 323, 324, 410], []⟩,
  ⟨"H2_DISCOUNTED_ERROR_CHARGE", .openGoal, [399, 408, 321, 322, 73], []⟩,
  ⟨"H2_SUMMABILITY", .openGoal, [376, 409, 17, 70, 73, 321, 322, 413], []⟩,
  ⟨"H2_VIRTUAL_SECTION4_INTERFACE", .openGoal, [375, 13, 75, 76, 10, 78], []⟩,
  ⟨"H2_VIRTUAL_TAME_FULL_RETURN", .openGoal, [415, 373, 403, 14, 12, 326, 79, 80, 81, 82, 83], []⟩,
  ⟨"VIRTUAL_ROOT_CARRIER_SEPARATION", .openGoal, [374, 136, 137, 138], []⟩,
  ⟨"VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION", .openGoal, [174, 304, 305], []⟩,
  ⟨"VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR", .openGoal, [174, 222, 304, 418], []⟩,
  ⟨"VIRTUAL_WAVE_DEMAND_SCHEMA", .openGoal, [148, 149], []⟩,
  ⟨"VIRTUAL_FINITE_WORD_ROOT_PORTRAIT_AUTHORIZATION", .openGoal, [226, 221, 153, 222, 419, 420], []⟩,
  ⟨"DIRECT_DECORATION_END_PRIME_END_COFINALITY", .openGoal, [174], []⟩,
  ⟨"VIRTUAL_END_BLOWUP_REALIZATION", .openGoal, [421, 422, 301, 234, 302], []⟩,
  ⟨"VIRTUAL_DISCONNECTED_MARKING_TRANSFER", .openGoal, [174, 222, 303, 419, 421, 422, 423], []⟩,
  ⟨"VIRTUAL_CANTOR_PACKAGE_REALIZATION", .openGoal, [174, 222, 424], []⟩,
  ⟨"VIRTUAL_PREFIX_LOCAL_SCALE_SELECTOR", .openGoal, [156, 157, 310, 158, 159, 160, 162, 425], []⟩,
  ⟨"VIRTUAL_RETURN_BASE_ATLAS", .openGoal, [155, 156, 157, 426, 312, 219, 137], []⟩,
  ⟨"VIRTUAL_RETURN_BRANCH_LANGUAGE", .openGoal, [151, 309, 310, 427, 420], []⟩,
  ⟨"VIRTUAL_PROVISIONAL_COMPLEMENT_PAIR", .openGoal, [428, 152, 136, 61, 219, 137], []⟩,
  ⟨"VIRTUAL_ACCESS_ACTION_CERTIFICATE", .openGoal, [429, 153, 58, 48, 219], []⟩,
  ⟨"VIRTUAL_WAVE_MARKED_CORRESPONDENCE", .openGoal, [428, 429, 430, 154], []⟩,
  ⟨"VIRTUAL_WAVE_HORIZON_CERTIFICATE", .openGoal, [148, 149, 431], []⟩,
  ⟨"VIRTUAL_UNPROTECTED_ATOM_EXPOSURE", .openGoal, [147, 432, 315], []⟩,
  ⟨"VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE", .openGoal, [147, 432, 433, 315, 314], []⟩,
  ⟨"VIRTUAL_COMMON_FREE_COMPONENT", .openGoal, [147, 220, 314, 434], []⟩,
  ⟨"VIRTUAL_PROTECTED_ROUTING_CERTIFICATE", .openGoal, [147, 417, 219, 220, 435], []⟩,
  ⟨"VIRTUAL_CANONICAL_INTERFACE_CARRIER", .openGoal, [374, 417, 147, 311, 312, 313, 219, 436], []⟩,
  ⟨"VIRTUAL_CORRIDOR_PAIR_NATURALITY", .openGoal, [437, 417, 375, 143, 144], []⟩,
  ⟨"VIRTUAL_ATTACHMENT_RESOLUTION", .openGoal, [437, 374, 375, 417, 145, 146, 143, 144], []⟩,
  ⟨"VIRTUAL_BOUNDED_ATTACHMENT_SUPPORT", .openGoal, [375, 58, 135, 138, 15, 142, 143, 144, 146, 438, 439], []⟩,
  ⟨"H2_VIRTUAL_LONG_ITERATE_WAVE", .openGoal, [415, 375, 373, 131, 130, 56, 58, 86, 87, 133, 134, 135, 136, 137, 417, 138, 139, 140, 141, 142, 440, 132], []⟩,
  ⟨"H2_ENTROPY_DICHOTOMY", .openGoal, [376, 414, 415, 416, 441, 77, 403, 407, 68], []⟩,
  ⟨"MBTT", .openGoal, [376, 409, 411, 412, 414, 442], []⟩,
  ⟨"H3_COERCIVITY", .openGoal, [376, 443, 39, 370], []⟩,
  ⟨"H4_RIGIDITY", .openGoal, [444], []⟩,
  ⟨"CONDITIONAL_REDUCTION", .ledgerProved, [0, 39], [376, 443, 444, 445]⟩,
  ⟨"UNIVERSAL_PROTECTED_TOWER_CLOSURE", .openGoal, [376, 443, 444, 445], []⟩,
  ⟨"UPTCR_IMPLIES_MLC", .ledgerProved, [0, 39], [447]⟩,
  ⟨"UPTCR_CROSS_VALIDATION", .ledgerProved, [39, 87, 312, 313], [447]⟩,
  ⟨"TERMINAL_NONLC_HUBBARD_CARRIER_PROPER", .openGoal, [21, 164], []⟩,
  ⟨"KKL_STATIONARY_MARKED_FIXED_END_PAIR_CERTIFICATE", .openGoal, [195, 196, 189], []⟩,
  ⟨"KKL_STATIONARY_TYPED_PAIRED_WAVE_REALIZATION", .openGoal, [196, 115, 190, 189], []⟩,
  ⟨"KKL_STATIONARY_BL0_UNIFORM_SURVIVOR_RESPONSE", .openGoal, [194, 452, 193], []⟩,
  ⟨"KKL_STATIONARY_SURVIVOR_EXCLUSION_OR_CHARGE", .openGoal, [197, 198, 453], []⟩,
  ⟨"KKL_STATIONARY_UNIFORM_COLLAR_EXIT_CHARGE", .openGoal, [199, 200], []⟩,
  ⟨"KKL_STATIONARY_SELECTED_PREDECESSOR_TERMINAL_VERTEX_SATURATION", .openGoal, [101, 21, 99, 106, 108], []⟩,
  ⟨"KKL_STATIONARY_PREDECESSOR_ENDPOINT_GATE_COHERENCE", .openGoal, [99, 102, 103, 100], []⟩,
  ⟨"DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION", .openGoal, [20], []⟩,
  ⟨"DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING", .openGoal, [20, 272, 278, 273], []⟩,
  ⟨"ESCAPE_RETURN_KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY", .openGoal, [176, 158], []⟩,
  ⟨"VIRTUAL_VERTEX_PACKAGE_SELECTOR", .openGoal, [161, 162, 160, 425, 432, 308], []⟩,
  ⟨"VIRTUAL_SCALE_TO_PUZZLE_SELECTOR", .openGoal, [426, 432, 308, 461], []⟩,
  ⟨"VIRTUAL_ATTACHMENT_FREE_ANCHOR", .openGoal, [437, 374, 375, 417, 145, 146], []⟩,
  ⟨"MLC", .openGoal, [0, 376, 443, 444, 445, 446], []⟩
]

def countWith (s : Status) : Nat :=
  (claims.toList.filter (fun c => c.status == s)).length

def dependencyCount : Nat :=
  claims.toList.foldl (fun total c => total + c.deps.length) 0

def assumptionCount : Nat :=
  claims.toList.foldl (fun total c => total + c.assumptions.length) 0

/-- Including assumption edges is essential: e.g. the recorded
    conditional UPTCR=>MLC statement has an open premise. -/
def edgesPointBackward : Bool :=
  (List.range claims.size).all (fun i =>
    (claims[i]!).deps.all (fun d => d < i) &&
    (claims[i]!).assumptions.all (fun d => d < i))

/-- The 316 documentary proved nodes have no direct *ordinary*
    dependency on a node labeled open. Conditional hypotheses are
    separate, and need NOT be discharged. -/
def ordinaryProofDependenciesClosed : Bool :=
  (List.range claims.size).all (fun i =>
    let c := claims[i]!
    c.status != .ledgerProved ||
      c.deps.all (fun d => (claims[d]!).status != .openGoal))

def conditionalPaperProofCount : Nat :=
  (claims.toList.filter (fun c =>
    c.status == .ledgerProved && !c.assumptions.isEmpty)).length

/-- Open goals whose ordinary prerequisites are already documentary
    proved/imported. This is a queue, NOT an analytic-proveability test. -/
def unblockedOpenCount : Nat :=
  (claims.toList.filter (fun c =>
    c.status == .openGoal &&
      c.deps.all (fun d => (claims[d]!).status != .openGoal))).length

theorem exact_ledger_size : claims.size = 465 := by decide +kernel
theorem imported_count : countWith .sourceImported = 34 := by decide +kernel
theorem documentary_proved_count : countWith .ledgerProved = 316 := by decide +kernel
theorem open_count : countWith .openGoal = 115 := by decide +kernel
theorem recorded_dependency_count : dependencyCount = 1035 := by decide +kernel
theorem recorded_conditional_count : conditionalPaperProofCount = 14 := by decide +kernel
theorem open_frontier_count : unblockedOpenCount = 20 := by decide +kernel
theorem acyclic_including_hypotheses : edgesPointBackward = true := by decide +kernel
theorem documentary_proved_deps_not_open :
    ordinaryProofDependenciesClosed = true := by decide +kernel

/-- The main research gates remain OPEN in the canonical ledger. -/
theorem terminal_research_gates_remain_open :
    ((claims[376]!).id = "H1_MARKED_CONSTRUCTION" ∧
     (claims[376]!).status = .openGoal) ∧
    ((claims[409]!).id = "H2_CALIBRATION" ∧
     (claims[409]!).status = .openGoal) ∧
    ((claims[444]!).id = "H3_COERCIVITY" ∧
     (claims[444]!).status = .openGoal) ∧
    ((claims[445]!).id = "H4_RIGIDITY" ∧
     (claims[445]!).status = .openGoal) ∧
    ((claims[447]!).id = "UNIVERSAL_PROTECTED_TOWER_CLOSURE" ∧
     (claims[447]!).status = .openGoal) ∧
    ((claims[464]!).id = "MLC" ∧
     (claims[464]!).status = .openGoal) := by
  decide +kernel

/-- The conditional implication is recorded as documentary proved,
    but its single hypothesis is the still-open universal package. -/
theorem terminal_conditional_hypothesis_is_explicit :
    (claims[448]!).id = "UPTCR_IMPLIES_MLC" ∧
    (claims[448]!).status = .ledgerProved ∧
    (claims[448]!).assumptions =
      [447] := by
  decide +kernel

#print axioms exact_ledger_size
#print axioms acyclic_including_hypotheses
#print axioms terminal_research_gates_remain_open
#print axioms terminal_conditional_hypothesis_is_explicit

end LoopsFormal.ResearchLedger
