# LaTeX manuscript

`main.tex` is the formal, source-locked manuscript for the unified MLC
research program. It deliberately distinguishes:

- imported source theorems;
- internally proved reductions;
- conditional implications; and
- open proof gates.

The manuscript must not state unconditional MLC until the machine ledger
marks every dependency of `MLC` proved or imported and the independent
dependency audit agrees.

## Build

From this directory:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\build.ps1
```

The build script first runs `generate_ledger_tex.py`, which validates
`../proof_obligations.json` and regenerates:

- `generated/ledger_counts.tex`;
- `generated/obligations.tex`.

It then uses `latexmk`, Tectonic, or `pdflatex`/`bibtex`, in that order.
The PDF is written to `build/main.pdf`.

## Editing rules

1. The generated files are never edited manually.
2. Every theorem environment carries a status in its printed name.
3. Imported results must cite the exact source scope in Section 2.
4. Open hypotheses cannot appear inside the proof of an unconditional
   theorem.
5. Before release, run:

```powershell
python ..\audit_proof.py
python ..\audit_transfer_regressions.py
powershell -NoProfile -ExecutionPolicy Bypass -File .\build.ps1
```

6. A successful build checks syntax and references; it does not validate a
mathematical proof.

## Live source status and last verified release

The post-Gate-N1 source ledger contains 437 obligations: 31 imported,
299 proved, and 107 open. The exact targets `MLC`,
`UNIVERSAL_PROTECTED_TOWER_CLOSURE`, and VAAPC-I remain open.
`UPTCR_IMPLIES_MLC` is only a proved conditional implication.

The current Gate-N1 synchronized manuscript has 198 pages and 5,964,916
bytes. Its SHA-256 digest is
`E443B54BB9FAC5D964FB6830AC7C8C8F57DB842EAF6A7478CE8FFBC1923EE999`.
It passed the ledger, ledger-tooling, transfer-regression,
TeX/BibTeX warning, and extracted-status checks. Gate N1,
`KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION`, is proved. The active
native repair has three remaining open gates: pointwise two-path
breaking, measurable final fixed-component exit, and typed
bounded-degree pushforward. The paired-response construction remains
an optional conditional route, not a dependency of the native proof.

No bulk visual sweep was performed. Targeted rendering of the changed
stationary pages 113--115 found no clipping, overlap, broken glyph, or
unreadable identifier.

The Research Push II audit adds fourteen proved local or compiler-level
results: critical-cut and proper-square degree conservation, a conditional
retimed finite-cylinder pair, criticality-swap and time-shear no-go
statements, the stagewise critical-word ladder, the Jordan base-change
dichotomy, a closure-embedded planar telescope compiler, planar end
collapse, normalized-germ constancy, a projection-collapse obstruction, and
a fixed-iterate end-fiber extension. It does not construct the missing
scale-two virtual root portrait, a protected marked relative-cover
telescope, a prime-end cofinal chain, or an analytic end blow-up. Those
residuals are recorded explicitly as open obligations rather than hidden in
the hypotheses of a promoted global theorem.

The Research Push III audit adds five narrow proved tools: the normalized
root-coordinate direct limit, finite shift-graded cylinder materialization,
exact conformal observable transport, the conditional serial-exhaustion
law, and the scalar-neck trace-mode no-go theorem.  It adds the explicit
open `END_PLUMBING_TRACE_RESPONSE_CONTROL` gate.  The supplied scalar
nodal-response, finite-horizon, strict-transition, and planar-free execution
claims are not promoted.

The Research Push IV audit proves the exact full trace response, semigroup,
scalar-collapse criterion, sharp trace-renormalized comparison, compact
half-cylinder limit, Hilbert-trace elimination law, and conditional strict
transition transfer for genuine complete-interface rectangles.  It rejects
the proposed dynamical collar: inverse pullback divides the angular
footprint by \(2^q\), so the full parent and child equipotential arcs do not
form one ray-bounded serial rectangle.  The proved no-go statement and open
`DIRECT_DECORATION_TRACE_COLLAR_REALIZATION` node keep
`END_PLUMBING_TRACE_RESPONSE_CONTROL` and H2 open.

The Research Push V audit proves the conditional active/inactive one-cell
decomposition, corrected open-atom refinement, regular-interface
fiber-product response, extended-infimum functoriality, a closed-form
pushforward no-go, and a fixed-standard-neck cap compactification.  It
rejects both proposed physical gate promotions.  An exact nested-rectangle
chain reactivates a one-sided port two levels later and bypasses the middle
shell; whole-tail uniformization also carries word-dependent endpoint
welding maps.  The new open nodes record all-depth contact closure, a true
finite-live frontier, and trace-welding compactness.

The Research Push VI audit adds only the proved
`BINARY_DIRECT_DECORATION_NESTED_SEPARATOR_CALCULUS`.  For one fixed binary
address chain, the accumulated prefix meets every future shell only on the
current separator, and physical boundary persistence is interval-convex.
This captures the Push-V rectangle bypass when composition is
prefix-to-next-shell.

The supplied finite atom automaton and protected response cocycle were not
inserted.  The atom-to-single-atom map fails in the expanding Böttcher-ray
model.  A finite relational raw mask is available under explicit
endpoint-orbit hypotheses, but its complete KL contact portrait and
trace-restriction operators are not yet realized.  A frozen overlay
normalizes in a word- and stage-dependent way, and the submitted
\(H^1\)/Dirichlet trace norm is not consistently typed.  The
complete audit is `../research_push_6_assessment_and_integration.md`, with
machine checks in `../validate_push6_separator_audit.py`.  The marked
separator, trace welding, collar, H2, MBTT, VAAPC-I, UPTCR, and MLC remain
open.

The Research Push VII audit adds the proved
`FIXED_BLOCK_BINARY_CONTACT_AUTOMATON` and
`FIXED_KKL_PAIR_STATE_MOMENT_FACTORIZATION`.  The first closes only the
unmarked structural puzzle-contact skeleton for one fixed direct-decoration
block.  The second is an exact fixed-tree Value regrouping whose dimension
depends on the terminal edge set.  The submitted boundary compiler is not
source-faithful at vertex joins, and the pseudo-piece source does not provide
the proposed ideal-arc Sobolev traces, inclusion welding, or physical
response cells.  The full audit is
`../research_push_7_assessment_and_integration.md`; all marked trace,
welding, response, H2, MBTT, UPTCR, and MLC gates remain open.

The Research Push VIII audit adds exactly two narrow proved results.
`FINITE_LINEAR_LABEL_MARKING_ENUMERATOR` solves a stipulated finite
deletion-and-seed label model by interval-convex closure and exhaustive
coarsening; it does not identify that model with a KKL immersion pullback.
`PULL_PUSH_WELDING_WORD_COMPOSITION_NO_GO` records that consecutive
pull--push operators are generally ill-typed and that the missing
interchange law fails for explicit \(2\times2\) matrices even after their
spaces are identified.  The packet's positive fixture is not a degree-one
boundary covering, its end-proper test does not inspect whole KKL end
intervals, and compiler success does not ensure that every demanded
component is proper or end-proper.  Consequently no marked analytic
interface, trace collar, welding, enlargement, transition, compactness,
rigidity, or MLC gate is promoted.  The complete hostile audit is
`../research_push_8_assessment_and_integration.md`.

The corrected source-realized follow-up proves
`TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION`,
`DEGREE_ONE_ANNULUS_IMMERSION_INJECTIVITY_NO_GO`,
`KL_TILE_INTERIOR_HOMOGENEOUS_TRACE`, and
`NONPROPER_LABEL_HULL_PULLBACK_NO_GO`.  For a fixed KL branch,
tile-component bijectivity plus tile injectivity would give an interior
embedding, but the tile premise is open: an explicit degree-one annulus
immersion has a same-tile self-collision.  Compact subarcs in one
intrinsic universal-cover tile have homogeneous Hilbert trace collars,
and a Jordan-subdomain crosscut proves that the finite deletion-and-seed
label hull need not be the KKL immersion pullback.  This historical pass
left `DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING` open; the later
canonical-localization collision pass removes it from the universal
dependency chain and reroutes the footprint problem through resolved
sheets and localization cosets.
The complete proof and obstruction are in
`../direct_decoration_path_lifted_collar_certificate.md`, with diagnostics
in `../validate_path_lifted_collared_interface.py`.  No global gate is
promoted.

The subsequent hostile fixed-branch audit proves
`KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY`,
`EMBEDDED_DISK_ACCESSIBLE_FOOTPRINT_THEOREM`, and
two no-go/conditional nodes:
`GENERAL_ANNULUS_IMMERSION_LOWER_STRIP_NO_GO` and
`COMMON_COORDINATE_NESTED_ANNULUS_OUTER_CAP`.  The named KL boundary is
the conformal ideal circle.  For an embedded disk pair, the exact KKL
pullback is the safe set defined by complete complement-footprint
containment.  A general degree-one annulus immersion need not be a
translation or lower strip.  The closed-\(O\)-port and three-atom
conclusions hold only in an explicitly common-coordinate inclusion
model.  In that pass the actual KL embedding and the
\(O\)- and \(\xi/\eta\)-footprints remained open.  The later canonical
collision resolves the full ordinary primitive canonical embedding
negatively; only restricted-stage embedding classifications remain open.
The sheet-resolved footprints, family-level disjointness, covering
refinement, and complete end-properness remain open.  Full proofs and corrections are in
`../embedded_disk_accessible_footprint_theorem.md` and
`../direct_decoration_outer_port_footprint.md`.

The next source pass proves
`KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION`.  For a degree-one annulus
immersion, a compatible universal-cover tile lift is injective exactly when
the bold base-annulus immersion is injective.  Full properness would make
the base map a one-sheeted covering, but KL prove only an embedded inner
collar and the limited end-properness used by their width argument.
The physical nesting of ordinary quadratic-like annuli cannot be
substituted for the bold ambient immersion at a general \(\psi\)-ql stage,
and the dynamical tile isomorphism is a different arrow from the inclusion
immersion.  At this stage of the audit the actual pseudo-piece embedding
remained open; the later canonical-localization theorem resolves the full
canonical seed negatively.  The
complete reduction, collision certificate, source audit, and
collar-truncation replacement program are in
`../actual_kl_tile_injectivity_gate.md`.

The same pass also proves
`KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO`.  An explicit finite Blaschke
quotient satisfies Kahn's analytic degree-one inner-boundary and exact
annular-modulus hypotheses, has no critical point in the source annulus,
and has an exact self-collision.  Gaussian-integer expansions, exact Sturm
chains, and rational Rouche disks certify the result.  It rules out an
abstract collar-to-global upgrade but does not realize the additional KL
dynamical path-space structure.  The proof and exact validator are
`../kahn_annulus_global_injectivity_no_go.md` and
`../validate_kahn_annulus_no_go.py`.

The release now includes four reproducible computational fractal plates:
a marked Mandelbrot overview, a three-scale parameter-plane zoom, a
six-parameter Julia-set atlas, and a golden-mean Siegel critical-orbit
portrait. Their exact parameters, windows, pixel counts, and iteration
cutoffs are recorded in `../figures/fractal_render_manifest.json`. These
plates are illustrations only and discharge no proof-ledger obligation.

The return-language results remain proved:
`RETURN_BASE_UNDERDETERMINATION`,
`DEMAND_CLOSED_RETURN_ATLAS_COMPILER`, and
`RETURN_ATLAS_ENLARGEMENT_NATURALITY`. Every compiled word is an actual
polynomial iterate on a nonempty selected component. Injective enlargement
preserves old words; exact complete-language stability requires a bijection
on demanded branch-component pairs. The new source pass imports
`LYUBICH_PRINCIPAL_RETURN_MAP` in its native category and proves
`NATIVE_PRINCIPAL_NEST_RETURN_ATLAS` and
`ISOTOPY_CLASS_RETURN_UNDERDETERMINATION`.

The source-facing pass proves `FIRST_DECORATION_SCALE_ESCAPE_ATLAS`,
`CRITICAL_BASE_CYCLE_EXCLUSION`, and `DECORATION_FAN_GROWTH`. It therefore
constructs the actual first direct-decoration selector and its return atlas,
then proves that a single critical base omits the intermediate little-Julia
cycle and that the raw separator marking has exponential cardinality. It does
not construct the recursive virtual selector at depth \(s\ge2\).

The present pass imports KKL's native terminal Hubbard tree in its exact
periodically repelling prime primitive category. It proves
`NATIVE_HUBBARD_SUBTREE_FUNCTORIALITY` and
`TERMINAL_CYCLE_HUBBARD_ANCHOR`: a finite marked vertex package has a unique
convex subtree, injective tree transport is exact on that subtree, and the
complete terminal cycle selects a connected native anchor and ideal
attachment side. This does not prove fullness or protected analytic
prime-end survival for a partial virtual carrier.

The follow-up type audit proves
`FINITE_EXACT_CANTOR_ENCODING_OBSTRUCTION` and
`FINITE_QUOTIENT_OBSERVABILITY_CRITERION`. An infinite virtual component
family cannot be identified injectively with a finite terminal-tree
package, and a finite quotient supports the claimed joint observables
exactly when those observables are constant on every quotient fiber. The
corrected analytic order begins with the open
`VIRTUAL_CANTOR_PACKAGE_REALIZATION`, followed by the prefix-local selector,
return correspondence, and frozen Wave horizon. Only then can the proved
abstract `VIRTUAL_PROOF_USE_TRACE_SELECTOR` interface be instantiated on
the actual virtual block and passed to the still-open terminal-tree
compatibility gate `VIRTUAL_VERTEX_PACKAGE_SELECTOR`.

The new analytic pass proves
`DIRECT_DECORATION_PULLBACK_COMPACTIFICATION` from Kahn--Lyubich's two
actual univalent \(f^q\)-pullbacks of the separator \(P\).  Finite addresses
are actual preterminal Julia pullbacks, infinite addresses are connected
nested puzzle fibers, and their planar union is compact.  The analytic
partial pre-root shift deletes the first symbol while geometric nesting
deletes the last; the empty root has a separate terminal-cycle arrow.
`PULLBACK_GAP_ENLARGEMENT_NATURALITY` proves commuting enlargement squares
inside the first-level gap.  The end fibers are not yet identified as small
Julia sets, and the newly isolated
`VIRTUAL_DISCONNECTED_MARKING_TRANSFER` remains open.  The proved
`FINITE_CYLINDER_COMMUTING_ITERATE_LIFT` supplies the exact conjugacy
formula after an equal-depth target cylinder is selected; the new
`VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR` is open.

The external-input audit proves
`COUNTABLE_FOLLOWER_STONE_COMPACTIFICATION`,
`CELLWISE_PACKET_PORT_CERTIFICATE`, and
`FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS` in their exact abstract
scopes. The first does not supply the compact geometric coupling required
by `H3_SYMBOLIC_SIDE_COMPACTNESS`; the stronger
`FUTURE_OBSERVABLE_COMPACTIFICATION` now supplies that node's formal
compact-topology branch once an exact countable presentation and
compact-target catalog are given. The second does not construct the
source-facing cell, packet, or access data required by VAAPC-I, and the
third applies only after one target base and its finite disjoint cylinder
family have been fixed. The
`VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION` remains open: it must prove
actual reached-component containment before fixed-base uniqueness can be
used by `VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR`.

The present push additionally proves the future-faithful end-topology
interface, nested finite-full-packet nonseparation, direct-decoration full
fibers and global nonseparation, the equivariant gap-cell atlas, finite
packet replacement, proper protected-impression exposure, a finite
direct-scale protected carrier, and interior pullback component forcing.
The protected theorem assumes finitely many actual chains with a proper
total boundary impression. The component theorem does not choose the target
base or authorize its reached component.

The remaining source-facing instantiation requires the open
`VIRTUAL_CANTOR_PACKAGE_REALIZATION` and
`VIRTUAL_PREFIX_LOCAL_SCALE_SELECTOR`, then the open
`VIRTUAL_RETURN_BASE_ATLAS` and `VIRTUAL_WAVE_DEMAND_SCHEMA`. They feed the
open `VIRTUAL_RETURN_BRANCH_LANGUAGE`,
`VIRTUAL_PROVISIONAL_COMPLEMENT_PAIR`, and
`VIRTUAL_ACCESS_ACTION_CERTIFICATE`, then
`VIRTUAL_WAVE_MARKED_CORRESPONDENCE` and
`VIRTUAL_WAVE_HORIZON_CERTIFICATE`.  Only afterward can the proved
future-trace interface be instantiated; `VIRTUAL_VERTEX_PACKAGE_SELECTOR`
and the final `VIRTUAL_SCALE_TO_PUZZLE_SELECTOR` remain open. Consequently `VAAPC-I`,
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`,
`VIRTUAL_COMMON_FREE_COMPONENT`, and the larger routing certificate remain
open.

The cumulative side-research library audit adds exact imports for the
Cheraghi--Shishikura and Levin satellite subclasses and the Elephant-Eyes
a-priori-bound branch, with their full hypotheses.  It proves the local
primitive-root parabolic nondegeneracy theorem, a fixed-modulus ambient-end
no-go, the serial-annulus singleton bridge, a sectorwise dyadic trace
isometry, and two response/welding no-go theorems.  It rejects the proposed
componentwise-constant trace quotient and weak graph compactification.  No
global open gate is promoted.

The latest source-complete pass proves three narrow statements.  The full
abstract degree-two \(\psi\)-ql axioms admit a remote self-collision and
therefore do not force global immersion injectivity.  A localization lift
of an independently verified physical embedding is injective exactly under
the subgroup-reflection equality \(a_*^{-1}(H_t)=H_s\); this does not
realize a general bold KL immersion as such a lift.  Finally, coherent
Kahn collars embed through a fixed finite chain only under explicit
central embedding, component bijection, exact gluing, and
collar-overlap hypotheses.  Exact relative cartesianity is essential there;
the theorem assumes the stronger full collar equality, which is not
supplied by the checked source.

The subsequent full-tile audit removes an overstrong dependency from the
fixed-pair interior embedding.  Component bijectivity gives
\(Q\cap P_{j(i)}=Q_i\), so injectivity of every full tile map automatically
reflects the collision-relevant overlap and is equivalent to injectivity
of the glued pseudo-piece map.  Full reflection over all of \(P_{j(i)}\)
is a non-gating saturation question.

The latest canonical-localization audit proves
`KL_CANONICAL_LOCALIZATION_FORCED_COLLISION`.  For every ordinary
primitive \(p\)-renormalizable seed, global degree \(2^p\) versus central
degree two supplies an excess full component of the pulled little-Julia
packet.  A Jordan peripheral loop around it is nonlocal in the source
cover but null in the target complement, so the localized inclusion
identifies two distinct source-cover points.  Kahn's exact equalizers
propagate the collision through every later inclusion leg and, whenever
the same seed carries the KL direct-decoration data, to the exact full
tile and glued pseudo-piece maps.  The universal embedded-carrier route is
therefore unavailable.  The actual \(O\)-footprint, omitted-sheet
exhaustion, uniform width error, and root-enlargement no-birth problems now
require a sheet-sensitive state retaining
\(a_*^{-1}(H_t)/H_s\).  VAAPC-I, UPTCR, and MLC remain open.

The sheet-resolution pass proves
`KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION`.  The canonical lift
factors uniquely as a covering \(q\) followed by an embedding \(e\), with
the same kernel pair as \(q\).  Winding separates all powers of the
peripheral class, so \([K:H_s]=\infty\): every full canonical collision
fiber is infinite and raw finite sheet enumeration is impossible.  Exact
base change propagates the factorization through full, unselected
complementary-cover equalizers, not through filled or prime-end
completion.

The latest pass proves
`KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT`.  Kahn's special
immersion-pullback lemma and the exact filled-set membership chain identify
the full unfilled equalizer, while the disk/FJ theorem makes its complement
connected.  Surjective \(q/e\) base change makes the resolved intermediate
connected.  For one fixed KL-eligible seed, the same
\(\mathbf U^m\)-tower is used.  For each source tile \(a\), oriented
annular degree \(+1\) identifies the pullback of target tile
\(j_\iota(a)\) with the connected source universal cover; the actual KL
lift and compatible basepoints fix deck phase.  Repeated source labels
over one target remain distinct.  This tilewise assertion is conditional on
a whole-annulus \(q/e\) factorization and does not identify the canonical
infinite sheet-resolution cover with the whole actual KL tile.

The boundary audit proves
`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY`.  In one based
universal-cover action the relevant groups split as
\(G=N\rtimes H\), with quotients by \(H,N,G\) equal to the source
annulus, resolved intermediate, and image factor.  A nontrivial universal
cover, and every nonconstant deck-invariant composite, has no continuous
point-valued extension at a deck-limit point.  The two finite-modulus
resolved-source annular wrapping ends \(\zeta_\pm\) lie in the kernel
limit set when \(N\ne1\).  KL's actual-tile ends \(\omega_\pm\) are its
named wrapping vertices and \(L_a\) extends there.  The based
biholomorphism transports
\(\overline\Phi_a(\omega_\pm)=\zeta_\pm\), and
\(K_a=L_a\Phi_a^{-1}=e_aq_a\) is the invariant resolved-source
composite.  Thus any whole-tile covering/embedding factorization of that
actual map must be one-sheeted.  The prior identification of the
canonical infinite resolution with the whole actual KL tile is therefore
quarantined.

The valid replacement is relative: on a deck-invariant subset of the
domain of discontinuity, the quotient ideal bordification is Hausdorff
and every continuous invariant composite extension descends uniquely.
The next audit therefore tests which map-level interface, if any, can
compare the canonical resolution with the independently source-defined KL
tile map without importing the forbidden full factorization.

The correspondence audit then proves
`CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO`.  A whole-tile square
cannot simultaneously use the based universal-cover identification,
conjugate the annular deck generators, retain an injective target
comparison, identify the two interior composites, and carry the wrapping
ends to KL's source-defined continuous boundary values when the canonical
deck kernel is nontrivial.  The ordinary primitive canonical kernel is
infinite, so this closes the whole-tile option negatively.  It does not
prove that the actual KL immersion is injective: an explicit
non-covering holomorphic immersion of the disk is noninjective and still
extends continuously to the closed disk.

The next proposition constructs one replacement for every supplied fixed
labeled same-source datum: the relation span, its tagged étale family of
maximal interior restrictions, non-descent, and the two wrapping cluster
values.  It also records the narrowly unscaled annulus-width no-go,
unchanged-equalizer retiming persistence, and the localization subgroup
criterion with its lift hypothesis.  It does not extend a tile map over
the whole standalone ideal circle or prove map properness/end-properness on
complete Wave intervals.

The geometric-trace pass then proves
`FULL_KL_PSEUDOPIECE_MAXIMAL_LIFT_PROPERNESS`: for one supplied full KL
pseudo-piece datum with its continuous KL ideal-boundary extension, every
maximal parametrized lift of a KKL-proper path has unique ideal endpoints
with exact endpoint naturality.  It separately proves
`PARAMETRIZED_PULLBACK_KKL_EXHAUSTION_NO_GO`: a parametrized fiber product
need not exhaust the geometric inverse trace, and one locally univalent
disk immersion can have infinitely many distinct proper source
restrictions.  Neither proposition proves whole-interval map properness,
end-properness, a bounded KKL response, or final-root no-birth.

The immediate constructive gate is now
`DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER`.  It must freeze the complete
target-family and universal-subordination ledger before the actual
canonical/KL stage alignment, relation-valued proper-path/end-interval
classification, response estimate, and independent geometric final-root
no-birth theorem can be attempted.

The exact subgroup formulas now test merger and birth only for the based
coset map.  They do not detect a new simply connected geometric component
or access.  After a restricted or revised interface is typed, the boundary
work must
retain the deck group, its limit set and domain of discontinuity, the
actual KL incidence relation, interval stabilizers, interior phase, and
all target cluster defects.  It must then enumerate landing components
and isolate exactly one KKL-proper lift (or classify every competing lift)
for each witness.  The conditional safe-set criterion also assumes the
explicit endpoint-subordination rules on the authorized boundary model.
VAAPC-I, UPTCR, and MLC remain open.

The latest stationary-Wave pass proves Kahn fiber-product filled-graph
naturality, realizes the two KKL final graph lifts as distinct whole
components, and corrects their final degree from one to two.  It also
proves one retained restriction chain for every selected unbreakable leaf.
It does not certify KKL line 1603: binding its two topological portions to
two coherent retained occurrences, marked-access transport, selected-collar
confinement, and deck-path noncollision remain open.  The off-by-one repair
is therefore conditional, and the actual two-pullback pass-through node is
open.  The bounded-visits strict-growth step, final
proper-path/measurable-lamination extraction, occurrence order, fixed-pair
restriction, and KL puzzle realization remain open as well.

The release audit requires:

- zero LaTeX, BibTeX, box, citation, and reference warnings;
- all finite adversarial regressions passing;
- extracted-text confirmation of the open MLC disclaimer and ledger counts;
- targeted rendered inspection only when a changed layout or figure cannot
  be validated from the build log and extracted text; bulk all-page visual
  sweeps are not required for text-only revisions; and
- synchronization of `build/main.pdf` with
  `../output/pdf/marked_width_mlc_manuscript.pdf`.
