# Post-repair semantic audit

Date: 2026-07-23

## 1. Scope and verdict

This audit compares the live statements, dependencies, and evidence anchors in
`proof_obligations.json` with the Markdown proof texts after the transfer/automaton
repairs. It specifically retests:

- entropy assigned to an unframed open transfer;
- acyclic zero singleton SCCs;
- permutation interior transport being mistaken for a clone;
- the counter-fiber condition being overstated as a global necessity;
- omission of nilpotent extinction;
- the degenerate one-vertex clone;
- LIFO stack behavior being inferred from set-theoretic nesting;
- obsolete ledger counts.

At the pre-KKL-clone-audit snapshot, the machine ledger was syntactically valid:

```text
ledger: valid (126 obligations)
statuses: imported=9, proved=91, open=26
target: MLC [open]
```

All six executable transfer regressions pass:

```text
PASS test_product_orientation
PASS test_open_endpoint_gauge
PASS test_boolean_support_functor
PASS test_zero_scc_and_extinction_examples
PASS test_future_index_obstructions
PASS test_counter_fiber_is_not_global_invariance
```

The repaired **proved ledger nodes** for the targeted matrix and language claims now
match their primary proof sections. In particular,
`IRREDUCIBLE_TRANSFER_ENTROPY_DICHOTOMY`,
`BOUNDED_BRANCH_SUPPORT_WITNESS`,
`PERMUTATION_COCYCLE_GAUGE`, `DEFECT_RUN_DECOMPOSITION`,
`CLONE_STRONG_CONNECTIVITY`, `COUNTER_SAFE_PUMPING`, and
`ZERO_ENTROPY_SHEAR_NORMAL_FORM` may remain `proved` in their current narrowed
scopes.

There are nevertheless two live stale summaries, three material evidence/statement
drifts in open nodes, and one unsupported uniform-dimension sentence in a proved
abstract theorem. None proves MLC, and none permits promotion of an analytic node.

## 2. Material findings

### F1 — two live summaries again assign entropy to unframed layer transfers

**Severity: material.**

`block_contraction_program.md:226-230` says that “irreducible non-permutation layer
transfers have a uniform graph entropy gap” and contrasts them only with reducible
spectral-radius-one shear. `virtual_clone_entropy.md:412-416` repeats essentially the
same claim.

Both formulations are stronger than the repaired theorem. The actual result in
`corridor_entropy_shear_dichotomy.md:78-138` applies to a nonzero irreducible
**framed return endomorphism**; `corridor_entropy_shear_dichotomy.md:45-49` and
`transfer_convention_and_frame.md:74-111` prove that an open layer has no intrinsic
spectral radius. The summaries also omit the \(\rho<1\) transient/extinction part of
the nonexpanding branch proved at
`corridor_entropy_shear_dichotomy.md:140-179`.

An independent target relabeling of
\[
S=\begin{pmatrix}1&1\\0&1\end{pmatrix}
\]
to \(JS\) changes its spectral radius from \(1\) to
\((1+\sqrt5)/2\), so “open layer entropy” is not a harmless shorthand.

**Required correction.** In both summaries replace “layer transfers” by “nonzero
irreducible closed or canonically framed return endomorphisms,” and describe the
complement as all nonexpanding framed returns: transient extinction or recurrent
feed-forward shear.

### F2 — `H2_ENTROPY_DICHOTOMY` points to unrelated evidence

**Severity: material ledger/evidence drift.**

The ledger statement at `proof_obligations.json:1129-1139` requires:

- entropy only on closed source-framed returns; and
- every nonexpanding residual routed to extinction, sectorial regularization, or a
  calibrated shear state inside a strictly contracting augmented block.

Its evidence is
`corridor_network_calibration.md#10-arithmetic-density-gate`. That section,
`corridor_network_calibration.md:441-485`, proves only the identity
\(N/(n+1)=2p\) and states a bounded-shift/large-shift chart gate. It neither states
nor proves the ledger obligation, and it does not contain the required strict
contraction of the retained-shear branch.

The dependency list is directionally sensible, but an anchor existing is not semantic
evidence. The current node is correctly `open`; the defect is traceability, not a
reason to promote or demote it.

**Required correction.** Add a dedicated open theorem section stating the exact
`H2_ENTROPY_DICHOTOMY` quantifiers and point the ledger there. Keep the arithmetic
density lemma as a dependency or local obstruction, not as the theorem evidence.

### F3 — `H1_MARKED_CONSTRUCTION` has outgrown its evidence section

**Severity: material ledger/evidence drift.**

The ledger statement at `proof_obligations.json:1043-1060` now requires faithfully
marked finite-control corridor/transfer blocks with a universal number of explicit
counters and, only if source-realized, a finite-alphabet molecule stack.

The cited evidence is
`virtual_hull_realization.md#6-finite-virtual-wad-realization-theorem`.
Its combined theorem at `virtual_hull_realization.md:373-414` asks for a carrier,
cell-tree/access data, a selected telescope, KKL translation marking, width charge,
parallel replication, and chart comparison. It does not state a finite-control
language, counters, stack memory, future equivalence, or counter/stack update rules.

Those requirements now live in
`virtual_language_memory.md:280-325` and
`virtual_support_automaton_construction.md:876-919`, but neither appears as a
dependency of `H1_MARKED_CONSTRUCTION`. This also leaves the architectural boundary
between H1 carrier construction and H2 follower construction ambiguous.

**Required correction.** Either narrow H1 back to carrier/telescope/access
construction and leave counter/stack follower realization wholly in H2, or expand the
H1 evidence section and dependencies to state exactly which finite-control side data
H1 constructs. Avoid making H1 depend circularly on a theorem that already depends on
H1.

### F4 — the strengthened virtual trichotomy statement is not present at its anchor

**Severity: moderate ledger/evidence drift.**

`proof_obligations.json:961-976` states a source-faithful
**counter/stack-follower** trichotomy whose eligible loops are counter-fiber-safe and
stack-neutral. The cited open theorem at
`corridor_entropy_shear_dichotomy.md:234-277` states the frame, clone, positive
entropy, extinction, and shear clauses, but contains no counter, stack, or
stack-neutral qualification.

The dependency on `H2_VIRTUAL_SUPPORT_AUTOMATON` imports some of that content
transitively, so this is not an omitted blocker in the dependency graph. It is still
a mismatch between the literal ledger theorem and its declared evidence.

**Required correction.** Add the counter/stack-follower hypothesis and
fiber-safe/stack-neutral eligibility clause to the open theorem itself, or split the
trichotomy into a transfer theorem and a separately cited follower-interface theorem.

### F5 — the master side-state wording can discard the raw nesting word before LIFO
is proved

**Severity: moderate architectural inconsistency.**

`master_transition.md:248-250` says that \(\omega_n\) records ordered molecule data
“only if” a source theorem proves a finite-alphabet stack rule. The source audit
reaches the opposite safe default:
`source_ledger.md:434-442` says that D25/KKL do not prove push/pop or reverse order and
therefore the full labeled word cannot be replaced by its depth. The correctly
phrased block interface at `block_contraction_program.md:46-48` retains the explicit
word and permits a LIFO **update** only after the source theorem.

The distinction is substantive:

- retaining a raw word is lossless side data;
- treating that word as an operational LIFO stack is an additional theorem.

**Required correction.** Make the master state always retain whatever ordered word
future admissibility needs. State that push/pop compression is enabled only after a
source-faithful LIFO theorem; otherwise the word remains opaque/uncompressed or is
replaced by a stronger follower invariant.

### F6 — the cell-tree theorem does not derive a uniform core-transfer dimension

**Severity: material theorem-text overclaim; the ledger is already narrower.**

`virtual_support_automaton_construction.md:486-499` concludes that universal bounds
in `CT3` and `CT4` make both the automaton state count and the **transfer dimensions**
universal. But:

- `CT3`, at `virtual_support_automaton_construction.md:444-451`, bounds the signature
  catalogs and structural token catalog;
- `CT4`, at `virtual_support_automaton_construction.md:453-457`, requires future-safe
  WAD compression.

Neither clause explicitly bounds the core dimension \(d\). A family with one control
state, one identity token \(B=I_d\), no WAD coordinates, and one Markov signature has
uniform future index and satisfies the formal finite-state conditions while
\(d\to\infty\). The state bound does not bound matrix dimension.

The proved ledger node `MARKOV_SIGNATURE_AUTOMATON` claims only a uniformly finite
automaton, so it does not need demotion. The prose theorem should either add
\(d\le d_0\) (and the relevant WAD bound) to its hypotheses or delete “and transfer
dimensions are universal.”

## 3. Targeted repairs that now pass

### Open-transfer entropy

The primary theorem files are correct:

- `transfer_convention_and_frame.md:72-129` restricts spectral certification to a
  framed return;
- `corridor_entropy_shear_dichotomy.md:45-49,120-138,271-273` repeats the restriction;
- `corridor_support_automaton.md:170-176` labels its Perron bound as a bare displayed
  matrix statement until closure/source identity are proved.

Only the two summaries in F1 regress.

### Zero SCCs

`corridor_entropy_shear_dichotomy.md:80` excludes the zero irreducible boundary with
the explicit word **nonzero**.
`corridor_support_automaton.md:136-139` requires a cyclic SCC containing a
positive-length closed walk and classifies the acyclic zero singleton as transient.
The corresponding ledger statements at
`IRREDUCIBLE_TRANSFER_ENTROPY_DICHOTOMY` and
`BOUNDED_BRANCH_SUPPORT_WITNESS` match.

### Permutation does not imply clone

`corridor_entropy_shear_dichotomy.md:51-71` proves only an identity interior gauge and
explicitly reserves side edges, endpoint multiplicities, the cross section, critical
data, and WAD incidence for the clone certificate.
`proof_obligations.json` states the same limitation in
`PERMUTATION_COCYCLE_GAUGE` and `DEFECT_RUN_DECOMPOSITION`.

### Counter-fiber safety

`virtual_language_memory.md:202-229` now gives the exact reachable-fiber equality
\[
\Phi(\nu+\eta)=\Phi(\nu+\Delta+\eta)
\]
and says that zero increment or fiber invariance is sufficient, not pathwise
necessary. `COUNTER_SAFE_PUMPING` matches it.

### Extinction

`corridor_entropy_shear_dichotomy.md:140-179` covers all \(\rho\le1\), includes zero
diagonal SCCs, and proves nilpotence when no recurrent cycle exists.
The open trichotomy at `corridor_entropy_shear_dichotomy.md:248-252` routes a purely
transient block to extinction. The ledger nodes
`ZERO_ENTROPY_SHEAR_NORMAL_FORM`, `H2_VIRTUAL_TRANSFER_TRICHOTOMY`, and
`H2_ENTROPY_DICHOTOMY` contain extinction.

### Clone degeneracy

`dynamical_corridor_certificate.md:83-95` now assumes every gate vertex lies on a
positive-length closed walk. The robust primitivity witness at
`dynamical_corridor_certificate.md:97-128` automatically excludes the edgeless
singleton. `CLONE_STRONG_CONNECTIVITY` matches the narrowed lemma.

### Stack is not inferred from nesting

The source boundary is correctly explicit in:

- `source_ledger.md:434-442`;
- `virtual_language_memory.md:132-155,280-325,343-344`;
- `virtual_support_automaton_construction.md:600-618,903-906,927`;
- `adversarial_audit.md:84`.

No checked source is credited with LIFO antirenormalization. F5 is a side-state
wording inconsistency, not a false imported source claim.

## 4. Historical counts and superseded prose

No occurrence of “123 obligations” exists. The only numerical `123` match is a source
line range in `virtual_automaton_source_research.md:380`.

The two occurrences of “115 obligations” are historical snapshots:

- `research_log.md:950-951`, followed by the later repaired count at
  `research_log.md:1030-1034`;
- `support_automaton_redteam.md:693-705`, explicitly called “the ledger snapshot
  reviewed here,” followed by the remediation status and current count at
  `support_automaton_redteam.md:751-768`.

They are not live-count contradictions. The old research-log entry also preserves
superseded shorthand at `research_log.md:818-851` and
`research_log.md:930-940`; the corrective entry at
`research_log.md:988-1023` expressly lists and repairs those errors. This is valid
chronological documentation, although adding a “superseded by the repair entry below”
note to the older headings would reduce search-result ambiguity.

The `124 obligations / 90 proved / 25 open` figures at
`research_log.md:1030-1034` and `support_automaton_redteam.md:765-768` are now also
historical repair-point snapshots. The increase to 126 at that audit point consists
of the proved
discrete-side-data compactness obstruction and the open
`H3_SYMBOLIC_SIDE_COMPACTNESS` obligation. Their evidence in
`virtual_language_memory.md:357-383` matches: a discrete unbounded counter/word space
is not precompact, and forgetting, bounding, or continuously compactifying the side
data remains open.

## 5. Dependency conclusion

The targeted algebraic repair chain is now sound at its stated scope:

\[
\text{source-column convention}
\Longrightarrow
\text{framed-return spectral invariance}
\Longrightarrow
\begin{cases}
\text{cycle permutation},\\
\text{positive irreducible gap},\\
\text{extinction/common-flag shear}
\end{cases}
\]

and finite support pumping remains only a Boolean skeleton theorem with contextual
loops retained. Counter and stack state are not discharged by that pumping theorem.

The remaining defects in this report do **not** supply a proof of the virtual
realization theorems. After correcting F1--F6, the live analytic frontier remains:
construct the source-faithful virtual core correspondence, prove a uniform
counter/stack or replacement follower invariant, realize the framed transfer
trichotomy with WAD/Value incidence, and prove strict calibrated complete-block
contraction together with symbolic side-data compactness. MLC remains open.

## 6. Remediation status after the second audit

This section records later changes; the line numbers and count in Sections 1--5 are
the historical snapshot that was audited.

- **F1 fixed.** Both stale summaries now restrict the entropy gap to nonzero
  irreducible closed or canonically framed returns and include transient/nilpotent
  extinction.
- **F2 fixed.** `H2_ENTROPY_DICHOTOMY` now points to the dedicated routing clause in
  `block_contraction_program.md`, Section 3.
- **F3 fixed.** `H1_MARKED_CONSTRUCTION` is narrowed to the raw carrier, access,
  critical-return, and stopping-time construction. Uniform finite control,
  counters, stack discipline, module dimensions, and memory-safe compilation are H2
  obligations.
- **F4 fixed.** The open Virtual Corridor Transfer Trichotomy now explicitly assumes
  the exact counter/stack follower, reachable-fiber-safe repetitions, and retained
  loop emissions.
- **F5 fixed.** `master_transition.md` always retains any future-relevant raw nesting
  word; it is operated on as a stack only after a source-faithful LIFO theorem.
- **F6 fixed.** `CT0` separately requires \(d\le d_0\) and \(w\le w_0\); the
  signature theorem no longer claims those bounds.

The later KKL source audit also invalidated a stronger assumption not tested in this
snapshot: its symbol \(T_F\) has incompatible orientation cues, and its printed
\(+\lambda^k\) finite-\(n\) clone equation fails on an explicit primitive graph.
The live project now locks \(B=N^{\mathsf T}\), KKL \(v,w\) as project
left/right, and Value \(v^2w\). The printed equation remains rejected, while
`corrected_clone_theorem_derivation.md` independently proves the exact
\(t^{-k}\) literal-clone equation, fixed-template limit, both typed gate-eigenvector
limits, and the \(n>K\) multiplier bound. Two independent red-team notes validate
that repair and record its nonuniform-template and perturbation boundaries.

The current machine snapshot, after integrating the Section-4, tame, long-Wave,
and finite inverse-tree fan audits, is:

```text
ledger: valid (156 obligations)
statuses: imported=11, proved=114, open=31
target: MLC [open]
```

## 7. Attachment-support audit update

The preceding count is now historical. The KKL corridor source pass added:

- imported `KKL_IDEAL_PULLBACK_NATIVE`;
- proved `ATTACHMENT_SUPPORT_REDUCTION`; and
- open `VIRTUAL_BOUNDED_ATTACHMENT_SUPPORT`.

The open node is deliberate. It prevents the project from silently replacing
KKL's actual local equality
\(\mathcal T'=\mathcal T\) by pullback-component saturation or by equal
translation labels. The live machine snapshot is:

```text
ledger: valid (159 obligations)
statuses: imported=12, proved=115, open=32
target: MLC [open]
```

The diagnostic suite now includes an explicit terminal attachment-window
regression and has 16 passing tests. These tests validate the finite
degree-weighted arithmetic only; they do not construct the virtual carrier.

## 8. Root-carrier reduction update

The subsequent carrier pass added two internal theorems and one explicit
open realization node:

- proved `ROOT_PULLBACK_FOREST_EQUIVALENCE`;
- proved `CRITICAL_VALUE_CORRIDOR_CRITERION`; and
- open `VIRTUAL_ROOT_CARRIER_SEPARATION`.

The live snapshot is now:

```text
ledger: valid (162 obligations)
statuses: imported=12, proved=117, open=33
target: MLC [open]
```

This refinement replaces free connector choices by one simultaneous root
component-routing problem. It does not reduce the open count artificially:
existence of the required root remains unproved.

## 9. LaTeX synchronization and release audit

The formal manuscript in `latex/` now imports its obligation appendix from the
machine ledger through `generate_ledger_tex.py`. This prevents the prose release
from presenting a stale obligation count or silently changing an obligation's
status. The generated appendix reports:

```text
ledger: valid (162 obligations)
statuses: imported=12, proved=117, open=33
target: MLC [open]
```

The first 31-page PDF release passed all 16 diagnostic transfer regressions,
compiled with zero LaTeX/package/box/reference/citation warnings, and passed
rendered-page and extracted-text checks. This is a consistency and presentation
audit only. The manuscript's main global statement remains conditional, and
`VIRTUAL_ROOT_CARRIER_SEPARATION` plus
`VIRTUAL_BOUNDED_ATTACHMENT_SUPPORT` remain explicit open inputs to the combined
Virtual Seed and Attachment theorem.

## 10. Corridor pair-naturality audit update

The attachment-transport pass added:

- proved `CORRIDOR_ATTACHMENT_TRANSPORT`;
- open `VIRTUAL_CORRIDOR_PAIR_NATURALITY`; and
- open `VIRTUAL_ATTACHMENT_FREE_ANCHOR`.

The live snapshot is now:

```text
ledger: valid (165 obligations)
statuses: imported=12, proved=118, open=35
target: MLC [open]
```

The new theorem proves that a commuting orientation-preserving homeomorphism
of the actual pulled/immersed carrier pairs transports attachment components,
supporting ideal intervals, and proof-used prime-end sides bijectively. One
attachment-free anchor then clears the entire natural degree-one corridor.

The two open nodes are intentional. Root routing gives only the selected
polynomial-carrier homeomorphism; it does not give the ambient pair square or
its prime-end extension. Likewise an anchor cannot control later stages until
that naturality is proved. The diagnostic suite now contains 17 passing
regressions.

## 11. Univalent pair and anchor-obstruction audit

The planned anchor pass added:

- proved `UNIVALENT_CARRIER_PAIR_TRANSPORT`;
- proved `ATTACHMENT_FREE_ANCHOR_UNDERDETERMINATION`; and
- proved `FINITE_ATTACHMENT_ORBIT_CLOSURE`.

The live snapshot is:

```text
ledger: valid (168 obligations)
statuses: imported=12, proved=121, open=35
target: MLC [open]
```

The proof constructs pair naturality only after one actual anchor pair is
supplied and transported in its entirety through the univalent corridor.
Prime-end functoriality requires no local connectivity. The interval/triod
countermodel shows that the published connected-hull description does not
select an attachment-free anchor. The finite least-closure theorem records
the replacement invariant and makes every collision under monotone absorption
permanent.

Accordingly `VIRTUAL_CORRIDOR_PAIR_NATURALITY` and
`VIRTUAL_ATTACHMENT_FREE_ANCHOR` remain open. The regression suite now
contains 20 passing diagnostic tests.

## 12. Canonical-interface and protected-access audit

The follow-up pass added four proved obligations:

- `INTERFACE_PROOF_USE_INVENTORY`;
- `FINITE_GEOMETRIC_SATURATION`;
- `CONNECTED_CARRIER_NO_MINIMUM`; and
- `QUADRATIC_PROTECTED_ACCESS_COLLISION`.

It also added the open obligation
`VIRTUAL_CANONICAL_INTERFACE_CARRIER`. The synchronized snapshot is:

```text
ledger: valid (173 obligations)
statuses: imported=12, proved=125, open=36
target: MLC [open]
```

A finite proof-use ledger now has one minimal typed inventory, but that
inventory is not a connected planar carrier. Two points have no least
connected full carrier, so "minimal connected hull" cannot supply Dudko's
missing connector rule.

The analytic obstruction uses \(f(z)=z^2\) on
\(U^-=\{|z-3/2|<1\}\). The first excess is the upper half-disk minus its
diameter \([1,2]\), its attachment trace is the entire diameter, and its
right-sheet itinerary has zero critical word. Absorption erases the protected
upper access at \(3/2\), so only \(\chi_{\rm access}\) is nonzero. The
replacement invariant retains the full attachment trace and partial
protected-access survival map.

No virtual theorem is promoted. The new open carrier obligation is a direct
dependency of `VIRTUAL_CORRIDOR_PAIR_NATURALITY` and
`VIRTUAL_ATTACHMENT_FREE_ANCHOR`. The regression suite contains 23 passing
diagnostic tests after integration.

## 13. UPTCR closure-package audit

The formal UPTCR pass adds exactly one open mathematical package and one
proved conditional implication:

- `UNIVERSAL_PROTECTED_TOWER_CLOSURE` is open and depends on the existing
  marked-construction, transition, compactness, and rigidity gates;
- `UPTCR_IMPLIES_MLC` is proved with `YOCCOZ` and `BACKWARD_RECORD` as proof
  dependencies and UPTCR as an explicit open hypothesis.

The proposition has six clauses. The ledger and manuscript do not collapse
them into the backward transition: construction, analytic realization,
response realization, compactness, and rigidity remain separately visible.
The rigidity clause includes nested compact connected **relative
neighborhoods** whose intersection is the full marked fiber, preventing the
invalid shortcut from a bare singleton fiber to local connectivity.

The source audit retains the exact scopes:

- Dudko's virtual-Julia-set paragraph is motivation and an open strategy;
- KKL Theorem B applies to prime primitive types with beau bounds and bounded
  puzzle Teichmüller diameter, not automatically to mixed towers.

The machine snapshot after this semantic integration is:

```text
ledger: valid (175 obligations)
statuses: imported=12, proved=126, open=37
target: MLC [open]
```

No status is promoted for `MLC`, `H1_MARKED_CONSTRUCTION`, `MBTT`,
`H3_COERCIVITY`, or `H4_RIGIDITY`. The regression suite contains 26
passing diagnostic tests after UPTCR integration.

## 14. Independent UPTCR cross-validation

The independent audit in `uptcr_cross_validation.md` found three statement
defects and repaired them without promoting a proof gate:

- “exactly one degree-two stage” is restricted to the selected quadratic
  return spine; auxiliary fan branches retain degree \(2^{m(\beta)}\);
- a bounded defect window bounds a charge only after a protected local model
  with zero fatal collision invariant has been obtained; and
- the block alternatives are inclusive certified routes, not an unproved
  disjoint trichotomy.

The conditional implication was rechecked through the invariant-line-field,
affine-normalization, singleton-fiber, and relative-neighborhood steps.
Those steps are now explicit in both the Markdown proposition and LaTeX
manuscript.

The attempted proof of the open hypothesis stops at its first clause.  The
finite predecessor-cell inventory has no source-proved regulated connector
or protected-access survival theorem.  Moreover, the existing
upper-half-disk quadratic example proves that monotone absorption alone
cannot supply one: it destroys a protected access even on a univalent
critical-value-free branch.  Thus the audit proves nonclosure of the current
derivation, not failure of UPTCR or MLC.

The synchronized snapshot is:

```text
ledger: valid (176 obligations)
statuses: imported=12, proved=127, open=37
target: MLC [open]
```

The ledger node `UPTCR_CROSS_VALIDATION` is proved, all six UPTCR clauses
remain open, and the diagnostic suite contains 29 passing tests.

## 15. Protected regulated connector audit

The connector pass proves one new conditional-input realization theorem
without promoting the virtual dynamical gate.

`PROTECTED_REGULATED_CONNECTOR_REALIZATION` is proved from an explicit
protected ribbon-routing certificate. The actual carrier is the union of
the full atoms, singleton free-port arcs, and a finite embedded ribbon tree.
The one-point attachment theorem proves fullness. Terminal crosscut domains
remain disjoint from the connector, so all declared prime ends survive
injectively and in cyclic order without a local-connectivity assumption.
The construction commutes exactly with univalent maps between Jordan
localizations.

The KKL lamination-lifted Hubbard tree is used only as a native positive
control and model for the canonical candidate. The new open obligation
`VIRTUAL_PROTECTED_ROUTING_CERTIFICATE` requires the actual virtual-Molecule
candidate to verify protected-collar avoidance, whole-package component
containment, parent routing, sheet separation, critical words,
obstacle/localization closure, future access completeness, and uniform
incidence or faithful compression.

The upper-half-disk model fails the new certificate at the correct place:
its trace is not a singleton and the excess occupies the protected upper
collar. A lamination lift can also fail if one projection fiber enters a
protected fjord. Thus connectedness is no longer confused with access
survival.

The follow-up `virtual_protected_routing_domain.md` proves the exact
topological selection criterion: one completed free-domain component must
have simultaneous singleton ports to all root-shadow clusters. A first
collar or obstacle separating two port classes is an exact
monotone-unrepairable obstruction. The actual assertion
`VIRTUAL_COMMON_FREE_COMPONENT` is open.

```text
ledger: valid (183 obligations)
statuses: imported=13, proved=130, open=40
target: MLC [open]
```

All 36 diagnostic regressions pass. The common-component and full routing
certificates are direct dependencies of
`VIRTUAL_CANONICAL_INTERFACE_CARRIER`; UPTCR-1 and MLC remain open.

## 16. Augmented-atom proof audit

The next pass proves only the planar implication
`AUGMENTED_ATOM_COMMON_DOMAIN`. Its proof uses the arbitrary-compacta form
of Alexander duality: each full continuum has vanishing first Čech
cohomology, finite disjoint unions preserve that vanishing, and adding
\(S^2\setminus U\) gives connected complement inside the Jordan
localization. Explicit port arcs then place every original root-shadow atom
in one component of the original free domain.

The proof does not infer accessibility from local connectivity, does not
claim a canonical spanning tree, and does not obtain a uniform marking
bound. The actual virtual assignment, post-fullification disjointness, and
surviving ports are the open
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`.

The annular regression distinguishes the two failure levels. Fullification
either merges the separated obstacle with an enclosed atom or makes that
atom interior and erases its port. This refutes the attempted augmented
packet. `VIRTUAL_COMMON_FREE_COMPONENT` is refuted only when the annulus is
also proved to separate the original frozen free domain. No packet
collision is silently promoted into a dynamical counterexample.

## 17. Fixed-packet closure proof audit

`augmented_packet_closure_audit.md` promotes only
`AUGMENTED_PACKET_CLOSURE_AUDIT`.  Its absorption identity proves that a
fixed finite assignment has one order-independent completed packet per
label.  The collision audit uses the actual intersection point and the raw
seed or bounded complementary chamber on each side; it does not infer
disjointness from disjoint raw seeds.

The port argument also has the correct quantifier.  It assumes one actual
unprotected access landing on each original atom, then truncates the finite
family inside pairwise disjoint packet neighborhoods.  It does not infer an
access from boundary membership or local connectivity.

Monotone persistence is restricted to fixed labels.  Reassigning a piece,
changing the root/sheet partition, retiming the block, or revising the
localization changes the problem and is not covered.  The theorem is
topological and proves no uniform width.

Accordingly `VAAPC-I`, `VAAPC-C`, `VAAPC-P`, `VAAPC-H`, and `VAAPC-U`
remain source-open, as do `VIRTUAL_COMMON_FREE_COMPONENT`, UPTCR-1, and MLC.

```text
ledger: valid (184 obligations)
statuses: imported=13, proved=131, open=40
target: MLC [open]
diagnostic transfer regressions: 39 passed
```

## 18. VAAPC-I horizon-first source audit

`vaapc_inventory_source_audit.md` promotes only
`HORIZON_FIRST_INVENTORY_AUDIT`.  For a fixed finite typed horizon graph,
dependency reachability from the complete proof-use seed set is the unique
least source-complete inventory.  The proof is a finite monotone-closure
argument.  Its horizon-extension clause is exact: the old slice remains
frozen if and only if no extended proof seed reaches an omitted old record.

The theorem does not supply the graph.  The checked Dudko paragraph gives
the virtual-Molecule copy chain and the connected-hull strategy, but its
“appropriate number” of first returns has no stopping rule.  Thus the first
undefined `VAAPC-I` field is \(N_{\rm stop}\), before component enumeration
or packet assignment begins.

KKL's native proof-use data are not silently reused.  Transport would
require a typed bridge preserving actual components, dependency paths,
stage branches, critical words, sheets, and proof-used prime ends.  That
bridge is not constructed in the checked sources.

Accordingly:

- `HORIZON_FIRST_INVENTORY_AUDIT` is proved;
- `VIRTUAL_WAVE_HORIZON_CERTIFICATE` is added and open;
- the typed assignment part of `VAAPC-I` remains open after the horizon;
- no status is promoted for `VAAPC-I`, `VAAPC`, UPTCR-1, UPTCR, or MLC.

```text
ledger: valid (186 obligations)
statuses: imported=13, proved=132, open=41
target: MLC [open]
diagnostic transfer regressions: 42 passed
```
