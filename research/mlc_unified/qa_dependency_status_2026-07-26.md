# Dependency and status QA — 2026-07-26

## 1. Verdict

This is a frozen QA-0/QA-1 audit.  It changes no mathematical status and
does not edit the manuscript, the machine ledger, or generated LaTeX.

The current ledger is **internally valid under its declared dependency
semantics**, but it is **not yet safe as a future promotion mechanism**.
There is no present false declaration of MLC, UPTCR, VAAPC-I, or the native
KKL stationary repair as proved.  All four remain open.  Two high-priority
dependency-architecture defects must nevertheless be resolved before any
new promotion:

1. three VAAPC clauses are represented only by non-semantic `maps_to`
   records, and making the complete-horizon clause semantic exposes a
   dependency cycle; and
2. the live ledger and the latest dependency narrative encode two different
   stationary-repair routes.

The audit also found incomplete local source custody, omission of formal
`hypotheses` from the generated TeX ledger, and nine unconsumed open gates
that need an explicit active/optional/superseded classification.

No critical finding establishes that a currently proved mathematical
theorem is false.  The findings concern logical traceability, reproducible
source custody, and prevention of a future unsupported promotion.

## 2. Frozen inputs and immutable snapshot

### 2.1 Ledger and release

The authoritative ledger at this checkpoint is:

```text
obligations: 423
imported:     28
proved:      291
open:        104
target:      MLC [open]
```

Key hashes:

| artifact | bytes | SHA-256 |
|---|---:|---|
| `proof_obligations.json` | 310,548 | `D8003A5D1BC288C90CBF7050001802A7DC403E602A344A7D8B11BF7F068D0ABF` |
| `README.md` | 113,419 | `80EEA3469C08023FAF6FAD73F086C441EC6F74CAE924AC47EC497933024FBFBC` |
| `source_ledger.md` | 152,978 | `FDA61A5E3067999F6EE4DF8412224CFB1294AA44F292C0D46C8C80594A9D007E` |
| `dependency_audit.md` | 167,736 | `6A0D1A7C48D9BBC18DD16F9B218251CDA67F0AB2CE901010B732003FE7266F9D` |
| `manuscript.md` | 107,024 | `7328F6C65B7E4BD6F9BA401DF74B2FD37FD10ECB2EAD14038887D8A72E1559B7` |
| `latex/generated/ledger_counts.tex` | 219 | `1BE8C3D0E7EC4EAF9A5C9951492746B3CACC006381780376B96FB0F76CF8C282` |
| `latex/generated/obligations.tex` | 479,156 | `4EA3741F6191047A8859BDE621AF3629E1B54843AE94FD892440028507988BC1` |
| build PDF | 5,934,669 | `58183A22CB3CA98832BDF3AA1C9857D9DA8AF97E040A4BDBDDAF7DCD56FDA834` |
| released PDF | 5,934,669 | `58183A22CB3CA98832BDF3AA1C9857D9DA8AF97E040A4BDBDDAF7DCD56FDA834` |

The build and released PDFs are byte-identical.  No broad visual PDF scan
was performed in this pass.

The 108 distinct ledger-evidence files, together with seven authoritative
status/build surfaces not already among them, form a 115-file active
artifact set.  For canonical lines

```text
<uppercase SHA-256><two spaces><forward-slash relative path>\n
```

sorted by relative path, the manifest digest is

```text
479E1D28DA21479021ACA7BEB331D6736975964DCEDD61BDD9E5B8B6D9F2E41C
```

Every one of the 115 paths existed at audit time.  Their individual hashes
are recorded in the companion JSON report.

### 2.2 Freeze-checkpoint hashes

Every hash asserted by `qa_freeze_checkpoint_2026-07-26.md` matches the
current file:

| file | asserted and observed SHA-256 |
|---|---|
| `qa_freeze_checkpoint_2026-07-26.md` | `242B9DEA969F89354C448EF49D46EFBA231B543217281FB382DA429EEDCC5104` |
| `kkl_wave_uniform_constant_source_audit.md` | `160106F9B02917FA5B3399C8D528DFEAE98510C150313AF23F295DEEB72D1A0F` |
| `kkl_stationary_typed_paired_wave_realization.md` | `FDF5C152B721D300FE2D590D47416E081B22DFA3E2BC56632131F1BFE15BD025` |
| `kkl_stationary_bl0_uniform_response_closure_audit.md` | `9A03A882B4FE234390DDA2DF74C6F17DA62028763C2AB4B4512F4D609F4E8564` |
| `kkl_wave_local_end_collision_reduction.md` | `323CBD280303B2F6D6B9E3629A5C5EC640B27E497A13C94EA70FF54261FF88EA` |

The last file remains quarantined: it is not evidence for any machine-ledger
node.

### 2.3 Locked sources physically present

The following locally present source artifacts were independently hashed:

| source artifact | bytes | SHA-256 |
|---|---:|---|
| `.tmp_wave_audit/kkl.tar` | 6,822,070 | `7FFDCDC90C0785AE55DE23F0AB64F63178E1F2C661FAB1FCC5C95768D8F53AF8` |
| `.tmp_wave_audit/dl23.tar` | 265,786 | `126CAAD9C5847EBB7918C305752783ECCE1B47541C7903D30D59A65485FB5702` |
| `.tmp_wave_audit/dlneutral.tar` | 2,023,468 | `1D84BFA8216A657CA8E99140BFA3423364BE047BD2051F6C349F552A9C3FBE55` |
| `.tmp_kl06_source.tar` | 109,031 | `3A63FC9773DB8B60ED4A0EB9A1C551E6F66C08E66AB92C36F4E2B482570AB817` |
| `.tmp_kl08_source.tar` | 125,758 | `DA8FCF924793267421F80BE3E17CD7EB2B72CD4F5B08E3F5A38E2161EC608234` |
| `.tmp_wave_audit/waves-with-Misha.tex` | 180,035 | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| `.tmp_wave_audit/value1.tex` | 9,987 | `2767F71E57862DA5CF50FF7B96FC08917E24CA8F9BD2D4523C467B2E896AD83A` |
| `.tmp_wave_audit/not-all-good2.tex` | 43,161 | `B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01` |
| `.tmp_wave_audit/dl23/Feigen.tex` | 176,349 | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| `.tmp_wave_audit/dlneutral/PseudoSiegelBounds.tex` | 490,747 | `4AE3253817EF8EEB76DF95FA411CB9C2B6CB0642C3C4AED4D8AE8305F2122172` |
| `.tmp_kl06_source/appendix.tex` | 7,265 | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |
| `.tmp_kl06_source/wad.tex` | 25,920 | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` |
| `.tmp_kl06_source/psiql2.tex` | 33,579 | `E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228` |

The current arXiv records were checked on 2026-07-26:

| arXiv record | current version |
|---|---|
| `2606.27272` (KKL) | v1 |
| `2512.24171` (Dudko survey) | v1 |
| `2309.02107` (Dudko--Lyubich Feigenbaum) | v3 |
| `2509.23031` (Dudko--Luo--Lyubich) | v2 |
| `2210.09280` (Dudko--Lyubich neutral) | v2 |
| `2205.03157` (BLOT) | v4 |

One bibliographic normalization is advisable: the current title of
`2509.23031v2` is *Uniform a priori bounds for neutral renormalization.
Variation II: \(\psi^\bullet\)-ql Siegel maps*, not the shortened title
currently used in the primary-source table.

## 3. Independent ledger validation

The audit independently validated the schema rather than relying only on
`audit_proof.py`.

### 3.1 Structural results

```text
schema_version:                 2
allowed statuses:              imported, proved, open
unique obligation IDs:         423 / 423
dependency edges:              938
hypothesis edges:               16
clause-map records:             27
missing dependency IDs:          0
missing hypothesis IDs:          0
missing clause-map IDs:           0
duplicate dependency entries:    0
duplicate hypothesis entries:    0
self dependencies/hypotheses:    0
dependency cycles:               0
combined dependency/hypothesis
cycles:                          0
bad or missing evidence paths:   0
bad Markdown evidence anchors:   0
normalized duplicate statements:0
proved/imported nodes with open
proof dependencies:              0
```

All required keys have the expected JSON types, every ID has the canonical
`[A-Z][A-Z0-9_]*` form, and no undeclared item keys occur.

There are twelve proved conditional results carrying sixteen explicit open
`hypotheses`.  Their statements all signal the conditional scope.  No
current target is incorrectly marked proved through one of those
hypotheses.

### 3.2 Generated-ledger determinism

Re-rendering both generated files in memory with
`latex/generate_ledger_tex.py` gives byte-for-byte the checked-in files:

```text
ledger_counts.tex: exact
obligations.tex:   exact
```

This verifies freshness.  It does not cure Finding DS-3 below: the generator
does not render the `hypotheses` field.

## 4. Backward dependency traversals

### 4.1 MLC

The dependency-only closure of `MLC`, including the root, has:

```text
352 nodes = 17 imported + 248 proved + 87 open
```

Its immediate inputs are:

| dependency | status |
|---|---|
| `YOCCOZ` | imported |
| `H1_MARKED_CONSTRUCTION` | open |
| `MBTT` | open |
| `H3_COERCIVITY` | open |
| `H4_RIGIDITY` | open |
| `CONDITIONAL_REDUCTION` | proved conditional |

The nine lowest open leaves of the current dependency graph are:

```text
DIRECT_DECORATION_END_PRIME_END_COFINALITY
H1_CELL_TREE_EXTRACTION
KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR
KKL_NATIVE_WAVE_WANDERERS_QUERY_SCHEMA_BOUNDARY_MAP
KKL_STATIONARY_MARKED_ACCESS_ITINERARY
KKL_STATIONARY_TWO_OCCURRENCE_BINDER
MAPPING_TELESCOPE
VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
VIRTUAL_WAVE_DEMAND_SCHEMA
```

“Lowest” means that none of the node's declared proof dependencies is open;
it does not mean the theorem is easy or source-complete.

### 4.2 UPTCR

The dependency-only closure of `UNIVERSAL_PROTECTED_TOWER_CLOSURE`,
including the root, has:

```text
350 nodes = 16 imported + 247 proved + 87 open
```

Its immediate dependencies are the same four global analytic gates:

```text
H1_MARKED_CONSTRUCTION
MBTT
H3_COERCIVITY
H4_RIGIDITY
```

Every `UPTCR-1` through `UPTCR-6` `maps_to` target is already contained in
the ordinary dependency closure.  Thus the UPTCR clause table does not hide
an additional dependency cycle.

UPTCR is not itself a dependency of `MLC`.  `UPTCR_IMPLIES_MLC` is proved
conditional but has no consumer.  The current MLC graph instead uses
`CONDITIONAL_REDUCTION`.  This is a redundant alternative closure
architecture, not a false status.

### 4.3 VAAPC-I

`VAAPC-I` is a clause of
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`, not a standalone obligation.
It maps to:

| obligation | status |
|---|---|
| `INTERFACE_PROOF_USE_INVENTORY` | proved |
| `VIRTUAL_WAVE_HORIZON_CERTIFICATE` | open |

The union of their dependency closures has:

```text
67 nodes = 4 imported + 48 proved + 15 open
```

The three lowest open leaves are:

```text
DIRECT_DECORATION_END_PRIME_END_COFINALITY
VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION
VIRTUAL_WAVE_DEMAND_SCHEMA
```

Thus `VAAPC-I` remains open exactly as stated in the freeze checkpoint.
The independent `INTERFACE_PROOF_USE_INVENTORY` result is not enough to
close the actual horizon certificate.

### 4.4 Native KKL stationary repair

The ledger's dependency-only closure of
`KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR`, including the root, has:

```text
20 nodes = 1 imported + 10 proved + 9 open
```

The two lowest open leaves are:

```text
KKL_STATIONARY_MARKED_ACCESS_ITINERARY
KKL_STATIONARY_TWO_OCCURRENCE_BINDER
```

The live ledger route is:

```text
KKL_STATIONARY_TWO_OCCURRENCE_BINDER
  -> KKL_STATIONARY_RETAINED_PORTION_REALIZATION
  -> KKL_STATIONARY_SELECTED_CORRIDOR_CONFINEMENT
  -> KKL_STATIONARY_SELECTED_COLLAR_DECK_NONCOLLISION
  -> KKL_STATIONARY_TWO_SIDED_WAVE_NONCOLLISION
  -> KKL_STATIONARY_TWO_PULLBACK_PASS_THROUGH
  -> KKL_STATIONARY_FINAL_PASS_THROUGH_PATH_EXTRACTION
  -> KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR,
```

with `KKL_STATIONARY_MARKED_ACCESS_ITINERARY` entering the selected-corridor
and noncollision stages.  This route also uses the already proved
degree-two correction.

The new access-local/paired-Wave route is not in that closure.  This is the
subject of Finding DS-2.

## 5. Findings

### DS-1 — High: VAAPC clause maps are non-semantic and conceal a cycle

The root statement `VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE` asserts all
five source-facing clauses `VAAPC-I/C/P/H/U`.  Its declared dependencies,
however, contain the mapped targets for only `VAAPC-I` and `VAAPC-P`.

The missing ordinary dependency reachability is:

| clause | mapped obligation | in VAAPC dependency closure? |
|---|---|---|
| `VAAPC-C` | `VIRTUAL_ROOT_CARRIER_SEPARATION` | no |
| `VAAPC-H` | `VIRTUAL_CORRIDOR_PAIR_NATURALITY` | no |
| `VAAPC-U` | `H2_UNIFORM_CORE_WAD_DIMENSION` | no |

The current validator checks only that a `maps_to` ID exists.  It does not
make the map status-bearing or require it to lie in the root's dependency
closure.  Consequently a future edit could mark the VAAPC root proved while
one or more named clauses remained open, and `audit_proof.py` would not
reject it.

Blindly converting all three maps to dependencies is not valid.  The
`VAAPC-H` conversion would expose the cycle

```text
VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE
 -> VIRTUAL_CORRIDOR_PAIR_NATURALITY
 -> VIRTUAL_CANONICAL_INTERFACE_CARRIER
 -> VIRTUAL_PROTECTED_ROUTING_CERTIFICATE
 -> VIRTUAL_COMMON_FREE_COMPONENT
 -> VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE.
```

Required correction before promotion: split the five VAAPC clauses into
first-class obligations, then distinguish the local packet-transport input
needed to construct a common free component from the stronger full
corridor-pair naturality theorem proved downstream.  The cycle must be
broken by theorem content, not hidden in metadata.

Current mathematical consequence: none.  The VAAPC root and VAAPC-I remain
open.

### DS-2 — High: the stationary frontier differs between ledger and narrative

The final section of `dependency_audit.md` displays:

```text
KKL_WAVE_PUSHFORWARD_UNIFORM_PACKET_CONSTANT
 + KKL_STATIONARY_TYPED_PAIRED_WAVE_REALIZATION
 -> KKL_STATIONARY_BL0_UNIFORM_SURVIVOR_RESPONSE
 -> KKL_STATIONARY_SURVIVOR_EXCLUSION_OR_CHARGE
 -> KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR.
```

In the machine ledger,
`KKL_STATIONARY_SURVIVOR_EXCLUSION_OR_CHARGE` has no consumer.  The
stationary repair instead depends on
`KKL_STATIONARY_FINAL_PASS_THROUGH_PATH_EXTRACTION` and the proved
degree-two correction, and its transitive closure follows the
two-occurrence/two-sided-noncollision route described in Section 4.4.

These may be two alternative proof strategies, but the current
documentation calls the paired-response route “the complete backward
chain,” while the ledger treats it as an orphan alternative.  The freeze
checkpoint correctly notes that QA-2 must decide whether pointwise breaking
or family-level response is the minimal native repair.

Required correction before promotion: reconstruct native KKL lines
1534--1623 and choose exactly one of:

1. retain the current pointwise ledger route and label the paired-response
   chain an explicitly non-gating alternative;
2. prove that the response chain is genuinely sufficient and replace the
   stationary dependencies; or
3. record two separate sufficient repair propositions and a disjunctive
   stationary gate.

Do not add both chains conjunctively merely to remove the discrepancy.

Current mathematical consequence: the native repair remains open.

### DS-3 — Medium: generated TeX suppresses formal hypotheses

There are twelve proved conditional nodes with sixteen formal open
`hypotheses`.  `latex/generate_ledger_tex.py` renders statements,
dependencies, clauses, and evidence, but never renders `hypotheses`.
Only incidental prose inside the statement tells a PDF reader that the
result is conditional.

This is not presently a false status: the statements themselves use
language such as “assuming,” “conditional on,” or explicitly formulate an
implication.  It is nevertheless a machine/manuscript traceability defect.

Required correction: render a separate `Hypotheses:` field for every node
and add a regression asserting that every machine hypothesis appears in
the generated appendix.

### DS-4 — Medium: local source custody is incomplete

The primary-source table records ten “local source hashes.”  Five matching
source files are present and match:

```text
KKL waves-with-Misha.tex
KKL value1.tex
KKL not-all-good2.tex
DL23 Feigen.tex
DL22 PseudoSiegelBounds.tex
```

Five recorded digests have no matching file anywhere under
`research/mlc_unified`:

```text
D25 main.tex       FD807D65C44852995182D23A4E96BB42717E8E7502F1D7B71636B16AF5D8A454
DL25 main.tex      ABFCC203BA7DC5F6A8F847AA8755FBCFA9091E8D6CAE520DFC5512FBDB1B8782
BLOT no-bounds.tex ED8F55AE8ADE9667488AD91B4175AB40BFD2E3B7179D8141397F4A17B5B80DF6
CS15 Main.tex      F5A6080081D7000D44985369BEBF72CC1AE9A057182A11F52DEF9E1AF256FC8E
L97 nest.tex       069C10711C36F5358134B418FDF6C5133A5AF16208D2B1C267EA7B4D3A5DF83A
```

The KL05 source archive and `kingdom.tex` hashes recorded later in the
ledger are also absent.  Across all ledger-evidence documents, 46 of 96
embedded SHA-256 values have no matching package file; most of the
additional unmatched values belong to external Push-I/VI/VII/VIII inputs.

This does not show that a recorded theorem is false.  It means the complete
QA-0 source snapshot cannot be reproduced solely from the current package.

Required correction: restore the exact archives/files or add a custody
manifest giving the external immutable location, arXiv version, download
date, archive hash, extracted member path, and member hash.

### DS-5 — Medium: nine open obligations have no consumer

Counting dependency, hypothesis, and clause-map consumers, these open
nodes are unconsumed:

```text
TERMINAL_NONLC_HUBBARD_CARRIER_PROPER
KKL_STATIONARY_MARKED_FIXED_END_PAIR_CERTIFICATE
KKL_STATIONARY_SURVIVOR_EXCLUSION_OR_CHARGE
KKL_STATIONARY_UNIFORM_COLLAR_EXIT_CHARGE
DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION
DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING
ESCAPE_RETURN_KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY
VIRTUAL_SCALE_TO_PUZZLE_SELECTOR
VIRTUAL_ATTACHMENT_FREE_ANCHOR
```

Several are explicitly optional or non-gating, so “unconsumed” does not
mean “wrong.”  The survivor-exclusion node is exceptional because the
latest dependency narrative presents it as gating.  The remaining eight
need a one-word machine classification such as `optional_alternative`,
`diagnostic`, `restricted_subclass`, or `superseded_by`, rather than being
indistinguishable from active blockers.

### DS-6 — Low: duplicated global closure presentation

`MLC` directly depends on the four global open gates and also on the proved
`CONDITIONAL_REDUCTION`, whose formal hypotheses are those same four gates.
Separately, `UPTCR_IMPLIES_MLC` is a proved conditional theorem with no
consumer.  UPTCR itself is not an MLC dependency even though its ordinary
closure nearly coincides with the MLC closure.

This redundancy is logically harmless while all targets remain open, but it
obscures which proposition is the canonical final interface.

Required correction: choose either the direct four-gate MLC presentation or
UPTCR as the canonical public closure interface, and label the other as a
derived alias/alternative theorem.

## 6. Status-surface consistency

The following surfaces agree on the live counts and global status:

```text
README.md
source_ledger.md
dependency_audit.md
manuscript.md
latex/generated/ledger_counts.tex
latex/generated/obligations.tex
output/pdf/README.md
released PDF extracted text
```

They consistently state:

```text
423 total / 28 imported / 291 proved / 104 open
MLC open
UNIVERSAL_PROTECTED_TOWER_CLOSURE open
VAAPC-I open
KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR open
```

Older counts in chronological research sections are identifiable as
checkpoint history, and the latest sections explicitly label the final
423/28/291/104 totals authoritative.  No current status mismatch was found.

Three evidence surfaces (`source_ledger.md`, `dependency_audit.md`, and
`manuscript.md`) were modified a few minutes after the ledger file.  Their
evidence anchors remain valid and their live statuses match the ledger; this
is not by itself stale evidence.  Future releases should nevertheless hash
the ledger and these surfaces in one atomic manifest.

## 7. Promotion freeze and next directives

Until DS-1 and DS-2 are resolved:

1. do not promote VAAPC, VAAPC-I, the KKL stationary repair, UPTCR, or MLC;
2. do not treat `clauses.maps_to` as proof dependencies;
3. do not silently merge the pointwise and family-response stationary
   routes;
4. do not use the quarantined local-end collision note as ledger evidence;
5. do not accept a generated appendix as a complete representation of
   conditional dependencies; and
6. do not call the package fully source-locked until the missing custody
   artifacts are restored or externally pinned.

The immediate mathematical QA task remains the native KKL line-by-line
reconstruction.  Its output must decide the DS-2 fork before any further
stationary construction is allowed to alter the dependency graph.

## 8. Audit commands and reproducibility

The following checks were run from `research/mlc_unified` or its repository
root:

```text
python audit_proof.py
independent JSON key/type/ID/relation validation
dependency-only DFS cycle detection
combined dependency+hypothesis DFS cycle detection
backward closures from the four requested frontiers
evidence-file and Markdown-heading validation
in-memory deterministic LaTeX regeneration
SHA-256 scan of all 3,679 files under research/mlc_unified
status-surface count/status comparison
current primary arXiv record checks
```

The stock proof audit passed:

```text
ledger: valid (423 obligations)
statuses: imported=28, proved=291, open=104
target: MLC [open]
```

This passing result is compatible with DS-1 and DS-2 because the current
validator neither assigns semantics to `maps_to` nor compares prose
dependency diagrams with the machine graph.
