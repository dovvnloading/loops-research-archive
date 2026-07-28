# Contributing to the marked-width research program

Contributions are welcome when they sharpen a theorem, close an explicit obligation, produce a counterexample, correct a source dependency, improve reproducibility, or make the mathematical architecture easier to verify.

Begin with the [research map](./RESEARCH_MAP.md), then locate the relevant statement in the manuscript or companion paper and its identifier in [`ledger.json`](./ledger.json). A useful contribution names the exact interface it changes.

## Contribution tracks

### Proof or proof repair

Submit a complete argument for a stated lemma, theorem, or open gate. Include:

- the exact statement and ledger ID;
- all hypotheses, including regularity, degree, marking, access, and compactness assumptions;
- every imported result used, with a theorem-level citation;
- the dependency changes implied by the proof;
- any statement elsewhere in the archive that must be narrowed, strengthened, or reclassified.

A proof that closes only a conditional subcase should state that subcase precisely. Do not promote a finite or one-scale theorem to a global conclusion without the transition theorem that justifies the promotion.

### Counterexample or obstruction

A counterexample should identify the smallest claim it defeats and verify each advertised hypothesis. Include:

- the target statement or ledger ID;
- the construction and parameter range;
- a hypothesis-by-hypothesis checklist;
- the exact failed conclusion;
- whether the failure is topological, analytic, combinatorial, quantitative, or logical;
- the strongest corrected formulation that survives, if known.

Finite matrix examples, planar models, and symbolic countermodels are valuable when their relation to the dynamical claim is explicit.

### Source or attribution audit

A source correction should give:

- the archive statement using the result;
- the original source, stable link, theorem/proposition number, and page when available;
- the source’s exact hypotheses and conclusion;
- the mismatch, omission, orientation error, or attribution issue;
- a proposed replacement citation or corrected use.

Secondary expositions may help orientation, but imported theorem status should terminate in a primary source whenever possible.

### Computational or numerical contribution

Computations are accepted as reproducible diagnostics. Supply:

- code and a minimal invocation;
- environment and dependency versions;
- deterministic seeds or a documented sampling procedure;
- machine-readable output;
- tolerances, precision, stopping rules, and failure modes;
- the claim being tested;
- a clear statement that the result is evidence, falsification, or illustration—not proof—unless accompanied by a rigorous argument.

Generated figures should include the data or program needed to reproduce them and a caption stating their mathematical role.

### Exposition, notation, or archive navigation

Expository contributions should reduce ambiguity without changing mathematical status. Name the affected definition or section, preserve source attribution, and state whether the change is purely editorial or alters the formal content.

## Submission standard

A research issue or pull request should contain:

1. **Target** — paper, theorem, section, or ledger ID.
2. **Current status** — imported, proved, conditional, or open.
3. **Claim** — one precise sentence describing the proposed change.
4. **Evidence** — proof, counterexample, source passage, computation, or reproducible artifact.
5. **Dependencies** — entries consumed or changed.
6. **Boundary** — what the contribution does not establish.
7. **Attribution** — authors and sources that must be credited.
8. **AI disclosure** — systems materially used and the human verification performed.

Use displayed equations for substantive identities and define notation locally. Distinguish an implication from its antecedent: proving “UPTCR implies MLC” does not prove UPTCR.

## Status discipline

The public ledger uses four logical roles:

| Role | Meaning |
|---|---|
| **Imported** | A theorem taken from cited literature, with hypotheses checked against the use |
| **Proved** | A complete internal proof is present and its declared dependencies terminate correctly |
| **Conditional** | The conclusion is proved from assumptions that remain unestablished in the program |
| **Open** | No complete proof is claimed |

A contribution may change status only when it supplies the missing argument and all dependencies have been audited. Numerical agreement, repeated model agreement, or the absence of a discovered counterexample does not change a theorem’s status.

## Paper-specific safeguards

### Paper 1

Do not replace the immersion language by embedding language. Any finite encoding of the localization state must address the infinite coset-valued sheet fiber or prove a future-faithful quotient preserving every observable later consumed.

### Paper 2

Preserve the one-scale boundary. Identifying the component quotient does not identify end fibers with small Julia sets, provide a self-return on an end fiber, or establish cross-scale compatibility.

### Paper 3

Paper 3 Draft II is the current QA-audited research preprint. Proposals should cite the draft label and exact statement being reviewed. Separate its finite planar carrier criteria from the unrealized virtual-dynamical application.

### Main reduction

Claims affecting H1–H4, UPTCR, VAAPC-I, or MLC require a dependency-level audit. A result that closes a stationary, finite, bounded-type, or single-scale case must retain that qualifier.

## Reproducibility and file placement

Place contributions with the object they support:

- paper source or theorem packets under the relevant `papers/paper*/` directory;
- consolidated proof research under `research/mlc_unified/`;
- executable diagnostics under `code/`;
- machine-readable outputs under `results/`;
- figures and their generation records under `figs/` or the relevant research figure directory.

Do not commit credentials, private correspondence, personal data, editor state, caches, generated dependency trees, or machine-specific absolute paths.

## AI-assisted research

AI assistance is permitted and should be disclosed when material. Name the system and its role—for example proof search, counterexample generation, code generation, source comparison, or editing—and describe the human verification performed. AI output is not a source citation and does not independently establish a proof.

## Scholarly conduct

- Credit original authors for imported mathematics.
- Quote sparingly and link to the primary source.
- State uncertainty and negative results directly.
- Preserve counterexamples and failed routes when they constrain future formulations.
- Do not imply affiliation, collaboration, or endorsement without explicit authorization.
- Keep discussion focused on claims, evidence, and reproducibility.

## Licensing

By contributing original material, you agree that it may be released under [CC0 1.0 Universal](./LICENSE). You must have the right to submit the material. Third-party content remains under its original terms and must be clearly identified and cited.
