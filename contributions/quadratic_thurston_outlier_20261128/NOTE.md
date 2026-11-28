---
ledger: UNIVERSAL_PROTECTED_TOWER_CLOSURE
result: evidence
ai: OpenAI ChatGPT GPT-6 Astra Pro
human_review: none
---

# Independent quadratic investigation: no qualifying theorem obtained

**Outcome: unsuccessful research attempt.** This packet is retained on the
closed draft PR as an investigation record. It is not submitted as a theorem,
a closure, or a qualifying partial result. In particular, it contains no new
Lean theorem and provides no Lean-CI proof evidence.

## Claim

No new mathematical claim is made. The investigation identified the archive's
precise open hypothesis and rejected several candidate results because they
were classical consequences, duplicates, outside the requested scope, or
unproved.

The front-matter value `evidence` describes the exploratory computation
preserved with this packet. It does not promote that computation to a proof
about complex quadratic parameters or to a result satisfying the user's mandate.

### The exact remaining hypothesis

The archive's terminal written reduction is `UPTCR_IMPLIES_MLC`. Its explicit
open premise is **`UNIVERSAL_PROTECTED_TOWER_CLOSURE`**, the Universal
Protected-Tower Compactness and Rigidity Proposition (UPTCR).

It requires universal constants chosen before the polynomial and tower,
independent of periods, rotations, transition depths, horizons, markings,
counters, and orders of regimes. Every infinitely renormalizable quadratic
must admit the same complete six-clause package:

1. Canonical actual protected carriers.
2. Exact analytic realization.
3. A uniformly finite, source-faithful response state.
4. A universal backward transition with the required error control.
5. Coercive marked compactness.
6. Tower rigidity, a singleton parameter fiber, and connected relative
   parameter neighborhoods.

The current construction already stops at Clause 1. Later compactness and
rigidity conclusions are also open hypotheses. The earlier
`CONDITIONAL_REDUCTION` assumes `H1_MARKED_CONSTRUCTION`, `MBTT`,
`H3_COERCIVITY`, and `H4_RIGIDITY`.

**Formalization distinction:** `ResearchLedger.lean` checks the dependency
record, and `ResearchGates.lean` proves implications for an abstract interface
with separately assumed terminal and complementary bridges. These are not a
Lean formalization of the full analytic quadratic implication.

## Evidence

Starting main commit: `f05f1b9dc8f5fc6eeb68491da2eb44eca6d6cec9`.

The draft was opened before theorem selection and formalization, and the
investigation was committed incrementally to PR #269:
https://github.com/dovvnloading/loops-research-archive/pull/269

Archive status pointers:

- `ledger.json`: `UPTCR_IMPLIES_MLC` and
  `UNIVERSAL_PROTECTED_TOWER_CLOSURE`.
- `research/mlc_unified/manuscript.md`: Proposition D and Theorem E.
- `research/mlc_unified/mlc_closure_proposition.md`: Sections 5--7.
- `ResearchGates.lean`: the header and `conditional_local_connectivity`.

### Candidate selection and rejection

`CANDIDATES.md` records the screen performed before any formalization.
The trace-recovery, characteristic-polynomial, critical-derivative, and
qualitative contraction proposals were rejected as classical. The archive
already formalizes center transversality and critical-coordinate results.
Angled internal addresses distinguish combinatorial classes; that does not
separate different parameters within one class.

The most concrete unproved candidate left by the screen was:

> For every k >= 2 and every complex parameter c for which 0 has exact
> period 2^k under z -> z^2+c, the Thurston cotangent operator on the sphere
> marked by the postcritical set has simple spectrum.

No proof of this statement was found. Buff--Epstein--Koch's Question 6 asks
for simplicity for all periodic unicritical polynomials, so their coefficient
formula does not prove this candidate. Finite characteristic-two tests do not
prove it either. It was therefore not formalized or submitted.

A broader approach asserting squarefree reduction of the normalized spectral
polynomial at every exact period was undermined by an exploratory period-nine
calculation. That calculation is a finite-field experiment, not a theorem
about repeated complex eigenvalues. Even a certified version would be a finite
arithmetic obstruction to one method, not the requested new fiber theorem.
Its reproduction is preserved solely to explain why the route was dropped.

### Lean and validation status

No Lean file was added, no new theorem was registered, and no new mathematical
claim passed a Lean build. Documentation/intake CI passing is not evidence of
a Lean proof.

The local toolchain was absent. Installing the official Lean archive exceeded
the workspace's approximately 400 MB available disk; the incomplete download
was removed. Existing repository CI remained a possible compiler. This
environment limitation was not the reason no theorem was delivered: no
candidate first survived both the novelty test and a complete mathematical proof.

## Dependencies

This investigation assumes no open ledger row as a proved theorem. The target
row is a research obligation, not an assumption used to manufacture a result.

The primary-source comparisons are listed in `CANDIDATES.md`. They include
Buff--Epstein--Koch on the Thurston operator, DeMarco--Koch--McMullen on
Teichmueller contraction, and Schleicher on internal addresses.

## Boundary

- No new criterion, obstruction, or reduction satisfying the user mandate
  was obtained.
- No Lean theorem is claimed; the required formal validation was not completed.
- No parameter fiber was shown to be a singleton.
- No result on infinitely renormalizable quadratics, UPTCR, H1--H4, or MLC
  was proved.
- No ledger status, existing theorem, or workflow was changed.
- Spectral simplicity, its relevance to contraction degeneration, and any
  bridge from that information to parameter-fiber rigidity remain unproved.

The repository's `AGENTS.md` explicitly directs an agent to close a draft
when no real qualifying progress was obtained, rather than submit a
restatement, survey, or plan. The PR is closed on that basis, preserving its
commits and releasing its claim on the obligation.

## Attribution

The reduction and obligation names belong to the existing archive.
The classical mathematical ingredients belong to the authors cited in the
candidate screen. This unsuccessful investigation and its exploratory code
are AI generated. No human specialist reviewed correctness or originality.
