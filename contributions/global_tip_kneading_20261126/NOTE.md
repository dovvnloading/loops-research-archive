---
ledger: NOV26_OPEN_WINDOW
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; Lean development and independent AI review
human_review: none
---

<a id="global-tip-kneading-20261126"></a>

# Global real kneading isolation for the finite primitive-tip family

## Claim

Work in progress. The target is global parameter exclusion for the actual
quadratic critical relations x_(6p)(c) + x_(3p)(c) = 0 and the selected
critical itineraries, for the ten finite periods p = 3,...,12. The archive
currently isolates these roots only inside microscopic seed intervals.
The general exact-cover soundness theorem now compiles locally; the ten
finite kernel certificates and their global geometric assembly are in progress.

## Evidence

The intended proof uses a complete rational interval cover, checked by the
Lean kernel, with soundness over all real parameters. Each rejected cell
must have a proved wrong orbit sign or a proved nonzero collision relation.
Center factors must be removed by an exact polynomial identity, not a
numerical zero tolerance. A retained root interval must have opposite
endpoint signs and a uniformly signed parameter derivative.

First compiled checkpoint: `formalization/weighted/GlobalTipIsolation.lean`.
Its five public theorems establish the exact critical-orbit difference
product, collision deflation, complete itinerary enclosure, exhaustive
closed-cover soundness, and nonvanishing parameter derivative under the
existing root certificate. Every split is sound on all real parameters,
and the deflated branch explicitly proves that the removed third-return
factor is nonzero. Local validation uses the repository's pinned Lean
4.32.0 and Mathlib revision. Full CI validation is still pending.

The proposed ten covers contain 1,806 leaves: 1,301 wrong-sign exclusions,
91 direct nonzero-relation exclusions, 404 deflated exclusions, and ten
retained root intervals. These counts describe the generated data, not a
replacement for its kernel checks. All Lean sources are registered in the
existing project and will receive its transitive dependency audit.

## Dependencies

The existing DepthThreeCert and DepthThreeReal interval engines, the
quadratic critical-orbit recurrence, and Mathlib. The earlier ten-period
verifier supplies root locators only; its numerical output is not a proof
input. Source context: research/tip_family_theorem/AUDIT.md, finding F02,
and research/independent_audits/real_primitive_tip_family_unconditional_20261116/.

## Boundary

NOV26_OPEN_WINDOW remains open during development. A global theorem for a
specified critical itinerary does not automatically identify an entire
maximal primitive component. The exact relation between the formal
itinerary predicates and a physical restrictive window must be stated and
proved separately. The all-period p >= 13 case, geometric copy
identification, KKL marking, widths, H1-H4, and MLC are not established by
the planned finite result. No ledger status change is requested yet.

## Attribution

This builds on the archive's ten-period parameter audit, exact interval
engines, and real collision-root soundness. Proof development and review
are AI-assisted; no independent human review has occurred. CC0 under the
repository's contribution terms.
