---
ledger: KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation and independent AI review
human_review: none
---

# Investigation of full-carrier stationary separation

Ledger statement being addressed:

> For the canonical Q_0-selected chain through H=b+2, prove in the full physical carrier that Q_0 separates alpha^0 from L_0^1 and, for every 1<=n<H, Q_n separates alpha^n from L_0^(n+1). Construct the proof-used collars and marked accesses and prove that competing carrier routes outside the selected inverse sheet do not bypass Q_n. Applying phi_0 inside one sheet is insufficient because a separating path in the full carrier may leave that sheet.

## Claim

**Draft investigation. No new theorem is claimed.** The initial attack examined
noncompact connected bypasses. The deeper archive audit below shows that the
set-level native separator already has a written solution, and that the obvious
external-ray route is already represented in Lean. The current target is therefore
the actual collar, marked-access, and retained-occurrence clause, rather than
another proof of set-level separation.

A result will count here only after a new Lean theorem is registered and passes
the repository's unchanged build and transitive axiom audit. Re-formalizing an
archived lemma, assuming the desired geometric identification, or proving a
classical substitute will not be presented as progress.

## Evidence

Baseline: `main` at `f05f1b9dc8f5fc6eeb68491da2eb44eca6d6cec9`.

The existing `StationaryCompactContact.lean` already proves compact-witness
injectivity and three conditional full-separation routes. It forces a surviving
antipodal connected bypass to accumulate on the deleted critical set (at zero
under the full empty-interior hypothesis). It does not exclude that accumulation.

### Checkpoint 2: rejected routes and the narrower native gap

1. **The external-ray cut already solves the set-level problem.**
   `StationarySeparatorTransport.quadratic_base_separator_of_exterior_ray`
   handles arbitrary connected retained sets, not merely compact witnesses.
   An ambient periodic ray landing at a repelling periodic point of the actual
   little Julia set supplies the closed unbounded cut. The written native proof
   already appears in
   `research/independent_audits/stationary_nonlc_predecessor_lift_20261126/NOTE.md`,
   section 6. Formalizing the classical landing theorem and instantiating this
   existing result would not satisfy this investigation's novelty requirement.

2. **Saturation and canonical connector access are already archived.**
   `research/independent_audits/stationary_fiber_saturation_20261126/NOTE.md`,
   sections 3--5, supplies a written primitive-renormalization saturation
   argument, prime-end correspondence, and connector-contact access data for
   its canonical construction. Its boundary explicitly excludes identification
   with an independently specified KKL Wave collar and all of its occurrences.
   Translating that packet into Lean would be formalization of prior work.

3. **A compact witness cannot be obtained by topology alone.**
   Consider the standard doubled topologist's sine continuum
   
       G = {(x, sin(1/x)) : 0 < x <= 1},
       V = {0} x [-1,1],   K = G union (-G) union V,
       Q = {0} x [-a,a],   0 <= a < 1.
   
   It is compact, full, symmetric, and has empty interior. Both
   `G union (V minus Q)` and `(-G) union (V minus Q)` are connected because
   their added vertical points are limit points of the respective connected
   graphs. Their common vertical tail is nonempty, so `K minus Q` is connected
   and contains antipodal points. A compact connected subset meeting both graph
   halves must contain the whole vertical limit segment, by projection onto
   the first coordinate and compactness. It therefore cannot avoid Q. This is
   a classical-type topological counterexample to the shortcut, not an actual
   polynomial Julia set, a new theorem, or a counterexample to the ledger claim.

4. **Relative critical clearance is not a native substitute.**
   If a proper periodic little filled Julia set Q in an empty-interior ambient
   Julia set contained a nonempty relatively open set, topological exactness
   of the ambient iterate would imply Q equals the ambient Julia set. Thus
   the sufficient relative-neighborhood hypothesis from the compact-contact
   module cannot simply be supplied for a genuine proper renormalization.
   This is a classical exactness consequence, recorded only to reject the route.

The remaining investigation asks for the particular marked collar and accesses
of the actual ambient iterated psi-quadratic-like construction, together with
their retained restriction occurrences through the required selected horizon.
Neither a singleton attachment point nor an abstract prime-end circle map alone
identifies those objects. A theorem that assumes that identification would leave
the same native gate open.

Lean and Lake are not installed in this local environment. Any proof submitted
will therefore require a successful build in the existing repository CI before
it is counted as a theorem. No Lean file has been added at this checkpoint.

## Dependencies

- `KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION` (target, still open).
- `KKL_NATIVE_TERMINAL_HUBBARD_TREE`.
- `KKL_STATIONARY_SELECTED_SMALL_JULIA_PREDECESSOR_CHAIN`.
- `KKL_STATIONARY_SELECTED_ALPHA_PREDECESSOR_CHAIN`.
- `KKL_STATIONARY_TERMINAL_CRITICAL_LIMB_INVERSE_SHEETS`.
- Earlier work: `contributions/stationary_compact_contact_separator_20261126/NOTE.md`,
  `contributions/stationary_separator_no_bypass_20261126/NOTE.md`, and
  `contributions/stationary_multi_interface_separator_20261126/NOTE.md`.

## Boundary

No obligation is closed and no mathematical advance is claimed at this
checkpoint. In particular the classical doubled-sine diagnostic is not offered
as a qualifying result. The native collar, marked-access, and full-horizon
occurrence clauses remain open. No status-record change is proposed. The draft
will be closed if the investigation produces no qualifying result.

## Attribution

The source problem belongs to the Kahn-Kapiamba-Lyubich program and the archive's
stationary separator analyses. The prior Lean modules are dependencies and prior
work, not discoveries of this investigation. No worldwide priority claim is made.
