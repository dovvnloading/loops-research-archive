---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="critical-crossing-deck-20261127"></a>

# All critical-crossing lifts and intrinsic phase words of an actual selected return

## Claim

For the actual one-critical selected quadratic return already constructed in the archive, every continuous target path has a continuous physical lift with any prescribed starting inverse point, even when critical encounters accumulate. Its entire space of continuous lifts is in bijection with independent Boolean choices on the actual connected components of the regular-time set. Every such return also contains closed target paths with arbitrarily many distinct closed source lifts sharing one regular basepoint: for every N, an injective family indexed by N-bit words lies over one common complete target loop.

These are compiled Lean theorems with a successful exhaustive transitive axiom audit. This is a partial result on MAPPING_TELESCOPE. It does not construct all native virtual stage cycles or establish the admissibility of the witness paths as native routes.

## Evidence

### 1. Exact physical objects and inherited hypotheses

Write f_c(z)=z^2+c and let

    p = f_c^a,     q(z) = z^2+c,     r = f_c^b,
    R = r o q o p = f_c^(a+1+b),     v = f_c^b(c).

For the classification and witnesses, A is an open physical source, D contains c,

    B = connectedComponentIn(q^(-1)(D), 0),
    p(A) = B,

p is injective on A, and r is injective on D. These are precisely the actual factorization hypotheses of the existing TelescopeDeckInvolution theorem. That theorem is imported: the intrinsic analytic involution tau is not reconstructed or assumed as an abstract two-sheet model. Its identities are p(tau(z))=-p(z), tau^2=id, and

    R(w)=R(z)  iff  w=z or w=tau(z)       for z,w in A.

The new quadratic_return_critical_value_iff identifies R(z)=v exactly with p(z)=0. Thus the collision set of a reference path and its deck mate is exactly the target path's critical-time set.

The unrestricted existence and all-path classification use the same stronger saturated-return hypotheses as TelescopePathPairing: V is open and preconnected, v belongs to V, D is the component of r^(-1)(V) containing c, B is the critical component above D, A is the component of p^(-1)(B) containing a point x with p(x)=0, and the prefix and suffix are injective on A and D. Properness, complete return fibers, and the analytic prefix/suffix inverses are reused from the archived theorems.

### 2. Existence through arbitrary critical encounters

TelescopeCriticalLift.lean proves quadratic_return_path_lift_with_critical_crossings. Given any continuous gamma:[0,1]->V and any z in A with R(z)=gamma(0), it constructs a continuous Gamma:[0,1]->A with

    R(Gamma(t)) = gamma(t),     Gamma(0)=z.

No avoidance, finite-crossing, isolated-zero, or locally finite partition hypothesis is present.

The construction first pulls gamma through the analytic suffix inverse. A square root of the resulting path minus c is chosen separately on each actual connected component of the nonzero-time set. The nonzero root theorem is imported from Mathlib, not reproved. At every zero, including every accumulation point of excursions, the exact identity

    norm(root(t)) = sqrt(norm(path(t)))

forces continuity. Extending the interval path to the real line by the standard interval retraction makes its regular components open intervals. The chosen initial root determines the required initial prefix value. Connectedness of the whole lifted interval and its initial membership retain the entire middle path in the actual critical component B. The analytic prefix inverse then places the entire physical path in A.

### 3. Intrinsic complete classification

For a target path gamma, let

    Z_gamma = {t | gamma(t)=v},     E_gamma = [0,1] minus Z_gamma.

A PhaseCut is a subset S of E_gamma for which both S and E_gamma minus S are open in the original time space. Given a reference lift Gamma_0, select tau(Gamma_0(t)) on S and Gamma_0(t) off S.

CriticalPhaseCuts proves that this selection is continuous exactly for the extracted phase cuts, including arbitrary accumulation of critical times. The proof places the frontier of S in the collision set and uses continuous pasting there. Conversely, for any continuous selection, its two regular phase loci are open inequality sets. Extraction and reconstruction are inverse operations, so no third kind of lift or hidden switching rule is omitted.

TelescopeCriticalPhase applies that equivalence to the actual return fibers. TelescopeCriticalPaths first constructs the reference lift, so its final target-path theorem does not assume a lift exists.

CriticalPhaseExcursions defines the inventory using the actual nonempty sets connectedComponentIn(E_gamma,t), with no caller-supplied partition. Openness and connectedness in the original interval topology imply

    {all continuous physical lifts of gamma}
      is equivalent to
    {functions from actual regular excursions to Bool}.

This is an equivalence of full timed paths, not a pointwise fiber count and not a quotient by homotopy or reparameterization. For a finite inventory of N excursions, the total number of lifts is exactly 2^N. The total census is unbased: it counts all starting inverse points. The separate anchored phase census proves that prescribing one regular excursion's phase removes exactly one Boolean choice. The existence theorem can prescribe a starting inverse even when the initial target value is critical.

### 4. A realized closed-loop witness in every actual source

TelescopeCriticalPhaseWitness constructs the paths inside A. It obtains the actual critical source x from p(A)=B and chooses a ball of radius epsilon about x contained in A. With delta=epsilon/2, put

    Gamma_0(t) = x + delta (t-1/3)(t-2/3),
    gamma(t) = R(Gamma_0(t)).

Both real factors have absolute value at most one on the unit interval, so the whole source path lies in that ball. Prefix injectivity proves that gamma meets v exactly at t=1/3 and t=2/3.

The second lift equals tau(Gamma_0) on the middle third and Gamma_0 on the two outer thirds. The involution fixes the source point at both crossing times, so the new classification proves continuity. The two lifts differ at t=1/2. Their endpoint values agree, and Gamma_0(0)=Gamma_0(1), so both are closed lifts of the same closed target loop with the same regular basepoint. They even agree on entire initial and final intervals.

Consequently both endpoint marks, regularity of the basepoint, and closedness of the target loop do not determine the interior critical-crossing lift.

### 5. Arbitrarily many realized phase words at fixed return degree

CriticalPhaseWords proves that the standard timed path concatenation retains both constituent paths: equality of two concatenations implies equality of both halves. It then constructs an injective family of concatenated loops from any two distinct based loops with one common complete projection.

TelescopeCriticalPhaseMemory instantiates this construction with the physical witness. Its theorem quadratic_return_unbounded_closed_phase_memory provides one regular physical point z in A such that, for every N, there is one closed target loop gamma_N and an injective map

    (Fin N -> Bool) -> {closed physical paths based at z}

whose whole paths remain in A and all project to gamma_N under the same actual R. This proves at least 2^N distinct full lifts with both endpoint marks fixed; it is not a claim that this lower bound is the exact total for gamma_N.

The return map, its degree, and the source basepoint are fixed while N varies. The target path varies with N, and all timed critical occurrences are retained.

### 6. Verification

The complete weighted Lean build and exhaustive transitive axiom audit passed on source revision [76dc11c24c3232eab61b39401a9ae00be4691c6d](https://github.com/dovvnloading/loops-research-archive/commit/76dc11c24c3232eab61b39401a9ae00be4691c6d). The authoritative evidence is [weighted CI run 45959876131, job 140375006317](https://github.com/dovvnloading/loops-research-archive/actions/runs/45959876131/job/140375006317).

All nine new modules compiled: CriticalPhaseCuts, CriticalPhaseCensus, CriticalPhaseExcursions, CriticalPhaseWords, TelescopeCriticalLift, TelescopeCriticalPhase, TelescopeCriticalPaths, TelescopeCriticalPhaseWitness, and TelescopeCriticalPhaseMemory. The audit reports allowed axioms only for every declaration in each of them. Its whole-package summary is:

    Build completed successfully (9066 jobs).
    AXIOM_AUDIT_PASS weighted: 195 modules, 4434 declarations

The existing coverage verifier enumerates declarations by their actual Lean module provenance and applies Lean.collectAxioms to every declaration, including definitions and generated declarations. The only permitted foundational axioms are propext, Classical.choice, and Quot.sound. The source trust-escape scan also passed. No sorry, admit, new axiom, native_decide, or other proof trust escape is used.

Contribution intake, source registration, and the repository's other completed checks passed on this proof revision. All modules are registered in the weighted Lake package, the theorem index, and the source inventory. Validation used the existing repository CI and pinned toolchain; no workflow or ledger status file was changed. Subsequent verification-note updates do not change these proof sources.

Reproduction:

    cd formalization/weighted
    lake build CriticalPhaseCuts CriticalPhaseCensus CriticalPhaseExcursions
    lake build TelescopeCriticalLift TelescopeCriticalPhase TelescopeCriticalPaths
    lake build CriticalPhaseWords TelescopeCriticalPhaseWitness TelescopeCriticalPhaseMemory

Then, from the repository root:

    python3 -B code/verify_lean_coverage.py --audit weighted
    python3 -B code/contribute.py check

## Dependencies

Ledger target: MAPPING_TELESCOPE. Its existing prerequisites are PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER, RELATIVE_COVER_LIFT, and STAGE_FORWARD_CLOSURE.

Existing Lean inputs: TelescopeDeckInvolution, TelescopeConformalInverse, TelescopeCollarRecognition, TelescopeUnbranchedCover, and their imported actual quadratic component and saturation results. The prior regular-path boundary is documented in contributions/analytic_deck_rigidity_20261126/NOTE.md and TelescopePathPairing.lean.

Mathlib inputs include Complex.exists_continuousOn_pow_eq, convex contractibility, connected-component topology, continuous pasting, interval retraction, finite cardinality, and the exact timed Path.trans/map operations. The repository pins Lean and Mathlib at v4.32.0; the package manifest pins Mathlib commit 81a5d257c8e410db227a6665ed08f64fea08e997.

## Boundary

Keep MAPPING_TELESCOPE open. The work removes the critical-value-avoidance condition from continuous path lifting for an already constructed actual selected return, classifies its entire lift space, and realizes endpoint ambiguity and finite phase words there.

It does not construct compatible embedded Jordan cores for every native virtual stage cycle, prove native full component/deck-phase alignment, or identify the witness paths with proof-used relative-cover routes. The precise missing package in [the critical chronology, Sections 10.1-10.2 and 15.3](../../research/mlc_unified/critical_chronology_and_retimed_telescope.md) consists of selected relative-cover lifts embedded on closed Jordan cores, compact containment in the authorized stage localizations, compatible basepoints and deck phases throughout the cycle, and containment of every postquadratic propagated critical value in its selected core. The new theorems start with the selected return already supplied; using them to construct those inputs would be circular. In particular, unrestricted continuous critical-crossing paths must not silently replace native admissible routes. The constructed target loops may backtrack and are not asserted simple or immersed.

Distinct timed paths are not asserted to represent distinct homotopy classes, different transverse width, different Value observables, or different future continuation behavior. The phase-word theorem therefore does not refute a finite future-equivalence summary or establish a native uniform-memory obstruction. It gives the precise failure of determining the complete critical-crossing lift from endpoint marks alone.

No uniform geometric bounds, collar moduli, Wave estimates, any H1-H4 obligation, UPTCR, or MLC are proved. No worldwide originality or priority claim is made. No human review has occurred.

## Attribution

Builds on the archive's actual one-critical return, analytic deck, and regular-path developments, and on the Kahn localization/telescope program credited there. Standard continuous-root and topology facts are imported from Mathlib. The contribution is the all-critical-times assembly and intrinsic phase accounting in this actual-return interface, together with the explicit physical closed-loop and arbitrarily long phase-word constructions. OpenAI ChatGPT, GPT-6 Astra Pro performed proof development, integration, and CI-driven revision.
