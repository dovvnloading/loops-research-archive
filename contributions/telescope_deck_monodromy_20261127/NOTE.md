---
ledger: MAPPING_TELESCOPE
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; collaborative proof development, adversarial review, and verification
human_review: none
---

<a id="telescope-deck-monodromy-20261127"></a>

# Exact critical-path lift and geometric-trace census for actual quadratic returns

## Claim

For the actual selected one-critical quadratic return already constructed in the archive, this contribution proves an exact continuation-history theorem. For every natural number n, there is one continuous target path with exactly 2^n continuous lifts in the complete physical source and exactly 2^n different geometric source traces. These are counts of all lifts and all realized range sets, with no prior finiteness or source endpoint assumption.

The same physical return also has explicit regular loops whose every lift closes for even turn count and ends at its distinct deck mate for odd turn count. Consequently its entire regular target admits no continuous global section into the selected source.

These are new formal interfaces beyond the archive's existing regular-path pairing theorem. They are partial progress for `MAPPING_TELESCOPE`; the native relative-cover and Jordan-core existence clauses are not proved.

### Actual objects and hypotheses

Write

\[
f_c(z)=z^2+c,\qquad F_c^k=f_c^k,\qquad R=F_c^{a+1+b},\qquad v_*=F_c^b(c).
\]

The Lean iterate is exactly `QuadraticEscape.orbit`, not a replacement dynamical model. Fix natural times a,b, a complex parameter c, an open preconnected target V containing v_*, and an anchor x with F_c^a(x)=0. The selected physical domains are

\[
D=\operatorname{Comp}_{c}((F_c^b)^{-1}(V)),\quad
B=\operatorname{Comp}_{0}(f_c^{-1}(D)),\quad
A=\operatorname{Comp}_{x}((F_c^a)^{-1}(B)).
\]

Assume F_c^a is injective on A and F_c^b is injective on D. These are the same actual-component hypotheses used by the existing telescope path-pairing theorem. No covering, inverse branch, deck involution, target loop, path lift, or path-space finiteness is supplied as an extra premise. The times a and b may be zero.

`quadratic_return_critical_trace_card_exact` constructs a continuous path gamma with image in V and both endpoints v_* and proves

\[
\#\{L:[0,1]\to A\text{ continuous}:R\circ L=\gamma\}=2^n
\]

and, separately,

\[
\#\{\operatorname{range}(L):L:[0,1]\to A\text{ continuous},\ R\circ L=\gamma\}=2^n.
\]

The second equality counts actual subsets of the complex plane. It rules out an explanation based only on different parametrizations of the same source image. `quadratic_return_unbounded_critical_trace_count` then defeats every proposed finite upper bound on this trace count, even with c,a,b,A,B,D,V fixed, if arbitrary continuous target paths visiting the branch value are permitted.

## Evidence

### 1. Reused foundation and the precise new boundary

The existing modules `TelescopeConformalInverse`, `TelescopeDeckInvolution`, `TelescopeUnbranchedCover`, and `TelescopePathPairing` already construct the analytic prefix inverse, the physical deck involution, the regular two-sheet covering, and exactly two lifts for every path avoiding v_*.

The earlier packet [analytic deck rigidity](../analytic_deck_rigidity_20261126/NOTE.md), in its Boundary section, explicitly leaves loop endpoint permutation and continuation through the branch value unproved. This packet addresses those two boundaries after the physical return has been constructed. It does not discharge a native existence or compatibility clause of the ledger obligation, and it does not count the reused regular two-lift theorem, properness, or degree-two construction as new results.

### 2. One physical critical excursion has exactly two lifts

Choose r>0 small enough that the closed radius-r disk about zero lies in the actual open central component B. The already verified analytic prefix inverse g:B->A satisfies F_c^a(g(w))=w and g(0)=x.

Use the central bump

\[
e(t)=4rt(1-t).
\]

Its two physical source paths are g(e(t)) and g(-e(t)); both start and end at x. Their common target path is

\[
\gamma(t)=F_c^b(e(t)^2+c).
\]

It lies in V, and suffix injectivity proves that it equals v_* only at t=0 or t=1. For any other lift L in A, suffix injectivity gives

\[
(F_c^a(L(t)))^2=e(t)^2.
\]

On the connected open interval (0,1), the quotient F_c^a(L(t))/e(t) is continuous and belongs to {1,-1}. It is constant. Prefix injectivity therefore identifies L with one of the two displayed paths, and the endpoint conditions extend this equality to the whole interval. The nonzero midpoint distinguishes the paths.

This is `quadratic_return_critical_excursion`. The single critical fiber is derived from the actual prefix, quadratic step, and suffix; it is not assumed to be singleton in the physical theorem.

### 3. Exact path census across critical joints

`PathExcursionCensus` proves the general finite concatenation interface. When a target joint has a singleton source fiber, splitting an arbitrary complete lift at that joint forces both halves to meet the common source point. Exhaustive classification of each single excursion then recursively recovers its entire Boolean choice word.

Conversely, every word concatenates to a continuous lift of the same complete target path. The proof constructs a bijection with `Fin n -> Bool`; it does not assume the path space finite and then apply a bound. `continuous_binary_lift_card_exact` also derives both source endpoints from the singleton fiber, rather than prescribing them in the counted type.

`quadratic_return_critical_lift_card_exact` supplies all these hypotheses for the actual physical bump excursions. This first count distinguishes parametrized histories. The next two steps strengthen it to geometric traces.

### 4. Markers recover choices from the full geometric trace

For i in Fin n, use distinct central markers and excursions

\[
z_i=\frac{r}{n+1}(1+i\,\mathrm{i}),\qquad e_i(t)=4t(1-t)z_i.
\]

Here the index i in the real coefficient is its natural-number value, and the final imaginary unit is \(\mathrm{i}=\sqrt{-1}\). All excursions and their negatives remain in the same radius-r central disk, independently of n.

`CriticalRayGeometry` proves exact incidence:

\[
z_j\in\operatorname{range}(e_i)\iff i=j,\qquad
z_j\notin\operatorname{range}(-e_i).
\]

The real coordinate forces the bump amplitude to be one in the first equality; the imaginary coordinate then forces the indices equal. The positive real coordinate excludes every negative ray.

Transport by g preserves this incidence. The physical marker g(z_j) belongs to the full source trace exactly when the word chooses the positive excursion at position j. Thus every choice is recoverable from the whole unparametrized range set, even after all excursions have been concatenated.

### 5. Exhaustion of all physical lifts and all range sets

`PathChoiceTraceCensus` extends the exact splitting argument to a different pair of excursions at each position. Its `continuous_choice_lift_card_exact` counts all continuous lifts; `all_trace_card_exact` counts all source range sets realized by any such lift.

`TelescopeCriticalTraceCensus` constructs the physical positive and negative paths g(e_i(t)) and g(-e_i(t)), proves their common target image, verifies the singleton critical fiber, and repeats the continuous-square-root classification for each individual ray. It then applies the two exhaustive count theorems. All domains, maps, and marker points are actual subsets, points, and iterates in the complex plane.

The concatenation uses fixed half-time joints and ends with a constant interval at the critical value. That final dwell adds no choice because its source fiber is singleton. Therefore n counts nonconstant excursions, not isolated critical-time points. At n=0, both counted spaces have one element: the constant critical lift and its singleton trace.

### 6. Explicit regular-loop phase and no global section

`TelescopeLoopMonodromy` uses one radius and one constructed physical involution tau for every natural turn count m. The central path is

\[
w_m(t)=r\exp(m\pi\mathrm{i}t),
\]

and the target loop is the actual suffix image of w_m(t)^2+c. Its displayed lift is g(w_m(t)). The existing regular-path uniqueness theorem proves that every physical lift has the same endpoint phase:

\[
\Gamma(1)=\Gamma(0)\quad(m=2k),\qquad
\Gamma(1)=\tau(\Gamma(0))\ne\Gamma(0)\quad(m=2k+1).
\]

A continuous global section on V minus {v_*} would turn the one-turn target loop into a closed lift, contradicting the odd-turn theorem. This is `quadratic_return_no_regular_section`.

These are phase computations for the explicit constructed loop family. No general winding-number classification of arbitrary loops, homotopy-invariance theorem, or deformation theorem is claimed.

### 7. Source map and verification

| Module | Role |
|---|---|
| [PathExcursionCensus](../../formalization/weighted/PathExcursionCensus.lean) | Exact complete-path census for repeated excursions |
| [PathChoiceTraceCensus](../../formalization/weighted/PathChoiceTraceCensus.lean) | Variable excursions, recoverable markers, exhaustive lift and geometric-trace counts |
| [CriticalRayGeometry](../../formalization/weighted/CriticalRayGeometry.lean) | Exact signed-ray geometry and marker separation |
| [TelescopeCriticalExcursions](../../formalization/weighted/TelescopeCriticalExcursions.lean) | Actual one-excursion classification and repeated physical lift census |
| [TelescopeCriticalTraceCensus](../../formalization/weighted/TelescopeCriticalTraceCensus.lean) | Exact counts of all actual lifts and all actual traces; unbounded trace count |
| [TelescopeLoopMonodromy](../../formalization/weighted/TelescopeLoopMonodromy.lean) | Physical regular-loop phase and absence of a global section |

There are 41 public theorems in these six modules. Every original module has compiled locally in the pinned Lean 4.32.0 project. Registration and proof-escape scans pass. A local `#print axioms` audit of all 41 public theorems found only `propext`, `Classical.choice`, and `Quot.sound`, with no additional axioms.

Reproduction with the repository toolchain:

```sh
cd formalization/weighted
lake exe cache get
lake build
cd ../..
python -B code/verify_lean_coverage.py --audit weighted
python code/contribute.py check
```

The existing weighted CI additionally builds the complete weighted project and audits every compiled declaration's transitive axioms. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

Verified proof checkpoint: [`b3906ab34f5a4047aa7c248c9522877b1e789e0b`](https://github.com/dovvnloading/loops-research-archive/commit/b3906ab34f5a4047aa7c248c9522877b1e789e0b).

- [Weighted Lean CI](https://github.com/dovvnloading/loops-research-archive/actions/runs/45977335795) passed the full build (9,082 build jobs) and the transitive axiom audit of all 203 weighted modules and 4,660 declarations. Each of the six new modules appears separately in the successful audit, including its private and generated declarations.
- [Research validation](https://github.com/dovvnloading/loops-research-archive/actions/runs/45977335826) passed, including the root and standalone Lean checks, audit-fixture regression, ledger consistency, physical-bridge checks, and rejection of transitive promotion from unresolved premises.
- [Contribution intake](https://github.com/dovvnloading/loops-research-archive/actions/runs/45977354715) passed. The local `python code/contribute.py check` also passed.

The source scan registered all 252 Lean files in the repository and found no prohibited proof-escape tokens. No `sorry`, `admit`, new axiom, or compiler-trust bypass is used by this contribution. The verification-only follow-up commit changes this note; the verified Lean sources and registrations remain identical to the proof checkpoint.

The initial candidate checkpoint `631ea4b` deliberately remained a draft. Its weighted CI rejected elaboration errors in the then-unverified physical modules. Those errors have been corrected and the corrected original files now compile locally. No result is certified on the basis of that failed run.

## Dependencies

- Ledger target: `MAPPING_TELESCOPE`. Its existing prerequisites are `PLANAR_CRITICAL_SPINE_TELESCOPE_COMPILER`, `RELATIVE_COVER_LIFT`, and `STAGE_FORWARD_CLOSURE`; this packet does not change their statements or status.
- Actual-object Lean inputs: `QuadraticEscape.orbit`, `SaturatedTelescope`, `TelescopeRamification`, `TelescopeCollarRecognition`, `TelescopeConformalInverse`, `TelescopeDeckInvolution`, `TelescopeUnbranchedCover`, and `TelescopePathPairing`.
- Generic library inputs: the pinned Mathlib continuous-path API, connectedness and discrete-image constancy, complex algebra and exponentials, finite-type cardinalities, and the existing formal inverse/covering constructions. No paper theorem is introduced as an unproved Lean premise or new axiom.
- The source index assigns the three physical modules to `CONSTRUCT`, whose full native construction remains open. The generic path and ray helpers are supporting metadata and do not promote that route.

## Boundary

This contribution does **not** close `MAPPING_TELESCOPE`. It assumes the specified actual selected components and prefix/suffix injectivity; it does not prove that every native virtual block supplies them. Native relative-cover realization, compatibility with source-prescribed deck markings, relatively compact cyclic Jordan cores, and protected prime-end/access identification remain open.

The exact trace census concerns continuous paths allowed to meet the propagated critical value. The constructed paths retrace radial segments and revisit the critical point. For several excursions their source ranges can be branched finite stars. They are not certified proper embedded arcs, WAD leaves, laminations, or members of KKL's proof-used Wave class. Hence the census proves neither a Wave-width lower bound nor a counterexample to a native theorem restricted to a narrower path class. It proves that degree two alone cannot bound complete geometric trace multiplicity for the unrestricted continuous-path class.

The regular-loop result concerns the explicit loop family, not an arbitrary fundamental-group calculation. Its absence-of-section corollary concerns the entire regular target; it does not exclude local inverse branches, which already exist in the archive.

The radius depends on the actual return. Although one chosen radius supports every finite excursion count, the separation between adjacent ray markers shrinks as n grows. There is no uniform separation, positive transverse mass, modulus estimate, infinite-stage compactness, cross-scale compatibility, or parameter-global continuation claim.

No change to `ledger.json` or any status record is requested. `MAPPING_TELESCOPE`, `CONSTRUCT`, H1-H4, UPTCR, and MLC retain their existing open statuses. No mathematical priority beyond the archive is asserted. Human review: none.

## Attribution

The archive's saturated telescope, analytic ramification, univalent collar, parameter-stable return, and analytic deck-rigidity contributions supply the physical foundation. The precise prior boundary is documented in [the analytic deck-rigidity packet](../analytic_deck_rigidity_20261126/NOTE.md). The native mapping-telescope goal and its restrictions are set out in [critical chronology and the retimed telescope](../../research/mlc_unified/critical_chronology_and_retimed_telescope.md), especially section 15.3.

Classical inverse-function and covering-space theory underpin the reused formal constructions. Mathlib contributors supply the general topology, path, analytic, and arithmetic APIs. The additions here are the exact complete-lift and geometric-trace census, its explicit realization in the selected actual quadratic return, and the explicit physical loop-phase computation and section obstruction. AI assistance is disclosed in the front matter; successful Lean compilation and the dependency audit, rather than that assistance, supply the verification.
