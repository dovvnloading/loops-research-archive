---
ledger: KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; Lean proof development, implementation, and independent AI mathematical review
human_review: none
---

<a id="local-degree-saturation-20261126"></a>

# Actual local ramification and finite-return carrier isolation

## Claim

This contribution formalizes local sheet exhaustion for actual complex quadratic
iterates and uses it to recognize a supplied primitive quadratic carrier as an
entire connected component of every finite return pullback. It also constructs
analytic power coordinates and counts the actual local inverse fibers for every
finite quadratic iterate, including repeated visits to the critical point.

All counted results are named Lean theorems in the existing weighted project.
The target ledger row remains open: the supplied embedding/conjugacy and the
identification with the particular KKL and Kiwi geometric objects are not
constructed here.

Write \(f_c(z)=z^2+c\), \(F_{c,n}=f_c^n\), and let \(K_c\) be the actual bounded-orbit
filled set, represented by the archive's proved escape-potential definition.

### 1. Arbitrary local ramification is realized analytically

For every \(c,x\in\mathbb C\) and every \(n\in\mathbb N\), define

\[
\nu(c,x,n)=\#\{j<n:f_c^j(x)=0\},\qquad m=2^{\nu(c,x,n)}.
\]

The theorem *quadratic_power_disk_chart* constructs \(a\ne0\), \(r>0\), an actual
open neighborhood \(U\) of \(x\), and analytic inverse coordinates
\(\phi:U\to B(0,r)\), \(\chi:B(0,r)\to U\), satisfying

\[
\phi(x)=0,\qquad \phi'(x)=1,\qquad
F_{c,n}(z)-F_{c,n}(x)=a\,\phi(z)^m\quad(z\in U).
\]

The exponent is computed from the actual orbit. A local degree, a branch chart,
or a bound on the number of critical encounters is not a premise. The theorem
includes \(n=0\) and repeated critical returns.

The theorem *quadratic_local_fiber_census* constructs an open neighborhood \(U\)
and \(\varepsilon>0\) for which the repository's actual finite inverse fiber obeys

\[
\operatorname{localFiber}(c,n,U,F_{c,n}(x))=\{x\},
\]

and, for every \(w\ne F_{c,n}(x)\) with
\(\operatorname{dist}(w,F_{c,n}(x))<\varepsilon\),

\[
\#\operatorname{localFiber}(c,n,U,w)=2^{\nu(c,x,n)}.
\]

Every complex power root is shown to lie in the chart disk and is transported
through the analytic inverse. Thus the census counts actual distinct inverse
points, including the collision at the central target.

### 2. Local degree bounds force geometric exhaustion

Let \(h:K_q\to\mathbb C\) be continuous and injective, let \(F:\mathbb C\to\mathbb C\)
be continuous, and suppose

\[
F(h(u))=h(f_q(u))\qquad(u\in K_q).
\]

At each intrinsic noncritical point assume an actual open neighborhood of \(h(u)\)
on which \(F\) is injective. At an intrinsic critical point assume a local
two-point fiber bound and a singleton fiber over its central target.
*quadratic_conjugacy_local_exhaustion* constructs an open neighborhood \(V\) of
\(A=h(K_q)\) with the exact equality

\[
V\cap F^{-1}(A)=A.
\]

Complete backward invariance and openness of the genuine quadratic source
produce the nearby inverse points. At zero, a symmetric intrinsic neighborhood
produces both opposite roots. Their images exhaust the ambient local fiber.
Compactness and injectivity construct the ambient target neighborhoods needed
to pass from intrinsic to ambient statements.

Consequently \(A\) is relatively clopen in \(F^{-1}(A)\). If \(A\) is preconnected,
it is the entire connected component through each of its points. No path
connectivity or local connectivity is required, and external connected
appendages are excluded. The exhaustion and clopen theorems themselves also
cover disconnected \(K_q\).

### 3. Primitive phase separation supplies the analytic premises

For \(n>0\), suppose \(0\in K_q\), \(h:K_q\to\mathbb C\) is continuous and injective,

\[
f_c^n\circ h=h\circ f_q,\qquad h(0)=0,
\]

and the central image is disjoint from each intermediate phase:

\[
h(K_q)\cap f_c^j(h(K_q))=\varnothing\qquad(0<j<n).
\]

*quadratic_primitive_conjugacy_component* derives source connectedness,
critical compatibility, local injectivity or the local square chart as
appropriate, and an ambient isolating neighborhood. It proves

\[
A\subseteq K_c,\qquad
A=\operatorname{Comp}_0\bigl((f_c^n)^{-1}(A)\bigr).
\]

The inclusion in \(K_c\) is itself proved: the escape potential attains a maximum
on any compact return-invariant carrier, while a positive return multiplies
that potential by \(2^n>1\). Its maximum must therefore vanish.
*quadratic_compact_return_invariant_subset_filled* states this independently
for every compact set invariant under a positive quadratic return.

No component equality, neighborhood univalence, local degree, or ambient
filled-set membership is assumed in the primitive theorem. The exact conjugacy
and the phase-disjointness hypotheses remain substantive inputs.

The more general *quadratic_return_conjugacy_isolation* uses an independently
verified critical itinerary instead of phase disjointness: no preterminal
critical encounter off the intrinsic critical point, and exactly one at it.

### 4. The exact component persists through every finite return depth

Under the same primitive hypotheses,
*quadratic_primitive_conjugacy_all_returns* proves, for every \(k\ge0\),

\[
A=\operatorname{Comp}_0\bigl((f_c^{nk})^{-1}(A)\bigr).
\]

For every prescribed finite horizon \(H\), it also constructs one open
neighborhood \(W_H\supseteq A\) with

\[
W_H\cap(f_c^{nk})^{-1}(A)=A\qquad(0\le k\le H).
\]

The explicit recursive window starts with the whole space and replaces a window
by \(V\cap F^{-1}(W)\), where \(F=f_c^n\) and \(V\) is the constructed one-return
isolating neighborhood. The windows decrease and retain the carrier.
A single neighborhood uniform over all infinite horizons is not concluded.

## Evidence

The six new modules contain 29 public theorem declarations, all registered in
the existing build and theorem index.

| Module in formalization/weighted/ | Public theorems | Role |
|---|---:|---|
| QuadraticLocalNormalForm.lean | 3 | Construct local analytic square coordinates and one/two-sheet bounds from actual critical itineraries. |
| LocalDegreeExhaustion.lean | 5 | Construct ambient root exhaustion, an isolating neighborhood, relative clopenness, and full component equality. |
| QuadraticPowerNormalForm.lean | 3 | Construct analytic power charts and inverse round-disk charts at every local multiplicity. |
| QuadraticLocalFiberCensus.lean | 4 | Transport all complex power roots and count actual local inverse fibers. |
| IteratedCarrierIsolation.lean | 9 | Prove explicit finite-window identities and component persistence in arbitrary topological spaces. |
| QuadraticCarrierSaturation.lean | 5 | Establish actual filled-set membership and primitive/all-finite-return component recognition. |

The existing CI scans all source, builds the weighted project, and audits every
declaration transitively, including private helpers and generated declarations.
The unchanged foundational allowlist is propext, Classical.choice, and
Quot.sound. No proof hole, new postulate, native decision shortcut, or workflow
change is introduced.

Reproduction, with the repository's pinned Lean 4.32.0 and Mathlib v4.32.0:

~~~sh
cd formalization/weighted
lake exe cache get
lake build
cd ../..
python3 -B code/verify_lean_coverage.py --audit weighted
python3 code/contribute.py check
~~~

The current execution environment has no usable Lean installation and became
unavailable during development. No local compilation is claimed. Implementation
checkpoints were committed directly to [PR #224](https://github.com/dovvnloading/loops-research-archive/pull/224);
the exact revision's CI build and complete dependency audit are the validation
authority.

Verified intermediate checkpoint:
[ac064dc1147c674fb1cfe58b7f6079c2d99031d9](https://github.com/dovvnloading/loops-research-archive/commit/ac064dc1147c674fb1cfe58b7f6079c2d99031d9)
passed the [full weighted build and audit](https://github.com/dovvnloading/loops-research-archive/actions/runs/45912644285/job/140224482245):
121 modules and 2,965 declarations. That checkpoint contains the first two
modules; all 8 declarations of QuadraticLocalNormalForm and all 7 declarations
of LocalDegreeExhaustion passed the audit. Later modules are governed by the
subsequent exact-head checks linked from the PR.

Independent AI reviews examined the critical-target case, disconnected sources,
the phase-to-critical-itinerary implication, the all-finite-horizon quantifiers,
and the distinction between a full ambient pullback component and a complete
monotone quotient fiber. These reviews are separate from kernel validation and
are not human peer review.

## Dependencies

The proof reuses actual statements from the archive:

- QuadraticUnivalentNeighborhood: extend critical-free compact injectivity to
  open injectivity.
- TelescopeConformalInverse: construct analytic inverse branches on proved
  univalent open domains.
- TelescopeRamification: exact actual-orbit factorization with exponent
  two to the number of criticalVisits.
- StationaryFiberDynamics: compactness and complete invariance of quadraticFilled.
- QuadraticEscape and QuadraticEscapeFullness: the escape functional equation,
  the bounded-orbit meaning, and connectedness when the critical orbit is bounded.
- The existing localFiber definition in the quadratic cylinder census.

Mathlib's analytic logarithm, inverse function theorem, and complex power-root
results supply the standard analytic and algebraic steps. They are used as
compiled theorem imports, not as new assumptions.

The target ledger prerequisites remain KKL_NATIVE_TERMINAL_HUBBARD_TREE,
KKL_STATIONARY_MODEL_TERMINAL_SHEET_INCIDENCE, and
KKL_STATIONARY_SELECTED_PREDECESSOR_CHAIN.
The contribution does not edit their status or the target's status.

## Boundary

The requested ledger equality for KKL's exact non-LC projection is not proved.
The archive's stationary fiber-saturation note, section 3.2, states a general
branched-cover exhaustion lemma; section 3.3 applies it to induced Kiwi plane
maps. This contribution proves an analytic specialization for actual quadratic
maps and finite iterates. It does not identify those quotient maps with the
polynomial coordinates used here.

The exact embedding/conjugacy is supplied. The primitive specialization uses
disjoint central/intermediate phases and does not assert their existence for
the native KKL construction. Touching or satellite phases need independently
verified itinerary hypotheses; they are not covered automatically.

An entire selected component of \(F^{-1}(A)\) need not be the whole set
\(F^{-1}(A)\). The theorem allows other pullback components. It does not prove
the full monotone-fiber identity, the selected geometric continuum correspondence,
or the required marked accesses and collars.

No straightening theorem, polynomial-like recognition theorem, native Wave
estimate, uniform infinite-horizon clearance, H1-H4, or MLC conclusion is claimed.
No ledger promotion is requested. These are advances in the archive's formal
coverage, not claims that classical local analytic normal forms or the written
exhaustion argument are new mathematics.

## Attribution

The local exhaustion argument is credited to the archive's
research/independent_audits/stationary_fiber_saturation_20261126/NOTE.md,
section 3.2. Existing compact-univalence, analytic-inverse, exact ramification,
geometric-fiber, and filled-set-fullness proofs are reused and credited above.
All new proofs and this note are contributed under the repository's CC0 license.
