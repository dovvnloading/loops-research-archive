---
ledger: KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION
result: partial
ai: OpenAI GPT-6 Astra Pro
human_review: none
---

<a id="unique-model-branch-20261127"></a>

# Unique model critical point and exact predecessor transport

## Claim

For the actual filled set K of f_c(z)=z^2+c, assume 0 belongs to K
and K has empty interior. Let p:K->Y be a continuous surjective
semiconjugacy to G:Y->Y, with connected geometric fibers, Hausdorff
target Y, and light model dynamics (every inverse-point fiber of G
is totally disconnected). Write b=p(0) and v=p(c)=G(b).

This contribution proves the following in the repository's Lean project.

1. The actual quadratic map is injective on every geometric fiber
   other than p^(-1){b}. The descended reflection S has exactly one
   fixed point: S(y)=y if and only if y=b.
2. The unique singleton inverse fiber is G^(-1){v}={b}. Every other
   model target has exactly two predecessors.
3. Every target w different from v has an open neighborhood W avoiding
   v whose full inverse image is the disjoint union of two open model
   sheets. Both sheets and both exact full physical lifts map
   bijectively onto their respective target sets.
4. If b is nonisolated, G has an injective open neighborhood at y if
   and only if y differs from b. For a nontrivial connected model,
   nonisolation is derived, so b is exactly the unique failure of
   local injectivity. An independently designated model critical point
   is proved equal to p(0) from its failure of local injectivity alone;
   that identification needs no nonisolation or connectedness premise.
5. For every target y and depth n, the complete distinct-predecessor
   count N_n(y)=card(G^(-n){y}) obeys

   N_0(y)=1,
   N_(n+1)(y)+[G^n(v)=y]=2*N_n(y).

   Defining D_0(y)=0 and D_(n+1)(y)=2*D_n(y)+[G^n(v)=y] gives the exact
   identity N_n(y)+D_n(y)=2^n. Consequently the count is 2^n exactly
   when y avoids v,G(v),...,G^(n-1)(v). All repeated projected
   postcritical encounters are retained. A finite proposed collection
   of genuine predecessors is exhaustive exactly when its cardinal
   plus D_n(y) equals 2^n.
6. For every actual a in K whose projected target p(a) avoids that
   finite model postcritical set, the original projection restricts
   to a bijection

   p : f_c^(-n){a} -> G^(-n){p(a)}.

   The complete geometric fiber over p(a) may be nontrivial.

The conclusion in item 4 concerns local injectivity. The cardinal
identities in item 5 count distinct inverse points; they are not
statements about a complex derivative or algebraic multiplicity on Y.

### What is new relative to the archive

[The preceding model-degree packet](../stationary_model_degree_20261126/NOTE.md),
Evidence item 10, explicitly leaves identification of the involution's
fixed locus open. Its local sheet theorem requires independently
distinguishing the two projected physical roots. Its all-depth
arbitrary-target result is an upper bound; exactness is proved for
singleton physical target fibers.

The new compact-fiber argument resolves that specific fixed-locus gap.
It removes the sign-distinguishing premise from all noncritical model
sheets, derives exact counts at arbitrary model targets, and removes
the singleton-target premise from inverse-label transport off the
projected postcritical set. The existing reflection descent,
whole-fiber transport and planar bypass arguments are reused.

## Evidence

Four registered Mathlib-backed modules contain 32 public theorems:

| Module | Main result |
| --- | --- |
| [StationaryUniqueBranch](../../formalization/weighted/StationaryUniqueBranch.lean) | Noncritical geometric-fiber injectivity and unique descended fixed point |
| [StationaryModelPredecessors](../../formalization/weighted/StationaryModelPredecessors.lean) | Exact one-step fibers and open sheets with full physical lifts |
| [StationaryBranchLocus](../../formalization/weighted/StationaryBranchLocus.lean) | Exact local injectivity locus, including the nondegeneracy condition |
| [StationaryBranchCensus](../../formalization/weighted/StationaryBranchCensus.lean) | Complete inverse census and actual/model inverse-fiber bijection at every depth |

### Proof mechanism

A geometric fiber away from b is compact and connected and omits zero.
The archive's actual-filled-set bypass theorem says a collision of
opposite quadratic roots in such a set would force zero into its
closure. Compactness makes the set closed, giving a contradiction.
Thus a collapsed reflected pair must lie over b. The independent
descended-reflection theorem then identifies the whole fixed locus.

For local branching, intersect any proposed injective neighborhood of
b with its reflected preimage. Pair completeness forces this open
intersection to be the singleton {b}, contradicting nonisolation.
Away from b, Hausdorff separation of the pair supplies an injective
neighborhood.

For the exact census, choose one inverse r(w) of each model target.
The other inverse is S(r(w)); they coincide exactly at w=v. The
complete next inverse level is the disjoint union of r(M_n) and
S(r(M_n minus {v})). Counting these sets yields the recurrence,
including critical targets and repeated critical visits.

For inverse-label injectivity, induct on depth. Two physical inverse
points with the same model label have equal one-step images by the
induction hypothesis. The common label cannot be b, because that
would put the final model target on the excluded postcritical orbit.
Noncritical geometric-fiber injectivity then identifies the two
physical points. Existing complete fiber transport provides
surjectivity.

### Verification

The unchanged repository workflows on
[PR #240](https://github.com/dovvnloading/loops-research-archive/pull/240/checks)
are the compilation and transitive dependency-audit authority.
The source modules, all public theorem names, and default Lake targets
are registered. No workflow, checker, status record, or trusted
mathematical constant is added or changed.

Reproduce from the repository root:

```sh
cd formalization/weighted
lake build StationaryUniqueBranch StationaryModelPredecessors StationaryBranchLocus StationaryBranchCensus
cd ../..
python3 -B code/contribute.py check
python3 -B code/verify_lean_coverage.py --audit weighted
```

The local workspace filesystem was full and no Lean executable was
available, so compilation is performed by repository CI rather than a
local build. The PR preserves implementation and correction commits;
its final head must pass before these results are counted.

## Dependencies

Target: KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION.

Formal dependencies: StationaryLightModel (descended reflection,
complete fiber transport, open sheets, inverse projection);
StationaryCompactContact (actual-filled-set bypass accumulation);
StationaryFiberDynamics and TerminalFiberExclusion (the actual filled
set, its compactness, complete invariance and surjectivity); Mathlib
topology, finite sets, and natural-number arithmetic.

Source context:
[the selected-predecessor audit, Proposition 4.5](../../research/mlc_unified/kkl_stationary_n2_selected_predecessor_endpoint.md#proposition-45-monotone-full-lift-criterion)
and
[the KKL/Kiwi identification audit](../../research/mlc_unified/kkl_stationary_n2_kiwi_model_identification_audit_20260727.md).

## Boundary

This is partial progress on the ledger row. It resolves the
critical-point-image clause for the stated class of actual quadratic
geometric quotient models; it does not establish the entire row.

The projection p, its monotone semiconjugacy properties, model
lightness, bounded critical orbit, and empty interior are explicit
hypotheses. Empty interior is not derived here from periodically
repelling dynamics. Genuine local branching requires nonisolation,
or a nontrivial connected model. The degenerate singleton quotient
satisfies the other assumptions and is handled correctly by the
counting statements, but has no failure of local injectivity.

The named KKL/Kiwi projection and physical lift still require
identification. The dendrite property, selected alpha correspondence,
singleton fixed-alpha fiber, full carrier identity T=p^(-1)(T_com),
selected Q_n-sheet correspondence, and geometric small-Julia-continuum
correspondence are not supplied here. Finite inverse-fiber bijectivity
does not imply singleton geometric fibers, native ideal-access
landing, or marked Wave transport.

No ledger status change is requested. H1-H4 and MLC remain open.
No claim of literature priority or independent human review is made.

## Attribution

Builds on Matthew Robert Wesney's archive, the prior Lean contributors
identified in the linked source packets, and Mathlib. Kahn, Kapiamba,
Lyubich, Kiwi, Douady and Hubbard retain attribution for their cited
dynamical constructions and theory. AI assistance: OpenAI GPT-6 Astra
Pro; human review: none. Released under the repository's CC0 terms.
