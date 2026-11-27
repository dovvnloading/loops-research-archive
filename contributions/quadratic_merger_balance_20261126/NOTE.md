---
ledger: DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

<a id="quadratic-merger-balance-20261126"></a>

# Exact component merger accounting for actual quadratic target enlargements

## Claim

**Verified:** all four modules compile in the repository's pinned Lean 4.32.0 project, and the existing transitive axiom audit passes. The mathematical source checkpoint is [fd0f574](https://github.com/dovvnloading/loops-research-archive/commit/fd0f5740bc568fa4d7772f64265c73100772cb89), with [successful Lean CI and audit](https://github.com/dovvnloading/loops-research-archive/actions/runs/45927679722). This is a proved partial result; the native ledger obligation remains open.

This contribution addresses the component-preservation part of DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH. It supplies an exact criterion for arbitrary connected open targets of actual quadratic iterates, and constructs maximal failures of a weaker critical-inventory-only criterion. It does not identify these arbitrary targets with authorized native final-root enlargements.

Write $F=f_c^n$, where $f_c(z)=z^2+c$. Let $U\subseteq V$ be nonempty connected open subsets of the complex plane. Let $B$ be an actual connected component of $F^{-1}(V)$, and let $C$ be the finite census of actual connected components of $F^{-1}(U)$ lying in $B$.

The archive already defines the natural-number-valued reflection debt $d(D)$ recursively along the quadratic factorization. This contribution proves that it is independent of the chosen point in an actual component. It does not define debt by the desired merger identity or assert that debt counts topological holes.

Set
$
P_n=\{f_c^k(c):0\leq k<n\},\qquad
Q_{\rm new}=\sum_{t\in P_n\cap(V\setminus U)}\operatorname{defect}_B(t).
$
Each distinct postcritical target value occurs once. Its actual fiber deficit retains the local multiplicities of all its critical inverse points in $B$; repeated orbit values are not counted repeatedly.

### 1. Exact component merger balance

The main identity is
$
|C|+\sum_{D\in C}d(D)=1+d(B)+Q_{\rm new}.
$

**LoopsQuadraticMergerBalance.merger_balance_any_anchor** states this without requiring the target used to enumerate the census to be regular. A regular target exists inside every nonempty open $U$, and the existing census-independence theorem removes that auxiliary choice.

The charge has an exact analytic interpretation:
$
Q_{\rm new}=
\sum_{\substack{z\in B\setminus F^{-1}(U)\\F'(z)=0}}
\bigl(\operatorname{mult}_z(F)-1\bigr).
$
Consequently, $Q_{\rm new}=0$ if and only if the derivative is nonzero everywhere in the newly admitted part of $B$. This is component-specific: a new postcritical value can contribute zero when its critical inverse points lie in other components. The corresponding theorems are **newCriticalCharge_eq_new_ramification**, **newCriticalCharge_eq_zero_iff_no_new_critical**, and **newCriticalCharge_eq_zero_iff_deriv**.

### 2. An exact certificate for retained geometric traces

Choose $x$ with $F(x)\in U$, and let $A$ and $B$ be the old and enlarged components through that same point. Then
$
B\cap F^{-1}(U)=A
\quad\Longleftrightarrow\quad
d(B)+Q_{\rm new}=d(A).
$
The same scalar equality is equivalent to
$
\forall S\subseteq U,\qquad
B\cap F^{-1}(S)=A\cap F^{-1}(S).
$

The subsets $S$ may be disconnected. The conclusion concerns complete geometric inverse traces as subsets of the complex plane, and is not restricted to a selected parametrized path lift.

The selected old debt always satisfies $d(A)\leq d(B)+Q_{\rm new}$. For every specified retained target $t\in U$, strict inequality is equivalent to the existence of an actual inverse point
$
z\in B\setminus A,\qquad F(z)=t.
$
The target $t$ may itself be a critical value. A failed scalar certificate therefore has a geometric witness on every retained fiber, not just one generic comparison fiber.

These statements are **quadratic_enlargement_cartesian_iff_charge**, **quadratic_enlargement_all_traces_iff_charge**, and **quadratic_enlargement_charge_iff_missing_point** in LoopsQuadraticMergerBalance.

### 3. Maximal silent mergers for every parameter and depth

For every $c\in\mathbb C$ and $n\in\mathbb N$, **LoopsQuadraticCompactMerger.every_quadratic_compact_silent_merger** supplies an old disk $U$, an enlarged connected open target $W$, and a selected inverse component such that:

- Both targets have compact closure, and $\overline U\subseteq W$.
- $\overline W\subseteq\mathbb C\setminus P_n$; neither target contains a postcritical value through depth $n$.
- Exactly $2^n$ old inverse components occur in the enlarged component.
- Every old component is univalent and has debt zero.
- The selected enlarged component has debt $2^n-1$, while the newly admitted critical charge is zero.
- At every $t\in U$, exactly $2^n-1$ inverse points in the enlarged component are absent from the selected old component.
- For $n>0$, the retained-source square is not Cartesian.

The zero-depth case is included and has zero defect. The nontrivial obstruction is explicitly restricted to positive depth.

This realizes the full possible merger for an iterate of degree $2^n$. Neither unchanged postcritical inventory nor relative compactness of the targets suffices to guarantee component preservation for arbitrary connected open polynomial targets.

## Evidence

Four new modules are registered as default build targets in the pinned Mathlib-backed Lean project. Their 42 public theorems are listed in the existing physical-bridge index. Helper lemmas are included in that count; the mathematical advances are the identities, equivalences, and all-parameter construction above.

| Module | Public theorems | Role |
|---|---:|---|
| QuadraticMergerBalance.lean | 12 | Intrinsic component debt, exact balance, analytic identification of new charge |
| QuadraticMergerNaturality.lean | 6 | Cartesian criterion, arbitrary retained traces, missing-point witnesses |
| QuadraticSilentMerger.lean | 18 | Full-degree silent mergers over the complement of the finite postcritical set |
| QuadraticCompactMerger.lean | 6 | Compact target construction and maximal missing-fiber count |

### Proof of the balance

The argument uses three previously compiled archive results: component degree conservation over the merger census, target-wise defect conservation, and the aggregate critical-defect/debt identity. For each old component $D$, the last identity says
$
\text{retained critical deficit in }D+d(D)+1=\deg(D).
$
Sum this over $C$. Degree conservation turns the right side into $\deg(B)$. Target-wise defect conservation turns the sum of retained critical deficits into the retained deficit of $B$. The enlarged postcritical inventory is the disjoint union of its old and newly admitted parts. Comparing the summed identity with the enlarged component's existing debt identity cancels the retained charge and gives the stated balance.

The analytic charge formula uses the archive's exact local ramification census. Over a target in $V\setminus U$, the fiber in $B$ already lies in $B\setminus F^{-1}(U)$, so its target-wise deficit is exactly the sum of local multiplicity minus one there. Every actual critical point has positive local excess, which gives the vanishing equivalences.

### Proof of the trace criterion

The old selected component $A$ belongs to $C$. Its debt is at most the total old debt. If there is a competing component, its contribution to $|C|+\sum d(D)$ is at least one. The exact balance therefore gives
$
d(B)+Q_{\rm new}=d(A)\quad\Longleftrightarrow\quad C=\{A\}.
$
The census membership theorem identifies singleton census with $B\cap F^{-1}(U)=A$. Intersecting with $F^{-1}(S)$ gives the statement for every retained subset $S$; taking $S=U$ gives the converse. The archive's complete-fiber characterization of no merger supplies the missing-point equivalence at every retained target, including critical targets.

### Proof of the relatively compact construction

Start with $V=\mathbb C\setminus P_n$. Its full inverse image is the plane minus a finite set, because every actual polynomial fiber is finite. Both sets are path connected. Hence the selected enlarged component contains every global inverse point of every $y\in V$, and has full degree $2^n$. Since the target contains no postcritical values, the existing aggregate identity gives debt $2^n-1$.

For relative compactness, choose a regular target $y$ and an inverse anchor $x$. Join every point of the finite global fiber over $y$ to $x$ by an actual path in $F^{-1}(V)$. The finite union of the path ranges is a compact preconnected set $K$ containing the complete fiber. Its image $F(K)$ is compact and preconnected inside $V$.

Apply the archive's existing **connected_precompact_target_neighborhood** theorem to obtain a connected open $W$ containing $F(K)$, with compact closure inside $V$. Because $K\subseteq F^{-1}(W)$ is preconnected through $x$, the selected $W$-component contains the complete global fiber over $y$; it therefore still has full degree. Finally choose a disk around $y$ with compact closure inside $W$. The archive's postcritical-free simply connected univalence theorem gives degree one and debt zero on every old component. The census degree identity and fiber-cardinality subtraction give the exact merger and missing-point counts.

The classical connectedness and univalence inputs are imported. They are not re-proved as the claimed advance.

### Committed validation record

The draft [PR #231](https://github.com/dovvnloading/loops-research-archive/pull/231) was opened before proof development, and every proof checkpoint was committed into it.

- [9dc3410](https://github.com/dovvnloading/loops-research-archive/commit/9dc34109261a4040ad3ffa7cf24b3c222d648006): initial balance and naturality development. Source registration and the proof-trust scan passed; CI found two implicit inverse-image set elaboration errors.
- [850c093](https://github.com/dovvnloading/loops-research-archive/commit/850c0936c2a307b4b35d50d94292993190216cb8): explicit source-set fixes, all-parameter silent mergers, and analytic vanishing criteria. The core balance proofs passed; one added zero-charge proof had an underconstrained finite-sum weight.
- [9aab93b](https://github.com/dovvnloading/loops-research-archive/commit/9aab93b079ece63e90b9058dd747b2f0e7e5fb1c): the balance and naturality modules compiled. The final silent-merger theorem needed an explicit conversion from the set-level simple-connectedness predicate to its underlying typeclass. The next checkpoint made that proof conversion explicit in both disk constructions, without changing a theorem statement.
- [0f73c4f](https://github.com/dovvnloading/loops-research-archive/commit/0f73c4f991f876c2377cc6dea7160b441a923cfa): the balance, naturality, and silent-merger modules compiled. The compact path-hull helper needed explicit lambdas to apply two set-inclusion proofs. The next checkpoint supplied those lambdas without changing the helper's statement or any dependent theorem.
- [fd0f574](https://github.com/dovvnloading/loops-research-archive/commit/fd0f5740bc568fa4d7772f64265c73100772cb89): all four modules compiled and the transitive axiom audit passed. All 23 workflows on this proof checkpoint succeeded.

The existing weighted build completed all 8,972 jobs. The declaration audit reported:

| New module | Audited declarations | Result |
|---|---:|---|
| QuadraticMergerBalance | 23 | Allowed foundational axioms only |
| QuadraticMergerNaturality | 13 | Allowed foundational axioms only |
| QuadraticSilentMerger | 34 | Allowed foundational axioms only |
| QuadraticCompactMerger | 11 | Allowed foundational axioms only |

These audit counts include compiler-generated and private declarations, so they differ from the public theorem index counts. The complete weighted audit passed for 151 modules and 3,281 declarations. It checks transitive dependencies using Lean.collectAxioms and permits only propext, Classical.choice, and Quot.sound. The source scan enforces absence of proof placeholders and prohibited trust escapes; no such escape or new axiom is present in the contribution. The contribution check also passes without the draft exemption, and the whitespace check passes.

All compiler repairs so far name existing terms explicitly; no theorem statement has been weakened. Local Lean compilation is unavailable in this workspace, so the repository's existing pinned CI build and transitive declaration audit are the validation authority. No workflow, validator, dependency pin, or ledger status has been changed.

## Dependencies

The target is DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH. Its listed proper-path and end-interval classification prerequisite remains open. The four other listed prerequisites are already marked proved; this contribution does not discharge their source-specific hypotheses or remove their stated scope restrictions. The target specification is [PE-5](https://github.com/dovvnloading/loops-research-archive/blob/main/research/mlc_unified/canonical_kl_geometric_trace_proper_end_response.md#pe-5-final-root-relation-no-birth).

The principal existing formal inputs are QuadraticEnlargementDegree, QuadraticComponentFiberDegree, QuadraticCylinderRamification, QuadraticLocalRamification, QuadraticRamificationCensus, and QuadraticInverseOpen. Mathlib supplies finite sums, compactness of finite path unions, and connectedness of finite-set complements.

The archive already has a reflection-rank equality criterion for no merger, degree conservation, and critical-deficit accounting. The new advance is their exact componentwise decomposition into newly admitted analytic critical charge and reflection-debt transfer, together with arbitrary-retained-trace equivalences and an all-parameter maximal realization inside relatively compact targets. It is not a claim that the rank criterion or classical finite-covering phenomena are new.

## Boundary

This is a partial result about actual complex polynomial inverse components. It is not a complete proof of the ledger obligation, and no ledger status change is requested.

The native final-root authorization, canonical/KL relation alignment, localization subgroup reflection and exhaustion, compactified endpoints and frames, proper-path status and multiplicities, protected accesses, obstacles, nonproper bridges, and cyclic order are not supplied by the component identity. The trace theorem controls subsets of the retained target $U$; it does not classify new target trace portions lying in $V\setminus U$.

The sharp example is an actual quadratic construction, but is not asserted to be an authorized native KL final-root enlargement. It disproves the sufficiency of a critical-inventory-only test for arbitrary connected open targets, including relatively compact targets. It does not refute the native ledger statement. A source-level closure must prove that its certified enlargements satisfy the required component criterion and must separately construct the remaining compactified and marked data.

H1-H4, UPTCR, and MLC remain open. No priority claim over the mathematical literature is made.

## Attribution

Builds on the archive's actual quadratic component degree, enlargement conservation, local multiplicity, critical census, and compact-neighborhood contributions. The native source motivation is Kahn-Lyubich decoration theory and the repository's canonical/KL geometric-trace specification. Proof development and review are AI-assisted; there has been no independent human review.
