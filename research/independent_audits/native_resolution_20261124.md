# Complete selected-family buffer exclusion and native transport refinements

**24 November 2026.** Based on archive revision
`9340778fa59029e1bfba88639b03dfb63115cab3`.

The main new result is a complete calculation of the support of the
canonical buffered arc diagram on the selected four-boundary surfaces:
**it is empty for every selected integer period p >= 10**. This resolves
the former large-period inner-support question and gives a concrete
obstruction to transferring the positive independent unbuffered defect to
that particular canonical diagram. It does not resolve MLC.

Three investigations were developed in parallel and cross-reviewed with
OpenAI GPT-6 Astra Pro assistance. The analytic proofs are written and use
the classical inputs stated in their individual notes. The exact checkers
certify their arithmetic and finite consequences; they do not formalize
the complex analysis. No human specialist review or novelty certification
is claimed.

## 1. What is now determined

Let `G=f_(c_p)^p:V_p -> U_p=D(0,R_p)` be the archive's selected real
restriction, and let `K0,K1,K2` be its three actual little filled
intervals. Define

\[
 Y_p=U_p\setminus(K_0\cup K_1\cup K_2).
\]

Use the **whole-component ideal marking**: each of the four ideal circles
is one marking component. This is the marking used for the unrefined
canonical diagram. For every eligible proper simple arc class `alpha`,
let `q_alpha` be its full universal quadrilateral width, with the KKL
normalization

\[
 w_\alpha=\max\{q_\alpha-2,0\}.
\]

The [complete exclusion proof](canonical_width_attack_20261124/NOTE.md)
gives, uniformly in all selected `p>=10` and all such arc classes,

\[
 q_\alpha<\frac{1999}{1000}<2,
 \qquad W_{\mathrm{can}}(Y_p)=0.
 \tag{1}
\]

This covers arbitrary windings and essential returning arcs. It is not
an enumeration truncated at a chosen deck-word length. The proof uses
embedded slit-and-cut rings to bound all four peripheral hyperbolic
lengths, the hyperbolic collar lemma for different boundary components,
and disjoint peripheral shadows for arcs returning to the same component.

| Peripheral component | Strict hyperbolic length upper bound |
|---|---:|
| Central little interval `K0` | `597/100` |
| Right little interval `K1` | `16/5` |
| Left little interval `K2` | `419/100` |
| Outer circle | `15/4` |

The two largest bounds already force every distinct-boundary seam beyond
the exact width-two distance `(log 2)/2`. A returning class consumes two
distinct peripheral shadow intervals; the length budget excludes it as
well. Exact intervals cover `p=10,...,16`, and a single corrected analytic
tail box covers every `p>=17`.

The earlier independent width theorem remains valid:

\[
 D_p=\frac1{C_p^+}+\frac1{C_p^-}-\frac1{P_p}>\frac1{100}.
 \tag{2}
\]

Equations (1) and (2) are compatible because (2) concerns independent
unbuffered Wave suprema on specified slit-tree path classes. In
particular, there is no positive constant `a` for which the proposed
direct comparison `||W_can(Y_p)|| >= a D_p` holds on this family.
Refining the marking changes the admissible arc classes and can introduce
classes subordinate to a whole boundary component. The proof of (1) does
not apply to arbitrary refinements, the ten-atom slit annulus, or an
all-scale protected tower. The cases `3<=p<=9` remain outside this
certificate.

The selected return exponent `p`, the native little-cycle period three,
and the native rotation denominator two are different clocks. Sending
the first to infinity does not make the latter two large. This is a
specific obstruction to a proposed calibration, not a contradiction of
KKL's near-degenerate or large-width theorems.

## 2. The path question is narrower

The [path proof](native_mark_attack_20261124/NOTE.md) supplies two
independent statements on the actual selected slit pair.

First, forgetting repeated component labels does not change the induced
ideal-set pullback:

\[
 \iota^*_{\mathrm{set}}X=q^{-1}(X)
 =\iota^*_{\mathrm{occ}}X,
 \qquad \iota^*_{\mathrm{set}}O=O'.
 \tag{3}
\]

A singleton unindexed restriction set has only finitely many
occurrences: each visits the same two distinct interior points, and
uniform continuity gives a positive lower bound on its parameter span.
Finitely many subordinate component homotopies can then be pasted.
The result includes points, open and closed arcs, punctured circles,
and the complete inner circle.

Second, for a **simple** proper parent, every proper path in its source
trace is homotopic relative to ideal endpoints either to a complete
maximal component or to a null hairpin. The marking filters discard the
latter. Thus raw-trace restrictions create no additional nontrivial arc
support for simple leaves. Path-as-map uniqueness, multiplicity, and
nonsimple pushed parents are different questions.

There is also a separate, explicitly **source-imported** route for the
original finite marking. The selected physical pair satisfies KKL
Propositions 6.5–6.6 with `q=2,b=2`; accepting those propositions yields
the native finite action. Proposition A.14 then rules out a nonempty
chain of lamination descendants selected from successive unbreakable
pushforwards through the saturation time, at most five steps, **when the
starting crest contains an original marked interval**. The
191-input certificate retains the difference between a punctured circle
and a full circle.

Importing a proposition under verified hypotheses is distinct from
independently repairing its proof. The note states the source's compressed
argument and typographical issue explicitly. Full independent `MARK`
and arbitrary finer-subarc native dynamics remain open.

## 3. Stationary exits can have different ends

The [variable-end theorem](stationary_transport_attack_20261124/VARIABLE_END_EXIT_TRANSFER.md)
replaces a common terminal endpoint by a finite budget of actual ends.
After Borel-selecting one maximal immersion lift joining distinct ideal
boundary components per simple parent, let `E` be the
graph of the **actual** unordered endpoint pairs, and let `L_v` be each
end's cyclic-cover local width. Then

\[
 \mathcal W(A)\le
 \inf_{a_v\ge0,\ a_u+a_v\ge1\ (\{u,v\}\in E)}
       \sum_v a_v L_v.
 \tag{4}
\]

Disjoint Borel geometric supports justify the parallel additivity used
in this bound. Tagged coincident images are not treated as disjoint.
The finite endpoint problem can improve a common-end or integral-cover
estimate; a triangle with equal budgets has the exact bound `3L/2`.

For the actual degree-`2^m` pullback, all ends above at most `b` target
small Julia sets have total peripheral degree at most `b 2^m`. Actual
exits incident to that collection therefore give

\[
 \mathcal W(A)\le b2^m\mathcal W(\mathcal RF).
 \tag{5}
\]

For fixed `b,m`, this bound is independent of the primitive period. A
sharper finite bank of the canonical degree-two predecessors gives
`2r W(RF)` at depth `m=b+r`, **with `2<=r<P` where `P` is the native
primitive little-cycle period**, if each parent has two distinct actual
bank hits, with the pair allowed to vary by parent. Here `P` is not the
selected return exponent `p` of Section 1. Both conclusions still require those physical
exits or hits. An endpoint on a carrier edge does not qualify as an ideal
endpoint on a removed little Julia set. The new theorem reduces the
existence target; it does not construct the missing exits.

## 4. Consequences for the research direction

The selected large-period inner canonical coefficients no longer need an
open-ended search: they vanish in the specified marking. A successful
calibration must therefore use a different explicitly defined observable
or a genuinely different geometric regime, with its own proved transfer.
The positive unbuffered defect alone cannot supply this missing step.

The path result removes occurrence deduplication and extra simple-leaf
arc support from the unresolved list. It leaves the all-path source
convention and quantitative retention visible. The stationary theorem
permits variable endpoint components, so a new construction can target
pointwise exits with a bounded degree sum rather than the stronger common
component assertion.

The global construction, calibration, nondegenerate compactness, and
rigidity/parameter-neighborhood obligations remain open. The canonical
465-entry July ledger, its statuses, and the historical November update
records are unchanged.

## 5. Reproduction

From the repository root:

```sh
python3 -B research/independent_audits/canonical_width_attack_20261124/verify.py --check-manifest
python3 -B -m unittest discover -s research/independent_audits/canonical_width_attack_20261124 -p 'test_verify.py' -v
python3 -B research/independent_audits/native_mark_attack_20261124/verify.py --check-manifest
python3 -B research/independent_audits/stationary_transport_attack_20261124/verify.py
python3 -B code/verify_physical_bridges.py
```

The individual notes state the analytic inputs, normalization proofs,
source pages, and exact scope of the computations. The pre-existing
selected-family theorem chain and its adversarial tests were also replayed
successfully during this investigation.
