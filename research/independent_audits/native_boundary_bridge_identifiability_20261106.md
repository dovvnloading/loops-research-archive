# Native interval-growth bridge: a coupled boundary certificate and a sharp information-loss example

**Date:** 2026-11-06  
**Target:** `KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR`  
**Predecessor:** [interval-growth repair](./interval_growth_repair_20261106.md), merged as PR #38.  
**Status:** a native source audit, a proved finite/topological bridge criterion, a coupled exact model, and a negative identifiability result. **The native analytic prime-end identification and the ledger gate remain OPEN.**

## 1. Result and boundary

The preceding repair required a **single faithful** interface from the Kahn–Kapiamba–Lyubich (KKL) ideal boundary and its immersion/cover dynamics to a marked contour with (a) complete edge multiplicities, (b) actual attachment gates, and (c) exact open/closed crests. An arbitrary expanding edge matrix and a separate expanding interval program are insufficient, even when both programs pass tests.

This pass establishes three narrowly distinguished results.

1. **Native exceptional-locus reduction (source consequence).** KKL's actual immersion pullback formula and proper-corridor statement imply that for parabolically `b`-bounded rotation `1/q`, the potentially nonproper limb indices occupy at most `min(q,2b+1)` limbs, whose total marked combinatorial length is at most `6b min(q,2b+1)`. This is a one-step support bound, **not** the missing global interval-growth theorem.
2. **Coupled finite boundary certificate (proved in the model).** An oriented degree-two boundary covering and one degree-one monotone source-to-target quotient produce a single exact interval action. In the ten-atom example, the edge-incidence matrix is **derived from precisely those boundary words**, not independently asserted. The same certificate checks all 100 proper marked intervals, zero-weight sector escape, and the `3/2` rational edge-weight estimate.
3. **Sharp finite-data nonidentifiability (proved countermodel).** There are two degree-one monotone quotients, one injective and the other with a nontrivial interior interval fiber, whose pullbacks of **every open or closed multi-interval of the old finite marking** agree. After the *same* degree-two covering, they have identical finite interval dynamics and identical derived edge matrix, but different fibers over an unmarked access. Therefore **no inspection of those finite interval words and incidence rows alone can determine the attachment/prime-end collapse data**. A source-realized access or fiber record is unavoidable.

The countermodel lives on topological circles, not on the actual KKL annuli or a quadratic polynomial. It does **not** show that KKL's native theory has a collapsing attachment or that their claimed conclusion is false. It establishes a logical limit on what the finite word/edge data could certify without additional hypotheses.

No status change is made to `KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR`, `KKL_PARABOLIC_WAVE_AMPLIFICATION`, H1–H4, UPTCR or MLC.

## 2. Primary source and scope

Source: Jeremy Kahn, Alex Kapiamba, and Mikhail Lyubich, *MLC for parabolically bounded primitive renormalization*, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1). The checked definitions/results are:

| Location | Actual source input | **Not** automatically supplied |
|---|---|---|
| §2.5 | Complete cycle of small filled Julia sets; native Hubbard tree; its abstract edge-incidence matrix `T_F`, with Perron root `lambda_F > 1` in prime primitive type | Positive edge mass expansion for **every proper ideal multi-interval** |
| §6.1, Prop. 6.5 | For `I` and `closure(I)`, `iota^*I` is the old portion plus complete Carathéodory boundaries of added tree components attached over `I` | A globally continuous, single-valued, monotone prime-end quotient `q` |
| §6.1, Props. 6.6–6.7 | `F_* = f_* iota^*` acts combinatorially, and is proper in the long translation corridor | Injective realization of every exceptional edge and vertex-side lift |
| App. A.1 | Finite/countable ideal markings, open connected multi-intervals, endpoints, and *entire* boundary components | An interval always being proper |
| App. A.3.1–A.3.4 | `f` induces covering action, `iota` induces maximal proper-path restriction, and **`F_* closure(I)` need not equal `closure(F_* I)`** | A pointwise inverse-image formula for arbitrary native prime ends |

In particular, Appendix A.3.2 defines `iota^*I` by a **proper-path universal condition**, not by announcing any pointwise map `q` from the source prime-end circle. In the finite model below, `q` is deliberately *supplied*. The native bridge remains a theorem to prove, not a notation change.

### The native one-step exceptional support is uniformly finite for fixed `b`

Let `L_j`, `j mod q`, be the native limbs and `b>=1` its parabolic occupancy bound. Source Lemma 4.8 proves `ell(L_j)<=6b`. Proposition 6.7 gives properness on the central range

`j = b,b+1,...,q-b-2`, when this range is nonempty.

If `q>=2b+2`, it contains `q-2b-1` limb indices; its complement has `2b+1`. Otherwise the whole set has `q <= 2b+1` indices. Thus the set of indices **not already covered by that properness conclusion** has size at most

\[
\min(q,2b+1),
\]

and its union has combinatorial length at most

\[
6b\min(q,2b+1)\le 6b(2b+1). \tag{2.1}
\]

This is an exact consequence of the source's existing native statements; there is no new native analytic proof hidden in (2.1). The bound counts *marking atoms*, not individual branch attachments or prime ends, and applies to the **one-step exceptional locus**. It does not bound their full pullback genealogy, the number of iterates, a universal `q`-independent surface, or the Wave-width loss. Endpoints straddling proper and nonproper limbs must be checked separately.

## 3. Exact coupled circle presentation

This section is a **finite source-typed model**, not a claim that a KKL immersion is conjugate to it.

Set `M=10`. Let

\[
 C=\mathbb R/(10\mathbb Z),\qquad
 C'=\mathbb R/(20\mathbb Z),\qquad
 p([t]_{20})=[t+5]_{10}. \tag{3.1}
\]

The map `p` is an oriented covering of degree two. Place ten target marking endpoints at the integers and source cuts at

\[
(T_0,\ldots,T_{10})=(0,1,4,5,6,8,13,15,16,17,20). \tag{3.2}
\]

Let `q_0:C' -> C` be the increasing piecewise-linear homeomorphism with lift `q_0(T_i)=i`, affine on each `[T_i,T_{i+1}]`, and `q_0(t+20)=q_0(t)+10`. Every old target atom `I_i=(i,i+1)` has pullback `(T_i,T_{i+1})`.

Define the modeled old interval action by

\[
 \Phi_{q_0}(I)=p(q_0^{-1}(I)). \tag{3.3}
\]

The ten target-word images of the old marking atoms, read in source cyclic order from the *single* `p`, are

```text
0 -> 5
1 -> 6 7 8
2 -> 9
3 -> 0
4 -> 1 2
5 -> 3 4 5 6 7
6 -> 8 9
7 -> 0
8 -> 1
9 -> 2 3 4
```

Their concatenation is `5,6,...,9,0,1,...,9,0,...,4`: exactly two turns. These are the original positive-model words in PR #38, now **generated from one covering and a common endpoint sequence**; the words are not independently selectable after (3.1)–(3.2).

### Derived edge incidence, not an independently chosen matrix

Mark target atoms as follows:

```text
atom:  0  1  2  3  4  5  6  7  8  9
kind:  v  X  Y  v  Z  v  Z  v  Y  X
```

Here `v` has zero edge mass and `X,Y,Z` are typed edge-side atoms. For each source atom of type `X`, count the *target edge types* appearing in its actual generated word; repeat for `Y,Z`. In type order `X,Y,Z`, every source atom of a fixed type gives the same row, and the resulting matrix is

\[
 A=\begin{pmatrix}0&1&1\\1&0&0\\1&1&0\end{pmatrix}. \tag{3.4}
\]

Indeed: the two `X` atoms 1 and 9 each traverse `Y,Z`; the two `Y` atoms 2 and 8 each traverse `X`; and the two `Z` atoms 4 and 6 each traverse `X,Y`. There is **no separate arbitrary matrix input** in the reproducible proof-checking code. With exact rational weights

\[
 w=(3,2,3)^\top,\qquad Aw=(5,3,5)^\top\ge \tfrac32 w, \tag{3.5}
\]

so the positive-edge part has a `3/2` expansion certificate. Direct enumeration of all 100 proper marked interval states shows that each saturates the whole circle, including the four zero-mass singleton vertex sectors. This is a finite consistency test, not a proof that an actual KKL edge map has these words.

## 4. Why the same finite interval dynamics cannot identify attachments

### Theorem 4.1 — finite marked-boundary identifiability fails

Let `p:C' -> C` be a fixed degree-two covering, and let `q_0,q_1:C' -> C` be continuous nondecreasing degree-one maps admitting lifts whose inverse image of every old marked endpoint `j` is the same singleton `{T_j}`. Suppose their source/target periods and the cyclic order of these endpoints agree. Then for *every* open or closed connected multi-interval whose endpoints belong to the old finite marking, and for every whole boundary component,

\[
 q_0^{-1}(I)=q_1^{-1}(I),\qquad
 p(q_0^{-1}(I))=p(q_1^{-1}(I)). \tag{4.1}
\]

The claim includes punctured-circle multi-intervals (all target atoms except one marked endpoint). It does **not** apply to sets with unmarked endpoints or to the whole proper-path restriction relation.

**Proof.** Lift a proper connected old interval to a real interval with endpoints at two integers `s` and `s+k`, `1<=k<=M`. Monotonicity, continuity and *singleton* endpoint fibers imply that its inverse image, open or closed as appropriate, is exactly the real source interval with endpoints at `T_s,T_{s+k}`. Because those endpoint preimages agree for both maps, the inverse intervals agree, including when `k=M` and the interval is the circle with one endpoint removed. For the whole target circle both inverse images are the whole source circle. Applying the same `p` proves (4.1). ∎

### Explicit witness using exactly the model in §3

Keep `p`, `T_i`, and `q_0`. Define `q_1=q_0` outside `[8,13]`, but inside that source interval use the consecutive affine/constant segments

\[
\begin{array}{rcl}
[8,9]&:&5\longrightarrow 11/2,\\
[9,10]&:&11/2\longrightarrow 11/2\quad\text{(constant)},\\
[10,13]&:&11/2\longrightarrow 6.
\end{array} \tag{4.2}
\]

Both are continuous nondecreasing degree-one maps; all ten marked endpoint preimages remain the same singletons. Thus **every old marked open and closed interval has exactly the same source pullback and the same degree-two pushforward**, and the entire word list and edge matrix (3.4) agree.

However,

\[
 q_0^{-1}(11/2)=\{21/2\},\qquad
 q_1^{-1}(11/2)=[9,10]. \tag{4.3}
\]

After applying the *same* degree-two covering,

\[
 p(q_0^{-1}(11/2))=\{11/2\},\qquad
 p(q_1^{-1}(11/2))=[4,5]\quad\text{in }C. \tag{4.4}
\]

So the same finite interval transition program cannot tell whether a nontrivial collapsed fiber exists at this **unmarked interior access**. A finite ribbon picture can interpret such a flat fiber as an attached hair, but (4.2) is **not claimed** to be a holomorphically realized KKL immersion or an actual full preimage tree.

This countermodel proves noninjectivity of the forgetful map

\[
 (p,q,\text{complete interior fiber/access data})
 \longmapsto
 \bigl(\Phi\text{ on old marked multi-intervals},A,w\bigr)
 \tag{4.5}
\]

in this explicit topological circle category. **It does not prove noninjectivity of native KKL's category**, where additional geometric constraints could remove this ambiguity. It does prove that finite transition values, even coherently generated ones, cannot themselves supply the missing geometric theorem.

### Marked-endpoint negative control

An attempted plateau at the *marked* old endpoint `5` is different. Replace `q_0` on `[8,13]` by a map constant `5` on `[8,9]` and strictly increasing to `6` on `[9,13]`. Its fiber over `5` is `[8,9]` and so

\[
 q_2^{-1}((5,6))=(9,13)\ne(8,13)=q_0^{-1}((5,6)). \tag{4.6}
\]

Its target interval word loses one target atom. Hence the **singleton endpoint-fiber hypothesis is necessary** for Theorem 4.1. This test also illustrates why the source's warning about closed-crest endpoint birth cannot be discarded: endpoint-only information and interior attachments answer different questions.

## 5. What remains for a native bridge

The source currently gives the `f_*` covering and the actual `iota^*` **proper-path relation** (plus its tree-attachment formula); the example above gives an explicit circular coordinate construction for a *synthetic* relation. These are not interchangeable.

A promotable native theorem must supply the following **joint** certificate for the *actual* KKL stage. It can use direct path/subordination data instead of a global monotone `q` if that is all the analytic category supports.

1. **Actual boundary identification:** specify actual source and target prime-end circles, the covering `p=f_*`, an orientation-compatible complete access chart for `iota^*`, and exact transport for each proof-used **open and closed** interval. Explicitly identify which prime-end impressions represent native vertices, old sides and attached preimage components; do not use an unproved global quotient `q`.
2. **Attachment completeness/provenance:** for every added component `X` of `T'\setminus T`, list both attachment-side accesses and its full Carathéodory boundary, verify the proper-path quantifiers in Proposition 6.5, and preserve each piece in the native interval pullback. A finite cyclic word with no attachment tags is insufficient by Theorem 4.1.
3. **Shared edge-incidence realization:** derive each target-edge traversal row from **the same actual covering/restriction diagram** used for the ideal interval action. Show that repeated traversals and their side orientations agree with the source `T_F`; if an image is proper, explain why target edge-side mass is counted without cancellation or loss. Only then infer a positive-edge inequality.
4. **Zero-mass gate escape:** construct the actual distinct prime-end gates at all `K_j`, establish their local degree-one/degree-two maps and missing-preimage attachment rule, and rule out periodic proper zero-mass sectors in the actual (including non-locally-connected) setting. A graph valence or a landing point does not automatically identify the number of prime-end accesses.
5. **Native Wave interface:** check actual closed-crest transport, properness, positive length and the `I_{j+1} superset F_*^{m_j} I_j` relation with unchanged markings. The source expressly warns that `F_* closure(I)` may differ from `closure(F_*I)`.

Propositions 6.5–6.7 and Lemma 4.8 provide substantial native inputs to (1)–(5), particularly central-corridor no-birth. Neither the general compactification nor the non-locally-connected boundary fibers can be inferred from a finite cyclic automaton. The **first remaining mathematical obligation** is therefore a source-faithful native `iota^*` access/fiber atlas (or a direct complete proper-path relation) *coupled* to `T_F` at the finitely many exceptional limbs, with their endpoint conditions. The number of exceptional limb indices is uniformly bounded by (2.1), but the missing proof is not merely finite arithmetic.

## 6. Reproduction and trust boundary

Run from the repository root:

```sh
python research/independent_audits/verify_native_boundary_bridge.py --check-manifest
```

The dependency-free checker uses only exact integers and `fractions.Fraction`. It regenerates [`results/native_boundary_bridge_20261106.json`](../../results/native_boundary_bridge_20261106.json) byte-for-byte and checks:

- the common degree-two covering, two degree-one monotone quotients, common old marked endpoint fibers and one genuine unmarked flat fiber;
- every one of the `10*10=100` old proper interval states (including punctured circles), exact open/closed inverse membership on both piecewise-linear quotients at every joint knot and midpoint, source cut lengths, cover-derived cyclic words and a missing-mark-endpoint negative control;
- the **typed `3x3` edge matrix derived from those exact words**, exact `3/2` edge-weight inequalities, non-repetition of proper intervals, and a tampered-row failure;
- the unmarked-access fiber difference after pushforward;
- the one-step native exceptional-limb count arithmetic for `b=1,...,50` and `q=2,...,200`.

The symbolic theorem proofs above concern continuous monotone maps and finite source/target circles; a finite integer test is not a proof of their analytic realization. The script does not run Lean, construct actual KKL surfaces, compute a native Carathéodory impression, or resolve any global MLC gate. AI materially assisted proof analysis and implementation; no independent human specialist review or claim of priority is made.

**Promotion decision:** retain the new exact coupled-certificate and nonidentifiability results as finite/topological mathematics. **Do not mark native interval growth or the MLC chain proved.**
