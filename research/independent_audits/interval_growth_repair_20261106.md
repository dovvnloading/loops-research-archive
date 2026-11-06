# Interval growth: a literal counterexample and a marked-contour repair

**Date:** 2026-11-06  
**Target:** `KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR`  
**Repository review base:** `385f28da0f58538b665fa5d1b19448d327d10018`  
**Status:** partial repair, with complete proofs in the stated finite marked-contour category. **The original native analytic obligation stays open.**

## 1. Outcome and exact scope

This note supplies more than the corrected pigeonhole count. It proves an interval-level nonperiodicity mechanism for finite saturated ribbon-contour systems, including the zero-edge-weight case that Perron–Frobenius expansion does not detect. It then proves a critical-visit bound allowing variable iterate times and enlargement between visits.

There are three different conclusions:

* **Literal negative result:** KKL v1 Proposition 6.9, quantified over every multi-interval, admits the whole boundary circle as a counterexample under the definitions in Appendix A.1. This is an endpoint-of-scope correction, not a refutation of the intended short-wave lemma or the paper's main theorems.
* **Proved finite theorem:** for the saturated marked-contour systems specified below, proper intervals cannot be periodic. A proper interval of length `k` must grow after `6b+k` critical encounters unless its image has already become the whole boundary. A short critical-enlargement chain has at most `(12b-1)^2` states.
* **Unresolved application:** the complete passage from the actual native KKL prime-end operation to this multiplicity- and attachment-faithful contour system has not been certified here for the full native class, particularly the non-locally-connected case. A locally connected combinatorial quotient, an edge matrix, or a diagram alone does not certify that passage.

No global ledger status changes are proposed. This is not a proof of MLC, the full Wave amplification theorem, a virtual carrier theorem, or an all-scale transport theorem. The finite regression is not a realization of a polynomial or a KKL wave. No independent human specialist review or Lean formalization is claimed.

## 2. Source and version boundary

The source is Jeremy Kahn, Alex Kapiamba and Mikhail Lyubich, *MLC for parabolically bounded primitive renormalization*, arXiv:2606.27272v1:

- [Versioned HTML](https://arxiv.org/html/2606.27272v1).
- [Versioned PDF](https://arxiv.org/pdf/2606.27272v1).
- The archive's source-facing gap is recorded in [direct_decoration_wave_proof_use_ledger.md, §3.2](../mlc_unified/direct_decoration_wave_proof_use_ledger.md#32-conditional-arithmetic-after-a-growth-lemma).
- The native/full-cycle scope and the warning against arbitrary virtual lifts are recorded in [terminal_hubbard_anchor.md](../mlc_unified/terminal_hubbard_anchor.md).

The relevant source locations are §2.5 (native tree, incidence operator and combinatorial model), Lemma 4.8 (limb length), §6.1 / Propositions 6.5–6.6 (saturated interval pullback and marking), Proposition 6.9 and the following proof of Lemma 6.4 (printed p. 44), and Appendices A.1 and A.3.4 (multi-intervals, crests, and endpoint-sensitive dynamics). Rendered PDF pages were inspected for the definitions and the target proof. Source claims are not silently strengthened to a new physical prime-end identification.

Notation here is independently normalized: `A` is a **row-source** edge-incidence matrix; `Phi` is the boundary interval operation, not a map on physical points. The exact source correspondence under review is `Phi = f_* iota^*`.

## 3. A counterexample to the literal unrestricted statement

Let `C` be the entire inner Carathéodory boundary of the native tree, with `M` marking atoms. Appendix A.1 permits an entire boundary component as a multi-interval. The complete boundary satisfies

\[
\Phi(C)=C,\qquad \ell(C)=M.
\]

It intersects the critical limb at every time. Set `n=6b+M-1`. There are `n+1=6b+M` distinct times in `[0,n]`, all critical encounters, but

\[
\ell(\Phi^n C)=M=\ell(C).
\]

Thus Proposition 6.9 as literally universally quantified cannot hold. The appropriate conclusion is **growth or full-boundary saturation**, or equivalently growth under the additional assumption that the final image is proper. A whole-boundary crest cannot be contained in a nonempty short wave's proper crest, so this correction is compatible with the intended application; it does not itself prove that application.

A second endpoint distinction is indispensable. On a circle with `M` atoms, a proper open interval containing all `M` atoms is the circle minus one marked point. There are `M` such intervals. None is the whole circle, and different missing points give different states even though their atom sets coincide.

## 4. The exact count and a finite dynamical theorem

Fix an oriented circle `C` subdivided by `M >= 2` marked points into open atoms. A nonempty proper open multi-interval is determined by a starting atom `s` and length `1 <= k <= M`; when `k=M` the marked point immediately preceding `s` is omitted. Let `L` be a proper run of `r` consecutive atoms.

### Lemma 4.1 — exact critical-state count

The number of proper length-`k` open multi-intervals meeting `L` is

\[
\min(M,r+k-1).
\tag{4.1}
\]

**Proof.** Rotate labels so `L` has atoms `0,...,r-1`. A length-`k` interval meets it precisely when its start lies among `-(k-1),...,-1,0,...,r-1`, interpreted modulo `M`. This consecutive string has `r+k-1` entries and gives exactly `min(M,r+k-1)` residues. Open-set intersection here agrees with having a common atom: a nonempty intersection of two open multi-intervals contains an atom. The argument includes `k=M`, with the missing endpoint retained. ∎

In particular, `r <= 6b` gives **at most `6b+k-1` states**. Therefore `6b+k` encounters give a strict pigeonhole excess. Equality of counts is not enough.

For the next theorem assume `Phi` is a deterministic, inclusion-monotone operation on these intervals and the full circle, with:

1. `Phi(C)=C`;
2. if `Phi(I)` is proper, then `ell(Phi(I)) >= ell(I)`;
3. no nonempty proper interval is periodic under `Phi`.

Section 5–6 gives a non-circular sufficient mechanism for property 3; it is not inferred from a global spectral radius alone.

### Theorem 4.2 — corrected interval growth

Let `I` be nonempty, `n>=1`, and `k=ell(I)`. If at least `6b+k` distinct times `0<=m<=n` satisfy `Phi^m(I) intersect L != empty`, then

\[
\Phi^n(I)=C
\quad\text{or}\quad
\ell(\Phi^n(I))>\ell(I).
\tag{4.2}
\]

**Proof.** Suppose the final image is proper and has length at most `k`. No previous image is the full circle because the full circle is absorbing. Monotonicity of length forces every intermediate length to equal `k`. Lemma 4.1 gives distinct encounter times `m_s<m_t` with `Phi^{m_s}(I)=Phi^{m_t}(I)`. This is a periodic proper state, contrary to property 3. ∎

The repeated states are indexed by the actual encounter times `m_s,m_t`, not by their positions `s,t` in the list of encounters.

## 5. A sufficient marked-contour realization package

The following finite category is more restrictive than a bare transition matrix. It makes every input to the proposed native repair explicit.

**Contour geometry.** A finite ribbon tree has a cycle of distinguished nondegenerate vertex bodies `K_0,...,K_{p-1}`, `p>1`, and possibly singleton junction vertices. Its contour marking consists of the two sides of each edge and the nonempty boundary sectors of the `K_j`. Singleton junctions contribute endpoints, not positive-length atoms. The tree is the minimal hull of the distinguished vertices, so a leaf is a `K_j` and has one attachment access. Distinct vertex sectors are separated by edge-side atoms.

**Complete pullback.** The source tree `T'` contains the old tree and is a complete preimage of the target tree under an orientation-preserving degree-two map. Added branches attach to the old tree without forming loops. Saturating a contour interval inserts the complete contour of each branch attached in its interior. The target boundary map is an orientation-preserving covering. The marked source intervals refine into full target-atom lifts.

**Edge multiplicities.** With rows indexed by source edges and columns by target edges, `A[e,e']` counts all target-edge traversals in the image of edge `e`. There is a positive vector `w` and `lambda>1` such that `Aw >= lambda w`. A primitive incidence matrix with Perron root greater than one supplies such a vector, but the boundary realization of its traversals is separately required.

**Vertex gates.** For each distinguished vertex, let `E_j` be its finite nonempty set of distinct external attachment accesses on its own boundary circle. Count accesses, not merely physical attachment points or abstract valences. The local boundary maps

\[
g_j:C_j\longrightarrow C_{j+1}
\]

have degree one except `g_0`, which has degree two, and satisfy `g_j(E_j) subset E_{j+1}`. A missing preimage gate in a vertex sector — a point in `g_j^{-1}(E_{j+1}) minus E_j` — inserts a complete edge-side contour under saturation. Thus that sector's next image contains an edge atom or is the whole contour. A vertex sector with no edge in its proper image maps into a sector at the next distinguished vertex.

These requirements hold in the geometrically realized ribbon systems just described: a missing preimage of an attachment is exactly an additional branch in the complete preimage tree. A complete lifted edge begins there. Minimality and acyclicity prevent that branch from secretly reconnecting elsewhere to the old tree. They are also explicit acceptance conditions for any application to actual native prime-end data. They are **not** asserted for arbitrary compressed, partially selected or quotient states.

### Lemma 5.1 — no wrapping while the image is proper

On a saturated interval whose target image is proper, the oriented boundary covering is injective. A lift to the universal covers of the boundary circles is strictly increasing. If its image contains more than one full turn, the image on the target circle is the entire circle. Exactly one turn with its two endpoints omitted gives a punctured circle and is still injective. Therefore distinct refined source atoms have distinct target atoms while the result is proper. In particular length cannot decrease. ∎

This statement is about the complete saturated boundary interval, not just its selected core edge; omitting the inserted branches invalidates the argument.

### Lemma 5.2 — the edge-weight bridge

Assign an edge-side atom the weight `w_e` of its underlying edge and a vertex-side atom weight zero. Let `mu(I)` be the sum over atoms contained in `I`. For a proper image,

\[
\mu(\Phi I)\geq\lambda\mu(I).
\tag{5.1}
\]

**Proof.** Each side of an old edge has, along its saturated source contour, the full traversals counted by the corresponding row of `A`. This can be checked by choosing a midpoint on each target edge: each traversal gives the appropriate side of one complete lifted edge. Branches inserted between old edge pieces add nonnegative contributions. By Lemma 5.1 no target side can be counted twice while the target interval is proper. Hence an old edge side contributes at least `sum_{e'} A[e,e'] w_{e'} >= lambda w_e`; summing gives (5.1). ∎

This is the missing *kind* of bridge in the phrase “contradicts `lambda_F>1`.” The source incidence matrix by itself is not (5.1).

## 6. The zero-weight case is not optional

An interval of weight zero consists of a single vertex sector. Expansion of edge weights says nothing about it. We now prove eventual escape from this case using the gate data, rather than assuming it.

Write `a_j=|E_j|`. Noncritical local degree one and forward invariance of gates give

\[
a_1\leq a_2\leq\cdots\leq a_{p-1}\leq a_0,
\qquad a_0\leq 2a_1.
\tag{6.1}
\]

A leaf distinguished vertex has one gate. Thus the smallest count `a_1` equals one, and every `a_j` is either one or two.

### Lemma 6.1 — vertex-sector escape

A vertex-sector orbit acquires an edge-side atom or saturates the whole boundary in at most `2p` steps.

**Proof.** If `a_0=1`, all gate counts are one. At the critical transition the single target gate has two distinct preimages, but only one is an old source gate. The other lies in the unique source sector and inserts an edge side. Every vertex-only orbit reaches that transition within one cycle.

If `a_0=2`, there is a first noncritical increase from one gate to two while following `K_1,K_2,...,K_0`. At that step the local circle map is a homeomorphism. Exactly one of the two target gates has a new preimage, in the unique source sector, and so an edge side is inserted. Unless an edge has already appeared, an arbitrary starting sector reaches `K_1` within one cycle; from its unique sector it reaches the first increase within the next cycle. ∎

Using gate counts is essential. Two tree branches at one physical landing point need not define two distinct prime-end attachment sites. A proof that counts branch valence as if it automatically counted boundary sites is not this proof.

### Theorem 6.2 — no proper periodic contour interval

A saturated contour system satisfying Section 5 has no nonempty proper periodic interval.

**Proof.** A periodic proper orbit stays proper. If `mu(I)>0`, iterating (5.1) around a period `q>=1` gives `mu(I)>=lambda^q mu(I)`, a contradiction. If `mu(I)=0`, Lemma 6.1 produces positive weight or saturation. Saturation is incompatible with a proper periodic orbit. Positive weight is incompatible with subsequently returning to weight zero by (5.1). ∎

### A negative control for the missing hypothesis

Take a three-atom circle with the following positively ordered substitution words:

```text
0 -> (0)
1 -> (1,2)
2 -> (0,1,2).
```

Their concatenation is two complete turns, so this defines a degree-two contour covering. Give the atoms weights `(0,1,1)`. Every proper image satisfies `mu(Phi I)>=2 mu(I)`, yet the proper zero-weight atom `0` is fixed. Thus orientation, degree two, and strict positive-edge expansion do not imply proper-interval nonperiodicity. This example fails the vertex-gate escape package. It is an abstract logical countermodel, not a claimed native KKL counterexample.

## 7. Variable-time visits and a stronger finite bound

Let `J_1,...,J_t` be nonempty proper open intervals, each meeting `L`, each of length at most `K`, and suppose

\[
\Phi^{m_j}(J_j)\subset J_{j+1},\qquad m_j\geq1.
\tag{7.1}
\]

For a system satisfying Theorem 6.2, the lengths are nondecreasing. On any constant-length plateau, every intervening image stays proper and (7.1) must be an equality: two proper open intervals of the same number of consecutive atoms cannot be strictly nested. This includes punctured-circle states, whose missing endpoint is retained. A repeated state in a plateau would give a proper periodic interval, so no state repeats there. Lemma 4.1 yields

\[
t\leq\sum_{k=1}^{K}\min(M,r+k-1)
 \leq\sum_{k=1}^{K}(6b+k-1).
\tag{7.2}
\]

Taking `K=12b-1` gives

\[
\boxed{t\leq(12b-1)^2.}
\tag{7.3}
\]

For a wave chain `A_1,...,A_N`, only `A_2,...,A_N` are automatically critical visits and short. Therefore the derived forbidden chain length is

\[
N=(12b-1)^2+2.
\tag{7.4}
\]

In particular `N=216b^2` remains sufficient, since for `b>=1`

\[
216b^2-1-(12b-1)^2=72b^2+24b-2>0.
\]

There is no claim that (7.4) is sharp.

### Closed crests and endpoint births

This chain argument does **not** assume `Phi(closure I)=closure(Phi I)`. The source explicitly warns against that equality. For closed crests `C_j` with nonempty multi-interval interiors, use `J_j=int C_j`. Monotonicity gives

\[
\Phi^{m_j}(J_j)\subset\Phi^{m_j}(C_j)\subset C_{j+1}.
\]

The left side is open and hence belongs to `int C_{j+1}`. A positive-length closed crest meeting the open critical limb has an interior atom meeting it. These facts give (7.1) without deleting endpoint-born additions from the actual closed-crest operation. Positivity, properness and the source shortness bound for the actual crests must be checked at application time; zero-length or arbitrary disconnected families are not covered by this theorem.

## 8. The exact remaining native acceptance test

The combinatorial result is not being substituted for an analytic realization theorem. To promote the original ledger obligation, supply one explicit identification of the actual native KKL operation with Section 5, verifying:

1. **Actual contour and multiplicities:** the ideal edge-side atoms and their complete saturated images carry every traversal counted by the row-source incidence matrix. No sheet, attachment contour or repeated side is silently discarded.
2. **Vertex gates:** actual prime-end attachment sites are finite, have the stated degree-one/degree-two circle maps, and a missing inverse attachment really inserts an entire edge-side atom into the specified `iota^*` interval.
3. **Native/non-LC scope:** the above identification applies to the physical boundary used by the wave, not only a locally connected rational-lamination quotient. The phrase “lift corresponding objects” does not alone prove a commuting boundary identification with these properties.
4. **Actual wave crests:** they are nonempty proper intervals of the required length, and successive critical visits give the inclusion used in Section 7 with the same markings and endpoints.

Sections 5–6 suggest how to construct this identification for an explicitly realized finite ribbon neighborhood. They do not provide a general non-LC physical realization. This is the precise remaining obstruction; it is not the counting calculation or the abstract Perron–Frobenius argument anymore.

A successful review may establish that already imported native results license all four items, or produce a new proof of the missing items. Until then, `KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR` remains open. Other stationary Wave extraction and width arguments remain separate even after this target is closed.

## 9. Executable verification and its limits

Run:

```sh
python research/independent_audits/verify_interval_growth_repair.py --check-manifest
```

The companion [manifest](../../results/interval_growth_repair_20261106.json) is deterministically regenerated using integers and rational arithmetic. The checker verifies:

- the count `min(M,r+k-1)` for all 10,912 triples with `2<=M<=32`, `1<=r<M`, `1<=k<=M`, with cyclic rotation reducing the start of the critical run to zero;
- all 100 proper states of a ten-atom abstract degree-two contour, including every punctured-circle state; every orbit saturates in at most five steps;
- all 1,003 admissible positive-time/enlargement transitions in its critical-state graph, which is acyclic and has maximum chain length four;
- a rational expansion certificate with edge weights `(3,2,3)` and factor `3/2`, with no floating-point eigenvalue computation;
- the invariant zero-weight negative control, normalized finite gate-count patterns, and the bound arithmetic for `1<=b<=1000`.

The all-parameter results are the written lemmas above, not the finite tests. The ten-atom example is deliberately not advertised as a certified polynomial, a source-defined KL sheet model, or an analytic wave. The regression exercises the proof's endpoint, multiplicity and zero-weight distinctions.

## 10. Attribution and promotion decision

The source interval dynamics, native tree and Wave architecture belong to Kahn–Kapiamba–Lyubich and their cited predecessors. The contribution of this pass is the explicit unrestricted-boundary counterexample, the endpoint-correct count, the saturated contour/edge-mass and zero-sector repair mechanism, the enlargement-chain estimate, and reproducible adversarial checks. Novelty or priority beyond this archive is not established.

OpenAI GPT-6 Astra Pro assisted source comparison, proof development, counterexample construction, code and exposition. The mathematical arguments remain proposed research for specialist review, not externally refereed results.

**Decision:** record the partial repair and exact surviving native identification obligation; do not mark the original gate, the Wave theorem, H1–H4, UPTCR or MLC proved.
