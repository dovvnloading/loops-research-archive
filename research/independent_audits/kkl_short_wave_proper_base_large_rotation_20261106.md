# Issue #40 — SHORT-WAVE BASE LOCALIZATION: no full-circle base at large rotation

**Date:** 2026-11-06.  
**Status:** a new **native Carathéodory topology theorem**. In the original KKL vertex-side marking, once the rotational limb number is large compared with the parabolic bound, **every short Wave has a proper supporting base**. It eliminates the entire full-circle/two-component crest case from the **short critical-visit** branch of the proof, regardless of whether the two source minimal end intervals are disjoint or overlap, and without local connectivity. This is **not** the remaining non-return dual-WAD theorem or global Wave amplification.

**Primary source:** Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §2.4–2.5 (the \(q\) actual limbs and the complete Hubbard carrier), §6 opening paragraph (the **original** marking \(\mathcal I\) from sides of the vertex package), §6 before Proposition 6.2 (a Wave is **short** when no leaf crests over a limb; the two minimal end lengths satisfy \(\ell(E_\pm)<12\mathbf b\)), and Appendix A.1 (proper marked paths, Wave base/end/crest, the two-atom restriction). Source v1 is fixed throughout.

## 1. A topological cut lemma on the actual annular carrier

Let \(V=\mathcal U\setminus\mathcal T\) be the **actual** annular complement in one native KKL stage and \(C=\partial_C^{\mathrm{in}}V\) its real prime-end circle. Let the original finite marking \(\mathcal I\) be subdivided into \(q\) distinguished, cyclically ordered **limb blocks** \(\mathbf L_0,\ldots,\mathbf L_{q-1}\). Each block contains at least one full original marked atom (from the small Julia cycle), and an atom lies in **at most one** limb block. Vertex-side atoms in central sectors not part of any limb are allowed and do not weaken the following count.

The only limb-marking property used below is

\[
\text{a union of }k\text{ full original marking atoms
 meets the interiors of at most }k\text{ limb blocks.}
\tag{1.1}
\]

**Source verification of (1.1).** KKL §4, proof of Lemma 4.8 (around its equation (4.10)), explicitly identifies every atom of \(\mathbf L_j\) with a **side of an edge or vertex other than \(\alpha_F\)** in the limb hull \(\mathcal G_j\). Distinct limb hulls lie in disjoint components of \(\mathcal T\setminus\{\alpha_F\}\); hence one such edge/vertex-side atom cannot belong to two *different* \(\mathbf L_j\) interiors. Each limb contains at least one small filled Julia vertex, so its boundary has a nonempty atom. This verifies the injection/count property **for the standard full KKL marking** even in the non-LC case insofar as §2.5 transports this graph-side combinatorics by its model lift. It does **not** identify individual prime-end impressions. For a *nonstandard* induced/refined marking, (1.1) remains an explicit stage-specific assumption and must not be inferred from graph valence alone.

### Lemma 1.1 (missed-limb cut)

Let \(\mathcal F\) be any actual lamination by **simple** proper paths with both ends on \(C\). Suppose there is one entire nondegenerate limb multi-interval \(L\subset C\) containing **no leaf endpoint**, and **no leaf of \(\mathcal F\) crests over \(L\)** in KKL's Appendix A.1/§6 sense. Then there is a *single* original marked cut \(e\in\overline L\) such that **every leaf of \(\mathcal F\)** is subordinate to the proper connected marked multi-interval

\[
\boxed{B_e=C\setminus\{e\}.}
\tag{1.2}
\]

In particular the whole lamination admits a **proper** base, independently of whether its support is connected or split into many homotopy packets.

**Proof.** A simple proper arc with both ends on the **same inner boundary component** of a topological annulus is boundary-parallel to one of the two **proper** boundary arcs joining its endpoints. This is the standard annular arc lemma: in the infinite-strip universal cover a lift of a simple arc cannot intersect any nontrivial deck translate. If its lifted endpoint had winding number outside the two alternatives \(0,-1\) relative to the endpoint lifts, that arc and an adjacent translate would have **alternating endpoints** on the same strip boundary line, forcing an intersection by Jordan separation. Therefore every such leaf has a unique, proper homotopy support subarc \(J_\gamma\subsetneq C\).

The **whole** limb \(L\) is disjoint from the endpoints of \(\gamma\). A connected simple boundary subarc \(J_\gamma\) from one endpoint of \(\gamma\) to the other has the following elementary dichotomy: its interior either avoids the interior of \(L\), or contains **all of** \(L\) (a subarc cannot enter and leave an interval of the circle without crossing both its boundary cuts, unless its own endpoint lies in that interval). In the second case the leaf's **crest**, its support subarc minus the two endpoint atoms, includes the entire limb \(L\), contradicting the no-crest assumption. Thus **every** \(J_\gamma\) avoids the interior of \(L\).

Choose a marked endpoint cut \(e\) at either boundary of \(L\), or a marking cut strictly inside the limb if it has more than one marked atom. Since no support subarc can include this cut without entering the limb while both of its endpoints lie outside, all \(J_\gamma\) avoid the **same** \(e\). Hence all leaves are subordinate to \(C\setminus\{e\}\), a proper connected **open** multi-interval in the original marking (the punctured inner circle), proving (1.2). No pointwise Carathéodory landing map or global \(\iota\)-boundary quotient was used. \(\square\)

**Boundary check:** The argument uses actual *simple* marked paths (not arbitrary immersed paths), and the original marked endpoint cuts. It holds when the Julia continuum is **non-locally-connected**, since only the real annular prime-end circle and its universal-cover order enter.

## 2. Main theorem — short Waves have proper bases for sufficiently large q

Let \(A\) be a **genuine KKL short Wave** with source-assigned (or explicitly tagged) minimal connected end multi-intervals \(E_-,E_+\). Their **source shortness consequence** (KKL §6 just before Proposition 6.2) is

\[
\ell(E_-)<12\mathbf b,\qquad\ell(E_+)<12\mathbf b.
\tag{2.1}
\]

### Theorem 2.1 (native large-rotation short-Wave proper-base theorem)

Assume the source original limb marking property (1.1). If

\[
\boxed{q\ge24\mathbf b,}
\tag{2.2}
\]

then **every** genuine KKL short Wave \(A\) admits a **proper connected** marked supporting base \(B\subsetneq C\). More strongly, **every inclusion-minimal source-compatible base tag** of \(A\) is proper. Consequently, **no genuinely short Wave at such a stage has the full inner prime-end circle as its minimal base**.

This applies whether the end intervals are disjoint, overlapping, or share marked cuts, and without any local-connectivity assumption.

**Proof.** Both end lengths are integers, so (2.1) implies

\[
\ell(E_-)+\ell(E_+)\le24\mathbf b-2<q.
\tag{2.3}
\]

Every leaf has one endpoint in \(E_-\), one in \(E_+\). By the limb-marking injection/count property (1.1), the union \(E_-\cup E_+\) meets the interior of **at most** \(\ell(E_-)+\ell(E_+)\) distinct full limb blocks. Since that number is **strictly below** \(q\), some entire limb \(L=\mathbf L_j\) contains no leaf endpoint.

Because \(A\) is short by definition, **no** leaf crests over that limb. Lemma 1.1 therefore gives one original marked cut \(e\) and a **single proper** connected base \(B_e=C\setminus\{e\}\) supporting **all** leaves. Thus the full circle is not a minimal supporting base, and no inclusion-minimal base tag can be \(C\). \(\square\)

**Threshold:** The proof works with \(q>\ell(E_-)+\ell(E_+)\). Under (2.1), the slightly better integral sufficient condition is \(q\ge24\mathbf b-1\). We record the cleaner \(q\ge24\mathbf b\), which is stable under usual endpoint-count conventions. This is **an actual stage-relative theorem**, not a universal \(q\)-independent constant.

### Corollary 2.2 (actual short critical crests are regular positive, if nonempty)

Assume \(q\ge24\mathbf b\), and suppose a genuine short Wave \(A\) has **a specified** inclusion-minimal base \(B_A\) and minimal end pair \(E_\pm\) in the source sense, with a **nonempty crest** \(C_A\). Then:

1. Theorem 2.1 forces the **specified minimal base to be proper**.
2. The companion [native noncrossing theorem](./kkl_wave_nonempty_crest_noncrossing_20261106.md), Theorem 2.1, proves that a nonempty proper-base crest is one **closed regular positive** marked interval:
   \[
   \boxed{
   C_A=\overline{J_A},\qquad
   J_A=\operatorname{Int}C_A\ \text{connected open marked},\quad
   \ell(J_A)=\ell(C_A)\ge1.
   }
   \tag{2.4}
   \]
3. Therefore the old **full-base two-component/isolated-endpoint crest problem is absent** throughout the short-Wave critical-visit part of the proof at this large rotation. It is **not necessary** there to introduce a disconnected extension of \(F_*\) just to propagate crests.

**Proof.** Theorem 2.1 gives a proper base for the source-tagged Wave, and properness of every minimal tag. Apply the companion noncrossing theorem to the specified minimal end/base data. Its proof uses only the no-two-atom-path condition and Jordan crossing on the actual annular cover. \(\square\)

**Careful domain:** The source's **critical visit** is a short Wave over the actual closed image of a previous crest. Corollary 2.2 does **not** prove all those closed images are well typed, nor guarantee a previous Wave has a **nonempty** crest or a critical visit exists. It proves that *once such a genuine short critical Wave and nonempty source-compatible crest have been selected*, the crest is regular positive without an additional full-base or zero-core hypothesis.

## 3. Why this is stronger than the earlier 24b full-base positive-atom result

The previous [noncrossing note](./kkl_wave_nonempty_crest_noncrossing_20261106.md), Theorem 3.1, only showed that a short Wave whose base was the **full circle** must have a positive-atom crest when the original marking has at least \(24\mathbf b\) atoms, leaving a **two-component** possibility. The present theorem shows that, under the actual **q-limb marking separation** and \(q\ge24\mathbf b\), the **full circle cannot be a minimal base at all**. It removes the two-component case rather than just ensuring it contains an atom.

The previous [two-component deck-collision theorem](./kkl_two_component_wave_deck_collision_20261106.md) remains correct as a general actual annular double-cover identity and as a necessary diagnostic for full-base laminations **outside** the large-q short class. It is no longer the **first** Wave-crest gate in the central large-q short critical-visit regime.

The [two-winding packet normal form](./kkl_annular_wave_two_packet_normal_form_20261106.md) independently decomposes any actual lamination with disjoint end tags into at most two proper-base homotopy packets and conserves their induced WAD norm exactly; Theorem 2.1 applies even to **overlapping** ends and needs **no packet splitting or width loss**.

## 4. The true remaining bottleneck

At high rotation \(q\ge24\mathbf b\), the following previously open assumptions become **source-derived geometry**, subject only to the actual end-tag and marked-limb hypotheses:

- a genuine short critical Wave has a proper minimal base;
- its nonempty crest is a single regular positive marked interval;
- the existing **open-core transport theorem** (from [the dual-WAD note](./kkl_dual_arc_wave_core_reduction_20261106.md), Theorem 4.2) applies without assuming any false equality \(F_*\overline J=\overline{F_*J}\), *provided the source-defined closed-crest inclusion is well typed*.

Thus the **central bounded-visits obstacle** is now even more concentrated: for any hypothetical proper original marked interval whose orbit **returns to the critical limb through a full marked atom**, produce one **nonzero source-defined dual bivertical/WAD witness** with the correct domination direction (or prove nonreturn by a different native geometric argument). Separately verify that “intersects critical limb” in the source's critical-visit definition implies a **full-atom** encounter for the open core: endpoint-only intersection cannot be counted without a separate gate check.

This is a **large-q original-native-category** reduction, not a synthetic interval simulation. It uses no global monotone \(\iota^*\) boundary map, no LC assumption, and no artificial finite transition matrix.

**Status / ledger:** The new proper-base and corollary are concrete geometric theorems subject to independent specialist review. They do NOT prove the missing critical-return dual witness, original closed crest transport on arbitrary accesses, KKL Lemma 6.4, global Wave amplification or MLC. **Keep Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION and MLC OPEN.**
