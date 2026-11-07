# Issue #40 — a TWO-PACKET NORMAL FORM for actual annular Waves with disjoint ends

**Date:** 2026-11-06.  
**Status:** a new topology-and-WAD **repair theorem** for the actual KKL marked annulus, requiring **no local connectivity** and no invented transition matrix. It resolves the ambiguous-base problem at the level of **arc-homotopy packets** whenever the two source-tagged end intervals are disjoint. It proves an exact **two-term WAD norm decomposition** and an explicit genuine **full-base Wave** exhibiting both winding packets. The scalar conformal width comparison needed by the full Wave amplification argument is **separately typed and NOT claimed unless its Parallel Law/normalization is verified**. The general overlapping-end category, native \(\iota^*\) transport, and dual critical-return witness remain open.

**Primary source:** Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), Appendix A.1 (actual marked path admissibility, Waves, bases and ends); A.2.2 (induced WAD, weight of each arc class, additive norm \(\|W\|=\sum_\alpha W(\alpha)\)); §§4 and 6 (actual Hubbard carrier complement and vertex-side marking). Companion: [real Wave-base nonuniqueness](./kkl_native_wave_base_nonuniqueness_20261106.md), [specified-base noncrossing crest theorem](./kkl_wave_nonempty_crest_noncrossing_20261106.md), [two-component deck-collision theorem](./kkl_two_component_wave_deck_collision_20261106.md). All assertions are about the **actual annular prime-end surface**, not the combinatorial rational-lamination model.

## 1. Genuine annular setting and the two windings

Let \(V=\mathcal U\setminus\mathcal T\) be an actual KKL annular carrier complement, with inner ideal boundary circle \(C=\partial_C^{\mathrm{in}}V\). Let \(\mathcal I\) be its actual finite vertex-side ideal marking. No assumption is made that individual prime-end impressions are singleton planar points.

Let \(A\) be a nonempty **actual lamination of simple marked proper paths**, with a **specified** source-compatible pair of **disjoint connected open end multi-intervals**

\[
E_-,E_+\subset C,\qquad E_-\cap E_+=\varnothing,
\tag{1.1}
\]

such that each leaf has exactly one endpoint in \(E_-\) and the other in \(E_+\). This disjoint-end condition is part of this theorem's **domain**, not asserted for every Wave in the source. A leaf is admissible only if it is **not subordinate to any connected marked multi-interval of length at most two** (KKL Appendix A.1).

Choose a lift of the circular order to \(\mathbb R\), normalized so that the lifted end intervals satisfy

\[
\widetilde E_-=(a,b),\quad
\widetilde E_+=(c,d),\qquad
a<b<c<d<a+1.
\tag{1.2}
\]

The two directed complementary gaps between these ends are \(G_0=(b,c)\) and \(G_1=(d,a+1)\). The annulus's universal cover is a strip whose *inner boundary* is \(\mathbb R\), with deck translation \(T(t)=t+1\).

For each actual simple leaf \(\gamma\), orient it from \(E_-\) to \(E_+\), choose its lift beginning at \(x\in(a,b)\), and let its other endpoint be \(y+n\) with \(y\in(c,d)\) and \(n\in\mathbb Z\). The integer \(n\) is the **relative winding**, determined by the *real homotopy class* and the selected end lifts.

### Lemma 1.1 (a simple inner-to-inner annular arc has **only two** possible relative windings)

\[
\boxed{n\in\{0,-1\}.}
\tag{1.3}
\]

**Proof.** If \(n\ge1\), the four endpoint positions of the lifted arc \(\tilde\gamma\) and its positive deck translate \(T\tilde\gamma\) satisfy

\[
x<x+1<y+n<y+n+1.
\]

The two lifted proper arcs therefore have **alternating** endpoints on the same boundary line of a simply connected strip. The Jordan crosscut separation theorem forces them to intersect. But the lift of an **embedded** path in the annulus cannot intersect a nontrivial deck translate: otherwise its projection self-intersects. Contradiction.

If \(n\le-2\), compare \(\tilde\gamma\) and \(T\tilde\gamma\) with their endpoints listed in *increasing* order. Because \(x<y<x+1\), we have

\[
y+n<y+n+1<x<x+1.
\]

Again the endpoint sets alternate and the lifted arcs must intersect, contradicting simplicity. Thus \(-1\le n\le0\), proving (1.3). This argument takes place on the **actual prime-end universal cover** and never uses planar landing of impressions. \(\square\)

**Important correction to common intuition:** the two classes are topological **directions round the inner boundary**, not arbitrary higher Dehn-twist powers. Even if an immersed representative of a class winds several times, it cannot be a **simple** embedded leaf with both endpoints on this one inner boundary component.

## 2. Canonical winding packets and proper bases

For \(\epsilon\in\{0,-1\}\), let

\[
A_\epsilon=\{\gamma\in A: n(\gamma)=\epsilon\}.
\tag{2.1}
\]

These are sublaminations of *actual original leaves*. They are disjoint leaf families and partition \(A\).

### Theorem 2.1 (two-packet Wave normalization, with unique **packet** bases)

For each nonempty \(A_\epsilon\):

1. **Real proper base.** There is a proper connected open multi-interval \(B_\epsilon\subsetneq C\) to which *all leaves of \(A_\epsilon\)* are subordinate, chosen as the **marked convex hull in the corresponding directed boundary arc** of the actual endpoint atoms occupied by the packet. Every leaf is a KKL-admissible marked path, so \(A_\epsilon\) is a **genuine Wave** subordinate to \(B_\epsilon\).
2. **Unique packet-minimal base.** That hull is the unique least proper connected marked base supporting \(A_\epsilon\), *within its fixed winding class*. It is specified by the actual endpoint atoms and the **actual** homotopy direction; no arbitrary choice between the two gaps is made.
3. **Exhaustive decomposition.**
   \[
   \boxed{A=A_0\sqcup A_{-1}.}
   \tag{2.2}
   \]
   One or both packets may be empty. Thus a base-ambiguous disconnected Wave can be **normalized into at most two base-unambiguous Wave packets** in the disjoint-end subclass, with no need to identify individual non-LC prime-end impressions or change the marked path definition.
4. **Exact WAD norm bookkeeping.** Let \(W_A\) be the WAD induced by \(A\), in KKL Appendix A.2.2, and \(W_\epsilon\) those induced by the packets. Since every arc class has a well-defined relative winding,
   \[
   \boxed{
   \|W_A\|=\|W_0\|+\|W_{-1}\|,
   \qquad
   \max\{\|W_0\|,\|W_{-1}\|\}\ge\tfrac12\|W_A\|.
   }
   \tag{2.3}
   \]
   Therefore at least one **proper-base packet** retains half the **induced WAD norm**, exactly, with no multiplicity loss or synthetic automaton.

**Proof.** Lemma 1.1 partitions every leaf into the two classes, and restricting a lamination to a subset of leaves preserves pairwise nonintersection and admissibility. For \(n=0\), every lifted leaf has both endpoints in the bounded real interval from its start in \(\widetilde E_-\) to its end in \(\widetilde E_+\); the simply connected strip makes its proper homotopy class boundary-parallel to that interval. After projecting to the annular prime-end circle, the class is subordinate to the connected marked hull of the occupied end atoms along the \(G_0\) side. This hull omits a point in the opposite gap \(G_1\), so is proper. For \(n=-1\) the same argument uses the reverse directed boundary arc through \(G_1\) and omits \(G_0\). The two hulls need only contain the actual packet endpoint atoms, **not all atoms of the potentially larger end tags** \(E_\pm\); this distinction is essential in the already-proved nonunique-base example.

Any connected marked base subordinate to the same packet and homotopy direction must contain the full boundary subarc between every occupied pair of endpoint atoms; omitting an atom in that hull would force a different lift/homotopy class. Hence the hull is the unique least base in that fixed winding class. This proves items 1–3. KKL Appendix A.2.2 defines the induced WAD as the conformal width assigned to each disjoint arc-homotopy class, with norm their nonnegative sum. No arc class belongs to both winding packets. Thus the WAD's nonnegative sum splits exactly, giving the first equation of (2.3), and the elementary two-number inequality gives its second equation. \(\square\)

**What the exact norm identity does NOT claim:** KKL writes \(\mathcal W(A)\) for conformal width of a lamination, and the **full amplification theorem is expressed in those widths**, not only \(\|W_A\|\). To replace every occurrence of \(\mathcal W(A)\) with \(\|W_A\|\) in the source's analytic inequalities requires either a source-licensed width-normalization identity or a **verified Parallel Law** for these two particular sublaminations. That analytic identification is **not proved in this note**. Formula (2.3) is exact in the native **induced WAD** category. No unproved coefficient-one \(\mathcal W\)-splitting or bounded additive loss is asserted.

## 3. The full-circle-base case is **real and normalized by two packets**

### Theorem 3.1 (an actual positive-width full-base Wave with two crest components)

Suppose the original KKL vertex-side marking has at least six nondegenerate cyclic atoms \(\mathbf I_0,\dots,\mathbf I_{M-1}\). Choose \(j\) with \(2\le j\le M-2\). In the *actual conformal collar* of the inner prime-end boundary:

- build a positive-width disjoint foliated quadrilateral \(Q_0\) with one end in \(\mathbf I_0\), the other in \(\mathbf I_j\), and paths boundary-parallel to the **clockwise** connected arc \(\mathbf I_0,\dots,\mathbf I_j\);
- build a second positive-width quadrilateral \(Q_{-1}\) with end arcs in different compact subarcs of the **same two original marking atoms**, but whose leaves are boundary-parallel to the **opposite** marked arc \(\mathbf I_j,\dots,\mathbf I_{M-1},\mathbf I_0\).

These two genuine foliated quadrilaterals can be chosen **disjoint** by taking narrow collars on the opposite sides of the two complementary routes and disjoint endpoint subarcs. Every leaf is an admissible KKL marked path because its supporting arc spans at least three marked atoms on either route.

Their union \(A=A_0\cup A_{-1}\) is an actual Wave lamination. It has **one canonical minimal base**, namely the entire inner circle:

\[
\boxed{B_A=C,}
\tag{3.1}
\]

because no *proper* connected marked arc can support both opposite relative homotopy classes between the same two end atoms. Its minimal two end intervals are precisely \(\mathbf I_0,\mathbf I_j\), and its full-base crest is

\[
\boxed{
C_A=C\setminus(\mathbf I_0\cup\mathbf I_j),
}
\tag{3.2}
\]

a union of **two disjoint positive closed marked components**.

By Theorem 2.1 the two original proper-base packets are exactly \(A_0\) and \(A_{-1}\), and their induced WAD norms **add exactly**. Thus the two-component full-base obstruction in the companion deck-collision note is **not just a hypothetical topology**; it occurs in a genuine carrier annulus already before a dynamical iterate.

**Proof.** The real conformal prime-end collar of the actual annulus provides the two disjoint quadrilaterals, each with strictly positive modulus. The admissibility test follows from the source's explicit exclusion of all paths subordinate to a marked multi-interval of length at most two and the choice of at least three atoms on each route. If there were a proper connected base \(B\) for the **union**, then the linear lift of \(B\) would determine a unique boundary-parallel homotopy direction for paths between \(\mathbf I_0\) and \(\mathbf I_j\). The two opposite packets have different winding class, so they cannot both be subordinate to \(B\). The whole circle is a connected marked multi-interval to which both are subordinate, hence it is the unique least base. Both end atoms must be present; since all leaves have one endpoint in each, their minimal ends are exactly those atoms. Subtracting these ends gives the two positive complementary closed arcs. \(\square\)

**Non-LC assurance:** the construction is performed on the *actual ideal prime-end collar*, whose circular order and conformal geometry do not depend on the planar impressions being singleton. This is a native annular geometric example, not a synthetic circle substitution or a chosen global immersion quotient. No particular quadratic parameter or critical-return itinerary is claimed.

## 4. Consequences for the source's Wave-base ambiguity and full Wave amplification

1. **Repair of literal nonuniqueness, disjoint-end category.** The earlier two-disconnected-packet counterexample legitimately has two incomparable global minimal bases, but its **winding packets** have individually unique proper marked bases. The canonical split (2.2), not an arbitrary global base choice, repairs the **base assignment** at the level of actual marked lamination classes.
2. **Full-base packets are not a generic new geometric species.** The actual full-base example proves it is the **union of two opposite proper-base packets**, whose separately defined crests are positive and single connected blocks by the companion noncrossing theorem. Thus a two-component full-base crest can be treated **packetwise** before the degree-two deck collision comparison.
3. **Width/critical-visit interface still open.** KKL's critical-visit definition relates the **original** Wave's conformal width and the descendant's width; selecting one WAD packet with at least half of \(\|W_A\|\) does not automatically preserve a coefficient-one additive Wave inequality. One must verify the exact parallel-width law and the comparison between source Wave width and induced WAD norm, **or** reformulate the visit invariant to use a multiplicity-aware packet vector. These are genuine analytic requirements; Lean algebra alone does not discharge them.
4. **If source ends overlap:** The theorem does not pretend that one can select disjoint tags from an arbitrary overlapping pair without losing source leaves or changing their end-minimality. That case and arbitrary full-circle Wave laminations with overlapping ends require separate topology or a source-defined split.

**Priority impact:** A **global pointwise \(\iota\) prime-end quotient is unnecessary** for this Wave-base normalization. The next hardest interface is between the two **actual proper-base packets** and the corresponding **source-defined pullback/closed-crest transport**, with their **WAD-mass tags preserved** under the genuine covering and immersion. In parallel the critical-return positive dual-WAD witness remains open. The former full-base/base nonuniqueness obstruction is **completely normalized for disjoint ends** at the topological/WAD level.

**Review boundary and status:** Theorems 2.1 and 3.1 are mathematical deductions within the actual KKL annular marked-surface category, using the published path admissibility definition. They have not been independently refereed. **Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, and MLC remain OPEN.** No all-native quadratic renormalization counterexample, coefficient-one Wave width theorem, or global non-LC \(\iota^*\) atlas is claimed.
