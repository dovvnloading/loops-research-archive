# Issue #40 — actual critical-root sector atlas under regular crosscut hypotheses

**Date:** 2026-11-06. **Status:** an actual-collar **conditional native local theorem** for the KKL one-root attachment point, plus its exact non-locally-connected obstruction. It constructs a local access correspondence from planar topology and proper paths, **not** a synthetic interval program or a global monotone quotient. The hypotheses at the critical point still need verification for the full native KKL category.

**Sources:** Kahn–Kapiamba–Lyubich, arXiv:2606.27272v1, §2.5 (genuine Hubbard tree and non-LC lift), §6.1 Proposition 6.5 (complete attached Carathéodory boundaries), proof of Proposition 6.8 (the common attachment point \(x\) and its atom/endpoint split), and Appendix A.1, A.3.2 (ideal-boundary proper paths). Companion: the half-turn native covering theorem in this draft PR.

## 1. What the source actually establishes at x

The proof of Proposition 6.8 states that the connected components of \(\mathcal T'=f^{-1}(\mathcal T)\) outside the old embedded tree \(\mathcal T\) all meet \(\mathcal T\) at a common **planar point** \(x\). It then uses a distinguished large critical-limb source interval \(\mathbf J'\subset\operatorname{Int}\iota^*x\). The equality of the **planar** roots of added components is not a statement that the **prime ends** incident to x are the same.

Even a locally connected slit tree has multiple accesses at an interior/branch point. In a non-LC carrier a prime-end impression may be non-singleton, making the planar-to-access inference even less defensible. The real quadratic witness \(P(z)=z^2-2\) in the companion note demonstrates two accesses at the same planar critical point.

The goal here is to construct a **checkable local access atlas** that can distinguish these possibilities, under named geometric hypotheses.

## 2. Native regular-root collar hypotheses

Fix an **actual** KKL stage \(F=(f,\iota)\). Work in its actual embedded carrier \(\mathcal T\subset\mathcal T'\) as identified by \(\iota\) in a neighborhood of \(\mathfrak K\) (KKL §6.1). Let \(x\) be the common planar attachment root of the added components in the proof of Proposition 6.8.

We impose the following **local** regular-root hypotheses, which are **not** being asserted for arbitrary non-LC KKL lifts:

**(RF1)** There is a closed Jordan disk \(D\) centered at x such that \(D\cap\mathcal T\) is precisely a finite star of \(m\ge2\) nonoverlapping simple old arcs \(h_0,\dots,h_{m-1}\) from x to \(\partial D\), and no other old carrier material accumulates in \(D\setminus\{x\}\). The cyclic ordering is induced by the orientation of the dynamical plane.

**(RF2)** In that disk, the *actual* added components \(X\in\pi_0(\mathcal T'\setminus\mathcal T)\) that meet x have finitely many disjoint simple attaching arcs \(e_X\) from x to \(\partial D\); different attaching arcs are disjoint away from x, lie in unique old sectors of \(D\setminus\mathcal T\), and no additional source carrier material accumulates at x between these arcs. Each such arc is part of the actual component \(X\), not a chosen abstract graph half-edge. This hypothesis includes **finiteness at x** and a regular cyclic fan; it is stronger than the source's one-root assertion.

**(RF3)** A collar of the relevant parts of \(\mathcal T'\) admits genuine proper crosscut chains in \(V'=\mathcal U'\setminus\mathcal T'\) following the two sides of every \(e_X\), with the resulting distinct prime ends and **complete** connected Carathéodory contribution \(B_X\). In particular each \(B_X\) is a proper interval with the expected two limiting side gates; this must be **verified** for non-LC attached continua and cannot be deduced from the point valence at x.

**(RF4)** The physical near-carrier identification by \(\iota\) carries the old local crosscut sectors to corresponding parts of \(V=\mathcal U\setminus\mathcal T\). The actual proper-path restriction is the one in KKL Appendix A.3.2; only the **local sector correspondence** constructed below is used, not a pointwise boundary extension of \(\iota\).

Every item can in principle be checked by source-defined crosscuts and attached continua. None follows merely from the abstract graph incidence matrix \(T_F\).

## 3. Theorem — finite regular-root prime-end sector census

The old \(m\) arcs divide a small punctured neighborhood of x into \(m\) old complementary sectors \(S_0,\dots,S_{m-1}\), in counterclockwise order. Let \(a_i\) be the **actual old prime end** approached by a chain of crosscuts shrinking to x **inside** \(S_i\). RF1 ensures \(a_i\ne a_j\) for \(i\ne j\), although every one of them has the same planar impression \(\{x\}\).

Group the attached components by their actual attaching sectors:

\[
\mathscr X_i=\{X\subset\mathcal T'\setminus\mathcal T:
e_X\subset S_i\},
\qquad r_i=|\mathscr X_i|.
\tag{3.1}
\]

### Theorem 3.1 (actual local root-sector atlas)

Under RF1–RF4 the following hold.

1. **Exhaustive sector assignment:** every attached component X in the regular root fan has one unique sector label i, and the labels occur in the cyclic order defined by the actual planar embedding at x. The count obeys \(\sum_i r_i=|\pi_0(\mathcal T'\setminus\mathcal T)|\) for the covered fan.
2. **Distinct side gates:** the \(r_i\) added arcs split the old sector \(S_i\) into \(r_i+1\) actual source complementary wedges. Their limiting proper crosscut chains give \(r_i+1\) distinct **terminal x-sector prime ends** in \(C'\). Each complete \(B_X\) is the connected contour block between its two terminal gates. In their actual cyclic order, the \(B_X\) and intermediate terminal gates form **one connected root-sector block** \(K_i\subset C'\).
3. **Different old sectors stay different:** the blocks \(K_i,K_j\) of distinct old sectors are separated in the source prime-end circle by nontrivial old side traces. Their planar impressions may all contain the same x, but they are **not** one prime-end fiber and cannot be given a single old access label.
4. **Local proper-path selection:** for the designated old access \(a_i\), the source-defined old/added contribution to the immersion pullback of a *marked open multi-interval I* (and separately its closure) includes every full \(B_X\) with \(X\in\mathscr X_i\) **exactly when the corresponding old access \(a_i\) is eligible for that input** in KKL Proposition 6.5. In particular, if \(a_i\in\overline I\setminus I\), a complete block may be **closed-only**; it is invalid to infer its inclusion from \(\overline{\iota^*I}\) without checking \(R(\overline I)\).
5. **Local attachment-collapse coordinate:** one can collapse each \(K_i\) to the corresponding old access \(a_i\), preserving cyclic order on the old side traces. This defines a degree-one *local order-preserving contour collapse* on the root fan. Where RF1–RF4 and Proposition 6.5 apply, it encodes the **same full attached-block membership** as the native immersion restriction for the specified marked inputs. It is **not** an asserted global boundary extension of \(\iota\), and no formula \(\iota^*I=q^{-1}(I)\) is asserted outside this regular-root atlas.

**Proof.** By RF1 the old spokes are an embedded planar star. Each complementary sector has a genuine proper crosscut chain shrinking through it to x, and chains in different sectors are separated by an old spoke; they therefore represent different prime ends in the old complement. Under RF2 every added attaching arc lies in exactly one old sector, giving item 1.

Order the new attaching arcs of one old sector by the actual orientation of D. The arcs are pairwise disjoint except at x, so they divide that sector into \(r_i+1\) connected wedges. RF3 supplies real proper crosscuts in all these wedges, giving different terminal x-accesses. Traversing a thin embedded regular collar around an added component enters along its first side and exits along its second; without passing an old spoke it cannot reach a different old sector. The complete Carathéodory contour \(B_X\) from Proposition 6.5 therefore lies contiguously between the two terminal gates, in the cyclic position determined by the root fan. Concatenating these blocks and the wedges between them gives the connected \(K_i\), proving item 2. Because any path joining different sectors in D without crossing an old spoke must leave the collar and pass around the old carrier, the respective root blocks are distinct in the prime-end cyclic order; that proves item 3.

For item 4, use the actual path-subordination definition in Appendix A.3.2, not planar landing-point equality. Proper paths shrinking through \(S_i\) are subordinate to the access \(a_i\). The source's Proposition 6.5 prescribes the complete Carathéodory boundary of each component meeting the old boundary over that input, rather than just its initial side. The local fan construction identifies those eligible components as precisely the X with corresponding i; no component in another old sector is substituted merely because its planar attachment point is x. Closed eligibility must be checked independently by the same source proposition. Finally, collapsing the consecutive K_i to a_i is monotone in their actual cyclic order, and leaves the old side traces in their old order. This encodes the *local* set membership just established; it does not give a global continuous immersion boundary map. \(\square\)

### Critical caveat about the theorem's scope

This is a theorem **conditional on an actual KKL root satisfying RF1–RF4**. It is not a claim that every \(\mathcal T'\setminus\mathcal T\) component in an arbitrary parabolically bounded prime primitive map is an embedded arc at x, has two prime-end gates, or lies in a unique old sector when the actual carrier is non-LC. In such a case the theorem yields a testable *first-failure location* (the missing RF1, RF2, or RF3 crosscut data), not proof of the full native atlas.

Also, the local contour collapse is an **access coding**, not a pointwise limit of the holomorphic immersion: an interior point of an attached arc is a boundary point of \(V'\) but an interior point of \(V\), so \(\iota\) need not have a target ideal-boundary limit there. This is exactly why the source defines \(\iota^*\) using proper paths.

## 4. Consequence for the KKL critical gate

KKL Proposition 6.8 identifies an actual interval \(\mathbf J'\) covering a long inverse critical-corridor package, contained in \(\operatorname{Int}\iota^*x\). The source's planar one-root assertion by itself does not select a unique \(a_i\). Theorem 3.1 shows the additional geometric assertion needed in the regular-root case:

\[
\exists i\quad
\mathbf J'\subset\operatorname{Int}K_i
\quad\text{with the corresponding actual old access }a_i.
\tag{4.1}
\]

If (4.1) is verified from the genuine critical preimage geometry, then the source's distinguished \(\iota^*x\) can be **typed** as the pullback associated to that access \(a_i\), with all same-sector attached \(B_X\) inserted and correctly ordered. If \(\mathbf J'\) meets two different blocks \(K_i\), additional old-side accesses or full-circle saturation must be accounted for; the equality of the planar attachment roots cannot justify silently combining two sectors.

This is not a counterexample to Proposition 6.8. It is the exact missing **access-selection requirement** before its planar x can be used as an unambiguous endpoint or marking atom in the corrected interval-growth repair.

## 5. Coupling to the actual covering and edge strips

Only after the RF1–RF4 census is constructed does the genuine covering \(p=f_*\) act on its actual source blocks. The companion half-turn theorem gives:

\[
p(R(I))\ne C\quad\Longrightarrow\quad
p|_{R(I)}\text{ is injective};
\tag{5.1}
\]

thus complete B_X in one proper-output connected pullback cannot collide or disappear in the covering, and a full source boundary block of positive angular access measure has positive target angular measure. At half a source circle, open and closed endpoint behavior separates sharply.

KKL §2.5 gives exactly two abstract preimage edges over each target Hubbard edge and its source-defined edge operator \(T_F\). Those graph edges must still be matched **individually** to the proper-path side accesses and attached blocks of the same \(F=(f,\iota)\). The native Wave marking is induced by sides of the **vertex package**, not automatically the sides of the graph edges. The RF theorem alone proves neither the original marking-length growth nor zero-weight sector escape.

## 6. Non-LC first-failure certificate and remaining gates

In the **actual** non-locally-connected lift \(\pi:\mathfrak K\to\mathfrak K_{\rm com}\) of §2.5, no result checked here proves RF1, RF2, or RF3 for the physical continuum at the critical x. In particular:

- A finite valence in the rational-lamination model does not guarantee a finite number of **actual** prime-end accesses or a regular Jordan crosscut fan.
- A common planar attachment point is not a unique prime end, even for locally connected continua.
- An abstract edge preimage count does not determine the access-order type or a complete \(\partial_C X\) boundary.
- An arbitrary global degree-one monotone quotient \(C'\to C\) remains unconstructed for the non-LC full category and cannot be inserted as an axiom.

**Next necessary native witness:** pick the actual critical-limb root x in a KKL stage; give proper crosscuts \(\gamma_{i,j}(n)\) tending to x for every relevant old and new terminal sector, prove their distinctness in the **actual** prime-end compactification, and identify the source-defined complete \(B_X\) between consecutive gates. Then verify the exact critical \(\mathbf J'\) occurs in a **specified** sector block and transfer the same records through \(p\) to the original vertex-side marking. Repeat for all exceptional neighboring limbs and the closed Wave crests. The theorem here does not perform that difficult full-source construction.

**Ledger:** Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, and global MLC all remain OPEN. No synthetic simulation, no global non-LC prime-end atlas, and no independent referee verification.
