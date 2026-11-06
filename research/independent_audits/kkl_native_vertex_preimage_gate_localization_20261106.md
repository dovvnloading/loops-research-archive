# Issue #40 — native vertex-preimage localization and an analytic gate atlas over isolated vertices

**Date:** 2026-11-06  
**Scope:** a new native localization theorem valid in the *actual* KKL carrier wherever the regular Hubbard-edge realization of §2.5 holds; a local holomorphic gate census over isolated finite-valence vertices; and a sharper first-obstruction certificate at small-filled-Julia vertices.  
**Status:** **partial mathematical result, not all-native closure**. Does not construct the remaining non-locally-connected vertex-continuum access selector, derive all the original Wave marking transitions, or prove zero-sector escape.

**Primary reference:** Jeremy Kahn, Alex Kapiamba, Mikhail Lyubich, *MLC for parabolically bounded primitive renormalization*, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §2.1 (the actual \(F=(f,\iota)\)), §2.4 (critical point in the critical limb; small Julia cycle), §2.5 (complete tree, regular edges, two inverse edges, and the non-LC lift), §6.1 (Propositions 6.5–6.8), Appendix A.1 and A.3 (ideal access and proper-path pullback). In particular, the explicit non-LC sentence of §2.5 says the combinatorial objects can be lifted by \(\pi\); it does *not* separately give an injection of individual prime ends.

The proof uses **the actual holomorphic quadratic covering** and the **actual** connected Hubbard carrier, never a synthetic cyclic-word model. The source's graph-edge map and its extension to analytic prime-end sides are **different types**.

## 1. Precise native assumptions and terminology

Fix a primitively renormalizable, periodically repelling KKL \(\psi\)-quadratic-like stage. In the near-filled-Julia identification by \(\iota\), write \(h=f\circ\iota^{-1}\) for the actual local degree-two branched map on an old-tree neighborhood. Let

\[
\mathcal K=\bigcup_{i=0}^{n-1}K_i,\qquad
\widehat{\mathcal K}=\mathcal K\cup
\{\text{branch points of }\mathcal T\text{ outside }\mathcal K\}
\cup\{\alpha_F\},
\tag{1.1}
\]

and \(\mathcal T'=f^{-1}(\mathcal T)\) in the source, using \(\iota\) only for the near-carrier identification. The old tree is forward-invariant, and its distinguished vertex package is forward-invariant: \(h(\widehat{\mathcal K})\subset\widehat{\mathcal K}\). The small Julia sets cycle, the branch points outside them are repelling periodic, and \(\alpha_F\) is fixed (KKL §§2.4–2.5).

**Regular-edge hypothesis (RE).** For each point \(y\) in a genuine open edge \(e\in E(\mathcal T)\), an embedded disk \(D_y\Subset\mathcal U\) exists with

\[
D_y\cap\mathcal T=\text{a single embedded simple arc through }y,
\quad D_y\cap\widehat{\mathcal K}=\varnothing.
\tag{1.2}
\]

This is the ordinary local property of the finite embedded graph-of-vertex-continua described in §2.5. It follows whenever the finitely many edge closures intersect only at their endpoint vertex continua and do not accumulate along another edge. For the actual non-LC lifted object, **RE is an analytic/planar realization condition** that should be checked from the lift, not inferred merely from a combinatorial edge label.

**Isolated-vertex hypothesis (IV).** A point \(v\in\widehat{\mathcal K}\setminus\mathcal K\) is an *isolated finite-star vertex* if some Jordan disk \(D_v\) satisfies \(D_v\cap\mathcal T\) is a union of exactly \(m\ge2\) simple arcs meeting only at \(v\), each crossing \(\partial D_v\) once, with no other carrier material. Such vertices occur in finite regular embedded Hubbard trees; a planar branch label alone is not enough to establish IV for an arbitrary non-LC lift.

The unique critical value of \(h\) lies in the cycle \(\mathcal K\), since the critical point is in \(K_0\) and \(f(K_0)=K_1\). In particular, regular open edges and isolated vertices outside \(\mathcal K\) contain **no critical value**.

## 2. Theorem A — added-tree roots cannot lie over regular edge interiors

### Theorem 2.1 (vertex-preimage localization; native)

Assume the **actual** old carrier has RE and \(\widehat{\mathcal K}\) is forward-invariant under \(h\), as above. Let \(x\in\mathcal T\) be a root of an added component \(X\) of the actual \(\mathcal T'\setminus\mathcal T\), meaning \(x\in\overline X\cap\mathcal T\). Then

\[
\boxed{h(x)\in\widehat{\mathcal K}.}
\tag{2.1}
\]

Equivalently, if \(h(x)\in e^\circ\) for any genuine target edge \(e\), there is a neighborhood \(N_x\) in which \(\mathcal T'=\mathcal T\); no added branch or endpoint can be born at \(x\).

**Proof.** Suppose \(y=h(x)\) lies in the interior of \(e\). Take the disk \(D_y\) of RE, so \(D_y\cap\mathcal T\) is a simple arc, and shrink it to avoid the unique critical value. As \(f\) is an unbranched degree-two cover over \(D_y\), its inverse image consists of two disks, each mapped biholomorphically onto \(D_y\). In the disk containing the actual source copy of \(x\), the set \(\mathcal T'=f^{-1}(\mathcal T)\) is therefore exactly one simple lifted arc through \(x\).

If \(x\) were in \(\widehat{\mathcal K}\), forward invariance would give \(h(x)\in\widehat{\mathcal K}\), contrary to \(y\in e^\circ\). Hence \(x\) lies in an **old open edge**. Applying RE to that old edge, the old \(\mathcal T\) contains a full local subarc through \(x\) within the lifted source arc. Shrink the source disk again so that its entire intersection with the single lifted arc is inside this old subarc. Thus \(\mathcal T'=\mathcal T\) in a neighborhood of \(x\). No component of \(\mathcal T'\setminus\mathcal T\) can have \(x\) in its closure. This contradiction proves (2.1). \(\square\)

**Important qualification.** The simpler statement “the source preimage is locally an arc, therefore no attachment” would be false without using **forward invariance of the old vertex package**. An old tree *endpoint* could lie in the middle of a lifted arc, permitting a new branch to continue past it. Forward invariance is what excludes that possibility for an actual KKL old tree over a regular target edge.

Theorem 2.1 is unaffected by whether some *other* vertex continuum \(K_i\) is locally connected. It is an actual univalent-local-disk argument; it asserts no global prime-end extension of \(\iota\).

### Corollary 2.2 (sharp division of vertex-preimage cases)

All possible roots lie in

\[
\mathcal T\cap h^{-1}(\widehat{\mathcal K})
=
\bigl(\mathcal T\cap h^{-1}(\mathcal K)\bigr)
\ \cup\
\bigl(\mathcal T\cap h^{-1}(\widehat{\mathcal K}\setminus\mathcal K)\bigr).
\tag{2.2}
\]

The first set consists of potential **small-filled-Julia vertex-preimage gates** and includes the possible degree-two critical case. The second consists of preimages of the **isolated singleton branch/central vertices**. The latter admit an explicit local gate atlas by the next theorem whenever IV holds. This is an actual geometric localization of the exceptional census, not merely the earlier bound on the number of limb indices.

## 3. Theorem B — complete local gate counts above a regular isolated vertex

### Theorem 3.1 (native univalent sector-lift atlas)

Suppose \(v\in\widehat{\mathcal K}\setminus\mathcal K\) satisfies IV, with target local valence \(m\ge2\). Let \(x\in\mathcal T\) be an actual preimage \(h(x)=v\). Then:

1. The map \(f\) has local degree **one** at \(x\); there is an actual conformal inverse chart \(h:N_x\to D_v\), and
   \[
   \boxed{\mathcal T'\cap N_x=h^{-1}(\mathcal T\cap D_v)}
   \tag{3.1}
   \]
   is an \(m\)-spoke embedded star.
2. The source complement \(N_x\setminus\mathcal T'\) has exactly \(m\) local sectors, each with an explicit *shrinking-crosscut* prime-end access at \(x\). These \(m\) source accesses are distinct, have the common planar impression \(\{x\}\), and map bijectively, in cyclic order, to the \(m\) genuine target sector accesses at \(v\).
3. Assume the actual old subtree \(\mathcal T\) is also a finite embedded local \(k\)-spoke star at \(x\), with \(1\le k\le m\), and its spokes are a subset of the lifted \(m\) spokes (as they are under the regular-edge/finite-vertex embedded realization). Then exactly \(m-k\) **source attaching spoke germs** at \(x\) belong to \(\mathcal T'\setminus\mathcal T\). In the planar cyclic order, if an old sector contains \(r_i\) new spoke germs, then it splits into exactly \(r_i+1\) source sector accesses.
4. If, in addition, the actual \(\mathcal T'\) is the tree-of-vertex-continua of §2.5 with no cycles and the added components meet \(\mathcal T\) only at \(x\), each missing spoke germ determines one distinct added component \(X\) attached at \(x\). The **complete** Carathéodory boundary of each such \(X\), not just the one spoke germ, remains included according to KKL Proposition 6.5 for each applicable open and closed marked input.

**Proof.** The critical value is in \(\mathcal K\), whereas \(v\notin\mathcal K\). Choose \(D_v\) avoiding the critical value and \(\mathcal K\). Its two preimage disks are biholomorphic sheets; the one containing \(x\) gives (3.1). Pulling back the \(m\) disjoint target spokes through this biholomorphism gives precisely \(m\) source spokes and preserves cyclic order. In each complementary local wedge construct a nested sequence of small crosscuts transverse to the wedge and tending to \(x\), with diameters tending to zero. Their nested complementary domains define a proper prime end of the **actual** source complement with impression \(\{x\}\). Two different wedges cannot yield equivalent prime ends: sufficiently small defining crosscut domains lie in different components of \(N_x\setminus\mathcal T'\). The biholomorphic map transports each chain to the corresponding target wedge, proving 1–2.

The old subtree is contained in the preimage tree under the near-carrier identification. Under the local-star hypothesis of item 3, its \(k\) old spokes form an actual subset of the \(m\) lifted spokes, so the other \(m-k\) spokes are precisely the new local germs, and insertion of \(r_i\) disjoint rays into one old wedge creates \(r_i+1\) new wedges. This proves item 3. If two distinct new rays belonged to the same component of \(\mathcal T'\setminus\mathcal T\), the connecting path through that component together with the two rays and \(x\) would give a cycle in the abstract tree of §2.5. The no-cycle property prohibits it; if every added component meets the old tree only at \(x\), no added ray can rejoin the old tree elsewhere. This gives item 4. The inclusion of each *entire* attached-component boundary is then the source's Proposition 6.5, not an extrapolation from local side germs. \(\square\)

**Crucial distinctions.** The \(m\) accesses in item 2 are **local prime-end crosscuts**, not the \(m\) points of a graph and not \(m\) different planar landing points. The counts \(m-k\) and \(r_i+1\) are valid only for an **actual** isolated-star chart; they do not apply to a non-locally-connected filled Julia continuum lacking such a chart. The number of *full marking atoms* in \(\partial_C X\) is also **not** determined by \(m-k\); it requires the original vertex-side marking and Proposition 6.5.

### Remark 3.2 (local degree-two model, with correct scope)

At a true critical point \(x_c\) of the quadratic map with \(v_c=h(x_c)\), holomorphic coordinates give the **genuine analytic local normal form**

\[
\zeta\circ h\circ z^{-1}(w)=w^2.
\tag{3.2}
\]

If (hypothetically) the target tree near \(v_c\) were an isolated \(m\)-spoke star, the preimage would have exactly \(2m\) spokes, and each target sector would have exactly two source-sector lifts. **In the actual KKL renormalization, however, the critical value lies in the nontrivial small filled Julia vertex \(K_1\)**. Consequently the target need *not* be an isolated star; equation (3.2) alone does **not** yield two gates per continuum or any finite count of accesses. Replacing a non-LC \(K_1\) by a single graph point before using (3.2) would be precisely the invalid shortcut Issue #40 forbids.

## 4. The remaining native non-LC access obstruction is over small Julia vertices

For the *actual* KKL stage, Theorem 2.1 excludes attachments over regular edge interiors. Theorem 3.1 supplies a complete **local** source-to-target prime-end sector atlas for each **isolated, regular branch/central vertex** of the target, including the exact old/new local spoke count when the old subtree has the regular source realization.

Therefore the genuinely unsolved access census can be **concentrated on**

\[
\boxed{\mathcal G_{\mathrm{wild}} :=
\mathcal T\cap h^{-1}(\mathcal K)}
\tag{4.1}
\]

plus any nominally isolated vertex for which the actual non-LC lift fails the stated IV/RE regularity. In the finite regular embedded-tree case the latter exception is empty. In the non-LC case, \(\pi:\mathfrak K\to\mathfrak K_{\rm com}\) provides a **combinatorial** vertex model but the source does not establish that preimages of \(\mathcal K\) have a finite local crosscut fan. A prime end may have a non-singleton impression, and distinct actual accesses may share a planar x.

For each \(x\in\mathcal G_{\mathrm{wild}}\), the unresolved native certificate is:

- The **actual** connected preimage vertex continuum \(f^{-1}(K_i)\) through \(x\), with the old/added incidence determined by the real embedded \(\mathcal T\subset\mathcal T'\).
- Every prime-end access \(\mathfrak a\) of \(\mathcal U\setminus\mathcal T\) involved in the chosen marked input at \(x\), distinguished even if its impression meets another access's impression.
- The real proper-path subordination relation defining \(\iota^*I\) and **independently** \(\iota^*\overline I\), inserting the complete \(\partial_C X\) of every applicable X as in Proposition 6.5; do **not** manufacture a global monotone boundary map.
- Source-edge sheets from the actual \(f^{-1}(E(\mathcal T))\), with multiplicity preserved under the proper-image covering lemma, *then* a comparison with the original **vertex-side** marking rather than assuming it equals edge sides.
- For every proof-used Wave crest \(C_A=B\setminus(E_-\cup E_+)\), its own **closed** source access transport, proper/short/positive checks, and any closure-triggered saturation.

This is **not a finite list of non-LC accesses**, and neither the one-root statement of KKL Proposition 6.8 nor a finite abstract Hubbard matrix gives one. The theorem proves a genuine *regular-site reduction* and finite analytic gate atlas in the other cases, not the entire target realization.

## 5. Adversarial checks and classification of proof status

| Assertion | Classification | What would falsify it |
| --- | --- | --- |
| No added root over a genuine regular target edge | **Proved under RE and vertex-forward-invariance** (Theorem 2.1) | An old vertex mapped to a target edge, or an actual edge without a local isolating disk |
| Distinct accesses and cyclic order over an isolated regular target vertex | **Proved under IV** (Theorem 3.1) | Failure of a finite local star, including a non-LC accumulation at the vertex |
| Exact count of new local spokes \(m-k\) | **Proved with the actual old \(k\)-star inclusion** | A missing analytic old-subtree identification, or nonregular source local geometry |
| One extra component per new spoke | **Proved with the actual no-cycle and one-root conditions** | A source component reconnecting to the old carrier at another point or multiple germs, not covered by the hypotheses |
| All non-LC small-Julia vertex accesses listed | **OPEN** | No actual crosscut atlas; \(\pi\) alone is insufficient |
| Full original marking transition, edge-weight expansion, zero-edge escape, genuine Wave closed-crest growth | **OPEN** | Requires complete actual access census and endpoint correspondence |

**Open gates:** Issue #40; KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR; KKL_PARABOLIC_WAVE_AMPLIFICATION; MLC. Do not promote them on this regular-site reduction. A new actual source-defined counterexample in the full KKL category has **not** been constructed. No independent referee validation is claimed.
