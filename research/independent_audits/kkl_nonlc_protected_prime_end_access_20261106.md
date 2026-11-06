# Issue #40 — a non-locally-connected, source-defined protected-prime-end correspondence

**Date:** 2026-11-06  
**Status:** **new local analytic/topological theorem without a finite-fan assumption**. Valid at actual KKL small-filled-Julia continua under the listed full-complement hypotheses; it identifies **protected** accesses of the small-Julia complement with the carrier-relative accesses used by KKL, and isolates the exact contact-impression obstruction. It does **not** identify the critical contact accesses, prove edge incidence on the original marking, or close Wave / MLC.

**Source:** Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §2.1 (actual \(\psi\)-ql maps), §§2.3–2.5 (small-Julia cycle, complete Hubbard carrier and non-LC lift), §6.1 (Proposition 6.5 and proof of Proposition 6.8), Appendix A.1 and A.3.1–A.3.2 (ideal prime-end accesses and proper paths). This complements [the native vertex-preimage gate localization theorem](./kkl_native_vertex_preimage_gate_localization_20261106.md).

## 1. Real domains, no rational-lamination substitution

Fix a KKL stage and one **actual** compact, connected, full small filled Julia set \(K_i\subset\mathcal T\) in the ambient conformal disk \(\mathcal U\). Assume the actual carrier \(\mathcal T\) is compact and full so that its complement \(V_T=\mathcal U\setminus\mathcal T\) has the inner prime-end circle \(C_T\). Let

\[
V_i=\mathcal U\setminus K_i,\quad
C_i=\partial_C^{\rm in}V_i,\quad
A_i:=\overline{\mathcal T\setminus K_i}\subset\mathcal T,
\quad R_i=A_i\cap K_i.
\tag{1.1}
\]

The closure \(A_i\) is taken in the *actual dynamical plane*. It contains the old carrier edges and all other vertex continua outside \(K_i\) (together with their possible points of contact with \(K_i\)). The **contact set** \(R_i\) need not be finite or totally disconnected in the non-LC lift. Nothing here identifies \(R_i\) with a finite set of points of the combinatorial \(\mathcal T_{\rm com}\).

The inclusion of physical Riemann surfaces

\[
j_i:V_T\hookrightarrow V_i
\tag{1.2}
\]

is a genuine holomorphic embedding. It need not extend continuously to all of \(C_T\) or \(C_i\). For \(a\in C_i\), let \(\operatorname{Imp}_i(a)\subset K_i\) be its **actual prime-end impression**, defined by any shrinking-crosscut chain and the intersection of the closures of its nested shadow domains in \(\mathcal U\). This impression can be a non-singleton continuum.

Define the **protected** and **contact-ambiguous** access sets:

\[
\begin{aligned}
\mathsf P_i&=\{a\in C_i:\operatorname{Imp}_i(a)\cap A_i=\varnothing\}
          =\{a:\operatorname{Imp}_i(a)\cap R_i=\varnothing\},\\
\mathsf B_i&=C_i\setminus\mathsf P_i
           =\{a:\operatorname{Imp}_i(a)\cap R_i\ne\varnothing\}.
\end{aligned}
\tag{1.3}
\]

Neither set is inferred from external-angle *landing points*. In the non-LC case a single impression may contain many points. The definition is source-intrinsic.

## 2. Theorem — a genuine crosscut chart for all protected accesses

### Theorem 2.1 (protected-prime-end transfer)

With (1.1)–(1.3), the following hold **without local connectivity of \(K_i\)**:

1. **Eventual avoidance of added carrier:** For every \(a\in\mathsf P_i\) and every defining nested crosscut chain \((Q_n,D_n)\) for \(a\) in \(V_i\), there is some \(N\) such that
   \[
   \boxed{\overline{D_N}\cap A_i=\varnothing.}
   \tag{2.1}
   \]
   Thus the tail of the **same actual crosscut chain** lies in \(V_T\), and defines a prime end \(\mathfrak t_i(a)\in C_T\) with the **same planar impression** as \(a\).
2. **Canonical and order-faithful:** The correspondence
   \[
   \mathfrak t_i:\mathsf P_i\longrightarrow C_T
   \tag{2.2}
   \]
   is independent of crosscut-chain choice, injective and orientation preserving. It is a homeomorphism onto an **open subset** of \(C_T\); in particular it preserves **distinct prime ends** even if their impressions intersect.
3. **Maximal protected neighborhood:** \(\mathsf P_i\) is open in \(C_i\). Each \(a\in\mathsf P_i\) has a genuine source-defined open prime-end interval \(J_a\Subset\mathsf P_i\) on which \(\mathfrak t_i\) is an order-preserving homeomorphism onto its image. These intervals are obtained from actual crosscut shadows avoiding \(A_i\), not from an assumed global monotone quotient.
4. **Sharp interface limitation:** The argument gives no map at \(a\in\mathsf B_i\). Such an access may have an impression meeting a carrier edge attachment even when the impression is non-singleton and no pointwise landing angle exists. The source's proper-path definition and Proposition 6.5, with complete \(\partial_C X\), remain necessary there.

**Proof.** Fix \(a\in\mathsf P_i\). Let \(Q_n\) be a defining chain of crosscuts of the actual domain \(V_i\), and let \(D_n\) be its nested prime-end shadow domains, chosen so that
\[
\operatorname{Imp}_i(a)=\bigcap_n\overline{D_n}
\]
inside a compact subset of \(\mathcal U\) near the inner boundary. The sets \(\overline{D_n}\) are nested compacta. If every \(\overline{D_n}\) intersected the compact set \(A_i\), the nested compact intersection property would produce a point of \(A_i\cap\bigcap_n\overline{D_n}=A_i\cap\operatorname{Imp}_i(a)\), contrary to protection. Therefore (2.1) holds for some N.

Because \(\overline{D_N}\cap A_i=\varnothing\), the entire tail of the chain and the domains that it cuts off are disjoint from \(\mathcal T\setminus K_i\). The crosscuts still have both endpoints on \(K_i\subset\mathcal T\), so they are **genuine crosscuts of \(V_T\)**, and their same nested shadow domains define a prime end \(\mathfrak t_i(a)\) of \(V_T\). The planar intersection of those domains remains \(\operatorname{Imp}_i(a)\), proving item 1. If two choices of defining chain represent the same \(a\), they are eventually mutually subordinate in \(V_i\); once their shadows avoid \(A_i\), the same mutual subordination holds in \(V_T\), proving independence.

Conversely, any two protected prime ends mapping to the same carrier prime end have tails of chains living in \(V_T\) that are equivalent there. Since \(V_T\subset V_i\), their chains are also equivalent in \(V_i\), proving injectivity. Choose one crosscut shadow \(D_N\) as above; the prime ends of \(V_i\) approached through a sufficiently small open sub-shadow inside \(D_N\) form an open boundary arc \(J_a\), and the same region in \(V_T\) represents a corresponding open boundary arc. Their crosscut-chain identifications coincide, and the orientation inherited from the actual plane agrees. By shrinking the sub-shadow, all its end impressions remain inside \(\overline{D_N}\), disjoint from \(A_i\), so \(J_a\subset\mathsf P_i\). This proves local openness and local homeomorphism, and hence items 2–3. Item 4 merely records that no disjoint-shadow argument exists for a prime end whose impression meets \(A_i\); no nonexistence of a different analytic correspondence is asserted. \(\square\)

**No false landing assumption:** The proof works entirely with nested **prime-end shadows** and their compact impressions. It never asks that \(\operatorname{Imp}(a)\) be a singleton. It is therefore a genuine piece of the **nonlocally connected native geometry**, unlike a finite regular-star approximation.

## 3. A **typed** commutation theorem for genuine covering pullbacks

For the actual KKL holomorphic covering \(f:V'=\mathcal U'\setminus\mathcal T'\to V=\mathcal U\setminus\mathcal T\), use **different source and target pairs**. This typing matters: the source is \(\mathcal T'=f^{-1}(\mathcal T)\), not the old \(\mathcal T\), even though \(\iota\) identifies the old tree with a subtree near \(\mathfrak K\).

Take an actual source full continuum \(K_s\subset\mathcal T'\) and actual target full continuum \(K_t\subset\mathcal T\), with \(f(K_s)=K_t\). Assume source and target Jordan neighborhoods \(W_s\subset\mathcal U'\), \(W_t\subset\mathcal U\) have been chosen so that

\[
f:W_s\setminus K_s\longrightarrow W_t\setminus K_t
\tag{3.1}
\]

is a **proper unbranched covering** of degree \(d\in\{1,2\}\). At a noncritical small-Julia cycle step \(d=1\) is the natural case, and at the critical step containing \(c\in K_0\) a degree-two component is the relevant candidate; *the actual selected component and neighborhood hypotheses must be verified before invoking this proposition*.

Apply Theorem 2.1 **twice**, to the nested **source** pair \((K_s,\mathcal T')\) and the nested **target** pair \((K_t,\mathcal T)\). This produces protected external-access sets \(\mathsf P_s,\mathsf P_t\) and actual embeddings

\[
\tau_s:\mathsf P_s\to \partial_C^{\rm in}(\mathcal U'\setminus\mathcal T'),
\qquad
\tau_t:\mathsf P_t\to \partial_C^{\rm in}(\mathcal U\setminus\mathcal T).
\tag{3.2}
\]

The local small-Julia covering induces \(p_{\rm loc}:\partial_CK_s\to\partial_CK_t\). The **global carrier complement** covering induces \(p_T=f_*:\partial_C\mathcal T'\to\partial_C\mathcal T\), where the boundary circles/covering extensions must be the actual KKL ones.

### Proposition 3.1 (source-to-target protected access square)

Let \(a\in\mathsf P_s\) with \(p_{\rm loc}(a)\in\mathsf P_t\). Assume its protected source crosscut tail lies in \(W_s\setminus K_s\) and, on a sufficiently small angular neighborhood of \(a\), the actual holomorphic image \(f(Q_n)\) is a defining crosscut chain in \(W_t\setminus K_t\) (this holds on the genuine local covering chart of (3.1)). Then the following **correctly typed** equality of carrier-relative prime ends holds:

\[
\boxed{
p_T\bigl(\tau_s(a)\bigr)=\tau_t\bigl(p_{\rm loc}(a)\bigr).
}
\tag{3.3}
\]

Each sufficiently small protected access chart maps homeomorphically to its target chart; globally two distinct source charts may map to the same target when \(d=2\). Neither an impression with multiple points nor an added component is silently identified with one planar point.

**Proof.** Represent \(a\) by a defining source crosscut chain whose shadow eventually avoids \(\overline{\mathcal T'\setminus K_s}\); by Theorem 2.1, the **same** chain represents \(\tau_s(a)\) on the **source** carrier circle. Under the local covering hypothesis, the image crosscuts define \(p_{\rm loc}(a)\) on the target small-Julia boundary. Since the latter is protected, the tail of the image chain avoids \(\overline{\mathcal T\setminus K_t}\), and those **same target crosscuts** define \(\tau_t(p_{\rm loc}(a))\) on the **target** carrier circle. But \(p_T\) is defined by applying the *same actual holomorphic \(f\)* to the source carrier crosscut chain. Both routes therefore have the same defining target chain, proving (3.3). \(\square\)

**Strict typing boundary:** The square relates the **covering** \(f_*\) for two appropriately nested source/target pairs. It is **not yet** the KKL operation \(F_*=f_*\iota^*\). The latter also requires the source-defined proper-path immersion pullback \(\iota^*\), including complete attached-component boundary blocks at **unprotected contact** accesses. In particular, do not replace \(\tau_s\) by the old-target map \(\tau_{i-1}\) without changing the carrier from \(\mathcal T'\) to \(\mathcal T\): that would be a source/target type error.

## 4. Exact first-failure locus for the critical-limb pullback

At the distinguished critical-root \(x\) in the proof of KKL Proposition 6.8, determine which actual small filled Julia continuum \(K_i\) contains \(x\), if any. The vertex-preimage localization note shows all attachments are over the vertex package, and explicitly resolves the regular isolated-star branch cases under their native local chart hypotheses.

If \(x\in K_i\), the **only** small-Julia external accesses not covered by the protected transfer theorem are

\[
\boxed{
\mathsf B_i=\{a\in\partial_C K_i:
\operatorname{Imp}_i(a)\cap
\overline{\mathcal T\setminus K_i}\ne\varnothing\}.
}
\tag{4.1}
\]

In particular, **any** access whose impression contains an actual attachment contact \(x\in R_i\) belongs to \(\mathsf B_i\). These are exactly the source accesses requiring additional proper-path and attachment-block information; the source's one-planar-root statement does not assign them a unique ideal-boundary occurrence.

**What is now justified without LC:** every protected external small-Julia access has a canonical, order-faithful actual carrier-relative access, and the real holomorphic cover transports those charts. No finite fan, graph valence, rational lamination landing map, or singleton impression was used.

**What is still missing:** the actual contact-impression access census on \(\mathsf B_i\), its possible infinite cardinality, the full \(B_X\) blocks of \(\mathcal T'\setminus\mathcal T\) placed in the correct connected \(\iota^*\) intervals, and the original vertex-side marking edge multiplicities and closed critical-wave crest constraints. The **number** of contact accesses is not bounded by the number of abstract Hubbard edges without an independent analytic theorem.

An endpoint can have zero angular measure yet change saturation or birth an entire \(B_X\) under the **closed** immersion pullback. Thus angular-measure preservation on proper covering images and the protected-access transfer do not replace the open/closed endpoint audit.

## 5. Review and ledger status

This result gives an **actual non-LC prime-end access atlas away from contact impressions**. It does not fulfill Issue #40's all-native acceptance theorem or its native counterexample alternative.

The next proof must directly construct, at the critical small-Julia contact set, proper-path restrictions and actual crosscut chains for the **unprotected** \(\mathsf B_i\). If it cannot, report the missing crosscut/access selector as the first failure—do not substitute the rational-lamination model or silently declare the source's planar root to be one prime end.

**Keep OPEN:** Issue #40, \`KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR\`, \`KKL_PARABOLIC_WAVE_AMPLIFICATION\`, and MLC. No numerical simulator, independent specialist review, or claim of full native closure.
