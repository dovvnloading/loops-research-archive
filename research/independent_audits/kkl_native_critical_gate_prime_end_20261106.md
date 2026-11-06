# Issue #40 — a source-defined native critical-gate prime-end theorem

**Date:** 2026-11-06  
**Scope:** first native access/attachment step for [Issue #40](https://github.com/dovvnloading/loops-research-archive/issues/40).  
**Status:** **PARTIAL, source-derived theorem.** This note is **not** the complete exceptional-limb edge-incidence realization, a native interval-growth repair, a full Wave theorem, or an MLC result. It uses no finite synthetic boundary simulator.

## 1. Precise primary-source inputs

Version lock: Kahn–Kapiamba–Lyubich (KKL), [*MLC for parabolically bounded primitive renormalization*, arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1).

- **§2.1:** a pseudo-quadratic-like map is a pair \(F=(f,\iota):(\mathcal U',\mathfrak K')\rightrightarrows(\mathcal U,\mathfrak K)\); \(f\) is a holomorphic degree-two branched covering, while \(\iota\) is a holomorphic immersion. They are different maps.
- **§2.5:** the *complete* small-Julia-cycle Hubbard carrier \(\mathcal T\), its combinatorial edge matrix \(T_F\), and its lifted carrier in the non-locally-connected case. The combinatorial projection is **not** automatically an identification of actual prime ends.
- **§6.1, before Proposition 6.5:** \(\mathcal T'=f^{-1}(\mathcal T)\), and \(f,\iota\) restrict to a covering and immersion on the complements. The identification \(\mathcal T'\subset\mathfrak K\) uses injectivity of \(\iota\) *near* \(\mathfrak K\), not a globally defined inverse of \(\iota\).
- **Proposition 6.5:** the exact union of old boundary portions and **whole Carathéodory boundaries** of attached components, valid independently for an open marked multi-interval and for its closure.
- **Propositions 6.6–6.7:** the induced action \(F_*=f_*\iota^*\) is combinatorial and proper in the long corridor of noncritical limbs.
- **Proof of Proposition 6.8:** an explicit *critical-limb* preimage package is contained in the interior of the pullback of a distinguished attachment point/access \(x\), whether \(x\) belongs to a marked atom or is a marked endpoint.
- **Appendix A.1 and A.3.1–A.3.4:** ideal boundaries, proper-path subordination, covering pushforward, the immersion's maximal proper-path restriction, and the warning that \(F_*\overline I\) need not equal \(\overline{F_*I}\).

This is an audit of the specified v1 source, not a claim to have reproved its published Propositions 6.5–6.8 from first principles.

## 2. Actual surfaces and the covering access map

Let \(F=(f,\iota)\) be a KKL primitively renormalizable, periodically repelling, parabolically bounded \(\psi\)-ql stage with rotation number \(1/q\) and source parameter \(\mathbf b\). Write

\[
\mathcal T'=f^{-1}(\mathcal T),\qquad
V=\mathcal U\setminus\mathcal T,\qquad
V'=\mathcal U'\setminus\mathcal T'.
\tag{2.1}
\]

Use the **actual** inner ideal/Carathéodory boundary circles

\[
C=\partial_C^{\mathrm{in}}V=\partial_C\mathcal T,\qquad
C'=\partial_C^{\mathrm{in}}V'=\partial_C\mathcal T'.
\tag{2.2}
\]

These are boundaries of the actual carrier complements, not circles chosen to fit a transition word. In Appendix A.1, the ideal-boundary construction is expressed through the universal cover as \((\partial\mathbb D\setminus\Lambda)/\Delta\). A Carathéodory point is an **access**, not necessarily a unique point of the Julia set.

### Lemma 2.1 (native annular covering chart, with its precise hypothesis)

Suppose the KKL carrier \(\mathcal T\) is compact, connected and full in the disk \(\mathcal U\), with the unique critical value of \(f\) in \(\mathcal T\), as in the usual annular Hubbard-carrier stage. Then \(V,V'\) are connected annuli; the restricted map

\[
f:V'\longrightarrow V
\]

is an unbranched **degree-two covering**. There are conformal annular coordinates in which

\[
V\cong\{r<|z|<1\},\quad
V'\cong\{\sqrt r<|w|<1\},\quad
f(w)=w^2,\qquad 0<r<1.
\tag{2.3}
\]

Consequently the actual inner prime-end covering \(p:C'\to C\) is, in these coordinates,

\[
p(e^{2\pi it})=e^{2\pi i(2t)}.
\tag{2.4}
\]

This statement applies to non-locally-connected **boundary impressions** whenever the actual carrier has the stated annular complement; no unique landing point is assumed. It does **not** identify either coordinate \(t\) with a polynomial external-ray angle or with a rational-lamination label.

**Proof.** Since \(\mathcal T\) is a full continuum in the conformal disk, \(V\) is an annulus. The only branch value lies in \(\mathcal T\), so \(f\) is unbranched over \(V\). A loop surrounding \(\mathcal T\) surrounds the unique simple branch value, hence its monodromy exchanges the two sheets. Therefore \(V'=f^{-1}(V)\) is the connected double cover of \(V\), itself an annulus. The index-two subgroup \(2\mathbb Z\subset\pi_1(V)=\mathbb Z\) and annular uniformization give (2.3), with rotations absorbed in the charts. Prime-end compactification of these conformal annuli gives (2.4) on the inner circles. The proof uses accesses, not local connectivity of the planar boundary. \(\square\)

**Type restriction:** Lemma 2.1 is a covering statement about \(f\). It is **not** a global pointwise boundary extension theorem for \(\iota\). For any native stage where fullness/annularity of a lifted carrier has not been independently established, (2.3) is conditional and must not be imported by appealing only to \(\mathcal T_{\mathrm{com}}\).

## 3. The immersion is a proper-path relation, not an assumed quotient

For a connected \(J\subset C\), let \(R_\iota(J)=\iota^*J\) denote the **actual** Appendix A.3.2 restriction. It is the maximal source ideal-boundary subset characterized using proper paths \(\gamma\) in \(V\) having a unique proper restriction \(\gamma'\) under \(\iota\), and the implication

\[
\gamma'\text{ subordinate to }R_\iota(J)
\quad\Longrightarrow\quad
\gamma\text{ subordinate to }J.
\tag{3.1}
\]

For a proper path \(\gamma\), the immersion restriction consists only of those components of \(\iota^{-1}(\gamma)\) that are proper paths in \(V'\). This distinction is indispensable near a component of \(\mathcal T'\setminus\mathcal T\).

For each source-defined \(J\), let \(\mathscr A(J)\) be the collection of **actual connected components** \(X\) of \(\mathcal T'\setminus\mathcal T\) whose attachment is over \(J\), using precisely the attachment/access relation of KKL Proposition 6.5. Let \(B_X\subset C'\) denote the **complete** corresponding Carathéodory boundary contribution, with its full end accesses; do not replace \(B_X\) by a single landing point, a graph label, or one side. Put \(H(J)=\iota^{-1}(J)\) for the old, source-identified boundary portion in the notation of Proposition 6.5.

### Theorem 3.1 (native critical-neighborhood attachment pullback)

For every source-marked open multi-interval \(I\subset C\) and, **separately**, its closure \(\overline I\), the native pullback is given exactly by

\[
\boxed{
R_\iota(J)
=
H(J)\ \cup\ \bigcup_{X\in\mathscr A(J)}B_X,
\qquad J\in\{I,\overline I\}.
}
\tag{3.2}
\]

Moreover:

1. **No branch is deleted by immersion restriction.** Every \(X\in\mathscr A(J)\) contributes its entire \(B_X\) to \(R_\iota(J)\). This is a set-theoretic completeness assertion; **it does not assert an edge count or injectivity after the covering pushforward**.
2. **The same real maps drive interval pushforward.** For either allowed \(J\),
   \[
   F_*J=p(R_\iota(J)),
   \tag{3.3}
   \]
   where \(p\) is the covering of the actual source and target annular boundaries. There is no independent word substitution.
3. **Endpoint-birth localization.** Define the native open/closed defect
   \[
   D_\iota(I)=R_\iota(\overline I)\setminus\overline{R_\iota(I)}.
   \tag{3.4}
   \]
   Then
   \[
   D_\iota(I)\subset
   \bigl(H(\overline I)\setminus\overline{H(I)}\bigr)
   \ \cup\
   \bigcup_{X\in\mathscr A(\overline I)\setminus\mathscr A(I)}B_X.
   \tag{3.5}
   \]
   Thus a genuinely new source access at closure comes either from the **old lifted endpoint** or from a **closed-only attachment component**. Equation (3.5) is a containment, not an unjustified equality: boundaries may share accesses.
4. **A covering cannot repair unproved multiplicity.** Since \(p\) is continuous on the compact inner prime-end circles,
   \[
   F_*(\overline I)\setminus\overline{F_*I}
   =
   p(R_\iota(\overline I))\setminus p(\overline{R_\iota(I)}).
   \tag{3.6}
   \]
   This may or may not be empty; its vanishing is **not** a reason to omit the extra source accesses or to count two coincident image traversals as one.

**Proof.** Formula (3.2), including the use of whole attached-component boundaries and separate open/closed inputs, is exactly the geometric assertion of KKL Proposition 6.5, applied to the actual \((V',V,\iota)\). Appendix A.3.4 defines the action as the covering pushforward after the immersion restriction, giving (3.3). For (3.5), take \(a\in R_\iota(\overline I)\setminus\overline{R_\iota(I)}\) and apply (3.2) at \(\overline I\). If \(a\in H(\overline I)\), then \(a\notin\overline{H(I)}\). Otherwise \(a\in B_X\) for some \(X\in\mathscr A(\overline I)\). If that same \(X\) belonged to \(\mathscr A(I)\), then \(B_X\subset R_\iota(I)\), contradiction. Hence \(X\in\mathscr A(\overline I)\setminus\mathscr A(I)\). This proves (3.5) without any implicit singleton-impression assumption. Finally \(p(\overline S)=\overline{p(S)}\) for all \(S\subset C'\): continuity gives one inclusion, and compactness/closedness of \(p\) gives the other. Substitute \(S=R_\iota(I)\) to obtain (3.6). \(\square\)

**What is and is not new.** The completeness identity (3.2) is **imported** from the source, not a new proof of its Proposition 6.5. The native annular chart, typed composition, and the explicit endpoint-defect consequences record what follows rigorously. None of this is an explicit component-by-component census for a chosen \(F\).

## 4. A genuinely source-defined critical-limb gate

Assume \(q\ge2\mathbf b+2\). Write the central corridor and its complementary exceptional indices as

\[
G=[\mathbf b,q-\mathbf b-2]\cap\mathbb Z,\qquad
E=(\mathbb Z/q\mathbb Z)\setminus G.
\tag{4.1}
\]

The set \(E\) contains the critical limb \(0\) and its exceptional neighbors, with \(|E|=2\mathbf b+1\). If \(q<2\mathbf b+2\), take \(G=\varnothing\) and \(E=\mathbb Z/q\mathbb Z\). Thus always \(|E|\le\min(q,2\mathbf b+1)\), exactly the one-step support observation in [PR #39](https://github.com/dovvnloading/loops-research-archive/pull/39).

Construct the **actual** critical preimage package, following verbatim the *objects* in KKL's proof of Proposition 6.8:

- \(\mathcal P'\): the portion of \(F^{-1}(\mathcal L_{(\mathbf b,q-\mathbf b)})\) lying in the actual critical limb \(\mathfrak L_0\), as identified near \(\mathfrak K\) in §6.1;
- \(\mathbf J'\): the minimal lifted marking multi-interval of \(\mathcal I'=f^*\mathcal I\) containing \(\partial_C\mathcal P'\);
- \(x\): the distinguished **source-defined attachment point/access** in that proof.

### Theorem 4.1 (native point-to-long-corridor gate)

At the KKL stage just specified,

\[
\boxed{
\mathbf J'\subset\operatorname{Int}R_\iota(\{x\}),
\qquad
p(\mathbf J')=\mathbf L_{(\mathbf b,q-\mathbf b)}.
}
\tag{4.2}
\]

The source's proof distinguishes two **genuinely different** input types.

- **Marked-atom case:** if \(x\) lies in a marked atom \(\mathbf I_x\), its immersion pullback contains the long critical preimage package, and the corresponding stretching input can be taken from that atom.
- **Marked-endpoint case:** if \(x\) is a marked endpoint, the relevant interior is \(\operatorname{Int}R_\iota(\{x\})\), which is **not permitted to be replaced** by a point or by the closure of either adjacent open-atom pullback without a separate proof.

KKL Proposition 6.8 constructs a stretching multi-interval \(I_{\rm str}\) of combinatorial length at most two from these cases. Its image contains the long noncritical limb corridor. Thus (4.2) is a real critical-limb access/attachment correspondence in the native source category, not a synthetic circle example.

**Proof.** In the proof of Proposition 6.8, \(\mathcal L'_{[\mathbf b,q-\mathbf b-2]}\) and its minimal Carathéodory marking multi-interval are precisely \(\mathcal P'\) and \(\mathbf J'\) above. The proof states both \(f_*\mathbf J'=\mathbf L_{(\mathbf b,q-\mathbf b)}\) and \(\mathbf J'\subset\operatorname{Int}\iota^*x\). By Lemma 2.1 the covering pushforward on the actual Carathéodory inner boundary is \(p\), which yields (4.2). The subsequent two-case construction of \(\tilde{\mathbf I}_{\rm str}\) is exactly KKL's atom/endpoint distinction. We do not identify \(x\) with a unique planar landing point or count distinct accesses using the valence of \(x\). \(\square\)

### Corollary 4.2 (what proper corridor geometry actually excludes)

By KKL Proposition 6.7,

\[
\mathcal T'\cap\mathcal L_G=\mathcal T\cap\mathcal L_G.
\tag{4.3}
\]

Hence no **new interior tree component** can be attributed to a sector contained strictly inside the good corridor. For such sectors the complete attachment contribution in (3.2) is absent. This does **not** remove closed endpoint accesses at the boundary of \(G\), and does **not** bound return times, the number of exceptional components, or the multiplicity of their boundary accesses.

At the level of the marked open limb multi-intervals, KKL §6.1 also identifies

\[
F_*\mathbf L_0=C,\qquad
F_*\mathbf L_j=\mathbf L_{j+1}\quad(j\ne0).
\tag{4.4}
\]

These are native set-level interval images, **not** a statement that every small-Julia edge-side and every closed crest has preserved positive edge mass.

## 5. Non-locally-connected access discipline

KKL §2.5 defines \(\mathcal T_{\rm com}\) and then lifts the corresponding objects using \(\pi:\mathfrak K\to\mathfrak K_{\rm com}\) when \(\mathfrak K\) is not locally connected. The analytic data in (2.1) must nevertheless be formed from the **actual** \(f,\iota,\mathcal T,\mathcal T'\), not from a pointwise inverse on the combinatorial model. The annular prime-end chart in Lemma 2.1 needs no singleton impressions, and the proper-path formula (3.2) retains full component boundaries.

The following statements are **not** established here, and must not be silently inferred from the lift:

1. \(\pi\) induces an injective or order-preserving identification of all proof-used individual prime-end accesses;
2. every native component boundary \(B_X\) has exactly two gates or one positive edge traversal;
3. the two sheets of \(p\) remain distinct after applying \(p\) to source access sectors;
4. the actual lifted source-endpoint defect is empty;
5. the entire required non-locally-connected category satisfies every annular/fullness hypothesis without an independent check of its lifted carrier.

No choice of external angles, graph valence, or rational-lamination classes settles these assertions.

## 6. Exact native data required next (not a synthetic regression)

For each actual \(F\) in the required native category and each exceptional input atom/endpoint from \(E\), a completion certificate must contain **all** of the following records, obtained from \(f^{-1}(\mathcal T)\) and proper-path restriction, not chosen independently:

| Native item | Exact witness needed | This note |
| --- | --- | --- |
| Source and target | Actual \(V',V,C',C\), \(p\), \(\iota\), and source marking | Constructed/typed in §§2–3 (annular condition stated) |
| Critical package | \(\mathcal P',\mathbf J',x\), and its atom-vs-endpoint type | Source-defined in Theorem 4.1 |
| Added components | For every \(X\in\mathscr A(I)\) and \(\mathscr A(\overline I)\): complete \(B_X\), distinct accesses, cyclic order, and endpoint membership | Complete **set formula**; individual native census still open |
| Edge traversal | Each \(B_X\) and old side labeled by the exact oriented edge/side traversals of the **same** \(f,\iota\), with cover-sheet multiplicity, checked against \(T_F\) of §2.5 | Open |
| Zero-edge sectors | Native degree-one/degree-two gate maps and proof every proper zero-edge sector eventually gains edge mass or saturates | Open |
| Wave crests | Actual closed crest \(C_A\), independently checked \(F_*^{m}C_A\subset C_B\), positivity/shortness and endpoint-birth behavior | Open |

**Adversarial failure checks before any promotion:**

- An \(x\) at a marked **endpoint** must be processed through \(R_\iota(\{x\})\); simply closing \(R_\iota(I)\) can lose the critical gate.
- A collapsed or non-singleton **impression** cannot be used to identify two distinct prime-end accesses.
- Two source sectors with the same \(p\)-image cannot be silently counted once as an edge traversal.
- A positive Perron root of \(T_F\) alone says nothing about a proper interval supported entirely on zero-weight sectors.
- \(F_*C=C\) for the whole boundary is an absorbing case, not strict combinatorial length growth; use the corrected **proper-or-saturated** interval statement from [PR #38](https://github.com/dovvnloading/loops-research-archive/pull/38).
- KKL Appendix A.3.4 explicitly warns that \(F_*\overline I\) need not equal \(\overline{F_*I}\); proof-used closed Wave crests require their **own** pullback records.

## 7. Result and ledger boundary

**Established with source-defined geometry:** the true \(f\)-cover on the annular access circles; the immersion's proper-path construction; complete **set-theoretic** attachment inclusion for open/closed intervals; the source's explicit point-to-long-critical-corridor gate; and localization of possible closure-only access births. The theorem is not an independent proof that KKL's source geometry satisfies all assumptions of a stronger repair.

**Still missing:** the concrete exceptional component/gate census with distinct actual accesses; one-to-one derivation of the edge-incidence rows of \(T_F\) with multiplicity; zero-sector escape; and the closed-crest Wave transport inequalities across every required native stage, especially non-locally-connected lifts. Thus this is a **first source-defined theorem / precise remaining first-failure checklist**, not the complete acceptance theorem for Issue #40.

Do **not** close or promote \(\texttt{KKL\_BOUNDED\_VISITS\_INTERVAL\_GROWTH\_REPAIR}\), \(\texttt{KKL\_PARABOLIC\_WAVE\_AMPLIFICATION}\), or MLC on this result. No claims of independent specialist referee verification or of new priority are made.
