# Issue #40 — parabolic-tail **time-change holonomy** and reduction of infinitely many critical gate graphs to one

**Date:** 2026-11-06. **Classification:** an unconditional *physical orbit-equivalence theorem* extracted from the **actual** KKL limb-insertion embeddings, a finite abstract no-new-cycle/defect criterion, and an explicitly **conditional** native prime-end gate transport theorem. This is not a synthetic transition automaton or an assertion that the needed critical-access collar extension already exists. The conclusion is a concrete new strategy for closing all sufficiently large rotations in one parabolic tail from **one base return-graph certificate plus a uniform insertion compatibility lemma**.

**Primary source:** Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §3.1, definition of a \(k\)-limb insertion (the two distinct dynamics equations and the existence of balanced parabolic-tail insertions), Proposition 3.4 (parabolically bounded persistence), §2.4 (real \(q\)-limb rotation and critical limb), §2.5 (non-LC combinatorial Hubbard carrier), §4 Lemma 4.8 (\(\ell(\mathbf L_j)\le6\mathbf b\)), §6.1 Propositions 6.5–6.8 (\(\iota^*\) complete attachments and proper corridor). Companion [native critical-cut graph](./kkl_native_finite_critical_cut_first_return_graph_20261106.md).

## 1. Native \(q\to q+1\) insertion changes *time* rather than the embedded orbit

Let \(f_q\), \(f_{q+1}\) be **actual quadratic polynomials or \(\psi\)-ql realizations** involved in a single KKL \(k\)-limb insertion, with filled Julia continua \(K_q,K_{q+1}\) and actual continuous dynamical embedding

\[
\phi:K_q\hookrightarrow K_{q+1}.
\]

Choose \(k\) far from the critical limb; more precisely \(k\not\equiv0\) and the unique extra phase \(k+1\) is not the critical index in the new \((q+1)\)-limb labeling. KKL §3.1 requires, on the old indexed limbs,

\[
\boxed{
f_{q+1}\phi=\phi f_q\quad\text{for every limb except }k,
\qquad
f_{q+1}^{\,2}\phi=\phi f_q
\quad\text{on the exceptional old limb }k.
}
\tag{1.1}
\]

The equations are **published source hypotheses about the actual filled Julia embeddings**, not a new assumed circle map. Source labels are represented in \(k-q<j\le k\), precisely the indexing used in §3.1. Define the *physical time increment* on a point with old limb index \(j\) by

\[
\tau(j)=
\begin{cases}2,&j=k,\\1,&j\ne k.\end{cases}
\tag{1.2}
\]

### Theorem 1.1 (exact finite orbit-clock identity on the actual Julia continua)

Let \(x_0\in K_q\) have a finite old forward itinerary \(x_i=f_q^i(x_0)\), \(0\le i\le n\), with every \(x_i\) in a well-defined old limb away from the central fixed point \(\alpha_{f_q}\). Put

\[
T_0=0,\qquad
T_j=\sum_{i=0}^{j-1}\tau(\operatorname{limb}(x_i)),
\qquad1\le j\le n.
\tag{1.3}
\]

Then

\[
\boxed{
f_{q+1}^{\,T_j}(\phi(x_0))=\phi(f_q^j(x_0))
\quad (0\le j\le n).
}
\tag{1.4}
\]

**Proof.** The claim holds for \(j=0\). Suppose it holds for \(j\). Apply (1.1) to the *actual old point* \(x_j\) in its indexed limb, using one or two iterates of the new polynomial as prescribed by (1.2). Then

\[
f_{q+1}^{T_j+\tau(\operatorname{limb}(x_j))}(\phi(x_0))
=f_{q+1}^{\tau(\operatorname{limb}(x_j))}(\phi(x_j))
=\phi(f_q(x_j))=\phi(x_{j+1}).
\]

Induction completes the proof. No boundary extension or local connectivity is used. \(\square\)

The clock counts one extra iterate each time the old physical orbit visits the insertion limb. In particular

\[
\boxed{T_n=n+\#\{0\le i<n:\operatorname{limb}(x_i)=k\}.}
\tag{1.5}
\]

This is exact, not asymptotic and not restricted to a fixed small value of \(q\).

### Corollary 1.2 (critical-limb first return is orbit-equivalent under the insertion)

Assume in addition:

- \(\phi\) preserves membership of its embedded old points in the **critical limb**: \(x\in\mathfrak L_0^{(q)}\iff \phi(x)\in\mathfrak L_0^{(q+1)}\);
- the unique *intermediate* new point \(f_{q+1}(\phi(x))\) arising from any exceptional \(k\)-limb step lies in \(\mathfrak L_{k+1}^{(q+1)}\), which is disjoint from the new critical limb;
- the itinerary avoids the central fixed point, so its limb labels are unambiguous.

Then a first return of \(x_0\in\mathfrak L_0^{(q)}\) to the **old physical critical limb** after \(n\) old iterates corresponds **exactly** to a first return of \(\phi(x_0)\) to the new physical critical limb after \(T_n\) new iterates:

\[
\boxed{
\phi\circ \operatorname{Ret}_{q}^{\rm physical}
=
\operatorname{Ret}_{q+1}^{\rm physical}\circ\phi
}
\tag{1.6}
\]

on the embedded old return domain. In particular any periodic **point** cycle of the old first-return map has a time-changed periodic embedded point cycle in the new one, and conversely any periodic first-return cycle *entirely within the embedded old physical domain* projects backward.

**Proof.** At synchronized times \(T_i\), critical-limb membership is equivalent by the first hypothesis and Theorem 1.1. There are no new critical visits between these synchronized times when \(\tau=1\), and the only intermediate new iterate for \(\tau=2\) lies in the different limb \(\mathfrak L_{k+1}^{(q+1)}\). Hence first-return indices agree after replacing the old time \(n\) by \(T_n\). Injectivity of \(\phi\) preserves equality and distinctness of embedded first-return points. \(\square\)

**Critical distinction:** This is an **actual theorem about physical filled-Julia points and their limb itineraries**. It does NOT assert that \(\phi\) extends to a map of the individual **Carathéodory prime ends** of \(\mathcal U\setminus\mathcal T\), or that it intertwines the **immersed** boundary operation \(F_*=f_*\iota^*\). The non-LC source does not grant that inference. Our earlier real quadratic two-access examples demonstrate why planar embedding alone cannot uniquely select prime ends.

## 2. Why the internal critical-cut state family should be *stable* under balanced insertion

KKL §6.1 gives \(\Phi_q(\mathbf L_0^{(q)})=C_q\) and the [native critical-cut theorem](./kkl_native_critical_cut_gate_reduction_20261106.md) shows every **proper critical-return interval** of length \(<12\mathbf b\) must have an endpoint at an *internal critical-limb cut*. Thus it lies within at most \(12\mathbf b-1\) original marking atoms of the critical limb.

KKL's balanced insertion indices \(k_q\) satisfy \(k_q\to\infty\) and \(q-k_q\to\infty\). Therefore, for any fixed \(\mathbf b\), **eventually the inserted limb is farther than \(12\mathbf b\) limb steps from the critical limb in either direction**. Because each actual limb contains at least one original marked atom, all the finite **short critical-cut input words** lie entirely in an unchanged bounded critical neighborhood at the level of **combinatorial ribbon-side labels**. The source's continuous embedding conjugates the old and new *filled-Julia point dynamics* there as in (1.1).

But the **actual** source and target prime-end boundaries remain different analytic objects: to identify an internal critical cut of the old \(\mathcal I_q\) with a specific cut of the new \(\mathcal I_{q+1}\) and preserve its **full attached Carathéodory block**, we need a **marked collar/access lift of the actual limb insertion**. This is the next theorem's expressly named additional input, not something granted by the source's \(\phi\) alone.

## 3. A general **stuttering simulation** theorem for first-return gate graphs

Let \(G_q\), \(G_{q+1}\) be the **true** finite critical-cut first-return state sets from the companion source-defined note, with partial real maps

\[
R_q:G_q\rightharpoonup G_q,\qquad
R_{q+1}:G_{q+1}\rightharpoonup G_{q+1}.
\tag{3.1}
\]

No transition is invented; each is defined via **genuine** \(F_*=f_*\iota^*\) marked interval iterations, and terminates on actual saturation or length increase.

We introduce a checkable **insertion-access certificate** consisting of:

**(IA1) Gate identification.** There is an injection \(\Theta:G_q\to G_{q+1}\), preserving the actual two endpoint **prime-end** cuts, their cyclic side and original short marked length, and **surjective onto the new critical-cut return candidates**. (This is stronger than the physical \(\phi\) embedding; it is a genuine analytic collar/proper-path assertion.)

**(IA2) Forward simulation on returning packets.** For every \(u\in G_q\), if \(R_{q+1}(\Theta u)\) is defined and **remains proper and length-preserving**, then \(R_q(u)\) is defined and

\[
\boxed{
R_{q+1}(\Theta u)=\Theta(R_q(u)).
}
\tag{3.2}
\]

An inserted limb may instead cause extra branching, saturation, or strict marked-length growth, in which case **the new arrow is terminated** rather than incorrectly projected to an old arrow. The extra physical iterate in Theorem 1.1 gives the source's candidate stutter phase, but does **not** by itself verify (IA2) for \(\iota^*\).

### Theorem 3.1 (no *new* periodic critical-cut cycles under a certified insertion)

Assume (IA1)–(IA2). If \(R_q\) has **no directed cycles**, neither does \(R_{q+1}\).

**Proof.** Suppose the new true graph has a directed cycle
\[
v_0\to v_1\to\cdots\to v_{s-1}\to v_0.
\]
By surjectivity in (IA1), write each \(v_i=\Theta(u_i)\). By (IA2), every new arrow comes from a defined old arrow with
\[
\Theta(R_q u_i)=R_{q+1}(\Theta u_i)=\Theta(u_{i+1}).
\]
Injectivity of \(\Theta\) forces \(R_q u_i=u_{i+1}\). Thus the \(u_i\) form an old directed cycle, contradiction. \(\square\)

### Corollary 3.2 (a *single base certificate* controls an entire parabolic tail)

Fix a parabolic tail built by sufficiently balanced limb insertions. Suppose (a) the native return graph at one base rotation \(q_0\) is verified **acyclic**, (b) **all subsequent** insertions have a uniform source-defined (IA1)–(IA2) analytic collar/attachment certificate for the critical-cut family. Then every subsequent native critical-cut graph is acyclic, and (with the other already separated proper-length/closed-crest hypotheses) the corrected bounded critical-visit growth theorem follows uniformly along that tail.

This is a **complete mathematical implication**, but **not yet an unconditional statement about the KKL source category**: (IA1)–(IA2) are *precisely the missing analytic gates*. The geometric novelty is that the source's parabolic-tail insertion construction provides a physical **time-change orbit equivalence**, so those conditions plausibly require **one local critical-collar verification** rather than global non-LC prime-end reconstruction at every \(q\).

## 4. A stricter defect-cocycle criterion that tolerates *extra* noncritical stuttering states

A real surgery comparison might produce a few auxiliary states (e.g. extra inserted-sector phase tags) that do **not** lie in the image of \(\Theta\), violating IA1 literally. To handle those without introducing cycles, use the following independent **finite well-founded-rank certificate**.

Let \(G_{\rm old},G_{\rm new}\) be finite sets with a source-defined partial arrow \(u\to v\) on \(G_{\rm new}\), a projection \(\pi:G_{\rm new}\to G_{\rm old}\), an old strict rank \(h:G_{\rm old}\to\mathbb N\), and a nonnegative *stutter budget* \(s:G_{\rm new}\to\mathbb N\), bounded by \(B\).

**(SD) Every actual new arrow \(u\to v\)** either **decreases the old rank**
\[
h(\pi v)<h(\pi u),
\tag{4.1a}
\]
or **keeps the old rank and strictly decreases the stutter budget**
\[
h(\pi v)=h(\pi u),\qquad s(v)<s(u).
\tag{4.1b}
\]

### Theorem 4.1 (lexicographic holonomy defect forbids all new cycles)

Under (SD), the single integer potential

\[
\boxed{
H(u)=(B+1)\,h(\pi u)+s(u)
}
\tag{4.2}
\]

**strictly decreases on every actual new arrow**. Therefore \(G_{\rm new}\) has no directed cycle, even if the insertion creates extra intermediate gate states.

**Proof.** If the old rank drops by at least one, the first term of (4.2) drops by at least \(B+1\), whereas the second can increase by at most \(B\). Hence total \(H\) decreases by at least one. If the old rank is unchanged, the strictly decreasing stutter budget makes \(H\) decrease. A finite directed cycle would force \(H(u_0)>H(u_1)>\cdots>H(u_0)\), impossible. \(\square\)

This is an **algorithmic proof obligation** for actual KKL access transfers: build the two ranks from the real critical-cut return diagrams and a finite inserted-phase clock. It is not a proof that the source does supply (SD); the existence of such a rank is **exactly what needs analytic verification**.

## 5. What makes this a distinct approach

This is **not** another independent finite interval automaton, and it is **not** another request for all non-LC prime-end fibers. It exploits *a special fact of the KKL family that generic quadratic dynamics does not have*: parabolic tails are constructed by **actual limb insertions with a one-step/two-step dynamical embedding**. We can try to prove uniform interval nonreturn by **renormalization-group style induction in the limb number \(q\)**, using source-defined time-change plus a **single local near-critical access/collar theorem**.

The precise strategy is:

1. For one fixed primitive base type, establish the actual native critical-cut graph and prove acyclicity (or find a real directed cycle).
2. Derive the finite critical-collar insertion map \(\Theta\) directly from the actual surgery embedding and proper-path \(\iota^*\), **not** from a rational-lamination label alone.
3. Verify (IA2): any nonterminal **length-preserving** new return projects to an actual old return; the one extra physical phase only delays the clock or triggers additional length/saturation. If there are auxiliary states, build the stutter budget of (SD).
4. Iterate Theorem 3.1 or Theorem 4.1 along the entire balanced parabolic tail. The number of **input** gate states remains \(O(\mathbf b^2)\) (companion cut-gate note), independent of \(q\); the actual iterate *times* may increase with \(q\), but the return graph does not acquire new cycles.

### Failure controls

- A continuous \(\phi:K_q\hookrightarrow K_{q+1}\) does **not** imply a unique prime-end map of \(\mathcal U\setminus\mathcal T\). Even a real locally connected slit point has two genuine accesses. **Never** identify (1.6) with (3.2) without (IA1)–(IA2).
- The source's insertion relation is \(f_{q+1}^2\phi=\phi f_q\) on **one exceptional limb**, not \(f_{q+1}\phi=\phi f_q\) everywhere. Losing that extra iterate invalidates a return-clock comparison.
- An added limb may carry a new small Julia component/attached tree: the closed \(\iota^*\) boundary contribution may change even when old planar orbit itineraries match.
- A degree-two covering can merge two separate image packets; any purported monotonicity of marked length must use the actual connected proper-source injectivity and full attachment records, not a graph valence or PF root alone.
- **No width claim:** The theorem is a topological orbit/critical-return statement, not the Wave coefficient-one conformal width estimate.
- The actual \(\pi:\mathfrak K\to\mathfrak K_{\rm com}\) is a combinatorial lift in the non-LC case; it is **not** by itself the required collar/access transport.

**Verdict:** A proved physical time-change theorem plus proved finite no-cycle transfer criteria make *one base graph + uniform insertion collar* a viable alternative to infinitely many q-dependent exceptional-access audits. **Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, and global MLC remain OPEN.** This is a source-locked research theorem and roadmap for specialist review, not proof of all IA hypotheses or claim of priority.
