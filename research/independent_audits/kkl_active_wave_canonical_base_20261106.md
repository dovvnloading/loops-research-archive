# Issue #40 — CANONICAL ACTIVE WAVES: uniqueness of the base and positive crest at large rotation

**Date:** 2026-11-06.  
**Status:** a new native **active-Wave uniqueness theorem** based on the actual annular prime-end topology, admissible path homotopy, and the already proved proper-base noncrossing criterion. It repairs the **base/end ambiguity precisely where KKL's critical-visit proof uses nonempty crests**, without needing an all-access non-LC boundary quotient. A short Wave at rotation \(1/q\), \(q\ge24\mathbf b\), that participates in a genuine critical visit has a unique **active (nonempty-crest)** base/end tag and a single regular positive crest. The new result does **not** prove the native interval-growth nonreturn lemma or closed \(\iota^*\) transport on every endpoint.

**Primary source:** Kahn–Kapiamba–Lyubich [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1): Appendix A.1, especially the definition of an admissible marked path, Wave, smallest base, minimal end multi-intervals, and crest; §6 opening paragraph, short Wave definition, critical visit definition; §4 Lemma 4.8 and proof (original separated limb-side marking). Companion source-facing notes: [proper-base noncrossing crest theorem](./kkl_wave_nonempty_crest_noncrossing_20261106.md), [large-rotation short-Wave proper-base theorem](./kkl_short_wave_proper_base_large_rotation_20261106.md), [two-packet annular normal form](./kkl_annular_wave_two_packet_normal_form_20261106.md), and [literal disconnected-lamination base nonuniqueness](./kkl_native_wave_base_nonuniqueness_20261106.md).

## 1. The right domain: an *active* Wave

Let \(V=\mathcal U\setminus\mathcal T\) be an actual KKL annular Hubbard-carrier complement with inner **prime-end** circle \(C\) and finite **original vertex-side marking** \(\mathcal I\). No local connectivity of the planar Julia continuum is assumed.

A **tagged Wave presentation** is a datum \((A,B,E_-,E_+)\) in which:

- \(A\ne\varnothing\) is an actual lamination of **simple admissible marked proper paths**;
- \(B\subset C\) is a **specified inclusion-minimal connected marked supporting base**, so each leaf is subordinate to \(B\);
- \(E_-,E_+\subset B\) are **specified minimal connected end multi-intervals**, with each leaf having one endpoint in each;
- its crest is \(D=B\setminus(E_-\cup E_+)\).

The presentation is called **active** if \(D\ne\varnothing\). The word “active” is used only to record the exact condition required for a nonempty **critical visit**: an empty crest cannot contain the image of an interval that meets the critical limb. The tag is a bookkeeping convention at this stage, not an assertion that arbitrary disconnected laminations have globally unique end/base data.

We work first with \(B\subsetneq C\) **proper**. The central conclusion is that the tag becomes canonical as soon as the crest is nonempty.

## 2. A shared core in every admissible leaf's genuine prime-end support

A simple proper path \(\gamma\) with its two ends on one annular inner prime-end circle has a well-defined **boundary-parallel support subarc** \(S_\gamma\subsetneq C\), specified by its homotopy class rel ideal endpoints. The standard proof uses a lift to the infinite-strip universal cover and the fact that a lifted simple arc cannot meet any nontrivial deck translate: only the two simple winding classes \(0,-1\) occur between two ordered endpoint intervals. See the companion two-packet normal-form note, Lemma 1.1.

When \(\gamma\) is subordinate to a **proper** marked base \(B\), the support \(S_\gamma\) is the **unique** one lying inside \(B\). Conversely any other proper connected marked base that subordinates \(\gamma\) must also contain this **same** homotopy support, not an arbitrarily chosen shorter arc between its planar landing points.

### Lemma 2.1 (shared nonempty open crest core)

Let \((A,B,E_-,E_+)\) be an active presentation with proper base \(B\). By the actual [noncrossing crest theorem](./kkl_wave_nonempty_crest_noncrossing_20261106.md), Theorem 2.1, the two end intervals occupy the **opposite extremities** of \(B\) and leave a connected open marked gap

\[
G=\operatorname{Int}\bigl(B\setminus(E_-\cup E_+)\bigr),
\quad\boxed{\ell(G)\ge1.}
\tag{2.1}
\]

Then **every** leaf \(\gamma\) has its unique boundary-parallel support \(S_\gamma\) containing \(G\):

\[
\boxed{
G\subset S_\gamma\quad\text{for all leaves }\gamma\in A.
}
\tag{2.2}
\]

**Proof.** Cut the proper circular base at one point outside it and regard \(B\) as a linearly ordered marked interval. Each leaf has one endpoint in its **left prefix** \(E_-\) and the other in its **right suffix** \(E_+\) (or swap the end labels globally). Its unique homotopy support inside \(B\) is the subarc joining those endpoints in the linear order; it contains every marked atom lying strictly between the two end packets, hence contains the full open core \(G\). This holds for every leaf, independently of which atoms in the two end packets its endpoints occupy. \(\square\)

The lemma uses the **actual prime-end order and homotopy**, not the possibly non-singleton planar impressions of those prime ends.

## 3. Theorem — a positive-crest Wave has a unique minimal base and unique *active* ends

### Theorem 3.1 (canonical active-Wave presentation)

Let \(A\) be a nonempty admissible lamination admitting at least one **active** presentation \((A,B,E_-,E_+)\) with **proper** base \(B\). Then:

1. **The base is uniquely least.** Every proper connected marked multi-interval \(B'\) subordinating **all** leaves of \(A\) contains \(B\). Hence \(B\) is the **unique inclusion-minimal supporting base**, even if the lamination \(A\) itself has disconnected support.
2. **The positive-crest end pair is unique up to swapping.** If \(E'_-,E'_+\subset B\) is another **minimal connected end pair** giving a **nonempty crest**, then
   \[
   \boxed{\{E'_-,E'_+\}=\{E_-,E_+\}.}
   \tag{3.1}
   \]
   Thus the nonempty closed crest \(D\) is unambiguous among all active presentations.
3. **Regularity and positivity are intrinsic.** The canonical crest is a **single regular positive closed** marked interval:
   \[
   \boxed{
   D=\overline{\operatorname{Int}D},
   \qquad
   \operatorname{Int}D\text{ is a connected open }\mathcal I\text{-multi-interval},
   \quad \ell(D)\ge1.
   }
   \tag{3.2}
   \]

**Proof.** By Lemma 2.1 every actual leaf-support subarc \(S_\gamma\) contains the same nonempty connected open marked core \(G\). Thus

\[
S(A):=\bigcup_{\gamma\in A}S_\gamma
\tag{3.3}
\]

is **connected**, since all its constituent subarcs have a nonempty common intersection. It is also contained in the proper base \(B\). In the finite cyclic original marking, the **smallest connected open marked hull** \(H_{\mathcal I}(S(A))\) of a connected subset lying in some proper marked arc is unique: it consists of its occupied extreme atoms and the marked cuts/atoms between them in that same boundary direction.

Every connected marked base \(B'\) subordinating the same actual leaf homotopy classes must contain **each** \(S_\gamma\) and therefore the hull \(H_{\mathcal I}(S(A))\). Conversely that hull subordinates every leaf by the very definition of \(S_\gamma\). Because the given \(B\) was inclusion-minimal, \(B=H_{\mathcal I}(S(A))\). Hence \(B\subset B'\) for every proper supporting base \(B'\). The whole boundary \(C\) strictly contains \(B\), so is not another minimal base. This proves item 1.

For item 2, by the proper-base noncrossing theorem **any** other end pair giving a nonempty crest must likewise be a **left-prefix/right-suffix pair** in the *same unique linear base* \(B\), with at least one complete atom separating the ends. For each original leaf the endpoint in the left prefix is therefore the same **left endpoint** as under \(E_-\), and its right endpoint is the same right endpoint as under \(E_+\). Thus \(E'_-\) must contain **all** of the actual left endpoint atoms of the lamination, while \(E'_+\) contains all actual right endpoint atoms. Minimality as *connected* marked end intervals forces each to be exactly the marked convex hull of its respective occupied endpoint atoms, which are precisely \(E_-,E_+\). The only ambiguity is their global exchange, proving (3.1).

Item 3 follows directly from the noncrossing crest theorem and from item 2's intrinsic identification. \(\square\)

**Precise logical scope:** Theorem 3.1 proves uniqueness **among active proper-base presentations**, plus uniqueness of the base even against a proposed empty-crest or full-circle base. It does **not** assert that *no other nonminimal/overlapping end pair giving an empty crest can ever be written down*. Such an empty-crest assignment is irrelevant to a **critical visit** only once the source requires an actual **nonempty image set** to be contained in its crest, as it does in §6. This is why uniqueness in the **active** category is the correct proof obligation.

## 4. Corollary — canonical positive crests for all short critical visits at high rotation

KKL §6 defines a critical visit \(B\) of \(A\) as a **short** Wave over \(F_*^mD_A\) for some \(m\ge1\), where this actual image intersects the critical limb \(\mathbf L_0\). Thus \(D_B\) is **nonempty**. The source also proves that a short Wave's two minimal end lengths are each \(<12\mathbf b\).

### Corollary 4.1 (active short-Wave canonicality, native large-q class)

Assume the standard full KKL vertex-side limb marking, with rotation \(1/q\) and \(q\ge24\mathbf b\). Then every genuine short Wave which participates as a **critical successor** in the source's §6 scheme has:

\[
\boxed{
\begin{gathered}
\text{a unique inclusion-minimal proper base},\\
\text{a unique minimal end pair among those with nonempty crest},\\
\text{a single closed regular positive crest }D=\overline J,\quad\ell(J)\ge1.
\end{gathered}
}
\tag{4.1}
\]

**Proof.** The [large-rotation short-Wave theorem](./kkl_short_wave_proper_base_large_rotation_20261106.md) provides a proper supporting base and excludes full-circle minimal bases. Because a critical successor crests over an actual nonempty set meeting the critical limb, its crest is nonempty. Apply Theorem 3.1 to the resulting active proper-base presentation. \(\square\)

Moreover, if \(B\) is a critical successor of \(A\) and **both** are short active Waves in this class, their **canonically determined** open crest cores \(J_A,J_B\) satisfy the native inclusion

\[
\boxed{
F_*^{m}J_A\subset J_B
}
\tag{4.2}
\]

by the source-defined **closed** critical-visit inclusion \(F_*^mD_A\subset D_B\), the true monotonicity of proper-path pullback, and the openness of \(F_*^mJ_A\) (KKL Proposition 6.6). No false equation \(F_*\overline J=\overline{F_*J}\) is invoked, and all eligible attached-component Carathéodory boundaries remain in the **closed** pullback (Proposition 6.5).

**Remaining correct type checks:** To apply (4.2) to a chain one must still verify the source's \(F_*^mD_A\) action is defined on that actual closed crest for all intermediate steps, and that the critical-limb intersection of the closed image yields a **full atom** of the open core rather than just an endpoint. This is independent of canonicality and is not proved here.

## 5. What this repairs and does not repair

The earlier [native Wave-base nonuniqueness certificate](./kkl_native_wave_base_nonuniqueness_20261106.md) remains valid for **disconnected laminations without an active separated crest**. It shows that the literal general Wave definition needs care. The present theorem shows a striking **automatic repair in the exact proof-used active subclass**: once a proper-base lamination has a nonempty crest, the base and active ends are canonical, even if the lamination is disconnected and even if its planar Julia boundary is non-LC.

In the central large-\(q\) short-Wave regime this eliminates **three previously separate problems** from the Wave interface:

- choice of global base among equal-length incomparable minimal bases;
- nonempty zero-atom/endpoint-only crests;
- full-circle two-component crests requiring a disconnected \(F_*\) operation.

**Still open:** the true \(\iota^*\) closed input on exceptional non-LC critical access fibers, **full-atom critical encounter** after closed-to-open core transport, **critical-return positive bivertical/WAD witness** for every candidate recurrent interval, and the corrected bounded-visits interval-growth theorem. These are the remaining analytic gates. The theorem does not prove Wave amplification or MLC.

**Status:** new, fully source-typed topological theorem in the actual annular prime-end category (pending independent specialist review). No synthetic circle automaton and no global monotone \(\iota\) boundary quotient. **Issue #40, KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR, KKL_PARABOLIC_WAVE_AMPLIFICATION, and MLC remain OPEN.**


## Postscript — the original critical limb is OPEN, so full-atom encounters are automatic

The companion [source-defined closed-crest / open-limb contact theorem](./kkl_native_critical_atom_contact_and_full_wave_interface_20261106.md), Theorem 2.1, eliminates the final *independent* endpoint-only encounter condition in the high-\(q\) short critical-visit category. KKL §4 defines \(\mathbf L_0\) as an **open multi-interval**, while this paper proves a genuine short critical successor crest \(C_B\) is a **regular positive closed** marked interval. If \(C_B\cap\mathbf L_0\ne\varnothing\), their intersection contains **one entire original marking atom in \(\operatorname{Int}C_B\cap\mathbf L_0\)**: a marked cut internal to an open limb always has a neighboring original atom on both sides, and a positive regular closed block meeting that cut contains at least one such atom. This is also proved by integer-cut arithmetic in the Lean module.

**Important:** The theorem does not claim the *image of the preceding open core* \(F_*^mJ_A\) already meets \(\mathbf L_0\); closed-only \(\iota^*\) attachments may enlarge that image. It gives full-atom intersection for the **successor's canonical core \(J_B\)**, which is sufficient for the corrected constant-length plateau/pigeonhole argument. Only the native **positive dual witness/no-periodic-critical-return** and source-defined closed iterates remain.
