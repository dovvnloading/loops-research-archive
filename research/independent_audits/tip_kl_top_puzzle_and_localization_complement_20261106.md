# Exact KL top-puzzle candidate and a source-domain obstruction at the nonattracting 3/9 tip

**Later November 6 results:** the [terminal-first-child proof](tip_kl_terminal_first_child_20261106.md) and its two landed-ray tables resolve the nest and finite puzzle geometry, while the [common-exterior comparison](tip_localization_refinement_peripheral_monodromy_20261106.md) constructs a restricted based 9→3 map with infinite sheet fibers. The separate [center-identification proof](period27_center_tuning_identification_20261106.md) resolves the old `A*A*A` component question. The remaining selected `O/xi/eta` transition is still open; the checklist below records the earlier state. Section 5 also corrects the meridian's subgroup membership: the collision witness lies outside the source local subgroup.

**Audit (2026-11-06), for Issue #29. Status: PARTIAL; issue stays OPEN.** This note deliberately separates three categories: (A) exact arithmetic proved by Lean/independent rational checker, (B) standard complex-dynamical analytic inputs with cited sources, and (C) source-natural localization and prime-end identification **not yet available**. It does not identify an arbitrary exterior-ray collapse with a Kahn localization sheet, and does not prove MLC, H1–H4 or UPTCR.

## 1. Which source construction is being tested?

Primary source: J. Kahn and M. Lyubich, *A priori bounds for some infinitely renormalizable quadratics: II. Decorations*, [arXiv:math/0609046v2](https://arxiv.org/pdf/math/0609046v2), **§2.1, printed pp. 5–6, and Lemma 2.1 printed p. 6**; §2.2 printed pp. 7–8. The paper takes a dividing fixed point \(\alpha\) with \(q>1\) landing rays, obtains a critical Yoccoz piece \(Y^1\), and defines \(n\) as the *least positive* number with \(f^{qn}(0)\) in an off-critical depth-one piece \(Z_\kappa^1\). This is **not** the renormalization return period \(p\).

Its source-defined objects are
\[
P=Y^{(n-1)q+1},\quad V^0=Y^{nq+1},\quad
Q_L,Q_R\subset P\quad\text{(univalent }f^q\text{-pullbacks of depth }nq+1),
\]
with the pairwise-disjoint \(Q^v\) of Lemma 2.1 at depth \((2n-1)q+1\) obtained under \(f^{nq}\). A separate *primitive* return \(f^p\) and its disjoint little Julia cycle enter at the terminal stopping step of §2.2. The KL paper studies infinitely-renormalizable maps for its global a priori-bounds theorem; the elementary top-puzzle construction is used here only where its explicitly checked local hypotheses apply. **No claim of its global main theorem at this finite PCF example is intended.**

## 2. Explicit top Yoccoz puzzle in the ambient \(f(z)=z^2+c_{\rm tip}\)

The exact dyadic root bracket, critical preperiod 10/eventual period 9 and real restrictive intervals \(I_3=[x_6,x_3]\), \(I_9=[x_9,x_{18}]\) are in [the original tip certificate](period27_misiurewicz_tip_ray_access_20261106.md). Its [two-scale complex proof](nonattracting_tip_complex_two_scale_20261106.md) obtains \(V_9\Subset U_9=D(0,1/32)\), \(\overline{V_9}\subset D(0,27/1024)\), \(V_3\Subset U_3=D(0,1/4)\), \(K_9\subset K_3\), connected full little Julia sets, and pairwise disjoint **physical** phase sets at both scales under explicitly imported Rouché and Riemann–Hurwitz.

There are two real fixed points of \(f\):
\[
\alpha=(1-\sqrt{1-4c_{\rm tip}})/2<0,\qquad
\beta=(1+\sqrt{1-4c_{\rm tip}})/2>0.
\]
The real negative fixed point \(\alpha\) is dividing: the **two** periodic ambient rays of angles \(1/3,2/3\) land at it and are interchanged by \(f\). This uses the standard real-quadratic dividing-fixed-point and subhyperbolic rational-ray landing theorem; it is **not** inferred from checking \(2(1/3)=2/3\) alone. Their common preimage \(\alpha'=-\alpha>0\) receives rays \(1/6,5/6\). Exact rational signs for \(h(y)=y^2+y+c_{\rm tip}\) prove \(7/8<\alpha'<1\), whereas the critical value \(x_2=f^2(0)>1\) is strictly right of \(\alpha'\). Therefore, for the central depth-one piece bounded between \(\alpha\) and \(\alpha'\), \(x_2\notin Y^1\) and belongs to the right-hand off-critical piece \(Z^1_\kappa\). The **first** escape index is \(n=1\), with \(q=2\).

Thus the *top-puzzle*, rather than any abstract 3/9 clock identification, has
\[
\boxed{P=Y^1,\quad V^0=Y^3,\quad q=2,\quad n=1,\quad
\operatorname{depth}(Q_L)=\operatorname{depth}(Q_R)=3.}
\]
At \(n=1\), the “deep” branch time \(nq=2\) happens to coincide with the shallow time \(q=2\); the distinction persists in the source's theorem but not numerically in this example. The primitive physical return periods **3 and 9 are entirely different clocks**.

The nontrivial real vertices of the central \(Y^3\) pullback satisfy \(f^2(\pm t)=\alpha'\) for a root \(t\in(5/16,7/16)\). The signs \(f^2(5/16)>1>\alpha'\) and \(f^2(7/16)<7/8<\alpha'\) prove this bracket by IVT. In particular \(I_3\subset U_3\subset(-t,t)\) is **not** concluded: \(I_3=[x_6,x_3]\) is indeed inside \((-t,t)\) by rational bounds, but \(U_3\) is a complex disk and no identity of complex domains is claimed. The existing complex phase separation and primitive first return for the period-3 and period-9 physical restrictions are distinct from proving the entire **modified principal nest** in KL's chosen puzzle.

### The second top puzzle belongs to \(G=f^3\), not to \(f\)

A second application of the source's *top-puzzle algorithm* must use the actual degree-two polynomial-like map \(G=f^3:V_3\to U_3\), not the ambient \(f^6\) ray map. The analytic Rouché and critical-exclusion theorem in the preceding complex audit gives precisely this degree-two restriction, so \(G\) has its own external marking and \(G\)-internal rays by straightening. These are **not** identified with arbitrary ambient \(f\)-rays.

The new finite Lean theorem `inner_return_kl_fixed_and_vertex_brackets` checks that \(G(a)=a\) has a root \(a\in(3/32,1/10)\) on the positive real axis; the exact interval derivative inequality in the independent checker shows \(G'(a)<-1\). Evenness gives the other preimage \(-a\). Strict signs locate a positive preimage \(b_G\in(17/100,7/40)\) with \(G(b_G)=-a\), and the central depth-three vertices \(\pm t_G\), where \(G(t_G)=b_G\), satisfy \(1/32<t_G<1/16\). The original critical orbit satisfies \(G^2(0)=x_6<-1/10<-a\), so the first \(G\)-critical escape is again \(q_G=2,n_G=1\); the candidate second top pieces have \(P_G=Y_G^1\), \(V^0_G=Y_G^3\), and depth-three univalent \(G^2=f^6\) branches. The **terminal next renormalization** is the separate \(G^3=f^9\) return.

An additional *full complex* exclusion is finite-certified: \(\mathrm{Re}\,G(D(0,1/32))>7/40\). All potential central \(G^2\)-preimages of \(a\) lie between \(-7/40\) and \(7/40\), so no \(G^3\)-preimage of \(a\) can lie inside \(U_9\). This separates the second-scale top-puzzle vertices from \(K_9\) without pretending that the full nested KL **modified principal nest**, its landing prime-end side-markings, or the canonical localization of \(G\) has been built. The \(G\)-external ray table at this second scale remains to be source-marked and lifted; it cannot be copied from the ambient \(f\)-angle table above.

## 3. Actual source-facing ray/puzzle vertices (partial table)

Angles are ambient Böttcher dynamical angles; the landing assertions for the fixed/preperiodic rays use classical rational-ray landing and real-symmetric pullback, *plus* separation of the relevant real preimages. The table tracks **known top-puzzle vertices only**, not unbuilt Paper-1 localization prime ends.

| Point | Exact real location | Known ambient landing rays | Forward image | Puzzle role | Prime-end / sheet side |
|---|---|---|---|---|---|
| \(\alpha\) | negative dividing fixed point | \(1/3,2/3\) | fixed | \(Y^0,Y^1\) dividing vertex; \(Q_L\) attachment | NOT assigned |
| \(\alpha'=-\alpha\) | \((7/8,1)\) | \(1/6,5/6\) | \(\alpha\) | \(Y^1\) vertex; \(Q_R\) attachment | NOT assigned |
| \(-t\) | \((-7/16,-5/16)\) | \(7/24,17/24\) | negative real preimage of \(\alpha'\) | one \(Y^3\) vertex | NOT assigned |
| \(+t\) | \((5/16,7/16)\) | \(5/24,19/24\) | same negative real preimage of \(\alpha'\) | other \(Y^3\) vertex | NOT assigned |

The finite angular identities (doubling \(1/3\leftrightarrow2/3\), \(1/6,5/6\mapsto1/3,2/3\), and the 24-denominator pullback patterns) are checked in [TipKLPuzzle.lean](../../TipKLPuzzle.lean) and [the exact Python checker](verify_tip_kl_puzzle.py). **Neither code file proves landing or identifies the angles as particular prime ends**: the analytic assertion requires the standard noncritical local inverse branches, real cyclic order, and the graph's Jordan boundaries. The KL Yoccoz construction plus Lemma 2.1 supplies *theoretical* closed disjointness of the two \(Q^v\) in the valid source setting; it does **not** license equating these with the round-disk return domains \(V_3,V_9\).

## 4. Certified mismatch in the actual localization *target complements*

This is the strongest new first-failure result and does not depend on a guessed coset label.

Put \(K_p\) for the **actual** little filled Julia set of \(f^p:V_p\to U_p\) for \(p=3,9\), and
\[
B_3=\bigcup_{j=0}^{2}f^j(K_3),\qquad
B_9=\bigcup_{j=0}^{8}f^j(K_9).
\]
The existing *physical refinement* gives \(B_9\subset B_3\). Take a common ambient Jordan/equipotential domain \(U^0\) containing the full \(K(f)\) (the kind of ambient base used in Kahn I's canonical localization; do **not** substitute either tiny round disk \(U_p\) for this \(U^0\)). The target complements for the two **separate** primitive stages have the underlying sets
\[
\Omega_{t,3}=U^0\setminus B_3,\qquad
\Omega_{t,9}=U^0\setminus B_9.
\]
They satisfy the **opposite** inclusion to any naïve “forget nine-scale obstacles to three-scale obstacles” arrow:
\[
\boxed{\Omega_{t,3}\subset\Omega_{t,9}.}
\]
The inclusion is strict, with an explicit rational witness
\[
\boxed{z_*=\frac{31}{1024}.}
\]
Indeed, the Lean theorem `obstruction_point_in_outer_real_interval_not_V9` proves \(x_6<z_*<x_3\), so \(z_*\in I_3\subset K_3\subset B_3\), and also \(27/1024<z_*<1/32\), so \(z_*\notin V_9\supset K_9\). The theorem `obstruction_point_outside_all_noncentral_nine_phases` further checks the strict disk inequalities for **every** \(j=1,\ldots,8\), using the existing certified dyadic majorant \(\operatorname{deviation}(27/1024,j)\). Thus \(z_*\notin f^j(K_9)\) for all nine phases, and \(z_*\in B_3\setminus B_9\) is **actual complex-dynamical geometry**, not merely symbolic.

Consequently \(z_*\in\Omega_{t,9}\setminus\Omega_{t,3}\). The identity on the physical plane **does not even define a map**
\[
\Omega_{t,9}\longrightarrow\Omega_{t,3}.
\]
In particular, a proposed based covering map in that direction cannot simply be “the lift of the identity inclusion”; Kahn's standard lifting criterion \((a_*)H_s\subset H_t\) applies only *after an actual continuous base map \(a\) has been constructed*. There is an honest **first failing source-domain obligation** for the **naïve inclusion-based candidate**. This is **not** a proof that *every conceivable source-defined marked 9→3 transition is impossible*; a non-identity base map, a restriction of the source complement, or a more elaborate correspondence may exist.

## 5. A genuine one-stage source-localization collision, not an interstage one

The [prior paper-1 source audit](../mlc_unified/kl_canonical_localization_forced_collision.md) proves a general **one-stage** Kahn localization collision at a primitive connected little Julia set. The present tip gives a concrete extra physical inverse component in the **period-three** stage: exact rational interval signs show
\[
f^3(1)<0<f^3(9/8).
\]
Hence a real \(r\in(1,9/8)\) has \(f^3(r)=0\in K_3\). Since \(r>1>1/4\), \(r\notin K_3\), while the complex phase-1 and phase-2 enclosures of \(f(V_3)\) and \(f^2(V_3)\) exclude \(r\); thus \(r\notin B_3\). The connected component \(X\subset (f^3)^{-1}(K_3)\) containing \(r\) is an *extra component*, disjoint from the central \(K_3\). Under the existing source theorem, a based loop around \(X\) in
\[
\Omega_{s,3}=U^3\setminus (f^3)^{-1} B_3
\]
is nontrivial in \(\pi_1(\Omega_{s,3})\) and lies **outside** its local source subgroup \(H_{s,3}\), but contracts after inclusion in \(U^0\setminus B_3\) (where \(X\) is not removed). This gives an honest **one-stage** coset collision by the Kahn subgroup-reflection criterion, provided the global ordinary quadratic-like domains and local Jordan neighborhoods are taken as in that theorem. Separately, the six signed rational inequalities in `three_nested_preimage_brackets` give three consecutive actual real inverse branches of \(G=f^3\): \(s_1\in(1,17/16)\) with \(G(s_1)=0\), \(s_2\in(6/5,49/40)\) with \(G(s_2)=s_1\), and \(s_3\in(31/25,5/4)\) with \(G(s_3)=s_2\). Thus \(f^9(s_3)=0\in K_9\). The exact `period_nine_extra_preimage_outside_all_phases` theorem excludes the **entire** \(s_3\) bracket from all nine \(f^j(V_9)\), yielding a second one-stage extra inverse component at period nine. Neither bracket, by itself, constructs the relative loops and local covers of the source theorem, and neither witnesses the sought *interstage* 9→3 groupoid functor.

## 6. Remaining KL acceptance gates and a safe route to closure

1. The finite top-puzzle \(q=2,n=1\) and the source \(P,V^0,Q_L,Q_R,Q^v\) have a compelling **source-level candidate**. A full topological certificate must still specify the actual finite equipotential arcs, critical graph avoidance at every needed depth, a **closed** Jordan pullback proof for the exact phase tree, and the *modified principal-nest stopping times* matching \(p=3\) then \(g_3\)-period 3 (\(f\)-period 9). The existing `U_p,V_p` restrictions are not that selected puzzle.
2. The table lacks authenticated KL **prime-end side labels** \(O,\xi,\eta\), all proof-used depths, based path classes, and complete ray/access enumeration.
3. The 9-to-3 identity-based target-complement transition is demonstrably **undefined** at \(z_*\). To repair it, construct a separately source-defined map between appropriately restricted marked complements and prove naturality of all localization subgroup/groupoid data; then test whether the earlier distinct Levin ray values \(\Pi_3(114/511)=5/7\), \(\Pi_3(397/511)=2/7\) versus \(\Pi_9=0\) lift to an *actual KL prime-end/coset* identification. The angular data alone do not.
4. The older period-27 superattracting center's exact triple-airplane **component identity** remains separately conditional on a cited tuning/real-kneading rigidity theorem, and that center fails \(K(f)=J(f)\) regardless.
5. Leave the source-locked **465-entry MLC ledger**, H1–H4, UPTCR and MLC unchanged. No claims of source-localized 9→3 sheet functor or universal global closure.

### Reproduce and trust

```sh
lake build TipKLPuzzle TipComplexMargins
python research/independent_audits/verify_tip_kl_puzzle.py
python research/independent_audits/verify_tip_complex_domains.py --check-manifest
```

Lean recomputes integer/dyadic margins, not inverse Böttcher maps, ray landing, or KL localization. Python uses exact standard-library fractions. Classical imported topological and analytic inputs are cited above; peer review is still recommended.

**Attribution:** audit, finite arithmetic, and branch implementation produced with OpenAI GPT-6 assistance; neither original authors nor independent referees are represented as having reviewed this argument.
