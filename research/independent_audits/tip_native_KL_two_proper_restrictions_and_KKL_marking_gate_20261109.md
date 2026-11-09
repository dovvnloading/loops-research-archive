# A genuine two-channel proper-path restriction in the ORIGINAL KL W→V inclusion

**2026-11-09. Research status: rigorous source-defined obstruction to *unconditional* singleton proper restriction, NOT a counterexample to the KKL marked theorem.** This note directly attempts the remaining Issue #62 proper-path gate by working with the **actual** Kahn–Lyubich \(\Psi_G(W)\to\Psi_G(V^0)\) immersion, rather than a synthetic circle automaton or a chosen finite coset label. It supplies an explicit proper target path with two distinct proper source restrictions and a sharp original-side **proper-tail / interior-collapse** refinement.

The source category matters. In Kahn–Kapiamba–Lyubich (2026), Appendix A.3.2, the restriction \(\iota^*\gamma\) of a proper path is **defined as a set** of proper source paths, not intrinsically as a single path. Their *marked* pullback and combinatorial action additionally require selected ideal markings, path subordination, and refinement conditions (Appendix A.1, A.3.2, Proposition A.12). The theorem below **does not contradict** their theorems or prove that a proof-used marked path fails. It disproves the **stronger, tempting but invalid** assertion that all actual KL naturality immersions admit at most one proper source restriction for every proper target path. It gives an actual repeated source-channel fiber that any subsequent KKL marking must retain or explicitly rule out.

## 1. The actual original KL surfaces and source-locked geometry

Let \(G=f_{c_*}^3\) be the nonattracting second-stage quadratic-like restriction certified by the archive. The genuine *geometric* first child and parent are

\[
W_G=\operatorname{int}Y_G^6\Subset V_G=\operatorname{int}Y_G^3.
\]

Kahn–Lyubich, *A priori bounds II: Decorations*, §3.2.1, Lemma 3.3, build the ordinary **pseudo-pieces** \(\mathcal W=\Psi_G(W_G)\) and \(\mathcal V=\Psi_G(V_G)\) by gluing one **universal cover of the real G-carrier annulus** to each genuine exterior component of the geometric source piece. Lemma 3.4(ii) supplies an actual holomorphic inclusion *immersion*

\[
\boxed{\iota:\mathcal W\longrightarrow\mathcal V,}
\]

not a globally injective embedding. Source §3.2.4 names the original inner ideal \(J\)-sides \(\xi_i,\eta_i\), finite vertices, and outer ideal \(O\)-sides \(\lambda_i\).

Fix the real-symmetric source **topological** G external angle-height marking; it is *not* being declared a conformal Böttcher coordinate for the physical \(f^3\). With the original initial geometric potential height \(h>0\), the carrier universal strips have heights

\[
H_6=h/32,\qquad H_3=h/4.
\]

The actual 4 original W seam intervals, in units of \(1/192\), are

\[
W_0:(41,43),\quad W_1:(53,55),\quad
W_2:(137,139),\quad W_3:(149,151),
\]

and the 2 original V-parent seam intervals are

\[
V_0:(40,56),\qquad V_1:(136,152).\tag{1}
\]

These are exactly the original-source `results/tip_kl_side_atlas.json` records, **not** invented witness sectors. Their strict nesting is

\[
L_p<a_j<b_j<U_p,\qquad p=\lfloor j/2\rfloor,
\tag{2}
\]

where \((L_p,U_p)\) is the V seam and \((a_j,b_j)\) its W child seam. The original based W→V tile routes are **exactly**

\[
\boxed{W_0,W_1\mapsto V_0,\quad
       W_2,W_3\mapsto V_1,\quad
       \text{all four integer lift shifts}=0.}\tag{3}
\]

Each source W universal tile copy \(\widehat A_{6,j}\) thus maps by the universal lift of the **same physical carrier inclusion** \(A_6\hookrightarrow A_3\) into its source V-parent universal tile \(\widehat A_{3,p}\). On the chosen source topological uniform-cover strip coordinates, this map preserves the *same* unwrapped \(x\), physical ray height and full integer deck charge. Therefore for **any** positive-height universal-cover carrier point at a common \((x,t)\in\mathbb R\times(0,H_6)\), the points in the two source W tiles \(2p,2p+1\) have **equal target images** under \(\iota\), while they remain distinct points of \(\mathcal W\) by original KL Lemma 3.3 (disjoint tile images in the glued source pseudo-piece).

This is an actual source map identity on a full open carrier, not an inference from the two ray-access labels alone.

## 2. Main theorem: infinitely many *proper target paths* have two proper restrictions

**Theorem 2.1 (source-native failure of unconditional singleton proper restriction).** Let \(p=0,1\) index one of the source's genuine V-parent universal-cover tiles. For any integer \(m\ge0\) and \(0<s<1\), set

\[
x_m(s)=-m+(2m+1)s,\qquad
t(s)=4\varepsilon s(1-s),\quad \varepsilon=h/128>0,
\]

and let

\[
\boxed{\gamma_{p,m}(s)=(x_m(s),t(s))
\in\widehat A_{3,p}\subset\mathcal V.}\tag{4}
\]

Then:

1. \(\gamma_{p,m}\) is a genuine **proper path in the ideal-circle sense** of KKL Appendix A (not merely a path escaping compact sets). Its two distinct endpoints are the original target \(V_p\) ideal J-side points \((\xi_p,x=-m)\) and \((\eta_p,x=m+1)\), *strictly inside the sides*.
2. The **two** source paths in the genuine original W universal tiles \(j=2p\) and \(j=2p+1\), defined by the *same* coordinate formula (4), are distinct proper source paths \(\gamma_{j,m}'\in\mathcal W\). Their endpoints lie strictly inside the source \(\xi_j\) and \(\eta_j\) J-sides at the same respective unwrapped angles \(-m\) and \(m+1\).
3. They are **literal proper restrictions** of one target path:
   \[
   \boxed{\iota\circ\gamma_{2p,m}'
          =\gamma_{p,m}
          =\iota\circ\gamma_{2p+1,m}'.}
   \tag{5}
   \]
   Consequently, applying the *set-valued* restriction definition of KKL Appendix A.3.2,
   \[
   \boxed{\{\gamma_{2p,m}',\gamma_{2p+1,m}'\}
     \subseteq\iota^*\gamma_{p,m},\qquad
     \#(\iota^*\gamma_{p,m})\ge2.}\tag{6}
   \]
   No assertion of exact cardinality of the **entire** set of all proper restrictions is needed.
4. The construction is valid for **every \(m\ge0\)**, providing two distinct source restrictions for infinitely many explicitly described proper target paths in each original V parent. Their original source/target endpoint prime ends vary with \(m\) and retain their entire integer winding; no finite-sheet quotient is taken.

**Proof.** For \(0<s<1\), \(0<t(s)\le\varepsilon=h/128<H_6=h/32<H_3=h/4\). Hence (4) is a path entirely inside the genuine **source and target annular universal covers**, not an unspecified path near a chosen physical drawing. Its unwrapped angle is strictly increasing from \(-m\) to \(m+1\), so it is a simple curve inside each universal strip. As \(s\downarrow0\) and \(s\uparrow1\), its positive height tends to zero, while \(x_m(s)\) tends respectively to the **finite** strip ideal angles \(-m\) and \(m+1\). The source KL §3.2.4 strip/ideal-side identification guarantees continuous extension at both ends into the corresponding source and target *ideal circles*. Because the target and W side endpoints satisfy (2), and \(m\ge0\),

\[
-m\le0<L_p<a_j,\qquad
m+1\ge1>U_p>b_j,
\]

these endpoints are strictly in the original \(\xi\) and \(\eta\) ideal J-sides of **both** original W tiles and of the V parent. Thus the two W curves and the V curve are *proper* under the actual KKL ideal-end definition.

The **source-certified zero integer lift shift** (3) says that applying the original KL inclusion immersion to either W curve produces *exactly the same V universal-cover coordinate curve*, giving (5). KL Lemma 3.3 says different universal tiles of the glued W pseudo-piece are distinct source objects. As \(W_{2p}\) and \(W_{2p+1}\) are distinct and have disjoint tile images, their two entire proper paths are distinct. By the **literal** KKL Appendix A.3.2 definition of restriction as the set of proper source paths contained in \(\iota^{-1}(\gamma_{p,m})\), both belong to \(\iota^*\gamma_{p,m}\). This proves (6). \(\square\)

**Independent source check.** The previously merged exact ordinary KL source atlas already proves a finite collision at the unwrapped **\(11/48\)** between the distinct \(\eta_0\) and \(\xi_1\) side objects, whose images are the same point in the central interior of \(\Psi_G(V^0)\). The present proper-path theorem is different: (4) is **proper at both ends in the target V**, and both source restrictions are also proper. The certified \(11/48\) collision supplies a separate internal consistency check on the same source tile overlap, not a substitute for the path proof.

### Proposition 2.2 — the two restrictions even pass the *basic* KKL A.1 marked-path test

Equip the **actual** V pseudo-piece ideal circle with the six open intervals given by the interiors of its original KL \(\xi_p,\lambda_p,\eta_p\) arcs (\(p=0,1\)), in source cyclic order, and the actual W pseudo-piece ideal circle with the twelve corresponding original open intervals (\(j=0,1,2,3\)). These are bona fide **explicit ideal markings in the sense of KKL Appendix A.1**, but are not asserted to equal the **different, proof-used** KKL Hubbard-tree marking or to satisfy KKL's immersion-pullback/refinement compatibility.

For each \(\gamma_{p,m}\) and its two proper W restrictions in Theorem 2.1, the starting endpoint lies strictly inside its own \(\xi\)-marked interval, the terminal endpoint strictly inside its \(\eta\)-marked interval, and **between those two original marked intervals lies the nonempty original \(\lambda\)-interval**. They are therefore *nonadjacent* ideal marking intervals: every connected multi-interval containing both must include at least three original marked intervals (\(\xi,\lambda,\eta\) along the shortest boundary direction; the opposite direction is no shorter). Hence none of these three paths can be subordinate to a multi-interval of combinatorial length **at most two**. They are not only proper paths but are **paths in the respective source-defined marked surfaces \((\mathcal V,\mathcal I_{\rm KL,V})\) and \((\mathcal W,\mathcal I_{\rm KL,W})\)** under the literal KKL Appendix A.1 test.

**Proof.** The original KL §3.2.4 cyclic boundary order in one tile is \(\xi_j,\lambda_j,\eta_j\) up to reversal. The source endpoints \(x=-m\) and \(x=m+1\) are strictly interior to \(\xi_j\) and \(\eta_j\) by Theorem 2.1. In both the six-arc V circle and the twelve-arc W circle, every connected union of at most two marked intervals is disjoint from at least one of these two endpoint intervals. A homotopy *relative to ideal endpoints* cannot change the endpoint intervals. KKL A.1's definition of subordinate path therefore rules out subordination to any such short multi-interval. This holds for every \(m\ge0\), in both source channels, and relies on the **original source cyclic ideal-side incidence**, not a finite transition automaton. \(\square\)

**The exact remaining marked obstruction:** KKL Appendix A.3.2 does **not** say that an arbitrary pair of well-defined ideal markings is compatible with the immersion. It requires the maximally defined \(\iota^*\mathcal I_{\rm KL,V}\), when it exists, and a source refinement; it then ignores restrictions subordinate to a single pullback interval. Since the full original W \(\xi/\eta/\lambda\) arcs contain *genuine open interior-collapse subarcs* (next section), their full original marking cannot simply be declared an **end-proper pullback marking**. Thus Proposition 2.2 strengthens the example beyond unmarked paths, **but still is not a refutation of KKL Proposition A.12 or its unique-subordinate conditional**. One must calculate the actual pullback marking and its selected restrictions to decide that question.

## 3. A sharper *boundary-to-boundary versus interior-collapse* original side decomposition

Let \((L_p,U_p)\) be the source V-parent seam and \((a_j,b_j)\) the W child seam (1)–(2). Original KL Lemma 3.4(ii) and §3.2.4 imply the following exact behavior of the **continuous ideal extension of the actual W→V inclusion** on each original source W universal tile \(j\):

| Source W ideal part | Image in original V pseudo-piece | KKL-related consequence |
|:--|:--|:--|
| \(\xi_j:\ x\le L_p\), including the \(-\infty\) wrapping end | target \(V_p\) ideal \(\xi_p\), same unwrapped \(x\) | a source **closed proper tail** maps homeomorphically to a target ideal closed arc |
| \(\xi_j:\ L_p<x<a_j\) | **central interior of V** | whole \(\xi_j\) **cannot** be proper into target ideal boundary |
| \(\eta_j:\ b_j<x<U_p\) | **central interior of V** | whole \(\eta_j\) **cannot** be proper into target ideal boundary |
| \(\eta_j:\ x\ge U_p\), including the \(+\infty\) wrapping end | target \(V_p\) ideal \(\eta_p\), same unwrapped \(x\) | a source **closed proper tail** maps homeomorphically to a target ideal closed arc |
| \(\lambda_j^\circ\): finite outer carrier height \(H_6\) | **ordinary interior of V** because \(H_6<H_3\) | whole \(\lambda_j\) **cannot** map properly into the target ideal boundary |
| \(\omega_j^\pm\), original infinite wrapping joints | target \(V_p\) wrapping joints \(\omega_p^\pm\) | proper *source-to-source-ideal* endpoints are retained by the inclusion, even though the later fine-localization map does not extend there |

The source W side half-lines in this table are **genuine original KL \(\xi/\eta\) sides**. The "closed proper tail" assertions use the actual continuous extension from KL §3.2.4, and the coordinate \((x,t)\) on the source universal covers: the closed source ideal subarcs \([-\infty,L_p]\subset\xi_j\) and \([U_p,+\infty]\subset\eta_j\) map by \(\iota\) **homeomorphically** onto the target \(\xi_p\) and \(\eta_p\) ideal subarcs, respectively. In particular these are genuinely proper continuous maps on the indicated *compact* closed subarcs, rather than assertions based on winding-vector equality alone.

All original W full \(\xi_j,\eta_j\) and finite \(\lambda_j\) sides fail to be globally boundary-to-boundary under the inclusion: each has a nonempty *open subarc* mapped to **V interior**. For \(\xi_j\) the source exact witness interval is \((L_p,a_j)\); for \(\eta_j\) it is \((b_j,U_p)\). Every one of these **eight open intervals is strictly nonempty**, checked from (1), and the finite \(\lambda_j^\circ\) remain interior due the source carrier height. The original source is explicit that an inclusion immersion can send source boundary into target interior; this is a concrete decomposition of that phenomenon at all four actual W tiles.

These *proper tails* are candidate source **end intervals** for a KKL ideal marking. But merely finding closed proper tails does **not** prove that their full ideal-marking pullbacks \(\iota^*\mathcal I\) exist, are disjoint, give an admissible refinement, or select a unique proper restriction of a target **marked** path.

## 4. What this **refutes**, and what it emphatically does not

It **does refute**, for the actual source-defined KL immersion \(\Psi_G(W)\to\Psi_G(V^0)\), all of the following over-strong assertions:

- "Every target proper path has at most one proper source restriction" — false by the explicit **two complete source restrictions of (4)**, each with correct ideal endpoints.
- "The four original W tile labels can be collapsed to their two V-parent labels without retaining multiplicity for proper paths" — false for this explicit 2-channel fiber.
- "The inclusion is end-proper on every entire original W \(\xi,\eta,\lambda\) side" — false because every one contains a source-open subarc mapped into the original V **interior**.

It **does not refute** KKL 2026 Appendix A.3.2 or its Proposition A.12, which **deliberately** use a *set-valued* \(\iota^*\gamma\), require **selected ideal markings** and exact *subordination* and *refinement*, and permit **multiple restrictions/breakage**. Appendix A.1 further excludes some proper paths from a particular marked path category when they are subordinate to a multi-interval with combinatorial length at most two. Our \(\gamma_{p,m}\) have not been asserted to be admissible in any specific KKL \((V,\mathcal I)\) chosen for a proof-used wave. In particular our theorem is **not** a counterexample to an actually stated KL or KKL theorem, nor to an analytic proper-restriction hypothesis with those extra source predicates.

This gives a **precise first-failure certificate for a naive proof route**, not global MLC: in the exact original W→V source category, two properly endpointed distinct source paths survive over one proper target path. A valid *source-native* uniqueness proof must state which **one** of those source channels is selected by its marking/subordination hypotheses and why its other channel is excluded; or it must retain both in its interval/path accounting as KKL's set-valued formalism permits.

## 5. Next actual unresolved acceptance gate

**Construct the precise KKL marking \(\mathcal I\) on the target \(\Psi_G(V^0)\)** from proof-used ideal intervals and the actual source side incidence. On the source, begin with the eight proper closed tails \([-\infty,L_p]\) and \([U_p,+\infty]\) and the two-to-one occurrence data; then test:

1. Whether the **actual** inverse ideal marking \(\iota^*\mathcal I\) exists in KKL Appendix A.3.2's sense, including distinct endpoints, partial-marking disjointness and maximality — do not infer it from finite angle routes alone.
2. Whether each explicit \(\gamma_{p,m}\) is a *path in* \((\Psi_G(V^0),\mathcal I)\), rather than merely a proper path. KKL A.1's "not subordinate to a multi-interval of length at most two" clause is essential here.
3. Under an admissible source refinement, whether one, both, or neither of the two lifted proper paths survive the **exclusion** of restrictions subordinate to a single pullback interval.
4. The full actual **proper-end footprints**, all integer source deck charges, and any additional cross-component connector-word and endpoint occurrence data needed by KKL Proposition A.12. There is still no authenticated full nine-generator cross-scale connector table for the rest of Issue #62.

This is an executable research specification: an actual source-compatible marking and one exactly described proper target path can **prove or disprove** marked uniqueness without making unjustified assumptions about global circle quotients.

## 6. Source attribution, finite tests and trust boundary

Primary sources:

- **Kahn–Lyubich**, *A priori bounds for some infinitely renormalizable quadratics II: Decorations*, §3.2.1, Lemma 3.3, Lemma 3.4(ii), and §3.2.4, printed pp. 11–13: the actual path space, source universal-tile disjointness, natural inclusion immersion, and \(\lambda/\xi/\eta\) ideal boundary. https://arxiv.org/pdf/math/0609046
- **Kahn–Kapiamba–Lyubich**, *MLC for parabolically bounded primitive renormalization* (2026), Appendix A.1, A.3.2 and Proposition A.12, printed pp. 56–57, 63–64: ideal proper paths, **set-valued** immersion restriction, subordination and the precise selected interval action. https://arxiv.org/abs/2606.27272
- Existing source-authenticated archive: `research/independent_audits/tip_kl_pseudopiece_side_atlas_20261106.md`, source theorem 5.1 (\(11/48\) collision), `results/tip_kl_side_atlas.json`, merged PRs #60–66.

To reproduce at repo root:

```sh
python research/independent_audits/verify_tip_native_two_proper_restrictions.py --check-manifest
lake build TipNativeProperRestriction
```

The checker reads the **unchanged original source atlas** directly, independently derives the 8 strict child-in-parent inequalities and 8 source genuine side interior-collapse witness intervals, verifies all 4 original zero-shift tile routes, 4 closed proper-tail side correspondences (each twice), the original independent \(11/48\) source collision, and an adversarial finite regression of **128 exact target path parameter values and 256 source path-lift incidences**. A new Lean finite module proves the original strict nested child/parent seam inequalities and the necessary **all-nonnegative-integer** endpoint bounds. The infinite two-lift proper-path statement is a **written topological proof with original source citations**, not a Lean formalization of KKL path spaces or complex Riemann surfaces.

**Do not promote** H1–H4, UPTCR or MLC, alter the 465-entry ledger, or claim independent specialist proof validation/novelty. GPT-6 assisted the source comparison, proof synthesis, and exact certificate. The global original KL/KKL proof-used marked unique-restriction and the rest of Issue #62 remain **OPEN**.
