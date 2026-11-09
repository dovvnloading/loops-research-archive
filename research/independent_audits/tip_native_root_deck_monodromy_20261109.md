# Native KL root-landing ideal J-sides: one rooted lift, infinitely many proper nonroot lifts

**November 9, 2026 — source-specific mathematical audit for Issue #62.**
This is a theorem about the **actual ordinary** \`G=f^3\` Kahn–Lyubich W pseudo-piece at the archive's nonattracting real 3/9 Misiurewicz tip. It is not a full native interscale functor, not KKL unique-proper-restriction, and not a result toward closing H1–H4, UPTCR, or MLC. The analytic covering/prime-end assertions below are written proofs importing the source's original constructions; only exact finite angular facts have a machine certificate.

## 1. Typed objects and precise new result

Let \`K9⊂K3\` be the two certified nested, full physical filled sets; \`K9=[-p,p]\` is the interval root of the actual \`f^9=G^3\` return. The physical period-nine fine target, its marked canonical localization and exterior subgroup are

\[
T_9=U^0\setminus\bigcup_{(r,j)\ne(0,0)}D_{r,j},\qquad
D_{r,j}=f^{r+3j}(K_9),\qquad
\pi_9:(\widehat T_9,\widehat K_9)\longrightarrow(T_9,K_9),
\]
\[
\Omega_9=T_9\setminus K_9,\quad
\Gamma=\pi_1(\Omega_9)=F(b_{00},b_{01},b_{02},b_{10},\ldots,b_{22}),\quad
H=\langle b_{00}\rangle.
\]

The physical second-stage geometric first child \`W_G=int(Y_G^6)\` satisfies \`K9⋐W_G\` and \`W_G⊂T9\`. Its **ordinary source** pseudo-piece \`Ψ_G(W)\` is the Kahn–Lyubich (KL II, §3.2.1, Lemma 3.3) gluing of the *four* universal covers of the actual G-carrier annulus \`A_6=𝒰_G^6\setminus K3\` to the central geometric \`W_G\`, one per component of \`W_G\setminus K3\`. The important target map is the previously source-certified same-root immersion

\[
j_W:\Psi_G(W)\longrightarrow\widehat T_9,\qquad
\pi_9j_W=p_W.
\]

It agrees on the central geometric \`W_G\` with the holomorphic root section \`s_W\` constructed in merged PR #60. This is **not** the canonical-coarse native pseudo-piece used in the separate PR #37 comparison; nor is it an assumed map between complete compactified boundary circles.

For a source tile \`i∈{0,1,2,3}\`, the inherited positive G-angle-height strip coordinate on its **universal covering** is \`(x,t)\in R×(0,H_6)\`, with positive deck generator \`τ_i(x,t)=(x+1,t)\`. The actual source W open gluing seams are

\[
(a_i,b_i)=(41,43)/192,\ (53,55)/192,\ (137,139)/192,\ (149,151)/192.
\]

By KL II, §3.2.4 and the original source atlas, the finite remaining ideal J-side points on tile \`i\` are \`ξ_i: t=0,\ x≤a_i\` and \`η_i:t=0,\ x≥b_i\`. The open \`(a_i,b_i)\` portion is **glued into the central piece**, and is not a remaining J-side.

### Theorem A — a complete infinite *anchored deck-orbit* root classification

Take any one of the **eight** previously authenticated G rays with \`θ∈(a_i,b_i)\` in its original tile \`i\`, and its real physical landing \`q_θ∈K9\`. Let \`r_θ(t)\` be the physical G-exterior ray segment at small positive height, \`u_{i,0}(t)\` its central-gluing tile lift, and for \`n∈Z\`

\[
u_{i,n}(t)=\tau_i^n(u_{i,0}(t)).
\]

Then:

1. **Actual named finite J-side accesses.** For every \`n≥1\`, \`u_{i,n}(t)\` ends at a genuine finite \`η_i^\circ\` prime end of \`Ψ_G(W)\`, with unwrapped angle \`θ+n\`; for \`n≤-1\` it ends at a finite \`ξ_i^\circ\` prime end, with unwrapped angle \`θ+n\`. Its **physical projection lands at the same marked point** \`q_θ∈K9\`. These are neither open gluing-seam points nor the infinitely winding \`O/J\` joints.
2. **The only root-convergent lift is \`n=0\`.** The image \`j_W(u_{i,0}(t))=s_W(r_θ(t))\` converges to the marked point above \`q_θ\`. For every \`n≠0\`, \`j_W(u_{i,n}(t))\` does **not** converge to the marked root, and in fact has **no** accumulation point anywhere in the uncompactified fine canonical surface \`widehat T9\`.
3. **Every nonzero translate is a proper nonroot end.** For each fixed \`n≠0\`, \`j_W(u_{i,n}(t))\` escapes every compact subset of \`widehat T9\` as \`t→0\`, while \`π9j_W(u_{i,n}(t))=r_θ(t)→q_θ\`. Consequently \`j_W\` has **no continuous extension into \`widehat T9\` at any of these finite root-landing native J-side points**.
4. **All integer sheets are pairwise distinct.** For every fixed positive \`t\`, the infinitely many \`j_W(u_{i,n}(t))\`, \`n∈Z\`, are pairwise distinct points above exactly the same physical \`r_θ(t)\`.

Thus every one of the original eight \`ξ_i^\circ/η_i^\circ\` J-sides contains *two explicit* finite root-landing nonextendible points already at deck levels \`n=±1\` (16 witnesses), and infinitely many more. These are complementary to the **excluded-target** examples and **ordinary-exterior** locally extendible examples of draft PR #61; here the landing is in \`K9\`, so only the sheet obstruction can explain failure.

### Source-locked eight-anchor and sixteen-side table

All angles in the second through fourth columns are **G internal exterior angles**, not ambient physical \`f\`-ray angles. The landing and fine prime-end columns are the already certified PRs #55–60 data. Strict membership is rechecked against the genuine KL source atlas.

| Original W tile | Ray ID | Seam anchor θ | Finite ξ angle θ−1 | Finite η angle θ+1 | Fine Π9 | Physical K9 landing |
|:--|:--|:--|:--|:--|:--|:--|
| 0 | qR | 3/14 | −11/14 | 17/14 | 1/2 | −p |
| 0 | d | 25/112 | −87/112 | 137/112 | 3/4 | 0, lower |
| 1 | e | 31/112 | −81/112 | 143/112 | 3/4 | 0, lower |
| 1 | pR | 2/7 | −5/7 | 9/7 | 0 | +p |
| 2 | pL | 5/7 | −2/7 | 12/7 | 0 | +p |
| 2 | a | 81/112 | −31/112 | 193/112 | 1/4 | 0, upper |
| 3 | b | 87/112 | −25/112 | 199/112 | 1/4 | 0, upper |
| 3 | qL | 11/14 | −3/14 | 25/14 | 1/2 | −p |

### Proof of Theorem A

**(a) Native side type.** The source's topological annulus \`A_6\` has a universal-cover strip with translation \`τ_i\`. KL's gluing removes **only** the open interval \`(a_i,b_i)×{0}\` from the ideal J boundary of tile \`i\`. Because \`0<a_i<θ<b_i<1\`, every \`θ+n\` with \`n>0\` lies strictly above \`b_i\`, and every \`n<0\` lies strictly below \`a_i\`. These are genuine, distinct **finite** side prime ends (not the points at \`x=±∞\`). Integer translation does not change the physical ray projection, and the source-certified G ray \`r_θ\` lands at \`q_θ∈K9\`.

**(b) The source deck loop has a detectable non-root winding.** At any small positive height \`t\`, a horizontal strip path from \`u_{i,0}(t)\` to \`τ_i^n u_{i,0}(t)\` projects under \`p_W\` to \`n\` complete positive turns around the entire **coarse** carrier root \`K3\`. All three disjoint physical fine continua \`D_(0,0)=K9\`, \`D_(0,1)=G(K9)\` and \`D_(0,2)=G²(K9)\` lie in \`K3\`. Hence that actual based loop \`ℓ_{i,n}\` has exact integer winding

\[
\operatorname{wind}_{D_{0,1}}(\ell_{i,n})
=\operatorname{wind}_{D_{0,2}}(\ell_{i,n})=n. \tag{2.1}
\]

This is a homological statement about the **genuine carrier loop** in the physical \`Ω9\`, not a proposed identification of G straightening angles with conformal Böttcher coordinates on the physical plane. Depending on its based connector, the full free-group word of the loop is a conjugate of the coarse meridian \`β0^n\`; the source's prescribed global base paths must be specified before asserting a literal word in \`Γ\`. In the archive's fixed based peripheral convention \`β0=b00 b01 b02\`. The obstruction uses the invariant integer winding (2.1), and does not erase unknown conjugating words.

**(c) Based sheet separation for every \`n\`.** Use the distinguished sheet \`s_W(r_θ(t))\` at the loop basepoint. The based stabilizer of that sheet is the image of the *single fine root meridian* \`H_t\`, connected to the archived \`H=<b00>\` by a connector **inside \`W_G\setminus K9\`**. Every element of \`H_t\` has winding **zero** about each of \`D_(0,1)\` and \`D_(0,2)\`, because \`W_G\` avoids those fine obstacles. If \`j_W(u_{i,n}(t))=j_W(u_{i,m}(t))\` then the image of a source tile path between them would close under \`π9\`, forcing \`ℓ_{i,n-m}∈H_t\`. Equation (2.1) forces \`n=m\`. This proves all-sheet distinctness without a finite coset enumeration.

**(d) Root convergence and compact escape.** By original KL gluing, \`u_{i,0}(t)\` is identified with the central geometric ray segment for small positive \`t\`. The previous root-normalized section theorem therefore implies

\[
j_W(u_{i,0}(t))=s_W(r_θ(t))\longrightarrow \widehat q_θ
\in\widehat K9.
\]

Assume for \`n≠0\` that \`j_W(u_{i,n}(t_k))\` has a convergent subsequence in \`widehat T9\` for \`t_k→0\`. Continuity of \`π9\` and of the physical ray implies its limit lies over \`q_θ\`, and Kahn's marked localization has **one** point there, \`widehat q_θ\`. Kahn's projection is biholomorphic on a neighborhood of the *entire* marked root. For sufficiently large \`k\`, **both** the translated lift and \`s_W(r_θ(t_k))\` belong to this injective root chart and project to the same physical point, forcing equality. This contradicts (c). Thus the translated lift has **no** accumulation in \`widehat T9\` and must leave every compact set. Any continuous extension at its genuine source ideal prime end would supply precisely the excluded accumulation point. \`□\`

This is a **negative root-landing theorem** for all nonzero translates of the eight source-*anchored* rays. It does not compute the unrelated base-path defects of a ray taken from a different original W tile.

## 2. The exact *arbitrary connector* root-shift selector, once its word is known

The next theorem is general free-group theory and is independent of the source-specific gluing result. Its value is to replace an infinite search over coarse winding shifts by one forced candidate and an exact freely reduced word test.

**Theorem B (unique candidate and complete word criterion).** In the repository's based convention let

\[
\Gamma=F(b00,b01,b02,b10,\ldots,b22),\quad H=\langle b00\rangle,\quad
\beta_0=b00\,b01\,b02.
\]

For any fully specified **based connector defect** \`g∈Γ\`, the source-labeled fine cosets are \`Hβ0^n g\`, \`n∈Z\`. Exactly the following is equivalent to root convergence of a physical ray already known to land at \`K9\`:

\[
H\beta_0^ng=H
\quad\Longleftrightarrow\quad
\operatorname{red}(\beta_0^ng)\in\langle b00\rangle. \tag{2.2}
\]

If such an \`n\` exists, it is *necessarily unique* and

\[
\boxed{n=-\operatorname{wind}_{D_{0,1}}(g)
=-\operatorname{wind}_{D_{0,2}}(g).} \tag{2.3}
\]

The complete decision procedure is: compute \`n_*=-wind_D01(g)\`; compute the freely reduced word \`red(β0^{n_*}g)\`; return \`n_*\` if and only if that word is a power of \`b00\`, otherwise return **no root-compatible winding**. Additional zero-winding checks about the other generators may reject a word early, but are not by themselves sufficient.

**Proof.** If the coset is \`H\`, its representative is in \`H\`, where each \`D_(0,1)\`-winding is zero. The \`D_(0,1)\`-winding of \`β0^n g\` is \`n+wind_D01(g)\`, determining the unique candidate. That of \`D_(0,2)\` supplies the second equality. Conversely membership in \`H\` after exact free reduction is the definition of the root coset. For two putative solutions \`n,m\`, winding the quotient gives \`n=m\`. \`□\`

An adversarial example is the reduced commutator \`g=[b01,b02]\`: **every abelianized winding of g is zero**, so a winding-only test wrongly suggests \`n_*=0\`, but \`g∉H\`, and no n works. On the other hand \`g=β0^{-k}b00^m\` has precisely the root shift \`n=k\`. This is why the full nonabelian free word, not an independently chosen \`Z²\` proxy, is indispensable.

**Important gauge qualification.** Formula (2.2) uses the archive's fixed global based basis and exact right-monodromy convention. For the source tile deck loop alone, only a conjugacy class is fixed before choosing the KL prescribed connector into that global base. Theorem A does **not** assume those missing conjugating words are known: its source-native obstruction is the conjugacy-invariant \`D_(0,1)\`-winding. Theorem B is ready to process an actual \`g_θ\` as soon as it has been geometrically authenticated; it does **not** manufacture one.

## 3. Strict source-type boundaries and research consequences

- The original eight ray **anchors** live in open gluing seams and therefore are not ideal side points. The 16 unit deck **translates** are actual remaining finite \`ξ/η\` ideal prime ends, not artificial endpoint tags.
- The new obstruction occurs **above the marked fine root itself**. It is logically independent of draft PR #61's stronger *excluded physical phase* nonextension and its positive ordinary-exterior collar theorem; both remain valid in their distinct target categories.
- The Theorem A rays are *proper nonroot lifts* into the uncompactified fine canonical target. This establishes that **properness alone does not select the rooted sheet** on this cohort, but it does not decide the differently typed KKL unique-proper-restriction axiom.
- Theorem B addresses the algebraic decision problem **after** the defect word is given. In general it still remains necessary to compute the exact KL-prescribed \`κ'θ κθ^{-1}\` defects from the actual native source path groupoid, with no illicit traversal through \`K3\setminus K9\`.
- We do **not** claim an open interval of native J-side points landing in \`K9\`, a whole-circle side map, an all-θ classification across mismatched source tiles, or a globally proved analytic naturality theorem.
- There is no promotion of H1–H4, UPTCR or MLC, no ledger changes, and no assertion of specialist peer review or novelty/priority beyond this archive-specific construction.

## 4. Source references and verification

1. Kahn–Lyubich, *A priori bounds for some infinitely renormalizable quadratics II: Decorations*, §3.2.1, Lemma 3.3 (the path-space / universal-cover tile equivalence), §3.2.2, Lemma 3.4 (inclusion naturality), and §3.2.4 printed pp. 11–13 (the actual \`λ,ξ,η\` source ideal sides). https://www.math.stonybrook.edu/preprints/ims06-06.pdf
2. Kahn, *A priori bounds ... I*, arXiv:math/0609045v3, §7.4.1 Theorem 7.12 (marked localization, root-neighborhood biholomorphism). https://arxiv.org/pdf/math/0609045
3. Previously merged archive: \`tip_kl_pseudopiece_side_atlas_20261106.md\` §2,§4; \`tip_localization_refinement_peripheral_monodromy_20261106.md\`; \`tip_rooted_native_KL_section_and_four_tile_prime_end_cycle_20261108.md\` Theorems 2.2–2.3 and §4; and original manifests \`results/tip_kl_side_atlas.json\`, \`results/tip_nested_full_ray_census_20261107.json\`, \`results/tip_rooted_native_KL_section_20261108.json\`.

At repo root:

\`\`\`bash
python research/independent_audits/verify_tip_native_root_deck_monodromy.py --check-manifest
lake build TipNativeRootDeck
\`\`\`

The exact checker validates all eight anchor identities against the **original existing manifests**, all 16 one-step J-side translations, 320 additional nonzero sheet samples, and the nonabelian selector against **all 4,687 freely reduced words of length at most five over the three relevant generators**. Lean checks the strict original rational W seam containment and both genuine J-side displacement inequalities; it does not formalize complex covering spaces, KL prime ends, Carathéodory landing or Kahn's localization. Those source-imported analytic steps are the written proof above. This work was prepared with GPT-6 assistance and awaits independent mathematical specialist review.
