# A holomorphic rooted KL-core embedding and the four-tile prime-end cycle at the actual 3/9 tip

**November 8, 2026. Status:** New *positive all-puzzle-core theorem*, with a sharp *all-other-component* converse, for the exact real nonattracting period-3/9 Misiurewicz parameter of this archive. This moves beyond enumerating ray angles or classifying individual lifts. It constructs an actual coherent holomorphic section of the **fine canonical localization** on the whole source-defined second-stage KL geometric puzzle cores `P_G`, `V_G^0`, and `W_G`; recovers the authentic period-nine polynomial-like dynamics on the embedded central pair; classifies **every** alternative annular covering component using an infinite free-product malnormality theorem; and resolves the eight surviving physical ray accesses into the four **original W tile gluing channels** and their complete adjacent-tile cycle.

The theorem is NOT a whole native pseudo-piece embedding or a map of complete KL `O/xi/eta` ideal sides. The finite tile table is exact and Lean-checked; the infinite group, analytic root-section and prime-end theorems are explicitly written mathematical proofs importing the source's genuine physical-domain geometry and Kahn's localization theorem. H1–H4, UPTCR and MLC remain **OPEN**.

## 1. Actual physical setting and the missing interface

Let `f=f_{c_*}(z)=z²+c_*`, at the archive's exactly isolated twice-airplane-tuned Misiurewicz parameter, and write `G=f³`. The source's two authentic, connected degree-two polynomial-like returns have compact nested full filled sets `K9⊂K3`. Moreover

\[
K_9=[x_9,x_{18}]=[-p,p],\qquad p=x_{18}=-x_9>0.\tag{1.1}
\]

The interval identity, not an assumed drawing, is proved in [`tip_interval_root_and_marked_morphism_obstruction_20261106.md`](./tip_interval_root_and_marked_morphism_obstruction_20261106.md) using Douady–Hubbard straightening to the exact Chebyshev parameter `-2`. The nine sets

\[
D_{r,j}=f^{r+3j}(K_9),\qquad r,j\in\{0,1,2\},\tag{1.2}
\]

are pairwise disjoint physical real intervals. Let `U⁰` be the source's common bounded outer disk and put

\[
\Omega_9=U^0\setminus\bigcup_{r,j}D_{r,j},\qquad
T_9=\Omega_9\cup K_9.\tag{1.3}
\]

Kahn's genuine **fine canonical localization**

\[
\pi:(\widehat T_9,\widehat K_9)\longrightarrow(T_9,K_9)\tag{1.4}
\]

has exterior covering `π: \widehat Ω9 → Ω9`, subgroup `H=<b_{0,0}>` in the based free group

\[
\Gamma=\pi_1(\Omega_9)=F(b_{r,j}:0\le r,j<3).\tag{1.5}
\]

It is bijective on the compact marked root and biholomorphic on **a whole neighborhood** of that root; this is Kahn, *A priori bounds ... I*, arXiv:math/0609045v3, §7.4.1, Theorem 7.12 and proof. The exact physical meridians and correct nonnormal left-coset conventions were proved in [`tip_localization_refinement_peripheral_monodromy_20261106.md`](./tip_localization_refinement_peripheral_monodromy_20261106.md), §2–5, and the full two-charge sheet analysis was merged in [PR #59](https://github.com/dovvnloading/loops-research-archive/pull/59).

The second **ordinary** KL puzzle is based on `G=f³`. The source's actual landed `G`-internal tree has nested geometric Jordan disks (we always mean their **open interiors**)

\[
\boxed{W_G=\operatorname{int}Y_G^6\Subset
 V_G=\operatorname{int}Y_G^3\Subset
 P_G=\operatorname{int}Y_G^1.}\tag{1.6}
\]

The source proves `K9⊂⊂W_G`, `G³=f⁹:W_G→V_G` proper of degree two, and **each entire geometric disk** in (1.6) lies in `T9` and avoids the other eight fine-cycle obstacles. The second-stage phase-avoidance argument is given in [`tip_kl_pseudopiece_side_atlas_20261106.md`](./tip_kl_pseudopiece_side_atlas_20261106.md), §4; the return and compact nesting in [`tip_kl_terminal_first_child_20261106.md`](./tip_kl_terminal_first_child_20261106.md), §1–5. This source range check is essential: **a generic same-plane puzzle disk need not avoid the other fine obstacles**.

We abbreviate any of these three actual disks by `Y`. Put

\[
A_Y=Y\setminus K_9,\qquad j_Y:A_Y\hookrightarrow\Omega_9.\tag{1.7}
\]

Because `Y` is a Jordan disk and the nondegenerate interval `K9` is compactly in its interior, `A_Y` is a connected doubly connected plane region, with `π1(A_Y)≅Z`. The positive root-peripheral loop in `A_Y` maps under `j_Y` to the genuine fine meridian `b_{0,0}`, after using the source's root-compatible based connector. In particular

\[
\boxed{(j_Y)_*\pi_1(A_Y)=H=\langle b_{0,0}\rangle.}\tag{1.8}
\]

This is NOT the coarse peripheral `β0=b00 b01 b02`, which winds around **all three** fine obstacles lying in `K3`. The distinction drives every theorem below.

## 2. A sharp theorem: all rooted sections and all nonroot components

The following is general covering theory and can be applied later to other actual nested polynomial-like sources. Its use here depends on (1.4)–(1.8).

### Lemma 2.1 — a free peripheral factor is malnormal, not merely nonnormal

In `Γ=H*F(b01,b02,b10,...,b22)` with `H=<b00>`, for **every** `g∈Γ\H`,

\[
\boxed{H\cap g^{-1}Hg=\{1\}.}\tag{2.1}
\]

**Proof.** Use the reduced free-product normal form. Left- and right-multiply `g` by powers of `b00` to obtain a reduced double-coset representative `v` whose first and last syllables lie in the complementary free factor, and which is nonempty because `g∉H`. If `h=b00^m∈H` with `m≠0`, the word `v^{-1}hv` is reduced at the central `H` syllable and has nontrivial complementary syllables at both ends. It cannot belong to `H`. Conjugation by the stripped `H` powers does not change membership in `H`, proving (2.1) for every `g` and every `m`. This uses all free words, including commutators with **zero abelianization**, not a finite winding enumeration. `□`

### Theorem 2.2 — one rooted *one-sheeted* component, every other component universal

For each `Y∈{P_G,V_G,W_G}`, the connected components of the full preimage `π^{-1}(A_Y)` are indexed by the **non-group** double-coset set

\[
\boxed{H\backslash\Gamma/H.}\tag{2.2}
\]

The unique component indexed by `H` (the one approaching the marked root) maps **biholomorphically** onto `A_Y`. Every other component maps as the **universal holomorphic covering** of `A_Y`, with infinitely many sheets over every point. There are countably infinitely many nonroot components.

**Proof.** The pullback-component theorem for a cover with based subgroup `H` and included subspace subgroup `B=(j_Y)_*π1(A_Y)=H` indexes components by `H\Γ/B`, hence by (2.2). The subgroup of a component represented by `HgH` pulls back from

\[
 B\cap g^{-1}Hg=H\cap g^{-1}Hg.\tag{2.3}
\]

For `g∈H`, (2.3) is all of `B`, so the connected component has covering degree one. For `g∉H`, Lemma 2.1 gives the trivial subgroup, so the component is universal. Holomorphicity follows from the actual holomorphic covering charts. For countability, `Γ` is finitely generated and hence countable. Distinct nonroot double cosets `H b01^k H`, `k=1,2,...`, are separated by winding about `D_{0,1}`; therefore infinitely many components exist. `□`

The theorem classifies **all** components, not merely the previously exhibited two-coordinate sheet sublattice. In particular the `Z²` examples of PR #59 lie among these full, nonnormal component orbits; they are not incorrectly promoted into a quotient group.

### Theorem 2.3 — a genuine holomorphic rooted section of the **whole geometric puzzle disk**

For each of the actual disks `Y=P_G,V_G,W_G` there is a **unique holomorphic embedding**

\[
\boxed{s_Y:Y\hookrightarrow\widehat T_9,
\quad\pi\circ s_Y=\operatorname{id}_Y,
\quad s_Y(K_9)=\widehat K_9.}\tag{2.4}
\]

It is the prescribed inverse of Kahn's projection on the root-neighborhood chart, not a freely chosen external covering sheet. These embeddings are **strictly inclusion-natural**:

\[
\boxed{s_{P_G}|_{V_G}=s_{V_G},\qquad
       s_{V_G}|_{W_G}=s_{W_G}.}\tag{2.5}
\]

**Proof.** By Theorem 2.2, the root-adjacent component of `π^{-1}(A_Y)` maps with degree one. Its inverse `s_Y^∘:A_Y→\widehat Ω9` is holomorphic. The localization projection is biholomorphic on a neighborhood of its marked root and takes it bijectively onto an actual neighborhood of `K9`. On the punctured intersection with `A_Y`, that local inverse is the inverse belonging to the **same root-adjacent component**; by uniqueness of a one-sheeted inverse they agree. The two holomorphic inverses therefore glue to a holomorphic section on all of `Y`. Injectivity follows from `πs_Y=id_Y`, and every root point maps to its uniquely marked preimage. For nested disks, the two sections agree on a nonempty root neighborhood and hence on their connected overlap, proving (2.5). `□`

**Exact maximality criterion (all enlargements).** More generally, let `U⊂T9` be any connected open region with `K9⊂U`, `K9⊂⊂U`, and `U\setminus K9` connected, and use a root-compatible basepoint. A holomorphic section `s_U:U→\widehat T9` agreeing with the unique marked inverse near `K9` exists **if and only if**

\[
\boxed{ (j_U)_*\pi_1(U\setminus K9)\le H.}\tag{2.6}
\]

Necessity is the based covering lifting criterion for the restriction `s_U|U\setminus K9`. For sufficiency, that criterion produces the uniquely based exterior lift; gluing with the local inverse near the root is exactly the preceding argument. Section uniqueness is again forced by the root chart. If an enlargement contains a loop with nonzero winding about **any** fine component other than `D00`, then the subgroup condition fails. Importantly (2.6), not the weaker winding test, also catches free-group commutators missed by abelianization. This proves a sharp positive/negative boundary for rooted sections.

Since the coarse entire exterior has inclusion subgroup `<β0,β1,β2>` with `βr=b_(r,0)b_(r,1)b_(r,2)`, it violates (2.6). **The entire coarse localization has no rooted section into the fine localization.** The valid sections (2.4) exist precisely because these source-certified geometric disks avoid the other fine obstacles. A one-slit chart on an annulus, as in PR #59, is a different partial construction; the present embedded cores require no slit at all.

## 3. Full dynamic realization inside the fine canonical target

The original KL terminal-first-child theorem supplies the *actual* proper map

\[
G^3=f^9:W_G\longrightarrow V_G,
\qquad\deg(G^3)=2,
\quad \overline{W_G}\Subset V_G,
\quad K(G^3)=K9.\tag{3.1}
\]

Define on the **entire embedded central source disk**

\[
\boxed{
\widehat G^3=s_{V_G}\circ G^3\circ(s_{W_G})^{-1}:
 s_{W_G}(W_G)\to s_{V_G}(V_G).}\tag{3.2}
\]

**Theorem 3.1.** Formula (3.2) is a genuine proper degree-two polynomial-like return between strictly nested Jordan disks in the **actual fine canonical localization**. Its filled Julia set is exactly `\widehat K9` and its critical point is the marked lift of physical `0`. On a neighborhood of `\widehat K9` it agrees with the already constructed canonical localized period-nine return **as a germ**; equality of the two original global source-domain presentations outside their common germ is not asserted.

**Proof.** Sections (2.4)–(2.5) are biholomorphic onto their embedded images; conjugation therefore preserves properness, degree, critical multiplicities, compact nesting and the filled set. Both the physical map and the canonical localized period-nine return represent the same holomorphic germ near `K9` under Kahn's root-biholomorphic projection. The sections use that same chart, so they identify the germs. `□`

This is an **all-central-piece dynamical embedding**, not merely a finite combinatorial atlas or an arbitrary local inverse. For any additional source-central Jordan descendant lying in `P_G`, its geometric inclusion is automatically carried by the already defined `s_{P_G}`. Nothing here asserts that every native KL *universal-cover tile* embeds or that source ideal sides map continuously.

## 4. The complete original four-tile W access cycle: an exact, non-synthetic bridge

The source's genuine *ordinary G-stage* `W=Y_G^6` pseudo-piece has four universal-cover tiles, indexed in its prescribed cyclic order by `i=0,1,2,3`. Its **open inner gluing seams** in the `G`-straightening angle coordinate are

\[
(41,43)/192,\quad(53,55)/192,\quad
(137,139)/192,\quad(149,151)/192.\tag{4.1}
\]

They are source-defined actual landed accesses from [`results/tip_kl_side_atlas.json`](../../results/tip_kl_side_atlas.json), not guessed partitions of 512th angles. The 8 surviving **physical ambient `f` rays** and their actual Levin `Π3`, `Π9` angles from merged PRs #55–58 satisfy the following **strict** memberships:

| Original `G:W` tile | Sorted ambient ray angle | Outer `Π3` angle | Fine `Π9` angle | Physical fine endpoint |
|:--|:--|:--|:--|:--|
| tile 0 | `739/1022` | `3/14` | `1/2` | `−p` |
| tile 0 | `378423/523264` | `25/112` | `3/4` | `0`, lower access |
| tile 1 | `406473/523264` | `31/112` | `3/4` | `0`, lower access |
| tile 1 | `397/511` | `2/7` | `0` | `+p` |
| tile 2 | `114/511` | `5/7` | `0` | `+p` |
| tile 2 | `116791/523264` | `81/112` | `1/4` | `0`, upper access |
| tile 3 | `144841/523264` | `87/112` | `1/4` | `0`, upper access |
| tile 3 | `283/1022` | `11/14` | `1/2` | `−p` |

Every row additionally lies in the corresponding `G:V0` and `G:P` open gluing seam. The original same-stage inclusion `W→V0` routes the four W tile indices as

\[
\boxed{0,1\mapsto0;\qquad2,3\mapsto1,}\tag{4.2}
\]

with **zero** based integer angular shift (this is part of the genuine source atlas, independently checked here). There are two rays per W tile, and the two rays in each tile have **different** fine prime ends. In particular the **tile index by itself is not a fine access label**.

### Theorem 4.1 — an exact four-cycle, with the ORIGINAL KL incidence order

Index the two sorted rays of tile `i` by `e=0,1`. On these eight authenticated rows, the complete fine prime-end formula is

\[
\boxed{\Pi_9(i,e)={ (i+2+e)\bmod4\over4}.}\tag{4.3}
\]

Thus **every fine prime end is witnessed by precisely two source rays in adjacent W tiles**:

\[
\boxed{\Pi_9(i,1)=\Pi_9(i+1\bmod4,0),\qquad i\in\mathbb Z/4.}\tag{4.4}
\]

The four edges in source cyclic tile order are:

| W gluing tile pair | Fine prime end | Physical landing point | Source's *index-matched* adjacent ideal-side incidence |
|:--|:--|:--|:--|
| `0–1` | `3/4` | lower side of `0` | `η₀ ∪ ξ₁` |
| `1–2` | `0` | `+p` tip | `η₁ ∪ ξ₂` |
| `2–3` | `1/4` | upper side of `0` | `η₂ ∪ ξ₃` |
| `3–0` | `1/2` | `−p` tip | `η₃ ∪ ξ₀` |

This gives an honest **four-cycle of adjacent source tile CHANNELS**, with an alternating two edges within one `V0` parent tile (`0–1`, `2–3`) and two edges crossing between the two parent tiles (`1–2`, `3–0`). The two point accesses at `0` remain **different fine prime ends**, even though they have one physical landing point. The interval straightening `z=2cos(2πθ)` assigns fine angles `0` and `1/2` to the two endpoints, and `1/4`,`3/4` to the upper and lower side of its midpoint. The original physical ray pairing was proved in PR #54.

**Proof.** All eight `Π3` rational values and `Π9` values come from the real source-defined Levin maps of PR #55, not a new circle quotient. Compare them exactly with the four strict source seam intervals (4.1), then with the `V0` and `P` seams. Each tile receives the two table rows shown, strictly between the original seam endpoints. Direct rational substitution gives (4.3); it implies (4.4), no coincident angles within one tile, and exactly four two-element fibers. The source's own `W→V0` tile routes give the alternating parent pattern. The source side formula `∂^{v_i}Ψ_G(W)=η_i∪ξ_{i+1}` has **the same cyclic adjacent-index incidence** as (4.4), fixing the last column without changing any KL definitions. All these finite computations are verified by the new exact standard-library checker and Lean kernel theorem. `□`

**CRITICAL SIDE-TYPE DISTINCTION.** An ambient ray entering a tile **open gluing seam** is NOT a point of its ideal `ξ_i`, `η_i` or outer `λ_i` side: the source explicitly removes that open seam from the tile's remaining ideal boundary when gluing it to the central piece. The final column above is therefore an **incidence/tag correspondence**, **not** an assertion that the fine point equals the source puzzle vertex, or that the original native KL entire ideal side has been transported. The vertices of `W` are pullbacks of the dividing fixed point, whereas our fine endpoints belong to the *critical* preperiodic orbit. Equating them would be mathematically false.

## 5. Real prime-end naturality on the whole rooted annulus, and the precise nonextension

For each `Y`, the root-adjacent component `A_Y^{root}` is **conformally isomorphic** to the genuine physical annulus `Y\setminus K9` by Theorem 2.2. This automatically extends to a **homeomorphism of their complete prime-end compactifications**—both inner and outer prime-end circles. Thus the fine-root stage admits a **full inner-prime-end-circle transport** on every geometric core `P_G,V_G,W_G`, not merely four finite labels. Restricting this homeomorphism to the four selected fine ends gives the exact 8→4 incidence above.

Every nonroot component, on the other hand, is the universal cover of `Y\setminus K9`. Since the physical inner and outer boundaries are nondegenerate separated compacta, the annulus has finite positive conformal modulus. Its universal covering strip has two distinct infinitely wrapping prime ends. The covering extends on its two open boundary intervals, each as a universal cover of an inner or outer prime-end circle, but **cannot extend continuously to either wrapping endpoint** into any Hausdorff compactification containing the physical annulus as an embedded open region: distinct constant base images of infinitely translated interior points would otherwise have the same limit. This conclusion holds for **every** nonroot component over each of the three authentic KL puzzle disks, not just for one selected explicit native tile.

Together, the results give the exact interface boundary:

- The *entire geometric source central disk and its genuine return* embed holomorphically, coherently, with a complete rooted-annulus prime-end-circle homeomorphism.
- Four selected fine prime ends inherit exact original `W` tile **channel** labels, with an adjacent-cycle rule that agrees with the original ideal-side **indexing**.
- Every other annular sheet is universal and cannot have a whole wrapping-end extension. A bigger region exists only if its subgroup passes the **iff** criterion (2.6).
- There is still **no theorem** equating the original native KL `O/ξ/η` ideal sides with the inner prime ends of this new annulus, nor a full map of all native KL pseudo-piece tiles. Those are different surfaces, different boundary objects, and remain the next hard gate.

This is a structural bridge, not a substitute for KKL's universal unique-**proper**-restriction condition. All competing nonroot lifts remain proper in the filled fine surface by PR #59, so the present root section does **not** justify discarding them from a KKL path-family obligation.

## 6. Verification and next genuine research obstruction

Run at repository root:

```sh
python -m py_compile research/independent_audits/verify_tip_rooted_native_KL_section.py
python research/independent_audits/verify_tip_rooted_native_KL_section.py --check-manifest
lake build TipRootedNativeKL
```

The exact checker reads **three already-merged actual source manifests**, including the 24-original-tile `tip_kl_side_atlas.json`, the source-confirmed 8-ray Levin ladder, and the two-charge sheet grid. It independently checks every strict `W,V0,P` seam membership, the original source `W→V0` based zero-shift routes, the 4-cycle prime-end/tile formula, the physical three-point/four-prime-end distinction, and 7,424 reduced free-word conjugacy **samples** against the malnormality theorem. These samples are a regression, not an infinite proof; the universal free-group normal-form argument is written above. The Lean source, importing the existing `TipSheetGrid`, kernel-checks all eight original source-interval inequalities, the *independent* `TipLevinComposition` labels, the four adjacent edge equations, and the parent-tile crossing pattern. It does **not** formalize Kahn's analytic localization, Carathéodory, Riemann surfaces or KL gluing.

The next truly unproved task is to extend this **complete rooted geometric core section** across the **actual native KL universal-tile seam** while retaining individual integer deck winding and proving the source's proper-path endpoint condition on a complete proof-used ideal interval. The present iff obstruction says which extensions cannot exist without altering domain or sheet data. Any successful continuation must name the genuine `O/ξ/η` side **as a boundary arc of the correct native pseudo-piece**, distinguish it from this central gluing channel, and enumerate or charge every competing proper nonroot sheet. No global H1–H4, UPTCR or MLC promotion is made.

**Attribution and trust.** Kahn's localization theorem, Kahn–Lyubich's `W,V,P` puzzle and pseudo-piece definitions, Douady–Hubbard straightening, Levin's renormalization-ray maps, and classical free-product/covering/prime-end results remain their original authors' contributions. This source-specific synthesis, proof and finite verification were prepared with OpenAI GPT-6 assistance; independent mathematical specialist review and novelty/priority assessment are still needed.
