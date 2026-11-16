# Issue #62: exact KL J-side / V-tail footprints and a prescribed-connector evidence gate

**16 November 2026. Status: scoped next step; Issue #62 is NOT closed.** This audit crosses the exact native original `G=f³` source atlas of PR #60, native root deck of #63, C4 wake sector theorem of #64, strict finite J-side trichotomy of #65, whole boundary typing of #66, and proper-path / tail theorem of #67. It proves an additional **source-typed disjointness** of the marked fine-root J ends and the ordinary KL `W→V⁰` *boundary-proper* J tails. It does **not** invent unprovided physical based nine-generator connector words. These remain open and are explicitly recorded as `null` in the manifest, never as the identity.

**Trust boundary.** Rational inequalities and finite free-word controls in this note are checked exactly by the new Python verifier; the all-integer sector implications are proved below. KL original source prime ends, Carathéodory landing, Kahn's fine root chart, the real Jordan wake obstruction and native proper escape are *imported written analytic inputs*, **not certified by Python or Lean**. All require independent specialist review before claiming analytic closure or novelty.

## 1. The actual source ideal domain and three physical landing types

The stage is the ordinary `G=f³` Kahn–Lyubich `W=Y_G⁶` pseudo-piece `Ψ_G(W)`, with a **physical G carrier** and four distinct annular universal-cover tiles, as in KL II ``3.2.1–3.2.4 and Lemmas 3.3–3.4. The fine physical target has `K9=D_(0,0)⊂K3`, while `D_(0,1)` and `D_(0,2)` are removed fine obstacles within the coarse root. The fine uncompactified canonical localization is `π9:T̂9→T9`, `Ω9=T9\K9`.

For each original W universal tile `j`, its open inner *gluing seam* `I_j=(a_j,b_j)` (not an ideal J-side) and its actual strict finite J ideal sides are

| W tile | `(a_j,b_j)`, G unwrapped seam | strict finite `ξ_j` | strict finite `η_j` | V parent |
|---|---|---|---|---|
| `W0` | `(41/192,43/192)` | `x<a_0` | `x>b_0` | `V0` |
| `W1` | `(53/192,55/192)` | `x<a_1` | `x>b_1` | `V0` |
| `W2` | `(137/192,139/192)` | `x<a_2` | `x>b_2` | `V1` |
| `W3` | `(149/192,151/192)` | `x<a_3` | `x>b_3` | `V1` |

The four finite side endpoints `x=a_j` or `x=b_j` are source vertex ends, not *strict interior* finite J ends. At `x=±∞` the eight infinitely wrapping O/J joints are yet another source type. The four finite outer `λ` sides are distinct as well. The open seam `I_j` is glued to the central piece; an external ray with unwrapped angle there is **not** a surviving finite `ξ_j/η_j` ideal point.

Use the physical `G`-ray landing map `L_G:ℝ/ℤ→K3` (its existence and source-sector classification are imported analytic results from #64). Define, without assuming any interval or positive measure,

\[
E_i := \{\theta\in I_i:\ L_G(\theta)\in K_9\},\qquad 0\leq i\leq 3 .
\]

The actual **typed third-class finite original KL J ideal domain** is the following set of source ends, with *tile, side and unwrapped angle retained*:

\[
\mathcal J^9
=\bigcup_{\substack{i,j=0,\ldots,3\\\theta\in E_i,\ n\in\mathbb Z}}
\bigl\{(j,\xi_j,\theta+n,L_G(\theta)):\theta+n<a_j\bigr\}
\ \cup\
\bigl\{(j,\eta_j,\theta+n,L_G(\theta)):\theta+n>b_j\bigr\}.
\tag{1}
\]

This relies on #64's **source-sector exhaustion** of actual root-landing angles. `E_i` is not replaced by eight rationals, their convex hull, or an asserted open interval; the finite witnesses below are only exact rational points known to belong to these sets. A source J-point landing at `a` is **ordinary fine exterior** (locally extendible); a J-point landing at `x3` or `x6` is in removed `D_(0,1)` or `D_(0,2)` (nonextendible because of the physical target); *neither* is in (1).

The eight authenticated **open-seam ray anchors**, used only to generate actual ideal J witnesses by other-tile representation or native deck translation, are:

| original W seam | ray | `G` angle `θ` | fine `Π9` | physical fine root access |
|---|---|---|---|---|
| 0 | qR | `3/14` | `1/2` | `−p` |
| 0 | d | `25/112` | `3/4` | `0` lower |
| 1 | e | `31/112` | `3/4` | `0` lower |
| 1 | pR | `2/7` | `0` | `+p` |
| 2 | pL | `5/7` | `0` | `+p` |
| 2 | a | `81/112` | `1/4` | `0` upper |
| 3 | b | `87/112` | `1/4` | `0` upper |
| 3 | qL | `11/14` | `1/2` | `−p` |

The two accesses at `0` remain distinct prime ends despite their equal *physical point*. The verifier checks all eight against the original G atlas, the Levin `Π3/Π9` source ladder, and PR #60 and #63–65 manifests.

## 2. New cross-source theorem: the fine-rooted J ends collapse to V interior

KL II Lemma 3.4(ii) gives source-natural, zero-unwrapped-shift tile routes `W0,W1→V0` and `W2,W3→V1`. In the same original `G` universal-cover coordinate, the **V-parent** open seams are `(40,56)/192` and `(136,152)/192`, respectively. The entire exact source chain is

\[
40<41<43<53<55<56<136<137<139<149<151<152. \tag{2}
\]

The original PR #67 identifies the part of a W ideal side which remains a **proper V ideal J-side tail**: in parent `p`, `ξ` with `x≤L_p` and `η` with `x≥U_p`. The remaining open gaps `(L_p,a_j)` on `ξ_j` and `(b_j,U_p)` on `η_j` map to **V central interior**. This concerns the ordinary KL `Ψ(W)→Ψ(V⁰)` immersion, **not** fine-root convergence or the marked KKL restriction category.

**Theorem 2.1 (all source-sector angles and all integer translates).** Fix any `i` and any `θ∈I_i`, *without assuming `L_G(θ)∈K9`*. In tile `j` at unwrapped `x=θ+n`, the strict finite original J/source-to-V boundary type is:

| source representative | is it strict finite J? | ordinary KL W→V footprint |
|---|---|---|
| `j=i,n=0` | **No**, open gluing seam | central original W glue |
| `j=i xor 1,n=0` | **Yes**, `ξ` for even `i`, `η` for odd `i` | **V interior-collapse** |
| `j//2 ≠ i//2,n=0` | **Yes**, opposite-parent `ξ`/`η` | **V boundary-proper J tail** |
| `n≤−1`, all four `j` | **Yes**, `ξ` | **V boundary-proper J tail** |
| `n≥1`, all four `j` | **Yes**, `η` | **V boundary-proper J tail** |

**Proof, finite rational inequality with universal quantifiers.** For `i=0`, every `θ∈(41,43)/192` lies strictly in the mate tile `W1`'s `ξ` interior-collapse gap `(40,53)/192`. For `i=1`, every `θ∈(53,55)/192` is in the mate `W0`'s `η` interior-collapse gap `(43,56)/192`. Likewise, `i=2` yields mate `W3`'s `ξ` gap `(136,149)/192`, and `i=3` yields mate `W2`'s `η` gap `(139,152)/192`. Any angle in a sector of one V parent is strictly on the remote parent side of that remote V seam (`θ<136/192` from parent 0; `θ>56/192` from parent 1), hence opposite-parent points lie on proper V J tails. Finally, for all `0<θ<1` and **every** `n≤−1`, `θ+n<0<L_p`; for every `n≥1`, `θ+n>1>U_p`. Thus every nonzero deck translation lies in a V proper tail. All strict inequalities follow from (2), checked as `Fraction` comparisons by the verifier. `□`

**Corollary 2.2 (genuine fine-root versus V-tail disjointness; conditional analytic content).** On the subset `θ∈E_i`, merged PR #64's *source-specific* W→V naturality, real Jordan wake and Kahn fine chart result says that the fine lift converges to the marked root **iff** `j=(i xor 1),n=0` among strict finite J source points. Every other strict finite J end is a **proper nonroot lift** into the uncompactified fine canonical localization. Combining that **imported analytic** theorem with Theorem 2.1 gives the new source-typed implication:

\[
\boxed{\text{fine-rooted native finite J end over }K9
\iff \text{same-parent mate at }n=0
\iff \text{its ordinary W→V image collapses to V interior}.}\tag{3}
\]

All other native finite J points over that root, i.e. the **V boundary-proper J tails**, have **proper nonroot fine** lifts. In particular **no original W→V boundary-proper J tail over the K9 cohort is a marked fine-root J end**. The equivalence in (3) requires the specifically imported analytic source sector/root-sheet hypothesis; exact arithmetic alone does not prove it.

### Every finite certified row, with no fictitious whole-domain enumeration

The deterministic new `finite_j_side_footprints.json` lists **88** distinct source J ideal points from the eight authenticated rays, four original tiles, and three deck values `n=−1,0,+1`. From the 96 potential entries exactly eight own-tile zero-deck entries are **open gluing seams** and are excluded. Of the remaining 88:

* **8** same-parent mate, zero shift: fine marked root and ordinary KL **V interior-collapse**;
* **16** opposite-parent zero shift: fine proper nonroot and **V proper tails**;
* **64** nonzero unit shifts in all tiles: fine proper nonroot and **V proper tails**.

Each manifest record has the actual source W tile, side, exact unwrapped G angle, modulo-one G angle, fine angle, physical endpoint and named proof role. No finite sample set is promoted to the full `E_i`, whose size is unknown.

## 3. KL-prescribed path groupoid and the missing nine-generator word certificate

The **original** KL II `3.2.1 classifying paths—not an invented quotient—are paths in `U_G⁶\S_W` starting in `W`, where `K_W=W∩K3`, `S_W=closure(K3\K_W)`, with the **subordination** rule: whenever a prefix reaches `K_W` it is endpoint-rel homotopic to a prefix contained in `W`. Paths are identified by **homotopies through this restricted path space fixing the terminal endpoint**. By KL II Lemma 3.3 this yields the actual central W and **four disjoint annular universal-cover components**, glued only over the actual four simply connected `W_i`; the native J sides and deck translations are real **source ideal objects**, not just angle labels.

Fix the **physical** basepoint `x∈W\K3` and distinguished fine lift `s_W(x)` from PR #60. For a proof-used source J ray with physical positive-height point `y_{θ,t}`, the required coarse connector `κ′_{θ,t}:x→y_{θ,t}` must be realized in the **coarse exterior** `Ω3` by a *source-authorized* KL Lemma 3.3 path `δ_j` and an explicitly fixed coarse base whisker `c_j:x→x_j`. It cannot be chosen freely merely to simplify the result. The rooted PR #60 connector `κ_{θ,t}:x→y_{θ,t}` is permitted inside `W\K9`, where it **may cross `K3\K9`, forbidden to `κ′`**. In the *same* physical fine exterior, their actual based defect is

\[
g_{\theta,t}=[\kappa'_{\theta,t}\cdot\kappa_{\theta,t}^{-1}]
\in \Gamma=\pi_1(\Omega_9,x)=F(b_{00},b_{01},b_{02},b_{10},\ldots,b_{22}). \tag{4}
\]

The root stabilizer is `H=⟨b00⟩` and fine sheets are **left cosets `H\Γ` with right monodromy**. The coarse peripheral loop is `β0=b00 b01 b02`, *not* the fine root meridian `b00`. The missing original whiskers `c_j`, proof-used endpoint-fixed KL homotopy classes, physically certified nine-cut crossing lists and based basis-change paths **are not furnished by the original finite angle manifests**. Therefore **NO literal based cross-tile `gθ` word is computed** in this audit. The manifest explicitly has `"based_F9_defect_word":null` in every row. Setting such a word to identity through a category change would be a false proof.

### Exact nonabelian statement that *is* presently justified

For a **specified global based** coarse loop `B0` at that very `x` with word exactly `β0`, define the **based prefix** change `κ′⁽ⁿ⁾=B0ⁿ⋅κ′` (do *not* change the fine rooted path). Basic path concatenation in the correct category then gives

\[
g^{(n)}=\beta_0^n g,\qquad
H g^{(n)}=H\beta_0^n g,\qquad
H\beta_0^n g\neq H\beta_0^m g\text{ for }n\neq m. \tag{5}
\]

**Proof.** Concatenation is associative on based homotopy classes, so the first identity preserves the complete noncommutative **left** prefix order. Equality of the two **left** cosets would imply `β0^(n−m)∈H` because `(β0^n g)(β0^m g)^{-1}=β0^{n−m}`. This is impossible for `n≠m` since `β0` has `D_(0,1)` winding +1, while every element of `H` has zero winding there. This proves the all-integer assertion, independently of finite word samples. `□`

**Important qualification.** A source-native tile deck translation `τ_j^n` is **not automatically** the particular globally based prefix `B0^n`. It is known from #63 to wind `n` times around `D_(0,1)` and `D_(0,2)`, but its actual globally based word may be a **conjugate** of `β0^n` depending on the missing source base whisker. Therefore (5) must **not** be assigned as the literal `gθ` for an otherwise unspecified original KL side path.

For any **physically certified** full based word `g`, the unique candidate root shift is `n*=−wind_(D01)(g)`, and the exact criterion is `red(β0^n* g)∈⟨b00⟩`; with all nine generators and their order retained. Abelianization alone is insufficient: the nontrivial commutator `[b01,b02]` winds zero about *every* generator but is not in `H` and has no rooted shifted coset. The verifier checks all **5,527** reduced words of length ≤3 over all nine generators with exact cancellation, all tested based-prefix/coset orders, commutator counterexample and proper free subgroup membership.

### The genuinely unresolved proof gate

To turn a manifest `null` into a complete prescribed connector defect, a new source certificate must exhibit (i) the **actual KL Lemma 3.3 endpoint/subordination homotopy class**, source tile and original `G` carrier path; (ii) the actual coarse base whisker and physical positive-height endpoints, with the matching *fine* rooted W connector; (iii) ordered signed physical intersections with **nine verified disjoint fine cuts**, certified with exact/interval enclosures and an **explicit change into the archived based meridian basis**; and (iv) a second representative/homotopy check of the resulting **full freely reduced F9 word**, followed by the root test and source-typed prime-end convergence. A mere physical landing angle, C4 winding vector, or a synthetic group word does **not** meet the gate.

KKL Appendix A.3.2 is *set-valued* and additionally uses a **selected ideal marking and source subordination/refinement**. PR #67's **unmarked** ordinary KL W→V two-channel paths and PR #68's **physically marked** Hubbard-tree-complement paths belong to different immersions and cannot be merged into a proof of KKL unique proper restriction.

## 4. Certification, acceptance criteria and open obligations

Run from the repository root:

`python research/independent_audits/issue62_connector_defects_20261116/verify_issue62.py --check-manifest`

The checker re-reads original `results/tip_kl_side_atlas.json`, the source exact Levin ray census, the PR #60, #63–67 exact manifests, and the nine-phase exact dyadic interval certificate. It checks (2) and the complete source-sector implication for **all** angles in each `I_i` and all integer shifts (the last via inequality/monotonicity); cross-checks the **88** finite source instances with all original type/target labels; checks that ordinary a/excluded x3,x6 rays were not silently called root rays; and validates the **5,527** fully nonabelian reduced F9 controls. A small **Lean file** certifies only discrete based-word control examples using the **existing archived** F9 word definitions; no geometric source word is postulated.

The dedicated new workflow `.github/workflows/issue62-connector-defects.yml` runs this verifier and the independent prior PR #60/#63–67 regressions plus the registered Lean suite and the new discrete file. No README, research map, ledger, older file, Lakefile or other existing file is altered.

**Issue #62 acceptance status**: (1) genuine source subset typed by (1), with eight authenticated root angles and exact 88 J witnesses, **conditional** on imported landing/sector completeness; (2) KL source path equivalence and comparison defined with correct carriers/basepoint/monodromy, all-integer based-prefix groupoid law (5) proved, but **full original KL-prescribed connector words remain UNCOMPUTED**; (3) every instance in the certified eight-angle finite J cohort classified by the **previous written analytic source theorem**, newly cross-classified against actual W→V proper-tail vs collapse status; (4) complete source-KKL proof-used proper-restriction groupoid and all other source-defined based F9 words **OPEN**. H1–H4, UPTCR, MLC and the original 465-entry ledger remain **OPEN**. Independently verified specialist correctness/novelty has not been established.

### Primary source and archive provenance

- Kahn–Lyubich, *A priori bounds for some infinitely renormalizable quadratics II: Decorations*, KL `3.2.1–3.2.4, Lemmas 3.3–3.4. Published paper pp. 66–69; arXiv preprint printed pp. 11–13. [arXiv](https://arxiv.org/pdf/math/0609046); [published](https://www.numdam.org/item/10.24033/asens.2063.pdf).
- Kahn, *A priori bounds ... I*, `7.4.1, Theorem 7.12, root localization and marked biholomorphic chart: https://arxiv.org/pdf/math/0609045.
- Merged archive [PR #60](https://github.com/dovvnloading/loops-research-archive/pull/60), [#63](https://github.com/dovvnloading/loops-research-archive/pull/63), [#64](https://github.com/dovvnloading/loops-research-archive/pull/64), [#65](https://github.com/dovvnloading/loops-research-archive/pull/65), [#66](https://github.com/dovvnloading/loops-research-archive/pull/66), [#67](https://github.com/dovvnloading/loops-research-archive/pull/67); supplemental distinct-category [#68](https://github.com/dovvnloading/loops-research-archive/pull/68). The original precise page-level manuscripts and verifiers are under `research/independent_audits/`.
- Kahn–Kapiamba–Lyubich (2026), Appendix A.1/A.3.2 and Proposition A.12: https://arxiv.org/abs/2606.27272.

Prepared with GPT-6 assistance. The **original research analytic claims have not received independent mathematical specialist sign-off**.
