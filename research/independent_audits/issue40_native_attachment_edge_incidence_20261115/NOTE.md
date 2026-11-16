# Issue #40: actual-tip KKL attachment, complete marked-edge incidence, and Wave crest obstruction

**2026-11-15. Source-locked independent audit; NOT a solution of Issue #40.**

## The category, objects, and what is imported

Use the same **physical** 3/9 Misiurewicz tip in
[`TipKKLTreeMarking.lean`](../../../TipKKLTreeMarking.lean),
[`TipNativeProperRestriction.lean`](../../../TipNativeProperRestriction.lean),
[`results/tip_KKL_tree_marked_breakage_20261109.json`](../../../results/tip_KKL_tree_marked_breakage_20261109.json), and the preceding
[real phase certificate](../../../results/tip_root_interval_geometry.json). The parameter is strictly between
`-607918036626757496169199575185708826140/2^128` and
`-607918036626757496169199575185708826139/2^128`. Write
\(f_c(z)=z^2+c\), \(G=f_c^3:V_3\to U_3=D(0,1/4)\); **\(G\) has degree two on the central component** (though \(f^3\) has global degree eight). The inclusion \(\iota:V_3\hookrightarrow U_3\) is an embedding. The real tip interval, Misiurewicz dendrite identification, connected quadratic-like component and the KKL prime-end interpretation are *existing analytic inputs*, not consequences of finite arithmetic.

KKL [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §2.5 defines the **complete** Hubbard tree, edges and their two preimages; §6.1 Proposition 6.5 specifies the entire attached-component Carathéodory boundary in an immersion pullback; Proposition 6.6 gives the induced marking; Appendix A.1 defines open multi-interval markings and **closed** Wave crests; Appendix A.3.2–A.3.4 define set-valued proper restriction and covering pushforward. The certified real cut geometry yields
\[
T=[x_6,x_3],\qquad T'=G^{-1}(T)\cap V_3=[-x_3,x_3],\qquad A=T'\setminus T=[-x_3,x_6).
\]
There is **exactly one** attached component, rooted at the left end of \(K_2=[x_6,x_{15}]\). The fact that both sides of an embedded real slit give distinct prime ends is a *topological* input at this locally connected example; the script certifies its ten/twenty physical cut orders, not general non-locally-connected Carathéodory theory. In the target, \(U_3\setminus T\) has a 10-atom marked **inner** ideal circle; in the source, \(V_3\setminus T'\) has a 20-atom covering-marked **inner** circle. There are also outer ideal circles, treated as one whole-component atom; this audit makes **no claim of outer-boundary immersion properness**.

**Typing is essential:** \(G_*: \mathrm{Path}(V_3\setminus T')\to\mathrm{Path}(U_3\setminus T)\) is an unramified **covering pushforward**; \(\iota^*: \mathrm{Path}(U_3\setminus T)\rightrightarrows \mathrm{ProperPaths}(V_3\setminus T')\) is a **set-valued proper restriction**. Their composite \(F_*=G_*\circ\iota^*\) acts on admissible path families. The attached side \(A\) lies **inside** the target surface \(U_3\setminus T\): the inclusion has no pointwise prime-end boundary extension mapping it to the left tip. The block quotient below is merely a record of *path subordination*, not such a physical map.

## Complete one-step attachment and closed endpoint census

The ten target atoms \(I_0,\ldots,I_9\), in cyclic order, have physical types
`[K2, E20, K0, E0a, Ea1, K1, Ea1, E0a, K0, E20]`. Here \(K_0=[x_9,x_{18}]\), \(K_1=[x_{12},x_3]\), \(K_2=[x_6,x_{15}]\), and \(\alpha\in(3/32,1/10)\) is the dividing fixed vertex. The genuine **old** edges are
\(E_{20}=(x_{15},x_9)\), \(E_{0\alpha}=(x_{18},\alpha)\), \(E_{\alpha1}=(\alpha,x_{12})\). The ten physical source cut locations in increasing order are
`[-x12, x6, x15, -alpha, x9, x18, alpha, -x15, -x6, x12]`. The entire source cut preimage is fixed by real orbit identities, evenness, and monotonicity of \(G\) on each side of zero. The source covering atom \(S_s\) maps under **\(G_*\)** to \(I_{s\bmod10}\).

Applying **\(\iota^*\)** via KKL Proposition 6.5 instead produces the following **open** cyclic blocks, with both listed endpoint *accesses* adjoined only on taking the closure:

| target interval | actual open source atoms | closure endpoint accesses | old-tree edge sides | \(G_*P_i\) target atom word |
|---|---|---|---|---|
| \(P_0=\iota^* I_0\) | `18,19,0,1,2` | lower/upper at `x15` | none | `8,9,0,1,2` |
| \(P_1\) | `3,4` | upper `x15` / upper `x9` | `E20` | `3,4` |
| \(P_2\) | `5` | upper `x9` / upper `x18` | none | `5` |
| \(P_3\) | `6` | upper `x18` / upper `alpha` | `E0a` | `6` |
| \(P_4\) | `7,8,9` | upper `alpha` / upper `x12` | `Ea1` | `7,8,9` |
| \(P_5\) | `10` | upper/lower `x12` | none | `0` |
| \(P_6\) | `11,12,13` | lower `x12` / lower `alpha` | `Ea1` | `1,2,3` |
| \(P_7\) | `14` | lower `alpha` / lower `x18` | `E0a` | `4` |
| \(P_8\) | `15` | lower `x18` / lower `x9` | none | `5` |
| \(P_9\) | `16,17` | lower `x9` / lower `x15` | `E20` | `6,7` |

**Care with the tip gates:** the two ideal accesses at `-x12` lie **inside** \(P_0\); \(-x_3\) lies inside atom \(S_0\), not at a marking cut. Likewise \(x_3\) lies inside \(S_{10}\), and the closure of \(P_5\) has two `x12` accesses, not two `x3` accesses. Internal cuts are included in each displayed open connected block; only the external endpoints are omitted. The attached-component boundary contributes **all** `S19,S0,S1` (two sides and its tip), together with original `S18,S2` in \(P_0\). It cannot be counted only once as a graph edge. Every \(P_i\) is end-proper, but only \(P_0\) fails full properness (its attached sides map into the target interior). Disjointness and completeness are checked on the entire 20-cycle.

## Every old edge, every new sheet, and the source-derived \(T_F\)

The verifier divides the **actual real segments** by the above cut locations and maps each *physical segment* under \(G\) using exact orbit images and the certificate \(G'(x)=8x f(x)f^2(x)\), with \(f(x)<0<f^2(x)\) for \(|x|\le x_3\). The separate upper and lower accesses to one real segment count **one** Hubbard edge, not two. The complete preimage of each target old edge contains exactly two open physical sheets:

| target image edge | physical source sheets | sheet in new attachment? |
|---|---|---|
| \(E_{20}\) | `(-x12,x6)` and `(-x6,x12)` | first **yes**, second **no** |
| \(E_{0\alpha}\) | `(x15,-alpha)` and `(alpha,-x15)` | neither |
| \(E_{\alpha1}\) | `(-alpha,x9)` and `(x18,alpha)` | neither |

The first \(E_{20}\) sheet is in the attached component, **not** in old \(T\). For the three **old** source edges, the complete monotone image traces are
\[
 E_{20}\mapsto(E_{0\alpha},E_{\alpha1}),\qquad
 E_{0\alpha}\mapsto(E_{\alpha1}),\qquad
 E_{\alpha1}\mapsto(E_{0\alpha},K_0,E_{20}).
\]
The explicit `K0` between the last two images is a **vertex gap, not an edge**, so the edge word is not a purported contiguous contour word across a vertex. With **output edges as rows** and **old input edges as columns**, the genuine KKL edge-occurrence matrix, derived only **after** the physical trace, is
\[
 T_F=\begin{pmatrix}0&0&1\\1&0&1\\1&1&0\end{pmatrix},\qquad
 \det(tI-T_F)=t^3-2t-1=(t+1)(t^2-t-1).
\]
\(T_F^4\) has strictly positive integer entries, and \(\phi=(1+\sqrt5)/2>1\) has exact **left** edge weights \((\phi,1,\phi)\) (\(\phi^2=\phi+1\)). Hence this *physical old-edge chain* expands with factor \(\phi\) in weighted edge traversal counting. This is not a proof of growth for an arbitrary marked Wave, a zero-edge sector, or a non-locally-connected proper prime-end path. Covering-side duplications are not separate old edge traversals.

The verifier also emits full per-source-atom physical/image/carrier incidence, per-target pullback interval (including all source atoms and images), the complete two-sheet preimage of every edge, and every open/closed boundary endpoint. The machine does **not** import a transition matrix: it constructs the three-by-three matrix from source segments and maps.

## Zero-old-edge sectors: complete finite census and precise limitation

**All ten atomic target crest *types*** have old-edge incidence `I1,E20`, `I3,E0a`, `I4,Ea1`, `I6,Ea1`, `I7,E0a`, `I9,E20`, while the *entire* four zero-old-edge types are **\(I_0,I_2,I_5,I_8\)**, physically the sides of `K2,K0,K1,K0`. At source covering resolution there are eight zero-old-edge atoms, **`S0,S1,S2,S5,S10,S15,S18,S19`**; after **covering pushforward**, eight zero-output-edge atoms are **`S0,S2,S5,S8,S10,S12,S15,S18`**. Those different sets must not be conflated, and attachment `S19,S0,S1` is zero **old** edge even though part of it covers a target edge.

For *whole atomic open multi-intervals only*, the genuine \(F_*=G_*\iota^*\) computation yields:

| original zero-edge crest | first output containing an old edge side | first full-circle saturation |
|---|---:|---:|
| `I0` | 1 | 2 |
| `I5` | 2 | 3 |
| `I2` | 3 | 4 |
| `I8` | 3 | 4 |

These use a **cyclic source-word composition of actual computed blocks**, not a free-standing finite-state machine. The verifier distinguishes an open *ten*-source-atom halfturn (its covering image is a punctured circle) from a block of *more than ten* source atoms (its image includes every angle). The finite result **does not** prove that every positive-length *subsector*, every source-eligible path, or every native zero-edge Wave must grow or saturate. Such paths can terminate on distinct accesses within one marking atom and need a genuine gate/collar theorem; nothing about graph valence alone establishes it.

## Exact Wave compatibility decision and first false hypothesis

KKL Appendix A.1 defines a Wave by a lamination of paths subordinate to a boundary multi-interval \(B\), with **closed** crest \(C=B\setminus(E_-\cup E_+)\); there is **no source-defined finite family of “canonical KKL Waves”** indexed only by these ten atoms. Our ten three-atom rows are therefore **all elementary possible crest types**, not ten analytically realized positive-width Waves. On the **edge-charge compatibility test** (whether that crest is a genuine old marked Hubbard **edge side**), **six types pass** and **four types fail** (`I0,I2,I5,I8`). That table must not be misreported as a theorem about the existence of ten Wave families.

There *is*, however, a previously certified **actual positive-width Wave**, not a conjectural crest: concentric proper target circles with center `-9/64` and `3/256<r<1/64`, base `(I9,I0,I1)` and **closed crest \(I_0\)**. Its target leaf endpoints and both source gate crossings are certified for the *whole radius interval*, using the exact quadratic parameter bracket and an enclosing complex disk with \(|G(z)|<1/20\). The two genuine marked restrictions survive KKL's marking filters and their pushed child crests are **\(I_2,I_8\)**. The rectangle calculation imported from the previous analytic note gives the positive widths \(\log(4/3)/(2\pi)\) and \(\log(4/3)/\pi\) for each child. Yet **all three of these closed crests have ZERO old-tree edge mass**. The full image of \(P_0\) meets edge atoms, but that does **not** turn the closed crest \(I_0\) into an old edge, nor does it establish the requisite inclusion for the *full descendant closed crest*.

**First failed hypothesis of the naive edge-to-Wave transfer:**
> Every positive-width native KKL Wave (or each of its pushed child Waves) has a closed crest carrying positive old Hubbard-tree edge incidence.

This hypothesis is **false already in the actual physical tip**: the explicit positive-width `(I9,I0,I1)` Wave and its two children give a source-defined witness, not a synthetic matrix. The **narrowest corrected statement** is the exact \(\phi\)-edge growth for genuine traversals of the three old tree edges; Wave amplification needs an *additional* independently proved positive edge-charge/closed-crest transport lemma. No claimed contradiction of KKL follows: KKL permits breakable Waves and does not posit this invalid auxiliary edge-transfer hypothesis.

The source also explicitly warns that \(F_*\overline I\) may differ from \(\overline{F_* I}\). All displayed block closures are **source-access closures**, not asserted equality of those two different operations. A Wave with a closed crest is not automatically an allowed *open* interval word after lifting. A positive-width Wave whose crest is zero-edge can still have nontrivial properly restricted leaves, as this example proves.

## What is certified, what is analytic, what remains open

**Exact integer/rational/ball certification:** parameter guard; outward 256-bit orbit intervals; all real vertex/cut orders; full degree-two cut images; derivative sign on the entire source real interval; complete two-sheet physical edge occurrence, upper/lower distinct side bookkeeping; closed endpoints of all ten blocks; both \(G_*\) and \(\iota^*\) finite markings; matrix coefficients, polynomial/primitive power and exact Perron equation; all atomic zero-edge sectors; proper halfturn vs full-circle cyclic saturation; and **whole-disk**/whole-radius-range bounds for the existing Wave. Mutations of phase, parameter, omitted attachment atom, conflated f/iota and false Wave crest are rejected by explicit negative controls. Result manifest is regenerated, sorted and compared byte-equivalent as parsed JSON.

**Imported or written analytic argument, NOT verified by the script:** connected quadratic-like central component and its degree two, local connectivity/dendrite, identification of the ideal boundaries with slit-side prime ends, full KKL Proposition 6.5 attachment formula and path-subordination semantics, exact extremal widths via the logarithmic rectangle, and the classification of arbitrary proper paths. In particular, the project is not assuming a global continuous immersion boundary map or a non-LC monotone circle quotient.

**Still open in Issue #40:** general exceptional non-LC access/collar atlas and attachment multiplicities over larger `q`/iterate domains; all path-level gate images and no-cancellation of analytic immersed lifts; **zero-edge subsectors** (as opposed to whole marking atoms); positivity/shortness and endpoint inclusions of arbitrary **closed** Wave crests; compatibility of proof-selected canonical geodesic/WAD families with this edge model; and the general strict marked-length growth theorem. **No native counterexample to KKL's stated theorem is claimed.** Keep Issue #40, `KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR`, `KKL_PARABOLIC_WAVE_AMPLIFICATION`, H1–H4, UPTCR, and MLC open.

## Reproduce

```sh
python research/independent_audits/issue40_native_attachment_edge_incidence_20261115/verify_native_attachment_edge_incidence.py --check-manifest
python research/independent_audits/issue40_native_attachment_edge_incidence_20261115/verify_native_attachment_edge_incidence.py --adversarial
python research/independent_audits/verify_tip_KKL_tree_marked_breakage.py --check-manifest
lake build TipKKLTreeMarking TipNativeProperRestriction
```

New files are restricted to this audit subdirectory, `results/issue40_native_attachment_edge_incidence_20261115.json` and `.github/workflows/issue40-native-attachment-edge-incidence.yml`. No existing verifier, formalization, workflow, ledger or research map is edited. This note is a mathematics/reproducibility *audit*, not an independently reviewed global KKL proof.
