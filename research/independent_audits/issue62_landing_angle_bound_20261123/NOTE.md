# Issue 62: an exact one-third dimension bound for the actual fine-landing angles

Date: 2026-11-23 (America/New_York). Repository base: `ed64c7ad839dcc8b799d53379434f892fdc92a2c`.

This note proves an upper bound of **one third** for both the Hausdorff dimension and the upper box dimension of the actual fine-cycle landing-angle set in the normalized G external-angle circle. The proof uses the actual analytic landing and sector theorems already written in the archive, followed by a finite exact rational calculation. Its implication from physical landings to the symbolic survivor graph is only one-way. It does not identify the graph's entire survivor set with a physical landing fiber.

**Sharp value.** The [companion entropy proof](EXACT_DIMENSION.md) supplies the matching lower bound using the actual Chebyshev return. Together the two arguments give Hausdorff dimension and both box dimensions exactly 1/3 for E, each full phase set E_j, and, using the actual source symmetries, each individual seam root subset. The finite checker below certifies the arithmetic upper-bound ingredients; the entropy lower bound is a written application of cited classical theorems.

The accompanying `verify.py` uses only the Python standard library. It reads the actual `results/tip_kl_side_atlas.json`, constructs the graph, checks all strongly connected components, and verifies an exact vector identity that proves the path-count formula for **every** horizon. No finite sampling of long orbits, numerical eigenvalue, or unproved spectral asymptotic enters the estimate.

## 1. Actual dynamical set and the analytic inputs

Use the archive's actual parameter c_* and G=f_{c_*}^3. Let K3 be the connected, locally connected filled set of this quadratic-like return, and let

\[
 C_0=K9=[-p,p],\qquad C_1=G(K9)=D_{(0,1)},\qquad
 C_2=G^2(K9)=D_{(0,2)},\qquad B=C_0\cup C_1\cup C_2.
\]

These are actual pairwise disjoint compact intervals with G(C_j)=C_{j+1 mod 3}. Let

\[
 L:\mathbb T=\mathbb R/\mathbb Z\longrightarrow K3,\qquad
 d(\theta)=2\theta\pmod 1
\]

be the actual continuous G-Carathéodory landing map, so that L∘d=G∘L. Define

\[
 E_j=L^{-1}(C_j),\qquad E=L^{-1}(B)=E_0\cup E_1\cup E_2.
\]

The following analytic facts are used, rather than inferred from the graph.

1. The actual three fine intervals form the disjoint cycle just specified.
2. L exists continuously for all G angles and satisfies the actual semiconjugacy.
3. The source W-sector theorem exhausts **all** K9-landing angles, including irrational angles:

   \[
   E_0\subset I:=(41/192,43/192)\cup(53/192,55/192)
          \cup(137/192,139/192)\cup(149/192,151/192).
   \tag{1}
   \]

Items 1–2 are the actual dynamical setup in `research/independent_audits/tip_native_finite_J_side_target_trichotomy_20261109.md`, §1. Item 3 is Lemma 5.1 and Theorem 5.2 of `research/independent_audits/tip_native_C4_wake_root_sheet_naturality_20261109.md`, §5. The four rational endpoints are exactly those in stage G, piece W, `seam_stage_angles` of `results/tip_kl_side_atlas.json`. That JSON supplies exact numbers; the written source-sector theorem supplies their physical meaning.

All dimension and length statements below use the normalized external-angle coordinate on T. The archive explicitly labels the physical angle-height chart as straightening-transported and topological, not a physical conformal metric. No harmonic-measure, capacity, or extremal-width conclusion is asserted.

## 2. The one-way physical inclusion

Since G(B)⊂B, semiconjugacy gives

\[
d(E)\subset E.\tag{2}
\]

If θ∈E_j, its physical landing is in C_j. For some r∈{0,1,2}, G^r(L(θ))∈C_0. Thus d^r(θ)∈E_0⊂I. Consequently

\[
E\subset S:=I\cup d^{-1}(I)\cup d^{-2}(I),\qquad
E\subset\bigcap_{n\ge0}d^{-n}(S).\tag{3}
\]

Only (3) is needed. It is not asserted that every survivor of S lands in B.

The inverse images in S are exactly

\[
\left(\frac{a+k}{2^r},\frac{b+k}{2^r}\right),
\quad (a,b)\text{ one of the four intervals in }I,
\quad 0\le r\le2,\quad 0\le k<2^r.
\tag{4}
\]

They are 28 pairwise disjoint open intervals, all with endpoints in the 768-grid. In grid units, their endpoint pairs are

```
(41,43),   (53,55),   (82,86),   (106,110), (137,139), (149,151),
(164,172), (212,220), (233,235), (245,247), (274,278), (298,302),
(329,331), (341,343), (425,427), (437,439), (466,470), (490,494),
(521,523), (533,535), (548,556), (596,604), (617,619), (629,631),
(658,662), (682,686), (713,715), (725,727).
```

Each displayed pair (a,b) represents the **open** interval (a/768,b/768). Their total length is 1/8.

## 3. The finite graph, with boundary points kept separate

Put Q={j/768:0≤j<768} and

\[
Z=\bigcup_{r\ge0}d^{-r}(Q).
\tag{5}
\]

Z is a countable set, since each inverse image of the finite set Q is finite. More strongly, no point of Z can survive in S forever. Indeed, 768=3·2^8, so the exact finite calculation gives

\[
d^8(Q)=\{0,1/3,2/3\},\qquad \{0,1/3,2/3\}\cap S=\varnothing.
\tag{5a}
\]

The three excluded points have grid coordinates 0, 256 and 512, all outside the 28 open intervals displayed in §2. If θ∈E∩d^{-r}(Q), forward invariance would give d^{r+8}(θ)∈E⊂S, contradicting (5a). Therefore

\[
E\cap Z=\varnothing.
\tag{5b}
\]

This excludes every possible grid boundary and its preimages from the **actual** set. No equality of open and closed intervals is silently used, and no countable boundary set is added to the finite covers. That latter distinction is needed for the upper box-dimension conclusion, since adding an arbitrary countable set can increase upper box dimension.

For 0≤i<768, put J_i=(i/768,(i+1)/768). Let V be the indices i for which J_i⊂S. Since every endpoint of S lies in Q, S\Q is exactly the disjoint union of these cells. There are 96 such cells. Doubling sends the interior of J_i across the two cells with indices

\[
2i\pmod{768},\qquad 2i+1\pmod{768}.
\]

The single grid boundary between these two image cells is accounted for in Z. Form a directed graph on V by retaining precisely the edges

\[
i\longrightarrow j
\quad\text{for }j\in\{2i,2i+1\}\pmod{768}\text{ that belong to }V.
\tag{6}
\]

Let A be its 96×96 row-source adjacency matrix, with entries 0 or 1. It has 144 directed edges.

Every θ∈E has an allowed cell itinerary for all n≥0 by (3) and (5b). For an allowed n-edge path (i_0,…,i_n), the cylinder

\[
J_{i_0}\cap d^{-1}(J_{i_1})\cap\cdots\cap d^{-n}(J_{i_n})
\tag{7}
\]

is an open interval of length exactly 1/(768·2^n). Indeed, each chosen target cell in (6) selects one half of the current inverse branch; induction gives a single interval on which d^n maps affinely and bijectively onto J_{i_n}. Every graph path has such a nonempty cylinder. Distinct paths have disjoint interiors. Hence the number

\[
c_n=\mathbf1^T A^n\mathbf1
\tag{8}
\]

is exactly the number of these cylinders and, in particular, an upper bound on the number needed to cover all of E at this horizon. Here c_0=96; horizon n means n edges and n+1 cell visits.

## 4. Exact identities and all-horizon path counts

The finite calculation gives

\[
A^5\mathbf1=2A^2\mathbf1,\qquad
(c_0,c_1,c_2,c_3,c_4,c_5)=(96,144,192,192,288,384).
\tag{9}
\]

Equation (9) can be verified directly from (6). For a human-readable certificate, the value of A²1 at each vertex is grouped below; A⁵1 has exactly twice the stated value on each corresponding group.

| Value of A²1 | Grid-cell indices |
| --- | --- |
| 0 | 83, 84, 107, 108, 166, 167, 168, 169, 214, 215, 216, 217, 275, 276, 299, 300, 467, 468, 491, 492, 550, 551, 552, 553, 598, 599, 600, 601, 659, 660, 683, 684 |
| 2 | 82, 85, 106, 109, 164, 165, 170, 171, 212, 213, 218, 219, 274, 277, 298, 301, 466, 469, 490, 493, 548, 549, 554, 555, 596, 597, 602, 603, 658, 661, 682, 685 |
| 4 | 41, 42, 53, 54, 137, 138, 149, 150, 233, 234, 245, 246, 329, 330, 341, 342, 425, 426, 437, 438, 521, 522, 533, 534, 617, 618, 629, 630, 713, 714, 725, 726 |

For n≥2, multiplying the vector identity in (9) by A^{n−2} and then by 1ᵀ gives c_{n+3}=2c_n. The two missing cases n=0,1 hold by the displayed scalar values. Thus the recurrence is established for **all** n≥0, and induction gives

\[
\boxed{
c_{3k}=96\,2^k,\qquad
c_{3k+1}=144\,2^k,\qquad
c_{3k+2}=192\,2^k
\quad(k\ge0).}
\tag{10}
\]

In particular c_n≤192·2^{n/3} for every n≥0. There is no omitted polynomial prefactor or unexamined transient contribution: (10) counts paths in the **full** 96-state graph, including every transient starting state and every possible exit from its cyclic part.

For an independent structural audit, the exact strongly connected component calculation gives one cyclic component, with vertices

```
82, 85, 106, 109, 164, 165, 170, 171,
212, 213, 218, 219, 329, 330, 341, 342,
425, 426, 437, 438, 548, 549, 554, 555,
596, 597, 602, 603, 658, 661, 682, 685.
```

All other 64 components are single vertices without self-loops. Thus there are no additional cycles. The verifier also checks the exact full-matrix identity A¹³=2A¹⁰. Neither the dimension proof nor the path-count induction requires a numerical spectral calculation or a claim about diagonalizability.

## 5. The measure and dimension theorem

Set n=3k in (7)–(10). For every k≥0, E is covered by at most 96·2^k open intervals of length

\[
\frac1{768\,8^k}.
\]

Their total length is

\[
96\,2^k\frac1{768\,8^k}=\frac18\,4^{-k}\longrightarrow0.
\tag{11}
\]

So Leb(E)=0.

For every s>1/3, the sum of the s-th powers of the covering diameters is

\[
96\,2^k(768\,8^k)^{-s}
=96\,768^{-s}\,2^{k(1-3s)}\longrightarrow0.
\tag{12}
\]

It follows from the definition of Hausdorff measure that H^s(E)=0 for every s>1/3. Moreover, these are finite covers of the whole set E at a sequence of scales whose successive ratio is exactly eight. If N(E,ε) denotes the least number of intervals of diameter at most ε covering E, choose k≥1 such that

\[
\delta_k:=\frac1{768\,8^k}\le\epsilon<\delta_{k-1}=8\delta_k.
\]

Then N(E,ε)≤96·2^k and 8^k<8/(768ε), hence

\[
N(E,\epsilon)<192(768\epsilon)^{-1/3}
\quad\text{for }0<\epsilon<1/768.
\tag{12a}
\]

Using fixed grid boxes instead of arbitrary intervals changes this bound by at most a fixed factor. Therefore

\[
\boxed{\operatorname{Leb}(E)=0,\qquad
\dim_H(E)\le\overline{\dim}_{\mathrm B}(E)\le\frac13.}
\tag{13}
\]

The same two dimension upper bounds apply to each E_j⊂E. This proves upper bounds, not equality, and supplies no lower bound for the actual physical landing set. The exact endpoint exclusion (5b) is what permits the finite whole-set cover and hence (12a); treating the excluded points merely as a countable set would suffice only for the Hausdorff-dimension argument.

## 6. Consequence for every original finite ideal side

The qualitative result uses still less arithmetic. E is closed by continuity of L. It has empty interior by (13), so E is nowhere dense. Equivalently, one can prove this directly from forward invariance and the fact that 1/3 and 2/3 land at the G-fixed dividing point a, which is outside the disjoint three-cycle B; every nonempty angular interval eventually doubles onto the whole circle.

For a W tile with seam (a_j,b_j), the original strict finite ideal sides have unwrapped real coordinates

\[
\xi_j^\circ:\ x<a_j,\qquad \eta_j^\circ:\ x>b_j.
\]

The physical landing is L(x mod 1). The full real inverse image of E is a countable union of integer translates of a set of Hausdorff dimension at most 1/3, so its Hausdorff dimension in this **unwrapped angle coordinate** is at most 1/3. On every bounded side subinterval, only finitely many translates occur, and the upper box-dimension bound also holds. The full inverse image is closed and nowhere dense. Every nonempty subinterval of every original finite J-side therefore contains an open set of angles whose physical landing lies in K3\B, hence in the ordinary fine exterior Ω9.

The actual Case O covering-chart argument extends the specified fine immersion j_W at each of those source points to an ordinary **interior** point of the fine localization. Consequently no nondegenerate original J-side interval maps wholly into the fine target ideal boundary. Existing finite O-side and finite-vertex extension results, plus the finite number of wrapping joints, give the same obstruction on any nondegenerate interval of the entire original W ideal circle.

For the root-only source subset, use A_j=E_0∩(a_j,b_j) to avoid confusing the four seam subsets with the three physical phase sets E_j. Every A_j has Hausdorff dimension at most 1/3 in the angular coordinate and contains no nondegenerate interval. Its integer translates give the corresponding actual root-landing candidates on strict ξ/η sides.

The topological nowhere-density statement transports under a homeomorphic side parametrization. The numerical dimension bound does not automatically transport to a different conformal boundary coordinate. In particular it gives no zero-capacity or zero-width theorem.

## 7. Reproduction and exact scope

From the repository root, run:

```sh
python -B research/independent_audits/issue62_landing_angle_bound_20261123/verify.py --check-certificate
```

To regenerate the complete certificate, use
`--certificate research/independent_audits/issue62_landing_angle_bound_20261123/certificate.json`.

The default command only reads the source checkout. The output certificate records the source SHA-256 hash, the exact grid-endpoint exclusion (5a), all 28 intervals, all 96 vertices and 144 edges, all strongly connected components, and the complete vectors in (9). The Python verifier deliberately retains assertions under `python -O` by using explicit exceptions.

This is an actual physical-to-symbolic estimate conditional only on the stated, written analytic premises. It strengthens Issue 62's item concerning the actual root-landing source subset and rules out promotion of any nondegenerate original side interval into a fully boundary-valued fine end. It does not fill a literal F9 connector word, settle the native KKL proper-restriction/marking comparison, prove the remaining bridge gates, or establish MLC.

## 8. Pinned archive sources

- [Complete source K9-angle exhaustion, §5](https://github.com/dovvnloading/loops-research-archive/blob/ed64c7ad839dcc8b799d53379434f892fdc92a2c/research/independent_audits/tip_native_C4_wake_root_sheet_naturality_20261109.md).
- [Actual phase cycle, landing setup, dividing fixed point and Case O extension](https://github.com/dovvnloading/loops-research-archive/blob/ed64c7ad839dcc8b799d53379434f892fdc92a2c/research/independent_audits/tip_native_finite_J_side_target_trichotomy_20261109.md).
- [The exact W-sector seam data used by the verifier](https://github.com/dovvnloading/loops-research-archive/blob/ed64c7ad839dcc8b799d53379434f892fdc92a2c/results/tip_kl_side_atlas.json).
- [Complete original W ideal-circle decomposition and finite O-side/vertex extensions](https://github.com/dovvnloading/loops-research-archive/blob/ed64c7ad839dcc8b799d53379434f892fdc92a2c/research/independent_audits/tip_native_full_W_ideal_circle_pointwise_extension_20261109.md).
- [Issue 62 connector-defect source domain and retained unwrapped coordinates](https://github.com/dovvnloading/loops-research-archive/blob/ed64c7ad839dcc8b799d53379434f892fdc92a2c/research/independent_audits/issue62_connector_defects_20261116/NOTE.md).
- [Why the literal based connector words remain separate data](https://github.com/dovvnloading/loops-research-archive/blob/ed64c7ad839dcc8b799d53379434f892fdc92a2c/research/independent_audits/issue62_connector_words_20261116/NOTE.md).

## Attribution and review

Prepared with OpenAI GPT-6 Astra Pro for proof search, exact arithmetic and
independent adversarial review. The analytic premises are explicitly cited
above. No human specialist review or Lean formalization has occurred.
