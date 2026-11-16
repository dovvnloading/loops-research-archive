# Direct-at-depth QC audit for primitive-tip towers: uniform modulus, conditional width transport

**Independent additive audit — 2026-11-16.** This note addresses the precise gap in [the merged all-depth audit](../tip_family_all_depths_20261116/NOTE.md). **It does not close the unconditional depth-uniform canonical-KKL-width problem.** It isolates a genuinely non-compounding *complex-bounds/straightening* statement and proves a **conditional** non-compounding width lemma. It records explicitly why the conditional premise does not follow from complex a priori bounds or straightening. No established theorem is upgraded by the rational verifier.

## Verdict and quantifiers

| Statement | Status |
|:--|:--|
| Universal lower bound on *optimal* moduli of directly selected real finite **non-doubling** renormalizations | **Published theorem**, subject to existence/identification of the intended primitive tower |
| Same bound at every finite level of a genuinely infinitely renormalizable real quadratic | **Published theorem**, with no terminal-tip marking asserted |
| At each level, a quadratic-like representative of modulus at least one **fixed** positive number | **Consequence** of the preceding optimal-modulus theorem |
| Hybrid conjugacy near each little filled Julia set, with a single depth-independent bound on QC dilatation | **Consequence**, invoking the *quantitative* straightening lemma identified below; no effective number for K |
| Identification of the straightened parameter with the specified tuned suffix | **Classical tuning/real rigidity input**, not a consequence of the modulus estimate |
| Isomorphism of KKL **global** marked surfaces and their **entire** admissible Wave collections by that same conjugacy | **Open / additional hypothesis**; the natural near-filled-Julia-set conjugacy has no such guaranteed domain |
| Uniform width and crest-ratio bounds if that global family-preserving QC isomorphism exists | **Proved conditional analytic lemma** below; one QC comparison per depth, not a product |
| Depth-three (3,3,3) whole-disk and width inequalities | **Existing exact rational certificate**, independently re-run as a regression; not an all-depth proof |
| All finite primitive words have physical canonical widths bounded away from 0 uniformly, or converge in an infinite tower | **Open** |

## 1. Direct-at-depth complex bounds — no repeated straightening

Let F_c(z)=z²+c. For a finite primitive word w=(p₁,…,p_d) with p_i≥3 put n_j=∏_{i=1}^j p_i and let R_j denote a *central degree-two quadratic-like restriction* of F_c^{n_j}, **not** the globally degree-2^{n_j} iterate. We work only with **actual** designated nested primitive copies and their restrictions, as in the merged audit's H(j); a bare solution of P_{n_d}(c)=0 does not define the tower. Index R_j from j=1, and write χ_j for its straightened quadratic parameter. Intermediate χ_j is identified with the remaining suffix only when the tuning and signed kneading identifications have separately been established. In particular, χ_{d-1} is the single-level p_d-tip in the intended finite tuning construction; χ_d is the *terminal period-three marked model*, and it is **not automatic** that χ_d belongs to the indexed near-(-2) p≥3 family. Do not equate these two straightenings.

**Precise source and exception.** Lyubich–Yampolsky, *Dynamics of quadratic polynomials: complex bounds for real maps*, Ann. Inst. Fourier **47** (1997), pp. 1219–1255, DOI [10.5802/aif.1598](https://doi.org/10.5802/aif.1598), **Theorem 1.1** (conditional on bounded *essential* periods) and the distinct, stronger **“Complex Bounds Theorem” on p. 1220**, obtained together with prior large-essential-period work: there is an **absolute** μ₀>0 such that for every n-times renormalizable *real quadratic polynomial*, mod(R^n F_c)≥μ₀, **unless** the last renormalization is of *doubling type* and near the cusp. Here mod is explicitly defined on p. 1219 as the **supremum over admissible quadratic-like fundamental annuli**, not the modulus of a chosen physical disk. The quoted theorem already covers **finite** n, not just infinite towers, and does not assume bounded combinatorics. The terminal primitive stages here must actually be non-doubling; p_i≥3 is meaningful only together with the established primitive combinatorics. For a truly infinitely renormalizable real quadratic, its finite-level renormalizations are again renormalizable, so the authors explicitly give the universal conclusion without the cusp exception.

Independent context: Levin–van Strien, *Local connectivity of the Julia set of real polynomials*, Ann. Math. **147** (1998), pp. 471–541, DOI [10.2307/120958](https://doi.org/10.2307/120958), **Theorem A in the authors' [1995 preprint](https://www.math.stonybrook.edu/preprints/ims95-5.pdf), pp. 2–3**, constructs polynomial-like extensions with lower modulus depending only on the even critical order for **infinitely renormalizable** real unimodal polynomials (and controlled relative diameter). Its **Main Theorem** is Julia-set local connectivity, **not** local connectivity of the Mandelbrot set. Theorem A is not a replacement citation for a finite-tower all-n statement. Their proof uses cross-ratio/real bounds without a bounded-combinatorics assumption; compare de Melo–van Strien, *One-Dimensional Dynamics* (1993), Ch. VI §§2,5 (real bounds). For the **finite** universal claim use the explicit Lyubich–Yampolsky Complex Bounds Theorem, not Sullivan's bounded-type theorem alone.

**Exact one-step argument.** For every j with a realized non-doubling primitive renormalization, apply the published theorem **directly to F_c at its j-th renormalization**. It follows that sup mod(R_j)≥μ₀, uniformly in j, d, and p_i. Set once and for all μ=μ₀/2. The definition of supremum supplies **some** admissible restriction R_j:V_j→U_j with V_j compactly contained in U_j, proper of degree two, and mod(U_j\overline{V_j})>μ (with connected filled Julia set when the critical orbit is retained). There is no need and no license to choose the preselected round physical gate domains from the earlier audits; their moduli and Rouché gaps are not controlled by this argument. The source theorem provides **no explicit numerical μ₀**.

If c∞ is a genuinely infinitely renormalizable *real* quadratic carrying the prescribed infinite primitive itinerary, repeat the preceding argument at each finite j on **that one map**. The same μ works simultaneously for all j. Existence of nested real copies and rigidity/singleton shrinking are separate tuning inputs: nonempty intersection by itself does not identify a unique parameter or its exact marked itinerary. There is no “last tip” and hence no automatic terminal 10/20 KKL portrait for an infinite word.

**Quantitative QC source, and what it actually states.** Douady–Hubbard, *On the dynamics of polynomial-like mappings*, Ann. Sci. ENS **18** (1985), pp. 287–343, DOI [10.24033/asens.1491](https://doi.org/10.24033/asens.1491), **Theorem 1(a),(b)** gives a *hybrid* conjugacy and uniqueness up to affine conjugation when the filled Julia set is connected, but **does not state K(μ)**. An explicit statement of the needed uniform dependence appears as **M. Lyubich, [Conformal Geometry and Dynamics of Quadratic Polynomials](https://www.dance-net.org/images/files/events/rtns2008/materiales/notes_lyubich.pdf), Lemma 4.33, p. 143**: a quadratic-like map with fundamental-annulus modulus ≥δ has a hybrid straightening by a K(δ)-QC map. The author's notes contain editorial “??” placeholders in parts of the proof, so this is a clearly identified *quantitative lemma statement*, **not** a claimed numerical, peer-reviewed bound supplied by the 1985 theorem. Equivalently the usual uniform-tubing/quasisymmetry compactness construction is an additional standard QC input. In our notation choose **one** K=K_Lyubich(μ)≥1, independent of d,j,w; neither cited result makes it effectively evaluable here. Then a hybrid h_j conjugates each R_j to F_{χ_j} on *some neighborhood of their filled Julia sets*. This is **one h_j per j** and uses neither h_{j-1} nor a product of dilatations. On K(R_j), the map is conformal almost everywhere in the hybrid sense; **not** necessarily conformal on its entire slit complement.

## 2. The marking gap: a precise conditional transport lemma

The terminal **local** combinatorics in the merged audit has one old Hubbard-tree attachment, target ideal atoms I₀,…,I₉ and source atoms S₀,…,S₁₉. Its two operations are **different**:

* Covering pushforward: f_*(S_s)=I_{s mod 10}.
* Proper immersion restriction: ι*(I₀)=(S₁₈,S₁₉,S₀,S₁,S₂), and ι*(I₁),…,ι*(I₉) are respectively (S₃,S₄), (S₅), (S₆), (S₇,S₈,S₉), (S₁₀), (S₁₁,S₁₂,S₁₃), (S₁₄), (S₁₅), (S₁₆,S₁₇).

The source proper endpoint pairs (S₃,S₁), (S₁₉,S₁₇), (S₃,S₁₇) have inclusive source spans (3,3,7) and **cover-pushed** target spans (3,3,5), all passing the strict >2 filter. The old-edge incidence matrix is [[0,0,1],[1,0,1],[1,1,0]]. The I₀ crest is old-edge-free; I₁ and I₉ approach **one** old real edge from opposite sides, not two edges. These are archived *local* constraints, **not** a global count of 10/20 atoms at every physical ancestor. The new verifier checks these typed finite assertions but not their existence as analytic prime ends.

**Additional transport hypothesis T(j;ref).** In addition to a realized, marked primitive restriction and its hybrid h_j, assume there is an orientation-preserving K-QC homeomorphism H between the **entire marked slit surfaces used to define canonical widths at level j and at reference**, whose restriction near the little filled Julia set conjugates the returns, and which:

1. Carries the designated closed marked real Hubbard subtree, its single attached preimage, the two sides of each edge and the selected critical/repelling endpoints to the reference tree with their **cyclic order**; identifies the *actual* crosscut/prime-end completions and each atom I_i, S_s, not merely the abstract real critical itinerary.
2. Maps both the source and target slit surfaces, including **all** admissible path supports, and satisfies the **two separate** naturality diagrams H_target∘f_* = f_*^ref∘H_source and H_source∘ι* = (ι*^ref)∘H_target, interpreting the second equality as equality of **sets of proper paths** (never as a point map).
3. Maps the **full** A.1/A.3.2 KKL canonical Wave class *bijectively in both directions*, preserving eligible >2 proper endpoint arcs, the attachment/crest filter, the two selected proper children when the paired width is considered, and the definitions of the four-push crest descendant families.

An ambient conjugacy near the filled Julia set gives a homeomorphic image of its *included* finite Hubbard subtree and preserves local cyclic order and relative critical orbits. **It does not, by itself, imply (1)–(3)** for the independently defined *physical* KKL slit: the slit may extend beyond its domain, distinct ambient external rays/prime ends may not be transported, and the unrestricted canonical Wave supremum may use curves not contained in that neighborhood. Real symmetry, if needed for a particular real marking, must be chosen/justified; straightening alone does not assert an independently prescribed external marking. Topological equivalence on K does not determine quantitative gate geometry.

**Conditional theorem (non-compounding).** Let W_j* and W_ref* be suprema of extremal widths of *entire* canonical marked Wave families. Under T(j;ref) with H of maximal dilatation at most the same K, for **each matched Wave Γ** the quasiconformal extremal-length inequality (equivalently its reciprocal-width form) gives

    Width(Γ_ref)/K ≤ Width(H^{-1}Γ_ref) ≤ K Width(Γ_ref).

Because the two full admissible families are **bijective**, taking suprema in both directions proves, **for this single level j**,

    W_ref*/K ≤ W_j* ≤ K W_ref*.

This compares level j *directly* to reference, not to j−1. There is **no K^j**. If the reference has strict L_ref < W_ref* < U_ref, then

    L_ref/K < W_j* < K U_ref.

With a separately certified **p_ref≥13** single-level reference, the merged [canonical-width sandwich](../real_primitive_tip_family_canonical_width_sandwich_20261116/NOTE.md) §5 gives **0.26/K < W_j* < 0.78 K**, *conditional on T*. With arbitrary single-level **p_ref≥3** the safe published uniform comparison is instead **0.25/K < W_j* < 0.78 K** (the stronger 0.26 lower bound is **not** certified for p=3 or 4). The merged physical depth-two and (3,3,3) rows separately certify 0.25<W*<0.775 for their **specified physical geometries**, not through a uniform K.

If P is a positive parent Wave width and C its selected four-push descendant width, and **both parent and descendant families are paired by H**, the same two inequalities give for their **ratios**

    (C_ref/P_ref)/K² ≤ C_j/P_j ≤ K² (C_ref/P_ref).

For a ratio of suprema the same bound holds only when the two parent/descendant suprema are each transported as above and P_ref>0; it is **not** an identity of optimizers. The exponent **two**, not one, is essential: numerator and denominator can be distorted in opposite directions. Under the extra finite p=3 physical/KKL hypotheses in [crest-transport tip family](../crest_transport_tip_family_20261116/NOTE.md), its chosen four-push ratio satisfies 0.5676<r₃<0.5684, yielding the *conditional* transported interval 0.5676/K²<r_j<0.5684 K². The other archived coefficients cover **only p=4,…,8**; they do not give an all-p/all-depth crest coefficient. H must carry the specific chosen collars, not just “one edge in the crest.” These conditional ratios are **not** unconditional bounds for all towers.

**Why a one-sided argument fails.** A QC map defined only near K(R_j) can transport some specially selected witness curves; this can give a lower bound for a **carried subfamily** if it is admissible. It cannot give the upper bound for the supremum over **every** physical Wave without a reverse, family-wide inclusion. Neither a thick fundamental annulus nor local connectivity of a real Julia set supplies T or a canonical whole-slit extension. In particular a disk modulus cannot certify the two children, conformal full-plane-slit upper envelope, full round gate, or infinite-depth compactness of Wave optimizers. The central gap from the merged audit remains.

## 3. Locked depth-three consistency, not induction

For w=(3,3,3), (n₁,n₂,n₃)=(3,9,27), the *existing* [all-depth exact verifier](../tip_family_all_depths_20261116/verify.py) certifies the **physical** strict rational margins

| Source quantity | Strict certified number |
|:--|--:|
| first Rouché disk gap | > 0.127470 |
| second Rouché disk gap | > 0.006346 |
| third Rouché disk gap | > 0.003900 |
| separately normalized 81-return gap | > 0.172673 |
| complete radial gate lower width | > 0.252105 |
| complete plane-slit upper envelope | < 0.764704 |

These are **not** the modulus μ₀ and are **not** values of the canonical maximum W*. Subject to the prior named topological/conformal KKL imports they imply the strict physical **0.25<W*_(3,3,3)<0.775**. The inequality “0.26<W*_(3,3,3)” is *not* established by a radial witness >0.252105; its truth or falsehood cannot be inferred from that one witness. The current regression executes the archived verifier unchanged and compares its exact Fraction results to **strict** thresholds above; it does not round a floating estimate or assume Rouché gaps transfer across straightening.

**Proved (new here):** the elementary conditional QC-supremum and two-width-ratio implications, exact finite marking-consistency invariants, and no-compounding algebra. **Imported published:** non-doubling direct universal optimal moduli; DH hybrid straightening; real bounds and Levin–van Strien infinite case. **Quantitative published-status caution:** K(μ) as stated in Lyubich's draft Lemma 4.33 (no numerical K here). **Numerical/exact regression:** the unique depth-three packet above, using unchanged rational interval code. **Still open:** a *global* K-uniform marked-Wave transport T from local hybrid straightening, uniform physical gates/round disks and Rouché errors, a certified 0.26 reference for all p≥3, a uniform all-period crest ratio, and canonical Wave limits for infinite words. Therefore the desired unconditional 0.26/K…0.78K theorem is **not proved**.

## 4. Reproduction and adversarial review

From the repository root, using only standard Python 3.12:

    PYTHONDONTWRITEBYTECODE=1 python -B research/independent_audits/tip_family_depth_uniform_qc_20261116/verify.py
    PYTHONDONTWRITEBYTECODE=1 python -B -m unittest discover -s research/independent_audits/tip_family_depth_uniform_qc_20261116 -p 'test_*.py' -v

The new [dedicated CI workflow](../../../.github/workflows/tip-family-depth-uniform-qc.yml) reruns the exact depth-three certificate, new mutated-marking tests and unchanged local Lean build, and requires separate **existing Research validation and Weighted Lean** workflows at the exact PR head SHA. It rejects generated bytecode and modifications outside the two new paths. It does not claim to machine-prove the cited QC, rigidity, prime-end or KKL theorems.

**Hostile-review checklist:** distinguished R_j from F_c^{n_j} as a global map; finite complex bounds from the **Complex Bounds Theorem**, not Theorem 1.1 alone; supremum of moduli versus a *chosen* annulus; μ=μ₀/2 to handle nonattainment; final doubled-cusp exception; finite and infinite terminal marking distinguished; suffix χ_{j} not conflated with χ_{d}; source/target f_* and set-valued ι* never identified; opposite accesses of one real edge not counted as two; no claimed equality of selected and optimal Wave width; explicit K² for a ratio; p≥13 threshold for 0.26; strict depth-three inequalities rather than false 0.26 certification; and no use of physical Rouché gaps in an iterated straightening argument.
