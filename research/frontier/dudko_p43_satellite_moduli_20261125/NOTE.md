# Problem 4.3: ordinary satellite modulus obstruction / pseudo-Siegel test boundary

**Claim (pre-registration, before arithmetic):** Ordinary degree-two polynomial-like fundamental annuli of genuine nested satellite renormalizations cannot have a uniform positive lower modulus bound when relative periods are unbounded. The quantitative test below evaluates the published universal upper envelope, not a computed conformal modulus of an individual parameter. The proposed use of this observable as a direct test of pseudo-Siegel a priori bounds is ill-posed without a comparison theorem.

**Limits/status:** imported (ordinary PL obstruction, Blokh–Levin–Oversteegen–Timorin); open (Problem 4.3); finite certificate / negative result for the proposed proxy, not a proof of MLC. No individual parameter, pseudo-Siegel disk, or little-copy diameter will be inferred from a rotation denominator. No other archive obligation or ledger status is changed. This is a standalone source/type audit of the survey, not a model-to-geometry bridge for H1–H4.

## Source statements

Dzmitry Dudko, *On the MLC Conjecture and the Renormalization Theory in Complex Dynamics*, [arXiv:2512.24171v1](https://arxiv.org/html/2512.24171v1), §§4.4–4.5. Exact short problem statements (source attribution; not original CC0 material):

- Problem 4.3: “Establish pseudo-Siegel a priori bounds in the remaining unbounded satellite ql cases.”
- Interpolation Problem 4.4: “Develop a Virtual Molecule version of the Near-Degenerate Regime.”

Section 4.5 (source synopsis, not verbatim): for a primitive first ql renormalization near the Molecule, Dudko describes a canonical satellite-copy chain ending at a decoration containing the primitive copy. Puzzle control handles the smaller scales but not the earlier virtual Molecule scales. The latter split into virtual bounded-relative-period satellite and virtual near-neutral cases. The paper proposes partially invariant connected hulls of the little Julia sets, with finite postcritical control, and an a priori version of control otherwise expected from hyperbolicity. It says that Problems 4.3 and 4.4 together with §§4.1–4.4 should yield full MLC, not that this implication has been proved here. Read the original §4.5 at the link for the full wording and formulas. This note does not pursue 4.4. PDF page numbers and SHA-256 are to be extracted by CI (local sandbox cannot resolve arxiv.org); no guessed page numbers or hashes.

### Literature and observable

- Blokh, Levin, Oversteegen, Timorin, *Maps with No a Priori Bounds*, CMP 406:141 (2025), DOI [10.1007/s00220-025-05303-8](https://doi.org/10.1007/s00220-025-05303-8), Main Theorem, p. 2 of 15, definitions 2.3–2.4 and proof §2.2. For a satellite PL cycle of relative period s≥2, with connected filled set K* and quadratic PL restriction F:U→V of degree two, writing m=mod(V∖closure(U)) in the authors' normalization, the theorem gives
  m ≤ mod(U∖K*) < B(s):=2π/log(4(s+1)).
  It applies to each actual satellite level of a quadratic polynomial satisfying the single-contact/base-cycle hypotheses, independently of the choice of admissible ordinary PL domains. This is an upper bound, not a formula or lower bound for m.
- Dudko–Lyubich, *Uniform a priori bounds for neutral renormalization*, [arXiv:2210.09280v2](https://arxiv.org/abs/2210.09280v2), Uniform Bounds Thm 1.1, Mother Hedgehog Thm 1.2, Quasidisk Approximation Thm 1.3 in §1.1 (early version; PDF locations to be checked). These concern external extremal widths for combinatorial intervals of bounded-type Siegel maps, invariant neutral hulls and uniform quasidisk approximations, not ordinary degree-two satellite annuli. The survey Thm 4.2 and (4.7) describe almost-invariant disks, regularization of fjords and sector rescaling. The extension to remaining unbounded satellite ql cases is the open target.
- Kahn–Lyubich, *A priori bounds for some infinitely renormalizable quadratics: IV. Elephant Eyes*, [arXiv:2601.21905v1](https://arxiv.org/pdf/2601.21905v1), p. 1, §4.0.1 p. 9 (E1–E3: rotation 1/q, central occupancy, p=q+b with bounded b), Thm 7.1 p. 16 and §8 pp. 18–19. Their geometric setup and pull-off hypotheses must be checked; the existence of q large and p=q+O(1) alone is not a license to apply it to a pure satellite cycle. In particular a pure satellite cycle has a shared base point; the unbranched annuli asserted in §8 cannot surround one touching piece while avoiding the other. This paper does not provide a blanket ordinary satellite lower bound.

## Frozen quantitative pre-registration

Define a symbolic satellite tuning chain by successive rational relative rotations r_k=a_k/s_k, gcd(a_k,s_k)=1, k≥2, and periods P_1=1, P_k=P_(k-1)*s_k. Use the conventional satellite tuning combinatorics; conclusions are conditional on actual realization with the stated PL cycle at the stage, not existence/uniqueness of a limiting parameter. On the same quadratic f, each actual degree-two return f^(P_k):U_k→V_k has relative period s_k (base period P_(k-1)). The global polynomial degree stays two; do not apply the theorem to a parent straightening across an unverified hybrid collar.

Four chains (fixed before arithmetic):
- linear: r_k=1/k, s_k=k;
- exponential: r_k=1/2^k;
- constant control: r_k=1/2;
- golden convergent comparison: r_k=F_k/F_(k+1), F_1=F_2=1. Although the continued-fraction digits are bounded, these are distinct rational relative rotations at successive satellite levels, so this is **not** a bounded-satellite-relative-period control. It is a second unbounded-denominator diagnostic, not the single neutral golden-mean map.

Sample all chains at k=2,...,32,64,128; additionally linear at 256,1024,1048576. Use exact positive rationals and certified intervals for B only. The finite falsifiable surrogate H(delta): every admissible ordinary PL modulus at the registered stages is ≥delta=1/2 (chosen diagnostic threshold, not a constant from DL). Reject H on a chain if any certified upper endpoint of B is <1/2; otherwise report inconclusive, never pass. This is a necessary-condition test, not measurement of actual moduli. Preregister prediction: linear at k=1048576 and exponential at k=32 reject; golden at k=32 rejects; constant B stays identical and the test is inconclusive. No parameter-plane or orbit computations are planned. Analytic asymptotic test: B(k)=O(1/log k), B(2^k)=O(1/k), B(F_(k+1))=O(1/k); any uniform m>0 is impossible along these realized unbounded chains, and this assertion follows from the imported theorem irrespective of the finite test. Constant control is supported separately by survey Thm 4.1 for bounded ql combinatorics, not by B.

Error protocol: compute ln via binary range reduction and atanh rational series with an explicit positive tail, π via Machin and alternating arctan bounds, 80 terms each, outward decimal endpoints to 40 places, require displayed width ≤ 2×10^-40; assert exact rational comparisons, monotonicity and negative controls. No floating point, randomness or fitted rate. Only B's interval is narrow; the certified enclosure for m itself is (0,B_upper), not [B_lower,B_upper]. If the certificate fails, report failure rather than relax the criteria.

Hostile self-check: the annulus U∖K* and the fundamental annulus are not equal by definition; take the exact stated inequality, do not equate B with either modulus. Filled pseudo-Siegel fjords and sector quotients change the domain and admissible curve family. Neither the comparison of their widths with m nor a comparison between consecutive copy diameters and m is supplied by any cited theorem. A uniform quasidisk does not specify an exterior collar with definite annulus modulus; even concentric round disks permit arbitrarily thin collars. If a future construction gives a positive pseudo-Siegel modulus M_k and m_k≥c M_k for fixed c>0 on these same cycles, this imported obstruction falsifies that bridge (not the pseudo-Siegel conjecture). No such bridge is assumed. This is the bounded negative alternative to a direct Problem 4.3 test.

## Reproduction and records

From repository root (Python 3.12, standard library exact arithmetic, pinned PDF parser for source audit):
```sh
cd research/frontier/dudko_p43_satellite_moduli_20261125
python3 -B verify.py --output results.json
python3 -m pip install -r requirements.txt
python3 -B source_audit.py --output sources.json
```
CI is to record the numerical results, versioned source download SHA-256 and PDF-page markers; source download failure must be explicit, never replaced by a fabricated hash. Numerical result and final source manifest will be separate from this pre-registration commit. No human specialist verification performed; GPT-6.2 used for literature search, reasoning and code generation.

## Results

**No** for ordinary PL a priori bounds on realized unbounded-relative-period satellite chains. This is an imported theorem implication, with a finite exact-arithmetic certificate of its envelope. For pseudo-Siegel a priori bounds themselves the outcome is **not a well-posed test**; no yes/no about Problem 4.3 follows. All 135 registered rows were evaluated locally using exact Python Fraction arithmetic after the pre-registration commit `58d58db061a8c1bf005fdf7b024b8c93e4749b2b`; the frozen summary is `results_summary.json`, checked by the verifier on regeneration. Full rows are written to `results.json` by the verifier. Local run took about 1.3 seconds (Python 3.11-compatible standard library); CI pins Python 3.12.

| Chain | k | Lower endpoint of B | Upper endpoint of B |
|---|---:|---:|---:|
| linear | 32 | 1.2867991384445606775555345959616481419190 | 1.2867991384445606775555345959616481419191 |
| linear | 1048576 | 0.4120327143979468283239485289863640028970 | 0.4120327143979468283239485289863640028971 |
| exponential | 32 | 0.2666094201048480162137785664782561290879 | 0.2666094201048480162137785664782561290880 |
| exponential | 128 | 0.0697286175665722124558105068571794893872 | 0.0697286175665722124558105068571794893873 |
| golden convergents | 32 | 0.3816881905037018274963516707403589868719 | 0.3816881905037018274963516707403589868720 |
| constant | 2 (all) | 2.5285397774261001415531885020520887202836 | 2.5285397774261001415531885020520887202837 |

All displayed B intervals have width 10^-40. Actual m is enclosed only by 0<m<B_upper. First sampled rejection of δ=1/2: linear k=1048576, exponential k=17, golden k=24; constant inconclusive. The preregistered rejection checks at k=32 for exponential and golden both passed. These are not claims that m is close to B or has a matching lower rate.

### Soundness of arithmetic and hostile post-check

For integer x≥2 put e=floor(log2 x) by bit length and y=x/2^e. Then ln x=e ln 2+ln y. For 1≤y≤2, t=(y−1)/(y+1)∈[0,1/3]; the first N=80 terms of 2 sum_{j≥0} t^(2j+1)/(2j+1) are a lower bound, and the omitted positive tail is at most 2t^(2N+1)/((2N+1)(1−t²)). This also bounds ln 2. The alternating series for atan(1/5), atan(1/239) is enclosed by consecutive partial sums; π=16 atan(1/5)−4 atan(1/239). Positive division gives [2π_lower/ln_upper, 2π_upper/ln_lower]. Integer floor/ceiling provide outward endpoints. Each width and the comparisons are asserted exactly; the verifier also checks coprimality, monotonic disjointness of successive nonconstant B intervals, constant equality, and independent coarse π, ln 2 and B(2) bounds. No numerical linearization, finite orbit truncation or floating-point estimates enter.

A priori bounds normally quantify existence of *some* good domains at each scale, not that every arbitrarily chosen restriction has a good collar. The literal frozen H above is stronger than the usual existence hypothesis. This matters for the control: a thin collar may defeat H even when good collars exist. Crucially, BLOT bounds **every** admissible ordinary restriction, so a certified B<δ rejects even the weaker, meaningful existence hypothesis (there exists a collar of modulus ≥δ at each registered level). No post hoc threshold change is used.

For an actual infinite satellite chain, P_k/P_(k−1)=s_k by the definition of relative period; the BLOT hypothesis requires the connected PL sets meet only at the single base point as specified in their Main Theorem. Under that hypothesis the bound holds at every k, so the supremum of the ordinary fundamental annulus moduli over all admissible restrictions is at most B(s_k). If s_k→∞ this supremum tends to zero. For linear s=k, B∼2π/ln k; exponential s=2^k gives B∼(2π/ln 2)/k; Fibonacci denominators yield B∼(2π/ln φ)/k with φ=(1+√5)/2. These are asymptotics of the envelope; the actual moduli may vanish much faster. For unbounded but not divergent s_k, a subsequence suffices to rule out a positive uniform bound. No unique parameter or infinite tuning-limit realization is required for this conditional application. We do not claim existence of the infinite cascades with a unique limiting parameter, which would beg a rigidity question.

### Why this fails as a direct P4.3 experiment; next admissible observable

A pseudo-Siegel disk is almost invariant, and its fjord filling can remove an exterior bottleneck that a genuine small Julia-set PL cycle cannot ignore. A genuine fundamental annulus must separate a compact inner domain from its outer boundary in the original plane; a sector renormalization or filled-fjord regularization may have different boundaries, quotient identifications and admissible paths. No conformal equivalence, monotonic comparison in the needed direction, or uniform distortion constant is provided. The theorem-based degeneration is therefore compatible with the survey's proposed bounded *regularized* geometry. It is not contrary evidence about it. To make a follow-up falsifiable, first specify the source-defined pseudo-Siegel disks/sector charts, dams, first-return horizon and curve family at each actual complex satellite level, then certify either their normalized external interval extremal widths (uniform upper test) or a source-defined collar modulus (uniform lower test); certify the physical identification and any transport before numerical comparison. Denominator-only tuning codes cannot select these domains. The constant control is not a measurement, and the golden convergent comparison is not a bounded-relative-period control.

**Not established:** actual annulus measurements or exact modulus values; a sharp decay rate for m; any pseudo-Siegel bound or counterexample; existence/uniqueness of a limit of the prescribed tuning chains; actual copy diameters or their ratios; domain construction or a regularized-to-ordinary modulus bridge; Problem 4.4, full MLC, any ledger gate or a new imported theorem. The sole positive mathematical input is the published Main Theorem, applied with its stated hypotheses. The numerical component is a finite certificate of its bound, not independent empirical evidence of new dynamics.

Source audit below is separately generated in CI. Reproduce source audit and note insertion with `python3 -B source_audit.py --output sources.json --update-note NOTE.md`. The source survey HTML verified the two short problem statements and the section synopsis; the full section is linked rather than reproduced. The PDF byte hashes and page locations are not claimed until downloaded and checked.

<!-- SOURCE_AUDIT_BEGIN -->
Source audit pending.
<!-- SOURCE_AUDIT_END -->
