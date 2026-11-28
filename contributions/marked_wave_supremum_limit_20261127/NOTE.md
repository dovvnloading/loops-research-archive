---
ledger: NOV26_OPEN_OPTIMAL_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; mathematical investigation, Lean implementation and adversarial review
human_review: none
---

<a id="marked-wave-supremum-limit-20261127"></a>

# Quantitative convergence of the complete actual parent Wave supremum

## Claim

For every sequence of quadratic parameters satisfying the archive's existing
`NearTwoTip.ActualTip` predicate, the complete unrestricted parent slit-Wave
suprema converge to a finite limiting marked-plane supremum. The parameters
exist by a previously compiled construction. The new theorem supplies an
explicit finite-period error estimate and proves the same statement in the
original dynamical disks, with literal critical-orbit marks and relative
homotopies contained in those disks.

This advances the convergence clause of `NOV26_OPEN_OPTIMAL_LIMIT`. The
remaining identification with the narrower named canonical parameter
selection, the external ideal-boundary terminology, and the other clauses of
the composite obligation are stated under **Boundary**. The ledger is unchanged.

### Exact objects and quantifiers

Write

\[
 f_c(z)=z^2+c,\qquad x_j(c)=f_c^j(0),\qquad d_p=x_p(c_p)>0.
\]

For every integer \(p\ge17\), `ActualTip p c_p` requires
\(c_p\in[-2,-2+20\,4^{-p}]\), \(0<d_p\le12\,4^{-p}\), the
normalized coefficient `kappa p c_p` in \([1.7903,1.7904]\), the exact signed
relation \(x_{6p}+x_{3p}=0\), \(x_{3p}<0\), and
\(|x_j|\le2\) for \(j\le p\). These are the existing definition and
existence theorem in
[`NearTwoTip.lean`](../../formalization/weighted/NearTwoTip.lean).
The universal convergence theorem accepts **any** sequence satisfying that
predicate; the existential endpoint constructs such a sequence in Lean.

The physical outer disk, slit, and two ending atoms are exactly

\[
 U_p=D(0,2^{-p}),\qquad [x_{2p},x_p],\qquad
 (x_{5p},x_{3p})_{\rm lower},\ (x_{5p},x_{3p})_{\rm upper}.
\]

A parent leaf is an arbitrary continuous arc, injective on its open parameter
interval, with interior in the slit complement, initial and terminal ends on
the indicated opposite banks, and a literal endpoint-fixed homotopy to a simple
reference arc passing to the left of the slit. Physical endpoints may coincide
because their slit-bank accesses differ. A parent Wave is an arbitrary family
of such arcs with pairwise disjoint interiors and **Borel geometric support**.
There is no Borel leaf-space, smoothness, finite-length, optimizing-foliation,
or transverse-measure assumption.

For a family of traces \(\Gamma\), the conformal modulus is

\[
 \operatorname{Mod}(\Gamma)
 =\inf_{\rho}\int_{\mathbb C}\rho^2\,dA,
 \qquad \int_S\rho\,d\mathcal H^1\ge1\quad(S\in\Gamma),
\]

where the infimum ranges over all measurable nonnegative extended-real
densities. Hausdorff one-measure on the simple trace imposes no rectifiability
restriction. Let \(P_p\) be the supremum of these moduli over **all** parent
Waves just defined. `physicalParentWidth` is this complete supremum in the
original disk.

Let \(Q_k(z)=1-kz^2\), and let \(k_*\in[1.7903,1.7904]\) be the unique
root of

\[
 Q_{k_*}^{6}(0)+Q_{k_*}^{3}(0)=0.
\]

Put

\[
 a_*=(Q_{k_*}^{2}(0),Q_{k_*}^{5}(0),Q_{k_*}^{3}(0),1),\qquad
 a_p=(x_{2p}/d_p,x_{5p}/d_p,x_{3p}/d_p,1).
\]

The limiting width \(P_\infty\) is the same complete marked supremum in the
plane minus the slit with cuts \(a_*\). Lean proves the finite real limit

\[
 P_p<\infty,\qquad P_\infty<\infty,\qquad
 \boxed{P_p\longrightarrow P_\infty}.
\]

### Explicit finite-period comparison

Define

\[
 E_p=\sum_{i=0}^{3}|a_{p,i}-a_{*,i}|,\qquad
 B_p=4\cdot3906\cdot23646\cdot4^{-p},\qquad
 D_p=\left(\frac{1+100E_p}{1-100E_p}\right)^2.
\]

For every actual tip with \(p\ge30\), Lean proves

\[
 0\le E_p\le B_p<\frac1{200},
\]

\[
 \boxed{P_p\le D_pP_\infty,\qquad
 P_\infty\le D_pP_p+\frac{3\pi}{p-10}},
\]

and the real absolute-error estimate

\[
 \boxed{|P_p-P_\infty|
 \le1600B_pP_\infty+\frac{3\pi}{p-10}}.
\]

The constants are explicit and not optimized. No compactness radius depending
on an unknown maximizing Wave appears in the estimate.

## Evidence

### The obstruction overcome

Convergence of orbit coordinates does not itself prove convergence of a
supremum over all disjoint path families. A limiting Wave can contain leaves
reaching arbitrarily far out. Selecting its bounded leaves need not preserve
the required Borel geometric support. Treating either step as automatic would
leave the extremal problem unresolved.

The proof controls every escaping leaf by a common metric and compresses the
**entire** Wave to retain its bounded leaves within a valid Borel Wave. This
permits a uniform passage to the unrestricted supremum.

### Proof

1. **Transport all four marks.** A piecewise-linear horizontal perturbation
   is constructed from disjoint tent functions of radius \(r=1/100\).
   It maps each limiting cut to the actual cut, has displacement at most
   \(E_p\), forward Lipschitz constant \(1+E_p/r\), and inverse Lipschitz
   constant \((1-E_p/r)^{-1}\). The actual map transports the complete Borel
   Wave, the banks, and the entire relative homotopy. Hausdorff length and
   planar area inequalities prove the modulus comparison by constructing a
   transported admissible density. Width transport is proved, not assumed.

2. **Control all escaping leaves.** On \(N\) disjoint dyadic shells of inner
   radii \(r,2r,\ldots,2^{N-1}r\), use density \(1/(N2^jr)\) on shell
   \(j\). A connected trace joining the inner disk to radius \(2^Nr\)
   projects across every radial interval. The one-Lipschitz norm map and the
   Hausdorff-measure inequality make the density admissible even for
   nonrectifiable traces. Its area is exactly \(3\pi/N\).

3. **Keep the Borel family intact.** A continuous injective coordinate map
   fixes \([-R,R]\) and maps the line into \((-R-1,R+1)\). Applied to both
   coordinates, it compresses the whole Wave into the disk of radius
   \(2(R+1)\), preserves its Borel support and relative class, and fixes every
   originally bounded leaf. Modulus subadditivity handles the escaping traces
   without requiring either selected subfamily itself to be a Borel Wave.
   Thus the full plane supremum is at most the bounded-domain supremum plus
   \(3\pi/N\).

4. **Use literal dynamical estimates.** Finite-iterate estimates prove
   \(E_p\le B_p\), strict order of every actual mark, and normalized outer
   radius \(2^{-p}/d_p\ge2^p/12\). The limiting endpoint radius is less
   than \(4\). For \(p\ge30\), the choice \(N=p-10\) fits the compressed
   family and its displacement strictly inside the actual normalized disk.
   This proves both comparisons. The inequality
   \(1\le D_p\le1+1600E_p\) gives the displayed real error bound.

5. **Return to the physical problem.** Multiplication by \(d_p>0\) preserves
   the entire supremum exactly. It scales both real coordinates; the density
   and area factors cancel. An explicit contraction and homotopy concatenation
   reflect every selected plane-slit homotopy into the finite target disk.
   Scaling back proves that requiring relative homotopies inside \(U_p\)
   leaves the complete supremum unchanged.

6. **Prove finiteness.** Every opposite-bank leaf crosses the real line
   outside the slit, a definite distance from its starting endpoint. A single
   bounded-disk density is admissible for all such leaves and has finite area.
   It bounds all suprema at once. No optimizer or attainment theorem is used.

### Lean endpoints and module map

| Source | Main checked content |
|---|---|
| [SlitWaveModulus.lean](../../formalization/weighted/SlitWaveModulus.lean) | Density infimum, subadditivity, length and area transport |
| [SlitWaveEscape.lean](../../formalization/weighted/SlitWaveEscape.lean) | Common escape density with exact area \(3\pi/N\) |
| [MarkedSlitTransport.lean](../../formalization/weighted/MarkedSlitTransport.lean) | Complete Borel parent family, marked map and class transport |
| [MarkedSlitCompression.lean](../../formalization/weighted/MarkedSlitCompression.lean) | Whole-Wave compression retaining bounded leaves |
| [MarkedSlitDiskHomotopy.lean](../../formalization/weighted/MarkedSlitDiskHomotopy.lean) | Relative homotopies inside finite disks |
| [SlitWaveFinite.lean](../../formalization/weighted/SlitWaveFinite.lean) | Common finite-area metric for every parent leaf |
| [SlitWaveLimit.lean](../../formalization/weighted/SlitWaveLimit.lean) | `width_tendsto_of_mark_convergence` for the complete supremum |
| [ActualParentMarks.lean](../../formalization/weighted/ActualParentMarks.lean) | Literal orbit cuts, their order and error, disk exhaustion |
| [SlitWaveScaling.lean](../../formalization/weighted/SlitWaveScaling.lean) | `width_dilation_ball`, exact physical scaling |
| [ActualParentSupremum.lean](../../formalization/weighted/ActualParentSupremum.lean) | `physical_parent_optimum_real_converges`, `exists_physical_parent_optima_converging` |
| [ActualParentRate.lean](../../formalization/weighted/ActualParentRate.lean) | `physical_parent_period_comparison`, `physical_parent_real_error`, `physical_parent_disk_supremum` |

All eleven modules compile with the repository's pinned Lean and mathlib
versions. The unchanged
[CI run 46101186667](https://github.com/dovvnloading/loops-research-archive/actions/runs/46101186667)
on proof commit `80445d61e3658c560a96b29ab186fa5f40606344` completed the full
build (9108 jobs) and the transitive axiom audit of **all 216 weighted-project
modules and 5223 declarations**. That audit includes all 497 declarations
generated for these eleven new modules in CI and allows only `propext`,
`Classical.choice`, and `Quot.sound`. Explicit local axiom reports for the four
principal physical endpoints give exactly those same three foundations.
No proof holes or new axioms are introduced.

Every new source and public theorem is registered through the repository's
existing contribution script, and the non-draft contribution check passes.
Older modules' original imports, project checkers, and CI workflows are
unchanged. The later attribution and validation update changes this note only;
the Lean sources remain identical to the successful proof commit.

## Dependencies

### Prior work and novelty

The archive explicitly leaves convergence of the unrestricted optimum open in
[`THEOREM.md`, Open Problem 2](../../research/tip_family_theorem/THEOREM.md).
Its preceding Corollary 2 proves convergence only for the orbit-centered round
witness. The complete-path argument in
[`H3_WIDTH.md`, Section 7.2](../../research/independent_audits/maximal_native_wave_20261123/H3_WIDTH.md)
provides uniform tail bounds and explicitly does not give continuity of
optimizers. Neither supplies the complete-supremum convergence or uniform
finite-period comparison proved here.

Parameter existence and coefficient estimates come from
[`NearTwoTip.lean`](../../formalization/weighted/NearTwoTip.lean),
[`NearTwoShooting.lean`](../../formalization/weighted/NearTwoShooting.lean),
[`LimitingCrestParameter.lean`](../../formalization/weighted/LimitingCrestParameter.lean),
and the archived finite-iterate perturbation estimates. They are dependencies,
not claimed as new results of this contribution.

The concrete parent class follows the explicit slit atlas in
[`maximal_native_wave_20261123/NOTE.md`](../../research/independent_audits/maximal_native_wave_20261123/NOTE.md),
Sections 2 and 4, and its full-path treatment in `H3_WIDTH.md`, Section 3.
The current Lean proofs establish the concrete bank, relative-class,
finite-disk, and physical-dilation statements directly. They do not insert an
unproved native-width transport premise into the limit theorem.

Modulus, Lipschitz distortion, Hausdorff-measure transport, and annular cutoff
are classical tools. The new claim is the complete actual-family comparison
and convergence obtained by the uniform whole-Wave argument. The archive
comparison supports novelty relative to the inspected prior work; this
contribution does not certify worldwide priority.

In particular, general qualitative exhaustion is classical: Nobuyuki Suita,
[*On a continuity lemma of extremal length and its applications to conformal
mapping*](https://www.jstage.jst.go.jp/article/kodaimath1949/19/2/19_2_129/_pdf/-char/en),
Kodai Math. Sem. Rep. **19** (1967), 129-137, Section 3, Lemma 1, proves
continuity for increasing curve families. James A. Jenkins,
[*On the existence of certain general extremal metrics II*](https://www.jstage.jst.go.jp/article/tmj1949/45/2/45_2_249/_pdf/-char/en),
Tohoku Math. J. **45** (1993), 249-257, Theorem F and Section 2, provides
classical exact extremal-domain theory and discusses boundary-path extensions.
These results are relevant prior art, not new assertions of this contribution.

KKL [Appendix A.2.3](https://arxiv.org/html/2606.27272v1#A1.SS2.SSS3) gives
additive-error maximality of the canonical WAD, while Section 6.1 chooses a
nearly maximal Wave; those statements do not supply the displayed physical
finite-period estimate. Applying general exact extremal-domain theory to this
particular marked boundary-parallel class would itself require an identification
argument. This proof instead establishes the complete Borel-Wave comparison
directly. Its research claim is the explicit uniform actual-tip estimate and
its complete-family application, including the geometric measurability and
physical-disk class arguments, rather than a new principle of extremal-length
continuity or a new general attainment theorem.

## Boundary

- **Parameter selection.** The theorem concerns every actual quadratic tip
  satisfying `NearTwoTip.ActualTip`, and includes a proved construction of such
  tips. It does not identify that construction in Lean with the narrower
  uniquely named signed kneading chart
  \(14\,4^{-p}<c_p+2<16\,4^{-p}\), nor prove its prefix itinerary, least
  preperiod, or primitive period. Those predicates are absent from the existing
  `ActualTip` definition. The canonical selection bridge remains explicit,
  as in earlier actual-tip contributions.
- **Ideal-boundary vocabulary.** The proved family uses literal simple arcs,
  banks, Borel geometric support, and full relative homotopies in the physical
  disk. Reading it as the externally defined KKL A.1 optimum consumes the
  archive's written intrinsic ideal-slit atlas. A full Lean development of that
  external ideal-circle formalism and its equivalence is not supplied here.
  The limiting plane-slit end at infinity is a cusp, so the limit is called
  the limiting marked-plane supremum rather than asserted to satisfy every
  no-cusp standing hypothesis of A.1.
- **Remaining extremal questions.** No exact value, attainment, uniqueness of
  an optimizer, or new Lean positivity theorem is claimed. Independent child
  optima, the paired or covering-restricted optimum, and immersion-based
  restrictions are not addressed by these parent theorems.
- **Global scope.** The composite ledger entry remains open. This contribution
  proves its analytic parent convergence mechanism for the specified actual
  family and a quantitative estimate uniform over all its admissible Waves.
  It does not prove global H1-H4, UPTCR, or MLC.

## Attribution

The mathematical definitions and physical target are from the cited archive
and its cited KKL source. The proof uses mathlib's formal measure theory,
topology, and real analysis at the repository's pinned versions. New proof
design, Lean implementation, and adversarial review were AI-assisted by
OpenAI ChatGPT, GPT-6 Astra Pro. No human mathematical review has been recorded.
