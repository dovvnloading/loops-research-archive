---
ledger: H4_RIGIDITY
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro
human_review: none
---

# Connected-fiber detection by finite sampling energy

<a id="fiber-sampling-energy-20261127"></a>

## Claim

This packet develops an independent metric-sampling criterion for the terminal fiber and neighborhood requirement in H4. Its substantive estimate is the following complete Lean proof source, whose compilation status is recorded under Validation.

Let K be a preconnected subset of a pseudometric space. Let s : I → X be a finite indexed sample family, let a be any point of X, and put

$$
E(s,a)=\sum_{i\in I}d(s_i,a)^2.
$$

Assume every point of K lies within distance r of a sample. If x,y belong to K and 0 < r ≤ d(x,y)/8, then

$$
\boxed{d(x,y)^3\le 1024\,r\,E(s,a).}
$$

The samples and center need not belong to K. The theorem assumes neither compactness nor path connectedness. The constant 1024 is explicit and universal; optimality of the constant is not claimed.

The packet also proves finite stopping certificates, a connected-fiber triviality criterion, quotient/homeomorphism consequences, a direct local-connectivity criterion on metric spaces, and a conditional specialization to the actual bounded-critical-orbit Mandelbrot set. Explicit interval and two-point constructions delimit the hypotheses. **No actual infinitely renormalizable parameter is shown to satisfy the new certificate hypothesis.**

## Evidence

### 1. The archive's exact remaining hypothesis

At base commit [665e5f942d6b39902272fe6d8ca2dee6fbca8a6f](https://github.com/dovvnloading/loops-research-archive/commit/665e5f942d6b39902272fe6d8ca2dee6fbca8a6f), the ledger marks UPTCR_IMPLIES_MLC as a proved conditional implication. Its separate, still-open hypothesis is UNIVERSAL_PROTECTED_TOWER_CLOSURE. The full statement is [Proposition UPTCR](../../research/mlc_unified/mlc_closure_proposition.md), §§3–7.

That hypothesis asserts that every infinitely renormalizable quadratic admits one jointly realized six-clause package, with constants chosen before the polynomial and independent of the unbounded combinatorial data. The clauses are protected carrier, analytic realization, finite response, backward transition, coercive compactness, and terminal rigidity. The sixth already includes singleton parameter fibers and connected relative neighborhoods. H4_RIGIDITY is the terminal gate; its H3_COERCIVITY prerequisite is also open.

The actual ledger statement being addressed is:

> Controlled marked towers yield connected relative parameter neighborhoods forming a basis at the parameter with diameters tending to zero, either directly or through a precisely applicable trivial-fiber theorem.

[ResearchGates.lean](../../ResearchGates.lean) verifies composition of abstract predicates and explicitly requires the geometric terminal bridge. It does not instantiate those predicates with the full quadratic analytic construction. The archive's own [novelty/value audit](../../research/mlc_unified/novelty_and_value_audit_20260725.md), §9, explains why including terminal shrinking in a package does not prove that difficult clause.

This contribution uses no KKL Wave, marked width, collar, protected carrier, telescope, or tip-family theorem. The only archive dynamics imported by the final specialization is the genuine critical orbit and its already-proved escape characterization.

### 2. The imported pattern: metric sampling and quantitative support detection

The pattern is to distinguish average concentration from coverage of an entire connected support.

A positive-diameter connected set cannot be represented by only two isolated outliers: a continuous distance coordinate takes every intermediate value. A sufficiently fine sample cover must therefore pay for many *different* sample witnesses. Counting those witnesses before dividing by the sample count turns geometric extent into a lower bound on unnormalized quadratic energy.

This is a geometric-inference/metric-entropy pattern. The new research proposal is to certify a parameter fiber through the coupled quantity rE, including a genuine covering proof, rather than transport the archive's marked analytic state. Finite samples may be arithmetic parameters, but the formal results do not assume or prove an arithmetic realization.

### 3. Proof of the cubic estimate

[ConnectedFiberEnergy.lean](../../formalization/weighted/ConnectedFiberEnergy.lean), theorem connected_cubic_energy_bound, gives the following argument entirely inside Lean.

1. Write D=d(x,y). By the triangle inequality, at least one endpoint b is at distance at least D/2 from a. Let c denote the other endpoint.
2. Set N=floor(D/(16r)). The map z ↦ d(b,z) is continuous on the preconnected set K and takes the values 0 and D. The intermediate value theorem supplies N+1 sites p_j with
   $$
   d(b,p_j)=4rj,\qquad 0\le j\le N.
   $$
   Every site lies within radial distance D/4 of b.
3. Different sites have distance at least 4r, by the reverse triangle inequality. A sample within r of one site cannot also be within r of another. The witness selector is therefore injective; this is proved explicitly in [FiberSamplePacking.lean](../../formalization/weighted/FiberSamplePacking.lean).
4. Every selected sample has distance at least D/2-D/4-r ≥ D/8 from a. Summing its nonnegative contribution gives
   $$
   E(s,a)\ge (N+1)D^2/64.
   $$
5. The floor inequality gives D < 16r(N+1). Multiplication yields the displayed cubic bound.

This argument uses preconnectedness rather than a chosen path. It works with repeated entries in the original sample family because injectivity of the selected *indices* is proved from separation.

### 4. A finite stopping certificate

Theorem finite_energy_certificate accepts a certified numerical upper bound B ≥ E(s,a). Given a desired pair-distance tolerance δ>0, it assumes

$$
0<r\le\delta/8,\qquad 1024rB<\delta^3,
$$

and the actual radius-r covering of K. It concludes that every x,y in K satisfy d(x,y)<δ. Thus the numerical part can be checked using rational upper bounds; the energy itself need not have a closed form.

Theorem finite_cell_energy_certificate makes the covering interface explicit. It assumes a finite indexed family of cells C_i with

$$
K\subseteq\bigcup_i C_i,
\qquad
\forall i\ \forall z\in C_i,\quad d(z,s_i)\le r,
$$

together with the same energy budget. The cell containment is a mathematical premise. Merely drawing or enumerating cells is not a proof that they enclose the intended fiber.

### 5. All-scale fiber collapse and decomposition

[FineEnergyCertificates](../../formalization/weighted/FiberEnergyCollapse.lean) is the exact proposition

$$
\forall\varepsilon>0\ \exists n,s,a,r:\quad
0<r<\varepsilon,\quad rE(s,a)<\varepsilon,
\quad K\subseteq\bigcup_{i<n}\overline B(s_i,r).
$$

The samples, center, radius, and sample count may all change with ε. Theorem subsingleton_of_fineEnergyCertificates proves that a preconnected K with these certificates has at most one point. A hypothetical pair at distance D>0 is ruled out by choosing ε=min(D/8,D³/2048). The converse holds in a nonempty ambient space by a one-point zero-energy sample. Hence the criterion is exact for preconnected sets; it does not assert that constructing its certificates is easy.

For a map q with preconnected fibers, certificates on every fiber imply injectivity. If q is a quotient map, it is consequently a homeomorphism. A continuous surjection from a compact metric space to a Hausdorff space is covered as a special case. If that quotient space is locally connected, so is the source.

These consequences require the actual quotient or the stated compact/Hausdorff interface. No unconstructed model of M is silently used.

### 6. A direct local-connectivity reduction on the actual Mandelbrot set

Theorem locallyConnectedSpace_of_local_energy_certificates needs no quotient. At every point x of a metric space and every ε>0, assume there exists a **relative neighborhood** K of x, preconnected and covered by finite samples at radius r, such that

$$
0<r\le\varepsilon/8,
\qquad
1024rE(s,a)<\varepsilon^3.
$$

The finite estimate forces K inside the ε-ball about x. The resulting connected neighborhood basis proves local connectivity. The premise K ∈ 𝓝(x) is indispensable; containing x alone would not supply a neighborhood.

[MandelbrotSamplingReduction.lean](../../formalization/weighted/MandelbrotSamplingReduction.lean) defines the actual locus by

$$
M=\{c\in\mathbb C:\exists B\in\mathbb R\ \forall n,
\ |f_c^n(0)|\le B\},\qquad f_c(z)=z^2+c.
$$

The existing QuadraticEscape.parameterEscape_zero_iff identifies this definition with the zero set of the actual parameter escape potential. The module verifies that equality and closedness. The theorem quadratic_mlc_of_local_energy_certificates then applies the direct local criterion to the **subtype M with its relative topology**. In this specialization the samples and center are parameters in M.

This is a proved conditional reduction with a concrete sufficient hypothesis. It is not a proof of that hypothesis and is not a new established MLC case.

### 7. Three proved boundaries

[FiberEnergySharpness.lean](../../formalization/weighted/FiberEnergySharpness.lean) supplies three explicit stress tests.

**Squaring the radius makes the criterion false.** The grid i/n, 0≤i≤n, covers the whole unit interval at radius 1/n and has energy about zero at most n+1. Thus, for every ε>0, the fixed compact connected non-singleton interval has a cover with r<ε and r²E<ε. Theorem quadratic_radius_weakening_counterexample packages the contradiction to that proposed weakening. This proves failure of the squared-radius variant, not optimality of 1024 or a theorem about every real exponent.

**Dropping connectedness makes the criterion false.** The compact two-point set {0,1}, sampled exactly, satisfies FineEnergyCertificates with energy 1 and r=ε/2, while remaining nontrivial. This is disconnected_fine_energy_counterexample.

**Normalized second moments can hide a connected support.** Retain one copy of the interval grid and add n(n+1) zero entries. There are (n+1)² sample indices; the total energy is unchanged and the normalized energy is at most 1/(n+1). The whole interval is still covered at radius 1/n. Theorem unit_interval_normalized_energy_certificates proves arbitrarily small mesh and arbitrarily small normalized second moment simultaneously.

The last construction allows repeated entries. It refutes a criterion for unrestricted indexed samples. It does not refute a specialized theorem exploiting distinct Galois conjugates, canonical heights, or additional arithmetic structure. The code proves the stated second-moment fact; it does not claim a separate weak-convergence theorem.

### 8. Prior work and novelty boundary

Fiber methods themselves are established: Dierk Schleicher, [On Fibers and Local Connectivity of Mandelbrot and Multibrot Sets](https://arxiv.org/abs/math/9902155), treats trivial fibers as a route to local connectivity. The archive already contains nested-compact shrinking in Lemma 7.1 of its closure proposition, and common-cut quotient criteria in StationaryFiberDynamics.lean. None of these is represented as new here.

Related metric sampling ideas are also established. Eddie Aamari, *Rates of Convergence for Geometric Inference*, doctoral thesis (2017), [Chapter III](https://www.math.ens.psl.eu/~eaamari/files/Aamari_PhD_thesis.pdf), Lemma III.12 and Proposition III.14, relates connected-support diameter to covering counts and studies sampling under local mass bounds. Those results are background, not imported axioms in this Lean proof.

Arithmetic equidistribution has a substantial literature, including Favre–Gauthier, [Distribution of postcritically finite polynomials](https://arxiv.org/abs/1302.0810), and Gauthier–Vigny, [Part II: Speed of convergence](https://arxiv.org/abs/1505.07325). Those results are not substituted for the uniform covering and radius-energy estimates required here.

The cubic certificate, its formal connected-fiber/local-neighborhood reductions, and the explicit weakening tests were independently developed for this packet. Targeted archive and literature searches found no identical MLC sampling-energy criterion. That search is **not a proof of worldwide priority**. The packing tools are classical, and this elementary consequence may have appeared elsewhere. The contribution is the precisely stated and checked theorem package and a proposed independent bottleneck, not a claim that metric entropy, fibers, or arithmetic dynamics have never previously been connected.

### Validation

There are five proposed default-target Lean modules and 34 public theorem declarations in the final source package. All are registered in the existing source and theorem indexes. The repository's unchanged Lean 4.32.0 / pinned Mathlib workflows compile the proof sources and audit every compiled declaration.

**Current checkpoint: CI compilation and transitive dependency audit pending.** Source/registration and contribution-intake checks passed on the preceding committed checkpoint. This paragraph will be replaced with exact successful commit/run evidence after validation. Until then the complete sources are proof candidates, not a claimed passed build.

Local Lean installation could not fit the available scratch storage. Ordinary cleanup could not start after the disk filled, and the sandbox policy rejected an exact cleanup escalation. No local compilation is claimed. Development and validation continue through the GitHub connection and unchanged CI; no workflow, trust policy, toolchain, or validator has been weakened.

Reproduce with the pinned project:

~~~sh
cd formalization/weighted
lake exe cache get
lake build FiberSamplePacking ConnectedFiberEnergy FiberEnergyCollapse FiberEnergySharpness MandelbrotSamplingReduction
lake build
cd ../..
python code/verify_lean_coverage.py --audit weighted
python code/contribute.py check
~~~

The early draft PR, finite packing checkpoint, cubic proof, formal counterexamples, subsequent corrections, and final validation are preserved as successive commits. No force push or ledger promotion is used.

## Dependencies

- Research target: H4_RIGIDITY. H3_COERCIVITY, H4, UNIVERSAL_PROTECTED_TOWER_CLOSURE, and MLC remain open; none is a premise secretly supplied by this packet.
- Mathlib at pinned commit 81a5d257c8e410db227a6665ed08f64fea08e997: metric triangle inequalities, finite sums, the intermediate value theorem for preconnected sets, natural floors, topology of quotient/homeomorphism maps, connected neighborhood bases, and elementary real arithmetic.
- [QuadraticEscape.lean](../../formalization/weighted/QuadraticEscape.lean): the genuine quadratic orbit, parameterEscape_zero_iff, and continuity of the parameter escape potential. Only the actual-locus specialization imports this module.
- The cited dynamics and geometric-inference papers provide context, not unformalized theorem assumptions for the compiled results.

## Boundary

No H1–H4 gate, UPTCR clause, ledger status, or MLC case is promoted. Actual quadratic certificates at infinitely renormalizable parameters remain open.

To use the direct MLC reduction, one must construct the actual connected relative parameter neighborhoods at every scale, prove their complete finite enclosure or covering, and prove the coupled energy budget. To use the fiber route, one must identify the actual connected fibers, construct their covers and rate, and justify the applicable quotient/local-connectivity interface.

Finite source labels, numerical sample clouds, global marginal equidistribution, or small normalized variance do not supply those premises. The uniform statements over an entire fiber or relative neighborhood cannot be replaced by tests on its listed sample points. One successful finite certificate proves one scale.

This is an independent metric criterion and a conditional application to the actual parameter locus. The constant is not optimized, the repeated-sample obstruction has the scope stated above, and worldwide novelty has not been established. Independent human specialist review is outstanding.

## Attribution

The research direction and archive stewardship belong to Matthew Robert Wesney. The existing dynamics and formal infrastructure retain their original attribution. Classical metric, topology, and arithmetic literature is cited above.

OpenAI ChatGPT, GPT-6 Astra Pro developed the new proof package and note. Parallel AI work checked the archive bottleneck, proof interfaces, metric packing, quantitative consequence, explicit counterexamples, and the relative-topology boundary. These are AI checks; human_review remains none.
