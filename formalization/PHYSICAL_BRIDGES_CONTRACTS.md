# From a checked model to a theorem about the quadratic family

For the dependency graph, public status mirrors and additional written arguments, see the [route register](PHYSICAL_BRIDGES.md). Both indexes are maintained together.

Here **physical** means an object specified independently in the mathematics, such as the orbit of $f_c(z)=z^2+c$, a based covering of particular domains, or a family of proper curves on a marked Riemann surface. A claim about that object needs a way to identify it in the model. For example, `exact_real_quadratic_period27` already mentions the actual iterate of $f_c$. A table of labels with the same period needs a further argument to identify external rays landing in its plane. [Real-center theorem](weighted/Period27RealExactPeriod.lean) · [ray and orbit identifications](PHYSICAL_BRIDGES_DYNAMICS.md#ray-portraits)

| What the claim uses | Where to check its realization |
|---|---|
| Real centers, complex restrictions, phases, external rays, based sheets, parabolic tips | [Dynamical objects and their markings](PHYSICAL_BRIDGES_DYNAMICS.md) |
| Covering fibers, rooted ends, protected planar carriers, Waves, WAD weights, calibration and satellites | [Geometric and analytic comparisons](PHYSICAL_BRIDGES_WIDTH.md) |
| The bounded complementary components of a planar compactum | [Planar fill and a complete specialization](#planar-fill) |
| A clone adjacency operator or an exterior-map coefficient | [Clone spectrum](#clone-spectrum) · [boundary spectrum](#boundary-spectrum) |
| A statement imported from a proof ledger or the final reduction | [Evidence and dependencies](#ledger) · [same-carrier gates](#gate-h1) · [terminal implication](#gate-terminal) |

To read a transition, fix the parameter, stage, domains, marks, and observable in the **target** first. Identify the theorem actually verified on the **model**. Then prove the map between these objects, its domain of definition, and exactly the naturality or comparison the conclusion consumes. For example, if a model map $F$ describes a return $g$ through $qg=Fq$, induction gives $qg^k=F^kq$ wherever all $k$ returns exist. This only identifies projected iterates. To infer $g^k x=x$ from $F^k qx=qx$, prove $q$ separates $x$ and $g^kx$ in that fiber. A two-point involution projected onto one point satisfies the commuting identity and defeats the stronger inference at $k=1$.

The earlier `PlanarFullification` and `Period27RealKneading` realization modules build with the repository’s pinned Lean 4.32.0 and Mathlib. The printed dependencies of their principal theorems are `propext`, `Classical.choice`, and `Quot.sound`. This linked run concerns those earlier modules; it does not validate subsequent additions. [Earlier weighted proof build](https://github.com/dovvnloading/loops-research-archive/actions/runs/45268559641)

The added `Period27RealMarkov`, `FullCloneRenewal`, `FiniteMarkovFibers`, `Period27FiniteFibers`, `FiniteMarkovCorrelation`, and `FullCloneCorrelation` modules are explicit Lake default targets. Reproduce them with `lake build` in `formalization/weighted`, using the pinned toolchain. Their own principal-theorem dependency reports and current build result are in the [PR 115 checks](https://github.com/dovvnloading/loops-research-archive/pull/115/checks).

A **kernel proof** can already be about the physical target. A **written proof** can use a source theorem with its hypotheses verified here. A **conditional deduction** displays its unproved inputs, and an **open obligation** names a statement still requiring proof. A verifier can establish exact arithmetic or identify a counterexample within its declared model. Check the proof that makes that computation decisive for the target. [Declaration and evidence index](physical_bridge_index.json) · [source risk register](LEAN_RISK_REGISTER_20261123.md)

<a id="planar-fill"></a>
## A complete example — filling a compact set in the plane

Paper 3 defines the filled hull of compact $K\subset\mathbb C$ as $K$ together with every bounded component of its complement. Its packet theorem uses an operator on *all* sets. Both domains can be handled by the following explicit extension. [Paper 3, equation A-fill](../papers/paper3_protected_carriers/extracted/A_intro/preliminaries.tex) · [Paper 3, Lemma fill-absorption](../papers/paper3_protected_carriers/extracted/E_packets/audit.tex) · [Lean realization](weighted/PlanarFullification.lean)

1. For any $S\subset\mathbb C$, take $C_S(z)$ to be the connected component of $z$ in $\mathbb C\setminus S$, with $C_S(z)=\varnothing$ on $S$. Set $F(S)=\{z:C_S(z)\text{ is bounded}\}$. This gives the source membership formula point by point for compact $S$. In particular $S\subseteq F(S)$. If $S\subseteq T$, maximality of connected components gives $C_T(z)\subseteq C_S(z)$ for $z\notin T$, so $F(S)\subseteq F(T)$.
2. If $z\notin F(S)$, its component $C=C_S(z)$ is unbounded. Every point of $C$ has that same component, hence $C\subseteq\mathbb C\setminus F(S)$. The new component of $z$ contains $C$ and stays unbounded. This and extensivity prove $F(F(S))=F(S)$. Thus the computed `planarFullifier` meets all three fields of the existing `Fullifier` on its declared domain.
3. For bounded $S$, enclose it in a closed disk of positive radius $r$ about zero. The exterior $E=\{|z|>r\}$ is connected, since it is the exponential image of $\{\Re w>\log r\}$, and unbounded. Every unbounded complementary component meets $E$, so maximality puts every such component in the *same* component as $E$. This component is $F(S)^c$. For compact $S$, its complement is open and locally connected, so that component is open. Consequently $F(S)$ is a closed subset of the enclosing disk, hence compact. The argument includes $S=\varnothing$, for which $F(S)=\varnothing$.
4. For $K,L\subseteq\mathbb C$, monotonicity puts $F(K)\cup L\subseteq F(K\cup L)$. Fill both sides and use idempotence. The reverse inclusion follows from $K\subseteq F(K)$. This gives $F(F(K)\cup L)=F(K\cup L)$. Finite induction gives the one-shot fill of the union under every ordering of a fixed packet, including repeated pieces. On compact inputs each intermediate union and hull is compact. [Formal packet theorem](weighted/ProtectedCarrierLogic.lean)

The generalization has a testable boundary. For $S=\mathbb R\subset\mathbb C$, both complementary half-planes are unbounded. The definition still gives $F(S)=S$, while uniqueness of the exterior would be false. At a finite compact packet, access survival and disjointness of distinct completed packets require their own witnesses. [Packet and limit tests](PHYSICAL_BRIDGES_WIDTH.md#w3)

<a id="clone-spectrum"></a>
## From a clone matrix to an edge operator

For every delay $n$, the row-source adjacency matrix $A_n$ constructed from the archive's edge relation has a positive simple *eigenline* at $t_n\in(1,2)$, $t_n^{2n+5}=t_n+1$, and every other eigenvalue has modulus strictly below $t_n$. Existence and strictness are quantified over all delays. The bound $(2n+4)(t_n-1)\le1$ rules out a uniform $t_n\ge 1+\epsilon$ for $\epsilon>0$. [Matrix construction](weighted/FullCloneMatrix.lean) · [strict gap](weighted/FullCloneStrictGap.lean) · [eigenline](weighted/FullCloneEigenline.lean) · [rate](weighted/CloneRootRate.lean)

For a proposed physical edge operator $B$, first construct the marked physical edge set $E$. Produce a bijection $b:V_n\to E$ and a bijection, preserving orientation, multiplicity and stopping time, from **every** graph transition $u\to v$ to the proof-used physical occurrences from $b(u)$ to $b(v)$. Construct the stopping sections and certify exhaustion, including edges skipped or collapsed by an immersion. Compare the normalization of the weights if the operator is weighted. These are geometric obligations at the proposed stage. [Physical incidence contract](PHYSICAL_BRIDGES_WIDTH.md#w4) · [KKL Appendix C convention audit](../research/independent_audits/clone_spectral_referee_note.md)

**Conditional deduction.** For row-source counting operators put $Px(b(u))=x(u)$. Reindex the finite sum over $v$ using the proved occurrence bijections. This gives $(BPx)(b(u))=(A_nx)(u)$, hence $B=PA_nP^{-1}$. The spectral assertions transfer in both directions by applying $P$ and $P^{-1}$ to eigenvectors. If a separate comparison identifies a block or quotient only, the conclusion is limited to that block or quotient. Even an exact spectral identification gives a claim about edge counts. A width estimate additionally needs a lower bound comparing the physical widths on those very edges with the action of $B$, including loss, uniformly for the asserted range of stages. [Width and loss](PHYSICAL_BRIDGES_WIDTH.md#w5) · [depth and normalization](PHYSICAL_BRIDGES_WIDTH.md#w7)

<a id="clone-renewal"></a>
## From graph eigenvalues to a probability law and an actual correlation

These are separate transitions, with different evidence. Fix the **same** delay $n$, actual row-source adjacency $A$, positive root $t$, and positive vector $h$ throughout.

1. **Polynomial → actual matrix mode.** For any complex root $z^{2n+5}=z+1$, construct $v_i=z^i$ before and including the shortcut and $v_i=z^i/(z+1)$ afterwards. Check ordinary, shortcut and wrap rows. The hub coordinate is one. `complexCloneVector_eigen` and `clone_polynomial_root_is_eigenvalue` prove this converse; a necessary polynomial equation alone would not suffice.
2. **Actual matrix → stochastic kernel.** Set $P_{ij}=A_{ij}h_j/(t h_i)$. Positivity and $Ah=th$ give nonnegative entries and row sums one. The long and short probabilities are $1/(1+t)$ and $t/(1+t)$. `clone_stochastic_root_mode` proves stochasticity and a nonzero mode at $z/t$ together, consuming the real root equation and complex root equation explicitly. An arbitrary $t>1$ only gives an algebraic normalization, not probability rows. [Lean proofs](weighted/FullCloneRenewal.lean)
3. **Complex root selection → asymptotic.** The polar modulus equation has a strictly decreasing radius; the phase equation is strictly increasing. These identify the first conjugate pair as the actual subleading pair for every delay. The analytic implicit-function expansion then proves $(2n+9/2)^3(1-r/t)\to\pi^2/2$. Root selection and the infinite Taylor limit are **written**, with the analytic branch and remainder stated; the finite Python checks are regressions. [Full proof, §§3–4](../research/independent_audits/clone_renewal_clock_20261123.md)
4. **Stochastic model → constructed real dynamics.** Concatenate half-open intervals of lengths $h_i$, and give each the affine map of slope $t$ onto its declared successor interval(s). On interval $i$ put the explicitly computed density $\pi_i/h_i$. Prove invariance, then prove the formula for **every** finite itinerary cylinder by affine inverse branches. This identifies the stationary process of this constructed map with $P$. Pulling back a nonzero eigenvector gives the exact complex correlation $\int\overline{G}\,G\circ T^q\,d\mu=(z/t)^q\|G\|_2^2$. The interval, invariant measure and correlation deductions are **written**; the map is generally discontinuous. [Construction and independent checks](../research/independent_audits/clone_renewal_clock_20261123.md)

**Application to a different physical system remains conditional.** For a quadratic iterate or native KL return, construct its measurable coding and invariant measure, prove the entire finite-cylinder law, match the physical time unit, and prove the transported observable has positive squared norm. A finite edge bijection supplies no probability law by itself. A width or coercivity conclusion additionally requires its own analytic comparison. The new result proves that $t_n^n\to\sqrt2$ while $(r_n/t_n)^n\to1$, so expansion on a delay block cannot alone imply a uniform decay of correlations on that block. It supplies no closure of the global H1–H4 gates. Parry normalization and renewal diffusion have established predecessors, identified in the note; no worldwide priority claim is made.

<a id="finite-correlation"></a>
## Finite probability laws and their observable

[FiniteMarkovCorrelation](weighted/FiniteMarkovCorrelation.lean) makes the
probability and observation premises explicit. A row-stochastic real matrix
$P$ and a stationary probability vector $\pi$ determine, for every $q\ge0$,

$$
J_q(i,j)=\pi_i(P^q)_{ij}.
$$

`joint_probability` proves nonnegativity, total mass one, and both marginals
$\pi$. For the **same** matrix, a complex right mode $Pg=\lambda g$ with
$\lambda\ne1$ has stationary mean zero. Strictly positive $\pi_i$ and a
nonzero coordinate of $g$ give $M=\sum_i\pi_i|g_i|^2>0$. The separately
proved matrix-power action yields

$$
\sum_{i,j}J_q(i,j)\overline{g_i}g_j=\lambda^q M,
\qquad \frac{\sum_{i,j}J_q(i,j)\overline{g_i}g_j}{M}=\lambda^q.
$$

The orientation, conjugation, nonzero denominator, and every finite horizon
are part of the formal statements. The fair holding matrix $Q=(I+P)/2$
has the same stationary law and mode $(1+\lambda)/2$; its two-time laws and
correlations obey the corresponding identities. Lean proves this finite
matrix transformation. Independence of clock increments and realization as
a probability process are additional written steps below.

[FullCloneCorrelation](weighted/FullCloneCorrelation.lean) applies these
results to `cloneTransition n t` and the previously constructed nonzero
root eigenvector. Its stationary-vector and strict positivity premises
explicitly refer to that matrix. The formula $\pi_{n+1}=a/m$ and
$\pi_i=1/m$ otherwise, with $a=1/(1+t)$ and $m=2n+5-t/(1+t)$, is checked
by the written incoming-flow proof in the [renewal note](../research/independent_audits/clone_renewal_clock_20261123.md).
That explicit stationary formula and its physical invariant-density
realization are not labeled as Lean measure-theory proofs. The all-cylinder
proof is what turns the finite endpoint calculation into the correlation
of the actual constructed interval map.

<a id="clone-readout"></a>
## The measured statistic and the full clock law

The [readout note](../research/independent_audits/clone_resonant_readout_20261123.md)
continues from the explicitly realized affine map and its normalized complex
mode $\lambda=\rho e^{i\theta}$. It proves the following distinct transitions.

1. Choose a phase using $\int G^2\,d\mu$, then normalize the real part to
   obtain the actual real observable $F$ with covariance
   $\rho^q\cos(q\theta)$. An arbitrary real part need not have this covariance.
2. Sum the absolutely convergent covariance Fourier series to obtain the
   Poisson kernel $S(\omega)=(1-\rho^2)/|1-\lambda e^{-i\omega}|^2$.
   The real observable has the average of the positive- and negative-frequency
   kernels. Fourier evaluation is not a theorem identifying a causal response
   or an extremal width.
3. Derive the finite variance from its double covariance sum, retaining the
   endpoint remainder. With $D=2n+9/2$, the long-run coefficient is
   $S(0)\sim1/(4D)$, while the resonance height is
   $S(\theta)\sim4D^3/\pi^2$. At the integer window $N=2D$, the original real
   average has variance asymptotic to $1/(4D^2)$ even though $\rho^N\to1$.
4. Construct an actual product with a measure-preserving circle rotation to
   realize a phase-tracking readout. Its real normalized covariance is
   $\rho^q$ and its long-run variance coefficient is $S(\theta)$. Thus the
   coefficient ratio is asymptotic to $16D^4/\pi^2$. The product has a
   nonmixing circle factor; only the specified observable is being compared.
5. Construct the Bernoulli skew product or an independent Poisson observation
   clock. Compute the full transform $\mathbb E[\lambda^{N_t}]$, not just
   $\mathbb E N_t$. Equal expected iteration counts can give quadratic rather
   than cubic envelope decay. Even holding probability $c/D\to0$ changes
   the cubic leading constant from $\pi^2/2$ to $\pi^2/2+2\pi^2c$.

These analytic, real-phase, and measure-theoretic steps have complete written
proofs and [exact finite regressions](../research/independent_audits/verify_clone_resonant_readout.py).
The regressions are not universal proofs or certified root enclosures.
Transferring any conclusion to native quadratic/KL dynamics still requires
the actual probability law, observable, and full clock identification;
transferring it to a width additionally requires an independently proved
comparison to that defined width.

<a id="boundary-spectrum"></a>
## From finite coefficients to the exterior map

Use the normalized inverse exterior uniformization $\Psi(w)=w-1/2+\sum_{n\ge1}b_n w^{-n}$. The coefficient calculation must agree with its Laurent recurrence at each claimed index. The five-entry rational energy and Abel summation in Lean concern the displayed coefficients and finite intervals. For the physical exterior at $R=|w|>1$, the area theorem and the inner parameter disk of radius $1/4$ give $\sum n|b_n|^2\le15/16$. Subtract the verified partial energy, leaving an upper bound $E_N$ on the actual residual energy. Cauchy–Schwarz then gives
$$
 \left|\sum_{n>N}b_n w^{-n}\right|^2
 \le E_N\sum_{n>N}\frac{R^{-2n}}{n}
 \le\frac{E_N R^{-2(N+1)}}{(N+1)(1-R^{-2})}.
$$
At $N=5, R=2$ this equals the archive's squared-error bound $781339/19327352832$ on the right. The factor $1-R^{-2}$ explains the restriction on $R$. [Finite Lean identities](../MandelbrotSpectrum.lean) · [coefficient, area and landing sources, §§1, 4–5](../research/independent_audits/mlc_boundary_spectral_program_20261111.md)

At $R=1$, use the Fejér polynomials of these same coefficients. The written equivalence with MLC requires *uniform* Cauchy convergence on the entire circle. In the forward direction apply Carathéodory and Fejér to the continuous boundary trace. Conversely uniform convergence produces a continuous trace whose Poisson extension agrees with the analytic series in the open disk, so Carathéodory applies. For actual MLC this leaves $\forall k\ \exists N\ \forall m,n\ge N:\|\sigma_m-\sigma_n\|_\infty<2^{-k}$ open. Any finite coefficient prefix is compatible with tails of very different regularity among general analytic functions. For instance the tail $1/(n\log n)$ has finite area-type square energy and diverges radially at angle zero. This tests the inference from an energy bound alone. [Theorems 2.1 and 3.1](../research/independent_audits/mlc_boundary_spectral_program_20261111.md)

<a id="numerical-observations"></a>
## From sampled points to a statement about a continuum

| Experiment | Quantity observed | Independent step the physical conclusion requires |
|---|---|---|
| Limb diameters | Diameter of a finite pixel cloud clipped by a computed wake polygon | Prove membership of any two physical witness points for a lower bound. For an upper bound, enclose the entire limb in a certified cover and bound its diameter, including discarded pixels and ray-tracing error. A bound for all denominators additionally requires a uniform theorem. [Wake estimator](../code/exp1b_limbs_wake.py) |
| External rays | Continuation at finitely many positive potentials | Identify the chosen inverse branch throughout the continuation, bound its approximation error, and prove the diameter of the remaining ray tail tends to zero at the claimed endpoint. A certified point at positive potential still leaves this last limit. [Ray tracer](../code/exp2_rays.py) |
| Period doubling | Superstable roots, finite ratios and a collocation Jacobian | Isolate each root and prove its period to certify a finite ratio. An asymptotic scaling or unstable eigenvalue requires estimates on the full renormalization operator in a specified function space, including the truncation error and the removed coordinate mode. [Period-doubling computation](../code/exp3_feigenbaum.py) |
| Escape-time images | Samples on a finite window, mesh and iteration budget | A point escaping the certified escape radius gives an exterior witness. A finite nonescape record leaves eventual escape undecided. To claim a connected neighborhood basis, supply connected relative neighborhoods at every required scale and prove that they shrink. [Image generator](../code/exp4_images.py) · [relative-neighborhood argument](#gate-terminal) |

<a id="ledger"></a>
## What a ledger entry lets a reader verify

`ResearchLedger.lean` checks discrete metadata. To use an entry as mathematics, retrieve its exact statement, ordinary dependencies, **and** separately recorded hypotheses, then follow the cited theorem with its parameters, maps and assumptions in scope. The original `proved` label is documentary. For example, the source status of `UPTCR_IMPLIES_MLC` is proved and the hypothesis `UNIVERSAL_PROTECTED_TOWER_CLOSURE` is open. Treat both facts as part of the claim. The index links each registered model to a proof discussion, and the check reports coverage and references. A theorem lookup also prints the command to check its source with the pinned Lean toolchain, including for the five standalone audit modules. Reviewing the model’s application to the physical target requires the argument at the linked references. [Canonical ledger](../ledger.json) · [Lean mirror](../ResearchLedger.lean) · [source audit script](../research/independent_audits/audit_ledger_evidence.py)

Run these commands from the repository root.

```sh
python3 -B code/verify_physical_bridges.py
python3 -B code/verify_physical_bridges.py --theorem physical_kneading_numerator
python3 -B code/verify_physical_bridges.py --claim UPTCR_IMPLIES_MLC
python3 -B code/verify_lean_frontier_sync.py
(cd formalization/weighted && lake build PlanarFullification Period27RealKneading)
```

The evidence-file audit on base `365f49d` found 26 ledger pointers to seven absent Markdown files. The [evidence crosswalk](LEDGER_EVIDENCE_CROSSWALK.md#ledger-evidence) identifies the available replacement arguments, two corrections to their wording, two grid results with partial support, and the eight open obligations affected. The lookup prints the alternative evidence for each missing citation. The canonical ledger records 465 obligations. The index follows all 115 open entries, all 14 directly conditional canonical entries and all 46 records in the separate November register. For example, query `--claim NOV26_OPEN_QGAMMA` for the status of the individual canonical quadrilateral moduli. [Run the evidence-file audit](../research/independent_audits/audit_ledger_evidence.py)

## The same parameter and carrier through the reduction

Write $c\in\mathcal M$, and let $T_c$ contain the entire indexed tower, its selected predecessors, stages, branch maps, and proof-used marks. Instantiate `ResearchGates.Program` with these objects and the source definitions below. Its fields have arbitrary predicate types. Establish each realization from independent data. In particular, universal constants are chosen **before** $c$, its combinatorics and its unbounded depths. The permitted finite prefix can depend on $c$. [Six-clause source, §§3–5](../research/mlc_unified/mlc_closure_proposition.md) · [Lean gate composition and countermodels](../ResearchGates.lean)

<a id="gate-h1"></a>
### H1 — construct the protected object

For each infinitely quadratic-like renormalizable $f_c$, construct the rooted predecessor closure and realize it as a marked planar carrier at every checkpoint. Exhibit the protected paths, cyclic order, relative-cover sheet labels and all horizon branches. At each stage prove $g_j^{-1}(H_{j+1})=H'_j=\iota_j^{-1}(H_j)$, component exhaustion and properness for the two distinct maps. The one degree-two stage belongs to the selected spine. Count the critical encounters of each auxiliary branch separately. These obligations give the first two clauses on the *same* $T_c$. The finite routing criterion applies only after checking its obstacles and port hypotheses on that carrier. `separate_exists_does_not_supply_a_joint_tower` gives an explicit failure with two different witnesses. **Universal construction open.** [Source, UPTCR-1 and 2](../research/mlc_unified/mlc_closure_proposition.md) · [local realization checks](PHYSICAL_BRIDGES_WIDTH.md#w4)

<a id="gate-h2"></a>
### H2 — calibrate the measured quantities and derive transport

On that $T_c$, exhibit the map from each response coordinate to its specified physical curve family, conductor, or Value feature. Give both comparison inequalities where equivalence is claimed. Name the scale, electrodes, normalizing $r_{B,n}>0$, multiplicities, additive and relative errors, and how those errors accumulate along the selected backward path. For the **backward-transition** clause the source also requires MBTT, including chart compatibility, error charging and the choice of an earlier checkpoint. The abstract Lean slot `H2 M` already asks for both finite response and backward transition. Supplying just ledger `H2_CALIBRATION` does not establish that conjunction. The required estimate, above the declared threshold, is $L_{p(n)}\ge(\lambda_{\rm raw}-\delta)L_n-E_0$ with $p(n)<n$ and $\lambda_{\rm raw}-\delta>1$. Prove these for the actual proof-used observables with tower-independent constants. **General calibration and transport open.** [Master Transition, §§5–8](../research/mlc_unified/master_transition.md) · [same-surface comparison and buffered widths](PHYSICAL_BRIDGES_WIDTH.md#w6)

<a id="gate-h3"></a>
### H3 — obtain an admissible analytic limit

For each sequence of realized checkpoints satisfying the calibrated bounds and normalized incidence/congestion assumptions, extract a common subsequence in the specified marked topology. Prove nondegeneracy of the domains and maps, end-properness, survival of distinguished accesses and compatibility of cover subgroups, response forms and limiting observables. This is the use of compactness in the reduction. Compactness of a symbolic address space alone allows domains shrinking to a point while all labels stay fixed. The decreasing-envelope theorem needs its connected limiting traces checked on the physical carriers. **Universal analytic compactness open.** [Master Transition M6](../research/mlc_unified/master_transition.md#m6-coercivity) · [limit tests](PHYSICAL_BRIDGES_WIDTH.md#w3)

<a id="gate-h4"></a>
### H4 — get rigidity in parameter space

**Parameter equality by hybrid uniqueness.** For towers with equal full marked combinatorics, construct an orientation-preserving global quasiconformal conjugacy fixing infinity and justify the no-invariant-line-field input on the actual Julia set. For an infinitely renormalizable quadratic, McMullen's Theorem 8.1(2) gives $K=J$. Pullback invariance then makes the conjugacy's Beltrami coefficient vanish almost everywhere on $K$, so it is a hybrid equivalence. The connected-case uniqueness clause of Douady–Hubbard Theorem 1(b) supplies an affine conjugacy $A(z)=az+b$ between the polynomials. Comparing $A\circ f_c=f_{c'}\circ A$ gives $a=a^2$, $2ab=0$, and hence $a=1,b=0,c=c'$. This does not assert that the originally constructed quasiconformal map is conformal in the basin of infinity. Also construct the nested compact connected **relative neighborhoods** of $c$ in $\mathcal M$ with intersection this marked parameter fiber. Equality of parameters by itself does not construct those neighborhoods. **General rigidity and parameter-neighborhood realization open.** [Corrected endgame, primary theorem locators and current area results](../research/independent_audits/marked_slit_path_bridge_20261123/RIGIDITY_AND_REMAINING_GAP.md) · [Relative-neighborhood argument, §§3–4](../research/mlc_unified/uptcr_cross_validation.md)

**Conformality of the chosen conjugacy under stronger support hypotheses.** For towers with equal full marked combinatorics, construct a global quasiconformal conjugacy conformal on the Fatou set and justify the absence of invariant line fields on the Julia set in that regime. Agreement with the normalized Böttcher conjugacy supplies the exterior condition; any bounded Fatou components require their own conformal condition. The invariant Beltrami coefficient is then supported on the Julia set and vanishes almost everywhere, giving a conformal conjugacy. A conformal map fixing infinity has the form $az+b$. Comparing the quadratic and linear coefficients forces $a=1,b=0$, and comparing constants yields $c=c'$. Also construct the nested compact connected **relative neighborhoods** of $c$ in $\mathcal M$ with intersection this marked parameter fiber. Equality of parameters by itself does not construct those neighborhoods. **General rigidity and parameter-neighborhood realization open.** [Normalization and relative-neighborhood argument, §§3–4](../research/mlc_unified/uptcr_cross_validation.md) · [Explicit exterior-gauge counterexample and corrected theorem](../research/independent_audits/maximal_global_closure_20261123/EXTERIOR_GAUGE_REPAIR.md)

<a id="gate-universal"></a>
### What composes under the universal hypotheses

Fix $c$ after choosing universal constants. Select the joint carrier from H1. Apply response and backward transport, compactness, and rigidity successively to that very witness. This is the proof of `package_of_same_carrier_gates`. For the numerical bound used in the source, let $K=\max\{L_{\rm prefix}(c),D_*,E_0/(\lambda-1)\}$. At the first $n$ with $L_n>K$, the preceding values are at most $K$ while $L_{p(n)}\ge\lambda L_n-E_0>L_n$, a contradiction. This deduction uses a genuinely earlier $p(n)$ and a strictly positive $\lambda-1$. A selected tip, or a separate bound for each tower with uncontrolled constants, cannot instantiate the universal quantifier. **Composition proved under its inputs. The universal package is open.** [Source proof, Theorem 4.1](../research/mlc_unified/uptcr_cross_validation.md) · [typed implication](../ResearchGates.lean)

<a id="gate-terminal"></a>
### Why the last step gives local connectivity

For an infinitely renormalizable $c$, assume the source H4 has supplied nested compact connected relative neighborhoods $N_j\ni c$ with $\bigcap_j N_j=\{c\}$. For every relatively open $U\ni c$, failure of $N_j\subseteq U$ for all $j$ would give a nested sequence of nonempty compact subsets $N_j\setminus U\subseteq N_0$. Its intersection would contain a point of $\{c\}\setminus U$, impossible. Thus the connected neighborhoods refine every $U$. On the complement of infinite renormalizability use Hubbard's account of Yoccoz, Theorem III, with $c\in\mathcal M$. With connected neighborhoods at **each** point, each component of a relatively open set is relatively open (around each of its points take a connected neighborhood inside that open set). These components form the required connected open basis. The Lean implication takes both this terminal interpretation and the complement theorem as arguments. Its one-point countermodel satisfies every abstract carrier clause and falsifies local connectivity when the terminal interpretation is removed. **The implication is conditional and MLC is open.** [Theorem 4.1 and primary-source locator](../research/mlc_unified/uptcr_cross_validation.md) · [kernel countermodel](../ResearchGates.lean)

<a id="parameter-capacity"></a>
### An alternative parameter-capacity criterion

For nested nonpolar parameter compacta Fₙ in the same bounded Green domain D, let μₙ be their probability equilibrium measures and Vₙ their Robin energies. The equilibrium potential is Vₙ quasi-everywhere on Fₙ, so integrating against μₘ for m≥n gives I(μₘ,μₙ)=Vₙ. Consequently the charge increments Δₙ=μₙ₊₁−μₙ are mutually orthogonal and $V_N=V_0+\sum_{n<N}I(\Delta_n)$. A physical H₀¹ test with a certified charge difference and Dirichlet energy gives a lower bound for each increment by Cauchy–Schwarz. For connected subsets of M in D₁={G_M<1}, the continuum capacity estimate gives diameter(Fₙ)≤20 exp(−Vₙ). Thus an infinite divergent certificate on connected relative neighborhoods would give local connectivity directly, without the marked-tower or QC-rigidity route. [Equilibrium identities and diameter proof, §§1–3](../research/independent_audits/parameter_capacity_increment_20261123/NOTE.md)

The [same note, §§4–5](../research/independent_audits/parameter_capacity_increment_20261123/NOTE.md) constructs global logarithmic bumps and converts actual parameter-disk inclusions, child exclusions and escaping circular arcs into a nonlinear lower recursion. Its exact finite example uses F₀=M and F₁=closed B(−1,3/32), and proves V₁−V₀>1/3686400. It is a calibration at a hyperbolic parameter. The infinite schedule at unresolved parameters remains open. Pure functions of G_M have zero charge difference on M; rescaling G_M with the ground fixed leaves the useful ratio unchanged. The actual satellite-core theorem of Levin–Przytycki also excludes positive average logarithmic derivative for an induced system with an integrable return time. None of the angular measures in ROOT-MEASURE or ROOT-TRACE is substituted for the physical parameter equilibrium measures here. [Normalization loss and precise remaining application, §§6–8](../research/independent_audits/parameter_capacity_increment_20261123/NOTE.md)

<a id="native-frontier"></a>
## November 23 native-interface repairs

These are written proofs and source corrections on the indicated objects.
The executable checks cover finite or algebraic consequences. None of the
new continuum or complex-analytic arguments is a new Lean theorem, and
none changes the 465 source-locked obligations or their statuses.

| Exact object and quantifier | Identification and proof | Remaining boundary |
|---|---|---|
| The four native 3/9 tile images and all 88 prescribed finite-side records | The earlier C4 winding obstruction, same-parent naturality, and covering-component connectivity give exactly two coarse inverse-image components. [Connector theorem](../research/independent_audits/maximal_root_landing_20261123/NOTE.md) | A single root-normalized coarse starting sheet misses 44 specified lifts. A W prefix or two starting sheets repairs existence. This coarse obstruction is compatible with the 88 computed F9 words in CONNECTOR-WORDS; transport to an independently prescribed historical gauge remains separate. |
| Every component beyond a singleton cut fiber of a monotone dendrite quotient, using the actual marked physical continua | Compact-arc inverse images prove component correspondence and full-hull incidence. The Kiwi plane quotient constructs a physical carrier in the periodically repelling case. [One-cut theorem and critical-fiber lemma](../research/independent_audits/maximal_global_closure_20261123/CUTPOINT_PRUNING.md) | The named native carrier must satisfy the three stated monotone, singleton-fiber, and full-hull conditions. No Wave occurrence or two-path break is inferred from hull incidence alone. |
| Every properly presented lamination joining one whole ideal circle to other components, and every finite covering of that whole end | A countable restriction atlas extends the existing BOWR construction; injective support transport and the peripheral cyclic cover give exact width domination and degree scaling. [Theorems 2.1, 3.1, 4.1](../research/independent_audits/maximal_exit_transfer_20261123/NOTE.md) | Proper endpoints are tested on the final surface. Returning arcs on the same ideal circle are excluded. |
| Every final stationary parent leaf with the two specified actual filled-set hits | Koebe handles inner end-cuts. Fatou and boundary uniqueness make a failed finite-time unpunctured lift land on the outer ideal circle. Filled-set bijectivity identifies any successful second hit. Selecting one exit per parent gives the bound 2 W(RF). [Theorem 6.4 and Corollary 6.5](../research/independent_audits/maximal_exit_transfer_20261123/NOTE.md) | The actual N2 pass-through implication at both valid indices remains open. The quantitative route no longer requires an inner-to-inner exit or native successor marking filters. |
| The selected real-slit family with its exact proper restrictions, physical little intervals, and signed orders | Joukowski collars, annulus uniformization, the strip quotient, and all deck classes identify the intrinsic ideal classes. The genuine Chebyshev return proves escape of every nondegenerate zero-edge subarc for the explicit contour-code action. [Access and subarc proof](../research/independent_audits/maximal_native_wave_20261123/NOTE.md) | The sharp five-step and size-dependent subarc conclusions concern g_*q₀⁻¹. Native interpretation requires the unresolved full geometric-trace pullback identification (MARK); temporal-component properness does not prove it. Descendant-crest inheritance is a further premise. |
| Every admissible selected-family parent or child Wave in the indicated full path classes | Exact SC normalization, minimal three-atom parent bases and closed crests, positive child foliations, and square-sum metric periodization prove the intrinsic physical width comparison without full immersion MARK. Corrected widest-box errors give independent defect greater than 40/819 for p≥13; the separate p=13/p≥14 split certificate strengthens this to 11/126. Both give greater than 1/100 for every selected p≥3. [Full-path width proof](../research/independent_audits/maximal_native_wave_20261123/H3_WIDTH.md) | The physical signed-chart package is an explicit upstream input. Independently optimized unbuffered widths do not give a single pairable optimizing parent or iterative amplification. |
| Every maximal lift of a proper path on the specified full-carrier annuli in hyperbolic disk domains | The full critical-value carrier pulls back to one full continuum; the immersion maps the entire source annulus to the target, and bounded analytic boundary uniqueness proves both source ideal endpoints. [Annular properness](../research/independent_audits/maximal_global_closure_20261123/ANNULAR_RESTRICTION_PROPERNESS.md) | The carrier must satisfy the stated connectedness, fullness, forward invariance and critical-point conditions. The theorem does not create canonical paired germs or prove their retention. |
| Actual ordered retained occurrence paths with canonical selected-limb endpoints, a simple common pushed image, and native critical-contour locality | The connected selected carrier and a physical-endpoint homotopy exclude subordination of a collision image to the critical contour. Two further sequentially retained unique outputs give the crest contradiction. [Connected-carrier proof](../research/independent_audits/maximal_global_closure_20261123/CONNECTED_CARRIER_NONCOLLISION.md) | Connectedness of the intervening parent contact is unnecessary. Canonical occurrence existence, native contours and sequential survival remain premises. The result does not close N2. |
| Every outer-incident canonical class on the actual selected four-boundary surface for p≥11 | The actual primitive collar lift, cyclic modulus, disjoint stabilizer translates, SC normalization and Landen threshold prove q less than 2, including outer self-classes, so the buffered coefficient vanishes. [Matched outer-buffer proof](../research/independent_audits/maximal_native_wave_20261123/OUTER_BUFFER_EXCLUSION.md) | This supplies the selected outer application of local H4. It does not determine inner coefficients or a global H4 gate. |
| A global quadratic quasiconformal conjugacy and the exact support of its invariant Beltrami coefficient | An explicit Chebyshev self-conjugacy disproves the weak normalization inference. Exterior Böttcher agreement, and conformality on bounded Fatou components when applicable, make Julia no-line-field rigidity sufficient. [Corrected terminal theorem](../research/independent_audits/maximal_global_closure_20261123/EXTERIOR_GAUGE_REPAIR.md) | The hybrid-uniqueness route above can give parameter equality without conformality of the original map outside K. Neither route supplies the missing no-line-field input or uniformly quasiconformal pullback construction for arbitrary mixed towers. |

The new finite checks are linked by the `native-frontier` entry in the
theorem-level source index. The mathematical statements are the named
written theorems above; passing the source-index check does not certify
their proofs.

This audit and its new formalizations were prepared with OpenAI GPT-6 Astra Pro. Human mathematical review is pending.
