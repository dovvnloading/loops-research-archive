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
| The selected real-slit family with its exact proper restrictions, physical little intervals, and signed orders | Joukowski collars, annulus uniformization, the strip quotient, and all deck classes identify the intrinsic ideal classes. The genuine Chebyshev return proves escape of every nondegenerate zero-edge subarc for the explicit contour-code action. [Access and subarc proof](../research/independent_audits/maximal_native_wave_20261123/NOTE.md) | The sharp five-step and size-dependent subarc conclusions concern g_*q₀⁻¹. Native interpretation requires the unresolved KKL ideal-set pullback identification (MARK). Descendant-crest inheritance is a further premise. |
| The selected embedded slit pair with an explicitly occurrence-indexed maximal-component restriction | The component ideal-set pullback equals q₀⁻¹ on every nonempty connected inner subset and sends the outer circle to the source outer circle. From ordered cut ranks and the separately established covering alignment, Lean checks the blocks, partition, finite end-properness predicates, image table, all 90 open-run saturation cases, sharpness, and punctured-circle regressions. [Written component theorem](../research/independent_audits/immersion_mark_resolution_20261124/NOTE.md) · [Finite kernel certificate](../ImmersionMarkFinite.lean) | The source-identification premise (MC), including occurrence multiplicity and singleton semantics, is not proved. MARK remains open and SELECTED-ESCAPE conditional. Lean checks finite contour bookkeeping; prime ends, homotopies, and positive-subarc escape remain outside this new formalization. |
| Every admissible selected-family parent or child Wave in the indicated full path classes | Exact SC normalization, minimal three-atom parent bases and closed crests, positive child foliations, and square-sum metric periodization prove the intrinsic physical width comparison without full immersion MARK. Corrected widest-box errors give independent defect greater than 40/819 for p≥13; the separate p=13/p≥14 split certificate strengthens this to 11/126. Both give greater than 1/100 for every selected p≥3. [Full-path width proof](../research/independent_audits/maximal_native_wave_20261123/H3_WIDTH.md) | The physical signed-chart package is an explicit upstream input. Independently optimized unbuffered widths do not give a single pairable optimizing parent or iterative amplification. |
| Every maximal lift of a proper path on the specified full-carrier annuli in hyperbolic disk domains | The full critical-value carrier pulls back to one full continuum; the immersion maps the entire source annulus to the target, and bounded analytic boundary uniqueness proves both source ideal endpoints. [Annular properness](../research/independent_audits/maximal_global_closure_20261123/ANNULAR_RESTRICTION_PROPERNESS.md) | The carrier must satisfy the stated connectedness, fullness, forward invariance and critical-point conditions. The theorem does not create canonical paired germs or prove their retention. |
| Actual ordered retained occurrence paths with canonical selected-limb endpoints, a simple common pushed image, and native critical-contour locality | The connected selected carrier and a physical-endpoint homotopy exclude subordination of a collision image to the critical contour. Two further sequentially retained unique outputs give the crest contradiction. [Connected-carrier proof](../research/independent_audits/maximal_global_closure_20261123/CONNECTED_CARRIER_NONCOLLISION.md) | Connectedness of the intervening parent contact is unnecessary. Canonical occurrence existence, native contours and sequential survival remain premises. The result does not close N2. |
| Every outer-incident canonical class on the actual selected four-boundary surface for p≥11 | The actual primitive collar lift, cyclic modulus, disjoint stabilizer translates, SC normalization and Landen threshold prove q less than 2, including outer self-classes, so the buffered coefficient vanishes. [Matched outer-buffer proof](../research/independent_audits/maximal_native_wave_20261123/OUTER_BUFFER_EXCLUSION.md) | This supplies the selected outer application of local H4. It does not determine inner coefficients or a global H4 gate. |
| A global quadratic quasiconformal conjugacy and the exact support of its invariant Beltrami coefficient | An explicit Chebyshev self-conjugacy disproves the weak normalization inference. Exterior Böttcher agreement, and conformality on bounded Fatou components when applicable, make Julia no-line-field rigidity sufficient. [Corrected terminal theorem](../research/independent_audits/maximal_global_closure_20261123/EXTERIOR_GAUGE_REPAIR.md) | The hybrid-uniqueness route above can give parameter equality without conformality of the original map outside K. Neither route supplies the missing no-line-field input or uniformly quasiconformal pullback construction for arbitrary mixed towers. |

The new finite checks are linked by the `native-frontier` entry in the
theorem-level source index. The mathematical statements are the named
written theorems above; passing the source-index check does not certify
their proofs.

The following November 24 contracts refine the selected and stationary
interfaces. Their classifications distinguish written analytic proofs,
exact finite certificates, and explicit imports from the source. The
historical table above and the source-locked ledger are preserved.

<a id="selected-buffer-zero"></a>
## Complete buffered exclusion for the selected four-boundary surface

**Object and quantifier.** For every selected integer $p\ge10$, take the
actual surface $Y_p=U_p\setminus(K_0\cup K_1\cup K_2)$ with its minimal
marking by the four whole ideal boundary circles. Every admissible simple
ideal arc class, including every winding and essential returning class,
has full quadrilateral width $q_\alpha<1999/1000<2$. Consequently all
canonical coefficients $(q_\alpha-2)_+$ vanish and
$W_{\rm can}(Y_p)=0$. This strengthens the earlier outer-only result
BUFFER to BUFFER-ZERO on this precise marking. [Written theorem and
surface identification, §§1–5](../research/independent_audits/canonical_width_attack_20261124/NOTE.md)

**Proof and evidence.** Embedded slit-and-cut rings lift to primitive
peripheral cyclic covers. Their exact bounds give peripheral lengths
below $5.97$, $3.2$, $4.19$ and $3.75$. Disjoint hyperbolic collars handle
distinct boundary classes; the two oriented peripheral shadows of an
essential returning class give the necessary factor two. These are
written analytic arguments. The checker proves the numerical premises
with exact intervals for $p=10,\ldots,16$ and a uniform tail for $p\ge17$.
The tail uses the established derivative estimates only through the fifth
iterate and the exact reflection $X_6=-X_3$. The regression suite checks
this restriction, the width normalization and certificate replay.

```sh
python3 -B research/independent_audits/canonical_width_attack_20261124/verify.py --check-manifest
python3 -B -m unittest discover -s research/independent_audits/canonical_width_attack_20261124 -p 'test_*.py' -v
```

Uniformization, the collar lemma and the continuum proof are not newly
kernel-verified. Arbitrary marking refinements, the ten-atom tree annulus,
and $p\le9$ are outside this theorem. The independent unbuffered Wave
defect therefore cannot be identified with a positive buffered canonical
coefficient on these minimally marked surfaces. [Scope and exact
certificate](../research/independent_audits/canonical_width_attack_20261124/certificate.json)

<a id="native-component-refinements"></a>
## Component conventions and the source-imported finite native action

**Independent written results.** On the selected slit pair, deduplicating
maximal component restrictions modulo reparameterization preserves the
greatest ideal-set pullback $q^{-1}(X)$ for every nonempty connected inner
$X$, and preserves the outer-circle pullback. Uniform continuity makes
any singleton unindexed restriction set have finitely many occurrences;
their proper subordinate homotopies can be pasted. For a simple proper
parent, a trace-contained proper source path is homotopic relative to its
ideal endpoints to a full component, its reversal, or a null hairpin.
After the marking filters, the nontrivial arc support agrees with
component restriction. These are COMPONENT-SET and SIMPLE-TRACE;
multiplicity, path-as-map singleton tests, nonsimple parents and width
transport are not identified. [Theorems 3.4 and 4.1](../research/independent_audits/native_mark_attack_20261124/NOTE.md)

**Explicit source import.** The actual interval Hubbard hull, complete
pullback, prime primitive period-three little cycle, rotation denominator
$q=2$ and bound $b=2$ verify the physical hypotheses for KKL Propositions
6.5–6.6. Accepting those propositions gives the finite native action on
the original multi-intervals and their closures. With Proposition A.14,
a nonempty starting Wave whose crest contains an original marked interval
cannot have nonempty unbreakable lamination descendants through that
interval's saturation time, at most five pushes. This is NATIVE-FINITE,
an imported theorem application. It does not independently reconstruct
the source's compressed all-path argument or produce surviving descendants.
Full immersion MARK remains open. [Hypothesis audit, source-proof issue
and chain obstruction, §§5–6](../research/independent_audits/native_mark_attack_20261124/NOTE.md)

```sh
python3 -B research/independent_audits/native_mark_attack_20261124/verify.py --check-manifest
```

The checker covers 191 finite inputs: 100 proper open multi-intervals
including ten punctured circles, 90 proper closed closures, and the full
circle. It checks endpoint-aware saturation and the finite limb census.
It does not prove the homotopy theorems or the imported analytic statements.
[Exact certificate](../research/independent_audits/native_mark_attack_20261124/certificate.json)

<a id="variable-end-exits"></a>
## Terminal width from actual exits with varying endpoints

**Written modulus theorem.** Let $A$ be a Borel lamination of simple proper
parents. Suppose one maximal immersion lift per parent can be selected
measurably, proper in the actual final surface and joining two distinct
ideal boundary components. If $L_v$ denotes the local cyclic-cover width
of end $v$, then

$$
\mathcal W(A)\le\inf\left\{\sum_v a_vL_v:
a_v\ge0,\quad a_u+a_v\ge1
\text{ for every occurring endpoint pair }\{u,v\}\right\}.
$$

The sum uses only positively charged ends of finite local width. The
proof selects disjoint actual Borel lift supports, partitions them by
their endpoint pairs, proves exact parallel additivity, and applies the
whole-end cyclic width bounds. It does not use a counting-measure model
for overlapping pushed images. [VARIABLE-EXIT, Theorem 4.1](../research/independent_audits/stationary_transport_attack_20261124/VARIABLE_END_EXIT_TRANSFER.md)

For a final degree-$2^m$ native covering, all preimages of at most $b$
target little filled sets have total peripheral degree at most $b2^m$.
Thus actual exits incident to that bank imply
$\mathcal W(A)\le b2^m\mathcal W(\mathcal RF)$. For the sharper predecessor
bank at horizon $m=b+r$, with $2\le r<P$ and $P$ the native primitive cycle
period, its $r$ distinct whole ends each have degree two. Actual selected
maximal exits incident to that bank give $2r\mathcal W(\mathcal RF)$;
if both endpoints lie in the bank the bound is $r\mathcal W(\mathcal RF)$.
Different parents may use different endpoints. [Degree proof and exact
bank conditions, §5](../research/independent_audits/stationary_transport_attack_20261124/VARIABLE_END_EXIT_TRANSFER.md)

```sh
python3 -B research/independent_audits/stationary_transport_attack_20261124/verify.py
```

The kernel-checked [finite Lean accounting module](weighted/StationaryEndpointCover.lean)
isolates the real-valued double-counting identity, weak duality, one-end
and two-end bank bounds, and the conditional degree budget.
The input is the incidence-width bound at every positively charged end,
not an assumption that all ideal widths are finite. Uncharged values are
unused real placeholders; modulus and its extended-real infimum are
outside this module. The native degree census and actual exit existence
remain separate geometric inputs. See the [scope and reproduction note](../research/independent_audits/stationary_transport_attack_20261124/LEAN_ENDPOINT_ACCOUNTING.md).
The [weighted Lean workflow successfully built this module](https://github.com/dovvnloading/loops-research-archive/actions/runs/45655448328/job/139352354071) at revision `100575d96dd12acce42db2e085aa56e4f69c5ca7`; subsequent documentation-only commits preserve the Lean source, Lake configuration and toolchain. This verifies the finite algebra only.

A [one-hit landing reduction](../research/independent_audits/stationary_transport_attack_20261124/ONE_HIT_LANDING_REDUCTION.md)
shows that a single actual bank hit together with a genuine physical
landing on a different deleted continuum (or an ambient outer ideal
limit) supplies an eligible exit. At the high-type horizon m<P the
selected bank is disjoint from the original cycle, so a physical
landing on an original small Julia set is sufficient. A mere
carrier-edge endpoint or non-singleton impression is not sufficient;
the note contains an explicit planar counterexample to one-hit
properness in the carrier complement alone. This is a written
conditional reduction, not proof of the actual stationary premise.

The [simultaneous finite-length core](../research/independent_audits/stationary_transport_attack_20261124/EXCEPTIONAL_WIDTH_REDUCTION.md)
constructs one finite-energy all-sheet density on the ambient target
that removes nonlanding parents and controls every raw lift and all
its final collar coordinates modulo a width-zero family. After a bank
hit, failure of all eligible exits forces full unpunctured continuation,
no different-component hit, and two physical carrier-only endpoints
in the high-type application. Countable endpoint gates contribute
zero width; a planar rectangular example with width exactly 1/4
shows that unrestricted carrier-edge failures can have positive
width. Native dynamics or a separate quantitative residual bound
is still required. This is written analysis, not a Lean formalization
or a native stationary counterexample.

The [double-crossing charge](../research/independent_audits/stationary_transport_attack_20261124/DOUBLE_CROSSING_CHARGE.md)
bounds actual hits of any compact full continuum with an annular
collar avoiding the inverse original carrier by one quarter of the
reciprocal collar modulus. It uses two disjoint time crossings and
an all-sheet square-sum density, without a selected proper final
exit. A fractional cover of hit sets combines such collars even
at different horizons. Under the earlier full-hull pruning
hypotheses, the entire closed selected deep limb at b<n<q is
disjoint from T and has a univalent intermediate-horizon collar;
actual encounters with that limb can therefore be charged without
a small-Julia predecessor hit. Uniform modulus calibration and
native encounter/no-hit control remain open. A fixed-surface
rectangle family with widths 1/(2δ) and uniformly bounded
ambient vertical width disproves automatic calibration from the
abstract planar hypotheses. These are written analytic estimates
and a planar countermodel, not additional kernel theorems.

The [prefix-potential charge](../research/independent_audits/stationary_transport_attack_20261124/PREFIX_POTENTIAL_CHARGE.md)
uses the stronger full-hull consequence that every physical
carrier point exits the open critical limb by time b. A single
base potential equal to one near the first closed inverse limb,
and zero near the noncritical filled set and ambient boundary,
is pulled back by the actual finite degree-2^j maps and pushed
through all immersion sheets. Every proper parent with a deep
encounter has two unit-length halves in this metric even if its
two sides use different prefixes. Thus the width of the whole
encounter union is at most (2^(b+1)−1)/4 times the infimum
of this base Dirichlet energy; no separate collar calibration
per depth or bank is required. A quadratic cover of actual
endpoint indices gives a cheaper conditional outside-end
estimate. One actual raw restriction ending at a physically
localized selected deep contour suffices for a hit modulo zero;
the saturated monotone model provides a separate locality check.
The native occurrence assertion and a uniform bound on this
single response by R+V+1 remain open. The [finite Lean module](weighted/StationaryPrefixCharge.lean)
formalizes the orbit and quadratic-weight algebra and is subject
to the weighted kernel check; the conformal analysis is written.
The twelve prefix theorems passed the weighted mathlib workflow
at commit 1b7ec3aa59aa1943f5c5e260b630aae3f9804b0b; all seven
workflows triggered at the subsequent CI-wiring head
9f9cffa6b21df47119a986f9b4266185ba950d57 succeeded.

The [stage-endpoint census](../research/independent_audits/stationary_transport_attack_20261124/STAGE_ENDPOINT_CENSUS.md)
uses actual retained sequential windows and properness of the
terminal covering projection to recover a physical endpoint on
the original parent at every inner-ended stage, modulo zero
width. If more than b stages have a physical critical-limb
little-Julia endpoint, the records meet distinct final pulled
components; each component accounts for at most b stages.
The union of all possible stage components has total final
peripheral degree at most b(3·2^h−2) for h<P, by the exact
prefix census and at most one critical suffix arrow. Keeping only
the latest record per parent and the latest qualifying preimage
bank per final target improves the charge to
b·2^h+(b+1)(2^h−2^b), or (7b+3)·2^b at h=b+2. Two
physical records at distinct components (including original
endpoint times) suffice for a proper exit; all-sheet metric
push gives the uniform R-charge without a selected deep
encounter or its calibration. At h=b+2 the remaining parents
have at least three non-Julia-critical stages. Independently,
the full-hull singleton-cut hypothesis at all preperiodic
preimages of the dividing point bounds total (not only
consecutive) critical visits of every carrier point by b
before q; thus a chain stationary through 2b<q must have
an actual interior window birth. This is not necessarily
a selected deep or little-Julia hit. The grounded deep
condenser also splits into a free internal separation
cost and at most the full exterior width W(F); internal
calibration remains open. The [finite stage-counting module](weighted/StationaryEndpointVisits.lean)
isolates the occupancy, birth and degree-sum algebra;
kernel verification succeeded at c752905eb80e78614e8cc52d7d743b45f33a3c1d
(weighted mathlib run 45666874695, all seven workflows passed).
No native stationary or global gate is promoted.

The [canonical lift and direction theorem](../research/independent_audits/stationary_transport_attack_20261124/CANONICAL_LIFT_AND_DIRECTION.md)
charges incomplete canonical lifts of inner-ended parents by
2^h V(F), automatically using the last departure from the
actual full pulled carrier before outer escape. On the
complete family every inner-ended maximal raw restriction
is a gap of the nested physical contact sets, on a single
canonical lift at each prefix. Those lifts and gap records
have a Borel presentation. A compact connected set on which
an immersion is injective has a univalent filled-hull
neighborhood by the Jordan-boundary argument principle;
this supplies univalent parent caps without arbitrary collar
selection. Under the stated protected crest and geometric
fine/coarse filters, a signed crossing count and singleton
covering output give a unique positively oriented directed
component. For the corrected contour action with precritical
host locality, the positive critical source endpoint is
forced into the selected first inverse limb, not the
precritical limb. One-sided stationary endpoint births are
then forced already at h=b<q under the total-visit hypotheses.
These conditional direction results do not propagate a
later interior birth through all preceding selected limbs.
The free internal response between the first closed inverse
limb and T outside the critical limb gives a further
conditional width bound, with the entire outer-escape cost
explicitly charged to V(F), rather than the full filled-set
width. Uniform free-response calibration and native protected
block realization remain open. The new [finite module](weighted/StationaryCanonicalLift.lean)
checks ten crossing-indicator, saturation, birth and charge
theorems; the conformal and topological arguments are written
proofs, not kernel-formalized analysis.

The [quadratic deck separator](../research/independent_audits/stationary_transport_attack_20261124/SYMMETRIC_SEPARATOR.md)
uses the genuine model degree-two involution to exchange the
two preimages of the dividing fixed point. The real interval
fixed-point argument puts the model critical point on their
unique dendrite arc. The saturated critical fiber lies in the
small Julia set, so every connected physical filled-set route
between the two sides meets the separator. Retraction of the
full continuum to the selected closed limb propagates this
separation to all selected depths without a competing filled
route bypass. Under the finite saturated preimage-graph and
preperiodic-contact hypotheses, the root and deep attachment
hosts of the actual small Julia annulus are unique and deck
opposed, hence antipodal. This is a side-existence result,
not a retained Wave occurrence. An explicit symmetric planar
tree with f=z², fixed separator [-1,1] and bounded vertical
width has a free branch-response lower bound 1/(2δ), despite
the antipodal hosts. Thus the separator alone does not
calibrate that response in the native setting.

The [multiplicative collision gain](../research/independent_audits/stationary_transport_attack_20261124/COLLISION_GAIN.md)
proves an all-sheet metric estimate W(A)≤2^h W(D)/r²
for r genuinely disjoint parent-time windows projecting
to whole output paths. On a complete canonical lift family,
each retained inner-ended restriction is a gap on the
unique canonical lift. The actual one-step multiplicities
(one or two) multiply under nested windows. Therefore k
double stages in h give W(D)≥2^(2k−h) W(A), with at most
2^h V(F) charged separately for incomplete lifts.
Two protected deck-opposed crest anchors in one parent cap
suffice to certify a double stage, but the two separator
hosts alone need not satisfy the marking/filter conditions.
Native duplication frequency, output Wave controllability,
free-response calibration and the corrected marking
interface remain open. The [finite/real module](weighted/StationaryDeckSeparator.lean)
checks the interval fixed point, connected-image separation,
deck injectivity exclusion, and gain and gap algebra.
Its eleven public theorems compiled successfully at
f6702318e9e35b1bb0ef11de1b2edaeae5ab1af7
(weighted run 45671447375, log reports 8774 successful build
jobs; the workflow was cancelled after compilation when a
documentation revision advanced the branch).

The [angular calibration note](../research/independent_audits/stationary_transport_attack_20261124/ANGULAR_CALIBRATION.md)
gives a uniform flat-cylinder charge 1/(2ε) for a base of
angular span at least ε, and improves it to
π log(8/ε)/(log 2)^2 for families whose caps contain a
common fixed crest access. Thus exponentially small
qualified-anchor separations can suffice at linear
width cost. On the small-span residual, separated
qualified source anchors must occur in different
retained caps, giving a double stage even without
exact antipodality. Independently the positive strip
Poisson kernel bounds the degree-one inner-circle
distortion of I on the old-carrier annulus by
exp(±π V(F)), using its modulus at least half the
target modulus. This estimate does not apply to the
full pulled carrier inclusion, whose added pieces
land in the old annulus interior. Quantitative
attachment distortion and qualification of the
actual anchors remain separate native obligations.

The [coherent packet gain telescope](../research/independent_audits/stationary_transport_attack_20261124/COHERENT_PACKET_GAIN.md)
confines all proper simple crosscuts directed over one fixed
source inner access to a single degree-d covering chart
after an explicit width discard C_d=π log(16d)/(log 2)^2.
A radial half-annulus metric detects every escaping primary
leaf, with no transverse-measure subtraction. On complete
canonical lifts a good primary gives coefficient-one
transport for every subfamily. A second retained inner
restriction is its deck translate and occupies a disjoint
parent-time window, giving factor-two width gain. Covering
injectivity on the fixed primary chart makes all distinct
good parent images disjoint. Under the specified Borel
atlas this yields a weighted sum over multiplicity patterns,
W(D_good)≥Σ_k 2^k W(A_good,k), after total discard at most
2^h V+h C_2. A positive fraction η with even one duplicate
stage gives W(C)≥(1+η)W(A)−2E_h if the final good outputs
are in a genuine uniformly controllable Wave C. No majority
of duplicate stages or uniform angular calibration is needed.
Failure of gain leaves a quantitative single-restriction,
carrier-edge residual; the native directed occurrence and
controllable output premises remain explicit. The [finite
module](weighted/StationaryPacketGain.lean) checks the
weighted excess and response algebra. The first eleven public
theorems compiled in weighted run 45674655696 at revision
5e9c41e38b4dd565368a1e1ffc007dbcec7ac343 (8776 build jobs);
the workflow was cancelled after successful compilation by a
subsequent note revision. The expanded module adds the auxiliary
series-response theorems below and needs its own final kernel check.

The [attachment screening example](../research/independent_audits/stationary_transport_attack_20261124/ATTACHMENT_SCREENING.md)
uses an unchanged upper bank of a fixed slit, two attached
trees enclosing a room and narrow open neck, and a genuine
degree-two squaring cover. A harmonic cos-exponential
barrier followed by reflection and a local gradient estimate
bounds the new angle length by 16√2·M_0 exp(−π/(4δ)),
although the old length is fixed and both vertical widths
remain bounded. The neck has exact crossing width 1/δ.
This rules out an abstract attachment-angle estimate based
only on the listed nested-carrier and covering geometry;
it is not a compatible forward-invariant native primitive
dynamical model. The coherent-packet metric pruning avoids
this distortion for actual common-anchor packets.

The [auxiliary gap response](../research/independent_audits/stationary_transport_attack_20261124/AUXILIARY_GAP_RESPONSE.md)
uses a complete canonical lift with a genuine selected deep
pulled-carrier encounter. If it avoids one of the final bank
separators, finitely many distinct host groups of the full
saturated carrier give two raw gap windows across different
host groups. At least one is disjoint from the final primary
window. Under the explicit fine-side realization condition,
each has a whole fine atom of the separator in its disk-cap
base. Fixed-anchor confinement at the actual degree-2^h
cover costs at most N_b C_(2^h), with N_b=12b·2^h, and
gives genuine simple auxiliary output packets. Their uniform
native Wave controllability is a separate required input.
The auxiliary windows need not survive any intermediate
coarse filters and need not have distinct terminal images.
Square-sum metrics on the two disjoint parent windows give
w≤PB/(P+B), P≥w+w²/B for primary width P and total auxiliary
container width B. If the good primary output map is injective
and the auxiliary mass is ≥ηW(A), near-maximal auxiliary
containers give a primary response of order η²/N, after the
explicit discard. If both bank components are physically hit,
the earlier endpoint-cover R-charge applies. Thus the missing
two-retained-occurrence noncollision step can be bypassed in
the conditional actual-deep-contact branch; the deep-carrier
encounter, fine-side realization, native output controllability
and corrected geometric marking remain open. Five added
finite theorems in StationaryPacketGain check the contact
transition and auxiliary response algebra. No native or
global proof obligation is promoted.

The [near-critical packet control note](../research/independent_audits/stationary_transport_attack_20261124/NEAR_CRITICAL_PACKET_CONTROL.md)
conditionally supplies the previously missing auxiliary container bound:
the two separator images lie in BL_1 and BL_2, and the common chart
cut plus the near-critical bank gives one over-critical module and at
most 18b+1 localized Waves per actual confined packet. The weaker
end-fine-atom direction criterion still requires the actual proper
old-side and corrected marking hypotheses. The accompanying [finite
regression checker](../research/independent_audits/stationary_transport_attack_20261124/check_near_critical_packet.py) tests cyclic bank, chart cut and end-atom
combinatorics, not analytic or native geometric realization. Selected
deep contact, host/fine-side realization, directed retained occurrences
and native terminality integration remain open. No ledger status changes.

The [suffix-anchor response](../research/independent_audits/stationary_transport_attack_20261124/SUFFIX_ANCHOR_RESPONSE.md)
constructs full old-proper fine atoms by the commuting immersion/cover
square, extends critical saturation by degree-matched contour squares,
and applies signed raw-gap counts at every suffix. Either a distinct
auxiliary physical window exists or backward critical origin exclusion
forces the selected depth-h carrier contact on the positively oriented
class. Combined with the two-bank response this gives a conditional
O_b(R+V+1) bound at explicit terminal scale 1/(64N), with N=h+12b*2^h.
Final orientation (or an extra singleton step), the corrected geometric
marking and exact saturated graph/host realization, relative continuation
and ambient terminality remain explicit requirements. The [finite
checker](../research/independent_audits/stationary_transport_attack_20261124/check_suffix_anchor_response.py) passed 146,402 local cases; the new two Lean declarations
check only the finite backward and strict-response algebra, pending CI.
No native ledger promotion.

The [precritical terminal response](../research/independent_audits/stationary_transport_attack_20261124/PRECRITICAL_TERMINAL_RESPONSE.md)
uses the genuine deck-related old-proper atoms of the entire critical
little vertex to obtain a two-window width cap M/2+2(V+C_2) for
actual over-critical packets, without retained action. First/last
precritical end atoms give a common primary and the mixed cap
3M/4+3(V+C_2) with only one available singleton step. Combined with
the suffix/ separator series response this removes the final
orientation exception at scale 1/(512N) and treats small q by
stopping at the first precritical crest, on the stated exact
geometric directed-chain hypotheses. It is a relative cap, not
an absolute precritical discard for N1. The [new finite checker](../research/independent_audits/stationary_transport_attack_20261124/check_precritical_response.py)
passed 1,165,122 local cases; three added real-number Lean
inequalities await kernel CI. All seven workflows passed at
9fd71ee (including the two suffix theorems). Native relative
continuation, exact source marking and ambient comparison remain
open; no canonical ledger promotion.

The [positive crest continuation](../research/independent_audits/stationary_transport_attack_20261124/POSITIVE_CREST_CONTINUATION.md)
replaces the assumed intermediate central-ending/whole-limb crest
sequence by a gain-or-discard telescope from a positive initial
crest. At a noncritical step, first/last anchored gaps either
advance the entire crest or force double gain in a common primary
packet. Relative near-maximality gives the recurrence
L_(j+1)=2L_j+4C_2+lambda W. The final over-critical fraction
is controlled through a whole-packet extra primary and the two
deck-related raw windows; the oriented central residue uses the
suffix/ bank series response against the whole stage-h primary.
This gives an explicit conditional O_b(R+V+1) bound with the
uniform away-Shift input and all stated geometric realization,
singleton and comparison hypotheses. Small q stops at the
precritical crest. [The checker](../research/independent_audits/stationary_transport_attack_20261124/check_positive_crest_continuation.py)
passed 80,885 exact arithmetic cases. No new Lean theorem, actual
native geometry certification, or mixed-direction/ambient
terminality result is claimed.

The [signed endpoint shift](../research/independent_audits/stationary_transport_attack_20261124/AWAY_ENDPOINT_SHIFT.md)
supplies the previously separate away-Shift input on the same exact
corrected geometric action. End-fine probes inside and outside the
source cap trap the actual retained base and shift its endpoint limbs.
A median split and four fixed alternating half-plane electrodes give
the reciprocal width bound, with the canonical-completion and
chart-discard cost: W(A)<=4V+2C_2+4, or 2V+C_2+2 in one direction.
Simplicity of a surviving singleton is recovered by the actual
confined retained gap, and essential equal-end inputs cost <=1/2.

The [shared-crest ambient response](../research/independent_audits/stationary_transport_attack_20261124/AMBIENT_SHARED_CREST_RESPONSE.md)
constructs a common raw primary for the entire ambient lamination
(including short or breakable background), uses singleton identity
only on the stationary subset, and charges the positive and negative
stationary directions against the same whole primary widths.
An extra raw comparison stage, not an extra singleton requirement,
replaces the earlier relative precritical three-quarter cap by
O(C_2+d+sqrt(Md)), with d=M-W+E. On a common actual BL_1-atom
input with a stationary fraction sigma, this gives the explicit
ambient O_(b,sigma)(R+V+1) threshold and uniform K=6b(h+4)+1
response control. The corrected marking and exact saturated
graph/host hypotheses remain; a general unrelated-crest ambient
selection/replacement theorem and source-level downstream integration
are still open. The [discrete regression](../research/independent_audits/stationary_transport_attack_20261124/check_ambient_shared_crest.py) checks
the end-probe, endpoint-order and scale algebra, not the geometry.
Three finite real-number lemmas are added to StationaryPacketGain
pending kernel CI. All seven workflows passed at e967265.
No ledger status is promoted.

The [sector and phase assembly theorem](../research/independent_audits/stationary_transport_attack_20261124/SECTOR_PHASE_ASSEMBLY.md)
proves a degree-independent 4pi/log(2) discard for an anchored packet
with actual endpoints in a covering sector, and the same bound for
confinement between nested half-disks with fixed electrodes.
A finite target anchor/antipode cell partition and a reciprocal-width
order cut for shared endpoint cells assemble actual trajectories,
with total width loss at most m C_d + Delta + 2T L_* +
10 binomial(T,2) + 1, T<=4m^2. Delta is the explicit source-width
deficit from selecting the largest phase per directed cell pair.
It need not be a literal image collision; a two-deck-copy annular
example shows that it cannot be uniformly removed from the specified
images in general. In the corrected noncritical singleton corridor
the signed endpoint trap places all selected bases in one injective
sector, so Delta=0 and a simpler m(C_2+L_*)+2V transfer suffices.

The [multi-packet ambient alternative](../research/independent_audits/stationary_transport_attack_20261124/MULTIPACKET_AMBIENT_DEFICIT.md)
uses the assembled primary supports instead of a common ambient crest.
With the stated finite per-stage anchor and output control certificates
and the earlier exact native geometric hypotheses, the same stationary
defect inequality holds with E=E_base+sum Delta_j. At large absolute
scale and near-maximality a stationary fraction sigma forces a
cumulative phase deficit >delta W/4, delta=sigma^2/(2048N), or a
strict wider controllable output. This identifies two sizeable
different phase groups of one directed cell pair. Uniform native
control, critical-side phase response, actual source marking and
downstream integration remain open. [Finite checker](../research/independent_audits/stationary_transport_attack_20261124/check_sector_phase_assembly.py);
three new Lean accounting declarations await kernel CI. All seven
workflows passed at f32378d. No canonical ledger promotion.

The [critical phase localization and selection](../research/independent_audits/stationary_transport_attack_20261124/CRITICAL_PHASE_LOCALIZATION.md)
uses the native parabolic critical-cycle image condition and the
actual saturated minimal dendrite hull: images of old critical
hull arcs stay in the bounded BL_(-b)..BL_b bank. Refine the
target cut set by the bank atom boundaries. Every competing
directed cell pair then has a common actual whole near-critical
crest atom: either a critical old-proper anchor contributes,
or two phases with noncritical anchors force the cap through
the omitted BL_1. The phase deficit is bounded by the union
of critical-anchor and BL_1-crested target parents, and each
conflict phase packet is uniformly controllable. An away parent
whose positive primary crests BL_1 gives a distinct negative
raw window by the zero signed sum at a critical end-atom probe.
Finite optimal phase configurations may use all eligible
actual windows, preserving disjoint supports with one choice
per parent. A local exchange compares uncovered mass to
pivotal competing mass with no other admitted candidate;
duplicate eligible deck lifts of a singleton are always
covered. The exact remaining native target is a response
to sizeable pivotal near-critical conflicts and uniform
ambient control, not generic crossing images.
[Finite checker](../research/independent_audits/stationary_transport_attack_20261124/check_critical_phase_localization.py); two new accounting lemmas
await CI. All seven workflows passed at 9f2408f, including
1,981,536 finite phase-assembly regressions and three
new Lean declarations. No canonical ledger promotion.

The [phase-free anchored comparison](../research/independent_audits/stationary_transport_attack_20261124/ANCHORED_PHASE_FREE_RESPONSE.md)
takes a different maximality class: actual marked simple Borel
laminations sharing one whole crest atom, anywhere on the circle.
Fixed-map supremum finiteness follows by the cap-span band metric.
With a near-critical common anchor and this class's width cap,
a bounded-probe median Shift argument controls all away nonshort
modules without singleton hypotheses. Signed probe disagreements
give distinct actual raw windows, even when their terminal images
differ. A whole selected common primary sequence and the earlier
suffix/separator geometry give a quantitative mostly-short
conclusion for near-maximal near-critical anchored packets
without unbreakability or phase selection. The new class does
not impose the original source-uniform controllability bound,
and remote maximizing anchors, short-crest saturation and
uniform long fast-forward in this class remain genuine gates.
[Finite checker](../research/independent_audits/stationary_transport_attack_20261124/check_anchored_phase_free.py); three finite algebra lemmas
await CI. All seven workflows passed at 2bf9128, including
226,670 critical phase/selection checks and two Lean additions.
No ledger status is promoted.

This checker establishes finite rational endpoint-cover and degree-budget
certificates and rejects invalid accounting. It does not construct native
exits. The stationary hypotheses still need to supply one eligible actual
exit per retained parent, or the sufficient two-bank-hit condition. An
endpoint on a full carrier edge need not be an ideal end of the final
small-Julia surface. Those existence obligations, the independent repair
of the source stationary argument, and the global gates remain open.

This audit and its new formalizations were prepared with OpenAI GPT-6 Astra Pro. Human mathematical review is pending.
