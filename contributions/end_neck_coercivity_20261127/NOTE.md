---
ledger: END_PLUMBING_TRACE_RESPONSE_CONTROL
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; research, adversarial audit, and Lean proof development
human_review: none
---

<a id="end-neck-coercivity-20261127"></a>

# Investigation of all-depth annular response: no qualifying novelty claim

## Claim

**This investigation has not produced the new mathematical advance requested
by the user.** It does not close `END_PLUMBING_TRACE_RESPONSE_CONTROL` or
establish a new physical subcase of that obligation. The Lean sources record
the candidate argument precisely; new proof code is not being counted as
new mathematics.

The `partial` front-matter label classifies the model-level scope of the
candidate, not a claim that this packet should be accepted as a novel
research contribution. This packet is withdrawn as a proposed research
advance, and the draft is closed to release the open obligation. No ledger
or status record has been changed.

## Evidence

### 1. Target and audit

The investigation began from main commit
`e8d82717b184b5f4e46c34a46b1445fc75f33a1c`; it incorporated main through
`6a10209b3cc51878bc45de7668894757b2575e08` while preserving the registrations
from both branches. Draft PR #260 was opened before the proof development,
and successive checkpoints were committed to it.

The exact target requires source-defined all-depth contact-closed physical
interfaces, complete multi-port response and endpoint-welding control,
protected-carrier and last-live-port compatibility, and a uniform no-bypass
or coercive estimate before using a finite strictness margin. Existing
one-neck Fourier estimates, annular midpoint shorting, full-boundary
response comparisons, scalar elimination, and gauge/no-bypass obstructions
were excluded as possible new contributions at the outset.

The candidate attacked terminal dependence through an entire serial family
of collars. Its strongest completed formal statement is about arbitrary
fixed linear weldings in a positive-frequency trace model. It does not
construct the physical interfaces needed by the target.

### 2. The precise candidate estimate

For a normalized nonconstant Fourier mode, define

\[
 Q_e(u,v)=\frac{(u-ev)^2+(v-eu)^2}{1-e^2},\qquad 0\le e<1.
\]

For an arbitrary index set, sum these nonnegative energies in the extended
nonnegative reals. A terminal load is a function
\(B:\mathbb R^I\to[0,\infty]\) with \(B(0)=0\) and
\(B(sv)=s^2B(v)\) for every real \(s\). In particular the load is even.
No convexity, continuity, finite-dimensionality, or attained minimum is
assumed. Define the complete exit-trace elimination

\[
 T_e B(u)=\inf_v\left\{\sum_{i\in I}Q_{e_i}(u_i,v_i)+B(v)\right\}.
\]

If \(a\ge1\),
\(D\le a^2 B\), \(B\le a^2D\), and \(0\le e_i\le r<1\), then
both output comparisons hold with factor \(b^2\), where

\[
 b=\frac{a+1+r^2(a-1)}{a+1-r^2(a-1)},\qquad
 \frac{b-1}{b+1}=r^2\frac{a-1}{a+1}.
\]

The direct proof uses a single competing trace \((b/a)v\) for all
coordinates. It therefore remains valid after precomposition of the loads
by an arbitrary linear map of the whole trace space. A one-coordinate
quadratic pair realizes the comparison factor, so that factor cannot be
uniformly improved in this model.

Writing \(M(u)=\sum_i u_i^2\), with the sum understood in the same extended
sense, the response also satisfies

\[
 \frac{1-r^2}{1+r^2}M(u)
 \le T_eB(u)
 \le \frac{1+r^2}{1-r^2}M(u).
\]

Consequently any two initial loads become uniformly comparable after one
collar, including loads that were not comparable before it.

### 3. Actual infinite-depth conclusion of the model

A layer consists of its collar attenuation and one linear welding.
Compose layers in order from the observed boundary to the terminal end.
For two systems sharing the first \(N+1\) layers, put

\[
 p_N=\prod_{j=0}^{N}r_j^2,\qquad
 a_N=\frac{1+p_N}{1-p_N},\qquad
 C(u)=\frac{1+r_0^2}{1-r_0^2}M(u).
\]

Let \(E_n\) denote the response through \(n+1\) layers. At every observed
trace of finite mass, the difference of their response energies obeys

\[
 |E_n(u)-E_m(u)|\le (a_N^2-1)C(u)
 =\frac{4p_N}{(1-p_N)^2}C(u),\qquad n,m\ge N.
\]

The formal theorem states the first form of this bound; the second equality
is elementary algebra. The remaining layers and terminal loads can differ
arbitrarily. If \(r_j=e^{-L_j}\) and \(\sum_{j=0}^{N}L_j\to\infty\), the
responses have a single limit independent of every horizon-dependent
choice of terminal load. No norm bound or convergence of the fixed
sequence of weldings is used. The compared systems must share their
observed prefix; this is not a continuity theorem for varying prefixes.

This infinite-depth statement is obtained by composing the local estimate,
then proving a common-prefix Cauchy bound. It is not independently claimed
as original mathematics. Divergence of total length gives convergence; it
does not by itself give a summable error sequence in the native transition
norm. No such transition-error budget is proved here.

### 4. Lean source and validation scope

The six modules are under `formalization/weighted/`:

| Module | Exact role |
|---|---|
| `AnnularModeContraction` | Scalar rescaling, coercivity, and comparison-radius identities |
| `AnnularVariationalResponse` | Extended-energy trace infima, homogeneous loads, arbitrary linear welding, universal comparison |
| `AnnularResponseClock` | Product formulas and divergent-length convergence of the comparison radius |
| `AnnularResponseSharpness` | Exact scalar quadratic caps and optimality of the one-step factor |
| `AnnularFourierTrace` | Explicit harmonic interpolation and its least one-dimensional cylinder-mode energy among C1 competitors |
| `AnnularWeldedChain` | Finite-prefix estimates, Cauchy property, and terminal-independent infinite-depth limit |

The main limiting declaration is
`AnnularWeldedChain.divergent_length_terminal_independent_limit`.
The variational declaration is
`AnnularVariationalResponse.response_contraction`.
The physical-mode calculation is
`AnnularFourierTrace.mode_isLeast_energy`; its scope is one-dimensional
mode energy. It does not prove the complete angular Parseval identity,
Sobolev trace completion, or a gluing identification for native dynamical
surfaces.

All sources are registered as `METADATA`, making no model-to-physical
bridge claim. No validator, workflow, trust policy, or toolchain was
relaxed. The local workspace has no Lean installation and insufficient
space to install the pinned toolchain, so the unchanged repository CI
is the compilation and transitive-axiom judge.

**Validation status: passed.** All 23 CI workflows succeeded at the proof
checkpoint
[`bda5cc3466856207eff4492f635ed24ee577bfa1`](https://github.com/dovvnloading/loops-research-archive/commit/bda5cc3466856207eff4492f635ed24ee577bfa1).
The [weighted Lean run](https://github.com/dovvnloading/loops-research-archive/actions/runs/46111249010)
completed the full build and the transitive axiom audit. Each of the six
modules was audited individually, and the project-wide audit reported
`AXIOM_AUDIT_PASS weighted: 254 modules, 6626 declarations`.
Only the existing allowed axioms (`propext`, `Classical.choice`, and
`Quot.sound`) occur in the audited dependencies. Source coverage and the
checks rejecting proof trust escapes also passed. There are no proof holes,
new axioms, or weakened checks in these sources.

The final record update changes only this note; all Lean sources and their
registrations remain byte-for-byte identical to the successful proof
checkpoint. This establishes formal correctness of the stated model
results. It does not establish novelty or the missing physical hypotheses.

### 5. Why the nonlinear extension does not establish novelty

There is an exact line-envelope explanation. For each span
\(\ell=\mathbb R w\), including the zero subspace, define an extended
quadratic form by

\[
 q_{B,\ell}(tw)=t^2B(w),\qquad
 q_{B,\ell}(v)=\infty\quad(v\notin\ell),
\]

with value zero at the origin. The definition is independent of the choice
of generator after the corresponding coefficient change. Then

\[
 B(v)=\inf_\ell q_{B,\ell}(v).
\]

Annular elimination commutes with that infimum. Compared loads give
compared forms on each *same* line. Thus the apparent nonlinear/nonconvex
generality has a direct explanation by envelopes of constrained quadratic
loads; it does not by itself supply a new geometric mechanism.

The classical operator theory is already extensive. Lawson and Lim prove
Birkhoff/Riccati contraction on infinite-dimensional Hilbert spaces, so
infinite-dimensionality alone is not a priority claim. Qu studies
function-envelope contraction and exponential terminal-cost forgetting.
We do not assert that either paper literally states every extended-energy
hypothesis used in these files. We do conclude that no defensible new-math
claim has been established by the present investigation, and the requested
standard does not permit treating an unverified priority claim as progress.

### 6. Why the physical multi-port obligation is still open

For several live ports the correct trace space retains relative port
means: it is the direct sum of the full trace spaces modulo **one diagonal
constant**. The present model contains nonconstant coordinates only.

If a live external voltage \(x\) is retained, the load has the form
\(B(v,x)\). The proof rescales \(v\) while holding the external data fixed.
Joint quadratic homogeneity in \((v,x)\) does not justify that step.
Silently quotienting the constant on every port would remove actual
observables. The zero-frequency collar energy is proportional to
\((a-b)^2/L\), not to the uniformly coercive positive-frequency form above.
These distinctions are already documented in the archive; they are not
new obstructions proved by this packet.

The source-defined all-depth contacts, admissible welding cocycle,
protected carriers, retained relative means, genuinely last-live ports,
no-bypass statement, and Value/transition-norm compatibility remain
unconstructed. The formal model theorem does not infer any of those
hypotheses from its conclusion.

### 7. A stronger live-port route was also screened

We also investigated keeping the distal electrode voltages. For a genuine
Dirichlet problem with one distal electrode, the proposed route uses its
nonnegative equilibrium potential and the Poisson expansion on the first
round collar. If that collar has length \(L_0>0\), the normalized root
current measure has Fourier coefficients bounded by
\(nL_0/\sinh(nL_0)\) for \(n\ge1\). Once a valid serial capacity bound
is available, this can control root-to-electrode coupling with a retained
voltage. The argument requires actual variational clipping, harmonic
positivity, Fourier trace identification, and physical gluing. None of
those whole-surface identifications is proved by the six Lean modules.
This lead is therefore not counted as a theorem here.

There is a further limitation even after those identifications. For several
distal electrodes, let \(C\) be their capacitance matrix and let \(c_i\)
be its row sums, namely the root-to-electrode charges. The graph-Laplacian
inequality \(C\ge\operatorname{diag}(c_i)\) can help bound the Schur
complement correction to the root response. It does not bound
\(x^TCx\): large mutual conductance between two distal electrodes can
persist while all root charges tend to zero. Screening the root coupling
therefore does not compactify the full retained multi-port response.
This is another reason not to promote a root-local estimate to the open
full-state obligation. The proposed reasoning is a synthesis of classical
maximum-principle, Poisson-kernel, capacity, and elimination tools; no
priority or Lean-validated physical result is claimed for it.

## Dependencies

The ledger dependencies and the full original statement remain unchanged.
The prior-work audit included:

- `research/independent_audits/annular_midpoint_response_20261126/NOTE.md`;
- `research/independent_audits/whole-boundary-response_20261126/NOTE.md`;
- `research/mlc_unified/network_response_state.md`;
- `research/mlc_unified/direct_decoration_trace_response_conditional_20260725.md`;
- `research/mlc_unified/weak_welding_graph_compactification_20260725.md`;
- `research/mlc_unified/novelty_and_value_audit_20260725.md`;
- the trace-response and plumbing work in the research-push bundles.

## Boundary

No ledger row should be promoted from this packet. No new theorem about
native quadratic dynamics, all-depth physical plumbing, protected-tower
closure, or MLC is claimed. The exact candidate is retained so that the
attempt and its limitations are reviewable, not offered as a substitute
for the requested new mathematics.

The repository's `AGENTS.md` instructs an investigator who has made no real
progress to say so and close the draft rather than submit a restatement,
survey, or plan. That instruction, together with the user's stricter
novelty requirement, governs this investigation's disposition.

## Attribution

Classical Fourier-mode Dirichlet minimization, electrical elimination,
and Riccati contraction are prior mathematics. In particular:

1. Jimmie Lawson and Yongdo Lim, *A Birkhoff contraction formula with
   applications to Riccati equations*, SIAM Journal on Control and
   Optimization 46(3) (2007), 930–951, DOI
   [10.1137/050637637](https://doi.org/10.1137/050637637), especially the
   contraction theory in Sections 5–8. The paper explicitly includes the
   infinite-dimensional Hilbert-space setting.
2. Zheng Qu, *Contraction of Riccati flows applied to the convergence
   analysis of a max-plus curse-of-dimensionality-free method*, SIAM
   Journal on Control and Optimization 52(5) (2014), 2677–2706, DOI
   [10.1137/130906702](https://doi.org/10.1137/130906702), with author
   preprint [arXiv:1301.4777](https://arxiv.org/abs/1301.4777).

The target and earlier archive results belong to their cited authors.
AI assistance is disclosed in the front matter; no human mathematical
review has occurred. Neither new Lean code nor absence of an identical
search hit establishes mathematical priority.
