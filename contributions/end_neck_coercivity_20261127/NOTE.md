---
ledger: END_PLUMBING_TRACE_RESPONSE_CONTROL
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; research, adversarial audit, and prospective Lean proof development
human_review: none
---

<a id="end-neck-coercivity-20261127"></a>

# Draft: full-response coercivity through nested physical necks

## Claim

Work in progress. No new theorem or closure is claimed at this checkpoint.
The target is the all-depth coercive full-response clause of
END_PLUMBING_TRACE_RESPONSE_CONTROL. A contribution will count here only
if it supplies genuinely new mathematics and a theorem compiled in the
repository's Lean project with the existing trust audit.

## Evidence

The base is main commit e8d82717b184b5f4e46c34a46b1445fc75f33a1c.
The initial audit excluded already archived one-neck Fourier estimates,
annular midpoint shorting, whole-electrode response comparisons, and
abstract scalar elimination as possible new contributions.

The active question is whether the full physical trace response through
a serial family admits a coercive estimate stable under all permitted
boundary identifications, with an effective threshold not obtained merely
by multiplying the existing one-neck error factors. Any proof must identify
its actual analytic surfaces, trace spaces, gluing maps, and terminal
observables. Any obstruction must verify those same hypotheses.

Research milestones and rejected routes will be committed here as the
investigation proceeds. The local workspace has no Lean installation and
insufficient free space to install the pinned toolchain; the unchanged
repository Lean workflows will be the compilation and axiom-audit judge.

### First proof checkpoint: nonlinear variational contraction

Two initial Lean modules now contain the proposed algebraic and variational
proof. Their first compilation is pending; the statements below are not yet
reported as verified results.

For a normalized nonconstant Fourier mode, put

\[
 Q_e(u,v)=\frac{(u-ev)^2+(v-eu)^2}{1-e^2},\qquad 0\le e<1.
\]

For any index set, sum these nonnegative energies in the extended
nonnegative reals. A load is any nonnegative, degree-two homogeneous
function of the entire trace; convexity, continuity, existence of a
minimizer, and quadratic-form representation are not assumed. Eliminate
the full exit trace by taking the infimum of collar energy plus load.

If two loads compare in both directions by a factor \(a^2\), \(a\ge1\),
and every mode has \(e\le r<1\), the proposed output comparison factor is
\(b^2\), where

\[
 b=\frac{a+1+r^2(a-1)}{a+1-r^2(a-1)},\qquad
 \frac{b-1}{b+1}=r^2\frac{a-1}{a+1}.
\]

The proof uses one common trial-trace scaling \(v\mapsto(b/a)v\).
It therefore survives arbitrary linear mixing of the coordinates. The
initial source files are `AnnularModeContraction.lean` and
`AnnularVariationalResponse.lean` in `formalization/weighted/`.

This checkpoint concerns all **nonconstant** Fourier coordinates. The
relative constant mode and the native physical contact/welding
construction remain separate. Identifying the energy with the actual
cylinder Dirichlet problem and proving the all-depth terminal-independent
conclusion are active work.

The classical quadratic operator analogue is already in Jimmie Lawson
and Yongdo Lim, *A Birkhoff contraction formula with applications to Riccati
equations*, SIAM J. Control Optim. 46 (2007), 930–951,
doi:10.1137/050637637. Related function-space contraction occurs in Zheng
Qu, *Contraction of Riccati flows applied to the convergence analysis of a
max-plus curse-of-dimensionality-free method*, SIAM J. Control Optim. 52
(2014), 2677–2706, doi:10.1137/130906702. These are prior art. Neither the
general contraction idea nor the quadratic special case is claimed as new.

## Dependencies

The declared ledger dependencies and the complete original statement remain
in ledger.json. Initial prior-work checks include:

- research/independent_audits/annular_midpoint_response_20261126/NOTE.md
- research/independent_audits/whole-boundary-response_20261126/NOTE.md
- research/mlc_unified/network_response_state.md
- research/mlc_unified/novelty_and_value_audit_20260725.md
- The trace-response and plumbing work in the research-push bundles.

## Boundary

This draft has no proved result yet. It does not close the target obligation,
provide a source-defined all-depth contact or welding construction, or change
any ledger status. A known theorem, an abstract criterion assuming the desired
analytic control, or a routine corollary will not be reported as new progress.
If the investigation fails to obtain a substantive result, the draft will be
closed so that the obligation is unclaimed again.

## Attribution

The target and prior results belong to this research archive and their cited
original authors. Classical Fourier, extremal-length, and Dirichlet-space
tools will be attributed explicitly if used. AI assistance is disclosed above;
no human mathematical review has occurred.
