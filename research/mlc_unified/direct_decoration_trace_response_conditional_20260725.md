# Re-audit of the proposed conditional trace-response theorem

Date: 2026-07-25  
Status: **rejected as stated; corrected interface recorded below**  
Global status: `END_PLUMBING_TRACE_RESPONSE_CONTROL`, `UPTCR`, and `MLC`
remain open

## 1. Verdict

The earlier version of this note was not a valid conditional theorem.  Three
independent defects were found:

1. its displayed bilinear infimum is unbounded below;
2. quotienting each port by its own constants destroys relative electrode
   potentials; and
3. a strict contraction factor does not survive addition of an arbitrary
   common nonnegative component energy.

The local rectangle response, complete-trace fiber-product gluing, and
closed-form elimination results already proved elsewhere remain valid under
their stated hypotheses.  This note now records the exact correction and
does not promote a new theorem.

## 2. Correct Dirichlet response

For a connected Lipschitz cell \(D\) with retained boundary trace \(u\), the
response quadratic form is

\[
 q_D(u)=
 \min\left\{
   \int_D|\nabla U|^2:
   \operatorname{Tr}U=u
 \right\}.
\tag{2.1}
\]

The associated bilinear form is obtained by polarization, or equivalently
by taking the gradient inner product of the harmonic extensions.

The rejected formula

\[
 \inf\int_D\nabla U\cdot\nabla V
\tag{2.2}
\]

is not a response.  With zero traces, \(U=t\psi\) and \(V=-t\psi\) for
\(0\ne\psi\in H^1_0(D)\) make (2.2) tend to \(-\infty\).

## 3. Correct port gauge

For ports \(\Gamma_1,\ldots,\Gamma_N\) of one connected cell, the trace
space must retain relative constants:

\[
 \mathcal H_D=
 \left(\bigoplus_{i=1}^N H^{1/2}(\Gamma_i)\right)
 \Big/\operatorname{span}\{(1,\ldots,1)\}.
\tag{3.1}
\]

Equivalently, one may retain the mean-zero part of every port together with
an \((N-1)\)-dimensional vector of relative port potentials.

Independent quotients \(H^{1/2}(\Gamma_i)/\mathbb C\) are invalid.  On a
width-one rectangle of length \(R\), constant endpoint traces \(a,b\) have
energy

\[
 \frac{(a-b)^2}{R},
\]

but independent port quotients would send both traces to zero.

For a disconnected cell, there is one diagonal gauge constant per connected
component, not one per port.

## 4. Strictness is not automatic after gluing

Suppose \(q_{\rm out}=\mu q_{\rm in}\) with \(0<\mu<1\).  If the same
nonnegative component energy \(c=tq_{\rm in}\) is added to both responses,
then

\[
 \frac{q_{\rm out}+c}{q_{\rm in}+c}
 =\frac{\mu+t}{1+t},
\]

which tends to one as \(t\to\infty\).  Positivity and common addition
preserve non-strict Loewner comparisons with factor at least one, but they
do not preserve a strict factor below one.

A future physical response theorem must therefore prove at least one of:

- a relative bound \(c\le\varepsilon q_{\rm in}\) with an explicit
  resulting factor;
- a strict transition for the complete glued state;
- a coercive comparison that controls eliminated energy; or
- an additive-error estimate charged in the transition budget.

## 5. Surviving conditional interface

For an actual source-defined collar, a valid theorem may begin only after
the following data are proved:

1. a uniformly finite or compactly retained complete port state;
2. reference charts and trace maps on the full space (3.1);
3. closed, nonnegative quadratic forms defined by (2.1);
4. phase-preserving complete-trace gluing on actual common interfaces;
5. closed-range, coercivity, or lower-semicontinuous relaxation hypotheses
   for every eliminated variable;
6. a source-proved relative error or full-state strict transition; and
7. all-depth contact closure, no-bypass control, and endpoint-welding
   compatibility.

These are hypotheses to be constructed, not conclusions of the present
note.  In particular, a universal port bound, common trace space, physical
welding control, and strict response margin have not been established for
the direct-decoration or virtual towers.

The full failure and repair are proved in
`side_research_retained_lemmas.md`, Section 5.

