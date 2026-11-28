# Retained pre-formalization candidate: nonlinear half-plane reversal

**Committed before the new Lean implementation.** Status: candidate retained
after a *bounded* literature comparison, not yet proved or CI-validated.
No claim of global literature priority is made.

## Exact quadratic statement

Let `P_0(c)=0`, `P_{n+1}(c)=P_n(c)^2+c`, and let `M` be the set of
parameters with bounded critical orbit. Put
`X_n(c)=P_{n+1}(c)` and, for one *base* parameter `c`, define the
ordinary **spatial derivative cocycle**
\[
D_0(c)=1,\qquad D_{n+1}(c)=2 X_n(c) D_n(c).
\]
Thus `D_n(c)=(f_c^n)'(c)`. No second-orbit factor enters its definition.

For another parameter `d` put
\[
h=d-c,\quad \Delta_n(c,d)=X_n(d)-X_n(c),\quad
E_n(c,d)=\Delta_n(c,d)/D_n(c)
\]
and define the finite **nonlinear half-plane correction**
\[
K_n(c,d)=\frac{h+\Delta_n(c,d)^2}{D_{n+1}(c)}.
\]
The exact quadratic identity, with no infinite series assumption, is
\[
E_0=h,\qquad E_{n+1}=E_n+K_n.\tag{1}
\]

### The proposed new actual-family obstruction

Assume `c,d ∈ M`, `c ≠ d`, no `X_n(c)` vanishes, and
`D_n(c)^{-1} → 0` in the complex plane. Then **some finite n** obeys
\[
\boxed{\operatorname{Re}\left(
  \frac{h+\Delta_n(c,d)^2}{h D_{n+1}(c)}
\right)<0.}\tag{2}
\]
Equivalently, the normalized nonlinear cohomological corrections cannot
remain forever in the closed right half-plane when both *actual*
critical orbits are bounded and the base derivative cocycle expands.

**Proposed proof:** (1) gives
\[
\operatorname{Re}(E_N/h)=1+
 \sum_{n<N}\operatorname{Re}(K_n/h).
\]
If every real summand were nonnegative, this real part would be at least
one for all `N`. But boundedness of both actual critical orbits and
`D_N^{-1}→0` imply `E_N/h→0`. This is a contradiction.
No uniform dependence of orbit difference on `d`, arc in a fiber,
mixed-parameter reciprocal product, or convergence of a susceptibility
series is needed.

One can retain the quantitative finite consequence: under nonnegative
summands through horizon `N`,
\[
1\leq\frac{|\Delta_N(c,d)|}{|h|\,|D_N(c)|},
\quad\text{so}\quad
|D_N(c)|\leq\frac{B_c+B_d}{|d-c|}
\]
whenever the actual critical orbits have bounds `B_c,B_d`.
This expresses a **finite cohomological phase barrier to derivative
growth** rather than an assumed metric regularity estimate.

### The required fiber/MLC implication

Let `Y` be Hausdorff locally connected, and let `q:M→Y` be a
continuous surjection with connected fibers. Fix `c∈M` with
`D_n(c)≠0` and `D_n(c)^{-1}→0`. Suppose every `d∈q^{-1}(q(c))`
different from `c` obeys
\[
\operatorname{Re}(K_n(c,d)/(d-c))\geq0
\quad\text{for every }n\geq0.\tag{3}
\]
Then the fiber of `c` is exactly `{c}` by (2). Moreover, `M` has
a relative open **connected** neighborhood basis at `c`, by the
classical monotone-quotient endpoint, with compactness proved for the
genuine quadratic bounded-orbit locus.

This is a **conditional sufficient criterion**, not a proof that (3)
holds in any new parameter fiber. The map `q` is an explicit hypothesis;
Lean does not construct the canonical pinched-disk quotient.

## Why this candidate survives this bounded classical check

1. **Standard one-orbit derivative susceptibility / transversality.**
   Tsujii, *A transversality condition for quadratic family at
   Collet–Eckmann parameter* (RIMS Kokyuroku 1042, 1998, Theorem 1):
   https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1042-11.pdf.
   This gives a limiting positive ratio of infinitesimal parameter and
   spatial derivatives in a real quadratic Collet–Eckmann setting.
   Candidate (2) is an exact finite **nonlinear** statement for two
   distinct complex parameters with bounded orbits; it neither assumes
   nor claims this infinitesimal transversality conclusion.
2. **Levin, Shen and van Strien**, *Transversality for Critical Relations
   of Families of Rational Maps: An Elementary Proof*, in *Frontiers in
   Complex Dynamics* (2019), Theorem 3.3:
   https://link.springer.com/chapter/10.1007/978-3-030-16833-9_11.
   The theorem addresses finite critical-relation Jacobians and
   invariant quadratic differentials. It does not give the
   half-plane sign reversal for the nonlinear critical-orbit
   displacement of arbitrary distinct bounded complex parameters.
3. **Rivera-Letelier**, *Rational maps with decay of geometry:
   rigidity, Thurston's algorithm and local connectivity*,
   IMS Preprint 2000/9, Proposition 1.4 and Theorem D:
   https://www.math.stonybrook.edu/preprints/ims00-09.pdf.
   Candidate (2) assumes no summability, no a priori bounds and no
   geometric decay. The only asymptotic hypothesis is
   `D_n(c)^{-1}→0`; the fiber criterion is a **sign inequality for
   finite nonlinear corrections**, not the classical
   absolute-summability criterion.
4. **Schleicher**, *On Fibers and Local Connectivity of Mandelbrot and
   Multibrot Sets*, arXiv:math/9902155, Proposition 3.5:
   https://arxiv.org/pdf/math/9902155.
   Singleton-fiber ⇒ local connectivity is classical, as is the
   existing formalized monotone quotient lemma. Neither supplies
   the new dynamical phase reversal in (2).
5. **Archive comparison**:
   `QuadraticMixedSusceptibility.lean` uses
   `P_j(c)+P_j(d)` in a two-parameter inverse product and an ordinarily
   convergent mixed series on a fiber. This candidate instead divides
   by the **one-map** derivative `D_n(c)`, retains the exact nonlinear
   square term, and derives **finite sign reversal** without any
   convergence of a susceptibility series. The previous failed
   functional criterion in closed PR #280 imposed a metric estimate on
   the `ℓ∞` orbit difference; (2) does not.

**Novelty decision:** retain *conditionally* for implementation. No
identical theorem or direct implication was located in this bounded
classical screen. The algebraic identity by itself is elementary; the
proposed contribution is its universally quantified finite reversal,
a precise no-phase-reversal obstruction to nontrivial fibers, and the
proved pointwise MLC endpoint. This is not a claim of priority over
unexamined literature and does not prove (3) for a new class.

## Strict Lean acceptance requirements

Implement `QuadraticCohomologicalCone.lean` in
`formalization/weighted/`; use the actual `QuadraticEscape.orbit`;
prove (1), (2), the fiber singleton, and an endpoint concluding the
relative connected-neighborhood basis of the actual Mandelbrot set.
No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, or new
axioms. Register the module, public theorems, packet and sources in the
existing project and have CI compile/audit them. Do not promote the
candidate if compilation or the proved MLC implication fails.

## Boundary

No infinite renormalization hypothesis is introduced; the eventual
sign condition is not known to hold on a nontrivial fiber. Neither
UPTCR, H1–H4 nor MLC is proved. This is a candidate mathematical
obstruction, not a new parameter class yet.
