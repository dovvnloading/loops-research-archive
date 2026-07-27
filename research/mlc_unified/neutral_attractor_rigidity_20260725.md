# Neutral-attractor rigidity: source-locked correction

## What the current source adds

Willie Rush Lim's public note *The combinatorics of sector renormalization*
(arXiv:2607.11408v1, 13 July 2026) records a current neutral-renormalization
input that was absent from the earlier gap map. It says that sector
renormalizations of neutral quadratic polynomials can be chosen precompact and
can capture the critical orbit well. Its compactification retains infinite
first-return entries; these encode simple parabolic bifurcations, while the
Lavaurs--Epstein tower, top/bottom Lavaurs distinction, parabolic blow-ups, and
cyclic critical-orbit order remain part of the limiting data.

The note then states Theorem 1.1 ([DLL26]): the full renormalization attractor
for neutral quadratic polynomials is combinatorially rigid and, modulo
conformal conjugacy, is conjugate to the shift on the natural-extension
compactification. The proof summary uses uniform complex bounds for neutral
cascades and an affine conjugacy between combinatorially equivalent cascades;
the Brjuno subcase has an analytic translational-cascade model.

Source: <https://arxiv.org/html/2607.11408v1>

## Independent scope cross-check

The Stony Brook Dynamical Systems Seminar listing for 10 June 2026 describes
the same joint project as an extension of neutral-renormalization rigidity to
all irrational rotation numbers and all possible parabolic bifurcations, with
the proof based on pseudo-Siegel bounds and related rigidity ideas. This is
independent corroboration of the scope and status of the result, not an
independent proof of the manuscript theorem.

Cross-check: <https://www.math.stonybrook.edu/cal/agenda.php?LocationID=10>

## Exact import boundary

This is a substantive repair to the neutral-attractor branch. It removes the
need to leave neutral-cascade rigidity as an entirely unaddressed interface,
provided the theorem is accepted at the status reported by the source. The
source reference list identifies [DLL26] as:

> Dudko, Lim, and Lyubich, *Rigidity of the attractor of neutral quadratic
> polynomials*, 2026. Manuscript.

Therefore this audit treats the result as manuscript-backed, not as an
independently published theorem verified from its full proof. It is stronger
than the older survey-level statement of a neutral rigidity gap, but it is not
silently promoted beyond the source's scope.

## Why this does not close global MLC

The theorem concerns the neutral quadratic sector-renormalization attractor.
It does not supply the missing comparison map from every arbitrary unbounded
satellite quadratic-like return to that attractor. It also does not construct
the virtual-Molecule carrier, the critical-horizon interpolation, or the
parameter-rigidity transfer needed to turn a dynamical neutral cascade into a
global Mandelbrot local-connectivity proof. The parabolic/cylinder branch and
the satellite complement therefore remain active.

## Machine check

`validate_neutral_attractor_rigidity.py` locks the downloaded PDF hash

`68ACBB258E456A4A6F2EDF43E2E26030401251036E92662D507059DD08BEC91D`

and checks the theorem, neutral-cascade, compactification, Lavaurs, critical
orbit, and manuscript-status markers. It returns
`NEUTRAL_ATTRACTOR_RIGIDITY_SOURCE_VALID` with
`original_artifacts_written=false`.
