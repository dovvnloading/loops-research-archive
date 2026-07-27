# Elephant Eyes branch: source-audited closure contribution

## Scope

Kahn--Lyubich's *A priori bounds for some infinitely renormalizable
quadratics: IV. Elephant Eyes* treats an unbounded family not covered by a
finite-limb argument. Its hypotheses include:

* an even quadratic-like map with connected Julia set and both fixed points
  repelling;
* combinatorial rotation number (1/q);
* the Elephant Eye conditions E1--E2 on the sector and central little Julia
  set; and
* renormalization period (p=q+b), where (b) is bounded while (q) is
  unbounded.

The paper proves an a priori-bound theorem for this class using uniform
thin--thick decompositions and an amplification argument. This closes the
analytic a-priori-bound obligation for that specifically typed branch and
removes it from the undifferentiated unbounded-satellite bucket.

Source: <https://arxiv.org/html/2601.21905>

## MLC dependency boundary

Section 8 states that MLC at the corresponding parameter values follows from
the existing rigidity machinery together with the existence of little
Mandelbrot copies on Ecalle--Voronin cylinders. The cited DLP project is marked
“in preparation” in the source (with a January 2026 note that it was further
developed jointly with Alex Kapiamba). Therefore this audit imports the proved
a-priori-bound branch, but keeps the MLC consequence dependency-audited rather
than claiming a completed independent proof of the cylinder-copy input.

This is an important narrowing, not the global MLC theorem. Arbitrary
unbounded satellite towers, mixed regimes, and virtual-Molecule interpolation
remain outside the checked hypotheses.

## Machine check

`validate_elephant_eye_branch.py` locks the downloaded source hash

`5EB36430A51A3FB6A1C04DB15713AEBC86068118450893BA2042021E4A8DB725`

and checks the E1--E3 text, (p=q+b) arithmetic, the amplification theorem,
and the explicit Ecalle-cylinder/DLP dependency. It returns
`ELEPHANT_EYE_SOURCE_BRANCH_VALID` with `original_artifacts_written=false`.

