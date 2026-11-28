# Attempt record: the physical-plane extremal differential

Status: conjectural route, not a proof or a contribution result.

Let the ordered physical marking be a < b < c < d, and retain the repository's
complete ParentWave and width definitions. The parent class runs from the lower
bank of (b,c) to its upper bank around the left tip a of the slit [a,d].

## Candidate exact problem

The candidate differential is

    q(z) dz^2 = dz^2 / ((z-a)(z-b)(z-c)).

The prospective critical graph is [a,b] together with [c,infinity).
Regular closed trajectories in the complementary Teichmuller ring, cut at their
single crossing of (b,c), would be actual parent leaves. If their existence,
complete period inequality, and admissibility are established, the plane
parent optimum would equal the modulus of that ring, independently of d.

Writing m=(b-a)/(c-a) and K(m)=integral from 0 to pi/2 of
(1-m*sin(t)^2)^(-1/2), the candidate value is K(1-m)/(2*K(m)).
This formula has NOT been proved here.

A floating-point diagnostic at the archived limiting critical relation gives

- kappa approximately 1.790327491999345703396901954182001708027;
- (a,b,c,d) approximately
  (-0.7903274919993457, -0.7017809543951136, -0.1182699621003675, 1);
- m approximately 0.1317544014684906;
- candidate value approximately 0.7527550636374064.

These numbers are neither an exact certificate nor a theorem. They only test
consistency with the archive's previously proved lower and upper envelopes.

## Nontrivial proof obligations

1. Construct the global elliptic coordinate or equivalent trajectory family.
   Pointwise holomorphy of q is insufficient.
2. Prove that every competing parent arc, including arbitrary continuous
   simple arcs and all allowed excursions beyond d, has at least the required
   q-length. The relative-endpoint class must enter this proof explicitly.
3. Prove existence, simplicity, bank orientation, relative homotopy and Borel
   support of the whole candidate family.
4. Identify its all-density Hausdorff-trace modulus with the dual q-area;
   a smooth-parametrized substitute alone would not match width.
5. Instantiate the theorem with ActualParentMarks and the existing exact
   physical scaling, preserving the parameter-selection boundary.

## Rejected shortcuts

- The complete logarithmic-cover quadrilateral is only an upper envelope;
  its extremal foliation has not been proved to project injectively.
- The archived O(1/log R) discarded-family estimate cannot simply be replaced
  by an exponentially small estimate for arbitrary escaping families.
- A dipole heuristic is not sufficient. The candidate differential behaves
  like z^(-3), so its area tail is naturally of order 1/R, not 1/R^2.
- An assumed extremal foliation would assume the central missing theorem.
- A proof only of the rational differential's decay would concern an
  unlinked substitute quantity and would not satisfy the selected obligation.

## Available formal infrastructure

The repository provides full Borel ParentWave transport, complete supremum
definitions, Hausdorff trace modulus, physical orbit-cut convergence, and exact
physical dilation. Its smooth ConformalChart module provides measure and
line-integral transport for already supplied injective charts. The pinned
Mathlib RiemannMapping file contains only preliminary steps; it does not supply
a complete Riemann mapping, annulus uniformization, or Strebel theorem.

No novelty or completed Lean endpoint is claimed by this attempt record.
