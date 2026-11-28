# Candidate theorem and novelty pre-check

This statement is recorded before its Lean formalization. The initial
literature comparison has found no direct implication from the classical
results below; the exact statement's priority is not certified by a search.

## Candidate: quarter-turn rigidity of actual quadratic conjugacies

Let c,d be arbitrary complex numbers. Let h:C -> C be continuous and injective.
Assume, for every z in C,

    h(z^2+c) = h(z)^2+d,
    h(i*z) = i*h(z).

Then c=d. If c is nonzero, then h(z)=z for every z.

There is no postcritical finiteness, quasiconformality, differentiability,
normalization at infinity, or bounded-combinatorics premise.

## Proposed proof

1. The quarter-turn identity gives h(0)=0 and h(-z)=-h(z); the conjugacy at zero
   gives h(c)=d.
2. Compare the quadratic equation at z and i*z. Surjectivity of complex squaring
   then gives h(w+2c)=h(w)+2d for every w.
3. Rotate that translation law to obtain h(w+2ic)=h(w)+2id.
4. If c is nonzero, injectivity gives d nonzero. With a=d/c, the continuous
   function g(z)=h(z)-a*z has the two real-linearly independent periods 2c and
   2ic, so it is bounded on C by reduction to a compact fundamental square.
5. The exact values h(2nc)=2nd, combined with quadratic conjugacy and bounded g,
   force the coefficient d^2-dc to vanish. Since d is nonzero, d=c.
6. Now g=h-id is bounded and periodic. Evaluate quadratic conjugacy at z+2nc.
   Its term linear in n is 4nc*g(z), whereas the remaining side stays bounded.
   Thus g(z)=0.
7. For c=0, h(0)=0 and conjugacy at zero give d=0 directly. Identity of h is
   deliberately not claimed in this case: radial power maps are counterexamples.

The step to test is the conversion of one rotational compatibility into two
translation laws. The proof uses no orbit susceptibility, cross-ratio jets,
Green-density criterion, or marked-width construction.

## Intended proved MLC implication

Define the actual Mandelbrot set by boundedness of the critical orbit of z^2+c.
Let q from that set onto a Hausdorff locally connected space be a continuous
surjection with connected fibers. At a parameter c, assume every d in the
fiber q^(-1){q(c)} admits an h satisfying the two equations above.

The rigidity theorem implies d=c for every such d. The existing clean theorem
`QuadraticMonotoneFiberTopology.connected_open_basis_of_singleton_fiber`
then proves an open connected neighborhood basis in the actual Mandelbrot set
at c. The Lean theorem will prove this endpoint, not assume it as a terminal
bridge.

The map q and its properties remain explicit inputs. This is not a construction
of the canonical pinched-disk quotient. The extra rotational compatibility is
not asserted to follow from combinatorial equivalence.

## Classical pre-check

- Thurston's postcritically finite characterization and contraction theorem do
  not apply to the full stated parameter range or to this merely continuous map.
  Buff--Epstein--Koch, *Eigenvalues of the Thurston operator*, introduction and
  Theorems 1.4--1.5: <https://websites.umich.edu/kochsc/eigenvalues.pdf>.
- Connected polynomial-like straightening uniqueness requires a hybrid
  equivalence. No such analytic regularity is assumed in this candidate; it
  would need to be derived. Douady--Hubbard, *On the dynamics of polynomial-like
  mappings*, Ann. Sci. ENS 18 (1985), 287--343.
- Schleicher's fiber results supply the classical final topological implication,
  not the additional rotational rigidity statement:
  <https://arxiv.org/abs/math/9902155>.
- The first finite Thurston spectral moment is already an explicit coordinate
  for c; this candidate does not use that rejected spectral-separation route.
- Simultaneous semigroup conjugacy and local holomorphic group rigidity are
  being checked as the closest possible additional overlap. Their usual
  hypotheses (an entire semigroup, or germs fixing one common point) must not
  be silently asserted for these two maps.

## Proof and applicability boundaries

This candidate is a restricted rigidity criterion, not MLC itself.
A proof that actual unresolved combinatorial fibers admit quarter-turn-compatible
conjugacies is not supplied. No new MLC parameter class is claimed merely by
establishing the criterion.

The claim of a new contribution, if the proof compiles, is confined to this
explicit rigidity mechanism and its formally proved implication to the actual
bounded-orbit locus. Priority remains subject to specialist literature review.
