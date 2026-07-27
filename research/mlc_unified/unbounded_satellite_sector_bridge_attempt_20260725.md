# Unbounded-satellite to sector-renormalization bridge: an actual closure attempt

## 1. Purpose and status

This is a new sub-research artifact. It does not modify the manuscript, its
source files, or either original PDF.

The target is the remaining unbounded-satellite part of the MLC proof. The
current public formulation separates it into pseudo-Siegel a priori bounds for
unbounded satellite quadratic-like levels and a virtual-Molecule interpolation
for mixed towers. The question tested here is whether the 2026 sector-
renormalization compactification supplies the missing bridge.

The result of this pass is mixed but concrete:

* the sector arithmetic and its parabolic compactification are proved directly
  from the current source formulas;
* this repairs the symbolic/chronological compactification layer for a
  near-neutral limit;
* the analytic transfer from an arbitrary satellite quadratic-like return to a
  neutral quadratic polynomial is not supplied by that paper and cannot be
  inferred from matching rotation numbers;
* consequently, Problem 4.3 is not closed by this bridge, and the MLC target
  remains open.

The first missing object is now typed as an analytic comparison package, not a
generic “sector marking” field.

## 2. Source boundary and notation

The primary sources checked for this pass are:

* W. R. Lim, *The combinatorics of sector renormalization*,
  arXiv:2607.11408v1, https://arxiv.org/html/2607.11408v1.
* D. Dudko, *On the MLC Conjecture and the Renormalization Theory in Complex
  Dynamics*, arXiv:2512.24171, https://arxiv.org/html/2512.24171.

Lim’s sector paper works with the neutral rotation model

    f_theta(z) = exp(2 pi i theta) z + z^2,

where theta is irrational in (-1/2,1/2). Its sector operation is a first
return operation on a radial sector for a rigid rotation, followed by the
power map that glues the sector sides. Dudko’s survey states that uniform
pseudo-Siegel bounds are known for the neutral family, but separately poses
the remaining unbounded-satellite bounds as Problem 4.3.

To avoid the overloaded letter q, this note uses:

* Q_sat for the denominator/relative period of a satellite level;
* theta for a neutral rotation number;
* Q_(n) for Lim’s sector return times.

No equality between Q_sat and Q_(n) is assumed.

## 3. Exact sector arithmetic proved from the source formulas

For theta in (-1/2,1/2) irrational, set

    epsilon(theta) = sign(theta),
    a_bar(theta) = floor(1 / |theta|).

Let theta_0 = theta and theta_n = g^n(theta), where g is the sector map.
Write epsilon_n = sign(theta_{n-1}) and a_bar_n = a_bar(theta_{n-1}). Define

    b_n = a_bar_n + (1 + epsilon_n epsilon_{n+1})/2,

and

    p_(0) = 0,       Q_(0) = 1,
    p_(1) = epsilon_1, Q_(1) = b_1,

    p_(n) = b_n p_(n-1) - epsilon_{n-1} epsilon_n p_(n-2),
    Q_(n) = b_n Q_(n-1) - epsilon_{n-1} epsilon_n Q_(n-2).

The source gives

    theta_n = -1/theta_{n-1} + epsilon_n b_n.

### Lemma 3.1 (exact closest-return identity)

For every n >= 0, with the empty sign product equal to 1,

    Q_(n) theta - p_(n)
      = (epsilon_1 epsilon_2 ... epsilon_n)
        theta_0 theta_1 ... theta_n.

In particular, if no theta_j is zero, then

    |Q_(n) theta - p_(n)| = product_{j=0}^{n-1} |theta_j|,

and each sector renormalization contracts the closest-return error by a
factor strictly smaller than 1/2.

### Proof

For n=1, the source relation at level one gives

    theta_1 = -1/theta_0 + epsilon_1 b_1,

so b_1 theta_0 - epsilon_1 = epsilon_1 theta_0 theta_1. Since
Q_(1) = b_1 and p_(1) = epsilon_1, the identity is exactly the n=1
instance. For the induction step, use

    theta_{n-1} theta_n = -1 + epsilon_n b_n theta_{n-1}

and substitute the two-term recurrence for Q_(n) and p_(n). The two terms
combine to

    Q_(n) theta - p_(n)
      = (epsilon_1 ... epsilon_n) theta_0 ... theta_n.

The absolute-value statement follows. Since |theta_j| < 1/2 by definition of
the sector domain, each factor is < 1/2. This is an exact arithmetic fact,
not a numerical estimate.

### Lemma 3.2 (parabolic symbol at an unbounded first digit)

Suppose theta_k is a sequence of irrational sector parameters with fixed sign
and a_bar(theta_k) -> infinity. Then theta_k -> 0, Q_(1)(theta_k) -> infinity,
and every convergent subsequence of the sector codes has first symbol

    (fixed sign, infinity)

in the compactified alphabet. The sector compactification therefore records
the degeneration as an explicit parabolic level rather than silently dropping
the return time.

### Proof

The definition of a_bar gives

    1/(a_bar(theta_k)+1) < |theta_k| <= 1/a_bar(theta_k),

so theta_k -> 0. Since b_1 is either a_bar_1 or a_bar_1+1,
Q_(1) -> infinity. The compactified code is the product compactification used
by Lim: a sequence of finite first digits tending to infinity converges, after
subsequence selection for the remaining digits, to the symbol infinity.

### Lemma 3.3 (explicit half-scale subsequence)

For the closest-return errors

    ell_n = |Q_(n) theta - p_(n)|,

there is a subsequence of sector levels at which ell decreases by a factor
less than 1/2. Thus the sector code retains a definite-contraction skeleton
even when individual consecutive continued-fraction levels have ratios close
to 1.

### Proof

The source’s sector bookkeeping defines the retained times t_n precisely so
that ell_{t_{n+1}} < ell_{t_n}/2. The point of this record is that the
contraction assertion belongs to the arithmetic sector system; it does not
assert geometric compactness for a satellite quadratic-like map.

## 4. What this repairs in the local proof program

The preceding lemmas close a narrow symbolic defect that had been left mixed
with the analytic virtual-scale problem:

1. the orientation sign is part of the address;
2. an unbounded first return is represented by the symbol infinity;
3. the return-time recursion remains typed at a parabolic level;
4. closest-return errors have an exact product formula; and
5. a definite-contraction subsequence is available in the rotation model.

This is enough to define a candidate sector chronology for a near-neutral
limit. It is not enough to define a holomorphic return map in the original
quadratic dynamical plane.

## 5. The attempted analytic transfer

Let R_j: U'_j -> U_j be satellite quadratic-like returns of a quadratic
polynomial, with relative period Q_sat,j -> infinity. Let alpha_j be the
marked periodic point and let lambda_j be the multiplier of the corresponding
cycle. A natural attempted transfer is:

1. choose a scale s_j from the critical-to-cycle geometry;
2. normalize by L_j(z) = alpha_j + s_j z;
3. form the normalized return

       G_j = L_j^{-1} o R_j o L_j;

4. compare G_j with the neutral model

       f_theta(z) = exp(2 pi i theta) z + z^2,

   where exp(2 pi i theta) is the limiting multiplier;
5. pull the pseudo-Siegel disks and sector returns for f_theta back through
   the comparison maps; and
6. use the resulting annular/modulus bounds to close the satellite
   parapuzzle.

The source formulas prove the arithmetic part of step 4 only after a neutral
model already exists. They do not prove that the normalized G_j converge to
that model, or even that a comparison map exists on the full region needed by
the pseudo-Siegel argument.

### Failed analytic square

To make the missing implication explicit, the required commutative diagram is

    G_j  --H_j-->  f_theta_j
     |             |
     |             |
   domains       pseudo-Siegel domains

with H_j a conformal or uniformly controlled quasiconformal comparison that
simultaneously preserves:

* the marked critical orbit;
* the access/prime-end marking;
* the return chronology Q_sat,j;
* the relevant annular moduli; and
* the parameter-dependent parapuzzle boundaries.

Matching only the multiplier is insufficient. A generic quadratic-like map
with the same multiplier has additional global return geometry, and a hybrid
straightening is not automatically conformal on the pseudo-Siegel annuli or
uniformly controlled on their boundaries. The local source data give a
quadratic-like map and a hybrid parameter, not the five-part comparison package
above.

Thus the square fails at the field

    H_j : normalized satellite return -> neutral sector model

with a domain large enough to carry the full pseudo-Siegel nest. The failure is
analytic and global; it is not repaired by adding another finite address word.

## 6. Conditional consequence, stated without promotion

The following implication is valid as a proof target:

> If every unbounded-satellite sequence admits the comparison package H_j with
> uniform distortion, critical/access preservation, and a parameter extension,
> then the neutral pseudo-Siegel bounds and the exact sector chronology can be
> transferred to the satellite sequence. Combined with the standard rigidity
> endgame, this would close that sequence’s local MLC fiber.

The antecedent is precisely the missing satellite-to-sector theorem. It is not
present in the checked sector paper, in Dudko’s survey, or in the local ledger.

The virtual near-Molecule case is strictly harder: even after a neutral bridge,
one must interpolate the primitive return with the chain of satellite copies and
construct the partially invariant virtual Julia set together with its critical
horizon and protected accesses.

## 7. Machine-checkable evidence record

The accompanying JSON certificate records the exact arithmetic checks and the
open analytic field. The validation script evaluates the recurrence and the
product identity on several irrational test parameters using high-precision
Decimal arithmetic, while treating the comparison package as intentionally
unproved. A passing numerical check is evidence for transcription accuracy;
it is not a proof of the analytic bridge.

Status labels:

* SECTOR_ARITHMETIC: proved from the source equations;
* PARABOLIC_SYMBOL: proved as a compact-symbol statement;
* SATELLITE_TO_SECTOR_ANALYTIC_COMPARISON: open;
* UNBOUNDED_SATELLITE_MLC: open;
* VIRTUAL_MOLECULE_INTERPOLATION: open;
* MLC: open.

## 8. Conclusion

This pass repairs the sector chronology and makes the exact analytic gap
smaller and more honest. It does not close Problem 4.3, Problem 4.4, or MLC.
The next mathematically meaningful target is a source-faithful theorem proving
uniform satellite-to-sector comparison on a full pseudo-Siegel nest. Until
that theorem exists, promoting the current ledger to MLC would be invalid.

Original documents remain untouched.
