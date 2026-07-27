# MLC actual closure attempt - proof frontier

Date: 2026-07-25  
Status: active research; MLC is not proved by this note.  The main manuscript
and its original PDFs are read-only.  This file is a new, separate research
artifact.

## 1. Correction of objective

The objective is the theorem itself:

> The Mandelbrot set is locally connected.

The earlier sub-research PDF was an audit and a closure proposal.  It did not
prove the conjecture.  The present attempt therefore starts at the first
analytic statement that would have to be proved, rather than treating a
conditional interface as a completed theorem.

The local ledger is authoritative for the current workspace snapshot:

- 256 obligations total;
- 182 proved internally;
- 16 imported;
- 58 open;
- `MLC`, `UNIVERSAL_PROTECTED_TOWER_CLOSURE`, `H3_COERCIVITY`, and
  `H4_RIGIDITY` remain open.

The earliest global gap is not a numerical estimate.  It is the construction
of an actual dynamical-plane renormalization object for the near-molecule /
virtual-satellite regime, together with the marked data needed by the
rigidity argument.

## 2. What the current primary literature actually establishes

The 2026 Kahn-Kapiamba-Lyubich paper proves beau bounds and rigidity for
parabolically bounded families of prime primitive types.  Its introduction
also explicitly says that the general MLC problem remains open and identifies
primitive classes outside that parabolically bounded range as remaining work.
Source: <https://arxiv.org/html/2606.27272>.

Dudko's 2025/2026 survey states the same boundary in a different language:
bounded-type quadratic-like and several neutral regimes are developed, while
the remaining unbounded satellite cases and the interpolation between
positive-entropy and zero-entropy regimes still require new renormalization
tools.  Source: <https://arxiv.org/html/2512.24171>.

Therefore the current project must not import either paper as an all-parameter
MLC theorem.

## 3. Exact remaining theorem target

The next theorem to attempt is the following source-faithful statement.

### Uniform near-molecule rigidity theorem (target)

For every infinitely renormalizable quadratic polynomial whose renormalization
scales contain unbounded satellite or virtual near-molecule levels, construct
actual normalized first-return data (not a parameter-copy label) and prove:

1. **Analytic realization.**  Each selected return is a genuine quadratic-like,
   near-neutral, sectorial, or puzzle return with explicit domains,
   codomains, return time, critical orbit, and hybrid normalization.
2. **Uniform degeneration control.**  At every level, either a uniform
   quadratic-like modulus bound holds, or a source-defined pseudo-Siegel /
   sectorial replacement supplies the corresponding compactness estimate.
3. **Marked transport.**  The ideal/access marking and every protected
   postcritical segment transport through the return and through changes of
   renormalization chart.
4. **Rigidity.**  The associated parameter pieces form connected relative
   neighborhoods whose diameters tend to zero.

Items 1-3 are the missing analytic input behind the project's open virtual
carrier and response obligations.  Item 4 is the parameter conclusion needed
to invoke the Yoccoz reduction.  This target is stronger and more precise than
the prior virtual-carrier slogan because it requires an actual map at each
scale.

## 4. A rigorous two-branch proof strategy

The survey's renorm-expanding / renorm-balanced dichotomy gives the right
first split, but its universal form is itself not yet a theorem.  A complete
proof must establish the following two alternatives for every problematic
sequence of scales.

### Branch E - renorm-expanding

Prove a uniform phase-parameter estimate for the relevant puzzle or
generalized quadratic-like returns.  The required output is not merely that a
typical derivative grows.  It must include:

- an actual nested puzzle/parapuzzle construction;
- a lower bound on the expansion along all proof-relevant branches;
- a distortion estimate transferring dynamical scale to parameter scale; and
- a conclusion that the nested parameter pieces have diameter tending to zero.

If these four outputs are proved, the branch closes by the Yoccoz rigidity
criterion.  A heuristic derivative dichotomy is insufficient.

### Branch B - renorm-balanced

Construct the geometric limit of the first-return maps in a normalized chart.
Then prove the limit belongs to a controlled near-neutral, satellite, or
virtual near-molecule class and has a hyperbolic/rigid renormalization.  The
required output is:

- compactness of the normalized maps and marked surfaces;
- a uniform pseudo-Siegel, cylinder, sectorial, or ql bound;
- compatibility of the limiting marking with the finite maps; and
- a parameter-side trivial-fiber statement.

This is precisely where the existing virtual interface fails: a terminal
Hubbard tree or a finite combinatorial word does not define the limiting
analytic map, its domains, or its accesses.

## 5. First attempted lemma and its obstruction

### Lemma under test

If a sequence of problematic renormalizations admits a normalized subsequence
with a nondegenerate marked analytic limit and the corresponding parameter
pieces have uniformly bounded puzzle Teichmuller diameter, then the parameter
fiber is a singleton and the pieces shrink to the parameter.

### Status

The implication is the standard rigidity endgame and is compatible with the
local conditional reduction.  It does not supply either hypothesis.  The
current workspace has no source-checkable proof that the virtual-satellite
sequence has a nondegenerate marked limit, and no proof of bounded puzzle
Teichmuller diameter in the mixed regime.

The attempted shortcut "compact symbolic encoding implies analytic
compactness" is invalid: a symbolic limit can collapse a carrier, pinch a
prime end, lose a marking, or retain an unbounded response dimension.  This is
why `H3_COERCIVITY` and `H4_RIGIDITY` remain open in the ledger.

## 6. Concrete next proof obligation

Do not construct another abstract finite carrier.  Select one explicit
unbounded-satellite / near-molecule renormalization sequence and produce a
fully analytic certificate with these fields:

1. the actual quadratic polynomial and nested return domains;
2. all return times and critical-value images;
3. the normalized maps and hybrid coordinate changes;
4. the protected access/prime-end data;
5. the relevant modulus, extremal-width, or pseudo-Siegel estimate;
6. the parameter parapuzzle and its relative-boundary control; and
7. a failure certificate if any field cannot be constructed.

The certificate must be checked on the smallest nontrivial example before any
universal quantifier is attempted.  A successful example would be genuine
progress on the analytic interface.  A failure would identify the exact
obstruction and prevent another false promotion.

## 7. Current conclusion

This turn has not solved MLC.  It has corrected the research target from a
conditional virtual package to the actual missing theorem: uniform analytic
realization and rigidity for the remaining unbounded satellite / mixed
renormalization regimes.  The original documents remain untouched.

