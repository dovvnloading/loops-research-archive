---
ledger: KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR
result: partial
ai: Claude Code (Anthropic), model Claude Fable 5.2 (claude-fable-5-2); proof search, checker code and exposition
human_review: none
---

# Model result: in a marked contour substitution system, interval no-periodicity is equivalent to the absence of a rigid periodic atom

Ledger statement being addressed:

> Prove the marked-interval combinatorial-growth implication used by KKL’s bounded-visits lemma: establish the exact at-most 6b+k-1 count for length-k multi-intervals meeting the critical limb, obtain correctly indexed repetition only from a strict pigeonhole excess, and prove an interval-level no-periodicity or strict-growth statement. Global Perron-Frobenius expansion lambda_F>1 alone may not be cited as excluding a periodic marked interval.

## Claim

For every marked contour substitution system (the finite combinatorial model defined in step 1:
`M >= 2` atoms on a circle, each atom mapped onto a nonempty run of atoms, whole runs possibly
inserted at marked points, any degree), a nonempty proper open interval is periodic if and only
if some single atom is periodic with a one-atom image at every step (a *rigid cycle*); when there
is no rigid cycle, every constant-length stretch of an orbit is an injective run of rigid
intervals, which gives the strict-growth statement and the critical-visit counts of the ledger
row in this model, with a count independent of `k` as soon as the critical limb contains one
non-rigid atom; this is a theorem about the model only, and neither the identification of the
native KKL operation `f_* iota^*` with such a system nor the absence of rigid cycles there is
proved.

## Evidence

Everything below is elementary and self-contained. The earlier archive note
[`research/independent_audits/interval_growth_repair_20261106.md`](../../research/independent_audits/interval_growth_repair_20261106.md)
(called *the audit* below) already proved, for an abstract operation assumed to have no proper
periodic interval, the exact count `min(M, r+k-1)`, the corrected pigeonhole and a chain bound,
and gave one sufficient package (edge weights plus vertex gates) for no-periodicity. What is new
here is the exact, necessary and sufficient, atom-level form of the no-periodicity clause
(Theorem 1), the normal form of a constant-length stretch (Theorem 2), the resulting counts
(Corollary 3, Lemma 4, Corollary 5) and the exact statement of what an incidence matrix can and
cannot exclude (Proposition 6).

### 1. The model

A **marked contour substitution system** of degree `d >= 1` consists of:

- a circle cut by `M >= 2` marked points `p_0, ..., p_{M-1}` into open **atoms** `0, ..., M-1`
  (indices modulo `M`), atom `i` lying between `p_i` and `p_{i+1}`;
- integers `a_i >= 1` (the number of target atoms covered by atom `i`) and `c_i >= 0` (the
  number of target atoms inserted at the marked point `p_i`), with
  `sum_i a_i + sum_i c_i = d M`;
- a target atom `tau(0)`; put `tau(i+1) = tau(i) + a_i + c_{i+1}` modulo `M`. The sum condition
  makes this consistent around the circle.

So the image of atom `i` is the run of `a_i` consecutive atoms starting at `tau(i)`, and between
the images of atoms `i-1` and `i` sit the `c_i` atoms inserted at `p_i`. A **proper state** is a
pair `(s, k)` with `1 <= k <= M`: the open interval consisting of atoms `s, ..., s+k-1` and the
`k-1` marked points between them. For `k = M` it is the circle punctured at `p_s`, and the `M`
punctured circles are different states. The **length** is `ell(s, k) = k`. Write `C` for the whole
circle. For a proper state put

    Lam(s, k) = a_s + ... + a_{s+k-1}  +  c_{s+1} + ... + c_{s+k-1}

(the insertions at the two end points `p_s`, `p_{s+k}` are not counted: the interval is open).
The operation is

    Phi(s, k) = (tau(s), Lam(s, k))   if Lam(s, k) <= M,
    Phi(s, k) = C                     if Lam(s, k) >  M,        Phi(C) = C.

`Phi` is inclusion-monotone (the image of a sub-run is a sub-run of the image), `C` is
absorbing, and a proper image never has smaller length (Lemma 1). The model is my formalization
of what the audit's section 5 describes for a saturated ribbon contour: an orientation-preserving
boundary covering under which source atoms refine into full target-atom lifts (`a_i >= 1`), with
the complete contour of every branch attached in the interior of an interval inserted (`c_i`, or
a larger `a_i` when the branch is attached inside an atom). That the audit's systems are
instances rests on its description (its Lemma 5.1) and is not re-proved here.

An atom `i` is **rigid** if `a_i = 1`. On rigid atoms put `sigma(i) = tau(i)`; then
`Phi(i, 1) = (sigma(i), 1)`. A **rigid cycle** is a rigid atom `i` with `sigma^q(i) = i` for some
`q >= 1`, all of `i, sigma(i), ..., sigma^{q-1}(i)` being rigid. A proper state is a **rigid
interval** if `Lam(s, k) = k`. A state `I` is **periodic** if `Phi^q(I) = I` for some `q >= 1`.

### 2. Lemma 1 (length defect)

For a proper state, `Lam(s, k) - k = sum over its atoms of (a_i - 1) + sum over its interior
marked points of c_i >= 0`. Hence `Lam(s, k) >= k`, with equality exactly when every atom of the
interval is rigid and nothing is inserted at an interior marked point. In that case
`Phi(s, k) = (sigma(s), k)` and atom `s + j` is sent to atom `sigma(s) + j` for `0 <= j < k`.

*Proof.* The formula is the definition of `Lam` with `k` subtracted, and every term is
nonnegative. If all terms vanish then `tau(s + j + 1) = tau(s + j) + 1` for `0 <= j < k - 1`. ∎

### 3. Theorem 1 (exact atom-level criterion)

For a marked contour substitution system the following are equivalent:

1. some nonempty proper interval is periodic;
2. some single atom, as a length-one interval, is periodic;
3. there is a rigid cycle.

Moreover a proper state `(s, k)` is periodic if and only if `s` lies on a rigid cycle and every
state `(sigma^m(s), k)`, `m >= 0`, is a rigid interval; then all `k` atoms of the interval lie
on rigid cycles.

*Proof.* (3 ⇒ 2) If `s` lies on a rigid cycle of period `q` then `Phi^m(s, 1) = (sigma^m(s), 1)`
for all `m`, a proper state because `M >= 2`, and `Phi^q(s, 1) = (s, 1)`. (2 ⇒ 1) is trivial.
(1 ⇒ 3) Let `I_m = Phi^m(I)` with `I_0 = I = (s, k)` proper and `I_q = I_0`. Since `C` is
absorbing, every `I_m` is proper. By Lemma 1 the lengths are nondecreasing in `m`; they return to
`k` at time `q` and the sequence is periodic, so all lengths equal `k`. By the equality case of
Lemma 1 every `I_m` is a rigid interval and `I_{m+1} = (sigma(s_m), k)` where `s_m` is the first
atom of `I_m`. Two proper states are equal only if they have the same first atom and length, so
`sigma^q(s) = s` with `s, sigma(s), ...` rigid: a rigid cycle. The same argument applied to atom
`s + j`, using the last sentence of Lemma 1, puts every atom of `I` on a rigid cycle. Conversely,
if `s` is on a rigid cycle of period `q` and all `(sigma^m(s), k)` are rigid intervals, Lemma 1
gives `Phi^m(s, k) = (sigma^m(s), k)` and so `Phi^q(s, k) = (s, k)`. ∎

So the interval-level no-periodicity clause of the ledger row is, in this model, **equivalent**
to a statement about single atoms: no atom returns to itself through one-atom images. The
audit's negative control (`0 -> (0)`, `1 -> (1,2)`, `2 -> (0,1,2)`) is the system `a = (1,2,3)`,
`c = 0`, `tau(0) = 0`; its rigid cycle is the fixed atom `0`.

### 4. Theorem 2 (normal form of a constant-length stretch)

Let `I = (s, k)` be proper and `n >= 1`, and suppose `Phi^n(I)` is proper of length `k`. Then:

1. for `0 <= m < n`, `Phi^m(I) = (sigma^m(s), k)` is a rigid interval; in particular
   `s, sigma(s), ..., sigma^{n-1}(s)` are rigid atoms;
2. if the system has no rigid cycle, the `n + 1` states `Phi^0(I), ..., Phi^n(I)` are pairwise
   distinct, and so are their first atoms.

*Proof.* (1) All `Phi^m(I)`, `m <= n`, are proper and by Lemma 1 have length exactly `k`; apply
the equality case of Lemma 1 to each `m < n`. (2) The first atoms are `s_m = sigma^m(s)` for
`m <= n`, with `s_0, ..., s_{n-1}` rigid. If `s_i = s_j` with `i < j <= n` then
`sigma^{j-i}(s_i) = s_i` through rigid atoms, a rigid cycle. ∎

### 5. Corollary 3 (strict growth, two forms)

Assume there is no rigid cycle. Let `h` be the largest number of rigid atoms in a chain
`i, sigma(i), sigma^2(i), ...` (so `h` is at most the number of rigid atoms), and for a run `L`
of `r` consecutive atoms, `1 <= r < M`, let `g_k(L)` be the number of rigid intervals of length
`k` meeting `L`. Let `I` be a proper state of length `k`.

(a) If `n > h`, then `Phi^n(I) = C` or `ell(Phi^n(I)) > ell(I)`. The bound is attained by a
length-one interval at the start of a longest chain.

(b) If more than `E_k(L) = min(M, r + k - 1, g_k(L) + 1)` distinct times `0 <= m <= n` satisfy
`Phi^m(I) ∩ L ≠ ∅`, then `Phi^n(I) = C` or `ell(Phi^n(I)) > ell(I)`.

*Proof.* If the conclusion fails, `Phi^n(I)` is proper of length `k` and Theorem 2 applies.
(a) `s, ..., sigma^{n-1}(s)` are `n` distinct rigid atoms forming a chain, so `n <= h`.
(b) The states at the encounter times are pairwise distinct proper states of length `k` meeting
`L`. A length-`k` state meets `L = {0, ..., r-1}` exactly when its first atom is congruent to one
of the `r + k - 1` integers `-(k-1), ..., r-1`, so there are at most `min(M, r + k - 1)` of them
(this is the audit's Lemma 4.1). All of them except possibly the one at time `n` are rigid
intervals, so there are also at most `g_k(L) + 1`. ∎

The repeated states that a pigeonhole excess would produce are indexed by the actual times `m`,
as the ledger row requires; here no repetition occurs at all, by Theorem 2(2). With `r <= 6b`,
form (b) contains the audit's Theorem 4.2: `6b + k` critical encounters force growth or
saturation.

### 6. Lemma 4 (rigid intervals meeting a limb with a non-rigid atom)

Let `R` be any set of atoms, `L` a run of `r < M` consecutive atoms, and suppose `z >= 1` atoms
of `L` are not in `R`. Then for every `1 <= k <= M` at most `r - z` length-`k` intervals consist
of atoms of `R` and meet `L`. In particular `g_k(L) <= r - z`, for every `k`.

*Proof.* Label `L = {0, ..., r-1}` and let `n_1` be the first atom of `L` not in `R`. Call an
interval *good* if its atoms are in `R` and it meets `L`. A good interval does not contain `n_1`,
so `k < M`. Send a good interval to its last atom if that atom lies in `{0, ..., n_1 - 1}`, and to
its first atom otherwise. For a fixed `k` an interval is determined by its last atom and also by
its first atom, so the map is injective on each of the two classes. In the second class the
interval has no atom in `{0, ..., n_1 - 1}`: an atom `u < n_1` of the interval would force the
interval, which avoids `n_1`, to end in `{u, ..., n_1 - 1}`. Its first atom is then in `L`,
because an interval that starts outside `L` and meets `L` contains atom `0`, which is `n_1` or
lies in `{0, ..., n_1 - 1}`; so the first atom lies in `L ∩ R` after `n_1`. The first class has values in `{0, ..., n_1 - 1}`, all in `R`.
The two value sets are disjoint subsets of `L ∩ R`, which has `r - z` elements. ∎

Consequently, if there is no rigid cycle and the limb `L` contains a non-rigid atom, then
`E_k(L) <= r - z + 1 <= r` for **every** `k`: the dependence on the length `k` in the count
`r + k - 1` disappears.

### 7. Corollary 5 (variable-time enlargement chains)

Assume there is no rigid cycle. Let `J_1, ..., J_t` be proper states, each meeting `L`, each of
length at most `K`, with `Phi^{m_j}(J_j) ⊂ J_{j+1}` for some `m_j >= 1`. Then

    t  <=  E_1(L) + ... + E_K(L).

*Proof.* `Phi^{m_j}(J_j)` is proper because it lies in a proper state, so by Lemma 1 the lengths
`ell(J_j)` are nondecreasing. Where `ell(J_j) = ell(J_{j+1}) = k`, the image `Phi^{m_j}(J_j)` is a
proper state of length at least `k` inside a proper state of length `k`, hence equal to it (for
`k = M` two punctured circles are nested only if equal). So the `J_j` of length `k` form a
subsequence of one constant-length orbit stretch, and Corollary 3(b) bounds their number by
`E_k(L)`. ∎

With `r <= 6b` and `K = 12b - 1` (the limb-length and shortness bounds the audit takes from KKL)
this gives `t <= (12b-1)^2` in general, which is the audit's (7.3), and
`t <= (12b-1) * 6b = 72b^2 - 6b` when the limb contains a non-rigid atom. Both are below the
source constant `216 b^2`.

### 8. Proposition 6 (what an incidence matrix can and cannot exclude)

Suppose some atoms (the *edge-side* atoms) carry labels `e(i)` in a finite set `E`, and `A` is a
nonnegative integer `E × E` matrix with no zero row such that the image run of every edge-side
atom `i` contains, for each `e'`, at least `A[e(i), e']` edge-side atoms labelled `e'`. Then:

1. if an edge-side atom `i` is rigid, row `e(i)` of `A` is the unit vector at `e(sigma(i))`, and
   `sigma(i)` is edge-side; so a rigid cycle through an edge-side atom gives a cycle
   `e_0 -> e_1 -> ... -> e_0` in `E` along which every row of `A` is a unit vector;
2. no rigid cycle passes through an edge-side atom if there are a positive vector `w` and
   `lambda > 1` with `A w >= lambda w` (the audit's hypothesis), or if `A` is irreducible and not
   a permutation matrix;
3. the spectral radius of `A` being greater than one does not exclude a rigid cycle through an
   edge-side atom, and no hypothesis on `A` says anything about a rigid cycle through unlabelled
   atoms.

*Proof.* (1) The image of `i` is one atom and must contain at least `sum_{e'} A[e(i), e'] >= 1`
edge-side atoms. (2) Along the cycle `w_{e_{j+1}} = (A w)_{e_j} >= lambda w_{e_j}`, so
`w_{e_0} >= lambda^q w_{e_0}`, impossible. In the irreducible case the cycle is a set of indices
closed under `A`, hence all of `E`; then every row is a unit vector and an irreducible matrix
with unit rows is a permutation matrix. (3) Take `M = 4`, atoms `(x+, x-, y+, y-)`, `a = (1,1,3,3)`,
`c = 0`, `tau(0) = 0`, degree two. The words are `x+ -> (x+)`, `x- -> (x-)`,
`y+ -> (y+, y-, x+)`, `y- -> (x-, y+, y-)`, so `A = [[1,0],[1,2]]` in the basis `(x, y)`: spectral
radius `2`, reducible, and both sides of `x` are rigid fixed atoms. For unlabelled atoms the
audit's negative control applies. ∎

This is an abstract countermodel, not a Hubbard tree. It makes the last sentence of the ledger
row concrete in the model: the matrix excludes periodic edge-side atoms through the absence of
a cycle of unit rows, which `lambda_F > 1` alone does not give, and it never excludes a periodic
atom that is not an edge side (a vertex sector).

### 9. What this changes in the remaining native test

The audit's section 8 lists what must be verified for the actual KKL operation. By Theorem 1,
its items 1 and 2 (multiplicity-faithful edge weights, vertex gates) are needed only through the
following pair; given N1, condition N2 is necessary and sufficient for interval no-periodicity:

- **N1.** On the marked intervals used by the bounded-visits lemma, the native operation is a
  marked contour substitution system: every atom is sent onto a nonempty run of atoms, images of
  adjacent atoms are adjacent up to an inserted run at the common marked point, and nothing is
  inserted at the end points of an open interval.
- **N2.** No single native atom (edge side or vertex sector) is periodic through one-atom images.

Neither is proved here.

### 10. Exact finite certificate

    python contributions/rigid_atom_criterion_20261126/check_rigid_atom_criterion.py

Standard library only, integer arithmetic, about 20 seconds. It enumerates **all** 112,997
systems with degree 1 and `M <= 7`, degree 2 and `M <= 6`, degree 3 and `M <= 4`, simulates `Phi`
directly on every proper state, and asserts on each system: Lemma 1 and inclusion-monotonicity;
Theorem 1, including equality of the set of periodic proper states with the predicted set;
Theorem 2 and the sharpness of `h` in Corollary 3(a); the bound of Corollary 3(b) for every limb
length `r` and every orbit stretch; Corollary 5 by a longest-path computation in the chain graph
(`M <= 4`). It also checks Lemma 4 for every set `R` with `M <= 10`, the three named examples
(audit negative control, the matrix example of Proposition 6, an end-point insertion), and the
arithmetic identities of step 7 for `1 <= b <= 1000`. The script compares the theorems with data
it computes independently of them; it certifies those finite instances, and the statements for
all sizes rest on the written proofs above. Lean is not installed on the machine used and no Lean
file is part of this contribution.

## Dependencies

- Ledger: `KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR` (addressed, stays open);
  `KKL_WAVE_ATOMIC_SOURCE_OCCURRENCE_MANIFEST` (its closed prerequisite; not used in the proofs).
- In-archive: `research/independent_audits/interval_growth_repair_20261106.md`, for the
  description of saturated ribbon contours that the model abstracts (its section 5), the count
  `min(M, r+k-1)` (its Lemma 4.1, reproved in one line in Corollary 3), and the constants
  `r <= 6b`, `K = 12b - 1` which it takes from the source.
- Outside theorems used in the proofs: none. The model theorems are self-contained.
- Source of the operation being modelled, not used as a premise: J. Kahn, A. Kapiamba,
  M. Lyubich, *MLC for parabolically bounded primitive renormalization*, arXiv:2606.27272v1,
  Proposition 6.9 and Lemma 6.4 with Appendix A.1, as located by the archive's
  `research/mlc_unified/direct_decoration_wave_proof_use_ledger.md` section 3.2. I did not
  re-read the source; every statement about it here is taken from those two archive files.

## Boundary

- **Model only.** Nothing here is proved about the actual KKL prime-end operation
  `Phi = f_* iota^*`. The identification N1 of the native operation with a marked contour
  substitution system is open, in particular in the non-locally-connected case, and so is N2.
  Until both are proved the ledger row stays **open**; no status change is proposed.
- The hypothesis `z >= 1` of the `k`-independent count (the critical limb contains a non-rigid
  atom) is not verified for the native contour. Without it only the count `r + k - 1` is
  available.
- The time bound `h` of Corollary 3(a) is not uniform in `b`: nothing bounds the number of rigid
  atoms of a native contour in terms of `b`. Only the critical-visit forms (Corollary 3(b),
  Corollary 5) are of the `b`-uniform kind the bounded-visits lemma needs.
- Closed crests, end-point births, the passage from wave crests to chains of intervals, and the
  proof that actual crests are proper, short and nested are not addressed; the audit's section 7
  discussion of them is not re-proved or extended.
- Proposition 6 assumes the stated dictionary between edge-side atoms and matrix entries. That
  dictionary is not proved for the native Hubbard-tree incidence operator, and irreducibility of
  that operator is not claimed.
- The finite certificate covers the listed sizes only. No sharpness is claimed for the chain
  bounds. No Lean formalization. No human review.
- This does not prove the Wave amplification theorem, any of H1 to H4, UPTCR or MLC.

## Attribution

The interval dynamics, the native tree, the bounded-visits lemma and the constants `6b`, `12b`,
`216 b^2` belong to Kahn, Kapiamba and Lyubich (arXiv:2606.27272v1) and the predecessors they
cite. The saturated-contour description, the count `min(M, r+k-1)`, the growth-or-saturation
formulation, the chain argument and the three-atom negative control are from the archive note
`research/independent_audits/interval_growth_repair_20261106.md`; the source-gap analysis is from
`research/mlc_unified/direct_decoration_wave_proof_use_ledger.md`. This contribution adds the
explicit model with marked-point insertions, the rigid-atom equivalence, the constant-length
normal form, Lemma 4 and its `k`-independent counts, and Proposition 6 with its example. The
arguments are elementary; no novelty beyond this archive is claimed.
