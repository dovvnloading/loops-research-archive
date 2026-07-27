# Gate N1 — independent red-team of the Borel width envelope

## 0. Frozen target and verdict

This audit concerns

```text
kkl_stationary_n1_borel_width_envelope_20260726.md
```

at the pre-audit SHA-256

```text
03E4BF26BB2F2FBD13A59083EF421AC433A7938ADEB621BEACE32340DA697A4A.
```

The target note was not edited during this audit.

**Verdict.**  The width-envelope mechanism is mathematically valid and
removes the descriptive-set need for a chartwise interpretation of
DL's phrase “outermost curves,” provided the proof-internal relative
discard bound

\[
 \mathcal W(D_{\rm DL})\leq C_{\rm DL}
\tag{0.1}
\]

is retained as a separate analytic input.  Two local proof details
should be repaired before promotion:

1. avoid the undefined extended-real expression
   \((\infty-\infty)_+\) in Lemma 2.1; and
2. spell out the standard local argument that weighted length for a
   continuous positive conformal density is lower semicontinuous in
   the compact-open path topology.

Neither repair changes the theorem.

This audit proves no part of Gate N2, VAAPC-I, UPTCR, rigidity,
parameter-fiber shrinking, or MLC.

## 1. Logical form of the replacement

Let \(S\) have a standard-Borel leaf space \(L_S\) and an injective
jointly Borel evaluation by proper embedded paths.  Suppose an analytic
argument supplies an arbitrary, possibly non-Borel, discard
\(D\subset L_S\) such that:

\[
 \mathcal W(D)\leq C,
\qquad
 p\text{ is injective on }S\setminus D.
\tag{1.1}
\]

The proposed construction chooses a near-minimizing admissible density
\(\rho\) for \(D\), replaces it pointwise by a lower-semicontinuous
density \(\sigma\geq\rho\) with almost the same area, and defines

\[
 E_\sigma
 :=
 \{\ell\in L_S:
   \operatorname{Len}_\sigma(e_S(\ell,\cdot))\geq1\}.
\tag{1.2}
\]

Then:

1. \(D\subset E_\sigma\), by pointwise domination;
2. \(E_\sigma\) is Borel, by lower semicontinuity of weighted length;
3. \(\mathcal W(E_\sigma)\leq\operatorname{Area}(\sigma)
   \leq C+\varepsilon\);
4. \(S\setminus E_\sigma\subset S\setminus D\), so \(p\) remains
   injective; and
5. both the retained and discarded geometric unions are Borel by
   Lusin--Souslin.

The direction of containment in item 4 is essential.  The construction
does not attempt to find a Borel subset of \(D\).  It finds a Borel
**superset** of \(D\), so that the new retained family is a hereditary
subfamily of the analytic DL retained family.

## 2. Pointwise Vitali--Carathéodory step

### 2.1 Why almost-everywhere domination is insufficient

If \(\sigma\geq\rho\) only with respect to area almost everywhere, a
curve can be contained in the exceptional area-zero set.  Its
\(\rho\)-length can be positive while its \(\sigma\)-length is zero.
Thus the pointwise correction in the target note is necessary.

### 2.2 Verification of the correction

Let \(v\) be a nonnegative lower-semicontinuous majorant of \(h\)
almost everywhere with the required integral bound.  Put

\[
 N=\{h>v\}.
\]

Define the discrepancy without subtracting two infinite numbers:

\[
 a(x)=
 \begin{cases}
   h(x)-v(x),&x\in N,\\
   0,&x\notin N.
 \end{cases}
\tag{2.1}
\]

On \(N\), \(v(x)<h(x)\), so the extended difference in (2.1) is
well-defined in \((0,\infty]\).  In particular, the case
\(h(x)=v(x)=\infty\) lies outside \(N\).

For

\[
 N_k=\{x\in N:a(x)>2^k\},\qquad k\in\mathbb Z,
\]

choose open \(U_k\supset N_k\) with

\[
 2^{k+1}A_0(U_k)<b_k,\qquad
 \sum_{k\in\mathbb Z}b_k<\eta/2.
\]

This is valid even on a noncompact surface: \(A_0\) is a
sigma-finite Radon measure on a second-countable locally compact
space, and every measurable null set has open supersets of arbitrarily
small total measure.

The function

\[
 w=\sum_{k\in\mathbb Z}2^{k+1}\mathbf1_{U_k}
\]

is lower semicontinuous because indicators of open sets are lower
semicontinuous and the sum is the increasing supremum of finite
partial sums.  If \(2^m<a(x)\leq2^{m+1}\), then

\[
 w(x)\geq
 \sum_{k=-\infty}^{m}2^{k+1}
 =2^{m+2}>a(x).
\]

If \(a(x)=\infty\), the same sum diverges.  Tonelli gives

\[
 \int w\,dA_0
 \leq
 \sum_k2^{k+1}A_0(U_k)
 <\eta/2.
\]

Thus \(g=v+w\) is a pointwise lower-semicontinuous majorant with the
claimed integral.  This independently verifies Lemma 2.1 after the
minor definition (2.1).

The subsequent regularization

\[
 \sigma=\sqrt{g+\eta q^2},
\qquad q>0,\quad q\in C(V)\cap L^2(V),
\]

is valid.  A positive continuous \(L^2\) function exists on every
sigma-compact smooth surface by a compact exhaustion and a locally
finite partition of unity with rapidly decreasing coefficients.
Strict positivity is useful only in the nonrectifiable-path branch.

## 3. Lower semicontinuity of weighted length

### 3.1 Compact subpaths

Let \(\tau:V\to(0,\infty)\) be continuous.  For a compact parameter
interval \(I\), the functional

\[
 \gamma\longmapsto
 \int_{\gamma|I}\tau\,ds_0
\tag{3.1}
\]

is lower semicontinuous under uniform convergence.

One rigorous local proof is as follows.  Fix a path \(\gamma\) and a
number strictly below the right side of (3.1).  Choose a finite
partition of \(I\) fine enough that every corresponding image segment
lies in a relatively compact coordinate disk on which \(\tau\) varies
by less than a prescribed error.  In each disk, ordinary Riemannian
length is the supremum of finite sums of local distances and is lower
semicontinuous under uniform convergence.  Multiplying the local lower
bounds by the infimum of \(\tau\) on the disk and summing gives the
desired lower bound for all sufficiently close paths.  Letting the
partition and the oscillation error tend to zero proves (3.1).

Equivalently, the continuous positive density defines a local length
metric with the same topology.  The length of a path in a length
metric is the supremum of its finite partition sums.  The word
“local” is useful here: it avoids any unproved completeness or
global lower bound for \(\tau\) on a noncompact surface.

### 3.2 Lower-semicontinuous densities

For the strictly positive lower-semicontinuous \(\sigma\), choose
continuous functions

\[
 0<\sigma_j\uparrow\sigma.
\]

The construction in the target note,

\[
 \sigma_j=
 \max\{f_j,\sqrt\eta(1-1/j)q\},
\]

is increasing, continuous, positive, and bounded above by \(\sigma\).

If a compact subpath is rectifiable, monotone convergence with respect
to its arclength measure gives

\[
 \operatorname{Len}_\sigma(\gamma)
 =
 \sup_j\operatorname{Len}_{\sigma_j}(\gamma).
\tag{3.2}
\]

If it is nonrectifiable, the compact image has a positive minimum of
the continuous function \(\sigma_2\); hence its
\(\sigma_2\)-length, and both sides of (3.2), are infinite.  Therefore
(3.2) holds for every compact subpath.  A supremum of
lower-semicontinuous functions is lower semicontinuous.

For a proper path on \((0,1)\), total length is

\[
 \sup_{m\geq3}
 \operatorname{Len}_\sigma
 \left(\gamma|_{[1/m,\,1-1/m]}\right).
\tag{3.3}
\]

The countable supremum remains lower semicontinuous in the
compact-open topology.  No prime-end value of \(\sigma\) is required.
This verifies the target note's proper-tail and nonrectifiable cases.

### 3.3 Reparameterization and the Borel leaf map

Metric length is invariant under orientation-preserving or
orientation-reversing homeomorphic reparameterization.  It therefore
descends to the KKL/KL path convention.

If \(e_S\) is jointly Borel with continuous path fibers, then

\[
 \ell\longmapsto e_S(\ell,\cdot)
\]

is Borel into \(C((0,1),V)\).  The compact-open Borel sigma-algebra is
generated by evaluations at a countable dense set of times.  Hence the
preimage of

\[
 \{\gamma:\operatorname{Len}_\sigma(\gamma)\geq1\}
 =
 \bigcap_{n\geq2}
 \{\gamma:\operatorname{Len}_\sigma(\gamma)>1-1/n\}
\]

is Borel.

## 4. Extremal-width and source audit

KL06 `appendix.tex` 17--36 defines extremal width of an arbitrary path
family as the infimum of the areas of densities assigning length at
least one to every path.  Consequently, from
\(\mathcal W(D)\leq C\) one may choose \(\rho\) with

\[
 \operatorname{Len}_\rho(\gamma)\geq1
 \quad(\gamma\in D),
\qquad
 \int\rho^2\,dA_0<C+\delta.
\]

Neither measurability of \(D\) nor a selection from \(D\) enters this
definition.  Since \(\sigma\geq\rho\) pointwise, \(D\subset E_\sigma\).
Since \(\sigma\) is admissible for all of \(E_\sigma\),

\[
 \mathcal W(E_\sigma)\leq\int\sigma^2\,dA_0.
\]

This part of the argument is exact.

The envelope theorem does **not** derive (0.1) from DL's displayed
aggregate inequality

\[
 \mathcal W(S_{\rm DL}^\sharp)
\geq
\mathcal W(S)-O(\log2).
\]

That inference would be invalid without additional structure.
The required relative estimate is proof-internal:

1. DL 2830--2838 gives \(T=O(\log2)=O(1)\) discarded deck-span
   packets;
2. DL 2839, together with the unit-buffer charge and Shift Argument,
   bounds every nonzero-span packet by an absolute constant;
3. DL 2841 deletes one additional bounded outer buffer; and
4. the Parallel Law gives the width bound for the union of the
   discarded packets.

This is exactly the analytic input already isolated as Lemma 2.3,
equation (2.5), in
`kkl_stationary_relative_wave_continuation.md`.  If that proof-internal
relative estimate is not accepted, the Borel envelope cannot repair
it.  The envelope resolves only the measurable type of the retained
family, not the DL analytic pruning lemma.

## 5. Application and inheritance audit

Let

\[
 D_{\rm DL}=S\setminus S_{\rm DL}^\sharp
\]

be the actual set-theoretic DL discard.  Apply the envelope theorem to
obtain \(E_{\rm DL}\supset D_{\rm DL}\), and set

\[
 S_{\rm Bor}^\sharp=S\setminus E_{\rm DL}.
\]

Then

\[
 S_{\rm Bor}^\sharp\subset S_{\rm DL}^\sharp.
\]

Every property needed later in Gate N1 is hereditary under this
restriction:

1. point-set injectivity of the degree-two covering;
2. being a sublamination subordinate to the same Wave base;
3. individual direction above the same connected crest interval;
4. properness of every leaf;
5. one-step or residual finite-horizon unbreakability;
6. the relative-cover inequality, by monotonicity and inclusion in
   the full pullback; and
7. the standard-Borel ordered presentation, because a Borel leaf
   subset inherits the source code, evaluation, endpoints, and order.

The image geometric union is Borel: the map on the parameterized
retained union is Borel and injective, so Lusin--Souslin applies.  The
image is a Wave or is empty.  No maximality is used.

The discarded family in the revised N1 construction is
\(E_{\rm DL}\cap S=E_{\rm DL}\), whose width is at most
\(C_{\rm DL}+\varepsilon\).  Thus the analytic constant changes by an
arbitrarily small absolute amount.  There is no factor equal to the
number of arc charts.

## 6. Consequence for the former order-ideal obstruction

The width-envelope theorem bypasses rather than proves

```text
DL_BUFFER_CHARTWISE_ORDER_IDEAL.
```

That chartwise statement remains unsupported by the locked wording of
DL 2827 and 2841, but it is no longer required for the corrected N1
existence theorem.  The live BOWR proof should not continue to claim
that every DL outer deletion is a chartwise initial/terminal interval.
Instead, it should:

1. import the proof-internal set-theoretic DL retained family and its
   relative discard bound;
2. apply the Borel width envelope once to the entire discard;
3. use the smaller Borel retained family in the stationary induction;
   and
4. replace the old transverse-width/ordered-buffer interface by the
   width-envelope clause.

This change also eliminates the need to make each individual dyadic
deck-span discard Borel.  Their only remaining role is analytic: they
prove the single relative bound (0.1).

## 7. Exact status

Subject to the two local traceability repairs in Section 0:

| obligation | status after this red-team |
|---|---|
| pointwise lower-semicontinuous density majorant | proved |
| Borel weighted-length threshold on proper paths | proved |
| Borel bounded-width superfamily | proved |
| Borel degree-two retained DL subwave | proved, conditional only on the already isolated analytic relative discard bound |
| `DL_BUFFER_CHARTWISE_ORDER_IDEAL` | unnecessary for corrected N1 |
| integration into live BOWR/N1 | not yet done |
| `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` | open pending integration |
| `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` | open pending integration and backward audit |
| N2, VAAPC-I, UPTCR, MLC | open |

## 8. Final repaired-hash disposition

The target author incorporated:

1. the extended-real discrepancy repair from Section 2;
2. the local weighted-length proof from Section 3; and
3. compactly-contained coordinate disks and a Lebesgue-number margin
   ensuring that uniformly close comparison paths remain in the same
   larger charts.

The resulting target was frozen and re-audited at SHA-256

```text
1B609ACFC44AC0F1D112AB698FC5A5C24E4BFB8D604552AD124285C1757D5805.
```

**Final theorem-internal disposition: pass.**  No further internal
obstruction was found.  The only external analytic premise is the
proof-internal DL relative bound
\(\mathcal W(D_{\rm DL})\leq C_{\rm DL}\), which the repaired target
states separately and does not infer from DL's aggregate displayed
retained-width inequality.

This pass proves `BOREL_WIDTH_ENVELOPE_PRUNING` once that analytic
premise and the supplied standard-Borel source-Wave presentation are
in force.  It does not, by itself, promote the unintegrated BOWR or N1
ledger entries.

## 9. Source-checkable final-snapshot addendum

The target was revised once more and frozen at SHA-256

```text
9F2ABD1E8DDD0E0E1B4FFC3B55B8DAF3BA64B4BCBE4E9562454A850E5E8422BE.
```

The changes from the previously audited `1B609...` snapshot are:

1. the retained-width consequence (1.5);
2. the named analytic interface
   `DL_RELATIVE_DISCARD_FAMILY_BOUND`; and
3. corrected target-Wave typing in the degree-two application.

### 9.1 Retained-width consequence

The new conclusion is

\[
 \mathcal W(S_\varepsilon^\sharp)
 \geq
 \mathcal W(S)-C-\varepsilon.
\tag{9.1}
\]

It follows from the KL06 Parallel Law without an additivity
assumption:

\[
 \mathcal W(S)
 =
 \mathcal W\!\left(
   S_\varepsilon^\sharp
   \cup
   (S\setminus S_\varepsilon^\sharp)
 \right)
 \leq
 \mathcal W(S_\varepsilon^\sharp)
 +
 \mathcal W(S\setminus S_\varepsilon^\sharp).
\]

Using the already proved discard bound and rearranging gives (9.1).
The conclusion remains valid when its right side is nonpositive.

### 9.2 Named relative-discard interface

The final snapshot names

```text
DL_RELATIVE_DISCARD_FAMILY_BOUND
```

for

\[
 \mathcal W(D_{\rm DL})\leq C_{\rm DL}.
\tag{9.2}
\]

The typing is correct.  It is explicitly classified as an analytic
import with proof-internal provenance:

- DL 2830--2838 gives \(O(\log m)\) nonzero deck-span packets;
- after deleting two unit buffers, DL 2839 plus the Shift Argument
  bounds each core;
- the two unit buffers have total width at most two;
- DL 2841 deletes one final bounded outer buffer; and
- the Parallel Law bounds the union of all discarded packets.

For the Gate N1 cover \(m=2\), the resulting constant is absolute.
The target explicitly rejects the invalid inference of (9.2) from the
aggregate retained-width display alone.  Thus the new name exposes,
rather than conceals, the sole external analytic premise of the Borel
envelope.

### 9.3 Target-Wave typing

The final snapshot no longer infers “target Wave” merely from
injectivity or from source subordination across different annuli.
It first proves only:

1. the finite covering sends every retained proper source leaf to a
   proper target path;
2. injectivity on the retained geometric union makes the target paths
   pairwise disjoint; and
3. Lusin--Souslin makes their geometric union Borel.

This gives a proper Borel target lamination.

In the stationary N1 application, the retained family lies in the
actual unbreakable \(F_*\)-output packet.  KKL Proposition A.14,
lines 2164--2168, applies to each actual singleton source/output pair:
the source singleton is a Wave over the prescribed interval, the
source leaf is unbreakable, and \(F_*\) acts combinatorially there.
It follows that every target singleton is directed over the same
prescribed target interval.  Their already proved lamination union is
therefore subordinate to one target boundary component and is a KKL
target Wave (or empty).  This is the correct target-side argument and
does not transport a source base between annuli.

### 9.4 Final disposition

All three revisions pass.  The theorem-internal proof of
`BOREL_WIDTH_ENVELOPE_PRUNING` remains complete at the final snapshot,
conditional only on the separately named
`DL_RELATIVE_DISCARD_FAMILY_BOUND` and the supplied standard-Borel
source-Wave presentation.

The integration and status boundary is unchanged:

- the width-envelope theorem passes;
- `DL_BUFFER_CHARTWISE_ORDER_IDEAL` is unnecessary;
- BOWR and Gate N1 still require live-file integration and a backward
  audit before promotion; and
- N2, VAAPC-I, UPTCR, rigidity, parameter fibers, and MLC remain open.
