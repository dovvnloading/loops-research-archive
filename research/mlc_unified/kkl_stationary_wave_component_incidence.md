# KKL stationary Wave pass-through correction

## 1. Exact status

This note proves the conditional source-local off-by-one reduction

```text
KKL_STATIONARY_OFF_BY_ONE_PASS_THROUGH_REDUCTION
```

For \(N=b+3\), **assuming the separately open two-sided Wave
noncollision lemma needed to validate KKL line 1603**, every leaf
occurrence of the actually defined \(A_{N-1}=A_{b+2}\) passes through
\(K_0^b\) and \(K_0^{b+1}\) in the sense used by KKL's
stationary-Wave proof.  The statement is unordered.  The indexing
reduction is proved; its geometric line-1603 hypothesis is not.

The companion proof
`pql_iterate_filled_graph_naturality.md` now constructs their canonical
graph lifts in the single final fiber-product pullback, proves the typed
\(f^{N-1}\)-projection formulas, and proves that their containing final
components are distinct.  It also proves that both graph restrictions
have degree two, contradicting the degree-one sentence printed in KKL's
stationary-alignment lemma.  The degree-two replacement preserves the
needed big-\(O\) estimate once the native final proper path is extracted.

It does **not** prove that KKL's undefined phrase “passes through”
survives the immersion restriction filter as one final proper path, or
that the two
successive-level pass-through predicates persist in one final
restriction, that they occur in a fixed order, or that one proper
restriction joins them.  Those claims require the open gates

```text
KKL_STATIONARY_FINAL_PASS_THROUGH_PATH_EXTRACTION
KKL_STATIONARY_TWO_SIDED_WAVE_NONCOLLISION
KKL_STATIONARY_FINAL_INCIDENCE_REFINEMENT
KKL_STATIONARY_NESTED_INCIDENCE_ORDER
KKL_STATIONARY_FIXED_PAIR_PROPER_RESTRICTION
TERMINAL_STATIONARY_RESTRICTION_KL_PUZZLE_SELECTOR
```

No statement below promotes VAAPC-I, UPTCR, or MLC.

## 2. Locked source and notation

The source is KKL `waves-with-Misha.tex`, SHA-256

```text
AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The proof-used occurrences are:

- lines 1547--1548: \(N=b+3\), \(A_0\), and the nested subwaves
  \(A_n\subset A_{n-1}\) for \(0<n<N\);
- lines 1597--1602: the source continua \(K_0^n\), fixed-point pulls
  \(\alpha^n\), and limbs \(L_0^n\);
- line 1603: the source asserts that, if \(n\ge b\), every leaf of
  \(A_{n+1}\) passes through \(K_0^n\), arguing that otherwise two
  portions push forward to Waves and the leaf breaks.  The implication
  requires the open theorem that those two retained Wave images are
  distinct after the untagged proper pushforward;
- line 1605: the printed conclusion invokes \(A_N\);
- lines 1591--1594 and 1609--1617: the stated stationary-alignment lemma
  and its later use at \(A_{N-1}\).

The construction defines \(A_n\) only for \(0\le n<N\).  Hence \(A_N\)
at line 1605 is undefined.  The proof below derives the exact
source-language conclusion for \(A_{N-1}\), conditional on the
line-1603 predicate, without using \(A_N\).

The phrase “passes through \(K_0^n\)” is retained deliberately.  KKL use
it while comparing restrictions in the successive pulled surfaces.  It is
not rewritten here as:

1. physical intersection of an open leaf with a removed continuum;
2. incidence with a named component of
   \((f^{N-1})^{-1}(\mathcal K)\); or
3. a proper path whose endpoint is on that component.

Those are stronger typed statements.

## 3. The exact off-by-one repair

### Theorem 3.1 (conditional off-by-one reduction)
(`KKL_STATIONARY_OFF_BY_ONE_PASS_THROUGH_REDUCTION`)

Let \(b\) be KKL's parabolic bound and \(N=b+3\).  For every leaf
occurrence
\[
 \alpha\in A_{N-1}=A_{b+2},
\]
KKL's line-1603 predicate holds for both
\[
 K_0^b
 \quad\text{and}\quad
K_0^{b+1}.
\tag{3.1}
\]
provided the two-sided Wave noncollision lemma validates KKL's
line-1603 predicate at \(n=b\) and \(n=b+1\).  No order is asserted.

#### Proof

Assume the two-sided noncollision statement, so the contradiction in
KKL line 1603 is valid for the two indices used below.
Because the subwaves are nested,
\[
 A_{b+2}\subset A_{b+1}.
\tag{3.2}
\]
First regard \(\alpha\) as a leaf occurrence in \(A_{b+1}\).  KKL line
1603 with \(n=b\) says that every leaf of
\[
 A_{n+1}=A_{b+1}
\]
passes through \(K_0^b\).  Thus \(\alpha\) has the first predicate in
(3.1).

Next use \(\alpha\in A_{b+2}\) and apply line 1603 with \(n=b+1\).
It says that every leaf of
\[
 A_{n+1}=A_{b+2}
\]
passes through \(K_0^{b+1}\).  Thus \(\alpha\) has the second predicate
in (3.1).

Both applications are within the declared range \(n\ge b\), and
\[
 b+2=N-1<N.
\]
Therefore no undefined \(A_N\) is used. \(\square\)

### Corollary 3.2 (conditional)

Conditional on the same noncollision hypothesis, the two-pass-through
sentence intended at KKL line 1605 is valid for the actually defined
\(A_{N-1}\), in the source's pass-through sense.

#### Proof

This is exactly Theorem 3.1. \(\square\)

## 4. Final-level graph lifts and components

KKL's iterated \(\psi\)-quadratic-like surface is a fiber product.  For
\(m=N-1\), the relevant final pulled package is
\[
 \mathcal K^m=(f^m)^{-1}(\mathcal K)
 \subset U^m.
\tag{4.1}
\]
Kahn's finite-iterate theorem proves that the iterated immersion
\(\iota_m|_{K^m}:K^m\to K^0\) is a homeomorphism.  Therefore the actual
graph lifts are
\[
\widehat K_r
=
\bigl(\iota_m|_{K^m}\bigr)^{-1}(K_0^r)
\subset U^m,
\qquad r\in\{b,b+1\},
\tag{4.2}
\]
and satisfy
\[
 \iota_m(\widehat K_r)=K_0^r,
 \qquad
 \widehat K_r\subset\mathcal K^m.
\tag{4.3}
\]
Thus
\[
C_r=\operatorname{Comp}_{\mathcal K^m}(\widehat K_r)
\tag{4.4}
\]
is well-defined.  The companion theorem proves
\[
 f^m(\widehat K_b)=F^2(K_0^0),
 \qquad
 f^m(\widehat K_{b+1})=F(K_0^0).
\tag{4.5}
\]
These are different members of the pairwise-disjoint primitive cycle
because its period is greater than one.

Suppose \(C_b=C_{b+1}=C\).  The set \(f^m(C)\) is connected and contained
in the finite disjoint union \(\mathcal K\), but by (4.5) it meets two
different components of that union.  Each component of a finite
pairwise-disjoint compact union is relatively open and closed, so a
connected subset cannot meet two of them.  This is a contradiction.
This is the ledger theorem
`KKL_STATIONARY_FINAL_COMPONENT_REALIZATION`.  It proves no
occurrence-level incidence.

The same graph calculation proves
\[
 \deg(f^m|\widehat K_b)
 =
 \deg(f^m|\widehat K_{b+1})
 =
 2.
\tag{4.6}
\]
The complete critical-itinerary proof is
`KKL_STATIONARY_DEGREE_TWO_CORRECTION`.  Consequently the source's
pushforward-lamination inequality must read
\[
 \mathcal W(B)\leq2\mathcal W(C)+4,
\tag{4.7}
\]
not \(\mathcal W(B)\leq\mathcal W(C)+O(1)\).  Since KKL subsequently
prove \(\mathcal W(C)\leq2\mathcal W(\mathcal RF)\), this changes only a
universal coefficient—conditional on the missing path extraction.

## 5. Open path-extraction, incidence-refinement, and order gates

### Obligation 5.0
(`KKL_STATIONARY_FINAL_PASS_THROUGH_PATH_EXTRACTION`)

Put \(m=b+2\) and use the actual final component over
\(K_0^{m-1}=K_0^{b+1}\).  First prove
`KKL_STATIONARY_TWO_SIDED_WAVE_NONCOLLISION`, thereby validating KKL
line 1603 at \(n=m-1\) for the defined \(A_m\).  Then address the
separate fact that “passes through” is not defined as a theorem about
immersion restrictions: prove that every retained
depth-\(m\) occurrence supplies one connected proper path from that
component to \(\mathcal K^m\) minus it; prove survival of the
subordinate/non-marked restriction filter, prime-end landing,
non-locally-connected model compatibility, measurable lamination
assembly, and
\[
 \mathcal W(A_m)\leq\mathcal W(B).
\tag{5.0}
\]
Together with (4.7), this repairs KKL's native stationary estimate with
degree two.

### Obligation 5.1
(`KKL_STATIONARY_FINAL_INCIDENCE_REFINEMENT`)

For every retained occurrence \(\alpha\in A_m\), prove that the two
successive-level pass-through predicates from Theorem 3.1 persist as
incidences with \(C_b,C_{b+1}\) in one actual component, or one
source-faithful finite ordered component chain, of
\[
 \iota_m^{-1}(\alpha)\setminus\mathcal K^m.
\tag{5.1}
\]
Record every intervening component, sheet, projection, and occurrence.
The graph theorem alone does not prove that two separately selected
shallower restrictions refine to the same final restriction.

If refinement fails, record the first split restriction, missing end
lift, or occurrence mismatch.

### Obligation 5.2
(`KKL_STATIONARY_NESTED_INCIDENCE_ORDER`)

After Obligation 5.1, prove a nested-domain theorem in \(U^{N-1}\)
showing that every retained oriented final restriction meets
\(C_b,C_{b+1}\) in one declared order.  The proof must address repeated
incidences and must not infer order solely from two separate separation
statements at different pullback levels.

## 7. Proper-restriction and KL gates

### Obligation 7.1
(`KKL_STATIONARY_FIXED_PAIR_PROPER_RESTRICTION`)

After the final incidence refinement and order are proved, construct for every
bound occurrence either:

1. one connected proper restriction with endpoints on
   \(C_b,C_{b+1}\); or
2. a source-faithful finite ordered restriction multicurve whose
   consecutive components carry the complete intervening-component
   itinerary.

Retain sheet, deck phase, order, obstacle, and occurrence multiplicity.
Prove a uniform width-retention estimate
\[
 \mathcal W(\mathcal H_{\rm stat})
 \ge
 \theta\,\mathcal W(A_{N-1})-E,
\tag{7.1}
\]
with \(\theta>0\) and \(E<\infty\) independent of the primitive period
and corridor length.  The ordered-multicurve alternative must use the
summed component length and must prove the required literal-subarc
overflow relation.

### Obligation 7.2
(`TERMINAL_STATIONARY_RESTRICTION_KL_PUZZLE_SELECTOR`)

Construct one authorized common puzzle certificate
\[
 (Y,v,w),\qquad v\ne w,
\tag{7.2}
\]
or a proved uniformly controlled tagged atlas, realizing the physical
endpoint components as \(S_Y^v,S_Y^w\).  Preserve localization, tile,
deck, cyclic order, obstacles, multiplicity, and final-root behavior.

## 8. Skeptic audit

1. The undefined \(A_N\) was not imported.
2. The off-by-one conclusion was kept conditional on the exact
   noncollision statement missing from KKL line 1603.
3. The base/near-\(K\) pulls were promoted only after the canonical
   filled-set graph homeomorphism was proved.
4. The level map is \(f^{N-1}\), not \(F^{N-1}\).
5. Distinctness was proved from the typed projection formula.
6. No incidence order was inferred from separate-level separation
   statements.
7. Two incidences were not promoted to one connected proper restriction.
8. No KKL component label was relabeled as a KL puzzle vertex.
9. No width retention was inferred from incidence.
10. All global gates remain open.
