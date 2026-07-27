# Gate N1 - A/B audit of the DL relative-discard import

## 0. Frozen target and verdict

This certificate audits the frozen file

```text
kkl_stationary_n1_dl_relative_discard_bound_20260726.md
```

whose SHA-256 is

```text
80ABC64278889469F1B95508A378D30F7DE003B5D6CECF05D64A6C84F6F419E9.
```

The target was not edited.

There are two logically different routes to the desired estimate. They
must not be identified.

### Route A: retained-width additivity

The measurable-support additivity argument in the frozen target is
mathematically correct, including extended-real widths, the finite-width
reduction, and the zero-width nonrectifiable family. As a source-locked
argument, however, it is conditional on

```text
DL_GENUINE_SUBWAVE_HAS_MEASURABLE_SUPPORT.
```

The locked Feigen source calls the output a "genuine subwave" and cites
DL2 Appendix A.3 in the proof, while DL2 Appendix A.1 defines
sublaminations to have measurable support. This is strong evidence for
the intended convention, but the Feigen text does not explicitly say
that it imports the Appendix A.1 measurable-support definition.
Therefore Route A should be presented either with that convention as an
explicit hypothesis or with an authoritative source confirming it.

### Route B: proof-internal DL deletion

Independently of Route A, Feigen 2827--2841 proves directly, in the
authors' native buffer/width terminology, that the discarded family has
width \(O(1+\log m)\). This route uses the Parallel Law only. It uses
neither exact measurable-support additivity nor subtraction of the
displayed retained-width inequality.

Consequently:

```text
DL_RELATIVE_DISCARD_FAMILY_BOUND
```

is licensed for the Gate-N1 degree-two packet by Route B. Route A
remains conditional as a separate derivation.

## 1. Frozen source ledger

| source | audited clauses | SHA-256 |
|---|---|---|
| `.tmp_wave_audit/dl23/Feigen.tex` | 1791--1792: buffers and their widths; 2813: Wave; 2823: annular pruning; 2827--2841: complete proof-internal deletion | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| `.tmp_wave_audit/dlneutral/PseudoSiegelBounds.tex` | 8538: measurable-support lamination convention; 8784--8789: unit-buffer universal push; Appendix A.3: Shift Argument | `4AE3253817EF8EEB76DF95FA411CB9C2B6CB0642C3C4AED4D8AE8305F2122172` |
| `.tmp_wave_audit/waves-with-Misha.tex` | finite marked inventory and canonical WAD bounds | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| `.tmp_kl06_source/appendix.tex` | extremal width and Parallel Law | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |
| `.tmp_kl06_source/wad.tex` | proper-lamination and finite canonical-width facts | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` |
| `kkl_stationary_n1_borel_ordered_wave_realization_20260726.md` | pre-pruning leaf atlas and filtered restriction code | `6F9B4085C914BD74DD5030C67F311334A4B4882594E111FF552429E4FCC9D118` |

## 2. Route A audit

### 2.1 Additivity on disjoint measurable supports

Let \(\Gamma_i\) have pairwise disjoint measurable geometric supports
\(Z_i\). Restricting any admissible metric \(\rho\) for
\(\bigcup_i\Gamma_i\) to \(\rho{\bf 1}_{Z_i}\) gives admissible metrics
for the individual families, and Tonelli gives

\[
\sum_i {\rm area}(\rho{\bf 1}_{Z_i})
=
{\rm area}\!\left(\rho{\bf 1}_{\cup_i Z_i}\right).
\]

This proves the reverse of the Parallel inequality. The ordinary
Parallel construction, using
\(\rho=(\sum_i\rho_i^2)^{1/2}\), proves the other direction. The
argument is valid in \([0,\infty]\). The target correctly checks
finiteness before subtracting finite retained and total widths.

### 2.2 Rectifiable core

The target's total-variation predicate in a finite-area round annulus
is Borel. The rectifiable and infinite-length leaf supports are Borel
by the injective Borel evaluation and Lusin--Souslin. On every
infinite-length leaf, the constant metric \(\varepsilon\) has infinite
path length, while its area tends to zero with \(\varepsilon\).
Therefore the nonrectifiable family has width zero. The empty-core case
is handled separately and correctly.

### 2.3 Exact conditional point

To deduce

\[
W(\mathscr S_{\rm rec})
=W(\mathscr S^{\rm new})+W(D_{\rm rec}),
\]

the retained support must be measurable. DL2 8538 gives precisely this
property for a sublamination in that paper. Feigen 2823 says "genuine
subwave" and Feigen 2839 invokes DL2 Appendix A.3, but the locked
Feigen text has no explicit global convention importing DL2 8538.
Thus this exact derivation is conditional on the named bridge.

The target's vertical-fiber example correctly shows why an arbitrary
nonmeasurable subfamily cannot be substituted.

## 3. Route B: direct proof-internal discard estimate

Let \(\mathscr S\) be the rectifiable input Wave in Feigen 2823.
Feigen 2830 decomposes it into pairwise-disjoint laminations

\[
\mathscr S
=
\mathscr S^0\mathbin{\dot\cup}
\mathscr S^1\mathbin{\dot\cup}\cdots
\mathbin{\dot\cup}\mathscr S^T,
\qquad
T=O(\log m)
\]

by Feigen 2837.

For \(t>0\), Feigen 2839 states

\[
W(\mathscr S^t)=O(1).
\]

The stated reason is that, after removing unit buffers, the packet
crosses its deck shift, to which the cited DL2 Shift Argument applies.
Therefore the Parallel Law gives

\[
W\!\left(\bigcup_{t=1}^{T}\mathscr S^t\right)
\leq
\sum_{t=1}^{T}W(\mathscr S^t)
=O(\log m).
\tag{3.1}
\]

Feigen 2841 then replaces the input by \(\mathscr S^0\) and removes one
additional \(O(1)\) outermost portion to obtain
\(\mathscr S^{\rm new}\). In the source's native terminology,
"removing \(a\) outermost curves" is removal of an outer buffer of
transverse width \(a\), not removal of a finite cardinality of leaves.
This reading is fixed by:

1. Feigen 1791--1792, where buffers of any width are defined as
   outermost subrectangles;
2. Feigen 2827, which announces removal of \(O(\log m)\) outermost
   curves as the loss asserted in the lemma;
3. Feigen 2839, which quantifies each span-packet loss by unit buffers;
   and
4. the paper's repeated use of "remove \(O(1)\) curves/buffers" as a
   transverse-width budget, including Feigen 2601.

Writing

\[
D_{\rm span}:=\bigcup_{t=1}^{T}\mathscr S^t,
\qquad
D_{\rm out}:=\mathscr S^0\setminus\mathscr S^{\rm new},
\]

the proof gives

\[
W(D_{\rm span})=O(\log m),
\qquad
W(D_{\rm out})=O(1).
\]

Set-theoretically,

\[
\mathscr S\setminus\mathscr S^{\rm new}
=
D_{\rm span}\mathbin{\dot\cup}D_{\rm out}.
\]

A second application of the Parallel Law yields

\[
W(\mathscr S\setminus\mathscr S^{\rm new})
\leq
W(D_{\rm span})+W(D_{\rm out})
=O(1+\log m).
\tag{3.2}
\]

This is the relative-discard estimate itself. No complement identity,
support measurability, finite-total-width subtraction, or Borel leaf
selector occurs in (3.1)--(3.2).

For Gate N1, \(m=2\), so (3.2) is bounded by one absolute constant.

For the original continuous-path packet, let
\(\mathscr N_\infty\) be the zero-width nonrectifiable family proved in
the target and apply the preceding estimate to the rectifiable core.
The full discard is

\[
D_{\rm DL}
=
\mathscr N_\infty\cup D_{\rm span}\cup D_{\rm out}.
\]

The Parallel Law and \(W(\mathscr N_\infty)=0\) give the same absolute
bound. Measurability of the union is not needed for this upper bound.
The later Borel width envelope supplies the Borel regularization.

## 4. Dependency and edge-case audit

1. The actual \(B_I(S)\) packet has finite width by the finite marked
   inventory, per-class canonical bounds, and a finite Parallel sum.
2. The empty rectifiable core gives a zero-width full packet and needs
   no DL pruning.
3. The extended-real additivity lemma is correct; Route B does not need
   it.
4. The BOWR leaf atlas, restricted-occurrence code, and direction
   predicate are constructed before pruning. There is no dependency
   cycle.
5. The target's source ledger cites BOWR Sections 2--5, although the
   construction of \(B_I(S)\) also uses pre-pruning Section 7.2. This
   is a traceability omission only; Section 7.2 does not depend on DL
   pruning or stationary continuation.
6. Native measurability does not by itself supply a standard-Borel leaf
   predicate. The proof correctly leaves Borel regularization to the
   separate width-envelope theorem.

## 5. Final status

| item | verdict |
|---|---|
| measurable-support additivity lemma | PASS |
| finite packet and rectifiable-core reduction | PASS |
| Route A, as a frozen source-locked derivation | CONDITIONAL on `DL_GENUINE_SUBWAVE_HAS_MEASURABLE_SUPPORT` |
| Route B, original Feigen 2827--2841 deletion | PASS in the source's native buffer/width terminology |
| `DL_RELATIVE_DISCARD_FAMILY_BOUND` for Gate N1 | PASS by Route B |
| BOWR dependency order | PASS; acyclic |
| `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` | not promoted by this certificate |
| N2, VAAPC-I, UPTCR, MLC | open |

No remaining analytic blocker was found for the degree-two relative
discard estimate. The remaining source-semantic issue concerns only
whether Route A may be advertised as unconditional; it does not block
Route B.
