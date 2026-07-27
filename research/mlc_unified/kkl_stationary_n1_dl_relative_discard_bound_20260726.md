# Gate N1 — relative DL discard from measurable-support additivity

## 0. Scope and result

This note addresses only

```text
DL_RELATIVE_DISCARD_FAMILY_BOUND
```

for the degree-two annular packet used in Gate N1.  It does not edit
the live BOWR proof, the analytic N1 proof, or the machine ledger.

The conclusion is:

> **Relative-discard theorem.**  Let \(\mathscr S\) be the actual
> proof-used proper Borel N1 Wave in the degree-two annular packet.
> After deleting a Borel zero-width family of nonrectifiable leaves,
> read the word *lamination* in the Dudko--Lyubich Wave lemma in its
> native measurable-support sense.  If
> \[
> p:A'\longrightarrow A
> \]
> is the degree-two annular cover, then DL 2821--2842 applies to the
> rectifiable core and produces a genuine retained subwave
> \(\mathscr S^\new\subset\mathscr S\) satisfying
> \[
> \mathcal W(\mathscr S\setminus\mathscr S^\new)
> \le C_{\rm DL}
> \tag{0.1}
> \]
> for one absolute constant.

The point missing from the earlier audit was exact additivity of
extremal width across a partition into sublaminations with disjoint
measurable geometric supports.  The Parallel Law alone has the wrong
direction, but measurable-support additivity supplies the reverse
direction.

The measurability adjective is essential.  Section 4 gives an exact
counterexample if “subwave” is weakened to an arbitrary, possibly
nonmeasurable, collection of leaves.

This note proves no part of Gate N2, VAAPC-I, UPTCR, rigidity,
parameter-fiber shrinking, or MLC.

## 1. Frozen source ledger

| source | clause | SHA-256 |
|---|---|---|
| `.tmp_wave_audit/dl23/Feigen.tex` | 1716 and bibliography 3336: `DL2` is Dudko--Lyubich, *Uniform a priori bounds for neutral renormalization*; 2813: a Wave is a lamination of proper paths; 2821--2824: the retained object is a **genuine subwave**; 2827--2841: annular deck pruning and the \(O(\log m)\) loss; 2839: the proof explicitly invokes the Shift Argument in `DL2`, Appendix A.3 | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| `.tmp_wave_audit/dlneutral/PseudoSiegelBounds.tex` | 8538: a lamination is a family of pairwise disjoint simple rectifiable arcs with measurable support, and a sublamination is required to have measurable support | `4AE3253817EF8EEB76DF95FA411CB9C2B6CB0642C3C4AED4D8AE8305F2122172` |
| `.tmp_wave_audit/dlneutral/PseudoSiegelBounds.tex` | 8784--8789: the annular universal-push lemma removes two unit buffers from a rectangle whose horizontal side maps injectively | same hash |
| `.tmp_wave_audit/waves-with-Misha.tex` | 514--525 and 1145--1147: fixed Hubbard-tree inventory and its side marking; 1867--1871: admissible marked paths/arcs; 1904--1914: finite-valued WADs induced by laminations and finite-support bound; 1930--1943: canonical quadrilateral and maximality; 2065--2067 and 2096--2097: pullback marking and restriction filters | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| `.tmp_kl06_source/appendix.tex` | 17--36: extremal width is the infimum of areas of measurable conformal metrics admissible on every path; 59--68: Parallel Law | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |
| `.tmp_kl06_source/wad.tex` | 142--150: a proper lamination has Borel geometric support and its one-arc-class pieces are sublaminations; 245--255: for every arc \(\alpha\), \(W_{\max}(S,\alpha)\in\mathbb R_+\) and \(W(\alpha)\le W_{\max}(S,\alpha)\le W_{\rm can}(S,\alpha)+2\) | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` |
| `kkl_stationary_n1_borel_ordered_wave_realization_20260726.md` | 45--56: pre-pruning standard-Borel leaf space and joint evaluation; 144--209: finite Borel arc packets; 559--715: Borel continuous compactified-arc/circle parameterizations | `6F9B4085C914BD74DD5030C67F311334A4B4882594E111FF552429E4FCC9D118` |

The exact convention bridge is as follows.

1. `Feigen.tex` contains no competing definition of *lamination* or
   *sublamination*.  Its line 2813 uses the unqualified technical word
   *lamination*, and line 2823 calls the output a *genuine subwave*,
   not merely an arbitrary subset of leaves.  Since a Wave at 2813 is
   by definition a lamination satisfying the stated “above” condition,
   an output that is itself a sub-Wave is again a lamination.
2. The same source identifies `DL2` at line 3336 as the locked
   DL-neutral paper, refers to `DL2` for the relevant width toolkit at
   line 1716, and, decisively, invokes `DL2`, Appendix A.3 inside the
   proof of the Wave-pruning lemma itself at line 2839.
3. The imported Appendix convention at DL-neutral 8538 says both that
   a lamination has measurable support and that a sublamination is a
   collection of its arcs whose support is measurable.  Hence the
   source phrase *genuine subwave* supplies exactly the measurable
   sublamination clause needed below.

This is not an inference from the word “subset.”  It is the convention
used by the cited argument that the Feigen proof imports.  If a referee
declines this convention bridge, then the proof stops at the explicit
single source obligation
`DL_GENUINE_SUBWAVE_HAS_MEASURABLE_SUPPORT`; Section 4 proves that the
clause cannot simply be omitted.

Here, as in KL06 142--150, “geometric support” means the union of the
interior images of the leaves, not the closure of that union; this is
the point set on which the path family lives.  KL06 uses the stronger
Borel convention; the argument below needs only area measurability.
This reading is also forced by the DL-neutral wording: if
\(\operatorname{supp}\mathcal L\) meant the topological closure of the
union, its required measurability would be automatic and the
measurable-support clause at 8538 would be vacuous.

The source distinction is:

1. measurable support is enough for the analytic equality in Section
   2; but
2. it does not automatically give the standard-Borel leaf predicate
   needed by BOWR.

The Borel width envelope remains useful for the second task.

## 2. Additivity on disjoint measurable lamination supports

### Lemma 2.1 (measurable-support Parallel equality)

Let \(V\) be a Riemann surface and let
\(\Gamma_1,\Gamma_2\) be path families whose geometric supports

\[
 Z_i:=\bigcup_{\gamma\in\Gamma_i}\gamma((0,1))
\]

are measurable and disjoint.  With all widths and sums interpreted in
the extended half-line \([0,\infty]\), then

\[
 \mathcal W(\Gamma_1\cup\Gamma_2)
 =
 \mathcal W(\Gamma_1)+\mathcal W(\Gamma_2).
\tag{2.1}
\]

The same equality holds for a finite or countable family of pairwise
disjoint measurable supports.  In particular, the statement does not
presuppose finite width.

#### Proof

The Parallel Law gives

\[
 \mathcal W(\Gamma_1\cup\Gamma_2)
 \le
 \mathcal W(\Gamma_1)+\mathcal W(\Gamma_2).
\tag{2.2}
\]

For the converse, let \(\rho\) be any measurable conformal density
admissible for \(\Gamma_1\cup\Gamma_2\).  Define

\[
 \rho_i:=\rho\,\mathbf 1_{Z_i}.
\tag{2.3}
\]

The function \(\rho_i\) is measurable because \(Z_i\) is measurable.
For every \(\gamma\in\Gamma_i\), the interior image of \(\gamma\) lies
in \(Z_i\).  Consequently

\[
 \ell_{\rho_i}(\gamma)
 =
 \ell_\rho(\gamma)
 \ge 1.
\tag{2.4}
\]

Thus \(\rho_i\) is admissible for \(\Gamma_i\).  Since the \(Z_i\) are
disjoint,

\[
\begin{aligned}
 \mathcal W(\Gamma_1)+\mathcal W(\Gamma_2)
 &\le
 \int_{Z_1}\rho^2\,dA+
 \int_{Z_2}\rho^2\,dA\\
 &=
 \int_{Z_1\cup Z_2}\rho^2\,dA\\
 &\le
 \int_V\rho^2\,dA .
\end{aligned}
\tag{2.5}
\]

If there is no admissible density, the admissible-metric infimum is
\(+\infty\) and the reverse inequality is immediate.
If the left side of (2.5) is \(+\infty\), (2.5) says every admissible
density has infinite area and therefore the union also has infinite
width.  Otherwise, taking the infimum over all admissible \(\rho\)
gives

\[
 \mathcal W(\Gamma_1)+\mathcal W(\Gamma_2)
 \le
 \mathcal W(\Gamma_1\cup\Gamma_2).
\tag{2.6}
\]

Together with (2.2), this proves (2.1).

For a countable family indexed by \(i\geq1\), the reverse inequality follows by the
same restriction and Tonelli.  For the upper inequality, if
\(\sum_i\mathcal W(\Gamma_i)<\infty\), choose for every
\(\varepsilon>0\) an admissible density \(\rho_i\) with

\[
 \int_V\rho_i^2\,dA
 \leq
 \mathcal W(\Gamma_i)+\varepsilon2^{-i},
\]

and put \(\rho=(\sum_i\rho_i^2)^{1/2}\).  Since
\(\rho\geq\rho_i\), this density is admissible for every
\(\Gamma_i\), while Tonelli bounds its area by
\(\sum_i\mathcal W(\Gamma_i)+\varepsilon\).  If the sum is infinite,
the desired upper inequality is tautological.  This proves the
countable extended-width statement. \(\square\)

### Corollary 2.2 (relative complement identity)

Let \(\mathscr S\) be a lamination and let
\(\mathscr R\subset\mathscr S\) be a sublamination such that both
geometric supports are measurable.  Put

\[
 \mathscr D:=\mathscr S\setminus\mathscr R.
\]

Then the support of \(\mathscr D\) is measurable and

\[
 \mathcal W(\mathscr S)
 =
 \mathcal W(\mathscr R)+\mathcal W(\mathscr D).
\tag{2.7}
\]

#### Verification

Distinct leaves of a lamination have disjoint interior images.  Hence
the supports of \(\mathscr R\) and \(\mathscr D\) are disjoint.  The
second is the measurable set difference of the support of
\(\mathscr S\) and the support of \(\mathscr R\).  Lemma 2.1 applies.
\(\square\)

No open separation of the two supports is used.  Their closures may
meet or share limiting leaves.  Pointwise restriction of an admissible
density to the actual measurable geometric supports is the reason the
equality remains valid.

The equality is valid in \([0,\infty]\).  This alone does **not** allow
one to subtract a retained-width inequality when both retained and
total widths are infinite.  The next proposition verifies that this
case cannot occur for the actual stationary N1 packet.

### Proposition 2.3 (finite width of every actual stationary packet)

Every proof-used stationary KKL Wave \(S\), and every annular
restriction packet \(B_I(S)\) to which the degree-two DL pruning lemma
is applied in Gate N1, has finite extremal width.

#### Proof

We separate the topological and analytic assertions.

**(a) Finite marked topology and supported arc classes.**  The
stationary surface is the annular complement of the full connected
Hubbard carrier inside the selected Jordan localization.  KKL
514--525 fixes the Hubbard-tree inventory, and KKL 1145--1147 equips
its complement with the marking induced by the sides of that
inventory.  The precise pre-pruning finiteness statement needed here
is already proved in BOWR Section 2: every proof-used stationary Wave
has a finite disjoint decomposition into Borel marked-arc packets.
The degree-two pullback remains finite marked: KKL 2065--2067 says the
marking lifts, and degree two gives at most two lift components of
each interval.

For completeness, the topological step in that proof is short and
includes zero-width classes.  If \(L\) is either \(S\) or \(B_I(S)\),
let \(\mathcal A(L)\) be **all** represented marked arc classes and
define the auxiliary function

\[
X_L(\alpha):=
\begin{cases}
1,&\alpha\in\mathcal A(L),\\
0,&\alpha\notin\mathcal A(L).
\end{cases}
\]

Distinct leaves in distinct classes are disjoint representatives, so
\(X_L\) is a WAD in the sense of KKL 1904.  KKL 1907--1908 therefore
gives

\[
 |\mathcal A(L)|
 \leq
 3|\chi(V_L)|+|\mathcal I_L|
 <\infty ,
\tag{2.8}
\]

For \(B_I(S)\), the two KKL restriction filters are imposed before DL
pruning, so every
surviving component is a path in the finite pullback marking; this is
why (2.8) applies to the actual DL input rather than merely to the
parent Wave.

No uniform bound in the rotation denominator is asserted or needed.
The conclusion is only that each fixed actual packet has finitely many
classes.

**(b) Finite width in each class.**  The marked-surface maximality
statement at KKL 1941--1943 gives, for every supported marked arc
\(\alpha\),

\[
 \mathcal W(L(\alpha))
 \leq W_{\rm can}(V_L,\alpha)+2
 <\infty .
\tag{2.9}
\]

This is the marked analogue of KL06 `wad.tex` 245--255, where
\(W_{\max}(S,\alpha)\in\mathbb R_+\) and
\(W_{\max}\leq W_{\rm can}+2\).  The last quantity in (2.9) is finite
in the KKL source construction: KKL 1904 takes WAD coefficients in
\(\mathbb R_{\geq0}\), KKL 1911--1914 says a lamination induces such a
WAD, and KKL 1930--1931 constructs its canonical coefficient as the
width of the vertical foliation of the corresponding nondegenerate
ideal quadrilateral.  The path condition at KKL 1867--1871 excludes
the boundary-degenerate one/two-interval classes; a nontrivial winding
class uses distinct lifts of its endpoint intervals and is likewise
nondegenerate.

**(c) Finite total width.**  Decompose \(L\) into the finitely many
families \(L(\alpha)\) from (2.8).  The Parallel Law, which needs no
measurability of the individual class supports for this direction,
and (2.9) give

\[
\mathcal W(L)
\leq
\sum_{\alpha\in\mathcal A(L)}
\mathcal W(L(\alpha))
<\infty .
\tag{2.10}
\]

This proves the assertion for both \(S\) and the actual degree-two
packet \(B_I(S)\). \(\square\)

### Lemma 2.4 (Borel rectifiable-core reduction)

Let \(\mathscr S=B_I(S)\) be an actual proof-used proper Borel Wave in
the source annulus \(A'\).  There is a disjoint Borel decomposition

\[
 \mathscr S
 =
 \mathscr S_{\rm rec}\mathbin{\dot\cup}\mathscr N_\infty
\tag{2.11}
\]

such that:

1. every leaf of \(\mathscr S_{\rm rec}\) is a simple rectifiable arc
   in a fixed conformal round-annulus model;
2. \(\mathscr S_{\rm rec}\) is a Wave above the same interval as
   \(\mathscr S\); and
3. \(\mathcal W(\mathscr N_\infty)=0\).

Only \(\mathscr S_{\rm rec}\) needs to be submitted to the native DL
lemma.

#### Proof

Choose a conformal uniformization

\[
 \phi:A'\longrightarrow
 \mathbb A_r:=\{z:r<|z|<1\}.
\tag{2.12}
\]

The KKL stationary annulus has no cusp, so \(0<r<1\); in any event the
round model has finite Euclidean area.  The uniformization extends
homeomorphically between prime-end compactifications.

Use only the **pre-pruning** part of the BOWR construction: its finite
standard-Borel leaf atlas and the fiberwise continuous compactified
parameterization

\[
 e:L_{\mathscr S}\times[0,1]\longrightarrow
 \overline {A'}^{\,{\rm pe}}.
\]

For a leaf code \(s\), define the total variation in the round model by

\[
\ell_0(s)
:=
\sup_{\substack{k\geq1\\
0=t_0<\cdots<t_k=1\\
t_j\in\mathbb Q}}
\sum_{j=1}^k
\left|
\bar\phi(e(s,t_j))-\bar\phi(e(s,t_{j-1}))
\right|.
\tag{2.13}
\]

For a continuous compactified path, rational partitions compute the
usual Euclidean arc length.  Every finite sum in (2.13) is Borel in
\(s\); hence \(\ell_0\), a countable supremum, is Borel.  Therefore

\[
L_{\rm rec}:=\{s:\ell_0(s)<\infty\},
\qquad
L_\infty:=\{s:\ell_0(s)=\infty\}
\tag{2.14}
\]

are Borel leaf sets.

On either set, the evaluation
\((s,t)\mapsto e(s,t)\), \(0<t<1\), is a Borel injection: each fiber
is simple and distinct leaves have disjoint interior images.
Lusin--Souslin therefore makes each geometric union Borel in \(A'\).
They define the proper Borel sublaminations
\(\mathscr S_{\rm rec}\) and \(\mathscr N_\infty\) in (2.11).
Wave direction above the fixed boundary interval is leafwise, so it
is inherited by \(\mathscr S_{\rm rec}\).

Finally, on the round annulus use the conformal density
\(\rho_\varepsilon\equiv\varepsilon\).  Every leaf of
\(\mathscr N_\infty\) has infinite Euclidean length, so
\(\rho_\varepsilon\) is admissible for that family for every
\(\varepsilon>0\).  Its area is

\[
\operatorname{area}_{\rho_\varepsilon}(\mathbb A_r)
=
\varepsilon^2\pi(1-r^2).
\tag{2.15}
\]

Letting \(\varepsilon\downarrow0\) proves
\(\mathcal W(\mathscr N_\infty)=0\).  Conformal invariance returns this
statement to \(A'\).  This proves all three clauses. \(\square\)

There is no dependency cycle here.  Equations (2.13)--(2.14) use only
the BOWR leaf atlas and parameterization constructed before any DL
pruning.  They do not use the DL relative-discard bound, the Borel
width envelope, or any later stationary continuation estimate.

## 3. Application to the degree-two DL packet

Let \(\mathscr S=B_I(S)\), and use Lemma 2.4 to write

\[
\mathscr S
=
\mathscr S_{\rm rec}\mathbin{\dot\cup}\mathscr N_\infty,
\qquad
\mathcal W(\mathscr N_\infty)=0.
\tag{3.1}
\]

If \(\mathscr S_{\rm rec}=\varnothing\), take
\(\mathscr S^\new=\varnothing\).  Then
\(D_{\rm DL}=\mathscr S=\mathscr N_\infty\) has width zero and the
claimed bound is immediate.  Hence assume below that the rectifiable
core is nonempty.

Choose also a round-annulus uniformization of the target \(A\), and
conjugate \(p\) by the source uniformization (2.12) and this target
uniformization.  The conjugate is again a degree-\(m\) holomorphic
cover of closed annuli, the prime-end interval \(J\) is transported
exactly, and \(\mathscr S_{\rm rec}\) is a rectifiable Wave in the
source round annulus.  Apply DL 2823 to this conjugated packet and then
pull the retained family back.  This avoids any assumption that
finite boundary length is invariant under a Riemann map between rough
physical boundaries.  DL gives

\[
 p|_{\mathscr S^\new}\text{ injective},
\qquad
 \mathcal W(\mathscr S^\new)
 \ge
 \mathcal W(\mathscr S_{\rm rec})-C(1+\log m),
\tag{3.2}
\]

where \(\mathscr S^\new\) is called a genuine subwave.

By Lemma 2.4 and the source convention in Section 1, both
\(\mathscr S_{\rm rec}\) and \(\mathscr S^\new\) have measurable
geometric supports.  Set

\[
 D_{\rm rec}:=
 \mathscr S_{\rm rec}\setminus\mathscr S^\new .
\tag{3.3}
\]

Corollary 2.2 gives

\[
 \mathcal W(\mathscr S_{\rm rec})
 =
 \mathcal W(\mathscr S^\new)
 +\mathcal W(D_{\rm rec}).
\tag{3.4}
\]

Proposition 2.3 gives
\(\mathcal W(\mathscr S_{\rm rec})<\infty\), and monotonicity gives
\(\mathcal W(\mathscr S^\new)<\infty\).  Therefore (3.4) is an equality
of finite real numbers, not the indeterminate relation
\(\infty=\infty+x\).  Subtracting the finite quantities in
(3.2)--(3.4) yields

\[
 \mathcal W(D_{\rm rec})
 \le
 C(1+\log m).
\tag{3.5}
\]

Define the discard relative to the **full** KKL packet by

\[
D_{\rm DL}
:=
\mathscr S\setminus\mathscr S^\new
=
\mathscr N_\infty\mathbin{\dot\cup}D_{\rm rec}.
\tag{3.6}
\]

The two supports are measurable and disjoint.  Lemma 2.1, Lemma 2.4,
and (3.5) give

\[
\mathcal W(D_{\rm DL})
=
\mathcal W(\mathscr N_\infty)+\mathcal W(D_{\rm rec})
\leq
C(1+\log m).
\tag{3.7}
\]

For Gate N1, \(m=2\), so

\[
 \mathcal W(D_{\rm DL})
 \le
 C_{\rm DL}:=C(1+\log2),
\tag{3.8}
\]

an absolute constant independent of satellite period, rotation
number, corridor length, marking cardinality, or the number of BOWR
arc packets.  This is exactly

```text
DL_RELATIVE_DISCARD_FAMILY_BOUND.
```

The explicit proof at DL 2830--2841 is consistent with (3.5):
nonzero deck-span packets have total \(O(\log m)\) loss, and the last
packet is trimmed at the outer edges.  DL-neutral 8784--8789 provides
the corresponding two-unit-buffer mechanism for a genuine rectangle
whose horizontal side maps injectively.  Those clauses explain the
constant in the published proof, but (3.4) shows that no independent
single-rectangle realization of the possibly restricted Wave
\(\mathscr S^0\) is needed merely to pass from the published retained
width to the relative complement bound.

### Borel consequence used by Gate N1

The support supplied by the native word *lamination* may be only
measurable, rather than Borel in the BOWR leaf code.  Therefore one
should not silently promote \(D_{\rm DL}\) to a Borel leaf set.

Instead, apply `BOREL_WIDTH_ENVELOPE_PRUNING` to the arbitrary family
\(D_{\rm DL}\), using (3.8).  It gives a Borel super-discard
\(E_{\rm DL}\supset D_{\rm DL}\) with

\[
 \mathcal W(E_{\rm DL})
 \le C_{\rm DL}+\varepsilon.
\tag{3.9}
\]

Then

\[
 \mathscr S\setminus E_{\rm DL}
 \subset
 \mathscr S^\new,
\]

so injectivity is inherited.  This is exactly the interface needed by
the integrated BOWR construction.

## 4. Why measurability cannot be dropped

The following model shows that the displayed retained-width
inequality alone does not imply a relative complement bound for an
arbitrary nonmeasurable collection of leaves.

Let \(Q=(0,1)^2\), and for \(E\subset(0,1)\) let

\[
 \Gamma_E
 :=
 \{\gamma_x(t)=(x,t):x\in E,\ 0<t<1\}.
\tag{4.1}
\]

For every \(E\),

\[
 \mathcal W(\Gamma_E)=m^*(E),
\tag{4.2}
\]

where \(m^*\) is Lebesgue outer measure.

To prove the lower bound, let \(\rho\) be admissible for
\(\Gamma_E\).  For every \(x\in E\), Cauchy--Schwarz gives

\[
 1
 \le
 \left(\int_0^1\rho(x,y)\,dy\right)^2
 \le
 \int_0^1\rho(x,y)^2\,dy.
\tag{4.3}
\]

The last integral is a measurable function of \(x\), so its integral
is at least \(m^*(E)\).  For the reverse inequality, choose an open
set \(O\supset E\) and use the density
\(\rho(x,y)=\mathbf1_O(x)\), then take the infimum over such \(O\).
This proves (4.2).

Choose \(E\subset(0,1)\) with

\[
 m^*(E)=m^*((0,1)\setminus E)=1.
\tag{4.4}
\]

Such sets exist; for example, one may take a Bernstein set arranged
so that both it and its complement meet every positive-measure compact
set.

Then

\[
\mathcal W(\Gamma_E)
=
\mathcal W(\Gamma_{E^c})
=
\mathcal W(\Gamma_{(0,1)})
=1.
\tag{4.5}
\]

Thus the retained inequality

\[
 \mathcal W(\Gamma_E)
 \ge
 \mathcal W(\Gamma_{(0,1)})-0
\]

holds, while the complement still has width \(1\).  This is an exact
counterexample to deriving the full relative bound (3.7) without
measurable-support
additivity.  It also explains why the word *genuine subwave* cannot be
replaced by an arbitrary set-theoretic independent family.

## 5. Dependency and skeptic audit

1. **No subtraction of inequalities without equality.**  The proof
   first establishes (3.4), then independently proves finiteness of
   the actual stationary packet in Proposition 2.3; it does not
   reverse the Parallel Law or subtract \(\infty-\infty\).
2. **No chartwise summation.**  The argument is applied once to the
   full rectifiable core, and its zero-width complement is restored
   only after the DL estimate.  The number of marked arc classes never
   enters the analytic loss.
3. **No transverse measure assumption.**  Lemma 2.1 derives the needed
   finite additivity directly from admissible densities on measurable
   geometric supports.
4. **No Borel overclaim.**  Native measurability proves the analytic
   bound; the independently proved Borel envelope performs the later
   Borel regularization.
5. **No rectangle overclaim.**  DL-neutral 8784--8789 corroborates the
   final buffer geometry, but the relative-complement deduction does
   not assume that an arbitrary restricted \(\mathscr S^0\) is itself
   a conformal rectangle.
6. **No period dependence.**  The cover degree is exactly two.
7. **No use of MLC or a later gate.**  Only the pre-pruning BOWR leaf
   atlas, the native DL Wave lemma, the definition of a genuine
   lamination, KKL/KL06 finite-width facts, and the admissible-metric
   definition of width enter.
8. **No hidden uniform-topology claim.**  The finite-width proof may
   use a marking with \(O(bq)\) intervals.  This affects neither the
   conclusion “finite” nor the DL constant, which depends only on the
   covering degree \(m=2\).

## 6. Exact status

Under the native DL measurable-support meaning of *genuine subwave*:

| obligation | status in this note |
|---|---|
| measurable-support width additivity | proved |
| relative complement identity | proved |
| finiteness of the actual stationary Wave and \(B_I(S)\) | proved from finite marked topology, KKL marked canonical maximality (the KL06 Property-A analogue), and the Parallel Law |
| continuous-path to rectifiable-DL-core reduction | proved; Borel nonrectifiable family has width zero |
| `DL_RELATIVE_DISCARD_FAMILY_BOUND` for degree two | proved from DL 2823 |
| Borel regularization of the discard | supplied separately by the audited Borel width envelope |
| `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` | not promoted here |
| `KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` | not promoted here |
| N2, VAAPC-I, UPTCR, MLC | open |

If the project refuses to read “genuine subwave” as having measurable
geometric support, Section 4 is the exact obstruction and the missing
source clause is

```text
DL_GENUINE_SUBWAVE_HAS_MEASURABLE_SUPPORT.
```

The locked DL-neutral definition at line 8538 supplies that clause.
