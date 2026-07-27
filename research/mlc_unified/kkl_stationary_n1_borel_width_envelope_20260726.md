# Gate N1 — Borel width-envelope lemma

## 0. Scope and status

This note addresses one exact interface in

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION.
```

The Dudko--Lyubich annular pruning lemma produces a set-theoretic
injective subwave whose discarded complement has bounded extremal
width.  Its proof does not give a sufficiently explicit Borel
description of the phrase “outermost curves.”  The result below avoids
that description.  It replaces an arbitrary bounded-width discarded
family by a Borel superfamily of essentially the same width.

The construction is analytic, not numerical.  It neither proves nor
uses Gate N2, VAAPC-I, UPTCR, rigidity, parameter-fiber shrinking, or
MLC.

The source snapshot for extremal width is

| source | clause | SHA-256 |
|---|---|---|
| `.tmp_kl06_source/appendix.tex` | lines 12--36: width is the infimum of the areas of admissible conformal metrics | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |
| `.tmp_wave_audit/dl23/Feigen.tex` | lines 2821--2842: relative annular pruning proof | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |

## 1. Statement

Let \(V\) be a second-countable Riemann surface.  Let \(S\) be a
proper Borel lamination equipped with:

1. a standard-Borel leaf space \(L_S\);
2. a jointly Borel evaluation
   \[
     e_S:L_S\times(0,1)\longrightarrow V;
   \]
3. a continuous proper embedded path \(e_S(\ell,\cdot)\) on every
   fiber; and
4. disjoint images for distinct leaf codes.

No transverse measure is assumed.

### Theorem 1.1 (Borel width envelope)

Let \(D\subset S\) be an arbitrary subfamily; \(D\) is not assumed to
be Borel.  If

\[
 \mathcal W(D)\le C<\infty,
\tag{1.1}
\]

then, for every \(\varepsilon>0\), there is a Borel leaf set
\(E_\varepsilon\subset L_S\) such that:

\[
 D\subset E_\varepsilon,\qquad
 \mathcal W(E_\varepsilon)\le C+\varepsilon.
\tag{1.2}
\]

Here \(D\subset E_\varepsilon\) means that every leaf of \(D\) has its
code in \(E_\varepsilon\).  Both the geometric union of
\(E_\varepsilon\) and the geometric union of
\(L_S\setminus E_\varepsilon\) are Borel subsets of \(V\).

Consequently, if a map is injective on the geometric union of
\(S\setminus D\), then it is injective on the Borel retained
sublamination

\[
 S_\varepsilon^\sharp:=S\setminus E_\varepsilon,
\tag{1.3}
\]

and

\[
 \mathcal W(S\setminus S_\varepsilon^\sharp)
 \le C+\varepsilon.
\tag{1.4}
\]

The Parallel Law also gives the retained-width form

\[
 \mathcal W(S_\varepsilon^\sharp)
 \ge
 \mathcal W(S)-C-\varepsilon.
\tag{1.5}
\]

The theorem does not select a maximal retained family.  Maximality is
unnecessary and, by itself, gives no width estimate.

## 2. Pointwise lower-semicontinuous majorants

The word *pointwise* is essential.  An almost-everywhere majorant does
not preserve admissibility: a curve can lie inside an area-zero
exceptional set.

Fix a smooth conformal background metric

\[
 ds_0,\qquad dA_0
\tag{2.1}
\]

on \(V\).  Its area measure is Radon and sigma-finite.

### Lemma 2.1 (pointwise Vitali--Carathéodory form)

If \(h:V\to[0,\infty]\) is measurable,
\(\int_Vh\,dA_0<\infty\), and \(\eta>0\), there is a lower
semicontinuous

\[
 g:V\longrightarrow[0,\infty]
\tag{2.2}
\]

such that

\[
 g\ge h\quad\text{at every point},\qquad
 \int_Vg\,dA_0
 \le
 \int_Vh\,dA_0+\eta.
\tag{2.3}
\]

#### Proof

The usual Vitali--Carathéodory theorem first gives a nonnegative lower
semicontinuous \(v\) with

\[
 v\ge h\quad\text{almost everywhere},\qquad
 \int_Vv\,dA_0
 \le
 \int_Vh\,dA_0+\frac{\eta}{2}.
\tag{2.4}
\]

Let

\[
 N:=\{x:h(x)>v(x)\}.
\]

Then \(N\) is null.  Put

\[
 a(x):=
 \begin{cases}
  h(x)-v(x),&x\in N,\\
  0,&x\notin N.
 \end{cases}
\]

This avoids the undefined extended-real expression
\(\infty-\infty\).  On \(N\), one has \(v<h\), so the displayed
difference is well-defined in \((0,\infty]\).

For \(k\in\mathbb Z\), let

\[
 N_k:=\{x\in N:a(x)>2^k\}.
\tag{2.5}
\]

Every \(N_k\) is null.  Choose positive numbers
\((b_k)_{k\in\mathbb Z}\) with

\[
 \sum_{k\in\mathbb Z}b_k<\frac{\eta}{2}.
\tag{2.6}
\]

Outer regularity supplies open sets \(U_k\supset N_k\) such that

\[
 2^{k+1}A_0(U_k)<b_k.
\tag{2.7}
\]

Define

\[
 w(x):=
 \sum_{k\in\mathbb Z}
 2^{k+1}\mathbf 1_{U_k}(x).
\tag{2.8}
\]

The indicator of an open set is lower semicontinuous.  Finite partial
sums in (2.8) are lower semicontinuous, and their increasing supremum
is lower semicontinuous.  Thus \(w\) is lower semicontinuous.

If \(0<a(x)<\infty\), choose \(m\) with

\[
 2^m<a(x)\le2^{m+1}.
\]

Then \(x\in N_k\subset U_k\) for every \(k\le m\), and hence

\[
 w(x)
 \ge
 \sum_{k=-\infty}^{m}2^{k+1}
 =
 2^{m+2}
 >
 a(x).
\tag{2.9}
\]

If \(a(x)=\infty\), the same series diverges at \(x\).  Therefore
\(w\ge a\) on \(N\).  Moreover, Tonelli's theorem and (2.7) give

\[
 \int_Vw\,dA_0
 \le
 \sum_{k\in\mathbb Z}2^{k+1}A_0(U_k)
 <
 \frac{\eta}{2}.
\tag{2.10}
\]

Now \(g:=v+w\) is lower semicontinuous, dominates \(h\) at every
point, and satisfies (2.3). \(\square\)

### Lemma 2.2 (strictly positive regularized density)

Let \(\rho:V\to[0,\infty]\) be a measurable conformal density of
finite area.  For every \(\eta>0\), there is a strictly positive lower
semicontinuous density \(\sigma\) such that

\[
 \sigma\ge\rho\quad\text{pointwise},
\qquad
 \int_V\sigma^2\,dA_0
 \le
 \int_V\rho^2\,dA_0+2\eta.
\tag{2.11}
\]

#### Proof

Apply Lemma 2.1 to \(h=\rho^2\), obtaining \(g\).  Choose a continuous
function \(q:V\to(0,\infty)\) with

\[
 \int_Vq^2\,dA_0\le1.
\tag{2.12}
\]

Such a function is obtained from a locally finite smooth partition on
a compact exhaustion, with sufficiently rapidly decreasing positive
coefficients.  Set

\[
 \sigma:=\sqrt{g+\eta q^2}.
\tag{2.13}
\]

The density is lower semicontinuous, strictly positive, and dominates
\(\rho\) pointwise.  Equations (2.3) and (2.12) give (2.11).
\(\square\)

## 3. Lower semicontinuity of weighted path length

Let

\[
 \mathscr P(V):=C((0,1),V)
\tag{3.1}
\]

with the compact-open topology.  This is a Polish space.

For a strictly positive lower-semicontinuous density \(\sigma\), define
the total weighted length by

\[
 \ell_\sigma(\gamma)
 :=
 \sup_{m\ge3}
 \ell_\sigma\!\left(
   \gamma\big|_{[1/m,\,1-1/m]}
 \right).
\tag{3.2}
\]

The compact-interval length is the usual line integral for a
rectifiable path and \(+\infty\) for a nonrectifiable path.

### Lemma 3.1 (lower semicontinuity of length)

The map

\[
 \ell_\sigma:\mathscr P(V)\longrightarrow[0,\infty]
\tag{3.3}
\]

is lower semicontinuous.

#### Proof

On a metrizable space, every nonnegative lower-semicontinuous
function is the increasing pointwise limit of continuous
nonnegative functions.  In the present construction,
\(\sigma\ge\sqrt{\eta}\,q\), where \(q>0\) is continuous.  Starting
with any increasing continuous approximation \(f_j\uparrow\sigma\),
replace it by

\[
 \sigma_j
 :=
 \max\left\{
   f_j,\,
   \sqrt{\eta}\,(1-1/j)q
 \right\},
 \qquad j\ge2.
\]

These functions are continuous, strictly positive, increase with
\(j\), remain bounded above by \(\sigma\), and converge pointwise to
\(\sigma\):

\[
 0<\sigma_j\uparrow\sigma.
\tag{3.4}
\]

For a continuous positive density \(\sigma_j\), weighted length on a
compact parameter interval is lower semicontinuous under uniform path
convergence.  Here is the local argument, which avoids assuming
completeness or a global positive lower bound.  Fix a path \(\gamma\)
and a number \(a<\ell_{\sigma_j}(\gamma)\).  Cover the compact image of
\(\gamma\) by finitely many coordinate disks
\(D_i^-\Subset D_i^+\), with
\(\overline{D_i^+}\) compactly contained in an actual coordinate
chart, on which the oscillation of \(\sigma_j\) is smaller than a
prescribed error.  A Lebesgue-number partition of the parameter
interval makes each image segment lie in some \(D_i^-\).
Consequently, every sufficiently uniformly close comparison segment
lies in the corresponding \(D_i^+\).  Ordinary Riemannian length in
that larger disk is the supremum of finite sums of local distances and
is lower semicontinuous under uniform convergence.
Multiplying those local lower bounds by the infimum of \(\sigma_j\) on
the corresponding disk and summing proves
\(\liminf_n\ell_{\sigma_j}(\gamma_n)\ge a\) whenever
\(\gamma_n\to\gamma\) uniformly.  Let the oscillation error tend to
zero and \(a\uparrow\ell_{\sigma_j}(\gamma)\).

Equivalently, each coordinate disk carries the local length metric of
\(\sigma_jds_0\), with the original topology, and compact-subpath
length is the supremum of finite local partition sums.

For a rectifiable path, monotone convergence with respect to
arclength gives

\[
 \ell_\sigma(\gamma)
 =
 \sup_j\ell_{\sigma_j}(\gamma).
\tag{3.5}
\]

If a compact subpath is nonrectifiable, strict positivity of
\(\sigma\) on its compact image and compactness imply that one
\(\sigma_j\) has a positive lower bound there; both sides of (3.5)
are then infinite.  Thus (3.5) holds for every continuous compact
subpath.

The supremum of lower-semicontinuous functions is lower
semicontinuous.  Apply this first to (3.5), then to the countable
supremum over \(m\) in (3.2). \(\square\)

### Corollary 3.2 (Borel admissibility threshold)

The set

\[
 \mathscr B_\sigma
 :=
 \{\gamma\in\mathscr P(V):\ell_\sigma(\gamma)\ge1\}
\tag{3.6}
\]

is Borel.  Indeed,

\[
 \mathscr B_\sigma
 =
 \bigcap_{n\ge2}
 \{\gamma:\ell_\sigma(\gamma)>1-1/n\},
\tag{3.7}
\]

and every set on the right is open.

No prime-end extension is used in Lemma 3.1.  The topology is local
uniform convergence on \((0,1)\), and total length is the supremum of
compact-subpath lengths.  Proper escape at the two tails therefore
creates no boundary term.

## 4. Proof of Theorem 1.1

By the admissible-metric definition of extremal width, for any
\(\delta>0\) there is a measurable conformal density \(\rho\) such
that

\[
 \ell_\rho(\gamma)\ge1
 \quad(\gamma\in D),
\qquad
 \int_V\rho^2\,dA_0
 \le
 \mathcal W(D)+\delta.
\tag{4.1}
\]

Apply Lemma 2.2 with an error chosen so that the right side of (2.11)
is at most \(C+\varepsilon\).  We obtain a strictly positive lower
semicontinuous \(\sigma\ge\rho\) with

\[
 \int_V\sigma^2\,dA_0\le C+\varepsilon.
\tag{4.2}
\]

The joint Borel evaluation with continuous fibers induces a Borel map

\[
 \widehat e_S:L_S\longrightarrow\mathscr P(V),
\qquad
 \widehat e_S(\ell)=e_S(\ell,\cdot).
\tag{4.3}
\]

To verify this, note that the Borel sigma-algebra of the compact-open
path space is generated by evaluations at a countable dense set of
times, and every such evaluation is Borel by hypothesis.

Set

\[
 E_\varepsilon
 :=
 \widehat e_S^{-1}(\mathscr B_\sigma).
\tag{4.4}
\]

Corollary 3.2 makes this a Borel subset of \(L_S\).  Pointwise
domination \(\sigma\ge\rho\) and (4.1) give

\[
 D\subset E_\varepsilon.
\tag{4.5}
\]

The metric \(\sigma ds_0\) is admissible for every leaf in
\(E_\varepsilon\), by the definition of that set.  Hence

\[
 \mathcal W(E_\varepsilon)
 \le
 \int_V\sigma^2\,dA_0
 \le
 C+\varepsilon.
\tag{4.6}
\]

Finally, restrict the injective evaluation \(e_S\) to

\[
 E_\varepsilon\times(0,1)
 \quad\text{and}\quad
 (L_S\setminus E_\varepsilon)\times(0,1).
\]

Both domains are standard Borel.  Lusin--Souslin makes both geometric
images Borel.  Thus both subfamilies are proper Borel laminations.

If a map is injective on \(S\setminus D\), (4.5) gives

\[
 S\setminus E_\varepsilon
 \subset
 S\setminus D,
\]

so it remains injective on the Borel retained family.  Equation (4.6)
is exactly (1.4).  Finally, the Parallel Law applied to the disjoint
partition

\[
 S
 =
 S_\varepsilon^\sharp
 \mathbin{\dot\cup}
 (S\setminus S_\varepsilon^\sharp)
\]

gives

\[
 \mathcal W(S)
 \le
 \mathcal W(S_\varepsilon^\sharp)
 +
 \mathcal W(S\setminus S_\varepsilon^\sharp).
\]

Combine this with (1.4) to obtain (1.5). \(\square\)

## 5. Application to the degree-two DL pruning

Let

\[
 p:A\longrightarrow B
\]

be the degree-two annular covering in Gate N1, let \(\mathscr S\) be
the Borel source Wave, and let
\(\mathscr S_{\rm DL}^\sharp\) be the set-theoretic injective subwave
given by DL 2821--2842.  Put

\[
 D_{\rm DL}
 :=
 \mathscr S\setminus\mathscr S_{\rm DL}^\sharp.
\tag{5.1}
\]

The displayed conclusion at DL 2823,

\[
 \mathcal W(\mathscr S_{\rm DL}^\sharp)
 \ge
 \mathcal W(\mathscr S)-O(\log2),
\tag{5.2}
\]

does **not by itself** imply an upper bound for
\(\mathcal W(D_{\rm DL})\).  The relative bound comes from the proof:

1. DL 2830--2838 decomposes the discarded nonzero deck-span classes
   into \(T=O(\log2)=O(1)\) disjoint packets;
2. for \(t>0\), write the packet as its one-buffer core \(C_t\) and
   the two deleted unit buffers \(Q_t^-,Q_t^+\).  DL 2839 and the
   Shift argument give
   \[
     \mathcal W(C_t)\le c_{\rm sh},
   \]
   while the buffer definition at DL 1791--1792 gives
   \[
     \mathcal W(Q_t^-)+\mathcal W(Q_t^+)\le2.
   \]
   The Parallel Law therefore yields
   \[
     \mathcal W(\mathscr S^t)
     \le c_{\rm sh}+2;
   \]
3. DL 2841 removes one final \(O(1)\) outer buffer; and
4. the Parallel Law bounds the width of their union.

Thus the proof supplies an absolute \(C_{\rm DL}\) with

\[
 \mathcal W(D_{\rm DL})\le C_{\rm DL}.
\tag{5.3}
\]

We record (5.3), with exactly this proof-internal provenance, as

```text
DL_RELATIVE_DISCARD_FAMILY_BOUND.
```

It is an analytic import.  The Borel envelope neither reproves it nor
infers it from DL's displayed retained-width inequality.

Apply Theorem 1.1 with, for example, \(\varepsilon=1\).  The Borel
discard \(E_{\rm DL}\) contains \(D_{\rm DL}\) and satisfies

\[
 \mathcal W(E_{\rm DL})\le C_{\rm DL}+1.
\tag{5.4}
\]

The retained family

\[
 \mathscr S^\sharp_{\rm Bor}
 :=
 \mathscr S\setminus E_{\rm DL}
\tag{5.5}
\]

is a proper Borel subwave and obeys

\[
 \mathscr S^\sharp_{\rm Bor}
 \subset
 \mathscr S^\sharp_{\rm DL}.
\tag{5.6}
\]

Therefore \(p\) is injective on its geometric union.  Its image is
Borel by Lusin--Souslin: the finite covering sends each proper source
leaf to a proper target path, and its restriction to the retained
geometric union is injective.  Thus the image is a proper Borel target
lamination; the DL lines used here do not, by themselves, type that
image as a target Wave.

In the stationary N1 application, every retained occurrence belongs
to the actual unbreakable \(F_*\)-output packet.  Apply KKL
Proposition A.14 (KKL 2164--2168) to each singleton source/output pair.
It makes every output leaf a target path directed over the prescribed
target interval.  Since the injective output family is a lamination
and all its paths are subordinate to the same target boundary
component, their union is a KKL target Wave (or is empty); the
singleton conclusion supplies the proof-used crest/direction.  No
source base is transported between different annuli.  Every later
relative-cover and degree-two pullback estimate remains valid after
passing to the smaller retained family.

The additive \(+1\) in (5.4) is absolute.  It is independent of
satellite period, rotation number, corridor length, and the number of
nonempty arc classes.

## 6. Why “genuine subwave” alone is insufficient

DL 1289--1297 defines paths and arc diagrams topologically.  At DL
2813 a Wave is called a lamination of proper paths, but the source does
not impose the KL06 requirement that its geometric union be Borel.
The adjective “genuine” at DL 2823 distinguishes an actual path
subfamily from a formal width or WAD; it does not state a descriptive-
set theorem.

This distinction cannot be ignored.  The vertical foliation

\[
 \{\{x\}\times(0,1):x\in(0,1)\}
\]

has Borel geometric union.  Restricting it to a non-Borel set of
parameters produces a topological sublamination whose geometric union
is not Borel.  Thus an arbitrary subwave of a proper Borel lamination
need not be proper Borel.

Theorem 1.1 supplies the missing Borel type without changing the DL
injectivity conclusion and with only an arbitrarily small additional
width charge.

## 7. Adversarial audit

1. **Almost-everywhere domination.** Rejected.  Lemma 2.1 repairs the
   null exceptional set pointwise.
2. **Nonrectifiable paths.** The strictly positive density and the
   metric-length definition assign infinite length on every
   nonrectifiable compact subpath; Lemma 3.1 still applies.
3. **Prime-end tails.** Length is defined on compact interior
   subpaths and then exhausted, so no boundary value of the density is
   required.
4. **Reparameterization.** Metric length is invariant under
   homeomorphic reparameterization, matching the KKL path convention.
5. **Non-Borel DL discard.** The construction never projects or
   selects from \(D_{\rm DL}\).  It uses \(D_{\rm DL}\) only to choose
   an admissible metric, which is allowed by the definition of width.
6. **Geometric support.** Borelness follows from the Borel leaf
   predicate and injective evaluation, not from an arbitrary union.
7. **Wrong aggregate inference.** Equation (5.3) is taken from the
   discarded packets in the DL proof, not inferred from (5.2).
8. **Per-chart loss.** No chartwise cut is made, so no hidden factor
   equal to the number of arc classes occurs.
9. **Maximality.** No Borel maximal-independent-set theorem is used.
   The retained family is simply a hereditary subfamily of the actual
   DL injective family.

## 8. Promotion consequence

The Borel width-envelope lemma removes the need for
`DL_CHARTWISE_BUFFER_CONVEXITY` in Gate N1.  Promotion still requires:

1. an independent check of Lemmas 2.1 and 3.1 above;
2. integration into the live Borel ordered-Wave realization;
3. replacement of the provisional transverse-width clause in the
   analytic N1 note;
4. a backward dependency audit of every use of the DL retained family;
   and
5. the ordinary ledger and regression checks.

Until that integration and audit are complete,
`STANDARD_BOREL_ORDERED_WAVE_REALIZATION` and
`KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` remain open.  Gate N2 and
all later global obligations remain open.

## 9. Exact substitutions in the analytic N1 proof

At every invocation of the relative DL pruning, replace the old
set-theoretic partition by

\[
 B
 =
 B^\sharp_{\rm Bor}
 \mathbin{\dot\cup}
 B^{\rm bad}_{\rm Bor},
\qquad
 B^{\rm bad}_{\rm Bor}:=E_{\rm DL}.
\tag{9.1}
\]

The following dependency audit is exhaustive.

| analytic use | reason it survives the replacement |
|---|---|
| injectivity of \(f\) on \(B^\sharp\) | \(B^\sharp_{\rm Bor}\subset B^\sharp_{\rm DL}\) |
| relative loss \(\mathcal W(B^{\rm bad})\le c_{\rm DL}\) | (5.4), after replacing the absolute constant by \(c_{\rm DL}+1\) |
| \(B^\sharp\cap f^{-1}(E)\subset f^*E\) | hereditary under passing to a subfamily |
| degree-two charge \(\mathcal W(B^\sharp\cap f^{-1}(E))\le2\mathcal W(E)\) | monotonicity plus the unchanged full-cover pullback identity |
| output \(R=f(B^\sharp)\) is a Wave | \(f\circ e\) is an injective proper Borel target lamination; KKL Proposition A.14 on the actual singleton source/output pairs supplies the common target interval and leafwise direction, and subordination to the target boundary component supplies the Wave type |
| critical case \(B^\sharp=\varnothing\) | every retained output would still violate the same leafwise direction obstruction |
| precritical estimate | the retained family only became smaller and the bounded discard only changed by an absolute constant |
| parent with no retained occurrence is charged to \(B^{\rm bad}\) | every directed occurrence of that parent lies in the complement of \(B^\sharp_{\rm Bor}\) |
| uniqueness of a retained occurrence/output | follows from injectivity on the smaller retained family |
| terminal saturation | uses the actual Borel retained output Wave and is unchanged |

The occurrence ledger must add the label

```text
metric-envelope discard
```

and must stop claiming that every bad occurrence has an original
deck-span or outer-buffer label.  Some leaves originally retained by
DL may be added to the Borel envelope.  They are charged by (5.4), not
by a newly invented per-chart estimate.

No proof step uses maximality of the DL retained family.  Hence the
strict inclusion in (5.6) creates no downstream obligation.
