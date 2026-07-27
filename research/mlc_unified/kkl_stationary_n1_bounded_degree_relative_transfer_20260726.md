# Gate N1: bounded-degree relative transfer and the exact residual extraction gate

## 1. Status, scope, and verdict

This note addresses only

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION
```

and, more specifically, the two source-relative estimates denoted
`RSC-1` and `RSC-2` in
`kkl_stationary_relative_wave_continuation_source_reconstruction_20260726.md`.
It does not edit the proof ledger or the LaTeX manuscript.

The result of the pass is asymmetric.

1. **The bounded-degree route proves the analytic inequality in
   `RSC-2`**, with no use of the coefficient-one Wave lemma and no
   choice of a single restriction occurrence.  The canonical
   realization is the full family of all retained restrictions.  The
   nested stationary Waves force every intermediate image of the
   relevant source subfamily to be a lamination.  A safe constant is
   \[
      D_b=2^{b+2}.
   \]
   Hidden sheet multiplicity and collision of untagged occurrences do
   not invalidate this estimate.  If a later formal interface insists
   that every path family be presented as a Borel object, Borel
   regularity of the full retained-restriction relation must still be
   supplied; it is not needed by the extremal-width inequality itself.
2. The same argument reduces `RSC-1` to an output-side or source-buffer
   estimate, but it does **not** prove that estimate.  In particular,
   bounded covering degree, the general degree-\(d\) pushforward lemma,
   occurrence saturation, and maximality do not imply that the omitted
   family has bounded width.
3. The exact missing analytic input is a **Borel, \(b\)-uniform,
   bounded-defect Wave extraction theorem** for the actual stationary
   one-step image.  Equivalently, one may prove a finite coherent-packet
   source-pruning theorem with a bounded total collision defect.
4. The native Dudko--Lyubich annular pruning proof does give the required
   *relative* source-buffer estimate on one coherent common-crest packet.
   It does not by itself produce the required packet decomposition or
   control inter-packet collisions in the KKL stationary family.

Consequently Gate N1 remains **open**, but its multiplicity-aware
`RSC-2` transfer part is closed at the path-family level.  The remaining
gap is not a coefficient loss.  It is the construction of the right
output Wave, with bounded omitted source width, together with whatever
Borel presentation is required by the final formal interface.

The global statuses are unchanged:

```text
KKL stationary repair: open
VAAPC-I:               open
UPTCR:                 open
MLC:                   open
```

## 2. Frozen sources and notation

The source statements used here are:

| source | clauses |
|---|---|
| KKL master `.tmp_wave_audit/waves-with-Misha.tex` | the degree-two complement covering and immersion at lines 1225 and 2062--2142; the domination lemma at 2086--2090; unbreakability at 2161--2162; the stationary families at 1547--1579 |
| KL06 `.tmp_kl06_source/appendix.tex` | width definition at 17--36; Series and Parallel Laws at 39--68; holomorphic transformation at 72--114 |
| Dudko--Lyubich `.tmp_wave_audit/dl23/Feigen.tex` | the one-common-interval annular pruning lemma and its proof at 2821--2842 |

Their locked SHA-256 values are, respectively,

```text
KKL master:
AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5

KL06 appendix:
EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3

Dudko--Lyubich Feigen.tex:
EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF
```

Fix the KKL parabolic bound \(b\), and write

\[
   N=b+3,\qquad 0\le n<N-1,\qquad h=n+1\le b+2.
\]

Let

\[
   V_j=\mathcal U^j\setminus\mathcal T^j,
   \qquad
   P_j=f^j:V_j\longrightarrow V_0,
   \qquad
   I_j=\iota_j:V_j\longrightarrow V_0.
\]

On the complements, \(P_j\) is an unbranched finite covering and

\[
   \deg P_j\le 2^j.                                      \tag{2.1}
\]

For a path family \(\Gamma\) in a target surface and a finite covering
\(p:X\to Y\), let \(p^*\Gamma\) denote the **full lift family**: every
lift, from every sheet, of every parametrized path in \(\Gamma\).
This is different from an arbitrarily selected inverse branch.

For the sequential argument below, it is safer not to identify the
different copies of the same model surface.  At time \(j\), write

\[
 \iota_j:V_j^{\rm res}\longrightarrow V_j^{\rm out},
 \qquad
 f_j:V_j^{\rm res}\longrightarrow V_{j+1}^{\rm out}.
 \tag{2.2}
\]

Here \(V_j^{\rm out}\) is a copy of
\(\mathcal U\setminus\mathcal T\), \(V_j^{\rm res}\) is a copy of
\(\mathcal U'\setminus f^{-1}(\mathcal T)\), \(\iota_j\) is the
immersion used to restrict a path, and \(f_j\) is the unbranched
degree-two covering used to push that restriction forward.  Thus a
single retained occurrence is typed as

\[
 \alpha_j\subset V_j^{\rm out},
 \qquad
 \beta_j\subset V_j^{\rm res},
 \qquad
 \iota_j(\beta_j)\subset\alpha_j,
 \qquad
 f_j(\beta_j)=\alpha_{j+1}.
 \tag{2.3}
\]

The containment in (2.3), rather than equality, is essential:
\(\beta_j\) is a retained component of the immersion restriction.
All widths below are taken in the surface containing the displayed
family.

## 3. Exact finite-cover width identity

The key multiplicity calculation is elementary but must be stated at the
level of path families.

### Proposition 3.1 (full-lift identity)

Let \(p:X\to Y\) be an unbranched conformal covering of finite degree
\(d\).  For every KL06 path family \(\Gamma\) in \(Y\), whose members
are parametrized by intervals,

\[
   \mathcal W(p^*\Gamma)=d\,\mathcal W(\Gamma).           \tag{3.1}
\]

The statement is valid for arbitrary path families; \(\Gamma\) need not
be a lamination.  Each interval-parametrized path is counted with all
\(d\) lifts determined by its \(d\) possible starting points over one
interior parameter value.  The proposition is not a statement about
closed lifts of maps whose parameter domain is \(S^1\).  KL06 defines
paths on intervals, so this is exactly the source convention.

#### Proof: upper bound

Let \(\rho(y)|dy|\) be an admissible conformal metric for \(\Gamma\).
Its pullback \(p^*\rho\) is admissible for every lift of every
\(\gamma\in\Gamma\), because a lifted path has exactly the same
\(\rho\)-length as its projection.  Since \(p\) has degree \(d\),

\[
   \operatorname{area}_{p^*\rho}(X)
   =
   d\,\operatorname{area}_{\rho}(Y).
\]

Taking the infimum over admissible \(\rho\) gives

\[
   \mathcal W(p^*\Gamma)
   \le d\,\mathcal W(\Gamma).                            \tag{3.2}
\]

#### Proof: lower bound

Let \(\sigma(x)|dx|\) be admissible for \(p^*\Gamma\).  Locally enumerate
the inverse branches of \(p\) by \(s_1,\ldots,s_d\), and push the density
on each sheet to \(Y\):

\[
   \sigma_j(y)
   =
   \sigma(s_j(y))\,|s_j'(y)|.
\]

Although the labels can permute under monodromy, the symmetric function

\[
   \rho(y)
   :=
   \frac1{\sqrt d}
   \left(\sum_{j=1}^d\sigma_j(y)^2\right)^{1/2}           \tag{3.3}
\]

is globally well-defined and measurable.

Fix \(\gamma\in\Gamma\).  Its \(d\) lifts, counted by starting sheet,
have \(\sigma\)-lengths \(L_1,\ldots,L_d\), each at least one.
Minkowski's integral inequality gives

\[
\begin{aligned}
 \ell_\rho(\gamma)
 &=
 \frac1{\sqrt d}
 \int_\gamma
 \left(\sum_{j=1}^d\sigma_j^2\right)^{1/2}|dy|\\
 &\ge
 \frac1{\sqrt d}
 \left(\sum_{j=1}^d
       \left(\int_\gamma\sigma_j|dy|\right)^2
 \right)^{1/2}\\
 &=
 \frac1{\sqrt d}
 \left(\sum_{j=1}^dL_j^2\right)^{1/2}
 \ge1.
\end{aligned}                                             \tag{3.4}
\]

Thus \(\rho\) is admissible for \(\Gamma\).  Moreover,

\[
\begin{aligned}
 \operatorname{area}_\rho(Y)
 &=
 \frac1d
 \int_Y\sum_{j=1}^d\sigma_j(y)^2\,dA_y\\
 &=
 \frac1d\operatorname{area}_\sigma(X).
\end{aligned}                                             \tag{3.5}
\]

Taking the infimum over admissible \(\sigma\) gives

\[
   d\,\mathcal W(\Gamma)
   \le\mathcal W(p^*\Gamma).                              \tag{3.6}
\]

Equations (3.2) and (3.6) prove (3.1). \(\square\)

If one of the two widths is \(0\) or \(+\infty\), the same conclusion
follows by the standard extended-value approximation.  The displayed
argument proves the nondegenerate finite case, which is the only case
used in the stationary estimate.

### Checks on Proposition 3.1

1. The proof counts every sheet.  It does not replace a multiset of
   lifts by one untagged image.
2. No injectivity of \(p\) on the selected family is assumed.
3. No coefficient-one Wave estimate is used.
4. The factor \(d\) is sharp: the full lift of a rectangle family under
   a degree-\(d\) annular cover consists of \(d\) parallel copies.
5. The argument is insensitive to whether distinct lifts project to the
   same unparametrized path.

## 4. One-step multiplicity-aware relative transfer

We now combine Proposition 3.1 with the KKL domination lemma.

### Definition 4.1 (retained-occurrence realization)

Let \(F=(f,\iota)\) act between the one-step marked complements.  Let
\(D\) be a sublamination of the target Wave surface.  A
**retained-occurrence realization from \(D\) to \(E\)** is a lamination
\(B\) in the source complement such that:

1. \(B\) consists only of restrictions surviving both KKL filters:
   it is a path in the fine marking and is not subordinate to one
   interval of the coarse immersion marking;
2. for every \(\alpha\in D\), the restriction
   \(\iota^*\alpha\) contains at least one leaf of \(B\);
3. every \(\beta\in B\) satisfies \(f(\beta)\in E\).

The definition does **not** require:

- one restriction occurrence per source leaf;
- injectivity of \(\iota\) on \(B\);
- injectivity of \(f\) on \(B\); or
- distinct untagged images for distinct occurrences.

If \(D,E,B\) and the occurrence relation are Borel in a fixed
standard-Borel path model, call this a **Borel realization**.  Neither
the KL06 definition of extremal width nor Proposition 4.2 below
requires this extra adjective.

### Proposition 4.2 (one-step relative transfer)

Under Definition 4.1, if \(f\) has degree \(d\), then

\[
   \mathcal W(D)\le d\,\mathcal W(E).                    \tag{4.1}
\]

#### Proof

By clause 2 and the KKL domination lemma,

\[
   \mathcal W(D)\le\mathcal W(B).                        \tag{4.2}
\]

Clause 3 gives

\[
   B\subset f^*E.
\]

Monotonicity of width under family inclusion and Proposition 3.1 give

\[
   \mathcal W(B)
   \le\mathcal W(f^*E)
   =d\,\mathcal W(E).                                    \tag{4.3}
\]

Combining (4.2) and (4.3) proves (4.1). \(\square\)

### Why multiplicity is harmless here

Suppose one untagged output path has two retained source occurrences.
Both occurrences lie in the full lift \(f^*E\), and both are counted in
the factor \(d\) in (3.1).  Nothing is silently collapsed.  This is
exactly the situation in which a coefficient-one estimate can fail but
(4.1) remains valid.

Unbreakability is used only to define the desired untagged next path.
It is **not** used to infer a unique restriction occurrence.

## 5. Sequential transfer through the stationary horizon

The KKL action is sequential.  The locked source proves equality of the
one-shot and sequential actions on multi-intervals, but no such
one-shot identity is needed here.  The declared nested stationary
sequence itself supplies a canonical occurrence realization.

### Lemma 5.1 (full-restriction realization on a stationary sequence)

Assume that the stationary sequence has been constructed through stage
\(n\):

\[
 A_n\subset A_{n-1}\subset\cdots\subset A_0,
 \qquad
 S_j:=F_*^jA_j
 \text{ is a Wave for }0\le j\le n,
 \tag{5.0}
\]

and \(A_0\subset A^{N\text{-nbr}}\).  For any subfamily
\(D_0\subset A_n\), put

\[
   D_j:=\Phi_j(D_0),\qquad 0\le j\le h,
\]

where \(h=n+1\) and \(\Phi_j\) is the sequential untagged path map.
Then, for every \(0\le j<h\):

1. \(D_j\subset S_j\), so \(D_j\) is a sublamination;
2. the full retained restriction family
   \[
      B_j:=\iota_j^*D_j
   \]
   after both KKL marking filters is a lamination in
   \(V_j^{\rm res}\);
3. \(B_j\) is a retained-occurrence realization from \(D_j\) to
   \(D_{j+1}\).

#### Proof

For \(j\le n\), nesting gives \(D_0\subset A_n\subset A_j\).  Applying
the unique untagged \(j\)-step map gives

\[
 D_j=\Phi_j(D_0)
 \subset \Phi_j(A_j)
 =F_*^jA_j
 =S_j.                                                   \tag{5.0a}
\]

Thus \(D_j\) is a sublamination of the Wave \(S_j\).

The full restriction \(\iota_j^*D_j\) means exactly the proper
components surviving the fine source marking and the coarser immersion
marking filters at KKL lines 2096--2097.  Restrictions of distinct
leaves cannot cross: an intersection point in \(V_j^{\rm res}\) would
map under the local homeomorphism \(\iota_j\) to an intersection of the
corresponding distinct leaves of \(D_j\).  Distinct restriction
components of the same leaf are disjoint by definition.  Hence \(B_j\)
is a lamination.

Because \(A_0\subset A^{N\text{-nbr}}\) and \(j<h=n+1<N\), no leaf of
\(D_j\) breaks at this step.  Therefore every leaf has at least one
retained restriction, and all its retained restrictions push under
\(f_j\) to its one untagged successor in \(D_{j+1}\).  Equivalently,

\[
 \text{every }\alpha\in D_j\text{ restricts to a leaf of }B_j,
 \qquad
 f_j(B_j)\subset D_{j+1}.                               \tag{5.0b}
\]

These are precisely the clauses of Definition 4.1.  Multiple
restriction occurrences are retained rather than selected away.
\(\square\)

Lemma 5.1 is a path-family statement.  If a downstream formalism
requires a Borel code for \(B_j\), one must additionally prove that the
full retained-component relation with both filters is Borel.  Section 9
audits that presentational issue; it is not used in the width estimate.

### Theorem 5.2 (sequential degree transfer)

Under the hypotheses of Lemma 5.1,

\[
   \mathcal W_{V_0^{\rm out}}(D_0)
   \le2^h\mathcal W_{V_h^{\rm out}}(D_h).                \tag{5.1}
\]

#### Proof

For each \(0\leq j<h\), choose the retained-occurrence realization
\(B_j\subset V_j^{\rm res}\) supplied by Lemma 5.1.  The fully
typed relations are

\[
 \iota_j(B_j)\prec D_j,
 \qquad
 f_j(B_j)\subset D_{j+1},
 \qquad
 B_j\subset f_j^*D_{j+1},                               \tag{5.1a}
\]

where \(\prec\) means that the restriction of every leaf of \(D_j\)
contains at least one leaf of \(B_j\).  The KKL domination lemma and
the full-lift identity give, in the correct surfaces,

\[
\begin{aligned}
 \mathcal W_{V_j^{\rm out}}(D_j)
 &\le \mathcal W_{V_j^{\rm res}}(B_j)\\
 &\le \mathcal W_{V_j^{\rm res}}(f_j^*D_{j+1})\\
 &=2\,\mathcal W_{V_{j+1}^{\rm out}}(D_{j+1}).
\end{aligned}                                            \tag{5.1b}
\]

Iterating the \(h\) inequalities (5.1b) proves (5.1).  No family is
silently moved between different ambient surfaces, and no one-shot
path identity is used. \(\square\)

### Corollary 5.3 (`RSC-2`)

Let

\[
   E_{n+1}:=Y_{n+1}\cup Z_{n+1}
\]

be a correctly typed output family, and let

\[
   D_0
   =
   \Phi_{n+1}^{-1}(E_{n+1})\cap A_n.
\]

Assume the stationary sequence hypotheses of Lemma 5.1.  Then

\[
 D_{n+1}=\Phi_{n+1}(D_0)\subset E_{n+1}.                \tag{5.2a}
\]

Theorem 5.2, monotonicity under the inclusion (5.2a),
\(n+1\le b+2\), and then the KL06 Parallel Law give, successively,

\[
\begin{aligned}
 \mathcal W\!\left(
   \Phi_{n+1}^{-1}(Y_{n+1}\cup Z_{n+1})\cap A_n
 \right)
 &\le
 2^{n+1}\mathcal W(Y_{n+1}\cup Z_{n+1})\\
 &\le
 2^{b+2}
 \bigl(
   \mathcal W(Y_{n+1})+\mathcal W(Z_{n+1})
 \bigr).
\end{aligned}                                             \tag{5.2}
\]

Thus `RSC-2` holds
with

\[
   D_b=2^{b+2},\qquad C_b=0,                              \tag{5.3}
\]

for every declared stationary sequence satisfying Lemma 5.1.

This is the main positive result of this note.

### Corollary 5.4 (transfer form of `RSC-1`)

For any output omission

\[
   O_{n+1}:=G_{n+1}\setminus R_{n+1},
\]

the same proof gives

\[
   \mathcal W\!\left(
      \Phi_{n+1}^{-1}(O_{n+1})\cap A_n
   \right)
   \le
   2^{b+2}\mathcal W(O_{n+1}).                           \tag{5.4}
\]

Equation (5.4) is a transfer theorem, not `RSC-1`: it gives a bounded
right side only after

\[
   \mathcal W(O_{n+1})=O_b(1)                            \tag{5.5}
\]

has been proved independently.

## 6. Saturation and maximality

Let \(C_{n+1}\subset R_{n+1}\) be the selected central output Wave.
Define the full occurrence saturation

\[
   A'_{n+1}
   :=
   \Phi_{n+1}^{-1}(C_{n+1})\cap A_n.                     \tag{6.1}
\]

This is the correct response to hidden output multiplicity.  If a
retained and a discarded occurrence have the same untagged central
image, (6.1) retains both.  Hence an untagged collision does not create
an artificial discarded class.

However, saturation proves no width bound by itself.  Two additional
facts are needed:

1. **admissibility:** \(A'_{n+1}\) is a Borel subwave and
   \(F_*^{n+1}A'_{n+1}=C_{n+1}\);
2. **extension:** the chosen stationary continuation \(A_{n+1}\)
   contains \(A'_{n+1}\).

The phrase “the maximal subwave” in KKL line 1548 is insufficient for
the second fact if “maximal” means only inclusion-maximal.  Two
incomparable eligible continuations need not contain one another.
It is enough to prove either:

- a greatest eligible continuation exists; or
- there is a specified maximal extension constructed **from**
  \(A'_{n+1}\).

Once this is done,

\[
   A_n\setminus A_{n+1}
   \subset
   A_n\setminus A'_{n+1},                                \tag{6.2}
\]

and the exact two-charge partition from the source reconstruction can
be used.

Thus saturation removes the collision ambiguity, while an extension
lemma removes the maximality ambiguity.  Neither supplies (5.5).

## 7. Why the general degree-\(d\) pushforward lemma does not prove `RSC-1`

KKL's general pushforward lemma has the aggregate form

\[
   \mathcal W(Q)
   \le
   d\,\mathcal W(R)+2d                                  \tag{7.1}
\]

for one extracted output lamination \(R\subset f_*Q\).  Even when all
objects are Borel and occurrence-saturated, (7.1) does not imply

\[
   \mathcal W\!\left(
     \Phi^{-1}(f_*Q\setminus R)
   \right)=O_d(1).                                       \tag{7.2}
\]

The obstruction is not algebraic subtlety: the coefficient \(d\) can
pay for an arbitrarily wide omitted parallel coordinate.

### Countermodel 7.1 (degree two, saturation, maximality, unbounded omission)

Fix an integer \(r\ge1\).  In a finite-type hyperbolic target surface
\(Y_r\), arrange \(r\) pairwise-disjoint four-holed planar blocks.
Inside block \(k\), choose two unit-width quadrilateral families,
denoted \(H_k\) and \(V_k\), with transverse arc classes.  Require:

1. every leaf of the foliation carried by \(H_k\) crosses every leaf
   of the foliation carried by \(V_k\);
2. quadrilaterals with different indices are supported in disjoint
   subsurfaces.

Joining the blocks by thin corridors makes \(Y_r\) connected without
changing the displayed incidences.  Let

\[
   R_r:=\bigsqcup_{k=1}^r\Gamma(H_k),
   \qquad
   O_r:=\bigsqcup_{k=1}^r\Gamma(V_k).
\]

The equality case of the Parallel Law gives

\[
   \mathcal W(R_r)=r,
   \qquad
   \mathcal W(O_r)=r.                                    \tag{7.3}
\]

The union \(R_r\cup O_r\) is not a lamination.  Moreover, \(R_r\) is
inclusion-maximal among sublaminations of that union, because every
leaf in \(O_r\) crosses the corresponding \(H_k\)-family.

Choose a connected degree-two unbranched cover

\[
   p:X_r\longrightarrow Y_r
\]

which is trivial over the displayed rectangles; the two sheets may be
joined outside those rectangles.  In \(X_r\), take:

- the sheet-zero lifts of all \(R_r\) leaves; and
- the sheet-one lifts of all \(O_r\) leaves.

These form one source lamination \(Q_r\).  Their supporting rectangles
are pairwise disjoint in \(X_r\), so

\[
   \mathcal W(Q_r)=2r.                                   \tag{7.4}
\]

Their untagged image is \(R_r\cup O_r\).  Select \(R_r\) as the maximal
output lamination.  The degree-two aggregate inequality is satisfied:

\[
   \mathcal W(Q_r)=2r
   \le2\mathcal W(R_r)+4=2r+4.                           \tag{7.5}
\]

Now saturate the retained source by taking every occurrence mapping
into \(R_r\).  This keeps exactly the sheet-zero \(R_r\)-lifts.  The
discarded occurrence family is the sheet-one lift of \(O_r\), and hence

\[
   \mathcal W\!\left(
      \Phi^{-1}\bigl((R_r\cup O_r)\setminus R_r\bigr)
   \right)
   =r.                                                    \tag{7.6}
\]

The right side tends to infinity while:

- the covering degree stays equal to two;
- the selected output is maximal;
- the retained source is fully occurrence-saturated; and
- the aggregate degree-two inequality remains true.

This is an analytic extremal-width countermodel, not a claim that the
configuration occurs in an actual stationary quadratic block.  Its
logical consequence is exact: bounded degree, aggregate pushforward,
saturation, and maximality cannot by themselves prove `RSC-1`.

The growing datum in the model is the number \(r\) of coherent
intersection coordinates.  Therefore the replacement hypothesis must
control that coordinate count or charge its total width.

## 8. What the Dudko--Lyubich annular proof does provide

The native Dudko--Lyubich lemma assumes:

1. a degree-\(m\) covering of closed annuli;
2. one fixed boundary interval \(J\); and
3. one genuine Wave above that same \(J\).

Its proof partitions the Wave into dyadic deck-span classes

\[
   \mathcal S
   =
   \mathcal S^0\dot\cup
   \mathcal S^1\dot\cup\cdots\dot\cup\mathcal S^T,
   \qquad
   T=O(1+\log m),
\]

bounds every \(\mathcal S^t\), \(t>0\), by an absolute constant, and
removes one final constant-width outer buffer from \(\mathcal S^0\).
If \(\mathcal B^0\subset\mathcal S^0\) denotes that final buffer, the
actual deletion satisfies

\[
 \mathcal S\setminus\mathcal S^{\rm new}
 \subset
 \mathcal B^0\cup\bigcup_{t=1}^T\mathcal S^t.
\]

The Parallel Law therefore gives the stronger source-relative form

\[
   \mathcal W(\mathcal S\setminus\mathcal S^{\rm new})
   \le c_{\rm DL}(1+\log m),                             \tag{8.1}
\]

not merely an aggregate comparison between
\(\mathcal W(\mathcal S)\) and
\(\mathcal W(\mathcal S^{\rm new})\).
This conclusion comes from the proof's disjoint deletion classes.  It
does not follow algebraically from the displayed aggregate inequality
\(\mathcal W(\mathcal S^{\rm new})
\ge\mathcal W(\mathcal S)-O(\log m)\).

### Measurability of the native partition

For one genuine rectangular Wave whose leaf set is already Borel in a
standard transverse parametrization, choose its transverse leaf
coordinate.  In the annular universal cover:

1. the two lifted endpoint maps vary monotonically along that
   coordinate;
2. the deck-span integer is therefore an integer-valued Borel function;
3. each dyadic span class is Borel; and
4. an outer buffer is a Borel initial or terminal interval in the
   transverse coordinate.

Thus the classes in (8.1) form a genuine measurable partition.  The
Parallel Law applies to the discarded union, and each discarded leaf
is charged once.

This is a conditional measurability verification, not a measurability
theorem imported from the DL text.  The published lemma does not set up
a standard-Borel path space or prove that an arbitrary KKL Wave admits
the required transverse Borel parametrization.  Those facts belong to
the residual extraction theorem.

For the one-step KKL covering, \(m=2\), so one coherent packet loses at
most one absolute constant.  If the actual stationary restriction
could be partitioned into at most \(q_b\) such packets and all
inter-packet collision loss had total width at most \(e_b\), then

\[
   \mathcal W(\text{one-step source defect})
   \le
   q_b\,c_{\rm DL}(1+\log2)+e_b.                         \tag{8.2}
\]

What is absent from the locked source is the theorem supplying
\(q_b\) and \(e_b\), and proving that the surviving images assemble
into the one typed Wave needed by the stationary decomposition.

The cyclic-cover counterexample to the broad KKL Wave assertion is
excluded from (8.1) precisely because its positive-width translated
coordinates do not form one Wave above one common \(J\).  Relabeling
their union as one untagged Wave does not create the missing common
crest.

### Lemma 8.0 (exact ambient localization)

Let \(A\subset X\) be an open subdomain of a Riemann surface, and let
\(\Gamma\) be a fixed parametrized path family whose paths are
contained in \(A\).  If the same paths are admissible objects in both
ambient surfaces, then

\[
   \mathcal W_A(\Gamma)=\mathcal W_X(\Gamma).            \tag{8.2a}
\]

#### Proof

The restriction to \(A\) of any \(X\)-metric admissible for \(\Gamma\)
is still admissible and has no larger area.  Hence
\(\mathcal W_A(\Gamma)\le\mathcal W_X(\Gamma)\).
Conversely, extend any admissible metric on \(A\) by zero on
\(X\setminus A\).  It is admissible for the identical paths in \(X\)
and has the same area, so
\(\mathcal W_X(\Gamma)\le\mathcal W_A(\Gamma)\).
\(\square\)

This lemma removes any analytic comparison loss after a packet has
been realized as the *same* path family in a genuine annular
localization.  It does not prove that an abstract KKL restriction
packet has such a realization; equality of the path objects is a
geometric hypothesis that must be checked.

### Proposition 8.1 (finite coherent-packet reduction)

The following result makes precise what common-crest packetization
would prove and what it would leave open.

Let \(S\) be a one-step unbreakable Wave in
\(V^{\rm out}\), and let

\[
 \Phi:S\longrightarrow G=F_*S
\]

be its unique untagged output map.  Suppose the following data have
actually been constructed.

1. There is a Borel disjoint source partition
   \[
      S=E_0\dot\cup S_1\dot\cup\cdots\dot\cup S_q,
      \qquad
      \mathcal W(E_0)\le e_0.                            \tag{8.3}
   \]
2. For every \(a\), there is a Borel retained-occurrence selector
   \[
      s_a:S_a\longrightarrow B_a\subset V^{\rm res}
   \]
   satisfying
   \[
      s_a(\alpha)\subset\iota^*\alpha,
      \qquad
      f(s_a(\alpha))=\Phi(\alpha).                       \tag{8.4}
   \]
3. Each \(B_a\) is a genuine common-crest Wave in an annular
   localization \(A_a\), above one fixed boundary interval \(J_a\).
   The restriction of \(f\) is a degree-\(m_a\) annular cover with
   \(m_a\le2\), and widths of subfamilies of \(B_a\) computed in
   \(A_a\) agree with their widths in \(V^{\rm res}\).
4. Native Dudko--Lyubich pruning produces a Borel subwave
   \(B_a^+\subset B_a\) such that
   \[
      f|_{B_a^+}\text{ is injective},
      \qquad
      \mathcal W(B_a\setminus B_a^+)\le c_{\rm DL}.      \tag{8.5}
   \]
5. The output packets
   \[
      R_a:=f(B_a^+)
   \]
   are pairwise compatible: any two leaves belonging to distinct
   packets are disjoint or are the same untagged leaf.  In addition,
   all \(R_a\) have the common output base/crest data needed for
   \[
      R:=\bigcup_{a=1}^qR_a                              \tag{8.6}
   \]
   to be one correctly typed Wave.

Then

\[
   \mathcal W\bigl(\Phi^{-1}(G\setminus R)\bigr)
   \le e_0+q\,c_{\rm DL}.                                \tag{8.7}
\]

#### Proof

Put

\[
 L_a:=B_a\setminus B_a^+,
 \qquad
 D_a:=s_a^{-1}(L_a).
\]

For every \(\alpha\in D_a\), the restriction
\(\iota^*\alpha\) contains the leaf \(s_a(\alpha)\in L_a\).  The KKL
domination lemma and (8.5) therefore give

\[
   \mathcal W(D_a)\le\mathcal W(L_a)\le c_{\rm DL}.
   \tag{8.8}
\]

If
\(\alpha\notin E_0\cup\bigcup_aD_a\), then \(\alpha\in S_a\) for one
\(a\), \(s_a(\alpha)\in B_a^+\), and hence

\[
   \Phi(\alpha)=f(s_a(\alpha))\in R_a\subset R.
\]

Consequently,

\[
 \Phi^{-1}(G\setminus R)
 \subset E_0\cup\bigcup_{a=1}^qD_a.                     \tag{8.9}
\]

The Parallel Law, (8.3), and (8.8) yield (8.7).  Notice that a discarded
restriction whose output also occurs in \(R\) does not enter the
left-hand side of (8.7); occurrence saturation can only improve the
bound. \(\square\)

### Corollary 8.2 (bounded collision defect)

Clause 5 may be replaced by the following weaker statement.  There are
subfamilies \(K_a\subset S_a\setminus D_a\) such that

\[
 \mathcal W\left(\bigcup_aK_a\right)\le e_{\rm coll},    \tag{8.10}
\]

and the packet images remaining after deletion of
\(s_a(K_a)\) satisfy clause 5.  Then

\[
 \mathcal W\bigl(\Phi^{-1}(G\setminus R)\bigr)
 \le e_0+q\,c_{\rm DL}+e_{\rm coll}.                    \tag{8.11}
\]

The proof is identical after adjoining \(\bigcup_aK_a\) to the
right-hand side of (8.9).

For later use, the exact residual invariant of a fixed pruned packet
system is therefore

\[
\begin{aligned}
 \Delta_{\rm coll}(\{S_a,B_a^+\})
 :=
 \inf\biggl\{
 &\mathcal W\left(\bigcup_aK_a\right):
 K_a\subset S_a\setminus D_a,\\
 &\bigcup_a f\!\left(
    B_a^+\setminus s_a(K_a)
  \right)
 \text{ is one correctly typed Wave}
 \biggr\}.
\end{aligned}                                            \tag{8.12}
\]

Here the infimum is over Borel deletions and includes the output
base/crest condition, not only absence of transverse intersections.
Proposition 8.1 and Corollary 8.2 can be summarized without loss as

\[
 \mathcal W\bigl(\Phi^{-1}(G\setminus R)\bigr)
 \le
 e_0+q\,c_{\rm DL}+\Delta_{\rm coll}+\varepsilon
 \tag{8.13}
\]

for every \(\varepsilon>0\), provided a deletion within
\(\varepsilon\) of the infimum is chosen.  Thus the required
quantitative object is a **width-weighted compatibility defect**.
Counting packet labels, intersection pairs, or sheets is not a
substitute for bounding (8.12).

### Exact conclusion of the packet test

Proposition 8.1 is a rigorous reduction of `RSC-1` to two geometric
inputs:

1. a \(b\)-uniform finite common-crest packetization, \(q\le q_b\),
   with \(e_0=O_b(1)\); and
2. pairwise output compatibility, or the bounded collision deletion
   estimate
   \(\Delta_{\rm coll}=O_b(1)\).

Neither input follows merely from
\(\ell(BL_0)\le6b\).  A leaf can have several retained restriction
occurrences, and the same central interval can support several
annular/deck coordinates.  A packet theorem must select one occurrence
per source leaf and prove that the selected restriction family really
is one DL common-crest Wave.  Likewise, finiteness of the packet list
does not bound collision loss: discarding one of two incompatible
packets can discard arbitrarily large width, as Countermodel 7.1
already demonstrates.

This also identifies the sharp frontier within Gate N1.  Once clauses
1--4 of Proposition 8.1 are proved with \(q\le q_b\), the sole
remaining `RSC-1` issue is an actual compatibility theorem for the
surviving packet images, not another covering-degree estimate.

### Gaps that packet notation must not conceal

The locked sources do not currently establish any of the following.

1. **Finite partition:** the retained-occurrence space has at most
   \(q_b\) common-crest annular packets.
2. **Exhaustion:** (8.3) covers every source leaf, up to a proved
   width-\(e_0\) family.
3. **Admissibility:** every selected \(B_a\) is a Wave in the fine
   source marking and survives the coarse-marking filter.
4. **Annular localization:** the local cover has the exact closed
   annulus and fixed-interval hypotheses of the DL lemma.
5. **Literal localization:** the annular and ambient path families are
   literally the same parametrized paths.  Once this is proved,
   Lemma 8.0 gives exact width equality; no comparison constant is
   needed.
6. **Measurability:** the partition, selector, DL deck-span classes,
   and buffer cuts are Borel in one fixed standard-Borel path model.
7. **Compatibility:** all cross-packet intersections and coincident
   untagged outputs are resolved without unbounded source deletion.
8. **Output type:** the compatible union is one Wave, not merely a
   finite union of laminations with unrelated bases.
9. **Dynamical semantics:** the output retains the required remaining
   unbreakability and creates no uncharged short leaves.

Thus the packet reduction is a proved conditional theorem, not a proof
that such packets exist in every stationary quadratic block.

## 9. Measurability audit

KL06 defines extremal width for an arbitrary path family, so Theorem
5.2 uses no Borel selector.  Lemma 5.1 takes the full retained
restriction family.  Nevertheless, the formal Gate N1 interface asks
for a standard measurable realization, and Proposition 8.1 uses Borel
packet and buffer ledgers.  The following audit isolates that additional
requirement.

### 9.1 Sufficient standard-Borel model

Use actual parametrized proper paths, with a fixed proper
reparametrization and the compact-open topology on compact
subintervals.  A sufficient setup is:

1. each proof-used lamination has a standard-Borel transverse
   parametrization;
2. the one-step retained-occurrence relation is Borel with nonempty
   countable fibers;
3. endpoint membership in every fine and coarse ideal interval is
   Borel; and
4. the terminal untagged path map is Borel on the declared
   unbreakable family.

Under item 2, the whole retained relation is a countable union of
graphs of partial Borel selectors by Lusin--Novikov.  Every such
selector is injective: if the same restriction leaf were selected for
two distinct target leaves, its \(\iota\)-image would be a subpath of
both, contradicting disjointness of distinct leaves of a lamination.
Lusin--Souslin makes each selector image Borel, and their countable
union—the full restriction family—is Borel.  The same argument applies
to one selected occurrence map used for a packet assignment.  Since
\(\iota\) is a local homeomorphism, restrictions of distinct target
leaves cannot cross in the source.

The unresolved Borel point is the premise, not the selection theorem:
the locked KKL source does not prove that the retained-occurrence
relation, with both marking filters imposed, is Borel in such a model.
This does not reopen Theorem 5.2 as an extremal-width inequality; it
blocks only a claimed Borel presentation and the measurable packet
construction needed for `RSC-1`.

### 9.2 What is not justified by a label

The following do not prove measurability:

- a sheet number attached after the fact;
- the assertion that \(F_*\alpha\) is one untagged path;
- a finite ribbon-tree route;
- an arbitrary use of the axiom of choice; or
- an equality of untagged image sets.

The KKL source defines the path operation but does not state the
standard-Borel occurrence theorem above.  Thus the analytic inequality
is proved here, while its application to every actual stationary
family still requires this measurable-realization lemma.

### 9.3 Width-zero exceptions

No family may be discarded merely because it is null for an auxiliary
transverse measure.  A permissible exceptional set must be proved to
have zero **extremal width** in the proof-used surface.  The cleanest
construction is to make all marking and buffer decisions Borel and
avoid an exceptional selector set entirely.

## 10. Exact residual theorem

The bounded-degree calculation shows that the next theorem should not
ask for another coefficient-one pushforward inequality.

### `STATIONARY_BOUNDED_DEFECT_WAVE_EXTRACTION`

For every fixed \(b\), every actual stationary Wave \(S_n\) must admit
a Borel occurrence-level construction with:

1. a Wave \(R_{n+1}\subset G_{n+1}=F_*S_n\);
2. a source defect \(D^{\rm ext}_n\subset S_n\) containing every source
   occurrence whose output is omitted from \(R_{n+1}\);
3. the uniform relative bound
   \[
      \mathcal W(D^{\rm ext}_n)\le e_b;                  \tag{10.1}
   \]
4. a disjoint typed decomposition
   \[
      R_{n+1}
      =
      C_{n+1}\dot\cup Y_{n+1}\dot\cup Z_{n+1};           \tag{10.2}
   \]
5. \(Z_{n+1}\) localized, or decomposed into at most \(z_b\) localized
   Waves with exact additive accounting;
6. inherited remaining unbreakability and either no short output birth
   or a short-birth charge included in (10.1);
7. the saturated central preimage (6.1) is a Borel admissible subwave;
   and
8. the chosen \(A_{n+1}\) is an extension of that saturated preimage.

A sufficient proof mechanism for (10.1) is:

- at most \(q_b\) coherent common-crest annular packets;
- Dudko--Lyubich source pruning on every packet;
- a Borel, occurrence-disjoint buffer ledger; and
- a proof that the width-weighted compatibility defect
  \(\Delta_{\rm coll}\) in (8.12) is \(O_b(1)\).

No scalar degree can replace the last item.

### Consequence if the residual theorem is proved

Pulling (10.1) back through the first \(n\) degree-two stages and using
Corollary 5.3 gives

\[
\begin{aligned}
 \mathcal W(A_n\setminus A_{n+1})
 &\le
 2^n e_b
 +
 2^{n+1}
 \bigl(
   \mathcal W(Y_{n+1})+\mathcal W(Z_{n+1})
 \bigr)\\
 &\le
 2^{b+1}e_b
 +
 2^{b+2}
 \bigl(
   \mathcal W(Y_{n+1})+\mathcal W(Z_{n+1})
 \bigr).
\end{aligned}                                             \tag{10.3}
\]

Once the correctly typed over/away propositions give

\[
   \mathcal W(Y_{n+1})+\mathcal W(Z_{n+1})\le k_b,
\]

(10.3) yields Gate N1 with

\[
   C_b^{\rm N1}
   =
   2^{b+1}e_b+2^{b+2}k_b.                                \tag{10.4}
\]

Every dependence in (10.4) is visible.  There is no dependence on the
satellite period \(q\), the rotation denominator, or the total marking
cardinality.

## 11. Multiplicative replacement for additive `RSC-1`

The finite stationary horizon permits a weaker transition than
\(\mathcal W(A_n\setminus A_{n+1})=O_b(1)\).  This section proves that a
finite coherent-packet theorem would instead give

\[
 \mathcal W(A_n)
 \le K_b\,\mathcal W(A_{n+1})+E_b,                      \tag{11.1}
\]

and that (11.1) is sufficient for the stationary telescope.  The
advantage is decisive: only one widest **source-preimage packet** is
continued.  Images of different packets never have to be assembled
into one lamination, so cross-packet compatibility is not required.

### Lemma 11.0 (finite typed disjointization)

Let \(R\) be a Borel Wave and suppose

\[
 R=L_1\cup\cdots\cup L_r                                \tag{11.0}
\]

is a finite Borel cover by subwaves with certified geometric types
that are hereditary under passage to subfamilies.  Define

\[
 \widehat L_1=L_1,
 \qquad
 \widehat L_j
 =
 L_j\setminus\bigcup_{i<j}L_i
 \quad(2\le j\le r).                                    \tag{11.0a}
\]

After empty families are removed, the
\(\widehat L_j\) are Borel, pairwise disjoint subwaves of the same
respective types and have union \(R\).  If \(Q\) is a source subwave
and \(\Psi:Q\to R\) is a Borel untagged path map, then
\(\Psi^{-1}(\widehat L_j)\) gives the corresponding Borel disjoint
source allocation; every nonempty preimage is a subwave because it is
a sublamination of \(Q\).

#### Proof

Finite unions, differences, and Borel preimages preserve Borelness.
The formula (11.0a) gives disjointness and exhaustion.  Every
\(\widehat L_j\) is a subfamily of \(L_j\), so the certified hereditary
type is preserved.  A subfamily of a Wave is a lamination subordinate
to the same base multi-interval and hence is a Wave.  The same argument
applies to every source preimage. \(\square\)

Ending at a fixed multi-interval, localization at one interval, and
subordination to a fixed away multi-interval are hereditary.  For an
“over \(BL_0\)” piece, heredity must be verified from the actual
common-crest construction; it is not inferred merely from a label.
Lemma 11.0 shows that overlap bookkeeping is not the real obstruction
once a finite **typed** cover is available.

### Hypothesis 11.1 (widest-preimage packet package)

For every fixed \(b\) and every stationary stage
\(0\le n<N-1\), suppose there are constants

\[
 1\le q_b,r_b<\infty,\qquad
 e_b,c_b,k_b<\infty.                                    \tag{11.2}
\]

and a Borel disjoint decomposition in the original level-zero source
surface, with every \(Q_{n,a}\) an admissible subwave,

\[
 A_n
 =
 E_n\dot\cup Q_{n,1}\dot\cup\cdots\dot\cup Q_{n,q_n},
 \qquad
 q_n\le q_b,
 \qquad
 \mathcal W(E_n)\le e_b.                                \tag{11.3}
\]

For every packet \(Q=Q_{n,a}\), require the following actual geometric
data.

1. Its \(n\)-step image
   \[
      P:=\Phi_n(Q)\subset S_n
   \]
   is a sublamination, and a retained-occurrence map
   \(s:P\to V_n^{\rm res}\) assigns to every
   \(\alpha\in P\) a restriction surviving both KKL filters, and
   \(B:=s(P)\).
2. \(B\) is one native DL common-crest annular Wave.  Native pruning
   gives a Borel subwave \(B^+\subset B\) with
   \[
      \mathcal W(B\setminus B^+)\le c_b,
      \qquad
      f_n|_{B^+}\text{ injective}.                       \tag{11.4}
   \]
3. Define, without quotienting occurrences,
   \[
   \begin{aligned}
      P^+&:=\{\alpha\in P:s(\alpha)\in B^+\},&
      P^-&:=P\setminus P^+,\\
      Q^+&:=Q\cap\Phi_n^{-1}(P^+),&
      Q^-&:=Q\setminus Q^+.
   \end{aligned}                                         \tag{11.5}
   \]
   and set
   \[
      R:=f_n(B^+)=\Phi_{n+1}(Q^+)                        \tag{11.6}
   \]
   Require \(R\) to be a Wave admitting an occurrence-disjoint
   controllability refinement
   \[
      R=R_1\dot\cup\cdots\dot\cup R_t,
      \qquad
      t\le r_b.                                         \tag{11.6a}
   \]
   Every \(R_\tau\) is a Wave with no short leaves and the remaining
   unbreakability required at stage \(n+1\).  Its source preimage
   \[
      Q_\tau
      :=
      Q^+\cap\Phi_{n+1}^{-1}(R_\tau)                    \tag{11.6b}
   \]
   is an admissible subwave, and
   \(Q^+=\dot\bigcup_{\tau=1}^tQ_\tau\).
4. Every \(R_\tau\) has exactly one certified type:

   - **central:** \(R_\tau\) ends at \(BL_0\), and \(Q_\tau\) is an
     eligible seed for a specified stationary continuation
     \(A_{n+1}\supset Q_\tau\);
   - **over:** \(R_\tau\) crests over \(BL_0\), and a separately proved
     coherent-packet version of the over-critical argument gives
     \(\mathcal W(R_\tau)\le k_b\);
   - **away:** \(R_\tau\) is localized and subordinate to
     \(\partial_{\rm C}\mathcal T\setminus BL_0\), and the KKL Shift
     argument, with unbreakability and absence of short leaves
     explicitly verified, gives
     \(\mathcal W(R_\tau)\le k_b\).

The bound in the over case is **not** imported from the printed
`prop:over critical` without repair: its published proof invokes the
false broad coefficient-one Wave lemma.  A sufficient repair is a
\(b\)-finite common-crest packetization of the next restriction of
\(R\); DL-prune its widest packet.  Every surviving output would crest
over

\[
 F_*BL_0=\partial_{\rm C}\mathcal T,
\]

and hence must be empty.  The finite-packet inequality then bounds
\(\mathcal W(R)\).  The away case uses the Shift lemma rather than the
broad Wave lemma, but still needs \(R^{\rm sh}=\varnothing\).

The typed statement in (11.6a) is stronger than the bare definition of
\(r_b\)-controllability, which only writes a Wave as a union of an
over-critical piece and localized pieces.  Once a Borel cover by the
required hereditary central/over/away types is proved, Lemma 11.0
supplies the occurrence-disjoint allocation.  What remains nonformal is
the existence and correct typing of that finite cover.

Hypothesis 11.1 is deliberately stated for the source preimages
\(Q_{n,a}\), not only for packets \(P\subset S_n\).  Choosing a packet
that is widest after pushforward need not choose a packet that carries
a definite fraction of \(\mathcal W(A_n)\).

### Theorem 11.2 (multiplicative stationary transition)

Under Hypothesis 11.1,

\[
 \mathcal W(A_n)
 \le
 K_b\,\mathcal W(A_{n+1})+E_b,
 \qquad
 K_b:=q_b r_b,                                           \tag{11.7}
\]

where one may take

\[
 E_b
 :=
 e_b+q_b2^{b+1}c_b+q_b r_b2^{b+2}k_b.                  \tag{11.8}
\]

#### Proof

Choose \(a_*\) so that

\[
 \mathcal W(Q_{n,a_*})
 =
 \max_{1\le a\le q_n}\mathcal W(Q_{n,a}),                \tag{11.9}
\]

and abbreviate the selected packet by
\(Q,P,B,B^+,P^\pm,Q^\pm,R\).
The Parallel Law and (11.3) give

\[
\begin{aligned}
 \mathcal W(A_n)
 &\le
 \mathcal W(E_n)+\sum_{a=1}^{q_n}\mathcal W(Q_{n,a})\\
 &\le
 e_b+q_b\,\mathcal W(Q).                                \tag{11.10}
\end{aligned}
\]

For every \(\alpha\in P^-\), the selected retained restriction
\(s(\alpha)\) belongs to \(B\setminus B^+\).  KKL domination and
(11.4) imply

\[
 \mathcal W(P^-)
 \le
 \mathcal W(B\setminus B^+)
 \le c_b.                                                \tag{11.11}
\]

Apply Theorem 5.2 to the \(n\)-step map from \(Q^-\subset A_n\) to
\(\Phi_n(Q^-)=P^-\).  This gives

\[
 \mathcal W(Q^-)
 \le2^n\mathcal W(P^-)
 \le2^n c_b.                                             \tag{11.12}
\]

Apply the Parallel Law to the occurrence-disjoint refinement
(11.6a)--(11.6b), and choose \(\tau_*\) so that

\[
 \mathcal W(Q_{\tau_*})
 =
 \max_{1\le\tau\le t}\mathcal W(Q_\tau).                \tag{11.13}
\]

Then

\[
\begin{aligned}
 \mathcal W(Q)
 &\le
 \mathcal W(Q^-)+\sum_{\tau=1}^t\mathcal W(Q_\tau)\\
 &\le
 2^n c_b+r_b\mathcal W(Q_{\tau_*}).                     \tag{11.14}
\end{aligned}
\]

If \(R_{\tau_*}\) is central, choose the specified continuation
\(A_{n+1}\supset Q_{\tau_*}\).  Equations (11.10) and (11.14) give

\[
\begin{aligned}
 \mathcal W(A_n)
 &\le
 e_b+q_b2^n c_b
 +q_b r_b\mathcal W(Q_{\tau_*})\\
 &\le
 K_b\mathcal W(A_{n+1})
 +e_b+q_b2^n c_b\\
 &\le K_b\mathcal W(A_{n+1})+E_b.                       \tag{11.15}
\end{aligned}
\]

Suppose instead that \(R_{\tau_*}\) is over or away.  The family
\(Q_{\tau_*}\subset A_n\) has the \((n+1)\)-step output
\(R_{\tau_*}\).  Theorem 5.2 and the noncentral bound give

\[
\mathcal W(Q_{\tau_*})
\le
2^{n+1}\mathcal W(R_{\tau_*})
\le2^{n+1}k_b.                                          \tag{11.16}
\]

Combining (11.10), (11.14), and (11.16), and using
\(2^n\le2^{b+1}\) and \(2^{n+1}\le2^{b+2}\), gives

\[
 \mathcal W(A_n)
 \le
 e_b+q_b2^{b+1}c_b+q_b r_b2^{b+2}k_b
 \le K_b\mathcal W(A_{n+1})+E_b.
\]

This is (11.7). \(\square\)

### Corollary 11.3 (finite-horizon telescope)

There are \(N-1=b+2\) transitions.  Iterating (11.7) gives

\[
 \mathcal W(A_0)
 \le
 K_b^{\,N-1}\mathcal W(A_{N-1})
 +
 E_b\sum_{r=0}^{N-2}K_b^r.                              \tag{11.17}
\]

For \(K_b=1\), the sum is \(N-1\); for \(K_b>1\), it is

\[
 \frac{K_b^{\,N-1}-1}{K_b-1}.
\]

Because \(b\) is fixed throughout the KKL Wave section, every factor
in (11.17) is an allowed \(b\)-dependent constant.  The Parallel Law
also gives

\[
 \mathcal W(A^{N\text{-nbr}})
 \le
 \mathcal W(A^{\rm sh})+\mathcal W(A_0).                \tag{11.18}
\]

Consequently, if the independently repaired terminal-alignment step
proves

\[
 \mathcal W(A_{N-1})=O_b(\mathcal W(\mathcal RF)+1),
\]

then (11.17)--(11.18) recover the conclusion needed from the stationary
paragraph.  The literal additive `RSC-1` estimate is stronger than
necessary for this finite-horizon use.

### What this route closes and what remains

Theorem 11.2 proves that the multiplicative route genuinely avoids
cross-packet compatibility.  It never unions two packet images:
unselected packets are paid for by the finite factor \(q_b\), not by an
additive discarded-width claim.

It does **not** obtain Hypothesis 11.1 from the locked sources.  The
exact remaining obligations are:

1. a \(b\)-uniform exhaustive packet count in **source-preimage
   width**, including any exceptional family \(E_n\);
2. one selected retained occurrence per leaf, surviving both marking
   filters, whose image packet is a literal DL annular common-crest
   Wave;
3. a proof that the pruned preimage \(Q^+\) is a subwave and, in the
   central case, is contained in the specified continuation
   \(A_{n+1}\);
4. a central/over/away typing theorem for the single pruned output,
   without first assembling all packet outputs;
5. preservation of no-shortness and the remaining unbreakability
   horizon;
6. a coherent-packet repair of the over-critical bound;
7. the terminal-alignment repair, including the printed
   \(A_N/A_{N-1}\) indexing defect.

The KKL notion of \(k\)-controllability plausibly supplies a finite list
of central/over/localized geometric types, and
\(\ell(BL_0)\le6b\) bounds the number of central endpoint intervals.
Neither fact alone proves clauses 1--2: a single interval can carry
several independent restriction/deck coordinates, and localization is
not the DL common-crest hypothesis.

Thus the new frontier statement is:

> Prove `STATIONARY_WIDEST_SOURCE_PACKET`, namely Hypothesis 11.1 with
> \(q_b,e_b,c_b,k_b\) independent of satellite period and marking
> cardinality.

This is strictly weaker than additive `RSC-1` and is not defeated by
the cross-packet compatibility countermodels.  It is still an open
native geometric theorem.

## 12. Adjacent-crest conveyor: audit of the one-packet route

There is a stronger possible route than Hypothesis 11.1.  It uses the
cyclic order of the limbs to create one common crest and then transports
that crest away from the critical limb:

\[
 BL_1\longmapsto BL_2\longmapsto\cdots\longmapsto BL_N.
 \tag{12.1}
\]

This route would restore the additive transition estimate.  It is not
yet a theorem from the locked text, because three boundary-order and
analytic-realization lemmas are unstated.  The exact conditional
argument follows.

### 12.1 Ordered-limb boundary lemma

Let

\[
 \mathcal C:=\partial_{\rm C}\mathcal T.
\]

The required topological input is:

> **`ORDERED_LIMB_PRIME_END_BLOCKS` (`OLPB`).**  
> The limb multi-intervals \(BL_j\) are connected prime-end blocks
> occurring on \(\mathcal C\) in the cyclic order of the planar limbs
> \(\mathcal L_j\).  If a leaf ends at \(BL_0\) and crests over some
> \(BL_j\), \(j\ne0\), then it crests over \(BL_1\) or \(BL_{-1}\).
> Moreover, if a leaf is subordinate to
> \(\mathcal C\setminus BL_0\) and crests over \(BL_m\), with
> \(1<m<q\), then one of its endpoints belongs to the bounded forward
> block between \(BL_0\) and \(BL_m\).

The underlying plane-tree statement can be proved independently.

#### Lemma 12.1A (contour blocks of a rooted plane tree)

Let \(G\) be a finite tree embedded in an oriented disk, let \(v\) be a
vertex, and let

\[
 G\setminus\{v\}=G_0\sqcup\cdots\sqcup G_{q-1}
\]

be its branches in counterclockwise order at \(v\).  On the oriented
boundary of a sufficiently small regular neighborhood of \(G\):

1. all sides supported on one \(G_j\) occur in one contiguous block;
2. those blocks occur in the cyclic order
   \(G_0,G_1,\ldots,G_{q-1}\); and
3. after the \(G_0\)-block is removed, every boundary arc crossing the
   \(G_m\)-block has one endpoint in the prefix consisting of the
   blocks \(G_1,\ldots,G_{m-1}\) and the other in the complementary
   suffix.

#### Proof

Choose pairwise-disjoint closed regular neighborhoods \(N_j\) of
\overline G_j\) which meet a small disk \(D_v\) around \(v\) in one
closed attaching interval each.  Since \(G\) is a tree, \(N_j\) has no
second attachment to \(D_v\); otherwise the two attachments together
with the path in \(G_j\) would form a cycle.  Consequently, a traversal
of \(\partial N(G)\) enters \(N_j\) through one side of its attaching
interval, traverses all boundary sides supported on \(G_j\), and exits
through the other side before it can enter another branch
neighborhood.  This proves contiguity.  The attaching intervals occur
on \(\partial D_v\) in the planar cyclic order of the branches, proving
item 2.  Removing the \(G_0\)-block turns the remaining contour into a
linearly ordered interval; item 3 is then the elementary separation
property of the \(G_m\)-subinterval. \(\square\)

The corresponding circle-arc assertion is immediate.  A boundary
parallel leaf ending in the \(G_0\)-block whose crest reaches any other
branch must leave \(G_0\) through one of its two sides, hence its crest
contains the first block met, \(G_1\) or \(G_{q-1}\).  A leaf avoiding
\(G_0\) and cresting over \(G_m\) has endpoints on opposite sides of
that block in the linear order from item 3.

Thus `OLPB` follows once one proves the bridge

> **`PRIME_END_CONTOUR_IDENTIFICATION` (`PECI`).**  
> KKL's marked prime-end component \(\mathcal C\), with the intervals
> induced by the sides of \(\widehat{\mathcal K}\), is order-isomorphic
> to the contour of a regular neighborhood of the rooted combinatorial
> Hubbard tree, and \(BL_j\) corresponds to the block of the
> \(j\)-th root branch.

For the locally connected model, `PECI` is the expected regular
neighborhood interpretation of “marking induced by the sides.”  For a
non-locally-connected filled set, the same statement must be checked
after passage to KKL's combinatorial model and then under its lift.
The locked source does not state this identification as a lemma.

Under `OLPB`, a Wave \(S\) ending at \(BL_0\) and having no short
leaves has the disjoint decomposition

\[
\begin{aligned}
 S^+
 &:=
 \{\gamma\in S:\gamma\text{ crests over }BL_1\},\\
 S^-
 &:=
 S\setminus S^+.
\end{aligned}                                           \tag{12.2}
\]

Every leaf of \(S^-\) crests over \(BL_{-1}\).  Both nonempty
subfamilies are Waves, because they are sublaminations of \(S\)
subordinate to its base.  If endpoint cyclic order is Borel, the two
pieces are Borel.

The “no short leaves” premise really follows for
\[
 A_0=A^{N\text{-nbr}}\setminus A^{\rm sh}.
\]
Indeed, if a short leaf lay outside the maximal short subwave
\(A^{\rm sh}\), adjoining that leaf would produce a larger short
subwave, a contradiction.

The KKL source gives the planar cyclic order of the limbs at line 501,
states that every \(\partial_{\rm C}\mathcal L_j\) is a multi-interval
at line 838, and uses the total count
\(|\mathcal I|\le6bq\) at line 889.  It does **not** explicitly prove
`PECI`.  Thus the abstract contour theorem is proved, while its exact
application to the KKL prime-end marking remains open.

### 12.2 Common-crest restriction and native pruning

The second required input is:

> **`COMMON_CREST_RESTRICTION_PRUNING` (`CCRP`).**  
> If \(S\) is an unbreakable Wave over a limb multi-interval \(I\),
> then the full retained restriction
> \(B=\iota^*S\), after both KKL filters, is one Wave over
> \(\iota^*I\), satisfies
> \(\mathcal W(S)\le\mathcal W(B)\), and admits an annular
> localization to which the native DL pruning proof applies.  It
> yields \(B^+\subset B\) with
> \[
>    \mathcal W(B\setminus B^+)\le c_{\rm DL},
>    \qquad f|_{B^+}\text{ injective}.                  \tag{12.3}
> \]

The analytic, non-Borel part of `CCRP` can be reduced to the locked
sources.

#### Lemma 12.2A (annular realization of the tree complement)

Assume the KKL Hubbard carrier is the finite planar tree of full vertex
continua and connecting edges described by its combinatorial Hubbard
tree.  Then \(\mathcal T\) is full, and the Carathéodory compactification
of \(\mathcal U\setminus\mathcal T\) is a closed annulus.  The same is
true for \(\mathcal T'=f^{-1}(\mathcal T)\), and

\[
 f:\mathcal U'\setminus\mathcal T'
 \longrightarrow
 \mathcal U\setminus\mathcal T
\]

is the degree-two annular covering required by the native DL lemma.

#### Proof

Every small filled Julia component is full; a point and an embedded
tree edge are full.  Order the finitely many vertex and edge continua
so that each new piece is attached to the preceding union along its
unique parent incidence.  The intersection is connected.  The planar
Janiszewski theorem implies inductively that the union of two
nonseparating compacta with connected nonempty intersection is
nonseparating.  Hence \(\mathcal T\) is full.  A full connected compact
subset of a Jordan disk has a doubly connected complement, whose
prime-end compactification is a closed annulus.  The pulled
combinatorial tree has the same acyclic incidence property, so the
argument applies to \(\mathcal T'\).  The critical point belongs to the
removed tree; therefore the quadratic covering restricts to an
unbranched degree-two cover of the complements. \(\square\)

KKL explicitly writes
\(B^{\rm nbr}=\iota^*A^{\rm nbr}\) and calls it a Wave over
\(\iota^*I\), with the domination inequality, in the proof at lines
1481--1482.  Proposition `prop:comb action` supplies the end-proper
combinatorial action used there.  A Wave over the whole limb block is
over each constituent marked interval, so Lemma 12.2A puts it exactly
in the native DL annular setting.  Section 8 derived the relative
source loss (12.3) from the disjoint classes in the native proof.

Accordingly, the remaining `CCRP` issue is a formal Borel realization
of the full restriction, deck-span classes, and buffer cut, plus
verification that the non-locally-connected lift has precisely the
tree-incidence realization assumed in Lemma 12.2A.  The broad printed
KKL Wave lemma is not used.

KKL Proposition `prop:nonbreaking` then gives

\[
 f(B^+)\text{ is a Wave over }F_*I.                     \tag{12.4}
\]

### 12.3 Repaired over-critical bound

Assume `CCRP`.  If \(Y\) is a one-step-unbreakable Wave over \(BL_0\),
then

\[
 \mathcal W(Y)\le c_{\rm DL}.                           \tag{12.5}
\]

To prove this, apply `CCRP` to get
\(C=\iota^*Y\) and \(C^+\subset C\).  By (12.4), the output
\(f(C^+)\) is a Wave over

\[
 F_*BL_0=\mathcal C.
\]

No nonempty Wave can have the whole ideal-boundary component in its
crest, because its two nonempty ends are disjoint from the crest.
Hence \(C^+=\varnothing\).  Domination and (12.3) give

\[
 \mathcal W(Y)
 \le\mathcal W(C)
 =\mathcal W(C\setminus C^+)
 \le c_{\rm DL}.
\]

Consequently, if \(S^-\) in (12.2) is two-step unbreakable, then

\[
 \mathcal W(S^-)\le3c_{\rm DL}.                         \tag{12.6}
\]

Indeed, one `CCRP` pruning maps its retained part to a Wave over

\[
 F_*BL_{-1}=BL_0.
\]

The discarded restriction has width at most \(c_{\rm DL}\); the
retained restriction is contained in the full degree-two lift of the
over-critical output.  Proposition 3.1 and (12.5) give

\[
 \mathcal W(S^-)
 \le c_{\rm DL}+2c_{\rm DL}.
\]

Thus the claim that the minus direction is bounded is correct only
after this two-stage argument.  One pruning maps \(BL_{-1}\) to
\(BL_0\); the next coherent pruning uses
\(F_*BL_0=\mathcal C\).

### 12.4 Bounded localization of the away output

Suppose \(2\le m\le N\), \(q>N\), and \(Z\) is an unbreakable Wave
subordinate to \(\mathcal C\setminus BL_0\) and over \(BL_m\).
The exact third input is:

> **`BOUNDED_FORWARD_END_LOCALIZATION` (`BFEL`).**  
> The bounded forward block from \(BL_0\) to \(BL_m\) contains at most
> \[
>    a_{b,m}\le6b(m-1)\le a_b:=6b(N-1)
> \]
> marked intervals, and every
> leaf of \(Z\) has an endpoint in one of them.

Under `PECI`, the endpoint assertion is Lemma 12.1A(3).  The forward
prefix is the union of the consecutive blocks
\(BL_1,\ldots,BL_{m-1}\), so KKL's bound
\(\ell(BL_j)\le6b\) gives the displayed cardinality.  KKL's use of
\(|\mathcal I|\le6bq\) at line 889 confirms that no additional marked
interval class is being counted outside the limb blocks.  Hence the
set-theoretic and numerical content of `BFEL` follows from `PECI`; what
remains is the Borel endpoint partition and the verification that each
localized piece meets the native Shift proposition exactly.

Assuming `BFEL`, partition \(Z\) by the marked interval containing its
forward endpoint:

\[
 Z=Z_1\dot\cup\cdots\dot\cup Z_s,
 \qquad
 s\le a_b.                                               \tag{12.7}
\]

Every \(Z_i\) is localized, subordinate to
\(\mathcal C\setminus BL_0\), and has no short leaves because it still
crests over \(BL_m\).  The KKL away-critical Shift argument, with its
end-order hypotheses checked, gives

\[
 \mathcal W(Z_i)\le c_{\rm sh}.
\]

The Parallel Law yields

\[
 \mathcal W(Z)\le a_b c_{\rm sh}.                       \tag{12.8}
\]

This is the point at which the advancing common crest removes the
unbounded marking count: \(m\le N=b+3\), so the forward endpoint lies
in a \(b\)-bounded limb window even when \(q\) is arbitrarily large.

### 12.5 One conveyor transition

Assume `CCRP`, `OLPB`, and `BFEL`.  Let \(S_n\) be a Wave satisfying

\[
\begin{aligned}
 &S_n\text{ ends at }BL_0,\\
 &S_n\text{ crests over }BL_{n+1},\\
 &S_n=S_n^{(N-n)\text{-nbr}},
 \qquad 0\le n<N-1,\\
 &q>N.
\end{aligned}                                           \tag{12.9}
\]

Apply `CCRP` and set

\[
 R_{n+1}:=f(B_n^+).
\]

By (12.4),

\[
 R_{n+1}\text{ crests over }BL_{n+2}.                  \tag{12.10}
\]

Partition it leafwise into:

- \(C_{n+1}\): leaves ending at \(BL_0\);
- \(Y_{n+1}\): remaining leaves cresting over \(BL_0\);
- \(Z_{n+1}\): all remaining leaves.

The circular-order statement in `OLPB` makes
\(Z_{n+1}\) subordinate to
\(\mathcal C\setminus BL_0\).  All three pieces inherit the common
crest \(BL_{n+2}\), hence have no short leaves.  Remaining
unbreakability gives, by (12.5) and (12.8),

\[
 \mathcal W(Y_{n+1})+\mathcal W(Z_{n+1})
 \le
 k_b
 :=
 c_{\rm DL}+a_b c_{\rm sh}.                             \tag{12.11}
\]

Let \(D_n\subset S_n\) consist of leaves not continued to the central
output.  Resolve its occurrences as

\[
\begin{aligned}
 D_n^{\rm pr}
 &:=
 \{\alpha\in D_n:
   B_n^+\cap\iota^*\alpha=\varnothing\},\\
 D_n^{\rm ext}
 &:=
 D_n\setminus D_n^{\rm pr}.
\end{aligned}                                           \tag{12.11a}
\]

For every leaf of \(D_n^{\rm pr}\), the full retained restriction has
a leaf in \(B_n\setminus B_n^+\).  KKL domination and (12.3) give

\[
 \mathcal W(D_n^{\rm pr})\le c_{\rm DL}.                \tag{12.11b}
\]

For \(\alpha\in D_n^{\rm ext}\), choose its occurrence in \(B_n^+\).
Unbreakability makes its image the unique untagged successor, and
injectivity on \(B_n^+\) prevents two retained occurrences there from
collapsing to that same successor.  The selected occurrence family
\(B_n^{\rm ext}\) is therefore a lamination satisfying

\[
 B_n^{\rm ext}
 \subset
 f^*(Y_{n+1}\cup Z_{n+1}).
\]

KKL domination, Proposition 3.1, and (12.11) give

\[
\begin{aligned}
 \mathcal W(D_n^{\rm ext})
 &\le\mathcal W(B_n^{\rm ext})\\
 &\le2\mathcal W(Y_{n+1}\cup Z_{n+1})\\
 &\le2k_b.
\end{aligned}                                           \tag{12.11c}
\]

The Parallel Law applied to (12.11a) now gives

\[
 \mathcal W(D_n)
 \le
 c_{\rm DL}+2k_b.                                       \tag{12.12}
\]

Define the continuation by full saturation:

\[
 A_{n+1}
 :=
 A_n^{\rm cc}\cap\Phi_{n+1}^{-1}(C_{n+1}),              \tag{12.13}
\]

where \(A_n^{\rm cc}\) is the current common-crest source packet and
\(\Phi_n(A_n^{\rm cc})=S_n\).  For every stage after initialization,
\(A_n^{\rm cc}=A_n\).
Then

\[
 S_{n+1}:=\Phi_{n+1}(A_{n+1})=C_{n+1}
\]

is a Wave ending at \(BL_0\), cresting over \(BL_{n+2}\), and carrying
the remaining horizon.  Saturation includes every source occurrence
with central output, so hidden duplicate outputs can only reduce the
discarded family.

Finally, apply Theorem 5.2 to the \(n\)-step preimage of \(D_n\):

\[
 \mathcal W(A_n^{\rm cc}\setminus A_{n+1})
 \le
 2^n(c_{\rm DL}+2k_b)
 \le
 2^{b+1}(c_{\rm DL}+2k_b).                              \tag{12.14}
\]

This is the desired additive transition.

### 12.6 Initialization and exact verdict

For \(A_0=A^{N\text{-nbr}}\setminus A^{\rm sh}\), use (12.2).  The
minus family costs at most \(3c_{\rm DL}\) by (12.6).  Apply the
conveyor transition with
\(A_0^{\rm cc}=A_0^+\), whose crest is \(BL_1\), and define
\(A_1\) only from that packet.  Even if a minus occurrence has the same
untagged central output, it is deliberately excluded and is already
charged by (12.6).  Hence

\[
 \mathcal W(A_0\setminus A_1)
 \le
 3c_{\rm DL}+c_{\rm DL}+2k_b.                           \tag{12.15}
\]

For \(n\ge1\), use \(A_n^{\rm cc}=A_n\).  Induction then
produces

\[
 S_n\text{ ending at }BL_0
 \quad\text{and cresting over }BL_{n+1}
\]

through \(n=N-1\), with the uniform additive loss (12.14).

Therefore the adjacent-crest route would prove Gate N1 in the
high-period range \(q>N=b+3\) once the following are proved on the
actual KKL carriers:

1. `PECI`, hence `OLPB`, including Borel cyclic-order splitting;
2. `CCRP`, including literal annular localization and the native
   source-relative DL buffer construction;
3. `BFEL`'s Borel partition and every Shift-lemma end-order
   hypothesis (its topological endpoint statement and
   \(6b(N-1)\) count follow from `PECI`);
4. exact central saturation (12.13) as an admissible subwave through
   the full horizon.

The route does not silently solve small periods.  If \(q\le N\), the
crest sequence (12.1) can hit \(BL_0\) modulo \(q\), so a separate
bounded-period theorem is required.  In the global KKL application
the Wave section sits inside the high-type-near-degenerate argument,
where the threshold on \(q\) may be enlarged to force \(q>N\), and the
bounded-\(q\) types may be absorbed into the finite family removed
before that argument.  This case split must be stated explicitly:
Gate N1 as reconstructed in Section 7 presently quantifies uniformly
over all \(q\).

The audit verdict is thus:

```text
adjacent-crest algebra and width accounting: proved conditional
minus-packet bound:                         proved conditional (two-stage)
plane-tree contour lemma:                  proved
prime-end contour bridge PECI:             open
ordered split OLPB:                        conditional on PECI
common-crest analytic realization CCRP:    open
CCRP annular/width core:                   proved under tree-incidence model
CCRP Borel/nonlocal lift bridge:           open
BFEL topology/count:                       conditional on PECI
BFEL Borel/Shift realization:              open
small-period branch q<=b+3:                open
Gate N1:                                   open
```

This route is materially sharper than the generic packet program:
after initialization it uses one packet per stage and would recover
additive, not merely multiplicative, control.

## 13. Adversarial checks

### 13.1 Duplicate untagged images

Two source occurrences may have the same untagged image.
Proposition 4.2 remains valid because both lie in the full lift family.
Saturation (6.1) retains both if the common image is central.

### 13.2 Opposite sheets or endpoint orientations

No sheet or orientation label is treated as a distinct output path.
The degree factor counts source lifts before untagging.

### 13.3 Aggregate compensation

Countermodel 7.1 shows that an arbitrarily wide omitted family can be
paid for by the factor \(d\mathcal W(R)\) in an aggregate estimate.
No subtraction of aggregate bounds occurs in this note.

### 13.4 Unbounded packet count

Even an absolute loss per coherent packet sums to an unbounded loss if
the number of packets is unbounded.  Equation (8.2) explicitly retains
the packet count.

### 13.5 Arbitrary inclusion-maximal continuation

An arbitrary maximal continuation need not contain the saturated
central preimage.  The extension clause in Section 6 is independent of
the width transfer.

### 13.6 Sequential versus one-shot paths

The proof uses the canonical full restriction at each sequential stage
and does not infer path-level equality from KKL's interval-level identity
\(f_*^h\iota_h^*I=F_*^hI\).

### 13.7 Non-lamination output

Proposition 3.1 applies to arbitrary target path families, but the next
iteration and the KKL over/away propositions require actual
laminations.  The bounded-defect extraction theorem must construct
them; the degree identity does not.

### 13.8 Fine/coarse filter

Only restrictions surviving both KKL filters enter Definition 4.1.
A topological lift that is discarded by either filter cannot carry the
domination inequality.

### 13.9 Source buffer counted twice

The Dudko--Lyubich classes and final buffer are disjoint occurrence
classes.  The Parallel Law is used in its upper-bound direction.
No leaf is assigned to two buffer charges.

### 13.10 Circularity

No use is made of Proposition `prop:into the critical limb`, its
stationary telescope, or the desired conclusion of Gate N1.

### 13.11 Widest output packet

Choosing the packet with largest width in \(S_n\) is insufficient:
the \(n\)-step relation need not preserve relative packet widths.
Theorem 11.2 maximizes the widths of the source preimages
\(Q_{n,a}\subset A_n\).

### 13.12 Finite packet count versus additive loss

Discarding \(q_b-1\) packets can have arbitrarily large additive width.
Theorem 11.2 makes no additive claim; the entire discarded mass is paid
for by the multiplicative factor \(K_b=q_b r_b\).  This is why the
cyclic-cover compatibility countermodels do not refute (11.7).

### 13.13 Hidden use of conformal invariance

The noncentral estimate does not infer
\(\mathcal W(B^+)=\mathcal W(R)\) merely from injectivity on a set of
leaves.  It applies Theorem 5.2 directly to the selected source
preimage \(Q_{\tau_*}\) and its \((n+1)\)-step output
\(R_{\tau_*}\).

### 13.14 Published over-critical bound

The printed `prop:over critical` is not imported as proved because its
proof invokes the false broad Wave lemma.  Hypothesis 11.1 isolates a
coherent-packet repair as an independent premise.

### 13.15 Finite-horizon coefficient growth

The factor \(K_b^{b+2}\) in (11.17) would be unacceptable in a theorem
requiring constants uniform in \(b\).  The KKL Wave section fixes \(b\)
before declaring its constants, so it is admissible for this local
stationary use.  It remains independent of satellite period, rotation
denominator, and marking cardinality.

### 13.16 Limb versus marked interval

\(BL_j\) is a multi-interval, not one marked interval.  Section 12 uses
one constituent interval only after requiring that the full restriction
is a Wave over the whole block and after isolating the actual annular
localization in `CCRP`.

### 13.17 One pruning of the minus direction

One pruning sends the \(BL_{-1}\)-crest to a \(BL_0\)-crest; it does
not make the output empty.  Equation (12.6) uses a second coherent
pruning and therefore checks the two-step unbreakability horizon.

### 13.18 Crest wraparound

The identity \(F_*BL_j=BL_{j+1}\) has indices in
\(\mathbb Z/q\mathbb Z\).  The conveyor is used only under \(q>N\);
otherwise it can hit \(BL_0\) and the argument changes type.

### 13.19 Hidden intervals between limb blocks

The estimate \(a_b=O(bN)\) is not inferred solely from
\(\ell(BL_j)\le6b\).  `BFEL` must audit every marked interval in the
prime-end block between consecutive limbs, including any access based
at \(\alpha_F\).

### 13.20 Heredity of a common crest

Central/over/away subfamilies are asserted to inherit the advancing
crest only after the actual leafwise cyclic-order statement is proved.
A coarse output label is insufficient.

## 14. Final determination

The bounded-degree route produces a genuine advance:

\[
\boxed{
 \mathcal W\!\left(\Phi_h^{-1}(E)\right)
 \le 2^h\mathcal W(E)
}
\]

for every correctly typed output family \(E\), under the explicit
stationary nesting and unbreakability hypotheses of Lemma 5.1.  This
proves the analytic content of `RSC-2` and makes occurrence
multiplicity harmless.  A Borel coding of the full restriction relation
is a separate formal-interface obligation, not an assumption in this
inequality.

It does not yet prove additive `RSC-1`.  There are now three rigorously
separated forward routes.

1. **Additive route:** construct, from the actual \(S_n\), a Borel Wave
   output whose omitted **source occurrence** family has \(O_b(1)\)
   width, with a uniformly bounded coherent-packet/collision ledger.
2. **Multiplicative route:** prove
   `STATIONARY_WIDEST_SOURCE_PACKET` (Hypothesis 11.1).  Theorem 11.2
   then replaces additive `RSC-1` by the finite-horizon recurrence
   \[
      \mathcal W(A_n)
      \le q_b\mathcal W(A_{n+1})+E_b,
   \]
   which is already sufficient for the stationary conclusion.
3. **Adjacent-crest route:** prove `OLPB`, `CCRP`, and `BFEL` from
   Section 12.  The conveyor calculation then gives the actual additive
   estimate with one common-crest packet per stage for \(q>b+3\);
   bounded periods require a separate branch.

The general degree-\(d\) pushforward lemma, saturation, and maximality
cannot replace either geometric theorem.  Countermodel 7.1 proves the
logical failure sharply.  The multiplicative route is the weaker and
currently more promising target because it does not require
cross-packet compatibility.

The proof-status ledger internal to this note is:

| item | status | unproved input, if any |
|---|---|---|
| Proposition 3.1, full-lift identity | proved | none |
| Proposition 4.2, one-step transfer | proved conditional | an actual retained-occurrence realization |
| Lemma 5.1, full-restriction realization | proved | declared stationary nesting and unbreakability |
| Theorem 5.2, sequential transfer | proved | Lemma 5.1 supplies the realization |
| `RSC-2` analytic inequality | proved | a correctly typed final output family |
| Lemma 8.0, ambient localization | proved | literal identity of the localized path family |
| Proposition 8.1, packet reduction | proved conditional | clauses 1--5 of that proposition |
| degree + saturation + maximality \(\Rightarrow\) `RSC-1` | refuted | Countermodel 7.1 |
| `RSC-1` for native stationary Waves | open | bounded packet exhaustion and \(\Delta_{\rm coll}=O_b(1)\) |
| Theorem 11.2, multiplicative transition | proved conditional | `STATIONARY_WIDEST_SOURCE_PACKET` |
| multiplicative stationary replacement | open | packet exhaustion, one-packet analytic realization/type, no-short horizon, over-critical and terminal repairs |
| plane-tree contour lemma | proved | none |
| adjacent-crest conveyor | proved conditional | `PECI`, `CCRP`, Borel/Shift realization, small-period branch |
| Gate N1 | open | one of the three extraction routes plus all stated output/horizon clauses |

Accordingly:

```text
RSC-2 analytic transfer: proved from stationary nesting/unbreakability
RSC-1:                   open
widest-source-packet:    open
adjacent-crest conveyor: open
Gate N1:                 open
KKL stationary repair:   open
VAAPC-I:                 open
UPTCR:                   open
MLC:                     open
```

## 15. Post-correction audit of the leafwise directed proof

This section audits the later candidate

```text
kkl_stationary_relative_wave_continuation.md
```

only at the three interfaces requested for Gate N1:

1. conversion of a KKL full restriction into a native
   Dudko--Lyubich annular Wave;
2. the central/over/away partition and every hypothesis of the KKL
   Shift estimate; and
3. the stationary horizon and the \(q\)-wrap indices.

The audit distinguishes the **full restriction**
\(\iota^*S\) from its **directed restriction**
\(B_I(S)\).  This distinction is not cosmetic.  The first need not be
one DL Wave; the second is the correct proof object.

### 15.1 Exact counterexample to the full-restriction inference

Let \(\overline A\) be a prime-end closed annulus and let
\(C\) be one boundary circle.  Choose two disjoint open end intervals
\(E_-,E_+\subset C\).  Their complement has two nonempty connected
arcs \(J_+\) and \(J_-\).

Choose four endpoints in cyclic order

\[
 a_-,a_+,b_+,b_-,
\]

with \(a_-,a_+\in E_-\) and \(b_+,b_-\in E_+\).  There are two
pairwise-disjoint proper simple crosscuts:

- \(\beta_+\), joining \(a_+\) to \(b_+\) and cutting off the
  \(J_+\)-side; and
- \(\beta_-\), joining \(b_-\) to \(a_-\) and cutting off the
  \(J_-\)-side.

They can be chosen in disjoint collars of the two complementary
boundary arcs.  Thus

\[
 L:=\{\beta_+,\beta_-\}
\]

is a lamination.  In the printed KKL definitions its smallest connected
base is the whole circle \(C\), its two ends are \(E_-\) and \(E_+\),
and its crest contains both \(J_+\) and \(J_-\).  Consequently \(L\) is
a KKL Wave over \(J_+\).

But DL `Feigen.tex` 2813 is leafwise: every curve in a DL Wave above
\(J_+\) must cut off the \(J_+\)-side.  The curve \(\beta_-\) does not.
Therefore

\[
 \boxed{
   \text{KKL Wave over }J
   \ \not\Longrightarrow\
   \text{one leafwise DL Wave above }J .
 }
 \tag{15.1}
\]

This is an exact annular counterexample to the assertion

> “Apply KKL 1477 to each singleton and unite; every retained
> component goes above the same pulled interval.”

KKL 1477 supplies an aggregate KKL Wave.  It does not rule out the
two opposite boundary directions in this example.  In particular, the
full family \(B=\iota^*S\) must not be passed directly to DL 2821--2842.

### 15.2 Finite directionalization is the exact replacement

For a proper simple crosscut \(\beta\) of a closed annulus, write

\[
 \beta\uparrow J
\]

when the boundary-side component cut off by \(\beta\) contains the
connected interval \(J\) on its prime-end boundary.  This is exactly
the leafwise DL predicate.

#### Lemma 15.1 (finite directionalization)

Let \(L\) be a finite KKL Wave whose aggregate crest contains a
connected interval \(J\).  Then

\[
 L[J]:=\{\beta\in L:\beta\uparrow J\}
 \ne\varnothing .
 \tag{15.2}
\]

Moreover \(L[J]\) is a native DL Wave above \(J\).

#### Proof

Every endpoint interval of every leaf of \(L\) belongs to one of the
two aggregate KKL ends.  Since \(J\) lies in the aggregate crest, none
of those endpoint intervals meets \(J\).

Let \(B_\beta\subset C\) be the connected boundary-side base of one
leaf.  Both end intervals of \(B_\beta\) avoid connected \(J\).
Therefore exactly one of the following holds:

\[
 J\subset B_\beta^\circ,
 \qquad\text{or}\qquad
 B_\beta\cap J=\varnothing .
 \tag{15.3}
\]

Indeed, a proper nonempty overlap without containment would put one
end interval of \(B_\beta\) inside \(J\), contrary to the preceding
paragraph.

If the second alternative held for every leaf, every \(B_\beta\)
would lie in the connected complementary boundary interval
\(C\setminus J\).  Since \(L\) is finite, its smallest connected common
base would also lie in \(C\setminus J\).  This contradicts
\(J\subset\operatorname{crest}(L)\).  Hence at least one leaf satisfies
the first alternative, proving (15.2).

The family \(L[J]\) is a sublamination and every one of its curves goes
above the same \(J\).  This is precisely DL's definition of a Wave
above \(J\). \(\square\)

The finiteness needed here is automatic for a singleton stationary
source leaf.  If \(\gamma\) is unbreakable, every retained component of
\(\iota^{-1}(\gamma)\) maps under the degree-two cover \(f\) to the same
parametrized successor.  There are at most two lifts of that successor.
Thus the complete filtered singleton restriction \(B_\gamma\) is
finite.

Let \(S\uparrow I\) leafwise, put \(J=\iota^*I\), and define

\[
 B_I(S):=
 \left\{
  \beta\in\iota^*S:
  \begin{array}{l}
   \beta\text{ survives both KKL filters},\\
   \beta\uparrow J
  \end{array}
 \right\}.
 \tag{15.4}
\]

For each \(\gamma\in S\), KKL 1477 applied to the unbreakable
singleton gives a nonempty finite KKL Wave over the pullback of the
singleton crest.  Proposition `prop:pullback description` is monotone
on connected boundary subsets, so
\[
 \iota^*I
 \subset
 \iota^*(\operatorname{crest}\{\gamma\});
\]
hence the same \(B_\gamma\) is a KKL Wave over \(J=\iota^*I\).
Lemma 15.1 gives at least one member of
\(B_\gamma\cap B_I(S)\).  Consequently:

1. every source leaf has a represented occurrence in \(B_I(S)\);
2. \(B_I(S)\) is a sublamination of the full restriction;
3. it is one native DL Wave above the fixed \(J\); and
4. KKL domination gives
   \[
    \mathcal W(S)\leq\mathcal W(B_I(S)).
    \tag{15.5}
   \]

No occurrence selector is used: all retained components satisfying the
leaf predicate are kept.  Applying the native DL pruning lemma to
\(B_I(S)\), rather than to \(\iota^*S\), is therefore a complete repair
of the obstruction (15.1).

### 15.3 Occurrence-resolved one-step charge

Let

\[
 B^\sharp\subset B_I(S)
\]

be the DL-retained subwave, let

\[
 R=f(B^\sharp),
\qquad
 \mathcal W(B_I(S)\setminus B^\sharp)\leq c_{\rm DL},
\]

and let \(C\subset R\) be the central output.  Put

\[
 E:=R\setminus C,
\qquad
 B_E:=B^\sharp\cap f^{-1}(E).
 \tag{15.6}
\]

For the source leaves having a retained occurrence over \(E\), KKL
domination applies to \(B_E\).  The only covering estimate used is

\[
 B_E\subset f^*E
 \quad\Longrightarrow\quad
 \mathcal W(B_E)
 \leq
 \mathcal W(f^*E)
 =
 2\mathcal W(E).
 \tag{15.7}
\]

The equality in (15.7) concerns the **full lift** \(f^*E\), not
\(B_E\).  No equality or coefficient-one invariance is asserted for
the retained occurrence family.  Hence

\[
 \mathcal W(\text{source discarded over }E)
 \leq 2\mathcal W(E).
 \tag{15.8}
\]

Together with the DL source discard, this is the exact one-step charge

\[
 c_{\rm DL}+2\mathcal W(E).
 \tag{15.9}
\]

### 15.4 Central/over/away partition: complete hypothesis audit

The corrected proof does not obtain controllability by treating an
aggregate over-\(BL_0\) Wave as leafwise.  It uses the proof of KKL
Lemma `lem:pushing controllable` at 1403--1411.

That proof classifies each output leaf separately:

1. it has an endpoint in one of the boundedly many intervals of
   \(BL_{[-b,b]}\); or
2. its singleton Wave is over \(BL_0\).

Starting with a Wave ending at \(BL_0\), partitioning its chosen
\(BL_0\)-endpoint among at most

\[
 \ell(BL_0)\leq6b
\]

marked intervals makes the input \(6b\)-controllable.  The one-step
KKL proof therefore supplies at most

\[
 \eta_b:=6b+4b(2b+1)
 \tag{15.10}
\]

localized output modules and one **leafwise** over-\(BL_0\) module.
Disjointize the finite cover by assigning a leaf to its first eligible
module.

Suppose in addition that the output \(R\):

- is one-step unbreakable; and
- satisfies \(R\uparrow BL_k\) leafwise for one \(k\ne0\).

Within each disjoint module assign leaves in the order

\[
 \begin{array}{lll}
 C:&\text{an endpoint belongs to }BL_0;&\text{central},\\
 Y:&\text{the singleton goes above }BL_0;&\text{over-critical},\\
 Z_r:&\text{all remaining leaves in localized module }r.&\text{away}.
 \end{array}
 \tag{15.11}
\]

This is exhaustive.  The leafwise over module contributes no residual
after \(Y\) is removed.  Every other residual lies in a localized
module.

For one residual leaf, neither endpoint belongs to connected \(BL_0\).
Its connected singleton base either contains all of \(BL_0\), in which
case it would have entered \(Y\), or avoids \(BL_0\).  Thus every
\(Z_r\) is both localized and subordinate to

\[
 \partial_{\rm C}\mathcal T\setminus BL_0.
 \tag{15.12}
\]

The KKL away-from-critical proposition at 1524--1532 now has all of its
native hypotheses:

| Shift hypothesis | verification |
|---|---|
| \(Z_r\) is a Wave | it is a sublamination of one localized module |
| localized | inherited from that module |
| subordinate to \(\partial_{\rm C}\mathcal T\setminus BL_0\) | (15.12) |
| one-step unbreakable | inherited from \(R\) |
| no short subwave | every leaf still satisfies \(Z_r\uparrow BL_k\), \(k\ne0\) |

Hence

\[
 \mathcal W(Z_r)\leq c_{\rm away}.
 \tag{15.13}
\]

The family \(Y\) is a lamination all of whose leaves go above the same
\(BL_0\).  The directed critical estimate obtained from Lemma 15.1 and
one DL pruning gives

\[
 \mathcal W(Y)\leq c_{\rm crit}.
 \tag{15.14}
\]

The Parallel Law yields

\[
 \mathcal W(R\setminus C)
 \leq
 c_{\rm crit}+\eta_b c_{\rm away}
 =:e_b.
 \tag{15.15}
\]

Thus the central/over/away decomposition and the Shift application
pass the adversarial audit.  The essential source fact is that KKL
1403--1411 constructs the over class leaf by leaf; an arbitrary
aggregate KKL over-Wave would not suffice.

### 15.5 Horizon and wrap audit

Put

\[
 N=b+3.
\]

There are exactly \(N-1=b+2\) transitions, indexed by

\[
 0\leq n\leq N-2=b+1.
 \tag{15.16}
\]

At transition \(n\), every current source leaf has

\[
 N-n\geq2
 \tag{15.17}
\]

remaining unbreakable steps.  After the transition, every output leaf
has

\[
 N-n-1\geq1.
 \tag{15.18}
\]

Therefore:

- the precritical \(BL_{q-1}\to BL_0\) charge has the two steps it
  needs; and
- the critical and away estimates on the output have the one step they
  need.

No transition at \(n=N-1\) is made.

For \(q=2\), the two adjacent blocks coincide:

\[
 BL_1=BL_{-1}=BL_{q-1}.
\]

The initial family is charged by the two-step precritical estimate and
the protected continuation is empty.

For \(q>2\), the initial forward packet is directed above \(BL_1\).
Before wrap, the directed crests are

\[
 BL_1,BL_2,\ldots,BL_{n+1}.
\]

Whenever the current crest is \(BL_{q-1}\), the construction charges
that packet and stops.  It never attempts to propagate it through

\[
 F_*BL_{q-1}=BL_0.
\]

If no wrap occurs within the finite horizon, the last constructed
family is \(A_{N-1}\); no \(A_N\) is defined or used.

The sequential transfer factor satisfies

\[
 2^n\leq2^{N-2}=2^{b+1}.
\tag{15.19}
\]

Thus the horizon, residual-unbreakability, factor, and wrap indices are
all correct.  In the wrap branch the empty output should be declared
explicitly before writing any output equality; this is a drafting
requirement, not a mathematical obstruction.

### 15.6 Exact post-correction verdict

```text
full restriction iota^*S is automatically one DL Wave: false
counterexample:                                      Section 15.1
directed restriction B_I(S):                         proved
one-step occurrence charge c_DL + 2 W(E):            proved
central/over/away partition:                         proved
native Shift hypotheses for every away module:       verified
q=2 and general wrap handling:                       verified
last transition index:                               N-2=b+1
largest sequential factor:                           2^(b+1)
A_N used:                                             no
```

Accordingly, the leafwise-directed analytic N1 proof is viable only in
the form using \(B_I(S)\).  Any version that feeds the complete
restriction \(\iota^*S\) directly into the native DL lemma must be
rejected.

This audit does not promote the later terminal-alignment gate, the
arbitrary-input Borel presentation, VAAPC-I, UPTCR, or MLC.

### 15.7 Final line-by-line red team of the corrected main proof

The analytic proof through equation (9.13) survives the final
line-by-line audit.  In particular:

1. finite directionalization is only existential and is applied
   singletonwise to a packet of at most two covering lifts;
2. the DL loss is charged on the source as
   \(\mathcal W(B_I(S)\setminus B^\sharp)\leq c_{\rm DL}\);
3. the retained noncentral charge uses only
   \(B_E\subset f^*E\), hence the degree-two factor
   \(2\mathcal W(E)\);
4. the central/over/away trichotomy supplies every native Shift
   hypothesis before the Shift bound is invoked;
5. full saturation makes the induction image equality exact even
   though \(\Phi_n\) need not be injective; and
6. the last possible loss is charged with
   \(2^{N-2}=2^{b+1}\).

There is, however, one exact post-proof ledger defect.  In
`kkl_stationary_relative_wave_continuation.md` at the displayed
partition (10.4), the classes as written are not necessarily mutually
exclusive.  A source leaf can have no occurrence in \(B^\sharp\) while
its unique untagged output nevertheless belongs to \(C\), because
another source leaf can supply the retained occurrence realizing that
same central output.  Such a leaf lies in both the printed
\(\mathsf D_1\) and \(\mathsf K\).

The correct disjoint source partition is

\[
 \begin{aligned}
  \mathsf K
  &:=
  \{\alpha\in S:\Phi_1(\alpha)\in C\}=P_C,\\
  \mathsf D_{\rm bad}
  &:=
  (S\setminus P_C)\setminus S^\sharp,\\
  \mathsf D_E
  &:=
  (S\setminus P_C)\cap S^\sharp .
 \end{aligned}
 \tag{15.20}
\]

For \(\mathsf D_{\rm bad}\), every directed occurrence is in
\(B^{\rm bad}\), so domination gives

\[
 \mathcal W(\mathsf D_{\rm bad})
 \leq
 \mathcal W(B^{\rm bad})
 \leq c_{\rm DL}.
 \tag{15.21}
\]

For \(\mathsf D_E\), at least one retained occurrence exists.  Its
output is the unique \(\Phi_1(\alpha)\); since
\(\alpha\notin P_C\), this output belongs to \(E=R\setminus C\).
Therefore that occurrence belongs to
\(B_E=B^\sharp\cap f^{-1}(E)\), and

\[
 \mathcal W(\mathsf D_E)
 \leq
 \mathcal W(B_E)
 \leq2\mathcal W(E).
 \tag{15.22}
\]

Thus the defect is confined to the prose ledger: equations
(7.5), (7.10), and (7.11) remain valid (they use a harmless
over-cover), and the analytic theorem is unchanged after replacing
(10.4) by (15.20).

Finally, the Borel qualification is independent of this analytic
repair.  The unconditional ledger gate remains open at

```text
STANDARD_BOREL_ORDERED_WAVE_REALIZATION
```

because the locked sources do not supply a standard-Borel leaf space,
Borel filtered-occurrence relation, and Borel ordered-buffer
calculus for every arbitrary KKL Wave.

### 15.8 Ordered-Wave Borel frontier

The separate independent audit

```text
kkl_stationary_n1_borel_ordered_wave_redteam_20260726.md
```

constructs and red-teams the missing measurable interface.  Its
principal results are:

1. strict planar nesting and the full-support area coordinate produce
   a Borel injective leaf code without assuming a measurable quotient;
2. Arsenin--Kunugui makes the realized coordinate set Borel;
3. the hyperspace initial-subarc functional gives a jointly Borel leaf
   parameterization;
4. a separate based-circle construction handles admissible leaves
   whose two tails land at the same prime end;
5. maximal partial immersion lifts, proper escape, endpoint
   convergence, and duplicate-germ removal have explicit Borel
   predicates;
6. the two KKL filters are handled by a countable universal-cover
   marked-arc tag;
7. raw occurrence count is rejected as a test for breakability;
8. terminal saturation is typed through the Borel compact-code
   embedding of the target leaf space; and
9. DL outermost buffers require only Borel order intervals, not a
   transverse countably additive width measure.

The audit also records two exact drafting hazards: zero-extremal-width
arc packets must not be omitted from the initial finite decomposition,
and a bare compact-image code must not be iterated as if it were a
parameterized path.  The safe finite-horizon route imports the native
proper Borel subwave \(A^{N\text{-nbr}}\) and carries a selected pushed
path evaluation on its already-unbreakable domain.

These results are candidates for closing
`STANDARD_BOREL_ORDERED_WAVE_REALIZATION` after integration and a final
source-hypothesis audit.  They do not affect the open status of N2,
VAAPC-I, UPTCR, or MLC.
