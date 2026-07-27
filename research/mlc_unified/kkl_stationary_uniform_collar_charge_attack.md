# Adversarial attack on the KKL stationary uniform collar-exit charge

## 1. Question and binary verdict

The open gate `KKL_STATIONARY_UNIFORM_COLLAR_EXIT_CHARGE` asks for
compatible embedded collars \(Q_h\), \(1\le h\le b+2\), and a
measurable first-exit selector such that

\[
 \frac{1}{\mu_h}
 \le
 C_b\bigl(\mathcal W(U\setminus T)+1\bigr),
 \qquad
 \mu_h=\operatorname{mod}Q_h.
\tag{1.1}
\]

The binary source-derivability verdict is:

\[
 \boxed{\textbf{NO: (1.1) does not follow from the locked
 qualitative collar and pseudo-polynomial-like hypotheses.}}
\tag{1.2}
\]

More precisely:

1. qualitative embedded-neighborhood existence gives only
   \(\mu_h>0\) for each individual block;
2. Kahn's quantitative polynomial-like restriction theorem is
   calibrated by
   \[
      \operatorname{mod}(U\setminus K)
      =
      \frac{1}{\mathcal W(F)},
   \tag{1.3}
   \]
   where \(K\) is the full filled set, not by
   \(\operatorname{mod}(U\setminus T)\);
3. KKL provide
   \[
      \mathcal W(U\setminus T)\le \mathcal W(F),
   \tag{1.4}
   \]
   the wrong direction for deriving (1.1);
4. an explicit degree-two pseudo-polynomial-like family below has
   uniformly bounded \(\mathcal W(U\setminus T)\), while the reciprocal
   modulus of **every** collar around \(K\) diverges;
5. that family is an abstract conformal countermodel, not an actual
   parabolically bounded stationary KKL block, so it does not disprove
   (1.1) in the full intended dynamical subclass;
6. the full KKL assertion therefore remains **open**, but it needs an
   additional vertical-to-collar calibration theorem or a
   route-localized replacement invariant.

No obligation is promoted in this note.  In particular, the
stationary quantitative defect bound, VAAPC-I, UPTCR, and MLC remain
open.

## 2. Locked sources

The locked KKL source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The exact clauses used here are:

- lines 439--448: a pseudo-quadratic-like map
  \(F=(f,\iota)\), its filled set \(K\), and
  \[
     \mathcal W(F)=
     \mathcal W(U\setminus K)
     =
     \frac1{\operatorname{mod}(U\setminus K)};
  \]
- lines 451--454: Kahn's polynomial-like restriction theorem as
  imported by KKL;
- lines 512--520: the Hubbard tree \(T\subset K\);
- lines 1145--1156: the vertical surface width
  \(\mathcal W(U\setminus T)\) and the terminal alternative;
- lines 1173--1175: the inequality
  \[
     \mathcal W(F)\ge \mathcal W(U\setminus T);
  \]
- lines 1225--1241: the complementary-surface covering/immersion and
  qualitative injectivity near the filled set; and
- lines 1547--1605: the finite stationary horizon
  \(h\le b+2\).

The locked Kahn source is

```text
.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
```

The exact clauses used here are:

- lines 16--41: the pseudo-polynomial-like axioms;
- lines 54--77: the quantitative polynomial-like restriction theorem;
- lines 87--153: the annulus-immersion lemma and its precise
  dependence on the ambient annulus;
- lines 155--178: the construction of the embedded restriction; and
- lines 350--421: finite pullbacks and relation iteration.

Kahn's theorem states that the modulus of the constructed
polynomial-like restriction is uniformly positive when the degree is
bounded and \(\operatorname{mod}(U\setminus K)\) is bounded below.
It does not state a bound in terms of
\(\operatorname{mod}(U\setminus T)\), and it does not state the linear
response (1.1).

## 3. First quantifier audit: arbitrary thin collars

The qualitative collar lemma in
`kkl_stationary_quantitative_defect_repair.md` chooses

\[
 K^h\subset O_h^-\Subset O_h^+\Subset O_h,
\tag{3.1}
\]

inside an embedding neighborhood and puts

\[
 Q_h=I_h(O_h^+\setminus\overline{O_h^-}).
\tag{3.2}
\]

For any one admissible pair in (3.1), one can move
\(\partial O_h^-\) arbitrarily close to \(\partial O_h^+\).  The
resulting annular modulus tends to zero.  Hence no estimate of the
form (1.1) can hold for **every** qualitative collar.

The ledger correctly uses an existential quantifier: one must
construct a well-calibrated collar.  Thus arbitrary thinning does not
refute the ledger obligation.  It does prove that the raw symbol
\(\mu_h\) is not an invariant until a selection or optimization rule
is specified.

This motivates the intrinsic definition

\[
\begin{split}
 \mathfrak C_h(F)
 :=
 \inf\Bigl\{
   \frac1{\operatorname{mod}Q}:\;&
   Q=I_h(O^+\setminus\overline{O^-}),\\
   &K^h\subset O^-\Subset O^+\Subset U^h,\\
   &O^-,O^+\text{ are Jordan disks and }
     O^+\setminus\overline{O^-}\text{ is essential in }U^h\setminus K^h,\\
   &I_h\text{ injective near }\overline{O^+}
 \Bigr\}.
\end{split}
\tag{3.3}
\]

If compatibility through all prefixes is required, define

\[
 \mathfrak C_{\le b+2}^{\rm comp}(F)
 =
 \inf_{\mathscr Q\ {\rm compatible}}
 \max_{1\le h\le b+2}
 \frac1{\operatorname{mod}Q_h}.
\tag{3.4}
\]

The infimum of an empty compatible class is \(+\infty\).  The desired
geometric part of (1.1) is precisely

\[
 \mathfrak C_{\le b+2}^{\rm comp}(F)
 \le C_b\bigl(\mathcal W(U\setminus T)+1\bigr).
\tag{3.5}
\]

Unlike the modulus of an arbitrarily chosen collar, (3.4) is
presentation independent.

## 4. Exact pseudo-polynomial-like countermodel

The following theorem shows that (3.5) is not a consequence of:

- the pseudo-polynomial-like axioms;
- a degree-two proper companion map;
- a globally embedded immersion;
- connected filled sets;
- finite Kahn iteration;
- a nondegenerate forward-invariant full tree \(T\subset K\); and
- a uniform bound on \(\mathcal W(U\setminus T)\).

### Theorem 4.1

Fix \(0<a<1\).  For \(1<R<2\), put

\[
\begin{aligned}
 U_R&=\mathbb D_R,\\
 U'_R&=\mathbb D_{\sqrt R},\\
 K&=\overline{\mathbb D},\\
 T&=[-a,a],\\
 f_R(z)&=z^2,\\
 i_R(z)&=z.
\end{aligned}
\tag{4.1}
\]

Then:

1. \(F_R=(f_R,i_R):(U'_R,K)\to(U_R,K)\) is a degree-two
   pseudo-polynomial-like map;
2. \(i_R\) is globally embedded;
3. \(T\subset K\) is a nondegenerate full tree and
   \(f_R(T)\subset T\);
4. the finite Kahn tower is
   \[
      U_R^h=\mathbb D_{R^{1/2^h}},
      \qquad K^h=K,
   \tag{4.2}
   \]
   and its complete immersion \(I_h\) is inclusion;
5. there is a constant \(M_a<\infty\), independent of \(R\), such
   that
   \[
      \mathcal W(U_R\setminus T)\le M_a;
   \tag{4.3}
   \]
6. for every collar allowed in (3.3),
   \[
      \frac1{\operatorname{mod}Q_h}
      \ge
      \frac{2\pi\,2^h}{\log R}.
   \tag{4.4}
   \]

Consequently, for every fixed \(h\ge1\),

\[
 \frac{
   \mathfrak C_h(F_R)
 }{
   \mathcal W(U_R\setminus T)+1
 }
 \longrightarrow+\infty
 \qquad(R\downarrow1).
\tag{4.5}
\]

#### Proof

The map

\[
 f_R:\mathbb D_{\sqrt R}\to\mathbb D_R
\]

is a proper degree-two branched cover.  The inclusion \(i_R\) is a
holomorphic immersion.  Directly,

\[
\begin{aligned}
 f_R^{-1}(K)
 &=\{z:|z|^2\le1\}
 =K,\\
 i_R^{-1}(K)
 &=K.
\end{aligned}
\tag{4.6}
\]

The common inverse is connected, so all pseudo-polynomial-like axioms
hold.  This proves assertions 1--2.

The segment \(T\) is compact, connected, and full.  Moreover,

\[
 z\in[-a,a]
 \quad\Longrightarrow\quad
 z^2\in[0,a^2]\subset[-a,a],
\tag{4.7}
\]

because \(a<1\).  This proves assertion 3.

For the ordinary quadratic-like relation with inclusion immersion,
each pullback replaces the outer radius by its positive square root.
Induction gives (4.2), and every complete immersion is inclusion.
This proves assertion 4.

The ring domain \(\mathbb D\setminus T\) is nondegenerate, so

\[
 m_a:=\operatorname{mod}(\mathbb D\setminus T)>0.
\tag{4.8}
\]

For \(R>1\), monotonicity of ring modulus under enlargement of the
outer domain gives

\[
 \operatorname{mod}(U_R\setminus T)
 \ge
 \operatorname{mod}(\mathbb D\setminus T)
 =m_a.
\tag{4.9}
\]

Therefore

\[
 \mathcal W(U_R\setminus T)
 =
 \frac1{\operatorname{mod}(U_R\setminus T)}
 \le
 \frac1{m_a}
 =:M_a,
\tag{4.10}
\]

proving assertion 5.

Now fix \(h\) and any admissible

\[
 K\subset O^-\Subset O^+\Subset U_R^h.
\tag{4.11}
\]

Because \(I_h\) is inclusion, conformal invariance gives

\[
 \operatorname{mod}Q_h
 =
 \operatorname{mod}(O^+\setminus\overline{O^-}).
\tag{4.12}
\]

The two Jordan disks in the definition make this collar an essential
subannulus of \(U_R^h\setminus K\).  Enlarging the outer boundary from
\(O^+\) to \(U_R^h\) and shrinking the inner compact set from
\(\overline{O^-}\) to \(K\) can only increase ring modulus.  Hence

\[
\begin{aligned}
 \operatorname{mod}Q_h
 &\le
 \operatorname{mod}(U_R^h\setminus K)\\
 &=
 \operatorname{mod}
 \bigl(
   \mathbb D_{R^{1/2^h}}\setminus
   \overline{\mathbb D}
 \bigr)\\
 &=
 \frac1{2\pi}\log R^{1/2^h}
 =
 \frac{\log R}{2\pi\,2^h}.
\end{aligned}
\tag{4.13}
\]

Taking reciprocals proves (4.4).  Combining (4.3) and (4.4), then
letting \(R\downarrow1\), proves (4.5). \(\square\)

### Qualification 4.2

Theorem 4.1 is stronger than an arbitrary-thin-collar example:
(4.4) bounds the modulus of **every** admissible collar, even though
the immersion is globally injective.

It is not an actual KKL stationary counterexample.  In particular:

1. \(T\) is a forward-invariant full tree but is not asserted to be
   the Hubbard tree of a prime primitive renormalization; and
2. \(z^2\) has a superattracting fixed point, whereas the proof-used
   KKL class is periodically repelling.

Therefore Theorem 4.1 refutes a deduction from the geometric and
pseudo-polynomial-like hypotheses presently cited for the collar
step.  It does not establish that (1.1) is false after every native
stationary combinatorial and dynamical hypothesis is imposed.

## 5. What Kahn's quantitative theorem actually supplies

Let

\[
 m(F)=\operatorname{mod}(U\setminus K)
 =\frac1{\mathcal W(F)}.
\tag{5.1}
\]

For a degree-\(D\) pseudo-polynomial-like map and a lower bound
\(m(F)\ge m>0\), Kahn's theorem supplies a number

\[
 \mu_{\rm K}(D,m)>0
\tag{5.2}
\]

and a polynomial-like restriction on which the immersion is embedded.
Here and below, \(\mu_{\rm K}(D,m)\) denotes any fixed monotone lower
response furnished by the theorem, simultaneously for all degrees at
most \(D\) and all ambient moduli at least \(m\).  Equivalently, one
may define it as the infimum, over that class of maps, of the supremal
modulus among the admissible restrictions constructed by the theorem.
Kahn's uniform-positivity assertion says precisely that this infimum is
positive.
The source does not give an explicit formula for
\(\mu_{\rm K}(D,m)\), but its quantifiers give a positive response for
every \(D<\infty\) and \(m>0\).

Apply this to the complete horizon-\(h\) pair, whose degree is

\[
 D_h=2^h\le2^{b+2}.
\tag{5.3}
\]

This application requires one short induction that should not be
hidden in the notation.  Kahn's pullback lemma gives degree-two
pseudo-polynomial-like maps

\[
 (i_r,f_r):(U^{r+1},K^{r+1})\longrightarrow(U^r,K^r)
 \qquad(0\le r<h).
\]

The pullback squares imply

\[
 I_h^{-1}(K)=P_h^{-1}(K)=K^h.
\tag{5.3a}
\]

The set \(K^h\) is connected, \(I_h\) is an immersion, and the
composition \(P_h\) is proper of degree \(2^h\).  Thus

\[
 (I_h,P_h):(U^h,K^h)\longrightarrow(U,K)
\tag{5.3b}
\]

is itself a pseudo-polynomial-like map of degree \(D_h=2^h\).
Moreover, the restrictions \(i_r:K^{r+1}\to K^r\) are
homeomorphisms in Kahn's pullback construction, so
\(I_h:K^h\to K\) is a homeomorphism.  These facts justify applying
the polynomial-like restriction theorem to the complete pair, rather
than merely to each degree-two one-step pair.

For the individually selected restriction, let \(W_h\) be the target
disk and \(W_h'\) its proper preimage.  Kahn gives

\[
 I_h|_{W_h'}\text{ embedded},\qquad
 I_h(W_h')\Subset W_h,
\tag{5.4}
\]

and

\[
 \operatorname{mod}
 \bigl(W_h\setminus I_h(W_h')\bigr)
 \ge
 \mu_{\rm K}(D_h,m(F)).
\tag{5.5}
\]

Since \(K\subset I_h(W_h')\), ring monotonicity gives

\[
 \operatorname{mod}(W_h\setminus K)
 \ge
 \mu_{\rm K}(D_h,m(F)).
\tag{5.6}
\]

The proper map

\[
 P_h:W_h'\setminus K^h\longrightarrow W_h\setminus K
\]

is an unbranched degree-\(D_h\) cover.  Therefore

\[
 \operatorname{mod}(W_h'\setminus K^h)
 =
 \frac1{D_h}\operatorname{mod}(W_h\setminus K)
 \ge
 \frac{\mu_{\rm K}(D_h,m(F))}{D_h}.
\tag{5.7}
\]

Put

\[
 M_h=\operatorname{mod}(W_h'\setminus K^h).
\]

Uniformize the source annulus as

\[
 \phi_h:
 \{1<|z|<e^{2\pi M_h}\}
 \longrightarrow W_h'\setminus K^h.
\]

Let \(O_h^-\) and \(O_h^+\) be the bounded Jordan domains enclosed by
the analytic curves

\[
 \phi_h\!\left(|z|=e^{2\pi M_h/4}\right)
 \quad\text{and}\quad
 \phi_h\!\left(|z|=e^{2\pi 3M_h/4}\right),
\]

respectively.  Then

\[
 K^h\subset O_h^-\Subset O_h^+\Subset W_h'\Subset U^h.
\]

Since \(I_h\) is embedded on \(W_h'\), it is injective on a
neighborhood of \(\overline{O_h^+}\).  Conformal invariance and the
round-annulus formula now give

\[
 \operatorname{mod}
 I_h(O_h^+\setminus\overline{O_h^-})
 =
 \frac{M_h}{2}.
\]

Thus this strictly interior individual collar satisfies

\[
 \operatorname{mod}Q_h
 \ge
 \frac{\mu_{\rm K}(D_h,m(F))}{2D_h}.
\tag{5.8}
\]

If one does not wish to invoke analytic level curves at the two exact
fractions, compact inward approximations give the same conclusion with
\(2\) replaced by any fixed constant greater than \(2\).  No
injectivity on a neighborhood of \(\overline{W_h'}\) is being assumed.

Thus the locked Kahn theorem supports the block-dependent response

\[
 \frac1{\operatorname{mod}Q_h}
 \le
 \frac{2D_h}{
   \mu_{\rm K}(D_h,1/\mathcal W(F))
 }.
\tag{5.9}
\]

Define

\[
 \Psi_b(x)
 =
 \max_{1\le h\le b+2}
 \frac{2^{h+1}}{
   \mu_{\rm K}(2^h,1/x)
 }.
\tag{5.10}
\]

Then the source supports, for separately selected collars,

\[
 \frac1{\operatorname{mod}Q_h}
 \le \Psi_b(\mathcal W(F)).
\tag{5.11}
\]

Two qualifications are essential.

1. The source does not state that \(\Psi_b(x)\le C_b(x+1)\).
2. Independently selected restrictions need not satisfy the complete
   prefix compatibility demanded by (3.4).  A quantitative compatible
   shrinking theorem is not present in the locked excerpts.

Equation (5.11), not (1.1), is the strongest direct quantitative
collar response supported by the cited Kahn theorem.

## 6. The missing comparison has the wrong known direction

Since \(T\subset K\), ring-domain monotonicity gives

\[
 \operatorname{mod}(U\setminus K)
 \le
 \operatorname{mod}(U\setminus T).
\tag{6.1}
\]

Taking reciprocals gives

\[
 \mathcal W(F)
 =
 \mathcal W(U\setminus K)
 \ge
 \mathcal W(U\setminus T).
\tag{6.2}
\]

This is exactly the direction used by KKL around source lines
1173--1175.  It cannot turn the full-width response
\(\Psi_b(\mathcal W(F))\) into a function of the smaller vertical
width.

A sufficient new source-level hypothesis would be a quantitative
reverse comparison

\[
 \mathcal W(F)
 \le
 A_b\bigl(\mathcal W(U\setminus T)+1\bigr),
\tag{6.3}
\]

together with a Kahn response estimate

\[
 \Psi_b(x)\le B_b(x+1)
\tag{6.4}
\]

and a compatible finite-horizon collar-selection theorem.  None of
(6.3), (6.4), or the compatible selection appears in the locked KKL
or Kahn clauses.

One may combine (6.3)--(6.4), but neither is logically necessary.
The exact direct missing hypothesis is simply the intrinsic
calibration

\[
 \boxed{
 \mathfrak C_{\le b+2}^{\rm comp}(F)
 \le C_b\bigl(\mathcal W(U\setminus T)+1\bigr).
 }
\tag{6.5}
\]

Writing (6.5) with the optimized conductance (3.4) prevents a choice
of accidentally thin collars from changing the truth value.

## 7. Sharper route-localized replacement

A collar around the **entire** filled set may be much thinner because
of geometry never encountered by the selected stationary route.  The
proof only needs to charge the leaves whose selected continuation
actually exits.

Let \(\mathscr E_h(F)\) be the marked curve family of all proof-used
selected continuations which:

1. start at the certified local seed and access;
2. follow the declared route orientation and occurrence windows; and
3. reach the first failure locus of the \(I_h\)-inverse branch before
   reaching the declared remote access.

Retain the complete occurrence, access, sheet, attachment, and
first-failure labels.  Define the **route-exit conductance**

\[
 \mathfrak E_h(F)=\mathcal W(\mathscr E_h(F)).
\tag{7.1}
\]

For a measurable defect family \(D_{1,h}\) with the same selector,
the inclusion of marked families gives directly

\[
 \mathcal W(D_{1,h})\le\mathfrak E_h(F).
\tag{7.2}
\]

The sharper replacement target is

\[
 \sum_{h=1}^{b+2}\mathfrak E_h(F)
 \le
 C_b\bigl(\mathcal W(U\setminus T)+1\bigr).
\tag{7.3}
\]

This formulation has three advantages:

1. it is independent of arbitrary Jordan-neighborhood choices;
2. it ignores thin parts of a global filled-set collar which no
   proof-used route visits; and
3. it already incorporates the measurable selector needed by the
   defect decomposition.

Any proof of (6.5) plus the annular-overflow theorem implies (7.3),
up to the finite factor \(b+2\).  The converse need not hold.
Therefore (7.3) is a genuinely weaker and more source-faithful
analytic target.

If neither (6.5) nor (7.3) can be proved, the response state must
retain

\[
 \bigl(
   \mathfrak C_{\le b+2}^{\rm comp}(F),
   \mathfrak E_1(F),\ldots,\mathfrak E_{b+2}(F)
 \bigr)
\tag{7.4}
\]

as an additional analytic counter.  It cannot be discarded merely
because an embedding neighborhood exists.

## 8. Measurability remains independent

Even a valid modulus bound does not construct the measurable
first-exit selector required in the ledger statement.

For a lamination parameter space \((\Lambda,\nu)\), one still needs:

1. a Borel field of initial local inverse germs;
2. a Borel maximal-continuation time;
3. a Borel first-failure code and exit subarc; and
4. compatibility of this selection with the transverse measure used
   to define extremal width.

Pointwise path continuation does not imply these statements.  Thus a
complete proof of the original gate requires both (6.5) and this
measurable-selection theorem, while the route-localized formulation
(7.1)--(7.3) builds the selector into the object being estimated.

## 9. Adversarial audit

### 9.1 Arbitrary collar versus optimized collar

Shrinking an arbitrary collar refutes only a universal-collar reading.
Theorem 4.1 refutes the stronger existential inference from the listed
abstract hypotheses by bounding **every** admissible collar.

### 9.2 Correct modulus monotonicity

For \(T\subset K\),

\[
 U\setminus K\subset U\setminus T,
\]

and enlarging the ring by shrinking its inner compact set increases
modulus.  Hence (6.1), not its reverse, is correct.

### 9.3 Correct covering factor

For an unbranched degree-\(D\) cover of annuli,

\[
 \operatorname{mod}(\text{source})
 =
 \frac1D\operatorname{mod}(\text{target}).
\]

This gives the factor \(D_h\) in (5.7)--(5.9).  No degree-one
stationary shortcut is used.

### 9.4 Finite horizon is not quantitative calibration

The number of horizons is bounded by \(b+2\), but each individual
collar modulus can still tend to zero with the block.  A finite
minimum of uncontrolled positive numbers is uncontrolled.

### 9.5 Global embedding does not save (1.1)

Every \(I_h\) in Theorem 4.1 is a global inclusion.  The failure is
not a sheet collision; it is the absence of conformal room between
the full filled set and the ambient boundary.

### 9.6 Vertical width and full width are distinct

In Theorem 4.1,

\[
 \mathcal W(F_R)
 =
 \frac{2\pi}{\log R}\longrightarrow\infty,
\]

while (4.3) bounds the vertical tree width.  This realizes the missing
reverse comparison exactly.

### 9.7 Actual KKL status

The countermodel does not satisfy every native stationary dynamical
hypothesis.  It must not be cited as a counterexample to the intended
KKL theorem.  Its valid conclusion is that those additional
hypotheses must be used in a new quantitative proof; the currently
cited collar theorems do not suffice.

### 9.8 Computation cannot promote the gate

No numerical modulus estimate is used.  The countermodel follows from
exact disk radii, ring-modulus monotonicity, and the formula
\(\operatorname{mod}A(r,R)=\frac1{2\pi}\log(R/r)\).

## 10. Final conclusion and exact next hypothesis

The final binary conclusion is:

\[
\boxed{
\begin{array}{c}
\texttt{KKL\_STATIONARY\_UNIFORM\_COLLAR\_EXIT\_CHARGE}\\
\textbf{does not follow from the currently locked source hypotheses;}\\
\textbf{it remains open in the full stationary KKL class.}
\end{array}}
\tag{10.1}
\]

The exact missing source-level input is one of:

1. the optimized compatible calibration (6.5), plus measurable
   first-exit selection; or
2. the sharper route-localized conductance bound (7.3).

A sufficient but stronger package is the reverse full/vertical width
comparison (6.3), a linear Kahn response (6.4), and quantitative
compatible collar selection.

Absent one of these theorems, the replacement state must retain the
collar/route conductances (7.4).  Qualitative embedded-collar
existence cannot discharge the analytic exit charge.
