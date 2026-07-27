# RETRACTED — KKL Wave local-end collision reduction

## Post-audit status (2026-07-26)

**This candidate proof is false and must not be cited as mathematical
evidence.**  It is retained below only as a forensic record of the failed
argument.  No lemma, theorem, corollary, stationary estimate, or status
recommendation in the historical text below is active.

The independent extremal-width audit
`qa_extremal_wave_2026-07-26.md` establishes:

1. Lemma 6.1 has an endpoint-counting error.  With the note's closed-hull
   convention, an interval of positive integral length \(q\) meets its
   translates through \(q\), so the exact count is
   \[
     s=\lfloor q\rfloor+1=q+1,
   \]
   not \(\lceil q\rceil=q\).
2. Lemma 6.2 is false for a more fundamental reason: the supremal
   self-translate span of one leaf does not control collisions between
   different leaves or different positive-width rectangular components.
   A dyadic span class need not be one Shift rectangle, and its widths may
   add by the Parallel Law.
3. Consequently Theorem 7.1, Corollary 8.1, and the stationary formula
   (9.3) are false/unavailable.
4. A finite cyclic-cover model has source width \(Nw\) while every target
   Wave in the set-theoretic pushforward has width at most \(w\), with
   covering degree bounded by the fixed integer \(M=N+2\).  Already for
   \(N=2\), letting \(w\to\infty\) contradicts every proposed
   coefficient-one \(O(1+\log M)\) loss.
5. The full cyclic pullback of one target Wave gives the same obstruction
   to the literal broad wording of KKL Lemma A.13 under the printed KKL
   definitions.  This does **not** refute Dudko--Lyubich's narrower native
   theorem for one Wave above one fixed boundary interval.

The admissible replacement is therefore not “full-base degree” alone.
One must prove either:

- a coherent single-crest/single-WAD-coordinate packet theorem and verify
  that every proof-used stationary Wave belongs to that restricted class;
  or
- a multiplicity-aware packet invariant that charges linearly for
  independent source conductance coordinates collapsing to one target
  coordinate.

Current statuses:

```text
this candidate:                                      retracted/false
literal broad KKL coefficient-one Wave statement:   source-defective
DL native one-common-interval annular theorem:       unaffected
restricted Wave pushforward theorem:                 open
KKL stationary repair:                              open
VAAPC-I:                                             open
UPTCR:                                               open
MLC:                                                 open
```

The complete counterexample, predicate audit, width-law verification, and
replacement invariant are in `qa_extremal_wave_2026-07-26.md`.

---

## Historical attempted proof (invalid; retained for traceability)

## 1. Outcome

This pass gives a negative answer for degree measured only on one
ending interval and a positive replacement theorem for degree measured
on the full Wave base.

> **Local-end no-go.**  Under the natural boundary-fiber definition of
> degree, there is no function of
> \(\deg_\partial(f;I')\) alone that bounds the number of target deck
> translates colliding with a Wave merely because the Wave ends at
> \(I'\).  For the annular model of \(z\mapsto z^m\), one can have
> \[
>   \deg_\partial(f;I')=1
>   \quad\text{and}\quad
>   m_{\rm col}\geq m-1.
>   \tag{1.1}
> \]

> **Full-base repair.**  Let \(B(A')\) be the full base of a Wave
> \(A'\) in a cyclic ideal-boundary collar.  If
> \[
>   \deg_\partial(f;B(A'))\leq d,
>   \tag{1.2}
> \]
> then the universal-cover dyadic pruning argument gives one absolute
> \(c_{\rm W}<\infty\) and a Wave \(A\subset f_*A'\) such that
> \[
>   \mathcal W(A')
>   \leq
>   \mathcal W(A)+c_{\rm W}(1+\log d).
>   \tag{1.3}
> \]
> No marking-cardinality, global annulus-degree, period, rotation
> number, or corridor-length term occurs.

Thus the exact replacement invariant is the collision span of the full
base, equivalently its boundary-fiber degree in the cyclic collar.  A
degree bound on a smaller ending interval is sufficient only after a
separate comparison
\[
 \deg_\partial(f;B(A'))
 \leq K\,\deg_\partial(f;I')
\tag{1.4}
\]
is proved.

For a stationary quadratic packet, one can avoid (1.4) by declaring
the whole base \(B(A')\) to be the degree-tested multi-interval and
using the safe global bound
\[
 \deg_\partial(f^h;B(A'))\leq2^h\leq2^{b+2}.
\tag{1.5}
\]
This yields the required \(b\)-controlled additive charge once the
actual packet supplies the cyclic collar, genuine source Wave, and
pulled-marking survival.

This pass does not construct those actual source Waves.  It does not
promote typed paired-Wave realization, the uniform \(BL_0\)-survivor
response, the stationary repair, VAAPC-I, UPTCR, or MLC.

## 2. Locked sources and proof boundary

The source files used here are:

| role | file | SHA-256 |
|---|---|---|
| KKL master | `.tmp_wave_audit/waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| DL Feigenbaum source | `.tmp_wave_audit/dl23/Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| DL neutral source | `.tmp_wave_audit/dlneutral/PseudoSiegelBounds.tex` | `4AE3253817EF8EEB76DF95FA411CB9C2B6CB0642C3C4AED4D8AE8305F2122172` |
| KL06 extremal-width appendix | `.tmp_kl06_source/appendix.tex` | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |

Relevant source locations:

* KKL master 1844--1875: ideal boundaries, markings, proper paths,
  laminations, Wave bases, ends, and crests;
* KKL master 2062--2072: covering extension, pulled marking, and
  pushforward;
* KKL master 2147--2152: the stated Wave pushforward estimate;
* DL Feigenbaum 2821--2842: the annular deck-pruning proof;
* DL neutral 1747--1750: unscripted constants are absolute;
* DL neutral 8849--8880: linked conformal shifts have width at most
  \(2\);
* KL06 appendix 59--68: the Parallel Law.

KKL do not define “degree on” an ideal multi-interval in the checked
source.  Section 3 supplies a precise definition for the cyclic-collar
case and tests it against the source applications.  The theorem proved
below is a direct cyclic-collar theorem.  Extending it to arbitrary
noncyclic ideal-boundary components would require a different
group-action argument and is not claimed.

## 3. Precise boundary degree

### 3.1 Cyclic collar model

Let
\[
 S_H:=\{z\in\mathbb C:0<\operatorname{Im}z<H\},
 \qquad H>0,
\tag{3.1}
\]
and let \(T(z)=z+1\).  A degree-\(M\) annular covering is conformally
represented by
\[
 F_M:
 A_M:=S_H/\langle T^M\rangle
 \longrightarrow
 A_1:=S_H/\langle T\rangle,
\tag{3.2}
\]
where \(F_M\) is induced by the identity on \(S_H\).  Under exponential
uniformizations, this is the usual \(z\mapsto z^M\) annulus model.

The same normalization applies to a cyclic ideal-boundary collar of a
covering between hyperbolic surfaces.  A lift between universal covers
is conformal; after conjugating the two cyclic stabilizers, its
boundary action is the identity on \(\mathbb R\), while the source and
target deck periods are \(M\) and \(1\).

### 3.2 Boundary-fiber degree of a proper interval

Let \(J'\) be a proper connected interval of the lower ideal boundary
of \(A_M\).  Choose its unique lift
\[
 \widetilde J=(a,b)\subset\mathbb R
 \quad\text{with}\quad 0<b-a<M.
\tag{3.3}
\]
Define
\[
 \deg_\partial(F_M;J')
 :=
 \sup_{\theta\in\mathbb R/\mathbb Z}
 \#\{x\in(a,b):x\bmod\mathbb Z=\theta\}.
\tag{3.4}
\]
The definition is independent of the chosen \(M\mathbb Z\)-translate
of \(\widetilde J\).  Since an interval of length \(L=b-a\) contains at
most \(\lceil L\rceil\) representatives of one class modulo
\(\mathbb Z\), and classes arbitrarily close to an endpoint attain this
maximum,
\[
 \deg_\partial(F_M;J')=\lceil b-a\rceil.
\tag{3.5}
\]
For integer \(b-a\), open endpoints give the same supremum.

Invariantly, (3.4) is the supremal number of sheets in an arbitrarily
small ideal collar of \(J'\).  For a covering extension
\[
 \partial f:\mathscr D_f\longrightarrow\partial_i V
\]
defined on the open dense ideal-boundary domain described by KKL
master 2065--2066, the corresponding collar definition is
\[
 \deg_\partial(f;J')
 :=
 \inf_{\mathcal C'\supset J'}
 \sup_{z\in V}
 \#\bigl(f^{-1}(z)\cap\mathcal C'\bigr),
\tag{3.6}
\]
where the infimum is over connected ideal collars on which the
covering extension is defined and finite-to-one.  In a cyclic collar,
(3.6) reduces to (3.4).

If no such finite-sheet collar exists, set the degree to \(+\infty\).
Endpoint multiplicities can equivalently be included by taking a
regular-value limsup.  They do not change the cyclic formula (3.5).

### 3.3 Why component degree is the wrong definition

The degree of the entire annular cover in (3.2) is \(M\) on every
boundary component.  KKL master 1742--1743, however, assigns degree
\(1\) to some ideal intervals and degrees \(2^r\) to others for the
same iterate.  Thus their intended quantity cannot be the degree of
the whole boundary component.  The collar/fiber definition (3.6) has
the required locality.

## 4. Collision multiplicity

Let \(A'\) be a Wave in \(A_M\) subordinate to its full base
\(B=B(A')\) on the lower ideal boundary.  Choose a lift
\(\widetilde B=(a,b)\) and one lifted lamination
\(\widetilde A\) whose leaves have both endpoints in
\(\overline{\widetilde B}\).

For a lifted leaf \(\widetilde\alpha\), let
\[
 \operatorname{Hull}_\partial(\widetilde\alpha)
\tag{4.1}
\]
denote the closed interval of \(\mathbb R\) between its endpoints in
the orientation selected by the Wave base.  Its one-sided translate
span is
\[
 s(\widetilde\alpha)
 :=
 1+
 \#\{k\in\mathbb Z_{>0}:
   \operatorname{Hull}_\partial(\widetilde\alpha)
   \cap
   T^k\operatorname{Hull}_\partial(\widetilde\alpha)
   \ne\varnothing\}.
\tag{4.2}
\]
Define
\[
 s(A'):=\sup_{\widetilde\alpha\in\widetilde A}
 s(\widetilde\alpha).
\tag{4.3}
\]

The translate \(T^k\widetilde\alpha\) can be linked with
\(\widetilde\alpha\) only if their boundary hulls overlap.  Therefore
the number of positive collision shifts satisfies
\[
 m_{\rm col}^+(A')\leq s(A'),
\qquad
 m_{\rm col}(A')\leq 2s(A')-1.
\tag{4.4}
\]
The factor \(2\) only records the two shift directions and is
irrelevant after taking a logarithm.

Because every leaf hull lies in \([a,b]\),
\[
 s(A')\leq\lceil b-a\rceil
 =\deg_\partial(F_M;B(A')).
\tag{4.5}
\]
Equation (4.5), not a degree bound on one end, is the collision estimate
used by the dyadic pruning proof.

## 5. Explicit \(z^m\) obstruction to end-only control

### Proposition 5.1

For every integer \(m\geq2\), the covering \(F_m:A_m\to A_1\) admits:

1. an ending interval \(I'\) with
   \(\deg_\partial(F_m;I')=1\); and
2. a simple boundary-parallel Wave leaf \(\gamma\) ending at \(I'\)
   whose chosen universal-cover lift is linked with each of its
   translates \(T^k\widetilde\gamma\),
   \(1\leq k\leq m-1\).

Consequently,
\[
 m_{\rm col}(\gamma)\geq m-1
 \quad\text{while}\quad
 \deg_\partial(F_m;I')=1.
\tag{5.1}
\]

#### Proof

Fix \(0<\epsilon<1/8\), choose
\[
 a:=2\epsilon,\qquad L:=m-\frac12,
\tag{5.2}
\]
and let
\[
 I':=(a-\epsilon,a+\epsilon)\pmod{m\mathbb Z}.
\tag{5.3}
\]
Its lift has length \(2\epsilon<1\), so (3.5) gives
\[
 \deg_\partial(F_m;I')=1.
\tag{5.4}
\]

Choose \(0<h_0<H\) and define
\[
 \widetilde\gamma(t)
 :=
 a+Lt+i h_0\sin(\pi t),
 \qquad 0\leq t\leq1.
\tag{5.5}
\]
Its initial endpoint is \(a\in I'\).  Its two endpoints lie on the
lower ideal boundary, and it is homotopic rel endpoints to the
boundary interval \([a,a+L]\); hence its source projection is
boundary-parallel and ends at \(I'\).

We first verify source simplicity.  If two parameters \(s,t\) project
to the same point of \(A_m\), then
\[
 h_0\sin(\pi t)=h_0\sin(\pi s)
\tag{5.6}
\]
and
\[
 L(t-s)\in m\mathbb Z.
\tag{5.7}
\]
Equation (5.6) gives either \(t=s\) or \(t=1-s\).  Since
\[
 |L(t-s)|<L<m
\tag{5.8}
\]
for distinct interior parameters, (5.7) forces \(t=s\).  Thus the
projection to \(A_m\) is simple.

Now fix \(1\leq k\leq m-1\) and put
\[
 t_k:=\frac12\left(1+\frac{k}{L}\right),
 \qquad
 s_k:=\frac12\left(1-\frac{k}{L}\right).
\tag{5.9}
\]
Because \(k\leq m-1<L\), both parameters lie in \((0,1)\).  They
satisfy
\[
 t_k=1-s_k,
\quad
 \sin(\pi t_k)=\sin(\pi s_k),
\quad
 L(t_k-s_k)=k.
\tag{5.10}
\]
Hence
\[
 \widetilde\gamma(t_k)
 =
 T^k\widetilde\gamma(s_k).
\tag{5.11}
\]
The intersection is transverse: the imaginary components of the two
tangent vectors have opposite nonzero signs because
\[
 \cos(\pi t_k)=-\cos(\pi s_k)\ne0.
\tag{5.12}
\]
Therefore the collision persists for a sufficiently thin foliated
rectangle around \(\gamma\).  This proves (5.1). \(\square\)

### What Proposition 5.1 proves—and does not prove

The proposition is an explicit counterexample to
\[
 m_{\rm col}(A')
 \leq
 \Phi\bigl(\deg_\partial(f;I')\bigr)
\tag{5.13}
\]
for every finite function \(\Phi\), when \(I'\) is merely one ending
interval.

It is not by itself a counterexample to KKL's width inequality.  A
single linked rectangle has universally bounded width by the Shift
Argument.  Producing a violation of the width estimate would require a
family with unbounded total width, not just unbounded collision count.
The proposition instead identifies the first failed implication in
the proposed universal-cover proof and the extra invariant it needs.

For the same example, the full base is the projection of
\((a,a+L)\), so
\[
 \deg_\partial(F_m;B(\gamma))
 =
 \left\lceil m-\frac12\right\rceil=m.
\tag{5.14}
\]
The full-base degree detects exactly the collision scale missed by
\(I'\).

## 6. Full-base collision theorem

### Lemma 6.1 (base degree controls translate span)

For every cyclic-collar Wave \(A'\),
\[
 s(A')
 \leq
 \deg_\partial(f;B(A')).
\tag{6.1}
\]

#### Proof

Normalize the collar as in (3.2) and lift the base to
\((a,b)\).  If a leaf has endpoint hull \([x,y]\subset[a,b]\), then
the positive integers \(k\) for which
\([x,y]\cap[x+k,y+k]\ne\varnothing\) satisfy \(k\leq y-x\).
Consequently,
\[
 s(\widetilde\alpha)
 \leq
 \lceil y-x\rceil
 \leq
 \lceil b-a\rceil.
\tag{6.2}
\]
Taking the supremum over leaves and using (3.5) proves (6.1).
\(\square\)

### Lemma 6.2 (dyadic collision pruning)

There is an absolute \(c_0<\infty\) with the following property.  If a
cyclic-collar Wave \(A'\) satisfies \(s(A')\leq d\), then it contains a
subwave \(A^{\rm new}\) such that:

1. all target-deck translates of a chosen lift of \(A^{\rm new}\) are
   pairwise disjoint;
2. the covering is injective on \(A^{\rm new}\); and
3.
   \[
     \mathcal W(A^{\rm new})
     \geq
     \mathcal W(A')-c_0(1+\log d).
     \tag{6.3}
   \]

#### Proof

This is the DL deck-pruning proof with the global deck index replaced
by the actual translate span.  We spell out why that replacement is
valid.

For a lifted leaf \(\widetilde\alpha\), let \(r(\widetilde\alpha)\) be
the number of target fundamental intervals met by its oriented
boundary hull.  By hypothesis,
\[
 1\leq r(\widetilde\alpha)\leq d.
\tag{6.4}
\]
Partition \(A'\) into the fundamental class \(A^0\) and dyadic classes
\(A^t\), \(t\geq1\), according to
\[
\begin{aligned}
 A^0 &: r(\widetilde\alpha)=1,\\
 A^t &: 2^{t-1}<r(\widetilde\alpha)\leq2^t.
\end{aligned}
\tag{6.5}
\]
Only
\[
 T\leq1+\lceil\log_2 d\rceil
\tag{6.6}
\]
classes are nonempty.

Fix \(t>0\).  A leaf in \(A^t\) has a boundary hull meeting more than
\(2^{t-1}\) consecutive target fundamental intervals.  Translating by
\(T^{2^{t-1}}\) interlaces the two ordered endpoint pairs.  After
discarding the universal outer buffer needed to exclude equality at a
class boundary, the canonical rectangle for \(A^t\) is linked with its
conformal translate.

The Shift Argument, DL-neutral 8849--8880, gives an absolute upper
bound for the retained linked rectangle; restoring the discarded unit
buffers changes that bound by another absolute amount.  Thus one
absolute \(a_1\) satisfies
\[
 \mathcal W(A^t)\leq a_1,
 \qquad t>0.
\tag{6.7}
\]
No global deck index enters (6.7).

Discard all \(A^t\), \(t>0\).  The Parallel Law, KL06 appendix 59--68,
and (6.6)--(6.7) give
\[
 \mathcal W(A')
 \leq
 \mathcal W(A^0)+
 a_1\bigl(1+\lceil\log_2d\rceil\bigr).
\tag{6.8}
\]

Leaves in the fundamental class have endpoint hulls contained in one
target fundamental interval.  The endpoint intervals of distinct
integer translates are therefore ordered and disjoint.  Removing the
one universal outer buffer used in DL-Feigen 2840--2841 gives a
subwave \(A^{\rm new}\subset A^0\) whose entire target-deck orbit is
pairwise disjoint.  Let the width of that final buffer be bounded by
the absolute constant \(a_2\).  Then
\[
 \mathcal W(A')
 \leq
 \mathcal W(A^{\rm new})+
 a_1\bigl(1+\lceil\log_2d\rceil\bigr)+a_2.
\tag{6.9}
\]
Since
\[
 \lceil\log_2d\rceil
 \leq1+\frac{\log d}{\log2},
\qquad d\geq1,
\tag{6.10}
\]
one absolute \(c_0\) absorbs \(a_1,a_2\) and the change of logarithm
base, proving (6.3).

Pairwise disjointness of the full target-deck orbit is exactly the
criterion that the quotient map be injective on the retained
lamination. \(\square\)

## 7. Width and marking preservation

### Theorem 7.1 (full-base Wave pushforward)

Let \(f:V'\to V\) be a holomorphic covering with a cyclic
ideal-boundary collar containing the full base of a Wave
\[
 A'\subset(V',f^*\mathcal I).
\]
Assume:

1. the ideal-boundary extension is defined on the full base
   \(B(A')\);
2. \(\deg_\partial(f;B(A'))\leq d<\infty\);
3. the cyclic collar and its lift preserve the complete pulled marking;
   and
4. the final retained target paths are not removed by a separately
   imposed coarse-subordination filter.

Then there is a Wave \(A\subset f_*A'\) with
\[
 \mathcal W(A')
 \leq
 \mathcal W(A)+c_{\rm W}(1+\log d),
\tag{7.1}
\]
where \(c_{\rm W}\) is absolute.

#### Proof

Lemma 6.1 gives
\[
 s(A')\leq d.
\tag{7.2}
\]
Apply Lemma 6.2 to obtain \(A^{\rm new}\subset A'\).  The covering is
injective and holomorphic on the retained lamination, hence conformal
there.  Conformal invariance of extremal width gives
\[
 \mathcal W(f_*A^{\rm new})
 =
 \mathcal W(A^{\rm new}).
\tag{7.3}
\]

KKL master 2066--2072 say that the target marking pulls back under the
cover and that a pushed proper marked path is a proper target path.
The image of a boundary-subordinate path is subordinate to
\(f_*B(A')\), and KKL master 2067 says that the pushforward of a
multi-interval is a multi-interval.  Since the deck orbit of
\widetilde \(A^{\rm new}\) is pairwise disjoint, its target projection
is a lamination.  Assumptions 3--4 ensure that it survives the complete
marking convention.  Therefore
\[
 A:=f_*A^{\rm new}
\tag{7.4}
\]
is a genuine target Wave.

Finally, (6.3) and (7.3) give
\[
\begin{aligned}
 \mathcal W(A')
 &\leq
 \mathcal W(A^{\rm new})+c_0(1+\log d)\\
 &=\mathcal W(A)+c_0(1+\log d).
\end{aligned}
\tag{7.5}
\]
Take \(c_{\rm W}=c_0\). \(\square\)

The coarse-filter clause is explicit because KKL master 2096--2097
later discards restrictions that are not paths in a refined marking or
are subordinate to one pulled interval.  The covering pushforward
itself preserves \(f^*\mathcal I\); an additional project-level filter
must be audited separately.

## 8. End-to-base comparison

### Corollary 8.1

Under the hypotheses of Theorem 7.1, suppose a Wave ends at \(I'\) and
\[
 \deg_\partial(f;B(A'))
 \leq
 K\,\deg_\partial(f;I')
\tag{8.1}
\]
for some \(K\geq1\).  Put
\[
 d_I:=\deg_\partial(f;I').
\]
Then
\[
 \mathcal W(A')
 \leq
 \mathcal W(A)+
 c_{\rm W}\bigl(1+\log d_I+\log K\bigr).
\tag{8.2}
\]

#### Proof

Apply Theorem 7.1 with \(d=Kd_I\) and use
\[
 \log(Kd_I)=\log K+\log d_I.
\]
\(\square\)

Proposition 5.1 proves that (8.1) is not automatic with universal
\(K\).  It is a genuine geometric certificate.

## 9. Stationary packet repair

Let \(P_h=f^h:X_h\to X_0\) be a proof-used stationary covering branch,
with \(h\leq b+2\).  Replace the ambiguous phrase “degree on an ending
multi-interval” by the following packet clause:

> **Full-base degree clause.**  For every source Wave \(B^i\), record
> its full base \(\operatorname{Base}(B^i)\) in the pulled ideal marking,
> certify one cyclic ideal collar containing that base, and verify
> \[
>   \deg_\partial(P_h;\operatorname{Base}(B^i))
>   \leq d_i^{\rm base}.
>   \tag{9.1}
> \]

The safe global quadratic degree gives
\[
 d_i^{\rm base}
 \leq\deg(P_h)\leq2^h\leq2^{b+2}.
\tag{9.2}
\]
Theorem 7.1 therefore gives one pushed Wave \(C^i\) with
\[
\begin{aligned}
 \mathcal W(B^i)
 &\leq
 \mathcal W(C^i)+
 c_{\rm W}(1+\log d_i^{\rm base})\\
 &\leq
 \mathcal W(C^i)+
 c_{\rm W}\bigl(1+(b+2)\log2\bigr).
\end{aligned}
\tag{9.3}
\]

This is exactly the common packet error needed by the already proved
paired-response algebra.  It does not require local-end collision
control.  It requires the actual source Wave and cyclic collar that
belong to the still-open typed realization.

KKL's native stationary argument treats the complementary surfaces as
having two boundary components (master 1442 and 1752), which is
consistent with this cyclic-collar model.  Those phrases do not by
themselves certify every newly proposed response packet; the packet
must still identify its actual collar and marking.

## 10. Adversarial audit

### 10.1 Short ending interval, arbitrarily large global degree

Proposition 5.1 gives \(d_I=1\) and collision count at least \(m-1\).
The full-base degree is \(m\), so the repaired invariant detects the
growth exactly.

### 10.2 Changing the logarithm base

Equation (6.10) absorbs the change into one absolute coefficient.

### 10.3 Degree one on the full base

If \(\deg_\partial(f;B(A'))=1\), every lifted leaf base lies in one
target fundamental interval.  Only the final universal separation
buffer is needed.  The theorem gives an \(O(1)\), not necessarily zero,
loss.

### 10.4 Large marking cardinality

The pruning uses the cyclic order and base span, not the number of
marked tiles.  Marking cardinality does not enter \(c_{\rm W}\).
Survival under an additional coarse filter remains a separate binary
hypothesis.

### 10.5 Noncyclic ideal boundary

No conclusion is claimed.  A noncyclic deck orbit need not admit the
linear dyadic span used in (6.5).  The actual stationary packet must
provide a cyclic collar or a new group-theoretic pruning theorem.

### 10.6 Full base crosses a critical boundary point

The interior covering is unbranched, but the ideal extension can fail
at exceptional boundary points.  Definition (3.6) requires a
finite-sheet collar or assigns infinite degree.  A finite value cannot
be inferred from a local access germ on only one side of the
exceptional point.

### 10.7 Image becomes coarse-subordinate

The pulled marking ensures target-path status at the native covering
level.  A later coarsening can discard the image.  Theorem 7.1 makes
survival under that extra filter explicit and does not count a
discarded family as a Wave output.

### 10.8 Width versus collision count

Proposition 5.1 is not promoted into a width counterexample.
The quantitative theorem uses the dyadic decomposition and Shift
bound, not collision counting alone.

## 11. Status recommendation

The original gate should be split rather than marked proved without a
definition:

```text
KKL_WAVE_LOCAL_END_COLLISION_REDUCTION
status: refuted under boundary-fiber degree on a mere ending interval
countermodel: Proposition 5.1

KKL_WAVE_FULL_BASE_COLLISION_CONTROL
status: proved for cyclic ideal-boundary collars
evidence: Lemma 6.1, Lemma 6.2, Theorem 7.1

KKL_STATIONARY_FULL_BASE_WAVE_PACKET_INSTANTIATION
status: open
requirements:
  - actual typed source Wave
  - complete full base in the pulled marking
  - cyclic collar on the actual stationary carrier
  - coarse-filter survival
  - degree bound on the full base
```

Once the last instantiation is supplied, (9.3) gives the common
\(C_b\) without any packetwise maximum of hidden constants.

No ledger or manuscript file was changed in this pass.  The typed
paired-Wave realization, uniform \(BL_0\)-survivor response, stationary
repair, VAAPC-I, UPTCR, and MLC remain open.
