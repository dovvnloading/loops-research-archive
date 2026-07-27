# Gate N1: cyclic-cover packet decomposition and relative-pruning no-go

## Status and scope

This note addresses only the abstract cyclic-cover route proposed for
`KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION` (Gate N1).  It separates two
claims that must not be conflated:

1. a finite sheet-pair decomposition of source arcs whose target
   straightenings do not cross; and
2. a degree-only bound on the source width discarded when one chooses a
   saturated target-compatible subfamily.

The second claim is false.  It fails for a fixed holomorphic
orientation-preserving degree-two annular cover, even when:

- the source family is a Borel proper lamination;
- every individual target image is simple;
- the source is already the union of only two coherent packets;
- the target image of each packet is a lamination;
- no two source leaves have the same target path, so saturation is
  vacuous; and
- the source and target annuli have fixed conformal types.

The stronger construction in Section 4A additionally makes both target
packets nested Waves with one common marked base, the same marked ends,
one common crest, and base combinatorial length three.

For every positive integer \(N\), the exact minimum discarded width in
the construction below is

\[
  N c_0,\qquad
  c_0=\frac{\log(3/2)}{\pi}>0.
\]

Consequently, there is no estimate depending only on the covering
degree.

This is an abstract no-go result.  It does **not** refute the native KKL
stationary statement.  The native family has additional structure:
one Wave base, \(\ell(BL_0)\leq 6b\), inherited unbreakability, the
fine/coarse restriction filters, and a prescribed central output.
The counterexample proves that at least one such native constraint must
enter quantitatively.  Covering degree, chord order, and saturation
alone cannot prove Gate N1.

No ledger or manuscript status is changed here.  Gate N1, VAAPC-I,
UPTCR, and MLC remain open.

## 1. Source conventions and the exact abstract question

The locked KKL source
`.tmp_wave_audit/waves-with-Misha.tex` uses:

- proper paths, arcs, laminations, and Waves at lines 1867--1875;
- extremal width of path families throughout the Wave argument;
- covering pushforward at lines 2065--2078;
- the warning that the pushforward of a lamination need not be a
  lamination at line 2072; and
- the printed broad Wave extraction statement at lines 2147--2152.

The source reconstruction in
`kkl_stationary_relative_wave_continuation_source_reconstruction_20260726.md`
shows that the actual stationary estimate needs a **relative**
source-complement bound, not an estimate comparing the whole source
width with the width of an untagged target set.

Throughout this note, extremal width means the conformal modulus of a
curve family:

\[
 \mathcal W(\Gamma)=\operatorname{Mod}(\Gamma)
 :=
 \inf_\rho\int_X\rho^2\,dA,
 \tag{1.1}
\]

where the infimum is over Borel metrics \(\rho\geq0\) satisfying

\[
 \int_\gamma \rho\,ds\geq1
 \quad\text{for every }\gamma\in\Gamma.
 \tag{1.2}
\]

This is the electrical-conductance convention: disjoint parallel
families add.

Let \(p:X'\to X\) be a finite cover and let \(\mathscr L\) be a source
lamination.  Define

\[
 \gamma\sim_p\gamma'
 \quad\Longleftrightarrow\quad
 p(\gamma)=p(\gamma')
 \tag{1.3}
\]

as equality of target paths.  A subfamily
\(\mathscr R\subset\mathscr L\) is **\(p\)-saturated** if it is a union
of the equivalence classes in (1.3).  It is **target-compatible** if
\(p_*\mathscr R\) is a lamination.

The exact abstract relative-pruning defect is

\[
 \Delta_p(\mathscr L)
 :=
 \inf\left\{
  \mathcal W(\mathscr L\setminus\mathscr R):
  \begin{array}{l}
  \mathscr R\subset\mathscr L\text{ is Borel and }p\text{-saturated},\\
  p_*\mathscr R\text{ is a lamination}
  \end{array}
 \right\}.
 \tag{1.4}
\]

The degree-only frontier claim would imply

\[
 \Delta_p(\mathscr L)\leq C_d
 \tag{1.5}
\]

for every degree-\(d\) cyclic cover and every admissible source
lamination.  Theorem 4.1 below disproves (1.5) for \(d=2\).

## 2. Two elementary modulus facts

### Lemma 2.1 (exact parallel additivity)

Let \(\Gamma_1,\ldots,\Gamma_m\) be curve families supported in pairwise
disjoint Borel open sets \(U_1,\ldots,U_m\) of one Riemann surface.
Then

\[
 \mathcal W\!\left(\bigcup_{j=1}^m\Gamma_j\right)
 =
 \sum_{j=1}^m\mathcal W(\Gamma_j).
 \tag{2.1}
\]

#### Proof

Let \(\rho\) be admissible for the union.  Its restriction to \(U_j\)
is admissible for \(\Gamma_j\).  Since the \(U_j\) are disjoint,

\[
 \int_X\rho^2\,dA
 \geq
 \sum_{j=1}^m\int_{U_j}\rho^2\,dA
 \geq
 \sum_{j=1}^m\mathcal W(\Gamma_j).
 \tag{2.2}
\]

Taking the infimum gives the lower bound in (2.1).

Conversely, fix \(\varepsilon>0\).  For each \(j\), choose an admissible
metric \(\rho_j\) supported in \(U_j\) with

\[
 \int_{U_j}\rho_j^2\,dA
 \leq\mathcal W(\Gamma_j)+\frac{\varepsilon}{m}.
 \tag{2.3}
\]

The pasted metric

\[
 \rho=\sum_{j=1}^m\rho_j
 \tag{2.4}
\]

is admissible for the union, and disjointness of the supports gives

\[
 \int_X\rho^2\,dA
 =
 \sum_{j=1}^m\int_{U_j}\rho_j^2\,dA
 \leq
 \sum_{j=1}^m\mathcal W(\Gamma_j)+\varepsilon.
 \tag{2.5}
\]

Letting \(\varepsilon\downarrow0\) proves the reverse inequality.
\(\square\)

### Lemma 2.2 (the fixed half-annulus family)

For \(c\in\mathbb R\) and \(0<r_1<r_2\), let

\[
 H(c;r_1,r_2)
 =
 \{z\in\mathbb C:r_1<|z-c|<r_2,\ \operatorname{Im}z>0\}.
 \tag{2.6}
\]

Let \(\Gamma(c;r_1,r_2)\) be the family of upper semicircles

\[
 \gamma_r(\theta)=c+r e^{i\theta},
 \qquad
 r_1\leq r\leq r_2,\quad 0<\theta<\pi.
\tag{2.7}
\]

Then

\[
 \mathcal W(\Gamma(c;r_1,r_2))
 =
 \frac{\log(r_2/r_1)}{\pi}.
 \tag{2.8}
\]

#### Proof

The conformal map \(z\mapsto\log(z-c)\) maps (2.6) to the rectangle

\[
 (\log r_1,\log r_2)\times(0,\pi).
 \tag{2.9}
\]

The semicircles become the vertical segments in this rectangle.  If a
rectangle has horizontal width \(a\) and vertical height \(h\), the
modulus of all vertical segments is \(a/h\): the constant metric
\(1/h\) gives the upper bound, and Cauchy--Schwarz on every vertical
segment, followed by integration in the horizontal variable, gives the
lower bound.  Substituting

\[
 a=\log(r_2/r_1),\qquad h=\pi
\tag{2.10}
\]

proves (2.8). \(\square\)

## 3. One fixed crossing cell

Work in the upper half of the Euclidean unit square.  Define

\[
 \mathcal A
 :=
 \Gamma(7/20;1/5,3/10),
 \qquad
 \mathcal B
 :=
 \Gamma(1/2;1/5,3/10).
 \tag{3.1}
\]

Every leaf of either family lies in

\[
 Q=(0,1)\times(0,1).
 \tag{3.2}
\]

The endpoints of a leaf \(\alpha\in\mathcal A\) lie in the two
intervals

\[
 I_1=(1/20,3/20),
 \qquad
 I_3=(11/20,13/20),
 \tag{3.3}
\]

while the endpoints of a leaf \(\beta\in\mathcal B\) lie in

\[
 I_2=(1/5,3/10),
 \qquad
 I_4=(7/10,4/5).
 \tag{3.4}
\]

These four intervals occur in the strict order

\[
 I_1<I_2<I_3<I_4
\tag{3.5}
\]

along the real boundary.

### Lemma 3.1 (complete crossing)

Every leaf of \(\mathcal A\) intersects every leaf of
\(\mathcal B\).

#### Proof

Let \(\alpha\in\mathcal A\) and \(\beta\in\mathcal B\).  Their four
endpoints on the real boundary occur in the alternating order

\[
 a_-<b_-<a_+<b_+.
\tag{3.6}
\]

A simple crosscut separates a disk into two components, and the two
boundary intervals between its endpoints lie on different sides.  The
endpoints \(b_-\) and \(b_+\) lie on the two different boundary
intervals determined by \(a_-,a_+\).  Hence any crosscut joining
\(b_-\) to \(b_+\) must meet \(\alpha\).  In particular \(\beta\)
meets \(\alpha\). \(\square\)

### Lemma 3.2 (equal positive width)

Both cell families have the same positive width

\[
 \mathcal W(\mathcal A)
 =
 \mathcal W(\mathcal B)
 =
 c_0
 :=
 \frac{\log(3/2)}{\pi}.
 \tag{3.7}
\]

#### Proof

Apply Lemma 2.2 with \(r_1=1/5\) and \(r_2=3/10\).
\(\square\)

Notice what this cell does and does not say.  It is fully consistent
with every local Shift-type conclusion saying that two transverse
families cannot both have arbitrarily large width: each side has the
fixed width \(c_0\).  The obstruction below comes from placing
arbitrarily many independent copies of this bounded cell in parallel.

## 4. Fixed-cover counterexample

Let

\[
 A=(\mathbb R/\mathbb Z)\times(0,1),
 \qquad
 A'=(\mathbb R/2\mathbb Z)\times(0,1),
 \tag{4.1}
\]

with the conformal coordinates induced by \(z=x+iy\).  Define

\[
 p:A'\longrightarrow A,
 \qquad
 p([x]_{2\mathbb Z},y)=([x]_{\mathbb Z},y).
 \tag{4.2}
\]

This is a holomorphic, orientation-preserving, unbranched cyclic cover
of degree two.  It extends to a degree-two cover on each ideal boundary
circle.  Both \(A\), \(A'\), and \(p\) are fixed for the rest of the
construction.

Fix \(N\geq1\), put

\[
 s_N=\frac1{3N},
 \qquad
 x_i=\frac{i}{N},
 \quad 0\leq i<N,
 \tag{4.3}
\]

and define the pairwise disjoint boundary cells

\[
 Q_i
 =
 (x_i,x_i+s_N)\times(0,s_N)
 \subset A.
 \tag{4.4}
\]

The conformal affine maps

\[
 \psi_i:Q\longrightarrow Q_i,
 \qquad
 \psi_i(x,y)=(x_i+s_Nx,s_Ny)
\tag{4.5}
\]

give translated/scaled copies

\[
 \mathcal A_i=(\psi_i)_*\mathcal A,
 \qquad
 \mathcal B_i=(\psi_i)_*\mathcal B.
\tag{4.6}
\]

Conformal invariance and Lemma 3.2 give

\[
 \mathcal W(\mathcal A_i)
 =
 \mathcal W(\mathcal B_i)
 =
 c_0
\tag{4.7}
\]

for every \(i\) and every \(N\).

Each \(Q_i\) has two disjoint lifts to \(A'\):

\[
 Q_i^0=Q_i,
 \qquad
 Q_i^1=Q_i+(1,0).
\tag{4.8}
\]

Let \(\widehat{\mathcal A}_i\) be the lift of
\(\mathcal A_i\) in \(Q_i^0\), and let
\(\widehat{\mathcal B}_i\) be the lift of
\(\mathcal B_i\) in \(Q_i^1\).  Finally set

\[
 \mathscr L_N
 =
 \bigcup_{i=0}^{N-1}\widehat{\mathcal A}_i
 \ \cup\
 \bigcup_{i=0}^{N-1}\widehat{\mathcal B}_i.
\tag{4.9}
\]

### Proposition 4.1 (all regularity and packet clauses)

For every \(N\), the family \(\mathscr L_N\) has all of the following
properties.

1. It is a Borel lamination by proper simple arcs in \(A'\).
2. Every individual image under \(p\) is a simple proper arc.
3. No two distinct source leaves have the same target path.
4. It is already partitioned into two coherent packets

   \[
   \mathscr P_{\mathcal A}
   =
   \bigcup_i\widehat{\mathcal A}_i,
   \qquad
   \mathscr P_{\mathcal B}
   =
   \bigcup_i\widehat{\mathcal B}_i,
   \tag{4.10}
   \]

   and each target image

   \[
   p_*\mathscr P_{\mathcal A}=\bigcup_i\mathcal A_i,
   \qquad
   p_*\mathscr P_{\mathcal B}=\bigcup_i\mathcal B_i
   \tag{4.11}
   \]

   is a lamination.
5. Saturation under (1.3) is vacuous.

#### Proof

Each family in (4.9) is continuously parametrized by the radius
\(r\in[1/5,3/10]\), hence is compact, in particular Borel, in the
compact-open topology on
proper paths.  Its leaves are pairwise disjoint concentric
semicircles.  Families with different \(i\) have supports in disjoint
cells.  The \(\mathcal A\)-families lie in the first cover sheet and
the \(\mathcal B\)-families lie in the second; therefore all source
supports are pairwise disjoint.  This proves clause 1.

The restriction of \(p\) to every \(Q_i^0\) and \(Q_i^1\) is a conformal
homeomorphism onto \(Q_i\).  Hence every target image is simple and
clause 2 holds.  Within each lifted cell the map is injective; an
\(\mathcal A_i\)-leaf cannot equal a \(\mathcal B_i\)-leaf because
Lemma 3.1 says that they cross; and different target cells are
disjoint.  This proves clause 3 and therefore clause 5.

Within either packet in (4.10), leaves from one cell are disjoint and
leaves from different cells have disjoint supports.  The same is true
after applying \(p\), proving clause 4. \(\square\)

### Theorem 4.2 (exact unbounded relative-pruning defect)

For the fixed degree-two cover (4.2),

\[
 \Delta_p(\mathscr L_N)=Nc_0.
\tag{4.12}
\]

In particular,

\[
 \sup_N\Delta_p(\mathscr L_N)=+\infty.
\tag{4.13}
\]

#### Proof

Let \(\mathscr R\subset\mathscr L_N\) be any target-compatible
subfamily.  The lower bound does not require saturation.

Fix \(i\).  If \(\mathscr R\) contains one leaf of
\(\widehat{\mathcal A}_i\) and one leaf of
\(\widehat{\mathcal B}_i\), their target images intersect by
Lemma 3.1.  This contradicts target compatibility.  Therefore at least
one of the following alternatives holds:

\[
 \mathscr R\cap\widehat{\mathcal A}_i=\varnothing,
 \qquad\text{or}\qquad
 \mathscr R\cap\widehat{\mathcal B}_i=\varnothing.
\tag{4.14}
\]

In the first case the full family
\(\widehat{\mathcal A}_i\) lies in
\(\mathscr L_N\setminus\mathscr R\); in the second case the full family
\(\widehat{\mathcal B}_i\) lies there.  Choose one such missing full
family and call it \(\mathscr D_i\).

The \(N\) families \(\mathscr D_i\) have pairwise disjoint source
supports.  Covering invariance and (4.7) give

\[
 \mathcal W(\mathscr D_i)=c_0.
\tag{4.15}
\]

By monotonicity and Lemma 2.1,

\[
 \begin{aligned}
 \mathcal W(\mathscr L_N\setminus\mathscr R)
 &\geq
 \mathcal W\!\left(\bigcup_{i=0}^{N-1}\mathscr D_i\right)\\
 &=\sum_{i=0}^{N-1}\mathcal W(\mathscr D_i)
 =Nc_0.
 \end{aligned}
\tag{4.16}
\]

Taking the infimum over all saturated target-compatible
\(\mathscr R\) proves

\[
 \Delta_p(\mathscr L_N)\geq Nc_0.
\tag{4.17}
\]

For the reverse inequality, retain the whole
\(\mathcal A\)-packet:

\[
 \mathscr R=\mathscr P_{\mathcal A}.
\tag{4.18}
\]

It is saturated by Proposition 4.1, and its target image is a
lamination.  Its complement is the disjoint union of the \(N\)
\(\widehat{\mathcal B}_i\), so Lemma 2.1 and (4.7) give

\[
 \mathcal W(\mathscr L_N\setminus\mathscr R)=Nc_0.
\tag{4.19}
\]

This proves (4.12), and (4.13) follows because \(c_0>0\).
\(\square\)

### Corollary 4.3 (degree and packet count do not bound the loss)

There is no function \(C(d)\) such that every degree-\(d\) cyclic cover
and every Borel proper source lamination satisfying the individual
simplicity condition has a saturated target-compatible subfamily
\(\mathscr R\) with

\[
 \mathcal W(\mathscr L\setminus\mathscr R)\leq C(d).
\tag{4.20}
\]

The conclusion remains false if the hypotheses additionally assert in
advance that the source is the union of \(O(d^2)\) coherent packets
whose target images are laminations.

#### Proof

Use Theorem 4.2 with \(d=2\).  Proposition 4.1 supplies only two
packets, while \(Nc_0\) exceeds every proposed \(C(2)\) for large
\(N\). \(\square\)

## 4A. Stronger counterexample: two nested packets with one common crest

The preceding cells are spatially separated.  One might hope that the
native Wave geometry rules them out because a Wave has one connected
base and a common crest.  That hope is still too weak: independent
conflicts can be nested at exponentially separated scales around one
crest.

Keep the fixed cover \(p:A'\to A\) from (4.1)--(4.2).  Work in a small
flat boundary chart centered at

\[
 x_*=\frac12
\tag{4A.1}
\]

on the lower ideal boundary of \(A\).  Fix

\[
 R_{\max}=\frac1{20},
 \qquad
 R_k=R_{\max}4^{\,k-N},
 \quad 1\leq k\leq N.
\tag{4A.2}
\]

Thus

\[
 R_{k+1}=4R_k,
 \qquad
 R_N=R_{\max}.
\tag{4A.3}
\]

For each \(k\), define two semicircle bands:

\[
 \mathcal E_k
 :=
 \Gamma(x_*;R_k,11R_k/10),
\tag{4A.4}
\]

and

\[
 \mathcal F_k
 :=
 \Gamma(x_*+R_k/4;R_k,11R_k/10).
\tag{4A.5}
\]

All these arcs lie in the fixed boundary chart because their horizontal
and vertical sizes are at most

\[
 \frac14R_{\max}+\frac{11}{10}R_{\max}
 =
 \frac{27}{20}R_{\max}
 <
 \frac1{10}.
\tag{4A.6}
\]

Lemma 2.2 gives the scale-independent width

\[
 \mathcal W(\mathcal E_k)
 =
 \mathcal W(\mathcal F_k)
 =
 c_*,
 \qquad
 c_*:=\frac{\log(11/10)}{\pi}>0.
\tag{4A.7}
\]

### Lemma 4A.1 (exact matching conflict graph)

The two unions

\[
 \mathcal E=\bigcup_{k=1}^N\mathcal E_k,
 \qquad
 \mathcal F=\bigcup_{k=1}^N\mathcal F_k
\tag{4A.8}
\]

are nested laminations.  Moreover,

\[
 \text{a leaf of }\mathcal E_k
 \text{ meets a leaf of }\mathcal F_\ell
 \quad\Longleftrightarrow\quad
 k=\ell.
\tag{4A.9}
\]

When \(k=\ell\), every \(\mathcal E_k\)-leaf meets every
\(\mathcal F_k\)-leaf.

#### Proof

The \(\mathcal E_k\) are concentric about \(x_*\).  If \(\ell>k\),
then every \(\mathcal E_\ell\)-radius is at least

\[
 R_\ell\geq4R_k
 >
 \frac{11}{10}R_k,
\tag{4A.10}
\]

so every \(\mathcal E_\ell\)-semicircle strictly contains every
\(\mathcal E_k\)-semicircle and the two do not meet.

For the \(\mathcal F\)-families, suppose again that \(\ell>k\).  The
distance between their centers is

\[
 \frac14(R_\ell-R_k)<\frac14R_\ell.
\tag{4A.11}
\]

Adding the largest possible inner radius gives

\[
 \frac14(R_\ell-R_k)+\frac{11}{10}R_k
 \leq
 \frac14R_\ell+\frac{11}{40}R_\ell
 =
 \frac{21}{40}R_\ell
 <
 R_\ell.
\tag{4A.12}
\]

Thus every \(\mathcal F_k\)-semicircle lies strictly inside every
\(\mathcal F_\ell\)-semicircle.  This proves that both unions in
(4A.8) are laminations and are nested by level.

Now take one radius

\[
 r\in[R_k,11R_k/10]
\tag{4A.13}
\]

from \(\mathcal E_k\), and one radius

\[
 s\in[R_k,11R_k/10]
\tag{4A.14}
\]

from \(\mathcal F_k\).  Relative to \(x_*\), the endpoint intervals are

\[
 [-r,r]
\quad\text{and}\quad
 [R_k/4-s,R_k/4+s].
\tag{4A.15}
\]

The inequalities

\[
 -r<R_k/4-s<r<R_k/4+s
\tag{4A.16}
\]

are strict because

\[
 |r-s|\leq R_k/10<R_k/4.
\tag{4A.17}
\]

Thus the endpoints alternate, and the crosscut argument from
Lemma 3.1 shows that the leaves meet.  This holds for every choice of
\(r,s\), proving complete crossing at equal levels.

If \(\ell>k\), every \(\mathcal F_\ell\)-semicircle contains every
\(\mathcal E_k\)-semicircle.  Indeed, the center distance plus the
largest inner radius is bounded by

\[
 \frac14R_\ell+\frac{11}{10}R_k
 \leq
 \left(\frac14+\frac{11}{40}\right)R_\ell
 =
 \frac{21}{40}R_\ell
 <
 R_\ell,
\tag{4A.18}
\]

the smallest outer radius.  Hence they do not meet.

If \(k>\ell\), every \(\mathcal E_k\)-semicircle contains every
\(\mathcal F_\ell\)-semicircle, because

\[
 \frac14R_\ell+\frac{11}{10}R_\ell
 =
 \frac{27}{20}R_\ell
 \leq
 \frac{27}{80}R_k
 <
 R_k.
\tag{4A.19}
\]

This proves the reverse implication in (4A.9). \(\square\)

### Lemma 4A.2 (one common marked crest)

There is an ideal marking of the target annulus by five intervals,
independent in cardinality of \(N\), such that both
\(\mathcal E\) and \(\mathcal F\) are Waves with the same two marked
ends and the same marked crest.

#### Proof

In the coordinate \(\xi=x-x_*\), define the three consecutive marked
intervals

\[
 \begin{aligned}
 I_L&=(-6R_{\max}/5,-R_1/2),\\
 C&=(-R_1/2,R_1/2),\\
 I_R&=(R_1/2,7R_{\max}/5).
 \end{aligned}
\tag{4A.20}
\]

Let \(O\) be the complementary open interval on that boundary circle,
and let \(I_{\rm in}\) be the entire other ideal boundary component.
Together with the four separating endpoints,

\[
 \mathcal I_N=\{I_L,C,I_R,O,I_{\rm in}\}
\tag{4A.21}
\]

is an ideal marking of cardinality five.  Its restriction to the
boundary component supporting the Waves has cardinality four.

Every left endpoint of an \(\mathcal E\)-leaf lies between
\(-11R_{\max}/10\) and \(-R_1\).  Every left endpoint of an
\(\mathcal F\)-leaf lies between
\(-17R_{\max}/20\) and \(-3R_1/4\).  Hence all left endpoints lie in
\(I_L\).  Similarly:

- every \(\mathcal E\)-right endpoint lies between
  \(R_1\) and \(11R_{\max}/10\);
- every \(\mathcal F\)-right endpoint lies between
  \(5R_1/4\) and \(27R_{\max}/20\);

so all right endpoints lie in \(I_R\).

Let \(B\) be the connected multi-interval formed from
\(I_L,C,I_R\) and their separating endpoints.  Each semicircle is
boundary-parallel on the \(B\)-side and hence subordinate to \(B\).
Because marked intervals are indivisible in the definition of a
multi-interval, the two ends of either packet are \(I_L\) and \(I_R\).
Its crest is therefore the intervening marked interval \(C\), together
with the two separating endpoints under the literal set-difference
convention.

Thus both packets have one common connected base of combinatorial
length three, the same two marked ends, and the same marked crest.
\(\square\)

Lift \(\mathcal E\) to the first sheet of \(A'\) and
\(\mathcal F\) to the second sheet.  Denote the resulting source
packets by \(\widehat{\mathcal E}\) and
\(\widehat{\mathcal F}\), and set

\[
 \mathscr N_N
 =
 \widehat{\mathcal E}\cup\widehat{\mathcal F}.
\tag{4A.22}
\]

As in Proposition 4.1, this is a Borel proper source lamination, every
target image is simple, equal-target saturation is vacuous, and each
of the two target packet images is a Wave with the common marked crest
from Lemma 4A.2.

There is also a single bounded-complexity source Wave containing both
packets.  Under the pulled outer-boundary marking, let
\(B^0\) and \(B^1\) be the two lifts of the three-interval target base
\(B\), and let \(O^0\) be the one lifted complementary interval lying
between them in the positive boundary order.  Then

\[
 B'=B^0\cup O^0\cup B^1
\tag{4A.22a}
\]

with the intervening marked endpoints is a connected source
multi-interval of combinatorial length

\[
 \ell(B')=3+1+3=7.
\tag{4A.22b}
\]

Every \(\widehat{\mathcal E}\)-leaf is subordinate to
\(B^0\subset B'\), and every \(\widehat{\mathcal F}\)-leaf is
subordinate to \(B^1\subset B'\).  Hence \(\mathscr N_N\) itself is a
source Wave whose minimal base has combinatorial length at most seven.
This observation still does not supply native KKL unbreakability or a
dynamical \(BL_0\) shift.

### Theorem 4A.3 (common-crest nested pruning no-go)

For the fixed degree-two cover (4.2),

\[
 \Delta_p(\mathscr N_N)=Nc_*.
\tag{4A.23}
\]

Therefore degree two, a source Wave of base length at most seven, two
target packets, nestedness of each packet, a common target Wave base of
combinatorial length three, common marked ends, and a common marked
crest do not imply an \(O(1)\) saturated relative-pruning bound.

#### Proof

By Lemma 4A.1, the target conflict graph between the two packet
laminations is exactly the matching

\[
 \{(\mathcal E_k,\mathcal F_k):1\leq k\leq N\}.
\tag{4A.24}
\]

At each level a target-compatible retained family must omit all of
\(\widehat{\mathcal E}_k\) or all of
\(\widehat{\mathcal F}_k\).  The source supports of all selected
missing level families are pairwise disjoint: levels are separated by
strict circle containment within a sheet, and the two packet sheets
are disjoint.  Lemma 2.1 and (4A.7) therefore give the lower bound

\[
 \mathcal W(\mathscr N_N\setminus\mathscr R)\geq Nc_*
\tag{4A.25}
\]

for every target-compatible \(\mathscr R\).

Retaining the complete \(\widehat{\mathcal E}\)-packet is saturated and
target-compatible, and its complement has width

\[
 \sum_{k=1}^N\mathcal W(\widehat{\mathcal F}_k)=Nc_*.
\tag{4A.26}
\]

This proves (4A.23). \(\square\)

### Native significance of Theorem 4A.3

The stronger construction rules out three tempting repairs:

1. "there are only two coherent target packets";
2. "both packets are nested around one crest"; and
3. "the source and target Wave bases have uniformly bounded
   combinatorial length."

None controls the number of independent **scale levels** at which the
two packets switch containment order.  In (4A.24), the switch occurs
once at every geometric scale \(R_k\), producing an unbounded matching.

What can exclude this in the native stationary KKL family is not static
Wave topology.  A native proof must use a genuinely dynamical
constraint, for example:

- inherited \((N-n-1)\)-step unbreakability plus the shifting action on
  \(BL_0\), to show that repeated containment switches force a leaf to
  meet a dynamical shift of itself;
- a bounded route/return itinerary theorem showing that only
  \(O_b(1)\) switch levels survive the fine/coarse restriction filters;
  or
- a total Shift-window estimate that charges the **sum** of the widths
  of all switch levels, not merely the width at one level.

Theorem 4A.3 is not an actual KKL block: it has no pseudo-quadratic-like
relation, no inherited iterate, and no native fine/coarse filtering.
It proves precisely that those missing dynamical data are essential,
rather than optional technical decoration.

## 5. A nonperipheral variant

The fixed-cover construction uses boundary-parallel proper arcs.  This
is enough to refute the abstract statement as posed, but it is useful to
check that merely banning boundary-parallel arcs does not create a
degree-only theorem.

Let

\[
 A_N=(\mathbb R/N\mathbb Z)\times(0,1),
 \qquad
 A_N'=(\mathbb R/2N\mathbb Z)\times(0,1),
\tag{5.1}
\]

and let \(p_N:A_N'\to A_N\) be reduction of the horizontal coordinate
modulo \(N\).  In each unit cell
\((i,i+1)\times(0,1)\), choose:

- a positive-width foliation by disjoint crosscuts from a short
  lower-left interval to a short upper-right interval; and
- its reflection, a positive-width foliation from a short lower-right
  interval to a short upper-left interval.

The two families may be taken as affine images of one fixed vertical
rectangle foliation.  Their common width \(c_1>0\) is independent of
\(i\) and \(N\).  Endpoint order on the two boundary components shows
that every leaf of the first family meets every leaf of the reflected
family.

Lift the first family in each cell to the first sheet of \(A_N'\) and
the reflected family to the second sheet.  The proof of Theorem 4.2
then gives

\[
 \Delta_{p_N}(\mathscr L_N^{\rm np})=Nc_1.
\tag{5.2}
\]

Every leaf now joins the two distinct ideal boundary components and is
nonperipheral.  Here the conformal type varies with \(N\), but the
topological type remains an annulus and the degree remains two.
Therefore a degree-only estimate still fails after a nonperipheral
restriction.

This variant is not needed for Corollary 4.3.  Its role is to prevent
the invalid repair “delete boundary-parallel leaves and invoke degree
alone.”

## 6. What cyclic chord order actually proves

The no-go above does not mean that sheet-pair bookkeeping is useless.
At the proper-arc-class level, a precise \(d^2\) packet statement is
true for disk chords.  It is strictly qualitative and does not imply a
bounded deletion charge.

### Proposition 6.1 (disk chord packet lemma)

Parametrize the source boundary circle by
\(\mathbb R/d\mathbb Z\), the target boundary circle by
\(\mathbb R/\mathbb Z\), and the degree-\(d\) boundary cover by

\[
 [x]_d\longmapsto[x]_1.
\tag{6.1}
\]

Let \(\mathscr C\) be a Borel lamination of geodesic chords in the
source disk.  Assume:

1. no endpoint lies over the chosen target cut \([0]_1\); and
2. the two target endpoints of every chord are distinct.

Straighten every target image to the unique target geodesic chord with
the same two endpoints.  Then \(\mathscr C\) admits a Borel partition
into at most \(d^2\) occurrence packets, each of whose target
straightenings is a lamination.

#### Proof

For each unoriented source chord choose its endpoint representatives

\[
 0<x<y<d.
\tag{6.2}
\]

Write

\[
 x=a+u,\qquad y=b+v,
\tag{6.3}
\]

where

\[
 0\leq a\leq b\leq d-1,
\qquad
 0<u,v<1.
\tag{6.4}
\]

If \(a=b\), put the chord in the packet \((a,a,0)\).  If \(a<b\), put
it in

\[
 (a,b,+)\quad\text{when }u<v,
\qquad
 (a,b,-)\quad\text{when }v<u.
\tag{6.5}
\]

The equality \(u=v\) would give equal target endpoints, excluded by
hypothesis 2.  The number of packets is

\[
 d+2\binom d2=d^2.
\tag{6.6}
\]

It remains to check target noncrossing within one packet.  The
diagonal packet \((a,a,0)\) is immediate: the boundary cover is
order-preserving on the single sheet interval \((a,a+1)\), so it
preserves nonalternation of endpoints.

Now fix \(a<b\) and two distinct source chords in one packet.  Relabel
them so that

\[
 x_1<x_2.
\tag{6.7}
\]

All \(x\)-endpoints occur in the source sheet interval
\((a,a+1)\), and all \(y\)-endpoints occur later in
\((b,b+1)\).  If \(y_1<y_2\), the source endpoints would occur in the
alternating order

\[
 x_1<x_2<y_1<y_2,
\tag{6.8}
\]

contradicting that \(\mathscr C\) is a lamination.  Hence

\[
 y_2<y_1.
\tag{6.9}
\]

Equivalently,

\[
 u_1<u_2,\qquad v_2<v_1.
\tag{6.10}
\]

In the \(+\) packet, \(u_j<v_j\) for \(j=1,2\), and therefore

\[
 u_1<u_2<v_2<v_1.
\tag{6.11}
\]

The two target chords are nested.  In the \(-\) packet,
\(v_j<u_j\), and therefore

\[
 v_2<v_1<u_1<u_2.
\tag{6.12}
\]

They are nested again.  Thus no two target straightenings in one
packet cross.

Finally, the endpoint maps and the finite comparisons in (6.3)--(6.5)
are Borel, so the packets are Borel. \(\square\)

### Qualification 6.2 (what Proposition 6.1 does not prove)

Proposition 6.1 is a theorem about proper-arc classes represented in
minimal position.  It does not prove that arbitrary raw image paths
under a noninjective holomorphic map are pairwise disjoint: two simple
representatives of noncrossing arc classes may form removable bigons.
For an analytic use, one needs either:

- canonical/geodesic representatives and an invariance theorem for the
  measured family; or
- a direct no-bigon statement for the actual pushed paths.

Nor does the proposition preserve one pure sheet-pair label after
saturating identical target paths.  One target chord can have
occurrences in several sheet-pair packets.  Saturation retains all
those occurrences and must record their finite multiplicity vector.
There are at most \(d^2\) endpoint sheet pairs, but this does not bound
the number or total width of independent target crossing cells.

Theorem 4.2 already grants the strongest favorable version of the
packet conclusion—two actual coherent packets—and still disproves the
degree-only quantitative conclusion.

## 7. Why pairwise extremal intersection estimates cannot repair the claim

Any Shift or extremal-intersection estimate is local to a conflicting
pair of curve families.  Abstractly, suppose a crossing relation gives

\[
 \min\{\mathcal W(E),\mathcal W(F)\}\leq C
\tag{7.1}
\]

for each completely crossing pair \((E,F)\).  This does not imply a
uniform bound on the total deletion needed to make the target family a
lamination.

In Theorem 4.2 the conflict graph is the disjoint union

\[
 K_2\ \dot\cup\ K_2\ \dot\cup\cdots\dot\cup\ K_2
\quad(N\text{ copies}),
\tag{7.2}
\]

where the two vertices of the \(i\)-th edge are
\(\widehat{\mathcal A}_i\) and
\(\widehat{\mathcal B}_i\), both of weight \(c_0\).  Every local
intersection estimate is satisfied with the fixed constant \(c_0\),
but every vertex cover has weight at least \(Nc_0\).  Target-compatible
selection is exactly an independent-set choice in this example, and
discarding source width is exactly the complementary vertex-cover
cost.

Thus the missing quantity is not:

- the covering degree;
- the number of sheet-pair packet types;
- the maximum multiplicity of one target path; or
- a pairwise Shift bound.

It is the **total weighted conflict-cover cost**.

## 8. The replacement invariant forced by the counterexample

For a source family \(\mathscr L\), define the weighted conflict-cover
defect by (1.4).  When the desired target output must satisfy additional
conditions, those conditions must be included in the admissible set,
not added after the estimate.

For the native stationary stage, the minimally honest object is

\[
 \begin{aligned}
 \Delta^{\rm N1}_{F,n}(S_n)
 :=
 \inf\{&
 \mathcal W(S_n\setminus R):\\
 &
 R\subset S_n\text{ is a Borel occurrence-saturated source subwave},\\
 &
 F_*R\text{ is an actual no-short Wave with the required }BL_0
 \text{ ending data},\\
 &
 R\text{ survives the fine/coarse marking filters and preserves the}\\
 &
 \text{inherited }(N-n-1)\text{-step unbreakability}\}.
 \end{aligned}
 \tag{8.1}
\]

This is not asserted to be finite or attained.  Those are part of Gate
N1.  The required native theorem has to prove, with all clauses in
(8.1) realized,

\[
 \Delta^{\rm N1}_{F,n}(S_n)\leq C_b.
\tag{8.2}
\]

For a less tautological necessary diagnostic, define the
**disjoint complete-conflict packing**

\[
 \Pi_p(\mathscr L)
 =
 \sup
 \sum_k
 \min\{\mathcal W(E_k),\mathcal W(F_k)\},
\tag{8.3}
\]

where:

1. all \(E_k,F_k\) are source sublaminations with pairwise disjoint
   source supports across distinct \(k\);
2. every target leaf in \(p_*E_k\) meets every target leaf in
   \(p_*F_k\); and
3. the families are saturated with respect to equal target paths.

Every target-compatible selection must delete one whole side of each
complete-conflict pair, so Lemma 2.1 gives

\[
 \Delta_p(\mathscr L)\geq\Pi_p(\mathscr L).
\tag{8.4}
\]

For Theorem 4.2,

\[
 \Pi_p(\mathscr L_N)=\Delta_p(\mathscr L_N)=Nc_0.
\tag{8.5}
\]

A bound on \(\Pi_p\) is necessary but, for an arbitrary nonperfect
conflict graph, need not be sufficient to bound \(\Delta_p\).  A
positive native proof therefore needs one of the following additional
structures:

1. a direct bound on \(\Delta^{\rm N1}_{F,n}\);
2. a proof that the native conflict graph is an interval/perfect graph,
   followed by a packing bound;
3. a decomposition into at most \(C_b\) Shift windows together with an
   additive total-width estimate across those windows; or
4. a stronger one-common-interval pruning theorem whose hypotheses are
   verified for the actual retained source occurrences.

The fact \(\ell(BL_0)\leq6b\) is a plausible input to such a theorem,
but it is not by itself the theorem: one must still prove that every
conflict cell is charged to one of those boundedly many marked windows
without repeated independent occupancy.

## 9. Adversarial audit

| attack | verification |
|---|---|
| The degree grows with \(N\). | False.  The cover (4.2) is fixed and has degree two for every \(N\). |
| The conformal type degenerates with \(N\). | False for the main construction.  Both annuli in (4.1) are fixed. |
| The source is not a lamination. | False.  All source cell supports are pairwise disjoint; within a cell the leaves are concentric semicircles. |
| The family is nonmeasurable. | False.  Each cell family is continuously parametrized by its radius; a finite union is Borel. |
| Some target path self-intersects. | False.  The cover is injective on every lifted cell. |
| Multiplicity collapse creates the loss. | False.  Every target path has exactly one occurrence in \(\mathscr L_N\). |
| Too many packet types create the loss. | False.  There are exactly two coherent packets. |
| Spatially separated crests create the loss. | False in the stronger model.  Theorem 4A.3 uses two nested packets with the same marked ends and one common crest. |
| Unbounded Wave-base combinatorics create the loss. | False in the stronger model.  Its source is a Wave with base length at most seven, and each target packet has the same base of length three. |
| Saturation repairs the loss. | False.  Saturation is already trivial. |
| Only one exceptional leaf crosses. | False.  In each cell every \(\mathcal A_i\)-leaf crosses every \(\mathcal B_i\)-leaf. |
| The cell widths tend to zero. | False.  Conformal scaling preserves the exact width \(c_0=\log(3/2)/\pi\). |
| Width additivity was assumed. | Lemma 2.1 proves exact additivity from the modulus variational definition. |
| A pairwise Shift estimate rules out the construction. | False.  Each cell has bounded width.  The unbounded quantity is the number of independent conflict cells. |
| Removing peripheral arcs repairs the degree-only theorem. | False in general; Section 5 gives a nonperipheral variant, though its annulus conformal type varies. |
| The counterexample disproves native Gate N1. | False.  It lacks the full native one-Wave, \(BL_0\), unbreakability, and restriction-filter package. |

## 10. Exact conclusion for Gate N1

The abstract frontier lemma has the following final status.

### Proved

1. At the geodesic proper-arc-class level in a disk, cyclic endpoint
   order gives at most \(d^2\) sheet-pair/sign packets with
   noncrossing target straightenings (Proposition 6.1).
2. The exact relative-pruning quantity is the weighted
   conflict-cover defect (1.4), not target set-theoretic width.
3. Independent conflict cells add exactly in source extremal width.

### Refuted

The implication

\[
\text{degree }d
+O(d^2)\text{ coherent packets}
+\text{nested common-crest Wave packets}
+\text{saturation}
+\text{pairwise intersection bounds}
\Longrightarrow
\Delta_p(\mathscr L)=O_d(1)
\tag{10.1}
\]

is false.  Theorem 4A.3 is a fixed-degree, fixed-cover,
common-crest positive-width counterexample.

### Still open and immediately required

To prove native Gate N1, one must use the actual stationary Wave
structure to rule out the analogue of the \(N\)-edge conflict matching.
The next valid analytic target is:

> prove that every complete target-conflict packing for the actual
> retained, no-short, inherited-unbreakable \(S_n\) is charged to
> boundedly many \(BL_0\) Shift windows with total width \(O_b(1)\);
> then prove that the native conflict relation has the interval/perfect
> structure needed to turn that packing bound into the saturated
> relative continuation (8.2).

Until both parts are proved on the actual KKL occurrence family, the
stationary relative Wave continuation remains open.
