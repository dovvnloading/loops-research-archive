# KKL stationary segmented-occurrence binder

## 1. Scope and verdict

This note audits one precise semantic question:

> Does a path occurrence in the iterated KKL action \(F_*^h\) have to
> be represented by one path in Kahn's \(h\)-fold pullback whose
> one-step coordinates are all the **full** proper paths selected at
> the successive KKL stages?

The answer is **no**.

KKL define an immersion restriction by **image containment**.  If
\(\gamma_{r+1}\) is selected at the next stage, the source gives

\[
 \iota\bigl(|\gamma_{r+1}|\bigr)
 \subset
 f\bigl(|\gamma_r|\bigr),
\tag{1.1}
\]

not equality of the two full parameterized paths.  In general,
\(\gamma_{r+1}\) occupies a strict parameter window in the preceding
covering image.  A common path in the \(h\)-fold relation exists only
after all earlier coordinates are truncated to the nested surviving
windows.  Those truncated coordinates need not be proper paths.

Consequently:

1. the exact equalizer theorem in
   `kkl_stationary_two_occurrence_binder_design.md`, Theorem 6.1, is a
   correct categorical theorem under its stated equality hypothesis;
2. its proposed semantic occurrence core is too restrictive to model
   every valid sequential \(F_*^h\)-occurrence;
3. exact common-parameter equality of the **full** stage paths is not
   necessary for a sequential KKL occurrence;
4. the correct finite invariant is a flag of full stage paths together
   with the occurrence window at every transition;
5. the flag reconstructs a unique compatible path at every finite
   prefix of the Kahn tower, while one terminal tower path alone loses
   the discarded shoulders of the earlier proper paths.

The finite reconstruction theorem is proved below.  It does not prove
that either portion proposed in KKL line 1603 supplies such a flag.
It also proves no proper ideal landing, marking, filter survival,
attachment control, Wave membership, or terminal noncollision for the
actual KKL stationary block.

In particular, this note does **not** prove or promote

```text
KKL_STATIONARY_TWO_OCCURRENCE_BINDER
KKL_STATIONARY_RETAINED_PORTION_REALIZATION
KKL_STATIONARY_TWO_SIDED_WAVE_NONCOLLISION
VAAPC-I
UPTCR
MLC
```

All remain open.

## 2. Locked sources and exact source semantics

The locked KKL source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The relevant source clauses are:

- line 406: paths are considered up to reparameterization; a proper
  path is a map \((0,1)\to V\) having a continuous extension to the
  ideal closure with both endpoints in the ideal boundary;
- lines 1844--1875: ideal markings, proper paths, simple arcs,
  laminations, and Waves;
- lines 2081--2084: for an immersion
  \(\iota:\mathcal V'\to\mathcal V\),
  \(\iota^*\beta\) is the set of proper paths in \(\mathcal V'\)
  **contained in** \(\iota^{-1}(\beta)\);
- lines 2096--2097: only fine-marked restriction paths which are not
  subordinate to one interval of \(\iota^*\mathcal I\) are retained;
- lines 2128--2142:
  \(F_*=f_*\iota^*\) acts successively on path families and arcs; and
- line 2161: a path breaks when its one-step \(F_*\)-image is not a
  single path.

Thus, if \(\beta_{r-1}\) is the full path entering stage \(r\), a
retained stage path \(\gamma_r\) satisfies

\[
 |\gamma_r|
 \subset
 \iota^{-1}(|\beta_{r-1}|),
 \qquad
 \beta_r=f\circ\gamma_r.
\tag{2.1}
\]

The first relation in (2.1) says only

\[
 \iota(|\gamma_r|)\subset|\beta_{r-1}|.
\tag{2.2}
\]

It does not say

\[
 \iota\circ\gamma_r=\beta_{r-1}
\tag{2.3}
\]

after reparameterizing both paths by self-homeomorphisms of
\((0,1)\).  Indeed, (2.3) is impossible whenever the inclusion in
(2.2) is strict.

The locked Kahn source is

```text
.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
```

The relevant clauses are:

- lines 188--214: the pullback universal property and the
  set-theoretic/topological equalizer;
- lines 259--265: when one leg is an immersion, the analytic pullback
  has the topological pullback as its underlying space;
- lines 350--399: the first pseudo-polynomial-like pullback;
- lines 410--416: the finite pullback tower and its commuting
  identities; and
- lines 418--421: the tower agrees with iteration of the underlying
  relation.

Put

\[
 X_0=\mathcal V,\qquad X_1=\mathcal V',
 \qquad
 i=\iota:X_1\to X_0,\qquad f:X_1\to X_0.
\tag{2.4}
\]

The point-set model of the safe \(m\)-fold relation domain is

\[
 X_m=
 \left\{
 (z_1,\ldots,z_m)\in X_1^m:
 f(z_r)=i(z_{r+1})\quad(1\le r<m)
 \right\},
\tag{2.5}
\]

with any proof-specific removed trees and obstacles imposed
coordinatewise.  Formula (2.5) is only the interior relation model.
Identifying it with the exact KKL proof-used complementary surface is
an additional analytic obligation.

For \(1\le r\le m\), let

\[
 q_{m,r}:X_m\to X_1,\qquad
 q_{m,r}(z_1,\ldots,z_m)=z_r.
\tag{2.6}
\]

Under Kahn's recursive identification, these are the one-step
coordinates

\[
 q_{m,r}
 =
 f_1\circ\cdots\circ f_{r-1}
 \circ i_r\circ\cdots\circ i_{m-1}.
\tag{2.7}
\]

The complete immersion and proper projections are

\[
 I_m=i\circ q_{m,1},
 \qquad
 P_m=f\circ q_{m,m}.
\tag{2.8}
\]

### Lemma 2.1 (tower orientation)

In the ordered relation coordinates of (2.5),

\[
 i_{m-1}(z_1,\ldots,z_m)=(z_1,\ldots,z_{m-1}),
 \qquad
 f_{m-1}(z_1,\ldots,z_m)=(z_2,\ldots,z_m).
\tag{2.9}
\]

Thus \(i_{m-1}\) deletes the terminal coordinate and
\(f_{m-1}\) deletes the initial coordinate.

#### Proof

At the first Kahn pullback, the source writes a point as \((x,y)\)
with

\[
 i(x)=f(y),\qquad i_1(x,y)=y,\qquad f_1(x,y)=x.
\tag{2.10}
\]

Putting \((z_1,z_2)=(y,x)\) changes the defining equality to
\(f(z_1)=i(z_2)\).  It also makes \(i_1\) delete \(z_2\) and \(f_1\)
delete \(z_1\), which is (2.9) for \(m=2\).

Assume (2.9) at level \(m\).  In the next pullback, take

\[
 x=(z_2,\ldots,z_{m+1}),\qquad
 y=(z_1,\ldots,z_m).
\tag{2.11}
\]

Then

\[
 i_{m-1}(x)=(z_2,\ldots,z_m)
 =
 f_{m-1}(y),
\tag{2.12}
\]

so \((x,y)\) is a point of the next Kahn pullback.  Its new immersion
projection is \(y\), the prefix obtained by deleting \(z_{m+1}\), and
its new covering projection is \(x\), the suffix obtained by deleting
\(z_1\).  This proves (2.9) by induction. \(\square\)

## 3. A holomorphic strict-window countermodel

The following model isolates the semantic error without claiming to
be an actual KKL Hubbard-tree block.

### Proposition 3.1

There are hyperbolic Jordan domains \(X_1\subset X_0\), a holomorphic
immersion \(i:X_1\to X_0\), a proper holomorphic cover
\(f:X_1\to X_0\), and a two-step sequence of proper paths

\[
 \beta_0,\quad\gamma_1,\quad\beta_1=f\gamma_1,\quad
 \gamma_2,\quad\beta_2=f\gamma_2
\tag{3.1}
\]

such that

\[
 i(|\gamma_1|)\subset|\beta_0|,
 \qquad
 i(|\gamma_2|)\subsetneq|\beta_1|,
\tag{3.2}
\]

but no reparameterizations of the two full paths
\(\gamma_1,\gamma_2\) satisfy

\[
 f\gamma_1=i\gamma_2.
\tag{3.3}
\]

Nevertheless, a strict parameter-window truncation of \(\gamma_1\)
together with the full path \(\gamma_2\) gives a path in \(X_2\).
The truncated first coordinate is not proper.

#### Construction

Let

\[
 X_0=\mathbb D,
 \qquad
 X_1=\Omega:=\{z\in\mathbb D:\operatorname{Im}z>0\},
\tag{3.4}
\]

and let \(i:\Omega\hookrightarrow\mathbb D\) be inclusion.  The domain
\(\Omega\) is Jordan.  By the Riemann mapping theorem and
Carathéodory's theorem, there is a conformal map

\[
 \phi:\Omega\longrightarrow\mathbb D
\tag{3.5}
\]

extending homeomorphically to the closures.  Postcomposing a fixed
Riemann map with a disk automorphism, normalize it so that

\[
 \phi(-1/2)=-i,\qquad \phi(1/2)=i.
\tag{3.6}
\]

Set \(f=\phi\).  Thus \(f\) is a proper holomorphic cover of degree
one and \(i\) is a holomorphic immersion.

Parameterize the vertical diameter by

\[
 \beta_1(t)=i(2t-1),\qquad 0<t<1,
\tag{3.7}
\]

and put

\[
 \gamma_1=\phi^{-1}\circ\beta_1.
\tag{3.8}
\]

Then \(\gamma_1\) is a proper crosscut of \(\Omega\), extending from
\(-1/2\) to \(1/2\), and

\[
 f\circ\gamma_1=\beta_1.
\tag{3.9}
\]

Let \(\overline\gamma_1\) denote its closed-crosscut extension.  The
concatenation

\[
 [-1,-1/2]\ *\ \overline\gamma_1\ *\ [1/2,1]
\tag{3.10}
\]

has a parameterization \(\beta_0:(0,1)\to\mathbb D\) which is proper
from \(-1\) to \(1\) and contains \(i(|\gamma_1|)\).  This supplies the
first relation in (3.2).

Now define

\[
 \gamma_2(t)=it,\qquad 0<t<1.
\tag{3.11}
\]

It is a proper path of \(\Omega\): its two ideal endpoints are
\(0\) on the diameter boundary and \(i\) on the circular boundary.
Its immersion image is the strict upper half of (3.7):

\[
 i\circ\gamma_2(t)
 =
 \beta_1\!\left(\frac{t+1}{2}\right).
\tag{3.12}
\]

Finally, \(\beta_2=f\circ\gamma_2\) is proper in \(\mathbb D\), because
\(f\) extends homeomorphically to the Jordan boundaries.

#### Verification

Equations (3.9) and (3.12) give

\[
 i(|\gamma_2|)
 =
 \{iy:0<y<1\}
 \subsetneq
 \{iy:-1<y<1\}
 =
 f(|\gamma_1|).
\tag{3.13}
\]

Reparameterizing a path by a self-homeomorphism of \((0,1)\) does not
change its image.  Hence no reparameterizations can turn (3.13) into
the full-path equality (3.3).

Define the strict window

\[
 a_1(t)=\frac{t+1}{2}:(0,1)\longrightarrow(1/2,1).
\tag{3.14}
\]

Then

\[
 \Theta_2(t)=
 \bigl(\gamma_1(a_1(t)),\gamma_2(t)\bigr)
\tag{3.15}
\]

belongs to \(X_2\), since

\[
 f\gamma_1a_1=i\gamma_2.
\tag{3.16}
\]

However,

\[
 \lim_{t\to0}\gamma_1(a_1(t))
 =
 \gamma_1(1/2)
 =
 \phi^{-1}(0)\in\Omega.
\tag{3.17}
\]

Thus the first coordinate in (3.15) has an interior endpoint and is
not a proper path of \(X_1\), even though the full path \(\gamma_1\)
is proper.  This proves every assertion. \(\square\)

### Qualification 3.2

Proposition 3.1 is a holomorphic countermodel to the claimed
categorical necessity of full-coordinate synchronization.  It is not
asserted to satisfy KKL's native Hubbard-tree marking or its
line-2097 retention filter.  Those analytic data are irrelevant to
the logical point: the defining containment in KKL line 2083 permits
a strict window, while Kahn's equalizer requires equality only for
the portions simultaneously present in the relation chain.

The example has degree one.  This is sufficient because the
full-coordinate assertion was based only on the immersion/cover
pullback formalism; it already fails in the injective special case.
Branching cannot restore a false categorical implication.

### Proposition 3.3 (unbranched degree-two version)

The strict-window countermodel can be chosen with \(f\) an unbranched
proper holomorphic covering of degree two.

#### Proof

Fix \(0<\rho<1\) and set

\[
 X_0=A(\rho,1)=\{z:\rho<|z|<1\},
 \qquad
 X_1=A(\sqrt\rho,1)=\{z:\sqrt\rho<|z|<1\}.
\tag{3.18}
\]

Let

\[
 i:X_1\hookrightarrow X_0,
 \qquad
 f:X_1\to X_0,\quad f(z)=z^2.
\tag{3.19}
\]

The inclusion is a holomorphic immersion.  Since \(0\notin X_1\),
\(f\) has no critical point on \(X_1\); it is an unbranched proper
holomorphic covering of degree two.

Define

\[
\begin{aligned}
 \beta(t)&=\rho^{\,1-t},\\
 \gamma(t)&=\rho^{(1-t)/2},
 \qquad 0<t<1.
\end{aligned}
\tag{3.20}
\]

The path \(\beta\) is a proper radial path of \(X_0\) from its inner
ideal boundary to its outer ideal boundary.  The path \(\gamma\) is a
proper radial path of \(X_1\) between its two ideal boundaries.  Set

\[
 \beta_0=\beta_1=\beta_2=\beta,
 \qquad
 \gamma_1=\gamma_2=\gamma.
\tag{3.21}
\]

Then

\[
 f\gamma(t)=\gamma(t)^2=\rho^{\,1-t}=\beta(t),
\tag{3.22}
\]

so both covering pushforwards are the full path \(\beta\).  On the
other hand,

\[
 i\gamma(t)
 =
 \rho^{(1-t)/2}
 =
 \beta\!\left(\frac{t+1}{2}\right).
\tag{3.23}
\]

Thus \(i(|\gamma|)\) is the strict terminal radial subpath

\[
 \{\sqrt\rho<|z|<1,\ z>0\}
 \subsetneq
 \{\rho<|z|<1,\ z>0\}
 =
 |\beta|.
\tag{3.24}
\]

The same strict window

\[
 a(t)=\frac{t+1}{2}
\tag{3.25}
\]

realizes both sequential restrictions
\(\beta_{r-1}a=i\gamma_r\).  No reparameterizations of the full paths
can satisfy \(f\gamma_1=i\gamma_2\), because their images are the two
unequal sets in (3.24).

The first coordinate of the corresponding terminal relation path is
\(\gamma a\).  As \(t\to0\),

\[
 \gamma(a(t))\longrightarrow\rho^{1/4},
\tag{3.26}
\]

which is an interior point of \(X_1\).  Hence that truncated
coordinate is not proper. \(\square\)

Proposition 3.3 is still not represented as a KKL Hubbard-tree block
or as a certificate for its ideal-marking filter.  It does show the
strict-window defect with exactly the unbranched degree-two
immersion/cover map types used on the complementary surfaces.

## 4. One-step occurrence windows

All parameter intervals below are oriented copies of

\[
 J_r=(0,1).
\tag{4.1}
\]

The use of separate symbols \(J_r\) is essential: the \(r\)-th
parameter belongs to the full path at stage \(r\), not to a universal
clock shared by all stages.

### Definition 4.1

Let

\[
 \beta:J_\beta\to X_0,\qquad
 \gamma:J_\gamma\to X_1.
\tag{4.2}
\]

An **occurrence map of \(\gamma\) in \(\beta\)** is a continuous map

\[
 a:J_\gamma\to J_\beta
\tag{4.3}
\]

such that

\[
 \beta\circ a=i\circ\gamma.
\tag{4.4}
\]

It is an **occurrence window** if \(a\) is a topological embedding
onto an open interval in \(J_\beta\).  The sign

\[
 \epsilon(a)\in\{+1,-1\}
\tag{4.5}
\]

records whether \(a\) preserves or reverses orientation.

Equivalently, define the parameter equalizer

\[
 E(\beta,\gamma)
 =
 \{(s,t)\in J_\beta\times J_\gamma:
       \beta(s)=i(\gamma(t))\}.
\tag{4.6}
\]

An occurrence map is exactly a continuous section

\[
 t\longmapsto(a(t),t)
\tag{4.7}
\]

of the second projection \(E(\beta,\gamma)\to J_\gamma\).
This formulation remains meaningful when a nonsimple target path has
several parameter occurrences with the same untagged image.

### Lemma 4.2 (window extraction for simple paths)

Assume:

1. \(\beta:J_\beta\to X_0\) is a topological embedding;
2. \(\gamma:J_\gamma\to X_1\) is a topological embedding;
3. \(i:X_1\to X_0\) is a local homeomorphism; and
4. \(i(|\gamma|)\subset|\beta|\).

Then there is a unique occurrence map \(a\), and it is an occurrence
window.

#### Proof

Because \(\beta\) is a homeomorphism from \(J_\beta\) onto its image,
the only possible occurrence map is

\[
 a=\beta^{-1}\circ i\circ\gamma.
\tag{4.8}
\]

The containment hypothesis makes (4.8) defined everywhere, and each
factor is continuous, so \(a\) is continuous.

Fix \(t\in J_\gamma\).  On a sufficiently small neighborhood of
\(\gamma(t)\), the map \(i\) is a homeomorphism.  The image of a small
two-sided subarc of \(\gamma\) is consequently a two-sided subarc of
the embedded path \(\beta\).  Hence (4.8) is a local homeomorphism
between intervals.

A local homeomorphism between intervals is locally either increasing
or decreasing.  Its local orientation sign is locally constant and
therefore constant on the connected domain \(J_\gamma\).  It follows
that \(a\) is strictly monotone and hence injective.  A local
homeomorphism is open, so \(a(J_\gamma)\) is an open connected subset
of \(J_\beta\), hence an open interval.  Thus \(a\) is an occurrence
window.  Uniqueness was already forced by (4.8). \(\square\)

### Qualification 4.3

Bare set containment does not always produce a parameter section when
the target path is nonsimple.  In that case an occurrence component
or section of (4.6) is additional data.  In the proof-used Wave
setting, one works with simple representatives of lamination leaves,
so Lemma 4.2 is the applicable finite statement once actual
containment of a specified retained component has been proved.

Lemma 4.2 proves nothing about the behavior of \(a(t)\) as
\(t\to0,1\).  A strict window can converge to interior parameters of
\(\beta\), exactly as in (3.14).  Thus it does not promote the
truncated path \(\beta\circ a\) to a proper path of \(X_0\).

### Corollary 4.4 (proof-used Wave specialization)

Suppose \(\beta_{r-1}\) and \(\beta_r\) are leaves of the proof-used
Waves, \(\gamma_r\) is an actual covering lift with

\[
 f\gamma_r=\beta_r,
\tag{4.9}
\]

and \(i(|\gamma_r|)\subset|\beta_{r-1}|\).  After choosing simple
oriented representatives, there is a unique occurrence window
\(a_{r-1}\) satisfying (5.3).

#### Proof

Lamination leaves have simple representatives; compare the
simple-path convention for arcs and the definitions of laminations
and Waves at KKL lines 1870--1875.  Choose a simple parameterization
of \(\beta_r\).  Since \(f\) is a covering on the complementary
surface, a chosen lift of that parameterized interval is unique after
one fiber value is fixed.  It is embedded: if
\(\gamma_r(s)=\gamma_r(t)\), then (4.9) gives
\(\beta_r(s)=\beta_r(t)\), and simplicity of \(\beta_r\) gives
\(s=t\).  The preceding Wave leaf \(\beta_{r-1}\) is embedded as well.
Lemma 4.2 now applies. \(\square\)

Corollary 4.4 is conditional on an **actual** covering lift and the
actual containment in the specified preceding leaf.  A coarse
itinerary label, adjacency alternative, or same-pulled-interval
alternative does not supply either hypothesis.  If a retained object
is used merely as a nonsimple path outside a Wave, the certificate
must store a section of the parameter equalizer (4.6); uniqueness
must not be asserted.

## 5. The segmented-occurrence invariant

Fix a finite horizon \(h\ge1\).

### Definition 5.1

A **segmented sequential occurrence** is the record

\[
 \mathfrak S_h=
 \left(
   \beta_0;
   \{\gamma_r,\beta_r\}_{r=1}^{h};
   \{a_{r-1}\}_{r=1}^{h}
 \right)
\tag{5.1}
\]

with the following typed clauses.

1. \(\beta_0:J_0\to X_0\) is the full initial proper marked path.
2. For \(1\le r\le h\),
   \(\gamma_r:J_r\to X_1\) is the full proper fine-marked path selected
   at stage \(r\), including its actual restriction-component,
   endpoint-access, attachment, sheet, and filter-survival witness.
3. For \(1\le r\le h\),
   \[
      \beta_r=f\circ\gamma_r:J_r\to X_0
   \tag{5.2}
   \]
   is the full stage output.
4. For \(1\le r\le h\),
   \(a_{r-1}:J_r\to J_{r-1}\) is an occurrence map satisfying
   \[
      \beta_{r-1}\circ a_{r-1}
      =
      i\circ\gamma_r.
   \tag{5.3}
   \]
5. In the **nested-window** case, every \(a_{r-1}\) is an occurrence
   window and its orientation sign is recorded.

Clause 2 contains analytic witnesses which the finite theorem below
does not manufacture.  The finite semantic core is

\[
 \boxed{
   \text{all full stage paths }
   \{\beta_0,\gamma_1,\ldots,\gamma_h\}
   \;+\;
   \text{all occurrence maps }
   \{a_0,\ldots,a_{h-1}\}.
 }
\tag{5.4}
\]

For \(0\le r<m\le h\), define the cumulative occurrence map

\[
 a_{r\mid m}
 =
 a_r\circ a_{r+1}\circ\cdots\circ a_{m-1}
 :
 J_m\to J_r,
\tag{5.5}
\]

and put \(a_{m\mid m}=\operatorname{id}_{J_m}\).  For
\(1\le r\le m\), define the stage-\(r\) segment surviving through
prefix \(m\) by

\[
 \widehat\gamma_r^{[m]}
 =
 \gamma_r\circ a_{r\mid m}.
\tag{5.6}
\]

When the \(a_r\) are windows, the image

\[
 W_{r\mid m}:=a_{r\mid m}(J_m)\subset J_r
\tag{5.7}
\]

is the nested parameter window of the full path \(\gamma_r\) that
survives to stage \(m\).  It can be a strict interval.

### Parameter-gauge invariance

Replace \(J_r\) by another oriented interval \(J'_r\) and choose an
orientation-preserving homeomorphism

\[
 u_r:J'_r\to J_r.
\tag{5.8}
\]

The reparameterized data are

\[
\begin{aligned}
 \beta'_r&=\beta_r\circ u_r,\\
 \gamma'_r&=\gamma_r\circ u_r\quad(r\ge1),\\
 a'_{r-1}&=u_{r-1}^{-1}\circ a_{r-1}\circ u_r.
\end{aligned}
\tag{5.9}
\]

Substituting (5.9) into (5.3) proves the same occurrence identity.
Therefore the invariant is the equivalence class of (5.1) under
(5.9), not the accidental numerical parameter values.  If
orientation-reversing gauges are permitted, the route orientations
must be transformed at the same time; retaining (4.5) avoids that
ambiguity.

## 6. Finite segmented reconstruction

### Theorem 6.1 (prefix-flag reconstruction)

Let \(\mathfrak S_h\) be a segmented sequential occurrence.  For every
\(1\le m\le h\), there is a unique continuous path

\[
 \Theta_m:J_m\longrightarrow X_m
\tag{6.1}
\]

such that

\[
 q_{m,r}\circ\Theta_m
 =
 \widehat\gamma_r^{[m]}
 =
 \gamma_r\circ a_{r\mid m}
 \qquad(1\le r\le m).
\tag{6.2}
\]

The paths form a segmented prefix flag:

\[
 i_{m-1}\circ\Theta_m
 =
 \Theta_{m-1}\circ a_{m-1}
 \qquad(2\le m\le h),
\tag{6.3}
\]

where \(i_{m-1}:X_m\to X_{m-1}\) is the Kahn immersion projection.
Their complete base and terminal projections are

\[
 I_m\circ\Theta_m
 =
 \beta_0\circ a_{0\mid m},
\qquad
 P_m\circ\Theta_m
 =
 \beta_m.
\tag{6.4}
\]

In particular, the terminal projection is the full stage-\(m\) output,
but an earlier coordinate in (6.2) can be a nonproper strict segment.

#### Proof

Fix \(m\).  Define the candidate pointwise by

\[
 \Theta_m(t)
 =
 \left(
   \gamma_1(a_{1\mid m}(t)),
   \gamma_2(a_{2\mid m}(t)),
   \ldots,
   \gamma_{m-1}(a_{m-1}(t)),
   \gamma_m(t)
 \right).
\tag{6.5}
\]

For \(1\le r<m\), the definition (5.5) gives

\[
 a_{r\mid m}
 =
 a_r\circ a_{r+1\mid m}.
\tag{6.6}
\]

Using \(\beta_r=f\gamma_r\) and the stage-\((r+1)\) occurrence
identity (5.3), we calculate

\[
\begin{aligned}
 f\circ\gamma_r\circ a_{r\mid m}
 &=
 \beta_r\circ a_r\circ a_{r+1\mid m}\\
 &=
 i\circ\gamma_{r+1}\circ a_{r+1\mid m}.
\end{aligned}
\tag{6.7}
\]

Equation (6.7) is exactly the \(r\)-th defining relation in (2.5).
Therefore \(\Theta_m(t)\in X_m\) for every \(t\in J_m\).  Each
coordinate in (6.5) is continuous, and \(X_m\) has the subspace
topology from \(X_1^m\), so \(\Theta_m\) is continuous.  Formula
(6.2) follows from (6.5).

If another path has all the coordinates in (6.2), its ordered tuple
in (2.5) agrees pointwise with (6.5).  It is therefore equal to
\(\Theta_m\).  This proves uniqueness.

In the ordered-tuple model, \(i_{m-1}\) deletes the last coordinate.
For \(1\le r<m\), the \(r\)-th coordinate of its left-hand side in
(6.3) is

\[
 \gamma_r\circ a_{r\mid m}
 =
 \gamma_r\circ a_{r\mid m-1}\circ a_{m-1},
\tag{6.8}
\]

which is the \(r\)-th coordinate of the right-hand side.  Hence (6.3)
holds.

Finally, (2.8), (5.3), and (5.5) give

\[
\begin{aligned}
 I_m\Theta_m
 &=i\gamma_1a_{1\mid m}\\
 &=\beta_0a_0a_{1\mid m}
 =\beta_0a_{0\mid m},
\end{aligned}
\tag{6.9}
\]

while the last coordinate in (6.5) is the full path \(\gamma_m\), so

\[
 P_m\Theta_m=f\gamma_m=\beta_m.
\tag{6.10}
\]

This proves (6.4). \(\square\)

### Theorem 6.2 (converse reconstruction)

Suppose full paths \(\beta_0,\gamma_1,\ldots,\gamma_h\), continuous
maps \(a_r:J_{r+1}\to J_r\) for \(0\le r<h\), and paths
\(\Theta_m:J_m\to X_m\) are given such that:

1. \(q_{m,m}\Theta_m=\gamma_m\) for every \(m\);
2. \(i_{m-1}\Theta_m=\Theta_{m-1}a_{m-1}\) for \(2\le m\le h\);
3. \(\beta_m=f\gamma_m\) for \(1\le m\le h\); and
4. \(\beta_0a_0=i\gamma_1\).

Then

\[
 \beta_{m-1}a_{m-1}=i\gamma_m
 \qquad(2\le m\le h),
\tag{6.11}
\]

so the data form a segmented sequential occurrence.  Moreover every
\(\Theta_m\) is the unique path constructed in Theorem 6.1.

#### Proof

Because \(\Theta_m\) takes values in the relation chain \(X_m\), its
last two coordinates satisfy

\[
 f(q_{m,m-1}\Theta_m)=i(q_{m,m}\Theta_m).
\tag{6.12}
\]

The prefix identity and the last-coordinate condition at level
\(m-1\) give

\[
\begin{aligned}
 q_{m,m-1}\Theta_m
 &=
 q_{m-1,m-1}i_{m-1}\Theta_m\\
 &=
 q_{m-1,m-1}\Theta_{m-1}a_{m-1}\\
 &=
 \gamma_{m-1}a_{m-1}.
\end{aligned}
\tag{6.13}
\]

Substitute (6.13) and \(q_{m,m}\Theta_m=\gamma_m\) into (6.12):

\[
 f\gamma_{m-1}a_{m-1}=i\gamma_m.
\tag{6.14}
\]

Since \(\beta_{m-1}=f\gamma_{m-1}\), equation (6.14) is (6.11).
Together with clause 4, all occurrence identities (5.3) hold.

Repeatedly applying the prefix identities also gives every coordinate
formula (6.2).  The uniqueness clause of Theorem 6.1 then identifies
each supplied \(\Theta_m\) with the constructed one. \(\square\)

### Corollary 6.3 (correct finite equivalence)

The following two finite records are equivalent:

1. the full sequential path list together with all occurrence maps,
   as in (5.1); and
2. the complete prefix flag
   \(\{\Theta_m\}_{m=1}^h\), all connecting maps
   \(\{a_m\}_{m=0}^{h-1}\), the initial path \(\beta_0\), and the
   last-coordinate identifications
   \(q_{m,m}\Theta_m=\gamma_m\), with the base compatibility
   \(\beta_0a_0=i\gamma_1\).

One terminal path \(\Theta_h\) alone is not equivalent to either
record.

#### Proof

Theorems 6.1 and 6.2 prove the equivalence of the two complete records.
For the final sentence, \(\Theta_h\) contains at stage \(r<h\) only

\[
 \gamma_r|_{W_{r\mid h}},
\tag{6.15}
\]

not the full path \(\gamma_r\).  Distinct full extensions outside
\(W_{r\mid h}\) can give the same terminal tuple.  Those extensions
can have different endpoints, relative homotopy words, attachment
provenance, or filter behavior.  Hence \(\Theta_h\) cannot recover the
full sequential record. \(\square\)

## 7. Why the full stage paths cannot be discarded

The KKL predicates are evaluated on the full stage path
\(\gamma_r\):

1. proper extension to the ideal closure;
2. endpoint membership in the fine marking \(f^*\mathcal I\);
3. non-subordination to a fine multi-interval of length at most two;
4. non-subordination to a single coarse interval of
   \(\iota^*\mathcal I\); and
5. actual component, access, attachment, sheet, and parent provenance.

The truncated coordinate

\[
 \widehat\gamma_r^{[h]}=\gamma_ra_{r\mid h}
\tag{7.1}
\]

need satisfy none of these predicates.  Proposition 3.1 gives an
explicit instance in which \(\gamma_1\) is proper but
\(\widehat\gamma_1^{[2]}\) has an interior endpoint.  Therefore a
certificate which requires every terminal-tower coordinate to be
proper excludes a legitimate sequential occurrence, while a
certificate which checks retention only on the terminal segments
checks the wrong objects.

This is the reason the prefix flag is necessary.  At prefix \(r\),

\[
 q_{r,r}\Theta_r=\gamma_r
\tag{7.2}
\]

is the full stage path, so its stage-\(r\) KKL predicates remain
auditable.  At later prefixes it is correctly truncated by the
subsequent occurrence windows.

## 8. Exact correction to the prior binder design

The prior design imposed

\[
 f\gamma_r=i\gamma_{r+1}
\quad\text{under one common parameter}
\tag{8.1}
\]

for the full proper stage paths.  The source supplies only

\[
 f\gamma_r\,a_r=i\gamma_{r+1}
\tag{8.2}
\]

for an occurrence window \(a_r\), when the relevant actual
restriction component and simple representatives have been fixed.

Accordingly:

1. the prior coordinate-synchronization lemma remains correct;
2. the prior synchronized-chain reconstruction theorem remains
   correct for data satisfying (8.1);
3. its claim to characterize arbitrary sequential \(F_*^h\)
   occurrences is false;
4. its semantic core clauses requiring one common full-horizon path
   with every \(q_{h,r}\Theta\) equal to the full proper
   \(\gamma_r\) must not be used as a necessary KKL binder condition;
5. Proposition 6.4 of that note remains a valid sufficient
   implication from its stronger hypotheses, but has no converse for
   a general retained chain;
6. Theorem 6.1 above is the correct finite replacement.

The correction can be summarized by the commutative, non-Cartesian
prefix relation

\[
\begin{CD}
 J_m @>{\Theta_m}>> X_m\\
 @V{a_{m-1}}VV @VV{i_{m-1}}V\\
 J_{m-1} @>>{\Theta_{m-1}}> X_{m-1},
\end{CD}
\tag{8.3}
\]

where the left map can have a strict image.  Replacing
\(a_{m-1}\) by the identity is an additional surjectivity assertion,
not a consequence of KKL's definition.

## 9. What remains for the actual two-occurrence binder

For each of the two line-1603 route signs
\(\epsilon\in\{-,+\}\), an actual KKL certificate must now construct a
separate segmented record

\[
 \mathfrak S_h^\epsilon
 =
 \left(
   \beta_0^\epsilon;
   \{\gamma_r^\epsilon,\beta_r^\epsilon\}_{r=1}^{h};
   \{a_{r-1}^\epsilon\}_{r=1}^{h}
 \right).
\tag{9.1}
\]

For every stage and both signs, it must prove:

1. the proposed portion is an actual proper source path, not merely a
   topological portion named in the base picture;
2. the actual restriction component is contained in the preceding
   full path;
3. the occurrence window extracted by Lemma 4.2 has the claimed
   orientation and endpoint accesses;
4. the full \(\gamma_r^\epsilon\), not merely its terminal surviving
   segment, belongs to \((X_1,f^*\mathcal I)\);
5. the full path survives the line-2097 coarse-interval filter;
6. every attachment, parent, sheet, and protected access is recorded;
7. the construction continues through the complete horizon without a
   missing or independently chosen stage;
8. the terminal full paths \(\beta_h^-\) and \(\beta_h^+\) belong to
   the named Wave family; and
9. the two terminal occurrences remain distinct after the untagged
   \(f\)-pushforward.

Neither line 1600 nor line 1603 supplies this list.  Line 1600 asserts
one restriction path at a fixed deep level.  It does not provide two
stagewise retained flags, the windows connecting their full stage
paths, or their filter and terminal noncollision witnesses.

## 10. Adversarial checks

### 10.1 Strict window

Proposition 3.1 has

\[
 a_1((0,1))=(1/2,1)\subsetneq(0,1).
\]

The sequential occurrence exists, while full-coordinate
synchronization does not.  This is the decisive counterexample.

### 10.2 Nonproper earlier coordinate

The same example gives

\[
 \lim_{t\to0}\gamma_1a_1(t)\in X_1.
\]

Thus full-stage properness cannot be transferred to a later truncated
coordinate.

### 10.3 Independent reparameterization

The transformation law (5.9) preserves every occurrence identity.
An equality test that compares raw parameter tokens without applying
this conjugacy is not invariant.

### 10.4 Nonsimple target

Set containment alone can correspond to several branches of the
parameter equalizer (4.6).  A branch or section must be recorded.
The simple-path hypothesis in Lemma 4.2 is therefore substantive, not
cosmetic.

### 10.5 Terminal-path information loss

Changing an early full path outside \(W_{r\mid h}\) leaves
\(\Theta_h\) unchanged.  It can nevertheless change the early path's
proper endpoints or relative homotopy word.  Hence a terminal tower
path cannot replace the prefix flag.

### 10.6 Empty or collapsed window

An occurrence window is an embedding from all of \(J_r\) onto a
nonempty open interval.  Constant maps and maps defined only on a
proper subset of the later full path are rejected.

### 10.7 Orientation reversal

An orientation-reversing window is allowed only with its sign and
endpoint-access swap recorded.  Silently treating it as preserving
the route order can interchange the two proposed line-1603 portions.

### 10.8 Full-path equality as a special case

If every \(a_r\) is a surjective orientation-preserving
self-homeomorphism, gauges (5.9) can normalize all of them to the
identity.  The prior common-parameter theorem is recovered exactly in
this special case.  The new theorem therefore extends rather than
contradicts the valid equalizer calculation.

### 10.9 Analytic overreach

No finite relation calculation proves:

- ideal-end landing of a tower path;
- properness of a truncated coordinate;
- survival of a KKL marking filter;
- equality with a full inverse-image component;
- distinctness of two terminal covering images; or
- uniform width or modulus control.

Each remains an independent analytic obligation.

## 11. Final status

The finite semantic correction is complete:

\[
\boxed{
\begin{array}{c}
\text{sequential KKL occurrence}\\[2pt]
\text{(full stage paths plus occurrence windows)}
\end{array}
}
\quad\Longleftrightarrow\quad
\boxed{
\begin{array}{c}
\text{compatible flag of prefix relation paths}\\[2pt]
\text{with full last coordinate at every prefix.}
\end{array}
}
\tag{11.1}
\]

The stronger formula

\[
 f\gamma_r=i\gamma_{r+1}
\tag{11.2}
\]

for all full stage paths is only the special case in which every
window fills the whole preceding parameter interval.

The actual KKL stationary two-occurrence binder remains open.  Its
next valid analytic target is not a single full-fiber-product path,
but two complete segmented prefix flags satisfying every properness,
marking, attachment, access, Wave-membership, and terminal
noncollision clause in Section 9.
