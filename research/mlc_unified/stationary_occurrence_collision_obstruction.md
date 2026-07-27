# Stationary Wave occurrence collision and the missing extraction lemma

## 1. Result and exact status

This note audits the proof step used in the stationary-Wave argument of
Kahn--Koropecki--Lyubich (KKL).  It establishes the following facts.

1. KKL's definition of immersion restriction is set-valued, and its
   definition of breaking is applied after the proper covering has
   pushed those restriction components forward.
2. Two distinct proper restriction components can have exactly the same
   image under the proper degree-two map.  Thus untagged pushforward
   forgets occurrence multiplicity.
3. Therefore the implication
   \[
      \text{two distinct retained restriction components}
      \quad\Longrightarrow\quad
      \text{the source leaf breaks}
   \tag{1.1}
   \]
   is not a formal consequence of KKL's Appendix definitions.
4. An explicit analytic pseudo-quadratic-like map realizes this
   proper-path collision.  Every disk, radius, common-inverse, path,
   properness, and image-equality assertion is checked below.
5. The common image in the model joins two different ideal-boundary
   components.  It is therefore **not a KKL Wave**, because a Wave is
   subordinate to one connected multi-interval in one ideal-boundary
   component.  The model does not realize the exact antecedent at KKL
   line 1603, where both images are asserted to be Waves.
6. The model is **not** asserted to satisfy KKL's full primitive,
   parabolically bounded Hubbard-tree hypotheses.  It is therefore not
   a counterexample to the intended stationary-Wave theorem.  It is a
   warning that distinct restriction occurrences alone do not imply a
   break under the abstract untagged path-pushforward formalism.
7. The exact unresolved source theorem is a KKL-specific **retained
   two-sided Wave noncollision lemma**.  It must use the terminal Wave
   endpoint/access data absent from the abstract model.  Merely attaching
   occurrence tags is not enough unless breaking is redefined and all
   Wave estimates are reproved for that tagged definition.

The note also isolates the formal endpoint-defined candidate once the
actual final component-to-component restriction exists leaf by leaf.
To promote it to a measurable lamination one must additionally prove
that the endpoint-selected union is Borel in Kahn's sense; the source
precedent alone does not discharge that Borel obligation.

The obligations

```text
KKL_STATIONARY_FINAL_PASS_THROUGH_PATH_EXTRACTION
KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR
KKL_STATIONARY_TWO_SIDED_WAVE_NONCOLLISION
```

remain open.  The off-by-one pass-through reduction is recorded only
conditionally on the noncollision obligation.  VAAPC-I, UPTCR, and MLC
remain open.

## 2. Locked sources and the exact logical interface

### 2.1 KKL source

The locked KKL source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The proof-used clauses are as follows.

- Lines 1356--1357 define \(n\)-unbreakability leaf by leaf.
- Lines 1547--1548 put \(N=b+3\), define \(A_0\), and define the nested
  subwaves \(A_n\) only for \(0<n<N\).
- Lines 1597--1602 define the selected continua \(K_0^n\), the pulled
  limbs \(L_0^n\), the relevant restricted paths, and the separator
  relation.
- Line 1603 argues that if a leaf did not pass through \(K_0^n\), two
  portions would push forward to Waves, "so" the leaf would break.
- Line 1605 invokes the undefined object \(A_N\).  The separate
  off-by-one repair replaces it by the actually defined
  \(A_{N-1}=A_{b+2}\); that repair does not validate the inference at
  line 1603.
- Lines 2081--2084 define the restriction \(\iota^*\gamma\) of a proper
  path to be the **set** of proper paths contained in
  \(\iota^{-1}(\gamma)\).
- Lines 2092--2097 define pulled ideal markings and expressly discard
  restriction components that are not paths in the source marking or
  are subordinate to a single pulled interval.
- Lines 2099--2108 give the itinerary proposition.  A consecutive
  itinerary step may be realized by an actual restriction path, by
  adjacency alone, or by two intervals lying in one pulled target
  interval.
- Lines 2128--2142 define
  \[
     F_* = f_*\iota^*
  \tag{2.1}
  \]
  on path families.
- Lines 2161--2162 say that a path breaks precisely when \(F_*\gamma\)
  is not a single path.
- Lines 2086--2089 give restriction domination.
- Lines 1750--1764 provide a useful source precedent: KKL form maximal
  endpoint-defined sublaminations of a complete restriction and use
  domination for the source leaves that contribute to them.

There is no occurrence multiplicity in (2.1).  In ordinary set
notation,
\[
   \{\delta,\delta\}=\{\delta\}.
\tag{2.2}
\]
If a multiset was intended instead, the source does not define
multiset laminations, multiset extremal width, or breaking for
multisets.

### 2.2 Kahn source

The locked source for the abstract pseudo-quadratic-like construction
is

```text
.tmp_kl06_source/psiql2.tex
SHA-256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
```

The relevant source clauses are:

- lines 20--41 for the pseudo-polynomial-like axioms;
- lines 60--77 and 155--178 for an embedded neighborhood of the filled
  set;
- lines 350--399 for pullback iteration and the filled-set
  homeomorphism.

The example below satisfies the abstract disk, proper degree-two,
immersion, full-continuum, and common-inverse clauses.  It also has the
native embedded collar near its filled set.  Its collision occurs away
from that collar.

## 3. The analytic model

Put
\[
   R=75,\qquad P=100,\qquad
   \beta=\frac{2\pi}{P}=\frac{\pi}{50},
   \qquad
   \Delta=e^{2\beta}-1.
\tag{3.1}
\]
Let
\[
   \mathbf U'=\mathbb D_{75},
   \qquad
   \mathbf U=\mathbb D_{5625},
\tag{3.2}
\]
and define
\[
   f(z)=z^2,
   \qquad
   K'=[-1,1],
   \qquad
   K=[0,1],
\tag{3.3}
\]
\[
   i(z)=\frac{e^{\beta(z+1)}-1}{\Delta}.
\tag{3.4}
\]
Here \(\mathbb D_r=\{z\in\mathbb C:|z|<r\}\).

We verify every pseudo-quadratic-like clause needed below.

## 4. Verification of the pseudo-quadratic-like clauses

### 4.1 The disks and full continua

Both \(\mathbf U'\) and \(\mathbf U\) are conformal disks.
The sets \(K'\) and \(K\) are compact and connected.  A line segment
does not separate the plane, so both are full continua.  Moreover,
\[
   K'\Subset\mathbf U',
   \qquad
   K\Subset\mathbf U.
\tag{4.1}
\]

### 4.2 The proper degree-two map

The map
\[
   f:\mathbb D_{75}\longrightarrow\mathbb D_{5625},
   \qquad f(z)=z^2,
\tag{4.2}
\]
is onto and has degree two, counting multiplicity.  Its only critical
point is \(0\), with local degree two.

It is proper.  Indeed, if \(C\Subset\mathbb D_{5625}\), choose
\(r<5625\) with \(C\subset\overline{\mathbb D}_r\).  Then
\[
   f^{-1}(C)\subset\overline{\mathbb D}_{\sqrt r}
   \Subset\mathbb D_{75},
\tag{4.3}
\]
and \(f^{-1}(C)\) is closed, hence compact.

Finally,
\[
   z^2\in[0,1]
   \quad\Longleftrightarrow\quad
   z\in[-1,1].
\tag{4.4}
\]
For the forward implication, write \(z=\rho e^{i\theta}\).
The condition \(z^2\geq0\) gives
\(2\theta=0\pmod{2\pi}\), so \(z\) is real; then
\(|z|^2\leq1\).  Thus
\[
   f^{-1}(K)=K'.
\tag{4.5}
\]

### 4.3 The immersion and target containment

Differentiating (3.4) gives
\[
   i'(z)=\frac{\beta e^{\beta(z+1)}}{\Delta}.
\tag{4.6}
\]
Since \(\beta>0\), \(\Delta>0\), and the exponential never vanishes,
\[
   i'(z)\neq0
   \qquad(z\in\mathbf U').
\tag{4.7}
\]
Hence \(i\) is a holomorphic immersion.

We next check \(i(\mathbf U')\subset\mathbf U\) using exact elementary
bounds.  If \(|z|<75\), then
\[
   \operatorname{Re}(z+1)<76.
\tag{4.8}
\]
The classical inequalities
\[
   \pi<\frac{22}{7},
   \qquad
   e<3
\tag{4.9}
\]
give
\[
   76\beta
   =
   \frac{38\pi}{25}
   <
   \frac{836}{175}
   <5.
\tag{4.10}
\]
Also \(e^x>1+x\) for \(x>0\), so
\[
   \Delta=e^{2\beta}-1>2\beta=\frac{\pi}{25}>\frac3{25}.
\tag{4.11}
\]
Therefore
\[
\begin{aligned}
   |i(z)|
   &\leq
   \frac{e^{\beta\operatorname{Re}(z+1)}+1}{\Delta}\\
   &<
   \frac{e^5+1}{3/25}\\
   &<
   \frac{(3^5+1)25}{3}
   =
   \frac{6100}{3}
   <5625.
\end{aligned}
\tag{4.12}
\]
This proves
\[
   i(\mathbf U')\subset\mathbf U.
\tag{4.13}
\]

### 4.4 Exact common inverse and the filled-set homeomorphism

Fix \(t\in[0,1]\).  By (3.4),
\[
   i(z)=t
   \quad\Longleftrightarrow\quad
   e^{\beta(z+1)}=1+\Delta t.
\tag{4.14}
\]
The right side is positive real and lies in
\([1,e^{2\beta}]\).  All logarithms give
\[
   \beta(z+1)
   =
   \log(1+\Delta t)+2\pi i k,
   \qquad k\in\mathbb Z,
\tag{4.15}
\]
and hence
\[
   z
   =
   -1+\frac{\log(1+\Delta t)}{\beta}+100ik.
\tag{4.16}
\]
For \(t\in[0,1]\),
\[
   0\leq\log(1+\Delta t)\leq2\beta,
\tag{4.17}
\]
so the real part in (4.16) lies in \([-1,1]\).  If \(k\neq0\), then
\[
   |\operatorname{Im}z|\geq100>75,
\tag{4.18}
\]
so \(z\notin\mathbf U'\).  Thus only \(k=0\) occurs in the source disk,
and
\[
   i^{-1}(K)=[-1,1]=K'.
\tag{4.19}
\]
Combining (4.5) and (4.19),
\[
   i^{-1}(K)=f^{-1}(K)=K'.
\tag{4.20}
\]

On \(K'\), formula (4.6) is positive real.  Moreover,
\[
   i(-1)=0,
   \qquad
   i(1)=1.
\tag{4.21}
\]
Consequently \(i|_{K'}:K'\to K\) is an increasing homeomorphism.
Equations (4.2), (4.7), (4.13), and (4.20) prove that
\[
   (i,f):(\mathbf U',K')\longrightarrow(\mathbf U,K)
\tag{4.22}
\]
is an abstract degree-two pseudo-quadratic-like map.

## 5. A simple proper target path

Define
\[
   \alpha:(0,1)\longrightarrow\mathbf U\setminus K
\tag{5.1}
\]
by
\[
   \alpha(t)
   =
   \frac{e^{2\beta t+2\pi i t}-1}{\Delta}.
\tag{5.2}
\]

### 5.1 Endpoint limits

Direct substitution gives
\[
   \lim_{t\downarrow0}\alpha(t)=0,
   \qquad
   \lim_{t\uparrow1}\alpha(t)
   =
   \frac{e^{2\beta}-1}{\Delta}
   =1.
\tag{5.3}
\]
Both limits lie on the inner ideal boundary determined by \(K\).

### 5.2 Target-disk containment

For \(0<t<1\),
\[
   |\alpha(t)|
   \leq
   \frac{e^{2\beta}+1}{\Delta}.
\tag{5.4}
\]
Since \(2\beta=\pi/25<1\), (4.9) and (4.11) give
\[
   |\alpha(t)|
   <
   \frac{e+1}{3/25}
   <
   \frac{100}{3}
   <5625.
\tag{5.5}
\]
Thus \(\alpha((0,1))\subset\mathbf U\).

### 5.3 Avoidance of \(K\)

If \(\alpha(t)\) is real, then
\[
   \sin(2\pi t)=0.
\tag{5.6}
\]
For \(0<t<1\), this forces \(t=1/2\).  At that point,
\[
   \alpha(1/2)
   =
   \frac{-e^\beta-1}{\Delta}
   <0.
\tag{5.7}
\]
Hence \(\alpha(t)\notin[0,1]\) for all \(0<t<1\).

### 5.4 Injectivity

If \(\alpha(s)=\alpha(t)\), then
\[
   e^{2\beta s+2\pi i s}
   =
   e^{2\beta t+2\pi i t}.
\tag{5.8}
\]
Taking absolute values yields \(e^{2\beta s}=e^{2\beta t}\).
Since \(\beta>0\), \(s=t\).  Thus \(\alpha\) is simple.

### 5.5 Properness

The map \(\alpha\) extends continuously to \([0,1]\), and its only
limit points outside \(\mathbf U\setminus K\) are the two points in
(5.3).  If \(C\Subset\mathbf U\setminus K\), then \(C\) has positive
distance from \(0\) and \(1\).  Consequently
\(\alpha^{-1}(C)\) is a closed subset of
\([\varepsilon,1-\varepsilon]\) for some \(\varepsilon>0\), and hence is
compact.  Thus \(\alpha\) is a proper simple path.

Topologically, a simple proper arc with both ends on one boundary
component of an annulus is boundary-parallel on one side.  Thus one can
choose a *target-side* ideal subdivision for which \(\alpha\) is
subordinate to a connected multi-interval of combinatorial length at
least three.  This makes \(\{\alpha\}\) a Wave for that isolated target
marking.  It does **not** prove that this marking participates in a
complete KKL marked action: the pullback/refinement condition at the
nonproper outer end is audited separately in Section 8.  The collision
below is leafwise, so no positive-width assertion is required.

## 6. Complete calculation of the immersion restriction

Solving \(i(z)=\alpha(t)\) gives
\[
   e^{\beta(z+1)}
   =
   e^{2\beta t+2\pi i t}.
\tag{6.1}
\]
Therefore
\[
   \beta(z+1)
   =
   2\beta t+2\pi i(t+k),
   \qquad k\in\mathbb Z,
\tag{6.2}
\]
and, because \(2\pi/\beta=100\),
\[
   z_k(t)
   =
   -1+2t+100i(t+k).
\tag{6.3}
\]

### 6.1 Only the sheets \(k=0\) and \(k=-1\) can enter the source disk

If \(k\geq1\), then
\[
   |\operatorname{Im}z_k(t)|
   =
   100(t+k)>100>75.
\tag{6.4}
\]
If \(k\leq-2\), then \(|t+k|>1\), and the same estimate holds.
Thus only \(k=0\) and \(k=-1\) can occur in
\(\mathbb D_{75}\).

### 6.2 The exact exit time

For \(k=0\),
\[
\begin{aligned}
   |z_0(t)|^2
   &=
   (-1+2t)^2+(100t)^2\\
   &=
   1-4t+10004t^2.
\end{aligned}
\tag{6.5}
\]
The equation \(|z_0(t)|=75\) is
\[
   10004t^2-4t-5624=0.
\tag{6.6}
\]
Its two roots have negative product, so it has exactly one positive
root:
\[
   t_*
   =
   \frac{4+\sqrt{16+4\cdot10004\cdot5624}}{20008}.
\tag{6.7}
\]
At \(t=1/2\), (6.5) equals \(2500<5625\), while at \(t=1\) it equals
\(10001>5625\).  Hence
\[
   \frac12<t_*<1.
\tag{6.8}
\]
It follows from the sign of the quadratic in (6.6) that
\[
   z_0(t)\in\mathbb D_{75}
   \quad\Longleftrightarrow\quad
   0<t<t_*.
\tag{6.9}
\]

For \(k=-1\),
\[
   z_{-1}(t)
   =
   -1+2t+100i(t-1)
   =
   -z_0(1-t).
\tag{6.10}
\]
Therefore
\[
   z_{-1}(t)\in\mathbb D_{75}
   \quad\Longleftrightarrow\quad
   1-t_*<t<1.
\tag{6.11}
\]

### 6.3 The two and only two proper restriction components

Define
\[
   \gamma_+
   =
   z_0\bigl((0,t_*)\bigr),
\tag{6.12}
\]
\[
   \gamma_-
   =
   z_{-1}\bigl((1-t_*,1)\bigr).
\tag{6.13}
\]
Equations (6.3)--(6.11) prove
\[
   i^{-1}(\alpha)=\gamma_+\sqcup\gamma_-.
\tag{6.14}
\]
No additional sheet meets the source disk.

The endpoint limits are
\[
   \lim_{t\downarrow0}z_0(t)=-1\in K',
   \qquad
   \lim_{t\uparrow t_*}z_0(t)\in\partial\mathbb D_{75},
\tag{6.15}
\]
\[
   \lim_{t\downarrow1-t_*}z_{-1}(t)
   \in\partial\mathbb D_{75},
   \qquad
   \lim_{t\uparrow1}z_{-1}(t)=1\in K'.
\tag{6.16}
\]
For interior parameter values, \(\gamma_+\) lies in the upper half-plane
and \(\gamma_-\) in the lower half-plane, so both avoid \(K'\).
The same compact-preimage argument as in Section 5.5 shows that both
are proper paths in
\[
   \mathbf U'\setminus K'.
\tag{6.17}
\]
They are distinct components, with sheet labels \(0\) and \(-1\).

## 7. The two distinct restriction components have one image

For \(0<s<t_*\), equation (6.10) gives
\[
   z_{-1}(1-s)=-z_0(s).
\tag{7.1}
\]
Since \(f(z)=z^2\),
\[
   f\bigl(z_{-1}(1-s)\bigr)
   =
   f\bigl(z_0(s)\bigr).
\tag{7.2}
\]
Therefore, as unparametrized paths,
\[
   f(\gamma_-)=f(\gamma_+).
\tag{7.3}
\]

For completeness, define their common image by
\[
   \delta(s)
   =
   (-1+2s+100is)^2,
   \qquad
   0<s<t_*.
\tag{7.4}
\]
Then
\[
   f(\gamma_-)=f(\gamma_+)=\delta((0,t_*)).
\tag{7.5}
\]

### 7.1 The common image is itself a proper path

Because \(|z_0(s)|<75\),
\[
   |\delta(s)|<5625.
\tag{7.6}
\]
Its imaginary part is
\[
   \operatorname{Im}\delta(s)
   =
   200s(-1+2s).
\tag{7.7}
\]
For \(s>0\), this vanishes only at \(s=1/2\), where
\[
   \delta(1/2)=(50i)^2=-2500\notin[0,1].
\tag{7.8}
\]
Thus \(\delta\) avoids \(K\).

If \(\delta(s)=\delta(t)\), then
\[
   z_0(s)=z_0(t)
   \quad\text{or}\quad
   z_0(s)=-z_0(t).
\tag{7.9}
\]
The first alternative gives \(s=t\).  In the second, comparison of
imaginary parts gives \(s=-t\), impossible for positive \(s,t\).
Hence \(\delta\) is simple.

Finally,
\[
   \lim_{s\downarrow0}\delta(s)=1\in K,
   \qquad
   \lim_{s\uparrow t_*}|\delta(s)|=5625.
\tag{7.10}
\]
Thus \(\delta\) is a proper path from the inner to the outer ideal
boundary of \(\mathbf U\setminus K\).

Combining (6.14) and (7.5),
\[
   i^*\alpha=\{\gamma_+,\gamma_-\},
\tag{7.11}
\]
but under the untagged set convention,
\[
\begin{aligned}
   F_*\alpha
   &=
   f_*i^*\alpha\\
   &=
   \{f(\gamma_+),f(\gamma_-)\}\\
   &=
   \{\delta,\delta\}\\
   &=
   \{\delta\}.
\end{aligned}
\tag{7.12}
\]
Consequently \(\alpha\) does **not** break according to KKL line 2161,
even though its immersion restriction has two distinct proper
components.

## 8. Partial ideal-marking analysis and the unresolved outer pullback

The collision in (7.12) is set-theoretic and already shows why
occurrence multiplicity cannot be inferred from an untagged image set.
We now record what can, and cannot, be certified about KKL's
ideal-marking filter in this model.

Put
\[
   V=\mathbf U\setminus K,
   \qquad
   V'=\mathbf U'\setminus K'.
\tag{8.1}
\]
Both are hyperbolic annuli without cusps.  Each has an inner ideal
boundary component belonging to the slit continuum and an outer ideal
boundary component belonging to the disk boundary.

On the inner ideal boundary:

1. \(f:V'\to V\) extends as an orientation-preserving degree-two
   covering;
2. \(i\) has degree one and is a homeomorphism on a collar of the inner
   ideal boundary, because \(i|_{K'}:K'\to K\) is a homeomorphism and
   \(i\) is locally injective on a neighborhood of \(K'\).

Let
\[
   g_\partial
   =
   f_\partial\circ i_\partial^{-1}
\tag{8.2}
\]
on the target inner ideal circle.  This is an orientation-preserving
degree-two circle covering.  Nothing proved above implies that an
arbitrary degree-two circle covering is conjugate to angle doubling, or
that its periodic points are dense.  To obtain those conclusions here
one would still have to:

1. construct a compactly contained embedded polynomial-like
   restriction from the local \(i\)-collar;
2. identify its prime-end external map with \(g_\partial\); and
3. invoke, with all hypotheses checked, the expanding external-map
   theorem for that restriction.

Those three analytic steps are not needed for the raw path-collision
theorem and are not proved in this note.  Accordingly, the rest of this
paragraph is conditional: assume that a finite
\(g_\partial\)-forward-invariant set \(E\) has been supplied such that:

- the two ideal ends of \(\alpha\) are not in \(E\);
- one boundary arc to which \(\alpha\) is subordinate contains at least
  three components of the complement of \(E\).

Thus
\[
   g_\partial(E)\subset E.
\tag{8.3}
\]
Mark the target inner ideal circle by the components of its complement
of \(E\), and mark the outer ideal circle as one entire interval.  Call
the resulting marking \(\mathcal I\).

On the inner ideal circle, the endpoint inclusion (8.3) gives the
required refinement relation.  Indeed, if
\(x\in i_\partial^{-1}(E)\), then
\[
   f_\partial(x)
   =
   g_\partial(i_\partial(x))
   \in E.
\tag{8.4}
\]
Therefore
\[
   i_\partial^{-1}(E)\subset f_\partial^{-1}(E),
\tag{8.5}
\]
which says precisely that the \(f\)-pulled inner marking refines the
\(i\)-pulled inner marking.

At the outer source boundary, \(i\) is nonproper: by (4.12), its
Euclidean boundary values remain strictly inside \(\mathbf U\).
That fact does **not** prove that KKL's maximal pullback
\(i^*\mathcal I\) has no remote ideal intervals there.  KKL line 2092
defines a pulled ideal subset through all subordinate proper paths, not
only through Euclidean boundary extension.  A complete action
certificate would have to enumerate those remote pulled intervals and
prove that \(f^*\mathcal I\) refines the resulting \(i^*\mathcal I\).
This inventory has not been supplied.  Consequently this section does
not claim that the displayed \(\mathcal I\) makes \(F_*\) a fully
defined KKL marked action.

Conditionally, if a compatible refinement containing the four displayed
ends is supplied, then:

- \(\alpha\) is a path because its subordinate base has combinatorial
  length at least three;
- \(\delta\) is a path because it joins different ideal-boundary
  components;
- \(\gamma_+\) and \(\gamma_-\) are paths in \(f^*\mathcal I\) because
  each joins the inner and outer ideal-boundary components of \(V'\).

A connected multi-interval lies in one ideal-boundary component.
Hence neither \(\gamma_+\) nor \(\gamma_-\) can be subordinate to a
multi-interval, of any length, that contains both its ends.  In
particular:

1. neither is excluded by KKL's definition of a path at line 1869;
2. neither is subordinate to a single interval in \(i^*\mathcal I\);
3. neither is discarded by the filter at lines 2096--2097.

Thus, under that additional compatible-action hypothesis, both
components in (7.11) survive the line-2097 filter, while their two
\(f\)-images still coincide as in (7.5).  The unconditional conclusion
of the model remains the proper-path collision (7.12), not a certified
collision of retained KKL Waves.

## 9. The exact obstruction to KKL line 1603

Let \(n\geq b\), and let \(\alpha\in A_{n+1}\).  Since
\[
   A_{n+1}\subset A_0\subset A^{N\text{-nbr}}
\tag{9.1}
\]
and \(n+1<N\) in every proof-used application, KKL's definition implies
that the successive untagged pushforward of \(\alpha\) remains a single
path through that horizon.

KKL line 1603 argues by contradiction:

1. if \(\alpha\) does not pass through \(K_0^n\), there are two
   restriction portions on the two sides of the separator;
2. both portions push forward to Waves;
3. therefore \(\alpha\) breaks.

Step 3 requires more than Steps 1--2.  It requires that the two
portions produce two **distinct retained output paths**.  The formally
missing predicate is:
\[
\begin{split}
 \operatorname{TSNC}(n,\alpha):\quad
 &\text{there exist retained proper components }
   \gamma^-_{n,\alpha},\gamma^+_{n,\alpha}\\
 &\text{on the two declared separator sides such that}\\
 &(f^{\,n+1})_*(\gamma^-_{n,\alpha})
   \neq
   (f^{\,n+1})_*(\gamma^+_{n,\alpha})
   \text{ as unparametrized paths.}
\end{split}
\tag{9.2}
\]
Here TSNC stands for **two-sided noncollision**.

The complete clause must also say that:

- both components survive every intermediate line-2097 filter;
- both terminal images are paths in the declared terminal marking;
- their endpoint intervals and parent itineraries are recorded;
- equality is tested after the full proper projection, not only before
  it.

The analytic model gives the underlying proper-path equality
\[
   \gamma_+\neq\gamma_-,
   \qquad
   f(\gamma_+)=f(\gamma_-),
\tag{9.3}
\]
but its common image is not a Wave and the complete outer marking action
is not certified.  It therefore does **not** violate the KKL-specific
predicate (9.2).  It proves only that (9.2) cannot be replaced by
distinct source components or distinct source sheets.  Its proper-path
collision certificate is
\[
\begin{array}{c|c|c|c}
\text{component}&\text{immersion sheet}&\text{source ends}
&\text{proper image}\\ \hline
\gamma_+&0&-1\ \text{to outer }z_0(t_*)&\delta\\
\gamma_-&-1&\text{outer }-z_0(t_*)\ \text{to }+1&\delta .
\end{array}
\tag{9.4}
\]
The merger is caused by the degree-two symmetry
\[
   f(z)=f(-z).
\tag{9.5}
\]
No critical point lies on either path: \(0\in K'\) has been removed.
Thus this is an occurrence collision under an unbranched covering of
the path surface, not a path crossing a critical point.

KKL's special Hubbard-tree and Wave endpoint combinatorics may rule out
(9.3) for the two particular portions in line 1603.  Establishing that
fact, including the full filter inventory, is precisely the open
noncollision lemma.

## 10. Why final component-to-component extraction needs a separate clause

Even if KKL line 1603 is granted as a source-language assertion, the
phrase "passes through \(K_0^n\)" is not defined in the Appendix as a
predicate on retained restriction components.

Put
\[
   m=N-1=b+2,
   \qquad
   Q=K_0^{m-1}=K_0^{b+1},
\tag{10.1}
\]
and let
\[
   \widehat Q
   =
   \bigl(I_m|_{K^m}\bigr)^{-1}(Q)
\tag{10.2}
\]
be the canonical final graph component already constructed in
`pql_iterate_filled_graph_naturality.md`.  Let
\[
   \mathcal K^m=P_m^{-1}(\mathcal K),
   \qquad
   V_m=U^m\setminus\mathcal K^m.
\tag{10.3}
\]

For a source leaf \(\alpha\in A_m\), define its typed retained final
restriction set
\[
\begin{split}
 \mathscr R_m(\alpha)=
 \{\,\gamma:\;&
 \gamma\text{ is a proper component of }
 I_m^{-1}(\alpha)\cap V_m;\\
 &\gamma\text{ is a path in the declared final marking;}\\
 &\gamma\text{ is not discarded by the pulled-interval filter}\,\}.
\end{split}
\tag{10.4}
\]
Let \(E_{\widehat Q}\) be the union of the marked ideal intervals
belonging to \(\widehat Q\), and let \(E_{\neg\widehat Q}\) be the union
of those belonging to
\(\mathcal K^m\setminus\widehat Q\).  Define
\[
\begin{split}
 \mathscr R_m^{\,Q}(\alpha)
 =
 \{\,\gamma\in\mathscr R_m(\alpha):&
 \text{ one end of }\gamma\text{ lies in }E_{\widehat Q},\\
 &\text{the other lies in }E_{\neg\widehat Q}\,\}.
\end{split}
\tag{10.5}
\]

The exact geometric predicate needed by the native KKL estimate is
\[
   \mathscr R_m^{\,Q}(\alpha)\neq\varnothing
   \qquad
   \text{for every }\alpha\in A_m.
\tag{10.6}
\]
Call (10.6) the **retained \(Q\)-exit property**.

Neither graph naturality nor the Boolean source phrase "passes through"
implies (10.6):

- the immersion restriction may split;
- a component may end at an ambient or nonproper ideal end rather than
  another member of \(\mathcal K^m\);
- a candidate component may be removed by the line-2097 filter;
- an itinerary transition in KKL Proposition 2099 may be adjacency or
  same-pullback containment rather than an actual path;
- two restriction occurrences may collide after \(P_m\).

Thus TSNC in (9.2) is the first missing predicate in the proof of line
1603, while (10.6) is the first missing predicate for the final
component-to-component extraction if line 1603 is taken as given.

## 11. Minimal replacement lemmas

### 11.1 Retained two-sided distinct-image lemma

The smallest repair that leaves KKL's existing definition of
unbreakability unchanged is the following.

> **Retained two-sided distinct-image lemma.**
> Under the complete hypotheses of KKL's stationary-Wave block, fix
> \(n\geq b\) and \(\alpha\in A_{n+1}\).  If the occurrence trace of
> \(\alpha\) does not pass through the selected separator \(K_0^n\),
> then the two separator-side portions determine retained proper paths
> \(\gamma^-_{n,\alpha}\) and \(\gamma^+_{n,\alpha}\) through every
> intermediate restriction, their terminal images are KKL Waves in the
> declared marking, and
> \[
>    (f^{\,n+1})_*(\gamma^-_{n,\alpha})
>    \neq
>    (f^{\,n+1})_*(\gamma^+_{n,\alpha})
> \tag{11.1}
> \]
> as paths in the terminal ideal marking.

With (11.1), the proof of the source-language pass-through is immediate:
the terminal pushforward contains at least two paths, contradicting
\((n+1)\)-unbreakability.

The proof of this lemma must use KKL-specific geometry.  At minimum it
must record, for both portions:

\[
   (\text{stage},\text{sheet},\text{parent component},
     \text{entry access},\text{exit access},
     \text{endpoint interval pair}).
\tag{11.2}
\]
It must then show that the two terminal endpoint pairs or terminal
geometric paths differ.  Distinct sheet labels before the proper map are
not sufficient, as (9.3) proves.

### 11.2 Final retained \(Q\)-exit lemma

To discharge the actual final extraction gate, one additionally needs:

> **Final retained \(Q\)-exit lemma.**
> For \(m=b+2\), every occurrence \(\alpha\in A_m\) satisfies
> (10.6).  The proof identifies the first and last ideal ends of the
> selected component, proves that both are in the complete final
> marking, and records all intervening tree vertices, filled components,
> sheets, and filter decisions.

This is a component statement, not a coarse label statement.  If it
fails, the required obstruction record is:

\[
\begin{split}
 (&\alpha,\text{ first split stage},\text{ sheet},
   \text{ component/access at }\widehat Q,\\
  &\text{other ideal end},\text{ filter reason},
   \text{ complete parent itinerary},
   \text{ terminal }P_m\text{-image}).
\end{split}
\tag{11.3}
\]

### 11.3 Occurrence tags as a larger replacement

One can instead define a tagged pushforward
\[
   F_*^\#\alpha
   =
   \{\,(f(\gamma),\omega(\gamma)):
       \gamma\in\iota^*\alpha\,\},
\tag{11.4}
\]
where \(\omega(\gamma)\) contains the data in (11.2).  In the analytic
model,
\[
   (\delta,\omega(\gamma_+))
   \neq
   (\delta,\omega(\gamma_-))
\tag{11.5}
\]
although the geometric paths agree.

This does **not** by itself repair KKL's printed proof.  Their
unbreakability is defined using the untagged \(F_*\), not \(F_*^\#\).
Replacing it by tagged unbreakability would require reproving every
Wave decomposition, width inequality, and maximal-subwave assertion
that uses breakability.  Therefore the distinct-geometric-image lemma
in Section 11.1 is the minimal repair compatible with the current
source.

## 12. Conditional endpoint selection and the Borel gate

The retained \(Q\)-exit property is the geometric gate.  It defines a
canonical maximal endpoint-selected candidate and avoids choosing one
leaf per source leaf.  It does not, by itself, prove that the candidate
is a Borel proper lamination in the precise sense needed for extremal
width.

Assume (10.6), and define
\[
   B_Q
   =
   \bigcup_{\alpha\in A_m}
   \mathscr R_m^{\,Q}(\alpha).
\tag{12.1}
\]
Equivalently, \(B_Q\) is the maximal sublamination of the complete
retained restriction \(I_m^*A_m\) whose leaves connect
\(E_{\widehat Q}\) to \(E_{\neg\widehat Q}\).

### Proposition 12.1

Under the complete-marking and retained-\(Q\)-exit hypotheses, assume
additionally that the endpoint-selected set \(B_Q\) in (12.1) is a Borel
proper sublamination of the complete retained restriction.  Then:

1. \(B_Q\) is a lamination in the final marked surface;
2. for every \(\alpha\in A_m\), \(I_m^*\alpha\) contains a leaf of
   \(B_Q\);
3. KKL's domination lemma gives
   \[
      \mathcal W(A_m)\leq\mathcal W(B_Q).
   \tag{12.2}
   \]

#### Proof

The first assertion is the explicit Borel-sublamination hypothesis.
Property (10.6) proves the second assertion.  Apply KKL's domination
lemma, lines 2086--2089, with
\[
   S=A_m,\qquad S'_1=B_Q.
\tag{12.3}
\]
Its hypothesis is exactly assertion 2, and its conclusion is (12.2).
\(\square\)

The endpoint predicate is countably typed by the ideal marking, and KKL
use analogous maximal endpoint-defined subfamilies at lines 1750, 1763,
and 1776.  That is useful precedent, but it is not a proof that every
endpoint-selected union in the present nonproper immersion restriction
is Borel.  One must prove Borel dependence of the retained component
and its two ideal endpoints in local flow-box coordinates, or construct
the sublamination by a source theorem that already includes this
measurability.

Thus the unresolved content has three separate parts: the two-sided Wave
noncollision needed for line 1603, the per-occurrence geometric
\(Q\)-exit statement (10.6), and the Borel endpoint-sublamination gate.

## 13. Adversarial audit

1. **No claim against the full KKL theorem.**  The explicit map is an
   abstract pseudo-quadratic-like map.  It is not asserted to be a
   primitively renormalizable, parabolically bounded KKL block.
2. **No numerical inference.**  All radius and path assertions follow
   from exact inequalities and the exact quadratic equation (6.6).
3. **All immersion sheets are exhausted.**  Equations (6.4),
   (6.9), and (6.11) prove that only \(k=0,-1\) occur.
4. **Both restriction components are proper.**  Their four ideal limits
   are listed in (6.15)--(6.16).
5. **Filter survival is conditional.**  Once a compatible full pulled
   marking exists, each component joins different ideal-boundary
   components and cannot be subordinate to one pulled interval.  The
   remote outer pullback inventory needed to establish that compatible
   action is not proved here.
6. **The collision is literal.**  Equation (7.1) and the identity
   \(f(z)=f(-z)\) prove equality of the two complete unparametrized
   images.
7. **The common image is a path.**  Equations (7.6)--(7.10) prove
   target containment, obstacle avoidance, injectivity, and properness.
   It is not a Wave because its ends lie on different ideal-boundary
   components.
8. **No critical crossing is hidden.**  The critical point \(0\) lies in
   the removed continuum \(K'\); neither restriction leaf meets it.
9. **A local embedded collar is insufficient.**  The model has the
   native embedded collar near \(K'\), but the chosen representative
   leaves that collar and acquires two remote restriction components.
   KKL's path restriction is applied to actual paths, not to an
   independently chosen collar representative.
10. **Graph naturality is not disputed.**  The homeomorphism
    \(i|_{K'}:K'\to K\) is proved in Section 4.4.  The failure concerns
    complementary path occurrences.
11. **Pass-through and \(Q\)-exit are separated.**  The KKL-specific
    two-sided Wave noncollision theorem is still required to validate
    the source contradiction at line 1603; the retained \(Q\)-exit
    property is separately needed for a component-to-component path.
12. **Tags do not silently change width.**  The tagged alternative is
    stated only as a larger replacement program.  No multiplicity is
    inserted into extremal width.
13. **Borel assembly is not assumed.**  Endpoint selection defines a
    canonical candidate but still needs a Borel-sublamination proof.
14. **Global status.**  Nothing here proves VAAPC-I, UPTCR, rigidity,
    or MLC.

## 14. Exact next proof target

The next source-specific proof attempt should work in the actual KKL
finite planar Hubbard tree and establish, in this order:

1. the two-occurrence binder from
   `kkl_stationary_retained_realization_source_audit.md`: two distinct
   complete fiber-product components realizing the two portions named at
   line 1603, not merely independently selected one-stage lifts;
2. survival of every intermediate line-2097 filter, with every
   attachment interval and whole-path subordination decision recorded;
3. complete marked-access records and selected-collar confinement with
   no re-entry or ambient sheet change;
4. the exact selected-collar deck-path noncollision predicate from
   `kkl_stationary_tsnc_source_reduction.md`; inequality of the complete
   deck-transformed endpoint pairs is a sufficient, not necessary,
   certificate;
5. conversion of the resulting source pass-through into the filled
   final restriction property (10.6);
6. prime-end compatibility in the non-locally-connected rational
   lamination model;
7. Borel dependence of the retained endpoint-selected subfamily.

The proved one-retained-chain theorem guarantees that at least one
retained component exists at each stage and that all retained components
have the same singleton untagged image.  It supplies none of the
two-occurrence coherence required in step 1.

If step 4 fails, the first collision must be recorded in the format
(11.3), and the Wave state must retain the occurrence tag (11.2).  If
step 5 fails, the first ambient or filtered exit from the component
\(\widehat Q\) is the exact obstruction.  No coarse pass-through label
can replace either certificate.
