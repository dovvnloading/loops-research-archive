# Canonical/KL geometric-trace proper-end response

## Fixed-map proper-lift theorem, exact exhaustion no-go, and replacement gate

**Date:** 2026-07-26  
**Proof status:** the fixed full-pseudo-piece maximal-lift theorem and the
two no-go propositions below are proved.  The Wave-uniform geometric-trace
response theorem is open.

This pass cross-examines the immediate target left by
`canonical_kl_restricted_interface_classification.md`.  It finds one
positive theorem and one decisive correction.

1. On a supplied **full** Kahn--Lyubich pseudo-piece inclusion immersion,
   every maximal parametrized lift of a KKL proper target path is itself a
   KKL proper source path.  Its two ideal endpoints and their target values
   are canonical.
2. The parametrized pullback does **not** exhaust the KKL restriction.
   KKL use every proper source path contained in the geometric inverse
   trace.  Even the identity map of the disk has additional loop-omitting
   and backtracking restrictions.
3. A single holomorphic disk immersion can give one proper target path
   infinitely many distinct proper source restrictions.  Equal-width
   interior branch collars then give an unbounded raw branchwise
   crossing-width response.
4. “Proper path,” “the immersion is proper on an ideal subset,” and
   “the immersion is end-proper on a pulled multi-interval” have different
   types.  A path component cannot be classified as “end-proper.”

Thus the previously proposed relation proper-end theorem is not proved in
its old form.  The exact replacement is a tagged, end-compactified
**geometric inverse-trace path space**, followed in the correct order by
marking construction, whole-end-interval properness, analytic response,
and a separate Cartesian final-root no-birth theorem.

No statement in this file proves an actual quadratic Wave-stage
alignment, a uniform Value response, final-root stability, VAAPC-I,
UPTCR, rigidity, or MLC.

---

## 1. Source lock and admissible imports

### 1.1 KKL source

The local copy

```text
.tmp_wave_audit/waves-with-Misha.tex
```

has SHA-256

```text
AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The exact imported clauses are:

- line 406: a proper path
  \(\gamma:(0,1)\to V\) extends continuously to
  \([0,1]\to V\cup\partial_iV\), with both endpoints in
  \(\partial_iV\);
- lines 2081--2084: for a holomorphic immersion
  \(\iota:V'\to V\),
  \(\iota^*\gamma\) is the set of **proper paths in \(V'\) contained in**
  \(\iota^{-1}(\gamma)\);
- lines 2092--2097: \(\iota^*I\) is defined by a universal
  unique-restriction/subordination condition; different pulled intervals
  may fail to exist or may overlap;
- lines 2128--2129: the pair \(F=(f,\iota)\) acts on
  \((V,\mathcal I)\) only after
  \(f^*\mathcal I\) refines \(\iota^*\mathcal I\);
- lines 2157--2159: \(\iota\) is end-proper on a multi-interval only when
  it is proper on every **complete end-interval** of that multi-interval.

These are definitions in their native setting.  They are not a theorem
that the canonical/KL relation realizes the setting at every Wave stage.

### 1.2 KL source

The local copy

```text
.tmp_kl08_source/psiql.tex
```

has SHA-256

```text
6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF
```

The exact imported clauses are:

- lines 95--160: construction of the full pseudo-piece
  \(\mathbf Y\) and its holomorphic immersion into the ambient bold
  domain;
- lines 169--207: dynamical maps induce coverings, whereas puzzle-piece
  inclusions induce immersions;
- lines 231--244: the full pseudo-piece has the named
  \(\lambda,\xi,\eta\) ideal-boundary tiling;
- lines 248--253: an inclusion immersion extends continuously to the
  full pseudo-piece boundary, but its source boundary need not map into
  the target boundary.

`KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY` supplies the separately proved
fact that the full source and target pseudo-pieces in this use are
conformal disks and that their named ideal closures are closed conformal
disks.  No local connectivity of a Julia set is used.

### 1.3 What is not imported

The following are not source consequences and remain unavailable:

- global injectivity of the inclusion immersion;
- properness on every named ideal interval;
- existence or pairwise disjointness of every \(\iota^*I\);
- refinement by the dynamical covering marking;
- uniqueness of a proper restriction;
- a finite sheet bound;
- a uniform response for omitted restrictions; or
- stability under a final-root enlargement.

---

## 2. Type ledger

Let \(V',V\) be hyperbolic surfaces, let
\(\iota:V'\to V\) be a holomorphic immersion, and let
\(\mathcal I\) be an ideal marking of \(V\).

The three predicates used by KKL are:

\[
\begin{aligned}
\operatorname{PathProp}_{V'}(\delta)
&:\quad
\delta:(0,1)\to V'
\text{ has two point-valued ideal endpoints},\\
\operatorname{BdProp}_{\iota}(X')
&:\quad
\iota\text{ extends continuously and properly on }
X'\subset\partial_iV',\\
\operatorname{EndProp}_{\iota}(I')
&:\quad
\operatorname{BdProp}_{\iota}(E)
\text{ holds for every complete end-interval }E\text{ of }I'.
\end{aligned}
\tag{2.1}
\]

Their inputs are, respectively, a path, an ideal-boundary subset, and a
multi-interval whose end-intervals have already been defined.  Therefore

\[
\boxed{
\text{“a path component is end-proper” is not a typed KKL assertion.}
}
\tag{2.2}
\]

The valid construction order is

\[
\begin{aligned}
&\text{geometric source restrictions}\\
&\quad\Longrightarrow
\text{the universal predicates defining every }\iota^*I\\
&\quad\Longrightarrow
\{\iota^*I:I\in\mathcal I\}\text{ is a partial ideal marking}\\
&\quad\Longrightarrow
f^*\mathcal I\text{ refines }\iota^*\mathcal I\\
&\quad\Longrightarrow
\operatorname{BdProp}\text{ and }\operatorname{EndProp}
\text{ on the complete intervals actually used.}
\end{aligned}
\tag{2.3}
\]

Reversing any arrow in (2.3) assumes part of the desired Wave action.

---

## 3. Fixed full-pseudo-piece maximal-lift properness

### 3.1 Hypotheses

Fix one supplied full KL pseudo-piece inclusion datum

\[
\iota:\mathbf Y_s\longrightarrow\mathbf Y_t
\tag{3.1}
\]

such that:

1. \(\mathbf Y_s\) and \(\mathbf Y_t\) are conformal disks;
2. their ideal closures
   \(\overline{\mathbf Y_s}^{\,i}\) and
   \(\overline{\mathbf Y_t}^{\,i}\) are the corresponding closed disks;
3. \(\iota\) is a nonconstant holomorphic immersion; and
4. \(\iota\) has the KL continuous extension

   \[
   \bar\iota:
   \overline{\mathbf Y_s}^{\,i}
   \longrightarrow
   \overline{\mathbf Y_t}^{\,i}.
   \tag{3.2}
   \]

The map in (3.2) is not assumed to be injective or boundary-valued.

Let

\[
\alpha:(0,1)\longrightarrow\mathbf Y_t
\tag{3.3}
\]

be a KKL proper path, with continuous extension

\[
\bar\alpha:[0,1]\longrightarrow
\overline{\mathbf Y_t}^{\,i},
\qquad
\bar\alpha(0),\bar\alpha(1)\in\partial_i\mathbf Y_t.
\tag{3.4}
\]

Form the parametrized fiber product

\[
\mathscr P_\iota(\alpha)
=
\{(t,z)\in(0,1)\times\mathbf Y_s:
  \alpha(t)=\iota(z)\}.
\tag{3.5}
\]

The already proved local-homeomorphism argument shows that each path
component \(C\) of (3.5) is a graph

\[
C=
\{(t,\widetilde\alpha_C(t)):t\in J_C\},
\qquad
J_C=(a_C,b_C)\subset(0,1),
\tag{3.6}
\]

of one maximal parameter-compatible lift.

### Theorem 3.1 -- maximal lifts are proper source paths

For every component \(C\) in (3.6), there are unique points

\[
p_C^-,p_C^+\in\partial_i\mathbf Y_s
\tag{3.7}
\]

such that

\[
\lim_{t\downarrow a_C}\widetilde\alpha_C(t)=p_C^-,
\qquad
\lim_{t\uparrow b_C}\widetilde\alpha_C(t)=p_C^+.
\tag{3.8}
\]

Consequently, after any orientation-preserving reparametrization
\((0,1)\cong J_C\), the lift is a KKL proper path in
\(\mathbf Y_s\).  Its endpoint values are exactly

\[
\bar\iota(p_C^-)=\bar\alpha(a_C),
\qquad
\bar\iota(p_C^+)=\bar\alpha(b_C).
\tag{3.9}
\]

Here \(\bar\alpha(a_C)\) means \(\alpha(a_C)\) when
\(a_C\in(0,1)\), and similarly at \(b_C\).

Thus an endpoint of \(J_C\) equal to \(0\) or \(1\) is a
boundary-valued point-end, while an endpoint strictly inside \((0,1)\) is
a target-interior break end.  Both are source ideal endpoints; this
pointwise distinction does not prove map properness on any nondegenerate
source ideal interval.

### Proof

We prove the assertion at \(a_C\); the argument at \(b_C\) is identical.
For \(\epsilon>0\), put

\[
Z_\epsilon
=
\overline{
  \widetilde\alpha_C(
    (a_C,a_C+\epsilon)\cap J_C
  )
}^{\,i}
\subset\overline{\mathbf Y_s}^{\,i},
\tag{3.10}
\]

and define the end cluster set

\[
Z_C^-=\bigcap_{\epsilon>0}Z_\epsilon.
\tag{3.11}
\]

Each \(Z_\epsilon\) is compact and connected: it is the closure in a
compact Hausdorff disk of the connected image of an interval.  The
family is nested and nonempty.  Hence \(Z_C^-\) is nonempty, compact, and
connected.

We next prove

\[
Z_C^-\cap\mathbf Y_s=\varnothing.
\tag{3.12}
\]

Suppose instead that \(x\in Z_C^-\cap\mathbf Y_s\), and put
\(y=\iota(x)\).  Because \(\iota\) is a local homeomorphism at \(x\),
choose neighborhoods \(U\ni x\) and \(V\ni y\) for which

\[
\iota|_U:U\xrightarrow{\cong}V.
\tag{3.13}
\]

Continuity of \(\bar\alpha\) gives
\(\bar\alpha(a_C)=y\) and puts a sufficiently short target tail inside
\(V\).  Since \(x\) is a cluster point, choose
\(t_0\in J_C\) on that tail with
\(\widetilde\alpha_C(t_0)\in U\).  The local inverse in (3.13) defines

\[
\beta(t)=(\iota|_U)^{-1}\alpha(t)
\tag{3.14}
\]

near \(a_C\), and
\(\beta(t_0)=\widetilde\alpha_C(t_0)\).  Uniqueness of lifts for a local
homeomorphism makes \(\beta\) and \(\widetilde\alpha_C\) agree on their
connected common parameter domain.

If \(a_C\in(0,1)\), equation (3.14) continues the graph through
\(a_C\), contradicting maximality in (3.6).  If \(a_C=0\), it would give
\(\bar\alpha(0)=\iota(x)\in\mathbf Y_t\), contradicting
\(\bar\alpha(0)\in\partial_i\mathbf Y_t\).  This proves (3.12).

By (3.12),

\[
Z_C^-\subset\partial_i\mathbf Y_s.
\tag{3.15}
\]

Continuity of (3.2) and (3.4) gives

\[
\bar\iota(Z_C^-)=\{\bar\alpha(a_C)\}.
\tag{3.16}
\]

It remains to show that a connected subset of a boundary fiber in (3.16)
is a point.  Uniformize the source and target as disks and write the
immersion as a bounded nonconstant holomorphic map

\[
F:\mathbb D\to\mathbb D
\tag{3.17}
\]

continuous on \(\overline{\mathbb D}\).  If a connected subset of
\((\bar F)^{-1}(w)\cap\partial\mathbb D\) were nondegenerate, it would
contain a nondegenerate circular arc \(A\).  Then

\[
H=F-w
\tag{3.18}
\]

would have continuous boundary value zero on \(A\).

Precompose \(F\) by a source-disk automorphism sending \(0\) to a point
where \(F\ne w\), so that \(H(0)\ne0\), and let
\(M=\max(1,\|H\|_\infty)\).  Jensen's formula gives a constant \(B<\infty\)
such that, for all \(0<r<1\),

\[
\int_0^{2\pi}
 \bigl(\log M-\log|H(re^{it})|\bigr)\,dt
\le B.
\tag{3.19}
\]

For every \(e^{it}\in A\), continuity gives
\(|H(re^{it})|\to0\), so the nonnegative integrand in (3.19) tends to
\(+\infty\) on a set of positive measure.  Fatou's lemma contradicts
(3.19).  Therefore every connected subset of a boundary fiber is a
singleton.

Apply this to the connected set \(Z_C^-\).  Write
\(Z_C^-=\{p_C^-\}\).  A curve in a compact Hausdorff space with exactly
one end cluster point converges to that point, proving the first limit in
(3.8).  The other end is identical, and (3.9) follows from continuity.
\(\square\)

### 3.2 Exact scope

Theorem 3.1 proves path properness for maximal parametrized lifts on a
supplied **full** KL pseudo-piece.  It does not prove:

- that those lifts exhaust \(\iota^*\alpha\) in the KKL sense;
- that \(\bar\iota(p_C^\pm)\) is always ideal;
- that \(\iota\) is proper on an ideal interval;
- that a pulled ideal marking exists;
- that any proper lift is unique; or
- that the tilewise canonical relation has a full relative-boundary
  extension.

---

## 4. Parametrized pullback does not exhaust KKL restriction

Let

\[
|\gamma|=\gamma((0,1))
\tag{4.1}
\]

denote the geometric trace of a path.  KKL's definition is

\[
\iota^*_{\rm KKL}\gamma
=
\left\{
\delta:
\operatorname{PathProp}_{V'}(\delta),\ 
|\delta|\subset\iota^{-1}(|\gamma|)
\right\}
\big/\text{reparametrization}.
\tag{4.2}
\]

By contrast, the parametrized fiber product records solutions of

\[
\iota(\widetilde\gamma(t))=\gamma(t)
\tag{4.3}
\]

on maximal parameter subintervals.  Equation (4.3) is stronger than
containment in (4.2).

### Proposition 4.1 -- identity-lollipop counterexample

There is a proper path \(\gamma\) in \(\mathbb D\) such that, for
\(\iota=\operatorname{id}_{\mathbb D}\),

\[
\{\text{maximal parametrized lifts of }\gamma\}
\subsetneq
\iota^*_{\rm KKL}\gamma.
\tag{4.4}
\]

### Construction and proof

Take ideal endpoints \(-1,1\), interior vertices
\(p=-1/2\), \(q=1/2\), and two disjoint arcs \(U,L\subset\mathbb D\)
joining \(p\) to \(q\), one above and one below the real axis.  Define
\(\gamma\) by the chronological word

\[
[-1,p]\ *\ U_{p\to q}\ *\ L_{q\to p}\ *\
L_{p\to q}\ *\ [q,1].
\tag{4.5}
\]

It extends continuously to the ideal endpoints \(-1\) and \(1\), so it
is KKL proper.  For the identity map, the parametrized fiber product is
the single graph

\[
\{(t,\gamma(t)):0<t<1\}.
\tag{4.6}
\]

Now define the simple lower route

\[
\delta=[-1,p]\ *\ L_{p\to q}\ *\ [q,1].
\tag{4.7}
\]

The path \(\delta\) is proper and

\[
|\delta|\subset|\gamma|
=\iota^{-1}(|\gamma|).
\tag{4.8}
\]

Therefore \(\delta\in\iota^*_{\rm KKL}\gamma\).  Its image omits \(U\),
so it is not a reparametrization of (4.5) and is absent from (4.6).
This proves (4.4). \(\square\)

### Corollary 4.2

The tagged fiber products constructed in
`CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION` are complete for
maximal **parameter-compatible interior lifts**.  They are not, without a
new trace theorem, complete for KKL restrictions.

Even requiring \(\gamma\) to be a simple crosscut does not enumerate
arbitrary raw proper paths: for the identity disk and the diameter from
\(-1\) to \(1\), a path can travel from \(-1\) to \(0\) and back to
\(-1\).  It is a proper source hairpin contained in the diameter trace
but is not a maximal oriented lift component.  KKL later ignores some
paths that are subordinate to one pulled interval or are not paths in the
refined marking, but that exclusion is downstream of the missing marking
construction and cannot be assumed here.

---

## 5. One target path can have infinitely many proper restrictions

The failure in Section 4 is not only a backtracking artifact.  The model
below satisfies the local-homeomorphism and exact sheet-relation
hypotheses used by the tilewise parametrized pullback.  It does **not**
have KL's continuous extension on the entire source ideal circle, so it
is a counterexample to inference from the current restricted relation
data, not to the stronger full-pseudo-piece hypotheses of Theorem 3.1.

### Proposition 5.1 -- exponential disk immersion

Let

\[
C(z)=\frac{1+z}{1-z},
\qquad
K(z)=e^{-C(z)}.
\tag{5.1}
\]

Then \(C:\mathbb D\to\{u:\operatorname{Re}u>0\}\) is a biholomorphism and

\[
K'(z)
=
-\frac{2e^{-C(z)}}{(1-z)^2}
\ne0.
\tag{5.2}
\]

Hence \(K:\mathbb D\to\mathbb D\) is a holomorphic immersion.

For the proper target diameter

\[
\alpha(s)=s,\qquad -1<s<1,
\tag{5.3}
\]

and every \(k\in\mathbb Z\), define, for \(0<t<1\),

\[
u_k(t)=-\log t+2\pi i k,
\qquad
z_k(t)=\frac{u_k(t)-1}{u_k(t)+1}.
\tag{5.4}
\]

Then

\[
K(z_k(t))=e^{-u_k(t)}=t.
\tag{5.5}
\]

The two source limits are

\[
\lim_{t\downarrow0}z_k(t)=1,
\qquad
\lim_{t\uparrow1}z_k(t)
=
\frac{2\pi i k-1}{2\pi i k+1}.
\tag{5.6}
\]

The second point lies on \(\partial\mathbb D\), because its numerator and
denominator have equal modulus.  Thus every \(z_k\) is a proper source
path contained in \(K^{-1}(|\alpha|)\).  The paths are distinct: their
second ideal endpoints are distinct.  Consequently

\[
\#K^*_{\rm KKL}\alpha=\infty.
\tag{5.7}
\]

Each path is also a maximal parametrized lift over the proper subinterval
\((0,1)\subset(-1,1)\).  Its left parameter end stops at the
target-interior point \(0\), while its source escapes to the ideal point
\(1\).  Thus path properness does not imply map-end properness, and a
single target proper path need not have a unique proper restriction.
\(\square\)

### 5.1 Label and phase consequence

The integer \(k\) is the logarithmic deck phase.  Erasing it changes the
infinite family (5.7) into a false singleton.  Therefore every candidate
response must retain either:

- every source label, sheet, coset, and deck phase; or
- a proved quotient congruence that preserves all later restriction,
  subordination, endpoint, and weight queries.

No such finite future-faithful quotient is currently available.

---

## 6. Raw sheetwise interior-crossing width is unbounded

The same immersion gives a quantitative obstruction.

Fix

\[
0<a<b,
\qquad
0<\theta<\pi,
\tag{6.1}
\]

and in the right-half-plane \(u=x+iy\) define

\[
R_k
=
\{a<x<b,\ 2\pi k-\theta<y<2\pi k+\theta\},
\qquad k\in\mathbb Z.
\tag{6.2}
\]

The rectangles are pairwise disjoint.  Because their vertical height is
\(2\theta<2\pi\), the map

\[
u\longmapsto e^{-u}
\tag{6.3}
\]

is injective on each \(R_k\), and maps every \(R_k\) biholomorphically
onto the same target sector

\[
S=
\{e^{-b}<|w|<e^{-a},\ |\arg w|<\theta\}.
\tag{6.4}
\]

Let \(\Gamma_k\) be the family of curves in \(R_k\) joining its two
vertical sides.  Conformal invariance and the rectangle formula give

\[
\mathcal W(\Gamma_k)
=
\frac{2\theta}{b-a}
=:w_0>0.
\tag{6.5}
\]

For \(|k|\le m\), the families have disjoint supports.  The parallel law
for extremal width therefore gives

\[
\mathcal W\left(
\bigcup_{|k|\le m}\Gamma_k
\right)
=
\sum_{|k|\le m}\mathcal W(\Gamma_k)
=(2m+1)w_0.
\tag{6.6}
\]

Hence

\[
\mathcal W\left(
\bigcup_{|k|\le m}\Gamma_k
\right)\longrightarrow\infty.
\tag{6.7}
\]

### Proposition 6.1 -- raw branchwise response no-go

Local univalence, exact sheet enumeration, and endpoint labels alone do
not imply a universal raw width bound for the disjoint interior crossing
families carried on distinct sheets.
Any rule that retains only a uniformly bounded number of the branches in
(6.2) and charges the remaining disjoint crossing families by their
ordinary nonnegative extremal width has an unbounded charge.

This proposition is deliberately narrow.  It does not rule out a
calibrated, signed, discounted, or source-specific Value response.  Such
a response must be explicitly constructed and proved observable; it
cannot be inferred from the present relation data.  The rectangles are
compact interior branch collars; this proposition does not itself realize
them as complete KKL-marked proper-path laminations.

---

## 7. Independent endpoint and enlargement counterchecks

These examples separate further hypotheses.  They are not asserted to be
actual quadratic Wave blocks.

### 7.1 Continuous boundary extension is not boundary properness

The embedding

\[
F(z)=\frac z2:\mathbb D\longrightarrow\mathbb D
\tag{7.1}
\]

extends continuously to \(\overline{\mathbb D}\), but

\[
F(\partial\mathbb D)
=
\{w:|w|=1/2\}
\subset\mathbb D.
\tag{7.2}
\]

Thus continuity, interior injectivity, and cyclic order on the source
circle do not imply properness on any nonempty source ideal arc.

### 7.2 A target landing point does not identify an access

The inclusion

\[
\mathbb D\setminus[0,1)\hookrightarrow\mathbb D
\tag{7.3}
\]

has two distinct source prime ends on the two sides of the slit with the
same target landing point.  Endpoint images alone therefore do not retain
access side or cyclic order.

### 7.3 A canonical deck-limit end need not be a point

For

\[
q(z)=e^{2\pi iz}
\tag{7.4}
\]

on a horizontal strip, deck translates \(z\mapsto z+n\) approach the two
wrapping ends.  Choose two distinct allowed heights \(y_1\ne y_2\).  As
\(n\to+\infty\), both sequences \(n+iy_1\) and \(n+iy_2\) approach the
same positive wrapping end, whereas

\[
q(n+iy_j)=e^{-2\pi y_j},
\qquad j=1,2,
\tag{7.5}
\]

are distinct constants.  The same argument with \(n\to-\infty\) treats
the other wrapping end.  Hence there is no point-valued quotient limit at
either wrapping deck-limit end.  Therefore these three endpoint frames
must remain separate:

1. an actual KL source prime end;
2. a canonical relative end in \(\Omega(N)/N\), or a recorded defect in
   \(\Lambda(N)\); and
3. a target ideal point, target-interior point, or target cluster set.

The two certified wrapping values in
`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY` do not fill the entire
\(\lambda,\xi,\eta\) boundary.

### 7.4 Subgroup compatibility is an independent input

For the identity map of an annulus, connected covers classified by

\[
H_s=2\mathbb Z,
\qquad
H_t=3\mathbb Z
\tag{7.6}
\]

do not admit the required based lift because
\(H_s\not\subset H_t\).  With

\[
H_s=6\mathbb Z,
\qquad
H_t=3\mathbb Z,
\tag{7.7}
\]

a lift exists but the first factor has two cosets.  Stagewise relation
spans therefore do not transport without explicit subgroup and monodromy
maps.

### 7.5 Coset equality does not prove geometric no-birth

Let \(U_0\Subset\mathbb D\) be a Jordan domain disjoint from a fixed
target crosscut.  Enlarge it to a Jordan dumbbell \(U_1\) by attaching a
thin lobe that crosses the crosscut.  Both inclusion diagrams have trivial
fundamental group, so all subgroup and coset tests are vacuous.  The new
lobe nevertheless creates a new inverse-trace component.

Thus final-root naturality requires a Cartesian component/path and
endpoint/access no-birth theorem.  It is separate from the response
estimate.

---

## 8. The replacement invariant

For one actual stage \(j\), the required response object is

\[
\mathfrak R_j^{\rm PE}
=
\left(
\mathfrak S_j^{\rm glued},
\mathcal I_j,
g_j^*\mathcal I_j,
\mathscr A_j,
\{\mathfrak G_{j,\gamma}\}_{\gamma\in\mathscr A_j},
\mathfrak E_j,
\mathfrak P_j,
\mathfrak W_j,
\mathfrak N_j^{\rm geom}
\right).
\tag{8.1}
\]

Every coordinate has a separate proof obligation.

### 8.1 Glued stage relation

\(\mathfrak S_j^{\rm glued}\) records:

- the actual source and target full pseudo-pieces;
- the dynamical covering \(g_j\);
- the inclusion immersion \(\iota_j\);
- every central and tile chart;
- the exact central/tile overlap equivalence;
- source label, target label, sheet, coset, and deck phase; and
- the chosen basepoints and subgroup morphisms.

The existing theorem supplies only fixed labeled tile relations.  It does
not yet construct this glued object at every Wave stage.

### 8.2 Complete proof-use family schema

\(\mathscr A_j\) is the target-first ledger of every curve family
\(\Gamma\) and every universal KKL subordination query used by Wave,
Wanderers,
domination, quasi-additivity, covering, or width comparison.  It may not
be defined by the desired answer.

### 8.3 Geometric inverse-trace path space

For \(\Gamma\in\mathscr A_j\) and \(\gamma\in\Gamma\), first form the
tagged geometric trace

\[
\mathcal Z_{j,\gamma}
=
\iota_j^{-1}(|\gamma|),
\tag{8.2}
\]

with its central/tile graph, source labels, and sheet data.  Then
\(\mathfrak G_{j,\gamma}\) retains:

- every proper source path contained in \(\mathcal Z_{j,\gamma}\);
- maximal oriented traversals and all branch-switching or hairpin paths;
- the multiplicity class \(0,1,\ge2,\infty\);
- all component vertices and seam transitions; and
- the end compactification used to decide properness.

The parametrized fiber product is a subrecord of
\(\mathfrak G_{j,\gamma}\), not its definition.  Whether a retained path
survives KKL's source-marking filter is a downstream annotation in
\(\mathfrak P_j\), not an input to this construction.

### 8.4 Three-frame endpoint record

\(\mathfrak E_j\) records, for every retained end, the conformal endpoint
triple:

\[
\left(
p_{\rm KL},
\ [p]_{\Omega/N}\text{ or }\operatorname{Defect}_{\Lambda},
 \ p_t\text{ ideal/interior, or }\operatorname{Cluster}_t(p)
\right),
\tag{8.3}
\]

together with complete named conformal \(\lambda,\xi,\eta\) incidence,
stabilizer, and cyclic order in the authorized ideal models.  Physical
complement-access footprints, access-side landing components, and their
target multi-intervals are constructed later in
`DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`; importing them here would be
circular.

### 8.5 KKL predicate record

\(\mathfrak P_j\) records:

1. all proper source restrictions;
2. the \(0,1,\ge2,\infty\) unique-restriction predicate;
3. target and source subordination;
4. existence and maximality of each \(\iota_j^*I\);
5. pairwise disjointness of the pulled partial marking;
6. refinement by \(g_j^*\mathcal I_j\);
7. map properness on every proof-used whole interval; and
8. map properness on every complete end-interval needed for
   end-properness.

### 8.6 Analytic response record

\(\mathfrak W_j\) is an actual WAD/Value response measure on every
retained and omitted restriction.  It must prove one of:

- zero omission;
- an exact retained aggregate containing all nonnegative mass; or
- a universal bound derived from a stated analytic estimate.

Propositions 5.1--6.1 show that the current local-univalence and labeling
data supply neither a bounded-sheet theorem nor a bounded raw-width
response; either input must be proved separately for the actual Wave
stages.

### 8.7 Naturality record

\(\mathfrak N_j^{\rm geom}\) contains the subgroup and monodromy maps
across stage transport.  Final-root transport additionally requires
Cartesian
bijections of:

- compactified trace components;
- proper-path multiplicities;
- ideal endpoints and target-interior accesses;
- obstacles and nonproper bridges;
- cyclic order.

No-birth is not included in \(\mathfrak W_j\); it is a separate geometric
theorem.  If later use requires response-weight equivariance under
enlargement, that is a corollary with both PE-4 and PE-5 as hypotheses,
not part of PE-5.

### 8.8 Finite quotient criterion

A finite quotient of (8.1) is admissible only after its kernel is proved
to be a congruence for every future stage and every allowed enlargement,
preserving:

\[
\begin{gathered}
0,1,\ge2,\infty\text{ restriction multiplicity},\\
\text{all KKL subordination and proper/end-proper queries},\\
\text{source labels, access order, endpoint strata, and cluster defects},\\
\text{exact aggregated WAD/Value mass},\\
\text{and component no-birth/no-loss}.
\end{gathered}
\tag{8.4}
\]

No such quotient is proved here.

---

## 9. Acyclic replacement proof program

The former single target is split into five independently auditable
nodes.

### PE-1. Wave proof-use ledger

Freeze the actual finite theorem-call and target-family schema, including
every KKL universal subordination query.  The first failure is one omitted
proof use, recorded with its theorem call and stage.

### PE-2. Canonical/KL stage alignment

For every PE-1 stage, construct the same-source seed, labels, lifted
basepoints, subgroups, covering map, immersion map, central chart, tile
charts, and seam equalizers.  The first failure is an actual map,
basepoint, label, subgroup, or seam mismatch.

### PE-3. Proper-path and end-interval classification

Construct \(\mathfrak G_{j,\gamma}\), \(\mathfrak E_j\), and
\(\mathfrak P_j\).  Only after every \(\iota_j^*I\) exists and the pulled
partial marking is proved may whole-end-interval properness be tested.
The first failure is a competing/missing proper path, a non-point
endpoint cluster, an access mismatch, an overlapping pullback interval,
or a nonproper complete end-interval.

### PE-4. Relation response

Construct \(\mathfrak W_j\), prove Value/WAD observability, and prove a
universal charge or zero omission.  The first failure is an explicit
row-space defect or an unbounded analytic family such as Section 6.

### PE-5. Final-root relation no-birth

Independently of PE-4, prove subgroup reflection/exhaustion and Cartesian
component, path, endpoint, access, obstacle, and nonproper-bridge
bijections under enlargement.  The first born or merged object is the
obstruction certificate.

PE-4 and PE-5 are parallel successors of PE-3.  Folding final-root
uniformity into PE-4 would hide the geometric counterexample in
Section 7.5.

---

## 10. Adversarial validation

### 10.1 Positive controls

1. **Identity disk, simple diameter.**  The unique maximal oriented lift
   has endpoints \(-1,1\), as Theorem 3.1 predicts.
2. **Noninjective disk immersion.**  The map
   \(F(z)=e^{4(z-1)}\) maps \(\mathbb D\) into itself, has
   \(F'(z)\ne0\), extends continuously to the closed disk, and is
   noninjective.  Theorem 3.1 still gives proper source endpoints for
   every maximal parameter lift.
3. **KL full pseudo-piece.**  Theorem 3.1 uses only the locked disk,
   immersion, and continuous-extension hypotheses and permits
   target-interior boundary images exactly as KL do.

### 10.2 Hostile tests

| Test | Result | Consequence |
|---|---|---|
| Identity lollipop | extra loop-omitting KKL restriction | parametrized lifts are not trace-exhaustive |
| Identity diameter hairpin | raw proper path not a maximal traversal | source-marking filter must be proved |
| Exponential immersion | infinitely many proper restrictions | no singleton or finite-sheet inference |
| Disjoint logarithmic rectangles | raw local width grows like \((2m+1)w_0\) | sheet labels alone do not bound interior crossing response |
| \(z/2\) disk embedding | all source ideal points map to target interior | boundary continuity is not properness |
| Slit-disk inclusion | two accesses share one landing point | landing point is not access data |
| Incompatible annulus subgroups | no lift | stage spans need subgroup morphisms |
| Dumbbell enlargement | new trace component with trivial groups | coset tests do not prove no-birth |

### 10.3 Rejected shortcuts

1. **“The fiber-product components are the KKL pullback.”**  False by
   Proposition 4.1.
2. **“A proper source lift makes the immersion proper at its ends.”**
   False by Proposition 5.1 and (7.1).
3. **“End-proper is a path-component label.”**  Ill-typed by (2.1).
4. **“Continuous prime-end extension is boundary-valued.”**  KL explicitly
   say otherwise.
5. **“The two wrapping points complete the relative boundary.”**  False;
   they are only the source-locked extension domain currently proved.
6. **“Exact sheet labels bound omitted width.”**  False by (6.7).
7. **“Subgroup reflection proves final-root naturality.”**  False by
   Section 7.5.
8. **“A finite diagnostic promotes an analytic response.”**  False; the
   models only prove no-go and bookkeeping statements in their exact
   categories.
9. **“This is an actual quadratic counterexample.”**  Not asserted.  These
   models disprove inference from the presently listed hypotheses; the
   actual Wave theorem remains open.

---

## 11. Promotion boundary

The source-checkable results of this pass support exactly:

```text
FULL_KL_PSEUDOPIECE_MAXIMAL_LIFT_PROPERNESS
PARAMETRIZED_PULLBACK_KKL_EXHAUSTION_NO_GO
```

The first is Theorem 3.1.  The second comprises Proposition 4.1,
Proposition 5.1, and the narrowly raw width Proposition 6.1.

The following remain open:

```text
DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER
DIRECT_DECORATION_CANONICAL_KL_STAGE_ALIGNMENT
DIRECT_DECORATION_RELATION_PROPER_PATH_END_INTERVAL_CLASSIFICATION
DIRECT_DECORATION_CANONICAL_KL_RELATION_PROPER_END_RESPONSE
DIRECT_DECORATION_FINAL_ROOT_RELATION_NO_BIRTH
DIRECT_DECORATION_OUTER_CAP_FOOTPRINT
DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION
VIRTUAL_WAVE_MARKED_CORRESPONDENCE
VIRTUAL_WAVE_HORIZON_CERTIFICATE
VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE
UNIVERSAL_PROTECTED_TOWER_CLOSURE
MLC
```

The immediate next constructive node is
`DIRECT_DECORATION_WAVE_PROOF_USE_LEDGER`.  It must be frozen before
stage alignment or any universal proper-end response can be meaningfully
quantified.
