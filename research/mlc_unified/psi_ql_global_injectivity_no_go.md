# Full \(\psi\)-quadratic-like axioms do not imply global injectivity

## 1. Theorem and exact scope

### Theorem 1.1 — abstract \(\psi\)-ql global-injectivity no-go

There is a degree-two \(\psi\)-polynomial-like map

\[
 (i,f):(\mathbf U',K')\longrightarrow(\mathbf U,K)
\]

in the exact sense of Kahn's definition such that:

1. \(\mathbf U'\) and \(\mathbf U\) are disks;
2. \(K\Subset\mathbf U\) is an FJ-set;
3. \(f:\mathbf U'\to\mathbf U\) is a proper holomorphic branched cover of
   degree two;
4. \(i:\mathbf U'\to\mathbf U\) is a holomorphic immersion;
5. the common inverse
   \[
     K'=i^{-1}(K)=f^{-1}(K)
   \]
   is connected;
6. \(i|_{K'}:K'\to K\) is a homeomorphism;
7. the complementary-annulus map
   \[
     i:\mathbf U'\setminus K'\longrightarrow\mathbf U\setminus K
   \]
   induces \(+1\) on fundamental groups; but
8. \(i\) is not injective, even on
   \(\mathbf U'\setminus K'\).

Consequently, neither the proper degree-two companion map nor the common
connected full-continuum pullback axiom upgrades the immersion in an
abstract \(\psi\)-quadratic-like pair to a global embedding.

This theorem is **not** a counterexample to global injectivity of a
particular Kahn--Lyubich immersion produced by canonical dynamical
localization or by the direct-decoration path-space construction.  Those
maps have additional construction history not included in the abstract
\(\psi\)-ql axioms.  The theorem proves that any argument for their global
injectivity must use that additional history, a new global properness or
path-lifting theorem, or a collar-truncated replacement.

`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING`, VAAPC-I, UPTCR, and MLC
remain open.

## 2. Source-locked hypothesis ledger

The relevant sources are:

```text
.tmp_kl06_source/intro.tex
SHA256 E7DD61396FEA927903D4DE4FD386E7AAEFD0BD3E2CEE1CE6F011680AD58144E0

.tmp_kl06_source/psiql2.tex
SHA256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228

.tmp_kl08_source/psiql.tex
SHA256 6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF
```

Kahn's definition is in `psiql2.tex`, lines 16--33.  It requires:

- disks \(\mathbf U'\) and \(\mathbf U\);
- a holomorphic immersion \(i:\mathbf U'\to\mathbf U\);
- a degree-\(d\) branched cover
  \(f:\mathbf U'\to\mathbf U\), used explicitly as proper at line 38;
- an FJ-set \(K\subset\mathbf U\);
- equality \(i^{-1}(K)=f^{-1}(K)=K'\); and
- connectedness of \(K'\).

The FJ-set definition in `intro.tex`, lines 254--255, is: compact,
connected, full, and containing more than one point.

Kahn proves only a polynomial-like restriction: `psiql2.tex`, lines
60--77, states that \(i\) is an embedding on a neighborhood selected near
\(K'\).  The proof at lines 155--178 first obtains local injectivity near
\(K'\), then truncates to an inner annular collar.  It does not assert a
global embedding of \(\mathbf U'\).

Kahn--Lyubich restate the same disk, branched-cover, full-continuum, and
common-inverse clauses in `psiql.tex`, lines 8--15, and import only the
local embedding near \(K'\) at lines 17--24.

The plane case in `psiql2.tex`, lines 43--51, is exceptional: when the
target is the complex plane, removability forces \(i\) to be an
isomorphism.  The construction below uses bounded hyperbolic disks and
therefore does not fall into that case.

## 3. Construction

Put

\[
 R=75,\qquad P=100,\qquad
 \beta=\frac{2\pi}{P}=\frac{\pi}{50},
 \qquad
 \Delta=e^{2\beta}-1.
\tag{3.1}
\]

Define

\[
 \mathbf U'=\mathbb D_R=\{z:|z|<75\},
 \qquad
 \mathbf U=\mathbb D_{R^2}=\{w:|w|<5625\},
\tag{3.2}
\]

\[
 f(z)=z^2,
 \qquad
 K=[0,1],
 \qquad
 K'=[-1,1],
\tag{3.3}
\]

and

\[
 i(z)=\frac{e^{\beta(z+1)}-1}{\Delta}.
\tag{3.4}
\]

Every subsequent claim is verified directly from (3.1)--(3.4).

## 4. Disk and FJ-set clauses

Both \(\mathbb D_{75}\) and \(\mathbb D_{5625}\) are simply connected
plane domains, hence disks.

The intervals \(K=[0,1]\) and \(K'=[-1,1]\) are compact, connected, and
nondegenerate.  A closed line segment does not separate the plane, so its
complement is connected; equivalently, each interval is full.  Thus \(K\)
is an FJ-set, and \(K'\) is also an FJ-set.  Moreover,

\[
 K\Subset\mathbb D_{5625},
 \qquad
 K'\Subset\mathbb D_{75}.
\]

No local-connectivity assertion about a Julia set is used: these continua
are explicit intervals.

## 5. The proper degree-two branch and its exact inverse

The map

\[
 f:\mathbb D_{75}\longrightarrow\mathbb D_{5625},
 \qquad f(z)=z^2,
\]

is onto and has degree two, counted with multiplicity.  Its only critical
point is \(0\), of local degree two, and its only branch value is \(0\in K\).

It is proper.  Indeed, if \(C\Subset\mathbb D_{5625}\), choose
\(r<5625\) with \(C\subset\overline{\mathbb D}_r\).  Then

\[
 f^{-1}(C)\subset\overline{\mathbb D}_{\sqrt r}
 \Subset\mathbb D_{75}.
\]

Since \(f^{-1}(C)\) is closed, it is compact.

Finally,

\[
 z^2\in[0,1]
 \quad\Longleftrightarrow\quad
 z\in[-1,1].
\]

For the forward implication, write \(z=\rho e^{i\theta}\).  The condition
\(z^2\geq0\) forces \(2\theta\equiv0\pmod{2\pi}\), so \(z\) is real; the
upper bound \(z^2\leq1\) then gives \(|z|\leq1\).  Therefore

\[
 f^{-1}(K)=K'.
\tag{5.1}
\]

## 6. The immersion maps the source disk into the target disk

Differentiating (3.4) gives

\[
 i'(z)=\frac{\beta e^{\beta(z+1)}}{\Delta}.
\tag{6.1}
\]

Here \(\beta>0\), \(\Delta>0\), and the exponential never vanishes.
Consequently \(i'(z)\neq0\) throughout \(\mathbf U'\), and \(i\) is a
holomorphic immersion.

We next verify the target containment without numerical approximation.
For \(|z|<75\),

\[
 \Re(z+1)\leq |z|+1<76,
\]

and hence

\[
 |i(z)|
 \leq
 \frac{e^{\beta\Re(z+1)}+1}{e^{2\beta}-1}
 <
 \frac{e^{76\beta}+1}{e^{2\beta}-1}.
\tag{6.2}
\]

We use only the elementary bounds

\[
 3<\pi<\frac{22}{7},
 \qquad e<3,
 \qquad e^x>1+x\quad(x>0).
\tag{6.3}
\]

For completeness, \(e<3\) follows from

\[
 e=2+\sum_{n=2}^{\infty}\frac1{n!}
 <
 2+\sum_{n=2}^{\infty}\frac1{2^{n-1}}
 =3.
\]

The upper Archimedean bound in (6.3) can also be certified by the classical
positive-integral identity

\[
 \frac{22}{7}-\pi
 =
 \int_0^1
 \frac{x^4(1-x)^4}{1+x^2}\,dx
 >0,
\]

while \(3<\pi\) follows from the perimeter of the inscribed regular
hexagon in the unit circle.

Now

\[
 76\beta=\frac{38\pi}{25}
 <
 \frac{38}{25}\frac{22}{7}
 =
 \frac{836}{175}
 <5,
\tag{6.4}
\]

and

\[
 e^{2\beta}-1>2\beta=\frac{\pi}{25}>\frac3{25}.
\tag{6.5}
\]

Substitution in (6.2) gives

\[
 |i(z)|
 <
 \frac{3^5+1}{3/25}
 =
 \frac{6100}{3}
 <2034<5625.
\tag{6.6}
\]

Thus \(i(\mathbf U')\subset\mathbf U\).

## 7. Exact common-inverse equality

Let \(t\in[0,1]\).  By (3.4),

\[
 i(z)=t
 \quad\Longleftrightarrow\quad
 e^{\beta(z+1)}=1+\Delta t.
\tag{7.1}
\]

The right side is positive real and belongs to
\([1,e^{2\beta}]\).  All complex logarithms of that number give

\[
 \beta(z+1)
 =
 \log(1+\Delta t)+2\pi i k,
 \qquad k\in\mathbb Z.
\]

Therefore

\[
 z=
 -1+\frac{\log(1+\Delta t)}{\beta}
 +100ik.
\tag{7.2}
\]

As \(t\) runs through \([0,1]\),

\[
 0\leq\log(1+\Delta t)\leq2\beta,
\]

so the real part in (7.2) runs through \([-1,1]\).  If \(k\neq0\),
then \(|\Im z|\geq100>75\), and \(z\notin\mathbf U'\).  Hence the only
solutions in \(\mathbf U'\) have \(k=0\), and

\[
 i^{-1}(K)=[-1,1]=K'.
\tag{7.3}
\]

Combining (5.1) and (7.3),

\[
 i^{-1}(K)=f^{-1}(K)=K',
\]

and the common inverse is connected.

On the real interval \(K'\), equation (6.1) is positive real.
Moreover,

\[
 i(-1)=0,
 \qquad
 i(1)=\frac{e^{2\beta}-1}{\Delta}=1.
\]

Thus \(i|_{K'}\) is strictly increasing and is a homeomorphism
\(K'\to K\), as Kahn's general theorem predicts.

## 8. The complementary-annulus degree is \(+1\)

Equality of two \(i\)-values has the exact form

\[
 i(z)=i(w)
 \quad\Longleftrightarrow\quad
 e^{\beta(z-w)}=1
 \quad\Longleftrightarrow\quad
 z-w=100ik
\quad(k\in\mathbb Z).
\tag{8.1}
\]

Before using (8.1) for a collision, we verify that the complementary
annulus still has the native degree-one behavior.

Let

\[
 \gamma(\theta)=2e^{i\theta},
 \qquad 0\leq\theta\leq2\pi.
\]

This is a positive generator of
\(\pi_1(\mathbf U'\setminus K')\).  Since
\(i^{-1}(K)=K'\), its image lies in \(\mathbf U\setminus K\).
Compute its winding about \(1/2\in K\).  The solutions of
\(i(z)=1/2\) are

\[
 z=x_0+100ik,
 \qquad
 x_0=
 -1+\frac1\beta
 \log\left(1+\frac{\Delta}{2}\right).
\tag{8.2}
\]

Because

\[
 1<
 1+\frac{\Delta}{2}
 <e^{2\beta},
\]

we have \(-1<x_0<1\).  Thus (8.2) has exactly one solution in
\(\mathbb D_2\), namely the \(k=0\) solution.  It is simple by (6.1).
The argument principle therefore gives

\[
 \operatorname{wind}(i\circ\gamma,1/2)=1.
\tag{8.3}
\]

Hence the induced homomorphism on the two annular fundamental groups sends
the positive generator to the positive generator.  Degree \(+1\) still
does not imply injectivity.

## 9. Exact remote self-collision

Take

\[
 z_+=50i,
 \qquad
 z_-=-50i.
\tag{9.1}
\]

They are distinct, satisfy \(|z_\pm|=50<75\), and are not in
\([-1,1]\).  Moreover,

\[
 \beta(z_+-z_-)
 =
 \frac{\pi}{50}(100i)
 =
 2\pi i.
\]

Equation (8.1) gives

\[
 i(z_+)=i(z_-).
\]

The common value is explicit:

\[
 i(z_\pm)
 =
 \frac{-e^\beta-1}{\Delta}<0.
\tag{9.2}
\]

By Section 6 it lies in \(\mathbf U\), and since \(K=[0,1]\), (9.2)
lies in \(\mathbf U\setminus K\).  Thus

\[
 i:\mathbf U'\setminus K'\longrightarrow\mathbf U\setminus K
\]

has a genuine self-collision.

## 10. Compatibility with the local-embedding theorem

The example does not contradict Kahn's local theorem.  By (8.1), every
nontrivial collision has imaginary displacement at least \(100\).
Consequently \(i\) is injective on every set of imaginary diameter less
than \(100\), including a sufficiently small neighborhood of
\([-1,1]\).  The local polynomial-like restriction and the inner-collar
embedding therefore remain valid.

What fails is precisely the unsupported passage from this local collar to
the entire complementary annulus.

## 11. Adversarial audit

### 11.1 Not merely an immersion-only example

The example includes the proper degree-two companion \(f(z)=z^2\), not
just an unrelated noninjective disk immersion.

### 11.2 Exact common inverse, not coarse image agreement

Section 7 enumerates every logarithmic sheet.  The period \(P=100\) and
source radius \(75\) exclude all nonzero sheets from the preimage of
\([0,1]\).  The collision occurs halfway between adjacent real-positive
sheets and therefore does not create a hidden second component of \(K'\).

### 11.3 The collision is outside the protected continuum

Both source points lie outside \(K'\), and their common value is negative,
hence outside \(K\).  This is a collision of the actual complementary
annulus map, not a collision absorbed by the filled set.

### 11.4 The annular degree remains one

Section 8 uses the argument principle rather than inferring degree from a
label.  Thus the example survives the degree-one condition used in the
tile/base reduction.

### 11.5 No critical point is hidden

Equation (6.1) is everywhere nonzero.  The self-collision is caused by
exponential periodicity, not branching of \(i\).

### 11.6 Properness is assigned to the correct arrow

The map \(f\) is proper.  The immersion \(i\) is not proper on the whole
complementary annulus, and the \(\psi\)-ql definition does not require it
to be.  Reassigning the properness of \(f\) to \(i\) would conflate the two
arrows.

### 11.7 Abstract pair versus actual KL path-space stage

The theorem refutes a deduction from the complete abstract \(\psi\)-ql
axioms.  It does not prove that the specific Kahn--Lyubich inclusion
immersion constructed from nested puzzle/path spaces has a collision.  A
theorem about that actual map must use its path-space construction and
must prove one of:

- global base-annulus injectivity;
- full properness;
- complete path and homotopy lifting; or
- an equivalent no-return-to-an-old-sheet statement.

Absent such a theorem, only Kahn's certified inner collar may be treated as
embedded.

## 12. Consequence for the project

The abstract whole-annulus upgrade is closed negatively:

\[
 \boxed{
 \text{full abstract \(\psi\)-ql axioms}
 \;\not\Longrightarrow\;
 \text{global injectivity of \(i\)}
 }.
\]

The remaining direct-decoration gate is narrower and more geometric:
prove global univalence for the **actual** KL path-space/localization
immersion, or replace the full pseudo-piece by the embedded inner collars
and record every path that exits them in a bounded defect ledger.

No global MLC obligation is promoted.
