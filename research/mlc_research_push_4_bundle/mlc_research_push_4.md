# Research Push IV: full trace-response plumbing and the exact equipotential-collapse criterion

## Status and principal conclusion

This note attacks the gate

\[
\texttt{END\_PLUMBING\_TRACE\_RESPONSE\_CONTROL}.
\]

The finite-edge plumbing model from Research Push III did not control arbitrary
Sobolev traces on the equipotential cross-sections. A long planar neck is not,
in general, a single scalar resistor. It has one constant channel and infinitely
many angular channels. The angular self-response does not vanish as the neck
length tends to infinity.

The correction is favorable rather than destructive:

1. the full Dirichlet-to-Neumann trace response of every ray/equipotential neck
   is explicit;
2. serial necks form an exact response semigroup;
3. the complete operator is determined by one scalar resistance, one marked
   interface phase, and a universal tangential operator;
4. after retaining the two half-cylinder trace responses and the exact constant
   resistor, the remaining coupling is exponentially small;
5. the estimate survives arbitrary Hilbert-space Schur-complement gluing;
6. the complete family has a compact operator limit as the tail grows;
7. any strict Loewner-monotone response transition survives after an explicit
   finite depth choice; and
8. exact scalar equipotential collapse holds precisely when every admissible
   interface trace is constant.

Thus the end-plumbing trace-response gate closes for the source-authorized
ray/equipotential collars of the direct-decoration system. This does not close
the global response-realization theorem, MBTT, geometric coercivity, mixed
rigidity, or MLC.

---

# Part I. Correction of the scalar plumbing model

## 1. Why finite conductance edges are not the full continuum neck

A finite conductance edge has one degree of freedom at each endpoint. Replacing
an equipotential cross-section by one graph vertex therefore assumes that the
cross-section is electrically shorted: every admissible potential is constant
along it.

A geometric Böttcher equipotential is only a level set of the dynamical Green
function. It does not force an unrelated harmonic function used in a response
or extremal-energy problem to be constant along that curve.

Consequently, the numerical graph audit in Research Push III validated the
single-edge model only after an equipotential-collapse hypothesis. It did not
validate the full boundary trace response of the planar neck.

## 2. Exact scalar-collapse counterexample

Let

\[
C_R=(0,R)\times(0,1)
\]

with Neumann conditions on the side walls \(y=0,1\). Prescribe traces

\[
f(y)=\sqrt2\cos(\pi y),\qquad g(y)=0
\]

on the left and right cross-sections. Both traces have mean zero.

The harmonic extension is

\[
u(x,y)=
\frac{\sinh(\pi(R-x))}{\sinh(\pi R)}\sqrt2\cos(\pi y),
\]

and its energy is

\[
\mathcal E_R(f,0)=\pi\coth(\pi R).
\tag{2.1}
\]

Hence

\[
\mathcal E_R(f,0)\longrightarrow\pi
\quad(R\to\infty).
\]

A scalar model retaining only the two trace averages assigns energy zero.
Therefore no full-trace estimate of the form

\[
\mathcal E_R(f,g)
\le \frac{C}{R}\,\operatorname{osc}(f,g)^2
\]

can hold for arbitrary admissible traces.

### Correction decision

The Push III node `ADAPTIVE_NODAL_RESPONSE_APPROXIMATION` must be replaced by
one of the following two statements:

- **shorted version:** every plumbing cross-section is a declared single
  electrical electrode, so only constant traces are admissible; or
- **full-trace version:** retain the complete Dirichlet-to-Neumann trace form
  and use the operator theorem below.

The second route is stronger and is developed here.

---

# Part II. Source-compatible trace collars

## 3. Canonical Böttcher rectangle

Let \(f\) be a quadratic polynomial with connected filled Julia set, and let
\(\Phi\) be its Böttcher coordinate in the basin of infinity. Write

\[
G(z)=\log|\Phi(z)|,
\qquad
\Theta(z)=\frac{1}{2\pi}\arg\Phi(z)\pmod1.
\]

A closed external sector bounded by two rays
\(\Theta=\theta_0,\theta_1\) and two equipotentials
\(G=t_-,t_+\), with \(t_-<t_+\), is mapped by

\[
(x,y)=
\left(
\frac{G-t_-}{2\pi(\theta_1-\theta_0)},
\frac{\Theta-\theta_0}{\theta_1-\theta_0}
\right)
\]

to the marked rectangle

\[
(0,R)\times(0,1),
\qquad
R=\frac{t_+-t_-}{2\pi(\theta_1-\theta_0)}.
\tag{3.1}
\]

The horizontal coordinate is the normalized potential direction, and the
vertical coordinate is normalized external angle. Dirichlet energy is
unchanged by this conformal coordinate.

## 4. Trace-compatible pullback chain

For an actual univalent branch of \(f^q\) in the external sector,

\[
G(f^qz)=2^qG(z),
\qquad
\Theta(f^qz)=2^q\Theta(z)\pmod1.
\tag{4.1}
\]

Thus an inverse branch scales the potential thickness and angular width by the
same factor. The normalized coordinate \(y\) is preserved, up to the marked
phase determined by the selected inverse branch.

Choose one parent equipotential cross-section \(\gamma\) and set

\[
\gamma_w=\phi_w(\gamma)
\]

for every finite address. Let \(C_{w,a}\) be the full ray/equipotential sector
between \(\gamma_w\) and \(\gamma_{wa}\). Then:

1. \(C_{w,a}\) is marked-conformally a rectangle of width one and length
   \(R_a>0\);
2. the child trace parameterization of \(C_{w,a}\) equals the parent trace
   parameterization of \(C_{wa,b}\);
3. a tail \(a_1\cdots a_m\) is marked-conformally a rectangle of length

   \[
   R(a_1\cdots a_m)=\sum_{j=1}^m R_{a_j};
   \tag{4.2}
   \]

4. the only extra interface datum is the exact external-angle phase; and
5. the construction is natural under every certified univalent presentation
   and root enlargement that retains the collar.

This is the required **trace-compatible external collar atlas**. A claimed
application must still verify that protected collars, obstacles, and
localization boundaries do not cut across the selected external sector.

---

# Part III. The exact full trace response

## 5. Trace Hilbert space

Let

\[
I=(0,1)
\]

and let

\[
\varphi_0(y)=1,
\qquad
\varphi_n(y)=\sqrt2\cos(n\pi y),\quad n\ge1,
\]

be the Neumann eigenbasis. Put

\[
A=\sqrt{-\partial_y^2{}_N},
\qquad
A\varphi_0=0,
\qquad
A\varphi_n=n\pi\varphi_n.
\tag{5.1}
\]

Let \(P_0\) be projection onto constants and \(Q=1-P_0\). The normalized trace
space is

\[
\mathcal H=H^{1/2}_N(I),
\]

with norm

\[
\|f\|_{\mathcal H}^2
=|f_0|^2+\langle Af,f\rangle
=|f_0|^2+\sum_{n\ge1}n\pi|f_n|^2.
\tag{5.2}
\]

The full response is most naturally regarded as a quadratic form on
\(\mathcal H\oplus\mathcal H\), rather than as a matrix after an arbitrary
finite electrode quotient.

## 6. Exact rectangle Dirichlet-to-Neumann theorem

### Theorem 6.1 - Full trace formula

For \(f,g\in\mathcal H\), let \(u\) be the energy-minimizing harmonic function
on \(C_R\) with end traces \(f,g\) and natural Neumann conditions on the side
walls. Then

\[
\begin{aligned}
\mathcal E_R(f,g)
={}&\frac{|f_0-g_0|^2}{R}\\
&+\sum_{n\ge1}n\pi
\left[
\coth(n\pi R)(|f_n|^2+|g_n|^2)
-2\operatorname{csch}(n\pi R)\Re(f_n\overline{g_n})
\right].
\end{aligned}
\tag{6.1}
\]

Equivalently, the Dirichlet-to-Neumann operator is

\[
\mathcal N_R=
\begin{pmatrix}
\alpha_R(A)&-\beta_R(A)\\
-\beta_R(A)&\alpha_R(A)
\end{pmatrix},
\tag{6.2}
\]

where

\[
\alpha_R(\lambda)=\lambda\coth(R\lambda),
\qquad
\beta_R(\lambda)=\lambda\operatorname{csch}(R\lambda),
\tag{6.3}
\]

and the continuous values at \(\lambda=0\) are

\[
\alpha_R(0)=\beta_R(0)=R^{-1}.
\tag{6.4}
\]

#### Proof

Expand \(f,g,u\) in the basis \(\varphi_n\). For \(n=0\), the minimizing mode
is linear in \(x\), with energy \(|f_0-g_0|^2/R\). For \(n\ge1\), the unique
mode is

\[
u_n(x)=
\frac{\sinh(n\pi(R-x))}{\sinh(n\pi R)}f_n
+
\frac{\sinh(n\pi x)}{\sinh(n\pi R)}g_n.
\]

Green's identity, or direct integration, gives the summand in (6.1). Orthogonality
of the modes completes the proof. \(\square\)

### Proposition 6.2 - Marked phase

Suppose the right cross-section is identified with the normalized left trace
coordinate by a unitary map \(U\) commuting with \(A\) and preserving constants.
Then the exact operator is

\[
\mathcal N_{R,U}=
\begin{pmatrix}
\alpha_R(A)&-\beta_R(A)U\\
-U^*\beta_R(A)&U^*\alpha_R(A)U
\end{pmatrix}.
\tag{6.5}
\]

For external-angle rotations on a circular trace and the identity/reflection
markings on an interval trace, this is the complete phase dependence. Serial
gluing multiplies the phases. For every \(R_0>0\), the family with
\(R\in[R_0,\infty]\) and phase in the compact marking group is compact in
the normalized trace-operator norm. Indeed, the diagonal part is phase
independent and the phase-dependent off-diagonal operator
\(A\operatorname{csch}(RA)U\) is smoothing; strong continuity of the compact
phase action becomes norm continuity after composition with that compact
operator.

### Circle and other side conditions

For a full annular neck, replace the Neumann interval operator by
\(|D|=\sqrt{-\partial_\theta^2}\) on the circle. For a sector whose side walls
carry a different self-adjoint condition, replace \(A\) by the positive square
root of the corresponding tangential Laplacian. The formulas below use only:

- a finite-dimensional kernel \(\ker A\);
- a first positive eigenvalue \(\lambda_1>0\); and
- the functional calculus of \(A\).

## 7. Exact response semigroup

### Theorem 7.1 - Concatenation law

If two trace-compatible rectangles of lengths \(R,S\) are glued along their
common parameterized cross-section, then

\[
\boxed{
\mathcal N_R\star\mathcal N_S=\mathcal N_{R+S},
}
\tag{7.1}
\]

where \(\star\) means addition of the two energy forms followed by minimization
over the common trace.

#### Proof

The glued surface is the rectangle \((0,R+S)\times(0,1)\). Restricting its
harmonic minimizer to the two subrectangles gives the minimizing interface
trace. Conversely, gluing two minimizing harmonic functions with a common
trace gives an admissible function on the long rectangle. The two variational
problems are identical. \(\square\)

### Consequence

A tail of many puzzle cells does not require storing one response operator per
cell. Its complete full trace response is exactly the single operator

\[
\mathcal N_{\sum_jR_j}.
\tag{7.2}
\]

Thus the full infinite-dimensional response is encoded by:

- the scalar total resistance \(R\);
- the fixed universal tangential operator \(A\); and
- the exact marked phase/orientation, which commutes with \(A\) in the
  Böttcher trace coordinate.

---

# Part IV. Exact equipotential collapse and its obstruction

## 8. The constant channel

Restricting (6.1) to constant traces gives

\[
\mathcal E_R(a,b)=\frac{|a-b|^2}{R}.
\tag{8.1}
\]

Hence the zero mode is exactly the scalar resistor of conductance \(1/R\).
There is no approximation in this channel.

## 9. Exact criterion

### Theorem 9.1 - Exact mean-collapse criterion

Let \(V\subset\mathcal H\) be a linear admissible trace subspace and let

\[
M:V\longrightarrow\mathbb C,
\qquad
M(f)=f_0,
\]

be the trace-mean map. The restriction of \(\mathcal E_R\) to
\(V\oplus V\) factors through the two means—that is, there is a quadratic form
\(q_R\) on \(M(V)\oplus M(V)\) satisfying

\[
\mathcal E_R(f,g)=q_R(Mf,Mg)
\quad(f,g\in V)
\tag{9.1}
\]

if and only if \(M|_V\) is injective.

If, in addition, constants are admissible (\(\mathbb C\varphi_0\subset V\)),
then this is equivalent to

\[
V=\mathbb C\varphi_0=\ker A.
\tag{9.2}
\]

The same conclusion holds under the weaker mean-subtraction condition
\(f-M(f)\varphi_0\in V\) for every \(f\in V\).

#### Proof

If (9.1) holds and \(f\in\ker(M|_V)\), then

\[
\mathcal E_R(f,0)=q_R(0,0)=\mathcal E_R(0,0)=0.
\]

Formula (6.1) gives

\[
\mathcal E_R(f,0)
=\sum_{n\ge1}n\pi\coth(n\pi R)|f_n|^2,
\]

so \(f=0\). Hence \(M|_V\) is injective. Conversely, if \(M|_V\) is
injective, every \(a\in M(V)\) has a unique representative
\(f_a\in V\); defining \(q_R(a,b)=\mathcal E_R(f_a,f_b)\) proves the
factorization.

If constants belong to \(V\), then for every \(f\in V\) the vector
\(f-M(f)\varphi_0\) lies in \(V\) and has zero mean. Injectivity forces it to
vanish, so \(f\) is constant. The same argument uses only the stated
mean-subtraction condition. \(\square\)

### Remark 9.2 - The one-dimensional shape exception

Without constant admissibility or mean-subtraction invariance, a nonconstant
one-dimensional space such as \(V=\operatorname{span}\{\varphi_0+\varphi_1\}\)
has injective mean map, so its response can formally be encoded by one scalar.
This is not equipotential shorting: the scalar determines one fixed nonconstant
shape. A claim that a geometric cross-section is one electrical electrode must
therefore verify the constant-trace condition, not merely one-dimensionality.

### Corollary 9.3 - Exact shorted-electrode collapse

If every cross-section is declared one perfect electrical electrode, so that
admissible traces are constant by definition, the full neck response is exactly
the one-edge conductance \(1/R\).

### Warning 9.4

Calling a curve a dynamical or Böttcher equipotential does not verify the
hypothesis of Corollary 9.2. Exact collapse is an electrical boundary condition
or a proved trace-invariance statement, not a geometric name.

---

# Part V. Trace-renormalized nodal response

## 10. The correct nodal model

The full response of a semi-infinite rectangle on a mean-zero trace is

\[
\langle Af,f\rangle.
\tag{10.1}
\]

Constants extend with zero energy. Therefore the correct long-neck
normalization is not the bare cut surface. It is the cut surface with one
semi-infinite cylindrical end on each side, together with the exact scalar
resistor joining the two constant modes.

Define

\[
\begin{aligned}
\mathcal E_R^{\#}(f,g)
={}&\frac{|f_0-g_0|^2}{R}
+\langle Af,f\rangle+\langle Ag,g\rangle.
\end{aligned}
\tag{10.2}
\]

Its operator is

\[
\mathcal N_R^{\#}=
\begin{pmatrix}
A+R^{-1}P_0&-R^{-1}P_0\\
-R^{-1}P_0&A+R^{-1}P_0
\end{pmatrix}.
\tag{10.3}
\]

## 11. Sharp exponential trace estimate

### Theorem 11.1 - Full trace-response control

Put

\[
\eta(R)=\frac{2}{e^{\pi R}-1}.
\tag{11.1}
\]

Then

\[
\left|
\mathcal E_R(f,g)-\mathcal E_R^{\#}(f,g)
\right|
\le
\eta(R)
\left(
\langle Af,f\rangle+\langle Ag,g\rangle
\right).
\tag{11.2}
\]

Consequently, whenever \(\eta(R)<1\),

\[
\boxed{
(1-\eta(R))\mathcal N_R^{\#}
\preceq
\mathcal N_R
\preceq
(1+\eta(R))\mathcal N_R^{\#}.
}
\tag{11.3}
\]

The constant \(\eta(R)\) is sharp for the normalized modewise operator bound.

#### Proof

For \(t=n\pi R\), subtracting the two mode forms produces the matrix

\[
M_t=
\begin{pmatrix}
\coth t-1&-\operatorname{csch}t\\
-\operatorname{csch}t&\coth t-1
\end{pmatrix}.
\]

Its eigenvalues are

\[
\frac{2}{e^t-1},
\qquad
-\frac{2}{e^t+1}.
\tag{11.4}
\]

Their largest absolute value is \(2/(e^t-1)\), maximized at the first mode
\(n=1\). The constant mode agrees exactly in \(\mathcal E_R\) and
\(\mathcal E_R^{\#}\). Summing the orthogonal modes proves (11.2). Since the
mean-zero half-cylinder energy is bounded above by \(\mathcal E_R^{\#}\),
(11.3) follows. \(\square\)

### General spectral form

For tangential spectral gap \(\lambda_1\), replace (11.1) by

\[
\eta_{\lambda_1}(R)=\frac{2}{e^{\lambda_1R}-1}.
\tag{11.5}
\]

## 12. Adaptive depth

To guarantee a prescribed relative trace error \(0<\delta<1\), it suffices that

\[
R\ge
\frac1\pi\log\left(1+\frac2\delta\right).
\tag{12.1}
\]

For a tail whose cells satisfy \(R_j\ge R_*>0\), it suffices to choose

\[
\ell\ge
\left\lceil
\frac{1}{\pi R_*}
\log\left(1+\frac2\delta\right)
\right\rceil.
\tag{12.2}
\]

The depth grows logarithmically in \(1/\delta\). No universal lower bound on a
single-cell resistance is needed: a small positive \(R_*\) is paid for by a
longer finite tail.

---

# Part VI. Compactness of the complete trace operator

## 13. Cylindrical-end limit

Define

\[
\mathcal N_\infty=
\begin{pmatrix}A&0\\0&A\end{pmatrix},
\tag{13.1}
\]

with \(A\) vanishing on constants. This is the response of two independent
semi-infinite ends.

### Theorem 13.1 - Operator-norm compactification

In the normalized \(\mathcal H\oplus\mathcal H\to
(\mathcal H\oplus\mathcal H)^*\) norm,

\[
\left\|
\mathcal N_R-\mathcal N_\infty
\right\|
\le
\max\left\{
\frac2R,
\frac{2}{e^{\pi R}-1}
\right\}.
\tag{13.2}
\]

Hence

\[
\mathcal N_R\longrightarrow\mathcal N_\infty
\quad\text{in operator norm}.
\tag{13.3}
\]

The map \(R\mapsto\mathcal N_R\) extends continuously to the compactified
parameter interval \([R_0,\infty]\).

#### Proof

On the constant two-dimensional block, the difference from the limit has
matrix \(R^{-1}\bigl(\begin{smallmatrix}1&-1\\-1&1\end{smallmatrix}\bigr)\),
whose norm is \(2/R\). On the mean-zero block, Theorem 11.1 gives the second
bound. The blocks are orthogonal. \(\square\)

### Consequence for the marked state

End plumbing introduces no arbitrary escaping infinite-dimensional operator.
In the canonical trace coordinate, the whole full-trace family is a compact,
one-parameter operator family. The root-side joint trace response is transported
exactly; only \(R\) and the marked phase change along the address tail.

---

# Part VII. Hilbert-space response gluing

## 14. Variational Schur complement

Let \(E\) be a finite external terminal space and \(\mathcal H_\Gamma\) a
Hilbert trace space. Let

\[
Q(x,\phi)\ge0
\]

be the closed component energy form for external data \(x\in E\) and interface
trace \(\phi\in\mathcal H_\Gamma\). Given a neck form \(N(\phi)\), define the
external response by

\[
q_N(x)=\inf_\phi\{Q(x,\phi)+N(\phi)\}.
\tag{14.1}
\]

This is the Hilbert-space Schur complement. It reduces to the usual matrix
Schur complement after a finite trace discretization, but no discretization is
part of the theorem.

### Lemma 14.1 - Order and relative bounds survive elimination

If

\[
(1-\delta)N_0\preceq N_1\preceq(1+\delta)N_0,
\qquad 0\le\delta<1,
\tag{14.2}
\]

then

\[
(1-\delta)q_{N_0}
\le q_{N_1}
\le(1+\delta)q_{N_0}.
\tag{14.3}
\]

#### Proof

Since \(Q\ge0\),

\[
(1-\delta)(Q+N_0)
\le Q+N_1
\le(1+\delta)(Q+N_0).
\]

Take the infimum over the same trace space. \(\square\)

## 15. Multiple end necks

Let \(R_1,\ldots,R_s\) be pairwise disjoint trace-compatible tails and put

\[
\eta_*=
\max_i\frac{2}{e^{\pi R_i}-1}.
\tag{15.1}
\]

Let \(\Lambda_{\mathrm{phys}}\) be the external response after gluing the exact
full necks \(\mathcal N_{R_i}\), and let \(\Lambda_{\#}\) be the response after
using \(\mathcal N_{R_i}^{\#}\).

### Theorem 15.1 - Full physical response comparison

On the quotient by global constants,

\[
\boxed{
(1-\eta_*)\Lambda_{\#}
\preceq
\Lambda_{\mathrm{phys}}
\preceq
(1+\eta_*)\Lambda_{\#}.
}
\tag{15.2}
\]

#### Proof

Sum Theorem 11.1 over the disjoint necks, add the nonnegative component energy,
and apply Lemma 14.1. \(\square\)

### Finite-electrode corollary

For any fixed finite trace-to-electrode map \(J\),

\[
(1-\eta_*)J^*\Lambda_{\#}J
\preceq
J^*\Lambda_{\mathrm{phys}}J
\preceq
(1+\eta_*)J^*\Lambda_{\#}J.
\tag{15.3}
\]

Thus finite-electrode response is safe as a **compression of the full trace
theorem**. It is not a substitute for proving that the discarded trace modes
are absent.

---

# Part VIII. Transfer of a strict response transition

## 16. Monotone homogeneous gauges

Let \(L\) be a nonnegative gauge on positive response forms satisfying:

1. positive homogeneity;
2. Loewner monotonicity.

Then (15.2) gives

\[
(1-\eta_*)L(\Lambda_{\#})
\le
L(\Lambda_{\mathrm{phys}})
\le
(1+\eta_*)L(\Lambda_{\#}).
\tag{16.1}
\]

## 17. Strictness survives

Suppose the trace-renormalized normalized block satisfies

\[
L_{\#}^{\mathrm{out}}
\le
\mu L_{\#}^{\mathrm{in}}+E,
\qquad 0<\mu<1.
\tag{17.1}
\]

If the input and output plumbing tails have relative errors at most \(\eta\),
then

\[
L_{\mathrm{phys}}^{\mathrm{out}}
\le
\mu_{\mathrm{eff}}
L_{\mathrm{phys}}^{\mathrm{in}}
+(1+\eta)E,
\tag{17.2}
\]

where

\[
\mu_{\mathrm{eff}}
=\mu\frac{1+\eta}{1-\eta}.
\tag{17.3}
\]

Hence strict contraction survives whenever

\[
\eta<\frac{1-\mu}{1+\mu}.
\tag{17.4}
\]

Equivalently, if the root backward factor is \(\lambda=\mu^{-1}>1\), the
materialized factor is

\[
\lambda_{\mathrm{eff}}
=\lambda\frac{1-\eta}{1+\eta}>1
\tag{17.5}
\]

whenever

\[
\eta<\frac{\lambda-1}{\lambda+1}.
\tag{17.6}
\]

Combined with (12.1), this gives an explicit finite materialization depth that
preserves the MBTT margin.

### Exact-retention alternative

If the state retains \(\mathcal N_R\) itself through the one-parameter
functional calculus (6.2), there is no plumbing approximation error at all.
The estimate above is needed only when replacing the finite neck by its compact
trace-renormalized nodal model.

---

# Part IX. Gate closure

## 18. The end-plumbing theorem

### Theorem 18.1 - END_PLUMBING_TRACE_RESPONSE_CONTROL

For every source-authorized direct-decoration address tail whose external
ray/equipotential sectors remain inside the authorized localization and avoid
all protected collars and obstacles:

1. the nested cells carry a canonical trace-compatible Böttcher rectangle
   atlas;
2. their full Dirichlet-to-Neumann trace response concatenates exactly;
3. the complete tail response is the universal operator \(\mathcal N_R\),
   determined by total resistance, marked phase, and the fixed tangential
   operator;
4. the family extends compactly to the infinite-tail operator
   \(\mathcal N_\infty\);
5. the trace-renormalized nodal model controls the physical response by the
   sharp relative factor \(\eta(R)=2/(e^{\pi R}-1)\);
6. all finite-electrode compressions and Loewner-monotone homogeneous gauges
   inherit the same comparison after arbitrary component elimination;
7. a source strict response transition retains a strict margin after an
   explicit finite depth choice; and
8. exact scalar equipotential collapse is used only when the admissible trace
   space is proved to consist of constants.

Therefore the direct-decoration end-plumbing trace-response gate is proved.

## 19. What remains open

This theorem does not prove:

- that every mixed virtual-Molecule block supplies an external collar avoiding
  all future protected data;
- a universally bounded external terminal, WAD, or Value dimension;
- a common response realization across every KKL, neutral, and virtual chart;
- the source trichotomy and discounted error charge for every mixed block;
- MBTT;
- geometric coercivity;
- mixed-tower rigidity; or
- MLC.

The global node `H2_RESPONSE_REALIZATION` remains open. Its end-plumbing
subproblem is now replaced by the exact operator theorem above.

---

# Part X. Ledger revision

## 20. Required correction

Withdraw or relabel the Push III node

\[
\texttt{ADAPTIVE\_NODAL\_RESPONSE\_APPROXIMATION}
\]

as

\[
\texttt{SHORTED\_EQUIPOTENTIAL\_NODAL\_RESPONSE},
\]

with the explicit hypothesis that every cut cross-section is one electrical
electrode.

Any dependent theorem that used an arbitrary additive scalar plumbing error
must instead depend on `END_PLUMBING_TRACE_RESPONSE_CONTROL` and use either:

- exact full-operator retention; or
- the multiplicative trace-renormalized estimate.

## 21. New proved nodes

The following nodes are supported by this note:

1. `BOTTCHER_TRACE_COLLAR_ATLAS`;
2. `FULL_TRACE_RECTANGLE_DTN`;
3. `TRACE_RESPONSE_SEMIGROUP`;
4. `EQUIPOTENTIAL_COLLAPSE_CRITERION`;
5. `TRACE_RENORMALIZED_NECK_ESTIMATE`;
6. `END_TRACE_RESPONSE_COMPACTIFICATION`;
7. `HILBERT_TRACE_GLUE_CALCULUS`;
8. `TRACE_STABLE_STRICT_TRANSITION_TRANSFER`; and
9. `END_PLUMBING_TRACE_RESPONSE_CONTROL`.

## 22. Failure certificate

A failed application must identify the first occurrence of one of:

- missing parent or child equipotential cross-section;
- missing protected side wall;
- obstacle or collar crossing the external sector;
- nonmatching trace parameterizations at a glued interface;
- an interface phase not retained in the marked state;
- an asserted scalar collapse with a nonconstant admissible trace;
- insufficient accumulated resistance for the claimed relative margin;
- a downstream gauge that is neither exact-response based nor Loewner
  monotone; or
- failure of the component trace form to transport under the certified
  presentation map.

---

# Part XI. Next critical target

The next larger response theorem is:

## Universal trace-interface authorization and bounded future response

For every mixed virtual-Molecule block, construct before the stopping execution:

1. the complete family of source-authorized trace collars and interface phases;
2. the exact root component joint response forms on external terminals and
   trace cross-sections;
3. protected enlargement maps acting continuously on those forms;
4. a future-complete finite external terminal and Value-feature quotient, or a
   uniformly controlled compact operator state;
5. chart comparisons placing KKL, neutral, and virtual response forms in one
   calibrated Loewner gauge; and
6. a complete block transition whose strict margin dominates all remaining
   non-plumbing errors.

The present theorem removes the end neck itself from that list of unknowns. It
also gives the exact margin formula needed to keep a future MBTT transition
strict.

---

# Computational audit

The companion script `full_trace_plumbing_audit.py` checks 500 randomized
finite Fourier/Schur-complement models. It verifies, to floating-point error:

- the sharp relative constant \(2/(e^{\pi R}-1)\);
- the exact response semigroup;
- preservation of the multiplicative estimate under random component
  elimination;
- compact convergence to the half-cylinder limit; and
- the mean-zero counterexample to scalar collapse.

The computation is a falsification test. The proof is the mode formula and the
variational arguments above.
