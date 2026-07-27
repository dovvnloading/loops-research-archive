# Research Push V: the physical direct-decoration collar and compact multi-port response

## Status and principal conclusion

This note replaces the idealized equal-footprint collar from Research Push IV by the actual
source object

\[
P\setminus Q_a^\circ .
\]

For the direct-decoration pullbacks of Kahn--Lyubich, the child puzzle piece is attached to
two boundary rays of the parent at one vertex.  The physical set is not literally one closed
quadrilateral: it contains an inactive common-ray attachment skeleton in addition to the
closure of the conducting interior.  After separating those two parts, the active region is a
marked Jordan quadrilateral.  At the next level its outgoing trace footprint and the incoming
footprint of the following cell are generally unequal.  Their common atoms are glued; both
one-sided differences remain side ports; and the overlap of the two inactive attachment arcs
remains nonconducting attachment metadata.

The resulting theorem package gives:

1. an explicit active/inactive decomposition of one physical
   \(P\setminus Q_a^\circ\);
2. a finite ray/equipotential cell decomposition in every source-authorized contact pattern;
3. an exact Boolean decomposition of two successive unequal footprints into common glue,
   two one-sided side-port families, a double-inactive attachment family, and endpoints;
4. compatible Douglas trace spaces that retain endpoint compatibility instead of falsely
   treating adjacent arcs as independent \(H^{1/2}\) coordinates;
5. exact partial-trace composition as a Hilbert-space fiber-product infimum;
6. exact last-use elimination as functorial pushforward of a closed quadratic form;
7. a Grötzsch-type lower bound by the sum of the physical shell resistances;
8. compact multi-port response after the finite live-port frontier is frozen; and
9. an explicit finite accumulated-resistance threshold for any prescribed response error.

The defensible ledger decision is:

\[
\boxed{\texttt{DIRECT\_DECORATION\_TRACE\_COLLAR\_REALIZATION is proved}}
\]

in the source direct-decoration category.  The analytic content of

\[
\boxed{\texttt{END\_PLUMBING\_TRACE\_RESPONSE\_CONTROL}}
\]

is also proved.  Its only remaining dependency is the upstream assertion that the proof has a
finite live common-refinement port frontier (equivalently, the relevant direct-decoration
instance of \(\texttt{VAAPC-I}\) or the complete horizon theorem).  It should therefore no
longer be counted as an independent analytic open gate.

This does **not** prove the universal Wave horizon, global \(\texttt{VAAPC-I}\), the common
mixed-regime H2 response/Value state, MBTT, coercivity, UPTCR, or MLC.

---

# Part I. Source geometry and one physical cell

## 1. Source-backed direct-decoration data

Let \(P\) be the direct-decoration puzzle piece and let \(Q_a\subset P\) be one of the
source univalent pullbacks.  The source supplies:

1. \(P\) and \(Q_a\) are closed Jordan puzzle pieces bounded by finitely many external-ray
   and equipotential arcs;
2. the selected branch \(f^{q_a}:Q_a\to P\) is a conformal homeomorphism; and
3. \(Q_a\) is attached to the two boundary external rays of \(P\) landing at the selected
   vertex.

Let \(A_a=\partial P\cap\partial Q_a\) be the resulting common attachment.  In the ordinary
source configuration, \(A_a\) is the union of two common ray subarcs meeting at the selected
vertex.  It is a topological closed arc with endpoints \(x_a^-\) and \(x_a^+\).

Let \(y_a^-\) and \(y_a^+\) be the parent equipotential endpoints on those two rays.  Define:

- the parent footprint \(\Gamma_a^-\), the arc of \(\partial P\) from \(y_a^-\) to
  \(y_a^+\) avoiding the selected vertex;
- the child footprint \(\Gamma_a^+\), the arc of \(\partial Q_a\) from \(x_a^-\) to
  \(x_a^+\) avoiding the selected vertex; and
- the exposed ray sides
  \[
  S_a^\pm=[x_a^\pm,y_a^\pm]_{\rho_a^\pm}.
  \]

The active boundary curve is

\[
\Gamma_a^-\cup S_a^+\cup\Gamma_a^+\cup S_a^-.
\]

## 2. The physical set has an inactive attachment skeleton

Put

\[
\Omega_a=\operatorname{int}P\setminus Q_a,
\qquad
C_a=\overline{\Omega_a}.
\]

The distinction between \(P\setminus Q_a^\circ\) and \(C_a\) is essential.

### Theorem 2.1 -- Active/inactive physical-cell decomposition

Assume \(P,Q_a\) are nested Jordan disks and their common boundary is the attachment arc
\(A_a\).  Then

\[
\boxed{
P\setminus Q_a^\circ=C_a\cup A_a,
\qquad
C_a\cap A_a=\{x_a^-,x_a^+\}.
}
\tag{2.1}
\]

Moreover:

1. \(C_a\) is a closed Jordan disk;
2. its boundary, in cyclic order, is
   \[
   \Gamma_a^-,\quad S_a^+,\quad\Gamma_a^+,\quad S_a^-;
   \tag{2.2}
   \]
3. the interior of \(A_a\) is not approached from the conducting domain \(\Omega_a\);
4. consequently, \(A_a\) carries no independent Dirichlet-to-Neumann trace of
   \(\Omega_a\); and
5. \(A_a\) remains in the marked state as an inactive attachment/access skeleton.

#### Proof

At an interior point of a common boundary arc, two nested Jordan disks lie on the same side
of that arc.  Since the two Jordan curves agree on a neighborhood of the point, their
interiors agree there.  Hence no point of \(\Omega_a\) approaches the relative interior of
\(A_a\).  The only possible contacts of \(C_a\) with \(A_a\) are its endpoints.

Removing the relative interior of \(A_a\) from \(\partial P\) leaves the arc
\(S_a^-\cup\Gamma_a^-\cup S_a^+\).  Removing it from \(\partial Q_a\) leaves
\(\Gamma_a^+\).  These two residual arcs meet only at \(x_a^-\) and \(x_a^+\), and their
union is a Jordan curve.  It bounds precisely \(C_a\).  Every point of
\(P\setminus Q_a^\circ\) either lies in this regular closed active cell or on the common
attachment arc, proving (2.1).  The trace assertion follows because a boundary trace of the
Dirichlet space is defined only on prime-end boundary approached from \(\Omega_a\).  ∎

### Corollary 2.2 -- The actual physical quadrilateral

There is a prime-end conformal map

\[
\Psi_a:C_a^\circ\longrightarrow(0,R_a)\times(0,1)
\]

sending \(\Gamma_a^-\) and \(\Gamma_a^+\) to the two vertical sides and
\(S_a^-\), \(S_a^+\) to the horizontal sides.  It is unique up to reflection in the
horizontal midline.  The number

\[
R_a=\operatorname{EL}_{C_a}(\Gamma_a^-,\Gamma_a^+)>0
\tag{2.3}
\]

is the physical shell resistance.

No equality of Euclidean lengths, harmonic measures, or trace densities of the two
footprints is asserted.  Their exact normalized trace parameterizations are the two boundary
maps induced by \(\Psi_a\).

## 3. Finite contact overlay

If \(\partial P\cap\partial Q_a\) contains more than the ordinary attachment arc, overlay
the two finite ray/equipotential boundary graphs and subdivide at every vertex and endpoint of
a common subarc.  This gives a finite embedded planar graph.  Every two-dimensional face is
finitely connected; add finitely many disjoint artificial crosscuts to make its components
Jordan cells.  Every artificial crosscut is entered twice as a paired internal trace port.
Exact partial-trace composition below eliminates those paired ports and recovers the response
of the original physical set.

Thus extra contacts do not license a one-cell claim, but they do not obstruct a finite exact
cellular realization.  The first undeclared contact is a failure certificate, not a reason to
replace the physical geometry by an ideal rectangle.

## 4. Pullback naturality

For a finite word \(w\), set

\[
C_{w,a}=\phi_w(C_a)
 =\overline{\operatorname{int}Q_w\setminus Q_{wa}},
\qquad
A_{w,a}=\phi_w(A_a).
\]

The footprints and ray sides are pulled back by \(\phi_w\).  Since \(\phi_w\) is conformal,

\[
\operatorname{EL}_{C_{w,a}}
 (\Gamma_{w,a}^-,\Gamma_{w,a}^+)=R_a,
\tag{4.1}
\]

and every prime-end trace parameterization, attachment label, protected subarc, and cyclic
order transports exactly.  The physical collar is therefore an actual finite-pullback object.

---

# Part II. Two successive unequal footprints

## 5. Attachment-arc Boolean decomposition

Fix an intermediate cylinder \(Q=Q_{wa}\).  Let

- \(A^-\subset\partial Q\) be the inactive attachment arc inherited from the preceding
  cell \(C_{w,a}\); and
- \(A^+\subset\partial Q\) be the inactive attachment arc of the following child
  \(Q_{wab}\subset Q\).

The active outgoing and incoming footprints are

\[
F^{\rm out}=\overline{\partial Q\setminus A^-},
\qquad
F^{\rm in}=\overline{\partial Q\setminus A^+}.
\tag{5.1}
\]

After subdividing at the endpoints of \(A^-\), \(A^+\), and every declared marked subarc,
the relatively open boundary atoms fall into four exact classes:

\[
\begin{aligned}
I&=\partial Q\setminus(A^-\cup A^+) &&\text{common active glue},\\
E^{\rm out}&=A^+\setminus A^- &&\text{outgoing-only side port},\\
E^{\rm in}&=A^-\setminus A^+ &&\text{incoming-only side port},\\
Z&=A^-\cap A^+ &&\text{double-inactive attachment skeleton}.
\end{aligned}
\tag{5.2}
\]

Endpoints form a finite zero-dimensional fifth class \(V\).  Thus

\[
\partial Q=I\sqcup E^{\rm out}\sqcup E^{\rm in}\sqcup Z\sqcup V
\tag{5.3}
\]

as a labeled common refinement.

Only \(I\) is glued.  The two sets \(E^{\rm out}\) and \(E^{\rm in}\) remain physical side
boundary.  The set \(Z\) is inaccessible from both active cells and is retained only as
attachment/access metadata.  This is the exact correction to the equal-footprint model.

## 6. Finite common-refinement atlas

Freeze a finite proof-use horizon.  On every source boundary insert endpoints of:

- all authorized parent and child attachment arcs;
- all intersections and one-sided differences in (5.2);
- every protected crosscut collar read by the proof;
- every obstacle or localization interface read by the proof;
- every response electrode and ideal interval read by the proof; and
- every endpoint required by an authorized presentation or enlargement map.

Let \(\mathscr P=\{J_1,\dots,J_N\}\) be the resulting relatively open boundary atoms,
together with their endpoint labels.  Every footprint, glue, side port, inactive attachment,
and declared observable is a union of named atoms.  Pullback by \(\phi_w\) gives the atlas
\(\mathscr P_w\) on every reached finite cylinder.

### Theorem 6.1 -- Exact physical trace atlas

For every reached word and authorized transition:

1. the conducting gluing trace is a union of common active atoms;
2. every atom active on only one side remains an external side port;
3. every double-inactive atom remains attachment/access metadata and is not inserted into the
   conducting trace space;
4. protected, obstacle, ideal, and response atoms retain their names and cyclic order;
5. pullback and presentation maps act by exact labeled trace isomorphisms; and
6. no equality of the two physical footprint lengths or trace densities is required.

For a source boundary with \(N_\partial\) initial atoms and \(m\) newly declared marked
subarcs, the refined boundary has at most \(N_\partial+2m\) relatively open atoms after
duplicate endpoints are removed.

For the unmarked structural footprint itself, two connected attachment arcs contribute at most
four distinct endpoints.  Hence each ordered symbol pair has at most four open boundary atoms
and four endpoint atoms.  For an alphabet of size \(d\), the depth-independent local structural
type count is therefore at most

\[
8d^2.
\tag{6.1}
\]

An outgoing-only or incoming-only atom that is not explicitly seeded by a future observable has
last use at its birth junction and is eliminated immediately by Theorem 9.1.  Thus unequal
footprints do not by themselves force an unbounded live response dimension; only proof-seeded
side atoms can persist.

---

# Part III. Compatible trace spaces and exact response composition

## 7. The trace space is not a naive direct sum

Adjacent \(H^{1/2}\) boundary arcs sharing endpoints are not independent: endpoint
compatibility is part of the global trace condition.  We therefore use the actual quotient
trace space.

For a marked Jordan cell \(\Omega\) and a finite union \(G\) of active boundary atoms,
define

\[
\mathcal T_\Omega(G)
 =\{\operatorname{Tr}_G u:u\in H^1(\Omega)\}
\tag{7.1}
\]

with the quotient norm

\[
\|\tau\|_{\mathcal T_\Omega(G)}^2
 =\inf_{\operatorname{Tr}_G u=\tau}
   \left(\|u\|_{L^2(\Omega)}^2+\int_\Omega|\nabla u|^2\right).
\tag{7.2}
\]

Equivalently, use the conformally invariant Douglas trace space on the prime-end circle and
then restrict to the named atom union.  The labels are restriction maps from this compatible
space; they are not a declaration that the atom traces form an unconstrained direct sum.

The complete ported response is the closed nonnegative form

\[
q_{\Omega,G}(\tau)
 =\inf_{\operatorname{Tr}_G u=\tau}
   \int_\Omega|\nabla u|^2.
\tag{7.3}
\]

Unlisted active boundary carries the natural Neumann condition.  Constants are retained as the
usual kernel until a quotient or external normalization is declared.

## 8. Exact partial-trace composition

Let two active cells \(\Omega_1,\Omega_2\) have disjoint interiors.  Let \(I\) be the union
of common active atoms, with the same prime-end parameterization on both sides.  Let
\(r_i:\mathcal T_i\to\mathcal T(I)\) be the two restriction maps and let
\(e_i:\mathcal T_i\to X_i\) retain every other live trace label.

### Theorem 8.1 -- Fiber-product response composition

The external response of the physical union is

\[
\boxed{
q(x_1,x_2)=
\inf\left\{
q_1(\tau_1)+q_2(\tau_2):
\begin{array}{l}
r_1\tau_1=r_2\tau_2,\\
e_1\tau_1=x_1,\ e_2\tau_2=x_2
\end{array}
\right\}.
}
\tag{8.1}
\]

The outgoing-only and incoming-only atoms from (5.2) occur among \(x_1,x_2\); they are not
minimized.  If the trace spaces happen to split into separated port coordinates, (8.1) reduces
to the familiar formula

\[
q(x,y)=\inf_h\bigl(q_1(x,h)+q_2(h,y)\bigr).
\tag{8.2}
\]

#### Proof

A finite-energy function on the physical union restricts to functions on the two cells with
the same trace on the actual common active boundary.  Its energy is the sum of the two cell
energies.  Conversely, two finite-energy functions with matching common trace glue to a
finite-energy function on the union.  Taking the joint infimum proves (8.1).  The quotient
trace spaces automatically retain every endpoint compatibility condition.  ∎

### Corollary 8.2 -- Associativity and conformal naturality

Composition is associative, independent of the order of internal-atom elimination, and
commutes with every conformal map preserving the atom labels, cyclic order, and trace
parameterizations.  Artificial crosscuts inserted in the finite contact overlay disappear
exactly after their paired traces are glued.

## 9. Exact last-use elimination

For a continuous linear forgetful map \(p:T\to T_{\rm live}\) between compatible trace
spaces, define the pushforward of a closed nonnegative form by

\[
(p_*q)(y)=\inf_{p\tau=y}q(\tau).
\tag{9.1}
\]

### Theorem 9.1 -- Functorial dead-port elimination

For composable forgetful maps \(T\xrightarrow{p}T_1\xrightarrow{r}T_2\),

\[
\boxed{(r\circ p)_*q=r_*(p_*q).}
\tag{9.2}
\]

Consequently, if a side-port trace is not read by any later transition, response, Value,
access, obstacle, or enlargement observable, it may be forgotten at its last-use stage.  This
commutes exactly with every later physical gluing, even when endpoint compatibility prevents a
naive product decomposition.

#### Proof

Both sides of (9.2) are the infimum of \(q(\tau)\) over the same fiber
\((r\circ p)\tau=z\).  ∎

If at most \(b\) ports are born per stage and every port has future lifetime at most \(L\),
the live non-interface frontier has size at most

\[
b(L+1).
\tag{9.3}
\]

A bounded-lifetime theorem is therefore sufficient; a bound on total historical port count is
not required.

---

# Part IV. Accumulated physical resistance

## 10. Serial shell law

For \(w=a_1\cdots a_m\), put

\[
C_j=
\overline{\operatorname{int}Q_{a_1\cdots a_{j-1}}\setminus
Q_{a_1\cdots a_j}},
\qquad
R_j=R_{a_j}.
\tag{10.1}
\]

The conducting interiors are disjoint.  Every curve from the outer active footprint to the
terminal active footprint contains, in chronological order, a subcurve crossing each active
cell from its parent side to its child side.

### Theorem 10.1 -- Extremal series lower bound

Let \(R(w)\) be the extremal resistance of the selected active tail after every one-sided
footprint piece is retained as boundary and every internal common atom is glued.  Then

\[
\boxed{R(w)\ge\sum_{j=1}^mR_{a_j}.}
\tag{10.2}
\]

For a finite root-cell alphabet,

\[
R_*:=\min_aR_a>0,
\qquad
R(w)\ge mR_*.
\tag{10.3}
\]

#### Proof

For each cell choose an almost extremal metric \(\rho_j\), supported in its conducting
interior and normalized so every parent-to-child crossing has \(\rho_j\)-length at least one.
Its area can be made arbitrarily close to \(1/R_j\).  For positive weights \(c_j\), the metric
\(\rho=\sum_jc_j\rho_j\) gives every complete crossing length at least \(\sum_jc_j\), while
disjoint supports give area arbitrarily close to \(\sum_jc_j^2/R_j\).  Taking \(c_j=R_j\)
yields (10.2).  Positivity of each nondegenerate quadrilateral modulus gives (10.3).  ∎

### Warning 10.2 -- Side-port shortcuts

A later operation that wires side ports from separated levels can bypass part of the serial
chain.  Such a wiring must be included before (10.2) is invoked.  The first undeclared bypass
is a trace-routing failure certificate.

---

# Part V. Compact multi-port response after the live frontier

## 11. Exact prefix and exact physical tail

Freeze the finite proof-use inventory and apply Theorem 9.1 after every last use.  Choose
\(N\) after the last live non-interface side port.  All unequal-footprint transitions and all
surviving ports up to stage \(N\) are contained in one exact compatible response form

\[
q_{\rm L}\quad\text{on}\quad X\times\mathcal H_{\rm in},
\tag{11.1}
\]

where \(X\) denotes the fixed compatible external trace space, not a naive sum of independent
atom spaces.  Let

\[
q_{\rm R}\quad\text{on}\quad\mathcal H_{\rm out}\times Y
\tag{11.2}
\]

be the terminal cap response.

First compose every remaining physical shell by (8.1), eliminating all proof-dead internal
trace atoms.  Select the connected conducting component joining the entrance and exit.  With
all other active boundary natural Neumann, it has one of the following standard prime-end
models:

1. a quadrilateral/strip when the terminal child remains attached to the entrance boundary;
2. an annulus/cylinder when the terminal child is compactly contained; or
3. a finite cell overlay that must be cut into the preceding two models and recomposed by
   (8.1).

In each case the two-interface response of the whole selected tail is the exact full-trace neck
operator \(\mathcal N_R\), where

\[
R\ge\sum_{j=N+1}^mR_{a_j}.
\tag{11.3}
\]

The normalized tangential operator \(A\) has one-dimensional kernel of constants and first
positive eigenvalue \(\lambda_1>0\).  For the width-one Neumann strip,
\(\lambda_1=\pi\); for a unit-circumference cylinder, \(\lambda_1=2\pi\).

The complete response is

\[
q_R(x,y)=
\inf_{\phi,\psi}
\left[
q_{\rm L}(x,\phi)+\mathcal N_R(\phi,\psi)+q_{\rm R}(\psi,y)
\right].
\tag{11.4}
\]

Every unequal footprint and every live side port is still present in \(X\) or \(Y\).  Only
proof-dead variables and actual internal common traces have been eliminated.

## 12. Trace-renormalized long-tail comparison

Write

\[
\mathcal H=\mathbb C\mathbf1\oplus\mathcal H_0.
\]

Let \(\mathcal N_R^\#\) retain the exact scalar resistor \(1/R\) on constants and the two
mean-zero half-cylinder responses \(A\), deleting only the positive-mode transmission across
the long tail.  Put

\[
\eta_A(R)=\frac{2}{e^{\lambda_1R}-1}.
\tag{12.1}
\]

Then

\[
(1-\eta_A(R))\mathcal N_R^\#
\preceq\mathcal N_R
\preceq(1+\eta_A(R))\mathcal N_R^\#.
\tag{12.2}
\]

Addition of the nonnegative cap forms and minimization over the complete trace spaces gives

\[
\boxed{
(1-\eta_A(R))q_R^\#
\preceq q_R
\preceq(1+\eta_A(R))q_R^\#.
}
\tag{12.3}
\]

No finite-electrode approximation and no false equipotential collapse is used.

## 13. Exact scalar internal reduction

Define the half-cylinder-closed cap forms

\[
\widehat q_{\rm L}(x,c)
 =\inf_{\xi\in\mathcal H_0}
 \left[q_{\rm L}(x,c\mathbf1+\xi)+\langle A\xi,\xi\rangle\right],
\tag{13.1}
\]

\[
\widehat q_{\rm R}(d,y)
 =\inf_{\zeta\in\mathcal H_0}
 \left[q_{\rm R}(d\mathbf1+\zeta,y)+\langle A\zeta,\zeta\rangle\right].
\tag{13.2}
\]

Then exactly

\[
\boxed{
q_R^\#(x,y)=
\inf_{c,d\in\mathbb C}
\left[
\widehat q_{\rm L}(x,c)+\frac{|c-d|^2}{R}+\widehat q_{\rm R}(d,y)
\right].
}
\tag{13.3}
\]

All positive trace modes remain in the local cap responses.  Only the exact scalar means are
transmitted through the renormalized tail.

## 14. Compact multi-port tail theorem

Work modulo the one global constant.  Write

\[
\widehat q_{\rm L}(x,c)
 =\langle Lx,x\rangle+2\Re\langle b_{\rm L}x,c\rangle
  +\alpha_{\rm L}|c|^2,
\tag{14.1}
\]

\[
\widehat q_{\rm R}(d,y)
 =\alpha_{\rm R}|d|^2+2\Re\langle b_{\rm R}y,d\rangle
  +\langle Ry,y\rangle.
\tag{14.2}
\]

Positive semidefiniteness implies

\[
\alpha_{\rm L}=0\Longrightarrow b_{\rm L}=0,
\qquad
\alpha_{\rm R}=0\Longrightarrow b_{\rm R}=0.
\tag{14.3}
\]

Let \(B\) bound the external-to-scalar coupling operator and let \(M\) bound
\(\|q_R^\#\|\) on the fixed normalized external trace space.

### Theorem 14.1 -- Compact multi-port response

For a fixed physical prefix and terminal cap, or for finitely many such types supplied by a
frozen branch graph, the exact responses \(q_R\) extend continuously to \(R=\infty\) in the
normalized response-operator norm.  Their image is compact.

If \(\alpha_{\rm L},\alpha_{\rm R}>0\), put

\[
\alpha_*=\min(\alpha_{\rm L},\alpha_{\rm R}).
\]

Then

\[
\boxed{
\|q_R-q_\infty\|
\le
M\frac{2}{e^{\lambda_1R}-1}
+rac{2B^2}{\alpha_*^2R}.
}
\tag{14.4}
\]

If either \(\alpha_{\rm L}=0\) or \(\alpha_{\rm R}=0\), the scalar-resistor correction is
exactly zero and only the first term remains.

#### Proof

The internal scalar matrix is

\[
M_t=
\begin{pmatrix}
\alpha_{\rm L}+t&-t\\
-t&\alpha_{\rm R}+t
\end{pmatrix},
\qquad t=R^{-1}.
\tag{14.5}
\]

When both coefficients are positive, \(M_t\ge\alpha_*I\) and the resolvent identity gives

\[
\|M_t^{-1}-M_0^{-1}\|\le\frac{2t}{\alpha_*^2}.
\tag{14.6}
\]

The scalar Schur complement therefore changes by at most
\(2B^2/(\alpha_*^2R)\).  If, for example, \(\alpha_{\rm L}=0\), then
\(b_{\rm L}=0\), and direct inversion of (14.5) shows that the entry seen by the right
external coupling remains exactly \(1/\alpha_{\rm R}\), independent of \(t\).  The scalar
Schur complement is therefore unchanged.  The same argument covers the other zero cases.

Equation (12.3) contributes at most \(M\eta_A(R)\).  This proves (14.4) and norm
continuity at infinity.  A continuous image of the compact parameter interval
\([R_0,\infty]\) is compact; a finite family of prefix/cap types remains compact.  ∎

### Corollary 14.2 -- Explicit accumulated-resistance threshold

For error at most \(\varepsilon\), when both scalar cap coefficients are positive it is
sufficient that

\[
\boxed{
R\ge
\max\left\{
\frac1{\lambda_1}\log\left(1+\frac{4M}{\varepsilon}\right),
\frac{4B^2}{\alpha_*^2\varepsilon}
\right\}.
}
\tag{14.7}
\]

If one scalar coefficient is zero, omit the second term.  If every remaining shell has
resistance at least \(R_*>0\), a sufficient additional physical depth is the ceiling of the
right side of (14.7) divided by \(R_*\).

## 15. Strict-transition use

There are two legitimate routes.

1. **Exact retention.**  Retain the compact parameterized response \(q_R\).  Then end
   plumbing introduces no approximation error.
2. **Limit replacement.**  Choose \(R\) by (14.7) so that the response perturbation is below
   the error allowance of the downstream calibrated gauge.  If the gauge is Loewner monotone
   and positively homogeneous, the multiplicative estimate (12.3) gives the sharper margin
   transfer from Research Push IV.

The theorem controls the plumbing contribution.  It does not supply the root strict
contraction, Value comparison, or discounted non-plumbing error budget required by MBTT.

---

# Part VI. Gate decisions and ledger consequences

## 16. DIRECT_DECORATION_TRACE_COLLAR_REALIZATION

### Theorem 16.1 -- Physical direct-decoration trace-collar realization

For every source direct-decoration pullback \(Q_a\subset P\):

1. the physical set \(P\setminus Q_a^\circ\) splits into an inactive ray-attachment skeleton
   and a finite active ray/equipotential Jordan-cell complex;
2. in the ordinary source case the active complex is one quadrilateral with actual, generally
   unequal, parent and child trace parameterizations;
3. every declared access, obstacle interface, ideal interval, and response electrode is a
   finite union of common-refinement atoms;
4. two consecutive cells have the exact decomposition (5.2)--(5.3);
5. only common active atoms are glued; both one-sided differences remain side ports;
6. double-inactive atoms remain marked attachment data and are not falsely inserted into the
   DtN trace;
7. composition and artificial-cut removal are exact; and
8. the complete construction transports under every finite inverse word.

Therefore

\[
\boxed{\texttt{DIRECT\_DECORATION\_TRACE\_COLLAR\_REALIZATION is proved}.}
\]

## 17. END_PLUMBING_TRACE_RESPONSE_CONTROL

### Theorem 17.1 -- Corrected end-plumbing theorem

Assume the upstream finite inventory supplies a last live non-interface side-port stage.  Then
the complete physical direct-decoration tail has:

1. an exact fixed compatible multi-port prefix response retaining every unequal footprint and
   every live side port;
2. exact partial-trace composition of all remaining shells;
3. an exact full two-interface trace response with resistance satisfying the serial lower
   bound;
4. exact last-use elimination of all proof-dead ports;
5. a compact response limit as the remaining resistance tends to infinity; and
6. the explicit bound (14.4) and depth rule (14.7).

Thus no independent analytic obligation remains in

\[
\boxed{\texttt{END\_PLUMBING\_TRACE\_RESPONSE\_CONTROL}}
\]

once \(\texttt{VAAPC-I}\), the Wave horizon theorem, or an equivalent source theorem has
supplied the finite live frontier.  The node should be represented as proved with that upstream
dependency, rather than as an additional open analytic gate.

## 18. Direct-decoration trace instance of VAAPC-I

For an already supplied finite direct-decoration branch graph of depth \(H\), let
\(N_0\) be the number of root common-refinement atoms and let \(d\) be the branch alphabet
size.  The unmarked structural transition atlas has at most \(8d^2\) local types, independently
of depth, and every unseeded one-sided atom is eliminated at its birth junction.  Before
dependency closure, the number of all pulled trace-atom copies is at most

\[
N_0\sum_{j=0}^{H}d^j.
\tag{18.1}
\]

Adding the finitely many component, access, obstacle, phase, and response records read by the
fixed graph still gives a finite actual universe.  The manuscript's horizon-first reachability
theorem then gives its unique least frozen inventory.

Hence the **direct-decoration trace-collar portion** of \(\texttt{VAAPC-I}\) is proved for
every already supplied finite source graph.  The global \(\texttt{VAAPC-I}\) node remains
open because the source-faithful complete Wave demand graph and its final horizon are not yet
constructed for every virtual-Molecule block.

---

# Part VII. Failure certificates and remaining path

## 19. Exact failure certificate

A failed application must record the first occurrence of one of:

1. an undeclared extra boundary contact;
2. a common attachment subarc inserted into the conducting trace even though it is inaccessible
   from the active interior;
3. a missing common-refinement endpoint;
4. a claimed glue atom not active from both adjacent cells;
5. a one-sided footprint atom discarded rather than retained as a side port;
6. a double-inactive atom treated as an electrical port;
7. a phase, orientation, or endpoint-compatibility mismatch;
8. a later wiring that shortcuts separated shell levels;
9. infinitely many live side ports after the claimed cutoff;
10. zero shell modulus;
11. failure of the scalar cap normalization needed for the stated rate; or
12. insufficient accumulated resistance for the claimed transition margin.

## 20. Remaining global gates

This push does not prove:

- the universal finite Wave horizon and global \(\texttt{VAAPC-I}\);
- a universal bound, bounded-lifetime law, or future-faithful quotient for the live multi-port
  frontier;
- the common primitive/neutral/virtual response and Value calibration required by H2;
- the root strict contraction, discounted non-plumbing errors, and chart-cycle closure required
  by MBTT;
- geometric coercivity;
- mixed-tower rigidity;
- UPTCR; or
- MLC.

The next irreducible response theorem is now:

> Prove a universal bounded-lifetime law or future-faithful quotient for the live
> common-refinement port frontier, and compare the resulting compact multi-port response
> uniformly with the KKL WAD/Value and neutral sectorial charts.

Once that theorem is available, the physical direct-decoration collar and its end plumbing no
longer contribute an uncontrolled state or error.
