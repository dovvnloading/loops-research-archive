# Finite-cylinder commuting-iterate lift

## 1. Status and purpose

This note proves the algebraic-analytic lift that is available before the
second virtual marking is constructed.

- `FINITE_CYLINDER_COMMUTING_ITERATE_LIFT`: **proved**.
- `VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR`: **open**.
- `VIRTUAL_DISCONNECTED_MARKING_TRANSFER`: **open**.
- UPTCR and MLC: **open**.

The proved statement says that once a target cylinder has been selected,
the lifted formula is forced by commutation of polynomial iterates.  It does
not select that target cylinder.  Fixed-base word uniqueness is formal once
the image is contained in a finite union of pairwise-disjoint closed
cylinders.  Target-base selection, reached-component exhaustion, cross-base
ownership, and all compatibility clauses remain the dynamical gate.

## 2. Equal-level multi-base data

Let \(f\) be a polynomial.  Fix an integer \(N\geq1\).  Let
\(P_\sigma,P_\tau\) be two marked base domains.  Let
\[
  h_w=f^N|_{Q_w}:Q_w\longrightarrow P_\sigma,
  \qquad
  h_v=f^N|_{Q_v}:Q_v\longrightarrow P_\tau
\tag{2.1}
\]
be homeomorphisms.  In the direct-decoration application,
\(N=qm\) and \(w,v\) are words of the same length \(m\).  The base labels
\(\sigma,\tau\) are retained because the second virtual marking need not
live over one common base.

Let \(A\subset P_\sigma\), \(B\subset P_\tau\), and let
\[
  F=f^r|_A:A\longrightarrow B
\tag{2.2}
\]
be a specified restriction of an actual polynomial iterate.  Define
\[
  A_w=h_w^{-1}(A),
  \qquad
  B_v=h_v^{-1}(B).
\tag{2.3}
\]

The equal-level condition in (2.1) is essential.  If the two cylinder maps
used different exponents, commutation alone would compare
\(f^{N_v+r}\) with \(f^{r+N_w}\), which need not be equal.

## 3. The commuting-iterate theorem

### Theorem 3.1 (`FINITE_CYLINDER_COMMUTING_ITERATE_LIFT`)

Assume the data of Section 2 and the target-cylinder containment
\[
  f^r(A_w)\subset Q_v.
\tag{3.1}
\]
Then
\[
  f^r|_{A_w}
  =
  h_v^{-1}\circ F\circ h_w.
\tag{3.2}
\]

If \(F(A)=B\), then
\[
  f^r(A_w)=B_v.
\tag{3.3}
\]
If in addition \(F:A\to B\) is proper of topological degree \(e\), then
\[
  f^r:A_w\longrightarrow B_v
\tag{3.4}
\]
is proper of degree \(e\).  Local degrees are preserved under (3.2).

#### Proof

Fix \(x\in A_w\).  By (3.1), \(f^r(x)\in Q_v\), so \(h_v(f^r(x))\) is
defined.  Using that both cylinder maps in (2.1) are restrictions of the
same iterate \(f^N\), polynomial iterates commute:
\[
\begin{aligned}
  h_v(f^r(x))
  &=
  f^N(f^r(x))\\
  &=
  f^r(f^N(x))\\
  &=
  F(h_w(x)).
\end{aligned}
\tag{3.5}
\]
The final equality holds because \(h_w(x)\in A\) and \(F=f^r|_A\).
Applying the inverse homeomorphism \(h_v^{-1}\) to (3.5) proves (3.2).

Equation (3.2) gives
\[
  f^r(A_w)
  =
  h_v^{-1}(F(A)).
\tag{3.6}
\]
If \(F(A)=B\), this is exactly (3.3).

Finally, (3.2) conjugates \(f^r:A_w\to B_v\) to \(F:A\to B\) by the
homeomorphisms \(h_w,h_v\).  Properness and topological degree are invariant
under such conjugacy.  The same local conjugacy preserves the local degree
at every point.  This proves (3.4) and the last assertion. \(\square\)

## 4. What degree preservation does not record

The theorem preserves total and local degree, but it does not reconstruct
critical chronology.  If a later proof reads the times
\[
  0\leq t_1<\cdots<t_k<r
\]
at which the orbit of a point meets a declared critical component, those
times must remain separate arrow metadata.  Equal total degree
\(2^k\) does not determine the ordered list \((t_1,\ldots,t_k)\).

Likewise, (3.2) transports no prime-end access, obstacle, or localization
record unless the selected cylinder homeomorphisms and \(F\) are already
marked by those data.

### Proposition 4.1 (`FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS`)

Fix a target base \(\tau\) and a depth \(m\).  Suppose the authorized
closed cylinders
\[
  \{Q_{\tau,v}:v\in W_{\tau,m}\}
\tag{4.1}
\]
form a finite pairwise-disjoint family of nonempty connected compact sets.
If \(C\) is nonempty and connected and
\[
  C\subset\bigcup_{v\in W_{\tau,m}}Q_{\tau,v},
\tag{4.2}
\]
then there is a unique \(v\in W_{\tau,m}\) such that
\[
  C\subset Q_{\tau,v}.
\tag{4.3}
\]

#### Proof

A finite family of pairwise-disjoint compact sets has positive pairwise
distance.  Each \(Q_{\tau,v}\) is therefore open and closed in the union
in (4.2).  Its connectedness makes it one connected component of that
union.  A connected subset \(C\) lies in one component, and pairwise
disjointness makes that component unique. \(\square\)

In particular, if \(A_w\) is nonempty and connected, then
\(f^r(A_w)\) is connected and Proposition 4.1 makes target-word uniqueness
formal **after** the target base and union containment have been proved.
This applies to the fixed-base direct-decoration cylinders, whose closed
pieces are pairwise disjoint.  It does not choose the target base and does
not apply to a multi-base family unless cross-base component ownership or
pairwise disjointness has also been proved.

### Lemma 4.2 (localized versus global pullback components)

Let \(P,Q\) be closed Jordan disks and suppose
\[
  f^N|_Q:Q\longrightarrow P
\tag{4.4}
\]
is a homeomorphism.  If \(Q^\circ\) lies in a component \(D\) of
\(f^{-N}(P^\circ)\), then \(D=Q^\circ\).

#### Proof

The set \(Q^\circ\) is open in \(D\).  If
\(x\in\overline{Q^\circ}^{\,D}\), then \(x\in Q\) and
\(f^N(x)\in P^\circ\).  A homeomorphism of closed Jordan disks carries
boundary to boundary, so \(x\notin\partial Q\).  Hence \(x\in Q^\circ\).
Thus \(Q^\circ\) is also closed in the connected set \(D\), and equality
follows. \(\square\)

Accordingly, a reached-component exhaustion statement must either use the
localized component
\[
  \operatorname{Comp}_{C}
  \bigl(f^{-N}(P_\tau^\circ)\cap U_{\tau,m}\bigr)
\tag{4.5}
\]
throughout, or invoke Lemma 4.2 before replacing it by the corresponding
global component of \(f^{-N}(P_\tau^\circ)\).  The two formulations may
not be switched without this check.

### Theorem 4.3 (`INTERIOR_PULLBACK_COMPONENT_FORCING`)

Assume the source cylinder and branch data of Section 2, with \(A\)
connected, and suppose
\[
  F(A)\subset P_\tau^\circ.
\tag{4.6}
\]
Then the connected lifted image \(f^r(A_w)\) lies in one component \(C\)
of
\[
  f^{-N}(P_\tau^\circ).
\tag{4.7}
\]
If an authorized target cylinder \(Q_v\) maps homeomorphically to
\(P_\tau\) under \(f^N\) and \(Q_v^\circ=C\), then \(v\) is unique in
every pairwise-disjoint authorized fixed-base family and Theorem 3.1
applies.

If the branch extends to the relevant closures and
\[
  F(\overline A)\Subset P_\tau^\circ,
\tag{4.8}
\]
then
\[
  \overline{f^r(A_w)}\Subset C.
\tag{4.9}
\]
In particular, the lifted closure meets no pullback boundary.

#### Proof

For \(x\in A_w\), commutation of polynomial iterates gives
\[
  f^N(f^r(x))
  =
  f^r(f^N(x))
  =
  F(h_w(x))
  \in P_\tau^\circ.
\tag{4.10}
\]
The image \(f^r(A_w)\) is connected, so it lies in one component \(C\)
of (4.7).  Lemma 4.2 identifies the interior of an authorized closed
Jordan cylinder with the corresponding global pullback component, and
Proposition 4.1 gives fixed-base uniqueness.  The containment required by
Theorem 3.1 is then available.

Under (4.8), the lifted closure is a compact subset of
\[
  (f^N)^{-1}(F(\overline A))\cap\overline C.
\tag{4.11}
\]
If \(y\in\overline C\) maps into \(P_\tau^\circ\), then \(y\) belongs to
the open set (4.7), hence to one of its components.  That component meets
\(C\), so it equals \(C\).  Thus (4.11) is contained in the open set
\(C\), which proves compact containment (4.9). \(\square\)

Theorem 4.3 removes no source-facing data.  It forces the open pullback
component only after the target base is typed, and it supplies a target
word only after that component is proved to belong to the authorized
cylinder family.  Parent, shift, and enlargement naturality follow by
uniqueness only after their actual component diagrams and metadata
preservation have been proved.

## 5. The exact remaining address selector

### Open Problem 5.1 (`VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR`)

For every realized finite virtual copy-chain prefix, base label
\(\sigma\), equal-depth cylinder word \(w\), and source-defined return
branch \(F=f^r|_A\), construct a unique target pair
\[
  \rho_{F,m}(\sigma,w)=(\tau,v)
\tag{5.1}
\]
such that
\[
  f^r\bigl(h_{\sigma,w}^{-1}(A)\bigr)
  \subset Q_{\tau,v}.
\tag{5.2}
\]
The construction must prove all of the following.

1. **Target-base existence.**  The target base \(\tau\) is part of the
   typed branch data or is selected by unique actual base containment.
2. **Reached-component exhaustion.**  The image in (5.2) lies in the
   open pullback component forced by Theorem 4.3, and that component is
   one of the authorized equal-depth target cylinders.  If closure
   compactness is claimed, verify (4.8).
3. **Uniqueness.**  In the fixed-base pairwise-disjoint case this follows
   from Proposition 4.1.  Otherwise cross-base component ownership and
   all closed boundary contacts must be audited.
4. **Prefix compatibility.**  If \(wa\) is a child cylinder and its target
   is \(vb\), deleting the final geometric symbol gives the target selected
   for \(w\).
5. **Dynamical compatibility.**  Deleting the first inverse symbol commutes
   with (5.1) wherever the pre-root partial shift is defined.
6. **Root compatibility.**  The empty word uses the separately declared
   terminal-cycle arrow, not an invented value of the partial shift.
7. **Marked compatibility.**  Critical chronology, sheets, accesses,
   obstacles, localizations, and terminal returns are carried by the
   selected arrow.
8. **Enlargement naturality.**  An authorized final-root enlargement does
   not change (5.1), unless an explicit first cylinder collision is entered
   in the ledger.
9. **Presentation invariance.**  Equivalent embedded marked data produce
   the same target component or a proved canonical conjugacy.

Only after (5.1)--(5.2) are proved can Theorem 3.1 be applied uniformly to
form the finite multi-base cylinder groupoid with objects
\((\sigma,w)\) and actual iterate arrows between them.

## 6. First-failure certificate

If uniqueness fails, record
\[
  \mathfrak F_{\rm addr}
  =
  (B,m,\sigma,w,F,r,\tau_1,v_1,\tau_2,v_2,
    X,\mathscr G,\mathscr W,\mathcal L),
\tag{6.1}
\]
where \(X\) is the first actual connected image component meeting both
candidate target cylinders, \(\mathscr G\) is its access record,
\(\mathscr W\) its obstacle and sheet ledger, and \(\mathcal L\) the
authorized localization.  A collision only in a finite quotient is not a
geometric failure certificate.

If existence fails, replace the two target entries by the complete list of
authorized target cylinders and record the first point or component of the
image outside their union.

## 7. Adversarial audit

1. **Unequal cylinder depths.** Rejected: the proof uses the same exponent
   \(N\) on both sides of (3.5).
2. **Containment inferred from labels.** Rejected: (3.1) is an actual planar
   component containment.
3. **Surjectivity inferred from containment.** Rejected: (3.3) additionally
   assumes \(F(A)=B\).
4. **Total degree substituted for chronology.** Rejected by Section 4.
5. **Root included in the deletion shift.** Rejected: the root has a
   separately typed arrow.
6. **Two boundary-touching cylinders treated as one target.** Rejected:
   uniqueness in Open Problem 5.1 is component-level and must audit closed
   boundary contacts.
7. **Finite-cylinder proof extended to ends by compactness.** Rejected:
   analytic realization on every end fiber remains part of
   `VIRTUAL_DISCONNECTED_MARKING_TRANSFER`.
8. **Diagnostic computation used as proof.** Rejected: regressions only
   test the algebra and collision bookkeeping.

## 8. Promotion decision

Theorem 3.1 proves `FINITE_CYLINDER_COMMUTING_ITERATE_LIFT`,
Proposition 4.1 proves
`FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS`, and Theorem 4.3 proves
`INTERIOR_PULLBACK_COMPONENT_FORCING`.  Together they reduce the
finite-cylinder part of `VIRTUAL_DISCONNECTED_MARKING_TRANSFER` to target
base selection, component authorization, cross-base ownership, marked
compatibility, and enlargement stability.  The global target-address
selector remains open.  No virtual package, horizon, UPTCR clause, or MLC
claim is promoted.
