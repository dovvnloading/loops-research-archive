# Corrected virtual scale-two corridor certificate

Date: 2026-07-26  
Status: the finite corridor-to-terminal-domain square is proved in the
source-defined decoration/principal-nest category; the virtual self-return
and marking-transfer theorem remain open. Original manuscripts and original
PDFs are unchanged.

## 1. Correction to the prior failure certificate

The earlier note
virtual_s2_corridor_root_compatibility_failure_20260725.md stopped at the
claim that the terminal return domains \(A_0,B\) were not known to lie in the
outer puzzle piece \(\mathcal P\). A re-audit of the locked Kahn--Lyubich
sources shows that this claim was too strong for the source-defined terminal
nest.

The direct-decoration source gives

\[
  \mathcal P=Y^{(n-1)q+1},\qquad V^0=Y^{nq+1}\subset\mathcal P,
\]

and two actual univalent pullbacks \(Q_L,Q_R\subset\mathcal P\) of
\(\mathcal P\) under \(g=f^q\). The principal-nest source defines the first
kingdom \(V^0\), its return domains \(W_i^0\Subset V^0\), and the nested
modified principal nest

\[
  V^0\supset W^0\supset\cdots\supset W^{r-1}\supset V^r\supset W^r\supset\cdots.
\]

At the terminal primitive level the actual return is

\[
  f^{p_{\rm term}}:A_0\longrightarrow B,
  \qquad A_0=W^r\Subset B=V^r\subset V^0\subset\mathcal P.
\tag{1.1}
\]

The decoration source uses the equivalent \(E\)-notation
\(A_0=E^\chi\), \(B=E^{\chi-1}\), with \(E^0=V^0\) and
\(E^\chi\subset E^{\chi-1}\subset E^0\). Thus the required
domain inclusions do hold in this native category.

## 2. Typed finite-cylinder square

Let \(w\in\{L,R\}^m\) be a finite word, and let

\[
  \phi_w:\mathcal P\longrightarrow Q_w
\]

be the actual inverse branch of \(g^m=f^{qm}\) supplied by the nested
univalent pullbacks. Since \(A_0,B\subset\mathcal P\), both restrictions
\(\phi_w|_{A_0}\) and \(\phi_w|_B\) are defined. The conjugate terminal map

\[
  \widetilde F_w
  =\phi_w\circ f^{p_{\rm term}}\circ\phi_w^{-1}:
  \phi_w(A_0)\longrightarrow\phi_w(B)
\tag{2.1}
\]

is therefore a genuine holomorphic proper map. It has the same degree as the
terminal return, namely degree two, and the square commutes exactly:

\[
\begin{array}{ccc}
  \phi_w(A_0)&\xrightarrow{\widetilde F_w}&\phi_w(B)\\
  \uparrow\phi_w&&\uparrow\phi_w\\
  A_0&\xrightarrow{f^{p_{\rm term}}}&B.
\end{array}
\tag{2.2}
\]

The source check does not rely on a drawing: it uses the source's nested
closed puzzle domains and the stated compact containments. The machine
validator validate_virtual_s2_corrected_corridor.py checks the source-text
anchors, the nested-domain implications, the conjugacy identity in a symbolic
model, and degree preservation. It writes only a new JSON certificate.

## 3. What this actually closes

The following finite statement is now source-faithful:

> For every finite outer cylinder whose inverse branch is defined on the
> direct-decoration puzzle piece, the native terminal primitive return can be
> pulled back as a well-typed degree-two holomorphic map on the pulled-back
> terminal domains; its domain, target, degree, and native ideal-side record
> are transported by the same univalent chart.

This removes the domain-typing objection in the earlier failure note. It also
shows that “the terminal domains might lie outside \(\mathcal P\)” is not a
valid obstruction in the checked Kahn--Lyubich category.

## 4. The remaining obstruction is different and stronger

Equation (2.1) is a conjugated return, not automatically an iterate of the
original polynomial. The actual-iterate composition that is available from
the same data is

\[
  f^{p_{\rm term}+qm}\big|_{\phi_w(A_0)}:
  \phi_w(A_0)\longrightarrow B,
\tag{4.1}
\]

because \(f^{qm}\circ\phi_w=\operatorname{id}\) on \(\mathcal P\). It is
degree two, but its target is the common native base \(B\), not the
pullback domain \(\phi_w(B)\). In particular, the finite cylinder does not
by itself produce a first-return map from \(\phi_w(A_0)\) back to itself or
to a certified virtual base.

Therefore the earlier failure should be replaced by this exact residual:

1. define the virtual scale-two state space and its selected components;
2. prove that the selected components and their parent/child accesses are
   represented by the source-defined pullback domains;
3. decide whether the virtual transition is the conjugated map (2.1), the
   actual iterate (4.1), or a different source-defined return;
4. prove the corresponding first-return/properness and critical chronology;
5. transport the complete protected prime-end marking and Wave-demand data.

Without these fields, the map in (2.1) cannot be promoted to
VIRTUAL_DISCONNECTED_MARKING_TRANSFER,
VIRTUAL_CANTOR_PACKAGE_REALIZATION, or VIRTUAL_RETURN_BASE_ATLAS.

## 5. Promotion decision

Promote the finite native corridor-domain compatibility lemma and the
source-supported terminal-domain containment. Do not promote the virtual
scale-two selector, virtual marking transfer, protected routing, UPTCR, or
MLC. The correction is a genuine narrowing of the gap, not a global proof.

## 6. Source anchors and cross-checks

- Kahn--Lyubich, *A priori bounds for some infinitely renormalizable
  quadratics II. Decorations*, locked kingdom.tex: the escape piece
  \(V^0=Y^{nq+1}\subset P\), outer piece \(P=Y^{(n-1)q+1}\), univalent pullbacks, and
  the modified nest/terminal primitive map.
- Kahn--Lyubich, *Local connectivity of Julia sets for unicritical
  polynomials*, locked kingdom.tex: first kingdom \(V^0\), return domains
  compactly contained in \(V^0\), the nested \(V^n,W^n\) dynasty, and
  \(g_n:W^n\to V^n\).
- KKL 2026, <https://arxiv.org/html/2606.27272>: the public theorem is scoped
  to parabolically bounded prime primitive families and does not supply the
  virtual-renormalization theorem.
- Dudko 2025/2026, <https://arxiv.org/html/2512.24171>: the virtual-hull
  paragraph does not define the missing state space, return base, or marking
  transfer.

Machine output: virtual_s2_corrected_corridor_20260726.json; the validator
reports CORRECTED_NATIVE_CORRIDOR_TYPED, with
original_artifacts_written=false.
