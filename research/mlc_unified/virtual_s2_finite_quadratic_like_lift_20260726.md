# Finite virtual scale-two quadratic-like lift

Date: 2026-07-26  
Status: proved for every finite direct-decoration cylinder; the infinite-end
limit and global virtual parameter transfer remain open. Original documents
and original PDFs are unchanged.

## 1. Input

Use the source-defined direct-decoration data

\[
  g=f^q,\qquad \phi_w:\mathcal P\longrightarrow Q_w,
\]

where \(w\) is a finite word in the two actual univalent pullback branches.
Use the terminal primitive quadratic-like return

\[
  F_{\rm term}=f^{p_{\rm term}}:A_0\longrightarrow B,
  \qquad A_0\Subset B,
\]

and the source-supported nesting

\[
  A_0\subset B\subset V^0\subset\mathcal P.
\tag{1.1}
\]

The compact first-return nest places the open terminal domains inside the
interior of the outer puzzle chart, so the restrictions of \(\phi_w\) to
\(A_0\) and \(B\) are holomorphic.

## 2. Finite quadratic-like map

Define

\[
  F_w
  :=
  \phi_w\circ F_{\rm term}\circ\phi_w^{-1}:
  A_w:=\phi_w(A_0)\longrightarrow
  B_w:=\phi_w(B).
\tag{2.1}
\]

Because \(\phi_w\) is conformal and \(A_0\Subset B\),

\[
  A_w\Subset B_w.
\tag{2.2}
\]

Thus \(F_w\) is a quadratic-like map. Its degree is two, its critical
chronology is the transported terminal chronology, and its filled Julia set
is exactly

\[
\begin{aligned}
K(F_w)
  &=\{z\in A_w:F_w^n(z)\in A_w\ \text{for all }n\geq0\}\\
  &=\phi_w\bigl(\{x\in A_0:F_{\rm term}^n(x)\in A_0\
     \text{ for all }n\geq0\}\bigr)\\
  &=\phi_w(K_0)=K_w.
\end{aligned}
\tag{2.3}
\]

The source domain \(A_w\), rather than the codomain \(B_w\), is essential:
\(F_w\) is not defined on \(B_w\setminus A_w\).

The key identity is

\[
  F_w^n=\phi_w\circ F_{\rm term}^n\circ\phi_w^{-1}.
\tag{2.4}
\]

This is an actual polynomial-like realization of every finite pullback
component \(K_w\). It closes the finite analytic-realization portion of the
second-scale attempt.

## 3. Compatibility with the actual polynomial

The map \(F_w\) is a conjugated quadratic-like return, not an iterate of the
original polynomial. The actual polynomial relation that remains available
is instead

\[
  f^{q|w|}\circ\phi_w=\operatorname{id}_{\mathcal P},
  \qquad
  f^{q|w|}(K_w)=K_0.
\tag{3.1}
\]

Consequently, the family \(\{K_w\}\) has exact parent, nesting, and
finite-cylinder shift data, while the maps \(F_w\) supply the missing finite
quadratic-like return on each component. No claim is made that \(F_w\) is
equal to \(f^r\) on \(K_w\).

## 4. What is now proved

For every finite word \(w\):

1. \(K_w\) is a connected filled Julia set of a degree-two
   quadratic-like map \(F_w\);
2. the map has an actual open domain \(A_w\Subset B_w\);
3. the native terminal degree and critical chronology are transported;
4. the native ideal side and any finite prime-end marking transport through
   \(\phi_w\);
5. the filled-Julia identity \(K(F_w)=K_w\) is exact, not a symbolic label.

This is stronger than the earlier finite pullback compactification, which
constructed \(K_w\) only as a nested continuum.

## 5. Exact remaining obstruction

For an infinite address \(\omega\), the end fiber is

\[
  E_\omega=\bigcap_m Q_{\omega|m}.
\]

The finite maps \(F_{\omega|m}\) have changing domains and changing
conjugating charts. The checked sources do not provide any of the following:

1. a nondegenerate normalized limit of \(F_{\omega|m}\);
2. a limiting quadratic-like/GPL map whose filled Julia set is \(E_\omega\);
3. a uniform modulus or chart-normalization bound preventing collapse;
4. a source-defined virtual return base and first-return chronology;
5. complete protected prime-end/Wave marking at the end.

Therefore this finite lift does not yet prove
VIRTUAL_CANTOR_PACKAGE_REALIZATION,
VIRTUAL_DISCONNECTED_MARKING_TRANSFER,
VIRTUAL_RETURN_BASE_ATLAS, UPTCR, or MLC.

## 6. Ledger decision

The corrected finite conjugacy is retained as a specialization of the
existing `RETIMED_FINITE_CYLINDER_PAIR` and
`NORMALIZED_RETIMED_GERM_CONSTANCY` results, rather than promoted as a
duplicate node.  The infinite-end, virtual-state, target-base,
protected-routing, parameter-rigidity, and MLC obligations remain open.
The next mathematically precise target is a compactness and nondegeneracy
theorem for the normalized family \(F_{\omega|m}\), uniformly over all
allowed end addresses.

Machine output:
virtual_s2_finite_quadratic_like_lift_20260726.json, status
FINITE_VIRTUAL_CYLINDER_QUADRATIC_LIKE_LIFT_VALID, and
original_artifacts_written=false.
