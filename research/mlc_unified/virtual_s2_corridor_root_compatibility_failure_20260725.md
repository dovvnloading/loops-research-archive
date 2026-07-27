# Virtual scale-two corridor-to-root compatibility failure certificate

Date: 2026-07-25  
Status: failed at the first domain-compatibility square; no universal
obligation is promoted.

## 1. Scope

This certificate tests the smallest remaining analytic bridge after the
finite outer-cylinder and native terminal-root passes. It does not modify
the main manuscript, either original PDF, or the proof ledger.

The source notation uses `P` both for the outer puzzle piece and, in the
terminal return, for a primitive period. To avoid conflating those objects,
write the outer puzzle piece as \(\mathcal P\) and the terminal period as
\(p_{\rm term}\) below.

## 2. Source-typed inputs

The direct-decoration source package gives closed Jordan pieces

\[
  Q_a\subset \mathcal P,\qquad g=f^q:Q_a\longrightarrow\mathcal P,
  \qquad \phi_a:\mathcal P\longrightarrow Q_a,
\]

with each \(g|_{Q_a}\) univalent and proper. For a finite word \(w\),
\(\phi_w:\mathcal P\to Q_w\) is therefore an actual univalent inverse
branch and \(g^{|w|}:Q_w\to\mathcal P\) is univalent.

The terminal primitive source package separately gives an actual return

\[
  f^{p_{\rm term}}:A_0\longrightarrow B,
  \qquad A_0\Subset B,
\]

with a multi-base chain, one degree-two arrow, all other arrows univalent,
and a native degree-two root record with ideal side \(I_{1\to0}\).

These are two genuine pieces of data, but they are not yet a common
analytic chart.

## 3. The attempted square

The natural finite-cylinder attempt is to pull the terminal return through
the outer chart:

\[
  F_w=\phi_w\circ f^{p_{\rm term}}\circ\phi_w^{-1},
  \qquad
  \phi_w(A_0)\longrightarrow\phi_w(B).
\]

For this expression to be an actual open-domain holomorphic map, the
following two inclusions (or a proved extension of \(\phi_w\) to the same
sets) are required:

\[
  A_0\subset\mathcal P,
  \qquad B\subset\mathcal P.
\]

The checked source records \(K_0\Subset\operatorname{int}V^0\subset
\mathcal P\) and \(A_0\Subset B\), but it does not record either
\(A_0\subset\mathcal P\) or \(B\subset\mathcal P\), nor an analytic
extension of \(\phi_w\) to them. The inclusion of the filled Julia set is
not a substitute for inclusion of the surrounding return domains.

Consequently the attempted square fails before degree, access, or marking
can be checked:

\[
\begin{array}{ccc}
  \phi_w(A_0) &\xrightarrow{\ ?\ }& \phi_w(B)\\
  \uparrow\phi_w && \uparrow\phi_w\\
  A_0 &\xrightarrow{\ f^{p_{\rm term}}\ }& B
\end{array}
\qquad
\text{is not typed on the stated domains.}
\]

## 4. Why the degree calculation cannot repair it

Every map assembled only from the finite outer cylinders and their inverse
branches is univalent. Hence its degree is one. The terminal degree-two
record is real, but it belongs to the separately constructed native root
return. It cannot be inserted into the outer cylinder by symbolic
concatenation. A valid scale-two object must first prove a corridor from a
finite cylinder or end fiber to the terminal return domains, then prove the
root transition and its marked prime-end transport on that common corridor.

## 5. Exact promotion decision

This is a first failed square for the missing virtual second-scale map. It
leaves `VIRTUAL_DISCONNECTED_MARKING_TRANSFER`,
`VIRTUAL_RETURN_BASE_ATLAS`, `VIRTUAL_CORRIDOR_PAIR_NATURALITY`,
`VIRTUAL_PROTECTED_ROUTING_CERTIFICATE`, and `MLC` open. The native
terminal root record remains valid, but no virtual scale-two analytic return
has been promoted.

## 6. Required next certificate

For one explicit finite word \(w\), construct and verify either:

1. actual open domains \(A_{2,w}\Subset B_{2,w}\subset\mathcal P\) with
   \(f^{p_{\rm term}}\)-compatibility and a proved conjugacy to the native
   root return; or
2. an explicit analytic extension of \(\phi_w\) to the terminal return
   domains, together with protected accesses, the degree-two chronology,
   and the marked correspondence.

If neither certificate can be constructed, the failure remains at the
corridor/domain interface rather than being hidden behind a virtual label.

## 7. Post-audit correction (2026-07-26)

The domain-containment statement in Sections 3--5 was too strong for the
source-defined Kahn--Lyubich terminal nest. The locked decoration source
gives \(V^0=Y^{nq+1}\subset\mathcal P\), where
\(\mathcal P=Y^{(n-1)q+1}\). The locked principal-nest source gives the
terminal domains \(A_0=W^r\Subset B=V^r\subset V^0\). Therefore
\(A_0,B\subset\mathcal P\) in that native category, and the conjugate
\(\phi_w\circ f^{p_{\rm term}}\circ\phi_w^{-1}\) is well typed on
\(\phi_w(A_0)\to\phi_w(B)\).

This historical failure certificate is superseded on that specific point by
virtual_s2_corrected_corridor_certificate_20260726.md and its validator.
The virtual self-return, state-space selection, protected marking, and MLC
obligations remain open because the corrected conjugate is not automatically
an iterate or a first-return of the original polynomial at the virtual scale.
