# KKL stationary Gate N2 frontier audit

Date: 2026-07-27  
Scope: only the selected-predecessor endpoint and line-1598 incidence
slice  
Global status: Gate N2, VAAPC-I, UPTCR, and MLC remain open

## 1. Source lock

The audited KKL source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The audited Dudko--Lyubich source used only to classify the
non-locally-connected lift wording is

```text
.tmp_wave_audit/dl23/Feigen.tex
SHA-256 EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF
```

The relevant KKL clauses are lines 457, 478--504, 514--543,
661--715, and 1597--1605.  The relevant Dudko--Lyubich clauses are
lines 956--958, 968--970, and 973--978.

## 2. Retraction and correction record

The pass rejected three shortcuts.

1. A selected inverse component need not meet a marked small-Julia
   continuum merely because it meets the original tree.  The
   middle-edge and one-gate graph examples remain valid logical
   countermodels.
2. The printed \(K_0^0\) at KKL line 1597 is not defined.  The
   corrected construction starts from the actual critical member
   \(Q_0\) of the primitive small-Julia cycle and sets
   \(Q_n=\phi_0^n(Q_0)\).
3. An earlier draft said that a sufficiently small injectivity
   neighborhood of \(\alpha_F\) has exactly the \(q\) global limb
   germs.  Local connectivity does not by itself justify that local
   component statement.  It has been removed everywhere and replaced
   by the two-preimage argument in Section 4 below.

No downstream theorem is permitted to cite any of these rejected
steps.

## 3. Canonical finite-horizon package

For \(H=b+2\), source limb dynamics give

\[
 D_0=F^{-1}(\mathfrak L_0)\cap\mathfrak L_0,
 \qquad
 F:D_0\longrightarrow\mathfrak L_0
\]

as a homeomorphism.  The proof counts the two noncritical preimages of
each \(y\in\mathfrak L_0\): one lies in
\(\mathfrak L_{q-1}\), and degree two plus
\(F(\mathfrak L_0)=K(F)\) gives exactly one in
\(\mathfrak L_0\).  Write its inverse as \(\phi_0\).

The corrected packages are:

\[
 Q_n=\phi_0^n(Q_0),
\qquad
 Q_n\subset L_0^n,
\qquad
 \alpha^n=\phi_0(\alpha^{n-1})\quad(n\ge2).
\]

The first \(L_0^1\) is the unique component of
\(\phi_0(L_0^0)\) containing \(Q_1\); later components are transported
by \(\phi_0\).  Actual-component and point addresses record the
ordered subsets, with empty depth-zero word and parent truncation only
for positive depth.  This proves finite selection, not full-carrier
separation, a Wave occurrence, or a prime-end access.

## 4. New unconditional terminal-sheet theorem

Define

\[
 \Omega_0=\mathfrak L_0,\qquad
 \Omega_n=\phi_0^n(\mathfrak L_0).
\]

For every \(n\ge1\),

\[
 \overline{\Omega_n}
 =\Omega_n\cup\{\alpha^n\},
 \qquad
 \Omega_n\in
 \pi_0\!\left(K(F)\setminus\{\alpha^n\}\right).
\]

This conclusion does not use local connectivity.

### 4.1 Excluding the fixed root

Suppose \(x_k\in D_0\) tends to \(\alpha_F\), and put
\(y_k=F(x_k)\).  The homeomorphism
\[
 F:\mathfrak L_{q-1}\to\mathfrak L_0
\]
supplies \(z_k\in\mathfrak L_{q-1}\) with
\(F(z_k)=y_k\).  KKL's limb-closure formula forces every accumulation
point of \(z_k\) into
\(\mathfrak L_{q-1}\cup\{\alpha_F\}\).  It must map to
\(\alpha_F\).  The other preimage \(\alpha^1\) lies in
\(\mathfrak L_0\), so \(z_k\to\alpha_F\).  The distinct same-image
points \(x_k,z_k\) then contradict local injectivity at the noncritical
fixed point.  Hence
\[
 \alpha_F\notin\overline{D_0}.
\]

### 4.2 Exact boundary

A boundary point of \(D_0\) cannot map into
\(\mathfrak L_0\), because the noncritical local inverse and uniqueness
of the critical-limb sheet would make it interior.  It therefore maps
to \(\alpha_F\).  The preceding exclusion leaves only
\(\alpha^1\).  Conversely, compactness applied to
\(\phi_0(y_k)\) for \(y_k\to\alpha_F\) puts
\(\alpha^1\) in the boundary.  Thus
\[
 \partial D_0=\{\alpha^1\}.
\]

The induction for \(\Omega_n\) is legitimate because
\(\overline{\Omega_{n-1}}\) is compact and lies wholly inside the
domain \(\mathfrak L_0\) of \(\phi_0\).  Both directions of
\[
 \overline{\phi_0(\Omega_{n-1})}
 =\phi_0(\overline{\Omega_{n-1}})
\]
are recorded: continuity and density give one inclusion, while
compactness makes the image of the closure closed and gives the other.

## 5. Locally connected and model incidence

In the locally connected physical category, the source-locked
empty-interior theorem plus fullness makes \(K(F)\) a dendrite.
Consequently \(L_0^0=T\cap\mathfrak L_0\) is connected.  For
\(T_n=F^{-n}(T)\),

\[
 L_0^n=T_n\cap\Omega_n.
\]

If \(L_0^n\cap T\ne\varnothing\), the terminal side in
\(\Omega_n\) either contains all of \(T\), or contains a component of
\(T\setminus\{\alpha^n\}\).  Since
\(\alpha^n\notin\mathcal K\), finite-tree pruning supplies an actual
marked small-Julia continuum on that side.  Therefore

\[
 L_0^n\cap T\ne\varnothing
 \Longrightarrow
 \exists i,\quad K_i\subset L_0^n.
\]

The same argument proves a stronger, correctly typed statement in
KKL's locally connected combinatorial model: the selected predecessor
contains an entire geometric model small-Julia continuum
\(\bar K_i\).  Only a subsequent finite-tree quotient collapses
\(\bar K_i\) to an abstract marked vertex.  It does not by itself lift
\(\bar K_i\) to physical \(K_i\)-contact.

## 6. Monotone full-lift criterion

The pass proves a sufficient bridge for the exact non-LC residue.
Assume:

1. the model is a dendrite and
   \(\pi:K(F)\to K(F)_{\rm com}\) is a continuous monotone surjective
   semiconjugacy;
2. \(\pi(\alpha^n)=\bar\alpha^n\) through \(H\), and the fixed fiber
   \(\pi^{-1}(\bar\alpha^0)\) is \(\{\alpha^0\}\);
3. \(T=\pi^{-1}(T_{\rm com})\);
4. \(\pi(Q_n)\subset\bar\Omega_n\), the critical points correspond,
   and \(\pi(K_i)\subset\bar K_i\) for the corresponding geometric
   model small-Julia continuum.

Monotonicity makes every point fiber connected.  Semiconjugacy then
puts \(\pi^{-1}(\bar\alpha^n)\) inside the finite set
\(F^{-n}(\alpha^0)\), so correct labelling and the singleton fixed
fiber force

\[
 \pi^{-1}(\bar\alpha^n)=\{\alpha^n\}.
\]

A monotone map onto a dendrite with singleton root fiber bijects the
components of the two punctured continua.  The proof uses inverse
images of compact model arcs; it does not assume that inverse images
of arbitrary nonclosed connected sets are automatically connected.
It follows that

\[
 \pi^{-1}(\bar\Omega_n)=\Omega_n,\qquad
 \pi^{-1}(L_{0,\rm com}^n)=L_0^n.
\]

Thus \(\bar K_i\subset L_{0,\rm com}^n\) forces
\[
 K_i\subset\pi^{-1}(\bar K_i)
      \subset\pi^{-1}(L_{0,\rm com}^n)=L_0^n.
\]
This closes non-LC MCI conditional on the four geometric
identification clauses.

The earlier point-valued clause
\(\pi(K_i)=\{\bar v_i\}\) was rejected during the primary-source
audit.  It conflated two maps:

1. the monotone rational-lamination projection from the physical
   filled continuum to its locally connected geometric model; and
2. the later finite-tree quotient that treats each geometric
   small-Julia continuum as an abstract vertex.

The canonical monotone model is injective on finite-orbit points,
whereas every nondegenerate periodic small-Julia continuum contains
distinct periodic points.  It therefore cannot collapse \(K_i\) to a
single geometric-model point.  The corrected continuum-valued clause
is both weaker and correctly typed.

The locked KKL and Dudko--Lyubich passages do not state every needed
identification.  Kiwi's Theorem 2, Proposition 4.2, and the
factorization \(h=\widehat w^{-1}\circ q\) in Theorem 5.12 supply
singleton complete fibers at periodic and preperiodic points for the
transported Kiwi model.  They do not construct a marked dynamical
homeomorphism of target models intertwining the Kiwi and KKL
projections, prove \(T=\pi^{-1}(T_{\rm com})\), or prove the
selected-sheet and physical/model small-Julia-continuum
correspondences.  Those remaining bridges stay open.

## 7. Line-1598 consequence

The primitive cycle period satisfies \(P\ge q\).  In the explicit
high-type range \(q>b\), contact at depth \(b\), dynamic continuum
saturation, and the predecessor recursion would put \(b+1\) distinct
cycle components in the critical limb, contradicting the
parabolic \(b\)-bound.  Hence:

- line 1598 and depths \(b+1,b+2\) are proved in the locally connected
  physical category;
- the same counting theorem is proved conditionally in general,
  with physical MCI as its hypothesis;
- the global physical non-LC statement remains open at the exact
  lift package above.

## 8. Still-open analytic gates in this slice

- `KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT`;
- `KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION`, a stronger
  sufficient route;
- `KKL_STATIONARY_SELECTED_SEPARATOR_REALIZATION` (`KSEP_H`);
- conditional proof-used occurrence compatibility (`PUS_H`);
- endpoint/access coherence or a direct marked-access substitute;
- the actual incoming proper host at KKL line 1600;
- the line-1603 two-sided retained route and noncollision.

The corrected \(Q_n\) chain is not called a full-carrier separator
until `KSEP_H` is proved.

## 9. Diagnostic and machine validation

The finite diagnostics are intentionally non-probative:

```text
audit_n2_marked_tree_pruning.py
  PASS: 18,248 trees and 272,739 full marked hulls
  PASS: middle-edge and one-gate negative controls

audit_n2_monotone_full_lift.py
  PASS: monotone singleton-root positive control
  PASS: geometric continuum lift positive control
  PASS: only the second tree quotient collapses the model continuum
  PASS: nonmonotone fold negative control
  PASS: nonsingleton-root negative control
```

The authoritative ledger currently parses with:

```text
465 obligations
34 imported
316 proved
115 open
MLC open
```

The LaTeX build completed with no actual warning, undefined-reference,
overfull/underfull-box, missing-character, citation, or error line in
`build/main.log`.  Text extraction found the new terminal-sheet and
monotone full-lift propositions, the small-Julia point-collapse
obstruction, all new open ledger nodes, and the literal terminal status
`MLC open`.  In accordance with the project's current QA directive, no
rendered-page sweep was performed.  Only manuscript pages 119--122,
containing the modified N2 argument, source-lock page 6, and ledger
pages 212--213 were rendered and visually checked; no clipping,
collision, missing glyph, or status misrendering was found.

```text
build/main.pdf
output/pdf/marked_width_mlc_manuscript.pdf
SHA-256 FDB35DF13A4D0F3B4114F1C8D688430A6B319E8C4B77DDB6EB2B2C85B193FC94

proof_obligations.json
SHA-256 309D69D322A2B6204105543F91EB031B8DDD17ACFF81529601D46A5C41BC15DE

latex/generated/obligations.tex
SHA-256 0439C426990C2238B6AA9ED9D7C0D9EBB7C9665744FD5F793DC13F600552EEF0
```

## 10. Classification

This pass contains a real theorem-level advance: terminal inverse
sheets are proved without local connectivity, and a complete
monotone full-lift implication reduces the remaining non-LC incidence
to explicit source-identification clauses.  It also proves that the
canonical monotone projection cannot collapse a nondegenerate periodic
small-Julia continuum to an abstract tree vertex; this removes an
incorrect quotient-level hypothesis and replaces it with the correctly
typed geometric-continuum correspondence.  It does not prove that
correspondence, the incoming Wave anchor, Gate N2, or any global MLC
gate.
