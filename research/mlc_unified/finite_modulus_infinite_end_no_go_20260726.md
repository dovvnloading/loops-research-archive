# No-go: fixed finite modulus does not close the infinite-end limit

Date: 2026-07-26  
Status: proved as an interface-level countermodel; it is not a counterexample
to the Mandelbrot conjecture. It identifies the missing geometric hypothesis
needed to pass from finite quadratic-like lifts to infinite-end shrinking.
Original documents and original PDFs are unchanged.

## 1. The tempting inference

The finite lift gives, for every finite word \(w\),

\[
  F_w=\phi_w\circ F_{\rm term}\circ\phi_w^{-1},
  \qquad
  K(F_w)=\phi_w(K_0).
\]

Because conformal conjugacy preserves the modulus of the terminal
quadratic-like annulus, one might try to conclude that the nested end fibers
\[
  E_\omega=\bigcap_m Q_{\omega|m}
\]
must be points or must carry a limiting quadratic-like map.

That inference is invalid without a geometric estimate controlling how the
ambient cylinders approach their boundary.

## 2. Explicit holomorphic countermodel to the inference

Let \(D=\{|z|<1\}\), and choose \(0<r<1\). Let

\[
  E_r=\left\{x+iy:x^2+\frac{y^2}{r^2}<1\right\}.
\]

The ellipse \(E_r\) is a symmetric Jordan domain contained in \(D\), tangent
to \(\partial D\) at \(+1\) and \(-1\).  Let

\[
  \phi:D\longrightarrow E_r
\]

be the unique Riemann map normalized by
\(\phi(0)=0\) and \(\phi'(0)>0\).  Uniqueness and the conjugation and central
symmetries of \(E_r\) give

\[
\phi(\overline z)=\overline{\phi(z)},\qquad
\phi(-z)=-\phi(z).
\]

Carathéodory extension then gives \(\phi(\pm1)=\pm1\), and the real
restriction is a homeomorphism.  Hence

\[
  \phi([-1,1])=[-1,1].
\tag{2.1}
\]

Since \(E_r\subset D\),

\[
  \phi(E_r)\subset E_r.
\]

Therefore the compact Jordan domains

\[
  \overline D\supset\phi(\overline D)\supset
  \phi^2(\overline D)\supset\cdots
\]

all contain the nondegenerate continuum \([-1,1]\). Their intersection is
nondegenerate:

\[
  [-1,1]\subset
  \bigcap_{m\ge1}\phi^m(\overline D).
\tag{2.2}
\]

Now take any degree-two polynomial-like map \(F:A\to B\) and define the
finite conjugates

\[
  F_m=\phi^m\circ F\circ\phi^{-m}.
\]

Every \(F_m\) is degree two and has exactly the same quadratic-like modulus
as \(F\), but the nested ambient end need not be a point and no ambient
limit map follows from modulus preservation alone.

This countermodel uses the same finite interface fields---univalent nested
charts, finite conjugated quadratic-like returns, exact degree, and fixed
modulus---but is not asserted to arise from a quadratic polynomial. It
therefore refutes only the proposed implication from those fields, not MLC.

## 3. The exact missing sufficient condition

A valid route to singleton end fibers is a serial separating-width theorem.
For each infinite address \(\omega\), one needs annuli \(R_m\) such that:

1. \(R_m\) separates \(E_\omega\) from a fixed outer compact set;
2. the \(R_m\) are pairwise disjoint in the nesting order; and
3.
\[
  \sum_{m=1}^{\infty}\operatorname{mod}(R_m)=\infty.
\tag{3.1}
\]

Grötzsch/serial-annulus extremal-length estimates then force
\(\operatorname{diam}(E_\omega)=0\). A stronger version with controlled
side ports could yield the required prime-end and parameter estimates.

The finite lift does not supply (3.1). Its fixed-modulus annulus is the
annulus of the conjugated terminal map inside \(B_w\); the next child
cylinder lies in a different side component of \(Q_w\setminus B_w\), so
these annuli are not automatically serial separators around the end fiber.
This is exactly the missing collar/trace/corridor geometry.

## 4. Ledger decision

Retain the no-go:

> finite degree-two quadratic-like lifts plus a uniform terminal modulus do
> not imply infinite-end shrinking, a limiting ambient quadratic-like map, or
> virtual parameter rigidity.

The next actual theorem target is therefore a source-faithful divergent
separating-width or equivalent protected-corridor estimate for every allowed
infinite address. Without it, the virtual Cantor realization and global MLC
endgame remain open.

Machine output:
finite_modulus_infinite_end_no_go_20260726.json, status
FINITE_MODULUS_END_NO_GO_VALID, and original_artifacts_written=false.
