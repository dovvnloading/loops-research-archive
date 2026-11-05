# Two short proof recoveries from missing ledger evidence

**2026-11-05.** These elementary proofs are newly written verification artifacts for two *previously marked-proved* ledger obligations whose original evidence files were not preserved in the checkout. They do not create new mathematical priority claims or resolve any open MLC gate.

## 1. Pulled equipotential angular mismatch

**Ledger ID:** \`PULLED_EQUIPOTENTIAL_SERIAL_RECTANGLE_NO_GO\`.

**Statement.** In the exact Böttcher covering model \(F(z)=z^{2^q}\) on a conformal radial sector where the chosen inverse branch is univalent, a nondegenerate equipotential arc of angular width \(\Delta\) has a pulled-back image of angular width \(\Delta/2^q\). If \(q\ge1\), the two full arcs cannot be opposite equipotential edges of one quadrilateral bounded by the **same two rays**.

**Proof.** In angular coordinates \(z=re^{2\pi it}\), the map sends \(t\mapsto 2^q t\pmod 1\). On a branch interval of length below the wrap threshold, its inverse is an affine map of angular derivative \(2^{-q}\). Thus a chosen parent arc spanning angles \(t_0,t_1\), with \(\Delta=t_1-t_0>0\), pulls back to an arc of angular width \(2^{-q}\Delta\). A quadrilateral whose two radial sides lie on the *same* rays \(t=t_0\) and \(t=t_1\) has each full equipotential side spanning that same angular interval, hence both widths equal \(\Delta\). For \(q\ge1\) and \(\Delta>0\), \(\Delta/2^q\ne\Delta\). Therefore the parent arc and its exact inverse-branch pullback are not the two full equipotential sides of such a quadrilateral. \(\square\)

**Boundary.** This rejects a particular *same-ray serial rectangle* identification. It does **not** show that the true pullback region lacks a more general cell decomposition, trace ports, or a nontrivial response operator. See \`research/mlc_unified/research_log.md\` (2026-07-25 trace-collar correction) and the existing finite diagnostic \`research/mlc_unified/validate_trace_collar_no_go.py\`.

## 2. Closed-form pushforward counterexample

**Ledger ID:** \`CLOSED_FORM_PUSHFORWARD_NO_GO\`.

**Statement.** A continuous linear projection of a densely defined closed nonnegative quadratic form need not produce a closed quadratic form under infimal pushforward, without coercivity or a closed-range / lower-semicontinuity condition.

**Proof.** Let \(H=\ell^2(\mathbb N)\), let \(A\) be the closed unbounded diagonal operator \((Ax)_j=jx_j\) with dense proper domain
\[
D(A)=\left\{x\in\ell^2:\sum_{j\ge1}j^2|x_j|^2<\infty\right\}.
\]
On \(H\oplus H\) consider
\[
q(x,z)=\|Ax-z\|_H^2,\qquad D(q)=D(A)\oplus H.
\]
The operator \(B(x,z)=Ax-z\) on \(D(A)\oplus H\) is closed: if \((x_m,z_m)\to(x,z)\) and \(Ax_m-z_m\to y\), then \(Ax_m\to y+z\), so closedness of \(A\) gives \(x\in D(A)\) and \(Ax=y+z\). Consequently \(q=\|B\cdot\|^2\) is a densely defined **closed** nonnegative quadratic form, since its form norm \(\|(x,z)\|^2+\|B(x,z)\|^2\) is the graph norm of closed \(B\).

For the bounded projection \(p(x,z)=x\), define the extended infimal pushforward
\[
(p_*q)(x)=\inf_{\{z:(x,z)\in D(q)\}}q(x,z),
\quad\text{with }\inf\varnothing=+\infty.
\]
If \(x\in D(A)\), choosing \(z=Ax\) makes \((p_*q)(x)=0\); otherwise it is \(+\infty\). Thus the finite form domain of \(p_*q\) is exactly \(D(A)\), and its form norm is the ordinary \(\ell^2\) norm. But \(D(A)\) is not complete in that norm. For example, the finite truncations of \(x=(1/j)_{j\ge1}\in\ell^2\) belong to \(D(A)\) and converge in \(\ell^2\), while \(x\notin D(A)\), since \(Ax=(1,1,\ldots)\notin\ell^2\). Hence \(p_*q\) is not closed. \(\square\)

**Boundary.** This is a functional-analytic non-preservation example, not an obstruction to infimal composition itself: extended-valued infimal pushforward remains associative under composition of maps. It does not prove or disprove a dynamically realized Hilbert trace-response law.

## Audit and status policy

These two entries were already marked proved before this recovery. No theorem status or analytic MLC gate is promoted by citing these independent proofs. The original missing review files, if found, should still be preserved for historical provenance and cross-checked against their declared source claims.
