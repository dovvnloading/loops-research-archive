# Issue #40 — a genuine quadratic excess-tree \(\iota^*\) atlas with strict closed-endpoint saturation

**Date:** 2026-11-06.  
**Mathematical status:** **Proved for the explicit holomorphic quadratic stage below**, with actual full-preimage tree, actual immersion \(\iota\), explicit conformal prime-end circles, complete branch pullback, and the edge-side incidence *from the same maps*. This is **not** a KKL prime-primitive renormalization and is **not** a counterexample to the intended KKL interval-growth theorem. It is a fully geometric test case for the missing exceptional-\(\iota^*\) correspondence, unlike PR #39's synthetic circle example.

**Versioned source:** Kahn–Kapiamba–Lyubich, *MLC for parabolically bounded primitive renormalization*, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §2.1 (ordinary quadratic-like maps are \(\psi\)-ql with \(\iota=\mathrm{id}\)); §2.5 (actual Hubbard edges and degree-two inverse-edge incidence); §6.1 Proposition 6.5 (immersion pullback includes *complete* added-component Carathéodory boundary, with open/closed inputs independent); Appendix A.3.1–A.3.4 (covering \(f_*\), maximal proper-path immersion restriction \(\iota^*\), and warning \(F_*\overline I\ne\overline{F_*I}\) in general).

## 1. Actual quadratic-like pair and actual excess tree

Put
\[
P(z)=z^2-1,\quad U=\{z:|z|<3\},\quad
U'=P^{-1}(U)=\{z:|z^2-1|<3\}.
\tag{1.1}
\]
The set \(U'\) is a simply connected Jordan domain (the single oval of the polynomial lemniscate with radius 3). Moreover
\(|z|^2\le |z^2-1|+1<4\) on \(U'\), so \(U'\subset D(0,2)\Subset U\). Hence
\[
F=(f,\iota)=(P,\mathrm{inclusion}):(U',K_P)\rightrightarrows(U,K_P)
\tag{1.2}
\]
is an actual quadratic-like, thus \(\psi\)-ql, pair in the sense of §2.1. Its filled Julia set is the connected basilica filled Julia set; it contains the postcritical orbit \(0\leftrightarrow-1\).

The genuine forward-invariant **postcritical Hubbard segment** and its **complete inverse tree** are
\[
T=[-1,0],\quad P(T)=T,\quad
T'=P^{-1}(T)=[-1,1],\quad T'\setminus T=(0,1].
\tag{1.3}
\]
Write \(X=(0,1]\). It is a single actual added branch with **one planar attachment point**
\[
\overline X\cap T=\{x\},\qquad x=0.
\tag{1.4}
\]
The critical point \(0\in T'\) maps to the target endpoint \(-1\in T\).

**Scope warning.** The segment \(T\) is the bona fide postcritical Hubbard tree for this postcritically finite quadratic map. It is **not** the complete *small-Julia-cycle* Hubbard tree for a prime primitive renormalization: \(P(z)=z^2-1\) has a **superattracting period-two** orbit, so it is **not periodically repelling**, and is satellite rather than prime primitive; the induced one-edge matrix below also has Perron root one. Therefore none of the special KKL \(q,b\)-corridor or \(\lambda_F>1\) conclusions is attributed to this example.

## 2. Genuine source and target prime-end circles, same covering

Set \(V=U\setminus T\), \(V'=U'\setminus T'\). They are genuine annuli and
\[
f=P:V'\longrightarrow V
\tag{2.1}
\]
is a connected unbranched degree-two covering. The **actual holomorphic immersion**
\(\iota:V'\hookrightarrow V\) is inclusion; it is not proper near the added branch \(X\), whose interior is in \(V\).

The explicit slit-exterior conformal coordinates are
\[
\Psi_{T'}(w)=\frac12(w+w^{-1}),\qquad
\Psi_T(u)=-\frac12+\frac14(u+u^{-1}),\qquad |w|,|u|>1.
\tag{2.2}
\]
Their restrictions to annular collars of the respective *inner* prime-end boundaries of \(V',V\) are genuine conformal charts (the outer boundaries of \(U',U\) need not be round in these coordinates). The identity
\[
\boxed{
P\bigl(\Psi_{T'}(w)\bigr)
=\frac14(w^2+w^{-2}-2)
=\Psi_T(w^2)
}
\tag{2.3}
\]
holds exactly. Thus with actual Carathéodory angular coordinates \(s,t\in\mathbb R/\mathbb Z\) induced by \(w=e^{2\pi i s}\), \(u=e^{2\pi i t}\), the real source covering is
\[
\boxed{p=f_*:s\longmapsto 2s\pmod1.}
\tag{2.4}
\]
This is not a circle program chosen independently of the tree: (2.4) is the boundary action of the **same polynomial** whose complete preimage tree is (1.3).

The planar landing maps are (both extend continuously in this locally connected slit example)
\[
L_{T'}(s)=\cos(2\pi s),\quad
L_T(t)=-\frac12+\frac12\cos(2\pi t).
\tag{2.5}
\]
In particular the **single target tip access** at the planar attachment point \(x=0\) is \(t=0\), while the source at the same planar \(x=0\) has two **distinct accesses**
\[
s^-=\frac14,\qquad s^+=\frac34.
\tag{2.6}
\]
The full added hair \(X\) fills the source contour arc
\[
B_X=[\tfrac34,1]\cup[0,\tfrac14],
\tag{2.7}
\]
where its two endpoint gates are \(s^+,s^-\) and its interior consists of the two physical sides of \(X\) and the tip access at 1. Its normalized angular length is \(1/2\). The two gates both have planar impression \(\{0\}\), yet are **different prime ends**. There is no valid operation “identify source accesses because their impressions share \(x\).”

## 3. Exact *derived* immersion contour code and actual \(\iota^*\) pullback

The old target upper and lower slit sides are the genuine open prime-end arcs
\[
I_+=(0,\tfrac12),\qquad I_-=(\tfrac12,1).
\tag{3.1}
\]
Their old source counterparts (with orientation induced by the conformal coordinates) are
\[
H(I_+)=(\tfrac14,\tfrac12),\qquad
H(I_-)=(\tfrac12,\tfrac34).
\tag{3.2}
\]

For clarity, the **geometrically derived** contour-collapse *coding* \(q:C'\to C\) can be written explicitly. It is **not** a continuous extension of the holomorphic inclusion \(\iota\) at the added hair, since \(X^\circ\subset V\) is interior to the target complement. Set
\[
q(s)=
\begin{cases}
0\pmod1,&s\in[\tfrac34,1]\cup[0,\tfrac14],\\
(2\pi)^{-1}\arccos(2\cos(2\pi s)+1),&s\in[\tfrac14,\tfrac12],\\
1-(2\pi)^{-1}\arccos(2\cos(2\pi s)+1),&s\in[\tfrac12,\tfrac34].
\end{cases}
\tag{3.3}
\]
It is continuous, monotone and degree one, with
\[
q^{-1}(\{0\})=B_X,\qquad q^{-1}(\{\tfrac12\})=\{\tfrac12\}.
\tag{3.4}
\]
**Derivation (not assumption).** On the old arc sides, equate the actual landing coordinates
\(L_T(q(s))=L_{T'}(s)\), retaining upper/lower side orientation. This uniquely gives the two arccos branches of (3.3). Since \(X\) is connected and meets the old tree **only** at the tip \(x\), the entire source branch contour between \(s^+\) and \(s^-\) must be inserted at the **one old tip access** \(t=0\); this gives the constant part. The two formulas join at \(s^\pm\) and at \(s=1/2\). Hence \(q\) is a consequence of the real embedded segments and their true prime ends, rather than an independently supplied abstract monotone quotient.

### Theorem 3.1 (actual analytic attachment-pullback for the two-side marking)

The native immersion proper-path restriction on the two open side atoms and their closures is
\[
\boxed{
\begin{aligned}
\iota^*I_+&=(\tfrac14,\tfrac12),&
\iota^*\overline{I_+}&=[\tfrac34,1]\cup[0,\tfrac12],\\
\iota^*I_-&=(\tfrac12,\tfrac34),&
\iota^*\overline{I_-}&=[\tfrac12,1]\cup[0,\tfrac14].
\end{aligned}
}
\tag{3.5}
\]
In particular the closed pullback includes the **complete Carathéodory boundary** \(B_X\), not only its root or its first edge-side germ. On this explicitly checked finite marking, the results coincide with \(q^{-1}(J)\) for each of the four inputs \(J\), but no global \(\iota\)-boundary extension is inferred.

**Proof.** The target old upper side is the upper planar approach to \((-1,0)\), and its source old counterpart is exactly \(s\in(1/4,1/2)\) by (2.5); likewise for the lower sides. The only component of \(T'\setminus T\) is the connected branch \(X\), whose attachment point \(x=0\) is **not in either open side atom** but **is in the closure of either**. Every source access in \(B_X\) is represented by a defining slit crosscut on a side of \((0,1]\). In the smaller source complement those crosscuts are genuinely proper, while the corresponding paths of the inclusion approach a point of \(V\) and are generally **not proper target paths**. The complete-branch rule of the actual proper-path restriction (the geometric reasoning of KKL Proposition 6.5) therefore inserts the whole \(B_X\) precisely when the old boundary access \(x\) is eligible. There are no other added components. Joining the old side traces (3.2) to the complete block (2.7) gives exactly (3.5); conversely any source access outside these sets is on the opposite old side and is excluded by old-side proper-path subordination. This proves the maximality in the four cases and agrees with the directly derived code (3.3). \(\square\)

## 4. An actual **strict** closed-pullback discrepancy

### Theorem 4.1 (native quadratic endpoint-only saturation)

For the very same actual maps \(f=P\) and \(\iota=\mathrm{id}\),
\[
\begin{aligned}
F_* I_+ &=p(\iota^*I_+)
=p((\tfrac14,\tfrac12))=(\tfrac12,1)=I_-,\\
F_*\overline{I_+}
&=p(\iota^*\overline{I_+})
=p([\tfrac34,1]\cup[0,\tfrac12])=C.
\end{aligned}
\tag{4.1}
\]
Thus
\[
\boxed{
F_*\overline{I_+}=C
\quad\ne\quad
\overline{F_*I_+}=[\tfrac12,1].
}
\tag{4.2}
\]
The same holds with \(+\) and \(-\) interchanged. The defect is **not** just a single missing point: the inclusion of the entire attached-component boundary at the **closed** old tip forces the covering image to become the whole circle.

**Proof.** Use (3.5) and the *polynomial-induced* covering \(p(s)=2s\bmod1\). The open old upper source arc has length \(1/4\), so its image is the proper lower target arc. The closed source arc wraps from \(3/4\) to \(3/2\) and has length \(3/4>1/2\), so its image is the entire circle. This is the exact half-turn saturation criterion of the companion native annular-cover theorem, applied to the actual polynomial. \(\square\)

The source closed-input defect itself is nonempty:
\[
\iota^*\overline{I_+}\setminus\overline{\iota^*I_+}
=B_X\setminus\{\tfrac14\}
\quad\text{(up to the old gate convention)}, 
\tag{4.3}
\]
and its *whole* source branch was independently determined by the analytic geometry. The important invariant assertion is the strict **set inclusion** of (4.2), not a one-point angular anomaly.

At the old zero-dimensional tip access \(a_x=\{t=0\}\), the native relation also gives
\[
\iota^*\{a_x\}=B_X,\qquad p(\iota^*\{a_x\})=C,
\tag{4.4}
\]
a genuine one-step local **zero-vertex-access saturation** example. It is intentionally written as \(p(\iota^*\{a_x\})\), not \(F_*a_x\) on the original open-multi-interval dynamical domain.

## 5. Exact edge-side incidence from the same source maps

The old combinatorial Hubbard tree \(T\) has the one edge \(e=(-1,0)\), with critical endpoint. Its graph image under the actual polynomial is \(P(e)=e\), traversed **once**. Therefore the source-edge row matrix and eigenvalue are
\[
\boxed{T_P=(1),\quad\lambda_P=1.}
\tag{5.1}
\]
The source full inverse tree has exactly **two** true preimage edges of \(e\):
\[
e_{\rm old}=(-1,0),\quad e_{\rm add}=(0,1),
\tag{5.2}
\]
and the map is univalent on their interiors. Its four **actual** source prime-end edge-side traces and target images are
\[
\begin{array}{c|c|c}
\text{source trace }s & \text{old/add} & p(s)\text{, target trace}\\ \hline
(\tfrac14,\tfrac12)&\text{old, upper}&(\tfrac12,1)\ \text{lower}\\
(\tfrac12,\tfrac34)&\text{old, lower}&(0,\tfrac12)\ \text{upper}\\
(0,\tfrac14)&\text{added, upper}&(0,\tfrac12)\ \text{upper}\\
(\tfrac34,1)&\text{added, lower}&(\tfrac12,1)\ \text{lower}
\end{array}
\tag{5.3}
\]
Each target side occurs **twice** in the full two-sheet preimage: once from the old edge and once from the added edge, as the source holomorphic covering demands. Each old edge-side occurs **once** in the old graph traversal. **No independent numerical edge-incidence matrix was selected.**

**Proof.** Formula (2.5) identifies old and new physical upper/lower source slit sides, and (2.4) maps the corresponding angular arcs as in (5.3). The two inverse edges are exactly the two real branches of the equation \(z^2-1=y\) for \(y\in(-1,0)\). The old graph map is strictly decreasing from 0 to -1 on \((-1,0)\), covers the target edge once, and has no interior critical point. \(\square\)

**Important restriction.** The one-edge eigenvalue is \(\lambda_P=1\), not the \(\lambda_F>1\) of prime primitive renormalization in KKL §2.5. This example **does not establish strict Perron edge-weight growth, absence of trapped zero sectors for every possible interval, or bounded-visit growth** in the required class. It does establish all **local analytic bookkeeping** for this concrete critical attachment, including multiplicity and endpoint behavior.

## 6. What the actual example proves and what it leaves open

The algebraic/conformal source-and-target maps, the embedded old and full inverse trees, the unique critical attachment, the full \(B_X\), the derived local contour code \(q\), the actual covering \(p\), the **open/closed** pullback discrepancy and the source edge-side incidence are all explicitly realized by the **same polynomial**.

This provides an adversarial **holomorphic** test for future KKL claims:

1. A planar attachment point \(x\) can have **two distinct source prime-end gates** (the genuine source here has \(s=1/4,3/4\)), even when the old target has only one tip prime end.
2. An immersion's proper-path pullback can add a **whole source boundary interval** when an old endpoint enters the closed input; replacing it with a point or with \(\overline{\iota^*I}\) gives a *strictly wrong* answer.
3. The covering may saturate upon inserting the complete \(B_X\). Such saturation is **not a cancellation of edge multiplicities**.
4. The corresponding edge-incidence count and its two source side sheets must be read from **the same** analytic preimage tree and covering.
5. A monotone contour collapse \(q\) can be **derived** in this analytic case but is **not** the pointwise prime-end extension of \(\iota\); assuming one exists in a wild non-LC stage is unjustified.

The local atlas cannot be imported wholesale to a small filled Julia continuum with non-singleton prime-end impressions: its contact sectors may lack the simple slit crosscut charts of (2.2). In KKL's **required** primitive category, the missing theorem remains the actual contact-impression/root gate selection (source and target), full \(B_X\) placement, equality with the original vertex-side marking and \(T_F\), all zero-sector escape, and the real **closed** critical-Wave crest inclusions.

**Disposition:** a rigorously source-defined **quadratic analytic attachment control**, not a full-category native counterexample and not Issue #40 acceptance. Keep \`KKL_BOUNDED_VISITS_INTERVAL_GROWTH_REPAIR\`, \`KKL_PARABOLIC_WAVE_AMPLIFICATION\` and MLC OPEN. No synthetic interval simulations or independent specialist proof review are claimed.


## Postscript — a stronger periodically repelling analytic control

The companion [exact Misiurewicz quadratic attachment/incidence atlas](./kkl_misiurewicz_actual_expanding_attachment_atlas_20261106.md) replaces the attracting basilica by a **periodically repelling** quadratic \(P_c(z)=z^2+c\) whose critical orbit lands on a repelling fixed point. Its old real postcritical Hubbard tree \(T=[c,c^2+c]\) has an actual added inverse branch attached at the second preimage of that fixed point. The **same** Joukowski source and target charts still give angular doubling, a complete \(\iota^*\) boundary block and a strict \(F_*\overline I\ne\overline{F_*I}\), but now a Markov-refined **signed edge-word** matrix has Perron root \(\sqrt2>1\). This is substantially closer to the source's periodically repelling, expanding setting, but remains **outside** its prime primitive renormalization category. It does not close Issue #40.
