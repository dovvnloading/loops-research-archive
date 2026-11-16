# Canonical KKL quadrilateral moduli at the physical PR #68 tip — a partial rigorous bound

**2026-11-16. Independent audit; status: PARTIAL, not a certification of any individual \(q_\gamma\).**
The full task of exhaustively enumerating classes with \(q_\gamma>2\) and deciding canonical
support is **not solved** here. This note adds certified, explicit *peripheral cyclic-cover*
bounds, a rigorous upper bound on the canonical WAD norm, and uniform (coarse)
upper bounds for all endpoint-pair types. Every individual \(q_\gamma\) is still open.

Sources: Kahn–Kapiamba–Lyubich (KKL), [*MLC for parabolically bounded primitive
renormalization*, arXiv:2606.27272v1](https://arxiv.org/abs/2606.27272),
Appendix A.2.1–A.2.5, especially the non-minimal-annulus construction in
A.2.3, the non-simply-connected ideal-interval definition in A.2.4, and
(A.2), (A.4). The unchanged audits are
[canonical_wad_electrode_incidence_20261116](../canonical_wad_electrode_incidence_20261116/NOTE.md)
and [canonical_wad_conformal_weights_20261116](../canonical_wad_conformal_weights_20261116/NOTE.md).
This finite checker does **not** formalize KKL's continuum covering or variational
theorems. No MLC or source-electrode transfer assertion is made.

## 1. Exact marking and the still-open problem

At the unchanged 128-bit dyadic PR #68 tip,
\[
\begin{aligned}
 U_3&=D(0,1/4),\\
 K_2&=[x_6,x_{15}]<K_0=[x_9,x_{18}]<K_1=[x_{12},x_3],\\
 Y_K&=U_3\setminus(K_0\cup K_1\cup K_2).
\end{aligned}
\]
The marking consists of **four entire Carathéodory boundary components**
\(I_{\rm out},I_0,I_1,I_2\), not the ten-atom marking on the different
tree annulus \(U_3\setminus[x_6,x_3]\). For an individual **unoriented,
admissible simple ideal arc class** \(\gamma\), two different lifts of its
end intervals in the universal cover define an ideal quadrilateral of
unbuffered width \(q_\gamma>0\), with
\[
w_\gamma=W_{\rm can}(\gamma)=(q_\gamma-2)_+,\qquad
\|W_{\rm can}\|=\sum_\gamma w_\gamma.
\]
The §5 horizontal-plus-vertical projection \(X\) drops bivertical
classes, so \(0\leq\|X\|\leq\|W_{\rm can}\|\).
**No physical one-slit condenser capacity \(C_j\) equals \(q_\gamma\).**
In particular the previously proven \(C_0>2\) does *not* establish
\(w_\gamma>0\) for any class, and \(C_1,C_2<2\) do *not* exclude any class.

There are ten **unordered endpoint types** (including self-endpoints);
these are **not** ten isotopy classes. A four-boundary surface can have
infinitely many simple arc homotopy classes even at a fixed endpoint type.
The KKL theorem that a WAD has at most \(3|\chi(Y_K)|+|\mathcal I|=10\)
positive classes is a bound on simultaneous *support*, not an algorithm
enumerating candidate classes. No word-length cutoff or exhaustive
\(q_\gamma\leq2\) exclusion is established here.

## 2. New analytic theorem: four explicit embedded collars

Write \(H=[m-a,m+a]\) for a real segment, and let
\(z=m+\frac a2(w+w^{-1})\), \(|w|>1\).
The image of \(|w|=t\) is the ellipse of major radius
\(a(t+t^{-1})/2\). We certify that the following four collars
\(A_H(t)=\{1<|w|<t\}\) embed in the **actual \(Y_K\)**:

| Peripheral boundary \(I\) | Segment \(H\) enclosed | \(t\) | Certified upper bound \(B_I\) |
|---|---|---:|---:|
| Outer | **whole tree** \([x_6,x_3]\) | \(23/10\) | \(943/125=7.544\) |
| \(K_0\) | \([x_9,x_{18}]\) | \(11\) | \(2621/1000=2.621\) |
| \(K_1\) | \([x_{12},x_3]\) | \(49\) | \(323/200=1.615\) |
| \(K_2\) | \([x_6,x_{15}]\) | \(25\) | \(1953/1000=1.953\) |

For the three inner collars, the exact major ellipse is strictly inside
\(D(0,1/4)\) **and misses both other inner slits**. For the outer collar
the entire tree contains all three slits, and the ellipse around the
*whole tree*, not an individual slit, is strictly inside \(D(0,1/4)\).
This yields an essential annulus for the outer peripheral homotopy class
even though the tree itself is *not* the canonical marking.
The verifier checks every inequality using outward rational enclosures
for \(x_3,x_6,x_9,x_{12},x_{15},x_{18}\). In particular, the earlier
\(K_0\) auxiliary \(t=21\) ellipse is **not** used as a three-hole collar:
it crosses another slit; only the safe \(t=11\) is used.

For a non-simply-connected boundary component \(I\), KKL A.2.4 defines
the *local width* \(W(I)\) as the conformal width of the annular
peripheral cyclic cover \(Y_I=\widetilde Y_K/\langle\tau_I\rangle\).
Each collar lifts **injectively and essentially** into \(Y_I\): its
fundamental group maps to the primitive loop around \(I\), so the
standard covering-space lifting criterion applies. The lifted collar
separates the two ends of the annular cover. On that cover define an
explicit admissible potential
\[
u(w)=\frac{\log|w|}{\log t}\quad (1<|w|<t),
\]
extended by constants 0 and 1 to the respective remaining components
(the orientation is reversed for the outer collar if necessary). It is
an \(H^1_{\rm loc}\) function with the required two end traces; its only
nonzero gradient lies in the collar. Conformal invariance of Dirichlet
energy gives the **exact** integral
\[
W(I)=\operatorname{Cap}(Y_I)
 \ \leq\int_{A_H(t)}|\nabla u|^2\,dA
 =\frac{2\pi}{(\log t)^2}\int_1^t\frac{dr}{r}
 =\frac{2\pi}{\log t}<B_I. \tag{1}
\]
Equivalently, this is the standard essential-subannulus modulus
monotonicity, with the *inverse modulus* convention used by KKL.
It does not assert that the unbuffered ideal quadrilateral embeds in
\(Y_K\), which is generally false.

All four integrals \(\int_1^t dr/r=\log t\) are bounded using rational
dyadic reduction and the atanh series with an explicit geometric
remainder. \(2\pi\) is enclosed by alternating Machin arctangent series.
The checker uses only Python integers and \`Fraction\`, not floating
point; the outward rational brackets for each integral and its reciprocal
energy appear in [results.json](results.json). It **does not** evaluate
a two-dimensional finite-element integral or any individual \(q_\gamma\).

## 3. Certified consequences (and precise limitations)

KKL A.2.3 gives
\(2\|W_{\rm can}\|=\sum_I W_{\rm can}(I)\), with self-endpoint
classes counted twice. Its (A.2), or equivalently the right side of
(A.4), gives \(W_{\rm can}(I)\leq W(I)\). Hence by (1),
\[
\boxed{0\leq\|W_{\rm can}\|
 <\tfrac12(7.544+2.621+1.615+1.953)
 =6.8665<\frac{687}{100}=6.87.} \tag{2}
\]
The **same** certified bound holds for the §5 projection:
\(0\leq\|X\|<687/100\). Neither norm is shown to be positive.

There is also a **uniform upper bound for every** admissible class,
not a verified value of a named class. If the endpoints are on distinct
components \(I,J\), then \(w_\gamma\leq
\min(W_{\rm can}(I),W_{\rm can}(J))\); if both endpoints are on \(I\),
then \(2w_\gamma\leq W_{\rm can}(I)\). Therefore
\[
 0<q_\gamma<
 \begin{cases}
 2+\min(B_I,B_J),&I\neq J,\\
 2+B_I/2,&I=J .
 \end{cases} \tag{3}
\]
For \(q_\gamma\leq2\), (3) is automatic; for \(q_\gamma>2\),
use \(q_\gamma-2=w_\gamma\) and the local weight bounds.
The [machine results](results.json) include all ten endpoint-type
instances of (3), with each correctly tagged **open**. For example
\(0<q_{K_1,K_1}<1123/400\) and
\(0<q_{K_0,{\rm out}}<4621/1000\); these are bounds
*for any admissible class of that type*, not particular lift
cross-ratios. **No upper endpoint in (3) is at most 2**, and there is
no new positive lower endpoint above 2, so positivity of
\(W_{\rm can}(\gamma)\) is unresolved in **all ten types**.

The previous one-slit capacities remain rigorously bracketed by
\(2.03<C_0<2.07\), \(1.07<C_1<1.62\) and \(1.39<C_2<1.96\)
and are logically distinct from (1)–(3). No dual ideal-quadrilateral
curve-family certificate, interval Fuchsian uniformization, exhaustive
deck-word search, or class-specific validated lower bound is supplied.
It would be incorrect to call this a *first rigorous evaluation of every
\(q_\gamma\)*.

## 4. Reproducibility and hostile-review checklist

From repository root:

\`\`\`sh
python research/independent_audits/canonical_wad_quadrilateral_moduli_20261116/verify.py --check-manifest
python -m unittest discover -s research/independent_audits/canonical_wad_quadrilateral_moduli_20261116 -p 'test_*.py' -v
\`\`\`

The verifier reads, but never modifies, the three existing results
manifests, recomputes the full exact physical orbit, verifies the strict
ellipse/gap conditions, and compares the deterministic checked JSON with
its own recomputed values. Negative controls mutate the dyadic input,
the canonical marking, earlier evidence, an outer/inner collar, and
too-optimistic width bounds. The dedicated CI workflow reruns both
merged canonical audits, protects the new-files-only diff, and dispatches
the existing research-validation and Weighted Lean workflows on the
**exact PR head SHA**. A passing checker certifies the stated rational
inequalities conditional on the written analytic theorem; it does not
replace a proof of KKL's annular cover statements.

Hostile-review boundaries: the outer carrier tree is used only as a
geometric obstacle, **not** as the canonical surface; the outer collar
must enclose *all* holes; \(t=21\) near \(K_0\) must not be treated as
embedded; the KKL local width is inverse annulus modulus; each
self-endpoint coefficient counts **twice**; unbuffered widths and
two-buffer canonical weights differ; capacity of a one-slit condenser
is not an ideal-cover quadrilateral width; the support-size bound 10
does not enumerate isotopy classes; the finite verifier does not prove
the covering theorem; and no extrapolation to a proof-selected §6 Wave
or physical electrodes is permitted.

**Certified here:** all four rational collar/integral/energy enclosures;
the conditional analytic local-width inequalities (1), endpoint-type
brackets (3), and norm bound (2). **Numerical-only:** none.
**Open:** every named \(q_\gamma\), exhaustive short-class list and
\(q_\gamma\leq2\) exclusion for all other classes, every positive/zero
canonical coefficient, the exact total WAD norm, exact \(\|X\|\),
and the repaired transfer constants. In the original task's strict
sense this is **not done**; the new result is the bound (2), not a
certification of support.
