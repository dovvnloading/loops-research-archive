# Canonical WAD conformal weights: a **nonclosing** exact auxiliary-condenser audit

**2026-11-16. Independent partial audit; no MLC or canonical-WAD weight certificate.**
This adds rigorous elementary conformal comparisons at the exact PR #68 tip
without altering the merged
[`canonical_wad_electrode_incidence_20261116/NOTE.md`](../canonical_wad_electrode_incidence_20261116/NOTE.md)
or its [`results` manifest](../../../results/canonical_wad_electrode_incidence_20261116.json).
It does **not** complete the requested certification: every individual
universal-cover ideal-quadrilateral modulus \(q_\gamma\), the canonical support,
its total weight, and the scalar repaired-transfer verdict **remain open**.
This is explicitly *not* an argument that all canonical weights vanish.

## 1. Exact domain and three different quantities

At the unchanged dyadic parameter the real critical-orbit intervals are
\[
K_2=[x_6,x_{15}]<K_0=[x_9,x_{18}]<K_1=[x_{12},x_3]
 \subset U_3=D(0,1/4),\qquad Y_K=U_3\setminus(K_0\cup K_1\cup K_2).
\]
KKL, *MLC for parabolically bounded primitive renormalization*,
[arXiv:2606.27272v1](https://arxiv.org/abs/2606.27272), Appendix
A.2.1–A.2.3, defines for a **specific simple ideal arc class**
\(\gamma\) on the **minimally marked four-boundary surface** \(Y_K\):
\[
q_\gamma=W(\widetilde I_\gamma,\widetilde J_\gamma),\quad
W_{\rm can}(\gamma)=(q_\gamma-2)_+.
\]
The §5 projection is \(X(\gamma)=W_{\rm can}(\gamma)\) for horizontal or
vertical classes and zero for bivertical classes. Neither the new
elliptic-annulus measurements below nor the source's free-outer
\(D_h(A_X,B_X)\) are these \(q_\gamma\). In particular, the universal
cover and the class \(\gamma\) must **not** be discarded when assigning
canonical WAD coefficients.

We instead define an auxiliary *target* Dirichlet capacity, one for each
slit \(K_j\):
\[
 C_j=\inf\!\left\{\int_{Y_K}|\nabla u|^2:\
 u|_{K_j}=1,\ u|_{\partial U_3}=0\right\}.
\]
There are **no** imposed values on the other two slit boundaries (natural
Neumann data). This differs from the **source** free-outer condenser
\(D_h\) in the parent audit, even though both are expressed via Dirichlet
energy.

## 2. Analytic theorem and explicit certifiable annuli

**Floating-collinear-slit lemma.** With these symmetric real boundary
conditions, \(C_j\) equals the two-electrode capacity of
\(U_3\setminus K_j\), as if the other two slits were filled back in.
Indeed restricting any \(H^1(U_3\setminus K_j)\) competitor gives
\(C_j\le C_j^{\rm one}\). Conversely for any admissible
\(u\in H^1(Y_K)\), \(v=(u(z)+u(\bar z))/2\) has no greater energy,
retains both imposed traces, and has matching upper and lower traces
on each **floating** real slit. The standard \(H^1\) gluing lemma
extends \(v\) through those slits (their endpoints are removable for
this gluing), with the same energy. Thus
\(C_j^{\rm one}\le C_j\), establishing equality. **This theorem
concerns these auxiliary capacitors only, not individual \(q_\gamma\).**

For \(K_j=[m_j-a_j,m_j+a_j]\), \(a_j>0\), use the conformal Joukowski
chart on the slit exterior:
\[
 z=m_j+\tfrac{a_j}{2}(w+w^{-1}),\quad |w|>1.
\]
The ellipse \(|w|=t\) has semiaxes
\(A(t)=a_j(t+t^{-1})/2\) and
\(B(t)=a_j(t-t^{-1})/2\). If
\( |m_j|+A(t_{\rm in})<1/4\) and
\(1/4+|m_j|<B(t_{\rm out})\), the first ellipse lies
inside \(U_3\), and the second contains its entire closure. Conformal
invariance and domain monotonicity therefore give the **true two-sided
auxiliary capacity enclosure**
\[
 \frac{2\pi}{\log t_{\rm out}}\le C_j\le
 \frac{2\pi}{\log t_{\rm in}}.
 \tag{A}
\]
The strict displayed **rational** bounds follow from the exact comparisons and interval calculations. The exact
128-bit dyadic parameter interval is propagated outward at 256 bits;
all tests of the two inclusions and the final rational brackets use
`Fraction`, alternating Machin bounds for \(\pi\), and positive
atanh-series remainder bounds for \(\log t\), **not binary floats**.

| Auxiliary target capacity | \(t_{\rm in}\) | \(t_{\rm out}\) | Certified strict rational enclosure |
|---|---:|---:|---:|
| \(C_0\) (K0 to outer) | 21 | 22 | \(203/100<C_0<207/100\) |
| \(C_1\) (K1 to outer) | 49 | 340 | \(107/100<C_1<162/100\) |
| \(C_2\) (K2 to outer) | 25 | 90 | \(139/100<C_2<196/100\) |

In particular \(C_0>2\), whereas \(C_1,C_2<2\). These are **not**
certified statements about \(q_\gamma\). Separately, the entire
annular collars \(1<|w|<11\) around \(K_0\),
\(1<|w|<49\) around \(K_1\), and \(1<|w|<25\) around
\(K_2\) lie in the genuine **three-hole** \(Y_K\); the verifier
also checks separation from the adjacent slits. The annular region around \(K_0\) extending to \(t=21\)
**contains** the other two slits and is used *only after* the
floating-slit lemma, not falsely asserted to be an embedded collar
in \(Y_K\).

## 3. What is and is not decided for canonical WAD transfer

KKL Appendix A.2.2 bounds the support cardinality of **any** WAD by
\(3|\chi(Y_K)|+|\mathcal I_{\min}|=3\cdot2+4=10\). This is a
source-dependent general topology bound, **not** a classification or a
list of which ten arc classes can carry weight. The exact canonical
weights require ideal quadrilateral widths in the universal cover.
Even though an entire physical annular collar is embedded, it would
be incorrect to infer that its full physical condenser capacity equals
\(q_\gamma\): the unbuffered ideal quadrilateral foliation need not
project injectively to that collar. KKL removes two square buffers
precisely before obtaining the disjoint canonical lamination. The
present calculation does **not** exclude any particular
\(q_\gamma>2\), and supplies no two-sided \(q_\gamma\) enclosure.

The parent audit certifies, for the **different source** electrodes,
\(3/5120<D_{1/1024}(A_X,B_X)<3/2560\), and identifies the failed
**common-surface and source-prime-end incidence** hypothesis. That is
an obstruction to **applying** the comparison theorem. It is not a
proof that numerical constants \(\kappa,C>0\) cannot happen to satisfy
\((\kappa/C)D_h\le\|W_{\rm can}\|\le D_h\), nor a proof that they do.
The norm \(\|W_{\rm can}\|\) and its horizontal/vertical projection
remain unknown, as does any WAD-to-single-Wave energy accounting.
No positive \(\kappa,C\) is certified; no certified scalar counterexample
is claimed. The repaired inequality is therefore **undecided** at this tip.

## 4. Exact reproducibility, hostile-review boundary, and disposition

From the repository root:

```sh
python research/independent_audits/canonical_wad_conformal_weights_20261116/verify.py --check-manifest
python -m unittest discover -s research/independent_audits/canonical_wad_conformal_weights_20261116 -p 'test_*.py' -v
```

The verifier rechecks the unchanged tip/audit provenance, recomputes
the source orbit, brackets \(\pi\) and logarithms by exact rational
series, checks both ellipse inclusions for every slit and the **smaller**
three-hole collars, then checks the declared strict capacity intervals.
Negative controls reject perturbed parameter/parent data, ellipses that
reach the disk boundary, and falsely enclosing ellipses. The dedicated
CI workflow runs those tests plus the original incidence audit and
its existing physical verifier, and dispatches both unchanged research
validation and weighted Lean workflows at the exact PR commit SHA.
The Python tests do not formalize the continuum gluing theorem,
conformal invariance, all ideal arc classes, or KKL's general topology
bound; those are explicitly written analytic inputs.

**Proved (written analysis):** floating real-slit capacity lemma, exact
Joukowski ellipse comparison (A), separate domain/quantity typing.
**Finite-certified:** outward dyadic geometry, rational transcendental
brackets, six ellipse inclusions, three embedded small collars, three
strict rational capacity enclosures. **Numerical-only:** none.
**OPEN / not done:** validated enclosures for every \(q_\gamma\), exhaustive
\(q_\gamma\le2\) proof, canonical support/total weight, its §5
horizontal+vertical projection, certified transfer constants or a
certified scalar impossibility proof. This note must not be used to
claim that the original canonical-weight certification task is complete.
