# Finite-period primitive-tip Wave gain: every p >= 3

**2026-11-16 — RESULT: STRICT POSITIVE INDEPENDENTLY MAXIMIZED UNBUFFERED A.1 DEFECT FOR ALL PRIMITIVE TIP PERIODS.** This add-only audit builds on the merged [limiting-gain](../tip_family_limiting_wave_gain_20261116/NOTE.md) and [canonical-gain](../tip_family_canonical_wave_gain_20261116/NOTE.md) audits. **All statements about the actual physical KKL ideal markings remain conditional on the previously isolated identification M.** Statements about the explicitly marked slit models are unconditional. Our Python code certifies rational interval implications of the analytic proof, not M, the topology, or the Schwarz–Christoffel theorem.

With exactly the earlier definitions, \(P_p\) is the unrestricted supremum of unbuffered A.1 parent Wave widths on \(\Omega_p=U_p\setminus[x_{2p},x_p]\), base \((I_9,I_0,I_1)\), crest \(I_0\). On \(\Omega'_p=V_p\setminus[-x_p,x_p]\), \(C_p^+\) and \(C_p^-\) are the **independently optimized** source suprema with bases \((S_1,S_2,S_3)\), \((S_{17},S_{18},S_{19})\) and crests \(S_2,S_{18}\). Conjugation gives \(C_p^+=C_p^-=:C_p>0\). The defect is

\[
D_p=(C_p^+)^{-1}+(C_p^-)^{-1}-P_p^{-1}=2/C_p-1/P_p.
\]

These are **not** the literal KKL A.2.3 buffered canonical WAD arc weights, which vanish here. No maximum is asserted to be attained.

## 1. All-period theorem and ten separate certified signs

For every integer \(p\ge3\), **conditional on M for the physical interpretation**,

\[
\boxed{D_p>1/100>0.}
\]

For \(3\le p\le12\), this note supplies individually certified physical parent competitors and domain-sensitive physical child upper bounds. For every \(p\ge13\), the corrected limiting audit proves \(D_p>40/819>1/100\). There is **no interpolation at 12/13**, no presumed convergence of the unrestricted optima, and no extrapolation of numerical measurements. The separate limiting marked model has \(0.696<D_\infty<0.793\) by that predecessor; we do not assert \(D_p\to D_\infty\).

**Tail correction, 2026-11-23.** The limiting verifier formerly divided
the parameter-displacement contribution to its physical cut error by 3.
Its corrected all-period parent certificate is \(P_p>13/20\); combined
with the unchanged \(C_p<63/50\), it gives \(40/819\).  This preserves the
all-period \(1/100\) conclusion and does not change any finite row below.
See the dated correction in the limiting audit and
[the separate complete H3 proof](../maximal_native_wave_20261123/H3_WIDTH.md).

All displayed decimals in the table are **strict rational bounds**, not optimizer approximations.

| p | Actual embedded parent width \(W_{P,p}>\) | Actual-source independent child \(C_p<\) | Defect \(D_p>\) |
|---:|---:|---:|---:|
| 3 | 0.490 | 0.974 | **0.010** |
| 4 | 0.511 | 0.985 | **0.070** |
| 5 | 0.581 | 0.988 | **0.300** |
| 6 | 0.581 | 0.988 | **0.300** |
| 7 | 0.581 | 0.988 | **0.300** |
| 8 | 0.581 | 0.988 | **0.300** |
| 9 | 0.581 | 0.988 | **0.300** |
| 10 | 0.581 | 0.988 | **0.300** |
| 11 | 0.581 | 0.988 | **0.300** |
| 12 | 0.581 | 0.988 | **0.300** |
| all p >= 13 | 13/20 | 63/50 | **40/819** |

Every finite row reruns the independent old dyadic root isolation and fixed-point intervals. The finite source-bound improvement is stronger than the displayed rounded cap:
\[
\boxed{C_p\le E_p-1/5{,}000{,}000<E_p\quad(3\le p\le12),}
\]
where \(E_p\) is the earlier **plane-slit full-log-lift** source child upper envelope. These strict bounds already give the rational positive margins
\[
\begin{aligned}
D_3&>2/(974/1000)-1/(490/1000)=300/23863>1/100,\\
D_4&>2/(985/1000)-1/(511/1000)=7400/100667>7/100,\\
D_p&>2/(988/1000)-1/(581/1000)=43500/143507>3/10
\quad(5\le p\le12).
\end{aligned}
\]
**No small period has a certified loss or remains sign-undecided.** The geometric bottleneck is \(p=3\), not a numerical precision failure; the earlier sign-indefinite brackets are sharpened by genuine embedded competitors, rather than by claiming that the full-lift envelopes are optimal.

## 2. Physical positive scale and embedded parent domains

Let \(f_c(z)=z^2+c\), \(G_p=f_{c_p}^p\), \(x_j=f_{c_p}^j(0)\), and \(G_p(z)=x_p+A_pz^2+E_p(z)\). **Physical cuts are \(x_{jp}\), not \(x_j\).** Since \(A_p<0\), use the real-order-preserving scale
\[
\lambda_p=-A_p>0,\quad X_{j,p}=\lambda_p x_{jp},\quad
\rho_p=\lambda_p R_p,\quad R_3=1/4,\ R_p=2^{-p}\ (p\ge4).
\]
In the alternative \(w=A_pz\) chart the analytic normalization is
\(h_p(w)=w^2+\tau_p+e_p(w)\); in **our** \(\xi=-w=\lambda_pz\) chart it is
\(\widehat G_p(\xi)=-\xi^2-\tau_p-e_p(-\xi)\). These formulas and real orders must **not** be conflated.

The normalized parent target is \(D(0,\rho_p)\setminus[X_{2,p},X_{1,p}]\). Define
\[
m=\tfrac12(X_{2,p}+X_{1,p}),\quad r=\tfrac12(X_{1,p}-X_{2,p})>0,\quad
\mathcal J_P(-e^z)=m-r\cosh z,\quad z=s+it,\ s>0,
\]
\[
a=\arccos((m-X_{5,p})/r),\qquad
b=\arccos((m-X_{3,p})/r),\qquad0<a<b<\pi.
\]
The two parent electrodes on the log diameter are \(t\in(-b,-a)\) and \(t\in(a,b)\), i.e. *opposite* slit-side accesses. The desired left-tip crest is across \(t=0\). The right-tip seam is at \(t=\pm\pi\).

**For p=3,4: a bounded right circular segment adapted to the physical disk.** Choose the following rational parameters:
\[
\begin{array}{c|cc}
p&h&T\\ \hline
3&83/100&31/10\\
4&88/100&31/10
\end{array}
\qquad
d=\frac{T^2-h^2}{2h}>0,\quad
L=\frac{T^2+h^2}{2h},
\]
\[
Q_{h,T}=\{\operatorname{Re}z>0,\ |z+d|<L\},\quad
0<s<h,\quad |t|<T<\pi,\quad b<T.
\tag{2.1}
\]
The domain is a circular segment with straight diameter on \(s=0\), not a semidisk. The Möbius map \(\psi(z)=(z-iT)/(z+iT)\) maps the segment onto a wedge of opening \(\theta=2\arctan(h/T)\); the fixed-branch power \(\psi^{\gamma}\), \(\gamma=\pi/\theta\), maps that wedge onto a half-plane. On the diameter \(z=it\) its ordered electrode images have magnitudes \(e^{\pm2\gamma\operatorname{atanh}(a/T)}\), \(e^{\pm2\gamma\operatorname{atanh}(b/T)}\). Put \(u=\gamma\operatorname{atanh}(a/T)\), \(v=\gamma\operatorname{atanh}(b/T)\). The SC half-plane cross-ratio and **exact full rectangle-foliation width** are
\[
k=\frac{\sinh(v-u)}{\sinh(v+u)},\qquad
\boxed{W_{P,p}^{\rm seg}=\frac{K(k)}{K(\sqrt{1-k^2})}},
\quad
K(k)=\int_0^{\pi/2}\frac{dt}{\sqrt{1-k^2\sin^2t}}.
\tag{2.2}
\]
The verifier uses the certified outward rational arctangent, logarithmic atanh, sinh, pi and elliptic series; the conformal mapping assertion itself is the classical analytic input.

**For p=5,...,12: a bounded right semidisk.** Take
\[
Q_R=\{s>0,\ s^2+t^2<R^2\},\qquad R=7/5,\quad b<R<\pi.
\tag{2.3}
\]
The map \(2Rz/(R^2-z^2)\) takes \(Q_R\) to the right half-plane and \(it\mapsto iB_R(t)\), where \(B_R(t)=2Rt/(R^2+t^2)\). Put \(A_R=B_R(a)\), \(B_R'=B_R(b)\), \(k=(B_R'-A_R)/(B_R'+A_R)\). Its SC rectangle foliation has
\[
\boxed{W_{P,p}^{\rm semi}=K(k)/K(\sqrt{1-k^2})}.
\tag{2.4}
\]

**Complete embedding, not just sample arcs.** Both simply connected quadrilaterals satisfy \(|t|<\pi\), so the logarithmic exponential is injective modulo the \(2\pi i\) deck group; Joukowski is injective off the slit. Every pulled-back **open horizontal SC rectangle leaf** is a simple proper arc with endpoints in \(I_9,I_1\); contractibility of the quadrilateral gives its homotopy to the \(t=0\) left-tip collar through \(I_0\), not to an A.1-forbidden one- or two-atom arc. The full horizontal foliation is therefore an **actual A.1 parent Wave** of base \((I_9,I_0,I_1)\), width exactly (2.2) or (2.4) by the Cauchy–Schwarz/constant-density rectangle argument. In particular \(P_p\ge W_{P,p}\).

For both domains \(|\cosh(s+it)|\le\cosh s\). The verifier checks the **strict whole-domain disk gate**
\[
|\mathcal J_P(-e^z)|\le|m|+r\cosh s
<|m|+r\cosh h<\rho_p
\tag{2.5}
\]
for each physical packet, with \(h=R\) for (2.3). At \(p=3\) the final normalized-coordinate margin is approximately \(0.0107\) (diagnostic, not a certificate). A disk of radius \(5/2\) used for the \(p\ge13\) tail would **not** fit periods 3 and 4, which is precisely why this new segment is necessary.

## 3. An actual-source strictly sharper upper bound

The earlier canonical-gain audit upper-bounds each source child by the **unrestricted plane-slit full-lift** SC modulus \(E_p\). Use the physical (unscaled) positive-\(x_p\) source Joukowski expression \(\mathcal J_C(e^{s+it})=x_p\cosh(s+it)\) and define
\[
a_c=\arccos(x_{4p}/x_p),\quad
b_c=\arccos(-x_{2p}/x_p),\quad
c_c=\arccos(-x_{5p}/x_p),\quad
d_c=\arccos(\alpha_p/x_p),
\]
\[
0<a_c<b_c<c_c<d_c<\pi.
\]
After reflecting the upper slit side, the four ordered electrode points of the *universal right-half-plane log cover* \(s>0,t\in\mathbb R\) are
\[
(e_1,e_2,e_3,e_4)=(\pi-d_c,\pi-c_c,\pi-b_c,\pi-a_c).
\]
The SC derivative (up to unit phase) is
\[
F'(z)=\prod_{j=1}^4(z-ie_j)^{-1/2}.
\]
The image rectangle **gap-side length** separating the two electrode sides is
\[
H=\int_{e_2}^{e_3}
\frac{dt}{\sqrt{(t-e_1)(t-e_2)(e_3-t)(e_4-t)}}
\le\frac{\pi}{\sqrt{(d_c-c_c)(b_c-a_c)}}.
\tag{3.1}
\]
Thus \(\widetilde\rho=|F'|/H\) is the voltage-one admissible lifted comparison density, and its **total area equals \(E_p\)**. To obtain the quotient density use \(\rho_{\rm per}(s,t)^2=\sum_{n\in\mathbb Z}\widetilde\rho(s,t+2\pi n)^2\); by Tonelli this preserves total area, and for each chosen lifted child path it is no smaller than the required lifted density. It does **not** assert that the plane comparison is a realized child Wave.

The checker independently reruns the exact Rouché expansion \(G_p(z)=x_p+A_pz^2+E_p(z)\) on \(|z|=R_p\), proving
\[
|A_p|R_p^2>|x_p|+\sup_{|z|\le R_p}|E_p(z)|+R_p,
\tag{3.2}
\]
as well as \(|G_p(0)|=x_p<R_p\). Therefore \(|G_p|>R_p\) on the circle and the central quadratic-like pullback component satisfies **\(V_p\subset D(0,R_p)=U_p\)**. This crucial source-domain fact is not borrowed from parent containment or a limiting chart.

The open unit box must be chosen **separately for each physical period**: the first tempting fixed box \(2<s<3\) does *not* lie outside \(U_p\) for all \(p\). The corrected verifier constructs the smallest integer \(s_p\ge2\), with \(s_p\le p\), such that
\[
x_{p,\mathrm{low}}\left(\frac12\sum_{n=0}^{24}\frac{s_p^n}{n!}-\frac12\right)>R_p.
\tag{3.3}
\]
Because \(e^{s_p}>\sum_{n=0}^{24}s_p^n/n!\) and \(e^{-s_p}<1\), this is a **strict rational certificate** for \(x_p\sinh(s_p)>R_p\). Define
\[
B_p=\{s_p<s<s_p+1,\quad 0<t<1\}.
\]
On \(B_p\), \(|x_p\cosh(s+it)|\ge x_p\sinh s>R_p\), so **every deck translate of \(B_p\) is absent from the physical source lift**. The verifier computes \(s_p=2,2,2,3,4,4,5,6,6,7\) for \(p=3,\ldots,12\), respectively, using the physical outward root packet and no numerical threshold inference. Since \(0<e_j<\pi<4\), we have \(|z-ie_j|<s_p+5\) on \(B_p\), yielding \(|F'|^2>(s_p+5)^{-4}\). By (3.1), the **missing positive energy** is
\[
\int_{B_p}\widetilde\rho^2\,dA
>\frac{(b_c-a_c)(d_c-c_c)}{\pi^2(s_p+5)^4}
>\frac{(b_c-a_c)(d_c-c_c)}{16(s_p+5)^4}
>\boxed{\frac1{5{,}000{,}000}}.
\tag{3.4}
\]
The last strict inequality is verified separately for each \(p\) from the outward angle intervals, including the gap \((b_c-a_c)(d_c-c_c)>9/100\). Restricting the full admissible quotient metric to \(\Omega'_p\) removes the positive energy of \(B_p\) without changing any physical child path length; hence
\[
\boxed{C_p\le E_p-\frac1{5{,}000{,}000}<E_p\quad(3\le p\le12).}
\tag{3.5}
\]
Conjugation gives the identical lower-child upper bound. We use actual bounded **child** domains and a period-specific deleted positive-area set, not an unproved monotonicity slogan or a fictitious child optimizer.

## 4. Why this is not KKL-style Wave amplification

The physical immersion is set-valued: \(\iota^*I_0=(S_{18},S_{19},S_0,S_1,S_2)\), \(\iota^*I_1=(S_3,S_4)\), \(\iota^*I_9=(S_{16},S_{17})\). It must **never** be replaced by the independent degree-two covering map \(f_*(S_j)=I_{j\bmod10}\). The attached source sides do not acquire fictitious target ideal endpoints.

The old and unchanged KKL A.11 serial inequality for a **leafwise two-child pairable** parent remains
\[
W_{\rm parent}\le W_+\oplus W_-,\qquad
P_{p,\mathrm{pair}}\le C_p/2,\qquad
2/C_p-1/P_{p,\mathrm{pair}}\le0.
\tag{4.1}
\]
Our *unrestricted* independent \(D_p>0\) says \(P_p>C_p/2\), so in fact \(P_p>P_{p,\mathrm{pair}}\) **for all p>=3**. Independent maximization does not commute with simultaneous proper restriction, without contradicting (4.1). It does **not** construct three jointly compatible maximizers or any iterative pullback amplification. The *literal buffered A.2.3 canonical arc weights* for these arcs were already shown to vanish; they must not be inverted. Any KKL-style depth amplification requires additional compatibility and nonzero buffered-weight hypotheses not proved here.

## 5. Verifier scope, hostile review, and open questions

Run from the repository root:

~~~sh
python -B research/independent_audits/tip_family_finite_p_wave_gain_20261116/verify.py
python -B -m unittest discover -s research/independent_audits/tip_family_finite_p_wave_gain_20261116 -p 'test_*.py' -v
~~~

The new verifier imports and reruns the unchanged limiting/canonical-gain/sandwich and finite-primitive source packets read-only. It uses exact \(\mathbb Q\) and outward grid \(2^{-512}\) elementary/elliptic series with rigorous tail bounds. It checks individually: the distinguished physical root and sign of \(A_p\); all full-domain parent disk and deck gates; the independent complex Rouché source gate; the **actual** child missing-energy gap; and strict reciprocals. The dedicated add-only workflow also invokes the original research-validation and weighted Lean workflows at the PR's exact head commit. These checks certify **arithmetic premises** only. Classical SC uniformization, the foliation/homotopy A.1 argument, covering-periodized conformal metrics, and KKL A.11 are **analytic arguments in this note**, not machine-proved theorems. M remains conditional.

Hostile-review points resolved: (i) do not use \(x_j\) in place of \(x_{jp}\), or the negative-order \(A_p\) scale; (ii) \(|t|<\pi\) for the *entire* parent foliation prevents quotient self-overlap; (iii) the \(p=3,4\) physical disk requires a circular segment and is checked with full complex-domain bounds; (iv) the removed child energy lies outside independently checked \(V_p\subset U_p\), and is counted **once** in the universal cover; (v) normalization is by the SC electrode-gap length H, not the wrong rectangle side; (vi) parent embedded widths are **lower** bounds whereas actual-source metric areas are **upper** bounds, and inversion reverses inequalities; (vii) no output is called a canonical optimizer or positive buffered WAD.

**Proved:** the ten finite strict margins, with the merged tail yielding the all-\(p\ge3\) sign; and, conditional on M, strict inequality of the unrestricted and pairable-parent suprema. **Numerical-only:** approximate diagnostic values of particular constructed widths if quoted; never the sign theorem. **Still open:** exact unrestricted supremal widths and attainment; convergence to limiting unrestricted suprema; joint optimizer compatibility and iterated KKL amplification; and the independent proof of physical ideal marking M. None of these open problems is silently promoted into a theorem.
