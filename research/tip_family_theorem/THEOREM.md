# The near-\(-2\) real primitive-tip family: a typed all-period theorem

**Status (2026-11-16).** This is a *synthesis with an explicit trust boundary*, not a new computer-assisted proof of complex dynamics. The parameter, real-order, and quadratic-like realization claims below are proved in the cited interval/analytic audits for **all** \(p\ge3\). The physical Hubbard-tree and ideal-boundary claims follow from the specified arguments **using named published general theorems**; their topological invocation is not formalized in Python or Lean. The harmonic equality is exact for the **specified circular/logarithmic Wave** when its KKL path/conformal-width identification is applied. It is **not** a claim about every Wave, the unrestricted maximal KKL Wave, or strict gain. The disaggregated referee ledger is [AUDIT.md](AUDIT.md); [verify_chain.py](verify_chain.py) checks independently recorded premises and cross-document invariants read-only.

## 1. Statement: one theorem with its exact domains of validity

Put \(f_c(z)=z^2+c\), \(x_j(c)=f_c^{\,j}(0)\) (**not** \(G_c^j(0)\)), \(G_c=f_c^{\,p}\), \(P_p(c)=x_{6p}(c)+x_{3p}(c)\), \(q_p=4^{-p}\), \(A_p(c)=\prod_{j=1}^{p-1}2x_j(c)\), and \(\tau_p=A_p x_p\). The *tip* refers to the inner **period-three** Chebyshev portrait for the physical **\(p\)-return**, hence to iterates \(3p,6p\), not to a period-\(p\) Chebyshev tip.

**Parameter-chart convention (part of the theorem, not implicit).** For \(3\le p\le12\), let \(s_p\) be the exact rational decimal seed listed as SEEDS[p] in [the ten-period verifier](../independent_audits/real_primitive_tip_family_unconditional_20261116/verify.py); set
\[
  \mathcal C_p^{\rm fin}=(s_p-10^{-75},\,s_p+10^{-75}).
\]
For \(p\ge13\), set
\[
\mathcal C_p^{\rm large}=\{-2+\varepsilon:\ 14q_p<\varepsilon<16q_p,\ 
 |x_p|<14q_p,\ -2<\tau_p<1/4\}
\]
and let \(\mathcal K_p\subset\mathcal C_p^{\rm large}\) be the *signed kneading subchart*: \(x_1<0\), \(x_j>0\) for \(2\le j\le p\), and the six \(G\)-returns \((x_p,x_{2p},\ldots,x_{6p})\) have signs \(+--+-+\). This condition contains **no equation** \(P_p=0\). In the theorem, “unique in its chart” means unique in \(\mathcal C_p^{\rm fin}\) for the first ten periods and unique in \(\mathcal K_p\) thereafter. Nothing asserts uniqueness in the entire maximal real primitive component or amongst all real roots of \(P_p\).

**Main theorem (all integers \(p\ge3\), with precisely typed analytic interpretation).** For every such \(p\):

**(A) Selected tip and quadratic-like realization — proved.** There exists exactly one \(c_p\) in the chart just specified with \(P_p(c_p)=0\). It has \(x_{3p}<0<x_{6p}\), is a simple root, and has the signed prefix and returns above. For \(p\ge13\),
\[
 \left|c_p+2-\frac{3\pi^2}{2}4^{-p}\right|<500p\,16^{-p},
 \qquad c_p+2\sim\frac{3\pi^2}{2}4^{-p}\quad(p\to\infty).
 \tag{1}
\]
The **strict** physical real orders are
\[
 x_{2p}<x_{5p}<x_{3p}<0<x_{6p}<\alpha_p<x_{4p}<x_p,\qquad
 G_p(\alpha_p)=\alpha_p, \tag{2}
\]
\[
 -x_p<-x_{4p}<x_{2p}<x_{5p}<-\alpha_p<x_{3p}
 <x_{6p}<\alpha_p<-x_{5p}<-x_{2p}<x_{4p}<x_p. \tag{3}
\]
Here \(G_p=f_{c_p}^{\,p}\) is increasing on \([-x_p,0]\), decreasing on \([0,x_p]\), and there is no earlier central critical return. With
\[
 R_3=1/4,\quad R_p=2^{-p}\ (p\ge4),\quad
 U_p=D(0,R_p),\quad V_p=\operatorname{component}_{0}(G_p^{-1}(U_p)),
\]
\(V_p\Subset U_p\) and \(G_p:V_p\to U_p\) is **proper holomorphic of degree 2**, even though the *global* polynomial \(f^{p}\) has degree \(2^p\). The certified \(p\)-return Rouché gap exceeds \(1/25\); for \(p\ge13\) it follows uniformly from
\[
 |A_p|R_p^2-|x_p|-T_p-R_p
 \ge 3/20-12\,4^{-p}-1/128-2^{-p}>1/25.
 \tag{4}
\]
No uniform bound on the modulus of the *subsequently shrunken* \(3p\)-return collars is claimed.

**(B) Actual little Julia sets and Hubbard tree — mathematical consequence using external theorems, not machine formalized.** Put \(t_p=x_{6p}=-x_{3p}>0\) and
\[
 K_0=[-t_p,t_p],\quad K_1=[x_{4p},x_p],\quad
 K_2=[x_{2p},x_{5p}],\quad T_p=[x_{2p},x_p].
\]
The properly restricted \(G_p\) admits a **prime, primitive period-three quadratic-like renormalization** whose three *actual* small filled Julia sets are \(K_0,K_1,K_2\), not merely suspected invariant orbit intervals. Its full KKL Hubbard tree is \(T_p\), with dividing fixed point \(\alpha_p\), and
\[
 T_p'=G_p^{-1}(T_p)\cap V_p=[-x_p,x_p].
\]
More specifically, for \(h_p(w)=A_pG_p(w/A_p)\), the component at 0 of \((h_p^3)^{-1}(D(0,3/10))\) maps properly with degree two into \(D(0,3/10)\) and has a **separate** normalized Rouché gap \(>1/8\). The actual little-Julia-set identification uses the Douady–Hubbard Straightening Theorem and the connectedness criterion; primeness uses McMullen's almost-disjointness theorem; the dendrite and repelling-periodic-point facts use the standard Misiurewicz theorem. The proof and the exact references are in §§3–4 below.

**(C) Physical KKL ideal marking and distinct operators — mathematical consequence using external theorems, finite tables certified.** In the *inner* ideal-boundary circle of \(U_p\setminus T_p\), mark the **five** increasing real cuts
\[
 (a,b,d,e,h)=(x_{5p},x_{3p},x_{6p},\alpha_p,x_{4p}).
\]
Their two slit-side prime ends give **ten** cyclic target atoms \(I_0,\ldots,I_9\), in the fixed order
\[
\begin{array}{c|l}
0&K2\_terminal\\1&edge\_K2\_K0\_upper\\2&K0\_upper\\
3&edge\_K0\_alpha\_upper\\4&edge\_alpha\_K1\_upper\\
5&K1\_terminal\\6&edge\_alpha\_K1\_lower\\
7&edge\_K0\_alpha\_lower\\8&K0\_lower\\9&edge\_K2\_K0\_lower
\end{array}
\]
The **ten** increasing inverse cuts in \(T_p'\) are
\[
 (-x_{4p},x_{2p},x_{5p},-\alpha_p,x_{3p},x_{6p},
       \alpha_p,-x_{5p},-x_{2p},x_{4p}),
\]
giving **twenty** source inner atoms \(S_0,\ldots,S_{19}\). **Each outer ideal circle contributes one whole-component atom** (not ten or twenty).

Exactly **one** new tree attachment occurs:
\[
 T_p'\setminus T_p=[-x_p,x_{2p}),\qquad
 \text{source attachment sides }S_{19},S_0,S_1.
\]
For the **unbranched covering** \(G_p:V_p\setminus T_p'\to U_p\setminus T_p\), its ideal-boundary *pushforward* is
\[
 G_{p*}(S_s)=I_{s\bmod10}\quad(0\le s<20).                    \tag{5}
\]
For the different **identity immersion** \(\iota:V_p\setminus T_p'\hookrightarrow U_p\setminus T_p\), the set-valued *proper restriction* of target atoms has consecutive source blocks
\[
\begin{array}{c|l}
 \iota^*I_0&P_0=[18,19,0,1,2]\\
 \iota^*I_1&P_1=[3,4]\\
 \iota^*I_2&P_2=[5]\\
 \iota^*I_3&P_3=[6]\\
 \iota^*I_4&P_4=[7,8,9]\\
 \iota^*I_5&P_5=[10]\\
 \iota^*I_6&P_6=[11,12,13]\\
 \iota^*I_7&P_7=[14]\\
 \iota^*I_8&P_8=[15]\\
 \iota^*I_9&P_9=[16,17]
\end{array}\quad
 (|P_i|)=(5,2,1,1,3,1,3,1,1,2).                            \tag{6}
\]
Every block is end-proper; only \(P_0\) is **not fully proper** because the three attached source sides map into **target interior**, not pointwise to an ideal target boundary. Neither \(G_{p*}\) nor \(\iota^*\) is a substitute for the other.

For proper target paths of a fixed admissible relative-endpoint class, with right real impression \(q_{\rm right}\in(x_{5p},-\alpha_p)\), a crossing left impression \(w\in(-x_{4p},x_{2p})\) yields **two** filtered proper source restrictions
\[
 (S_3,S_1),\quad(S_{19},S_{17}),
\]
whereas an avoiding \(w<-x_p\) yields **one**, \((S_3,S_{17})\). The respective *inclusive* shortest source-arc atom lengths are **\(3,3,7\)**. Their **cover-pushed**, *not immersion-pushed*, endpoint pairs are \((I_3,I_1),(I_9,I_7),(I_3,I_7)\), with shortest target lengths **\(3,3,5\)**. They all pass the strict \(>2\)-atom KKL short-path filter, and their endpoints are in different \(\iota^*\)-blocks. The \(2\)-versus-\(1\) claim concerns these specified proper isotopy classes (or actual circles certified wholly in the proper source), **not every curve, a duplicate full lift, or a failure of KKL's set-valued theorem**.

**(D) Old edges, closed crests, and a named circular-wave identity.** Count each *physical* real edge only once, notwithstanding two slit-side ideal accesses:
\[
 E_0=(a,b),\quad E_1=(d,e),\quad E_2=(e,h).
\]
Writing output-edge rows and input-edge columns, their occurrence matrix and positive left Perron eigenvector are
\[
 M=\begin{pmatrix}0&0&1\\1&0&1\\1&1&0\end{pmatrix},
 \quad\det(zI-M)=(z+1)(z^2-z-1),\quad
 \rho(M)=\varphi=\frac{1+\sqrt5}{2},\quad
 (\varphi,1,\varphi)M=\varphi(\varphi,1,\varphi).              \tag{7}
\]
The target **atomic zero-old-edge** types are \(\{I_0,I_2,I_5,I_8\}\). The source *inclusion* zero types are \(\{S_0,S_1,S_2,S_5,S_{10},S_{15},S_{18},S_{19}\}\), versus the different *cover-pushed* zero types \(\{S_0,S_2,S_5,S_8,S_{10},S_{12},S_{15},S_{18}\}\). The parent base \(B=(I_9,I_0,I_1)\) has **closed** crest \(I_0\); the two cover-pushed child bases \((I_1,I_2,I_3)\) and \((I_7,I_8,I_9)\) have crests \(I_2,I_8\). Each of these **three closed atomic crest types** has no old edge; no statement about *all fine subsectors* or arbitrary later iterates follows.

There is, **for each \(p\)**, a physically admissible *orbit-centred round crossing annulus* with
\[
 m_p=(x_{2p}+x_{5p})/2,\quad r_{{\rm in},p}=(x_{5p}-x_{2p})/2,\quad
 r_{{\rm gate},p}=\min\{-\alpha_p-m_p,\ x_{4p}+m_p\},\qquad
 0<r_{{\rm in},p}<r_{{\rm gate},p},                         \tag{8}
\]
and leaves \(|z-m_p|=r\) for \(r_{{\rm in},p}<r<r_{{\rm gate},p}\). The real gates and **whole-disk containment in \(V_p\)** are interval-certified for \(3\le p\le12\) and deduced from the explicit normalized \(G_p\) bounds for \(p\ge13\). Its **algebraic logarithmic-rectangle coefficients** satisfy
\[
 L_p=\log(r_{{\rm gate},p}/r_{{\rm in},p}),\qquad
 W_{\rm round}^{\rm sym}=\frac{L_p}{2\pi},\quad
 W_+^{\rm sym}=W_-^{\rm sym}=\frac{L_p}{\pi},
 \quad\boxed{\frac1{W_{\rm round}^{\rm sym}}
       =\frac1{W_+^{\rm sym}}+\frac1{W_-^{\rm sym}}}.       \tag{9}
\]
**Exact analytic scope:** interpreting these symbolic values as widths of the *actual* parent and two selected proper KKL Wave sublaminations requires the log-rectangle, univalence and conformal/extremal-width identification in KKL Appendix A.2–A.3 and the explicit slit/homotopy argument. This is the separately identified analytic step in §3, **not a conclusion of a finite atom table or of Lemma A.11 alone**. In that specified model the harmonic identity holds as equality; KKL's general restriction lemma supplies only an **inequality**. In particular (9) is **not strict Wave amplification**, not a canonical/maximal-Wave identity, and not a period-determined width.

## 2. Corollaries and conjectures (not additional clauses of the theorem)

**Corollary 1 — all-period realization with no \(p=12/13\) gap (proved).** The ten adjacent rational packets for \(p=3,\ldots,12\), including a direct \(p=3\) degree-two Rouché certificate, and the **entire** quantified chart proof for \(p\ge13\) cover every integer \(p\ge3\). The \(p\)-return gap \(>1/25\) and the **different** normalized \(3p\)-return gap \(>1/8\) both hold. Local finite-seed uniqueness does **not** become global component uniqueness at the join.

**Corollary 2 — convergence of the *orbit-centred round witness* (proved arithmetic/complex-domain estimate; actual-width reading uses (9)).** Let \(g_\tau(w)=w^2+\tau\) and let \(\tau_\star\) be the unique root of \(g_\tau^6(0)+g_\tau^3(0)=0\) in \((-1.795,-1.785)\). With \(u_j=g_{\tau_\star}^{\,j}(0)\) and \(a_\star=(1-\sqrt{1-4\tau_\star})/2\), define
\[
 R_{{\rm rad},\infty}
 =\frac{\min\{2a_\star+u_2+u_5,\;-2u_4-u_2-u_5\}}{u_2-u_5},
 \qquad W_{{\rm rad},\infty}=\frac{\log R_{{\rm rad},\infty}}{2\pi}.   \tag{10}
\]
The first branch of the minimum is strictly active. For every \(p\ge13\),
\[
 \left|\frac{r_{{\rm gate},p}}{r_{{\rm in},p}}-R_{{\rm rad},\infty}\right|
   <150000000\,4^{-p},\quad
 \left|W_{\rm round,p}^{\rm sym}-W_{{\rm rad},\infty}\right|
   <7000000\,4^{-p}.                                       \tag{11}
\]
The independently outward-certified limits are
\(5.1383080<R_{{\rm rad},\infty}<5.1383083\) and
\(0.2604925<W_{{\rm rad},\infty}<0.2604928\).
This is a theorem **only about the orbit-defined round witness**, not convergence of an unrestricted KKL-maximal Wave \(W_p^*\). The latter is an open extremal problem; the finite/limiting upper envelopes in the canonical-width audit are **upper bounds**, not attained KKL Waves.

**Corollary 3 — chosen radii are not canonical (proved algebraically).** For the *different*, optional \(-3x_p/4\)-centred family of annuli with radii \(x_p/16\) and \((p-1)x_p/(8p)\), the ratio is **by choice** \(2(p-1)/p\) and the symbolic parent width tends to \(\log2/(2\pi)\). At \(p=3\), the **source-locked physical** PR #68 annulus instead has centre \(-9/64\) and radii \((3/256,1/64)\); at \(p=4\), the native example has centre \(-17/512\) and radii \((1/256,3/512)\). They agree in **ratio**, not in individual circles. Taking a proper subannulus changes width at fixed \(p\), so “period determines Wave width” is false even at \(p=3\).

**Corollary 4 — finite four-push crest collars (strict interval arithmetic, conditional conformal interpretation).** For the *specified* native \(p=3\) parent Wave and the chosen \(-3x_p/4\) parents for \(p\ge4\), the independent whole-radius-bin audits certify the selected four-push q-side circular-collar ratio \(c_p^*\) for each \(3\le p\le16\); e.g.
\[
 c_3^*\in(0.98017,0.98038),\quad
 c_{12}^*\in(0.39680,0.39684),\quad
 c_{13}^*\in(0.39229,0.39233),\quad
 c_{16}^*\in(0.38261,0.38265).
\]
These are ratios for the *maximal connected circular subcollar of that fixed parent with the selected fourth-stage terminal gate*, **not** a supremum over all centres or arbitrary KKL Waves. The real/interval optimization is certified for those 14 periods; its interpretation as actual conformal descendant widths still imports the identified KKL path, injectivity and strip-width theorems. The terminal upper/lower closed crests touch opposite sides \(I_1,I_9\) of the **same** old edge \(E_0\), not two independent edges.

**Conjecture 1 — positive selected four-push ratio limit (OPEN; numerical evidence only).** The finite ratios in Corollary 4 approach
\[
 c_\infty\mathrel{\stackrel{?}{=}}
 0.3470049860435258\ldots>0,\qquad
 c_p^*\mathrel{\stackrel{?}{=}}
 \frac{A_\infty}{\log(2-2/p)}+O(4^{-p}),
 \quad A_\infty\approx0.2405255277.
\]
The suggested \(c_\infty(1+1/(p\log2)+O(p^{-2}))+O(4^{-p})\) expansion is **conjectural**, not a verified all-period rate. It needs all-\(p\) complex \(C^1\) control through four compositions, persistence of the KKL proper path class, endpoint transversality and noncancellation. The \(p\ge13\) *basic* quadratic-like theorem does **not** supply that transport estimate.

**Open problem 2 — canonical-width convergence.** With a fixed KKL base \(B=(I_9,I_0,I_1)\) and crest containing \(I_0\), let \(W_p^*\) be the supremum of conformal widths over **all** A.1-admissible parent laminations, and let \(W_{p,2}^*\le W_p^*\) impose the two prescribed surviving restrictions. Neither convergence of \(W_p^*\), equality of these two suprema, nor their exact values follows from (9)–(11). The canonical-width audit gives the separate inequality \(W_{\rm round,p}^{\rm sym}\le W_{p,2}^*\le W_p^*\le Q_p\) *in the declared KKL slit/width setting*, with a convergent **full-path upper envelope** \(Q_p\), but the two bounding families need not coincide.

**Other open problems.** Uniqueness across a maximal real primitive window beyond \(\mathcal C_p\); arbitrary fine zero-old-edge subsector escape, strict Wave gain, all-Wave uniform four-push transport, global H1–H4/UPTCR/MLC; and a machine-checked formalization of the external complex-analytic/topological arguments. None is proved here.

## 3. Complete dependency proof skeleton (type of input at every link)

All paths are relative to this directory. “Verifier” means the *exact rational/finite part* it checks, never an implementation of the named external theorem. Each step identifies an exact section, program and where relevant immutable data.

| Step / inference | Establishing argument (exact source and section) | Reproducer and what it checks |
|---|---|---|
| **1. Define the branch and its index.** \(x_j=f^j(0)\), six \(G\)-return signs and \(P_p\). | [Uniform NOTE §1](../independent_audits/real_primitive_tip_family_uniform_20261116/NOTE.md#1-which-tips-exact-branch-and-kneading); [Unconditional NOTE, “Finite unconditional theorem”](../independent_audits/real_primitive_tip_family_unconditional_20261116/NOTE.md); [All-p NOTE “Statement and precise scope”](../independent_audits/real_primitive_tip_family_all_p_20261116/NOTE.md). | [uniform/verify.py](../independent_audits/real_primitive_tip_family_uniform_20261116/verify.py), [unconditional/verify.py](../independent_audits/real_primitive_tip_family_unconditional_20261116/verify.py): strict root signs, derivatives, branch; their frozen results JSONs. |
| **2. Cover all periods without extrapolation.** Finite roots in \(\mathcal C_p^{\rm fin}\); large root in signed \(\mathcal K_p\), with uniqueness, error (1). | [Unconditional NOTE “Finite unconditional theorem”](../independent_audits/real_primitive_tip_family_unconditional_20261116/NOTE.md) for \(3\le p\le12\); [All-p NOTE, Proof I–III and its table of exclusion intervals](../independent_audits/real_primitive_tip_family_all_p_20261116/NOTE.md) for every \(p\ge13\). | [unconditional/verify.py](../independent_audits/real_primitive_tip_family_unconditional_20261116/verify.py), [all-p/verify.py](../independent_audits/real_primitive_tip_family_all_p_20261116/verify.py) functions verify_universal_constants, verify_model_and_cut_order, verify_whole_kneading_window and verify_period13_bracket. Test boundary \(p=12\) against \(p=13\) in verify_chain.py. |
| **3. Strict physical order and degree-two \(p\)-return.** O1, O2, intermediate signs, whole-disk Rouché gap. | [Unconditional NOTE “Direct degree-two Rouché theorem”](../independent_audits/real_primitive_tip_family_unconditional_20261116/NOTE.md); [All-p NOTE Proof II and IV](../independent_audits/real_primitive_tip_family_all_p_20261116/NOTE.md), particularly (9), (11), (R). | Their two verify.py programs; source [native PR #68 regenerate.py](../native_wave_transfer/regenerate.py) and [period-four regenerate_period4.py](../native_wave_transfer/regenerate_period4.py) with --check. Standard **Rouché's theorem** (reference R1), not proved by Python. |
| **4. Genuine \(3p\)-return exists separately.** Normalized \(h_p^3\), \(>1/8\) disk gap, compact degree-two component, phase neighborhoods. | [Prime-end identification NOTE §1 “New uniformly proper three-return restriction”](../independent_audits/real_primitive_tip_family_prime_end_identification_20261116/NOTE.md#1-new-uniformly-proper-three-return-restriction), eqs. (1)–(3). | [prime-end/verify.py](../independent_audits/real_primitive_tip_family_prime_end_identification_20261116/verify.py), check_all_finite and check_large_model; analytic **Rouché and Riemann–Hurwitz** (R1–R2). Distinct \(>1/8\) from step 3 \(>1/25\). |
| **5. Identify actual small Julia intervals.** Critical Chebyshev portrait and straightening to \(z^2-2\), \(K_0,K_1,K_2\). | [Prime-end NOTE §2 “The little Julia sets really are intervals”](../independent_audits/real_primitive_tip_family_prime_end_identification_20261116/NOTE.md#2-the-little-julia-sets-really-are-intervals), (4)–(5); intermediate domains paragraph. | Polynomial identities from steps 2–4; external **Douady–Hubbard** connectedness criterion/straightening (R3). **No mechanical verification** of DH85. |
| **6. Prime, primitive, dendrite and true KKL tree.** Exclude period two; all little sets disjoint; \(T_p\) is the minimal Hubbard continuum; \(\alpha_p\) dividing. | [Prime-end NOTE §3 “Primeness, periodic repulsion and local connectivity”](../independent_audits/real_primitive_tip_family_prime_end_identification_20261116/NOTE.md#3-primeness-periodic-repulsion-and-local-connectivity) and [§4 Lemma 4](../independent_audits/real_primitive_tip_family_prime_end_identification_20261116/NOTE.md#4-kkls-actual-hubbard-tree-and-ideal-boundary-circles). | External **McMullen Theorem 7.3** (R4), **Misiurewicz dendrite/local connectivity** (R5) and **KKL §§2.3–2.5** (R7); not Lean proofs. |
| **7. Prime ends and attachment.** Actual ten/twenty inner marking, one outer atom each, complete \(T_p'\) and single attached component. | [Prime-end NOTE §4 Lemma 5 and §5 “Single attachment”](../independent_audits/real_primitive_tip_family_prime_end_identification_20261116/NOTE.md#5-attachment-covering-and-immersion-explicit-tables); [Uniform NOTE §2, eqs. (2)–(4), (8)](../independent_audits/real_primitive_tip_family_uniform_20261116/NOTE.md). | [prime-end/verify.py](../independent_audits/real_primitive_tip_family_prime_end_identification_20261116/verify.py) for finite inputs, [native PR #68](../native_wave_transfer/regenerate.py) and [period 4](../native_wave_transfer/regenerate_period4.py) for source geometry; **Carathéodory** (R6) and **KKL §6.1 Props. 6.5–6.6** (R7) supply the analytic/topological meaning. |
| **8. Distinct \(G_*\) vs. \(\iota^*\), 2/1 filters.** Covering degree two; ten disjoint immersion blocks; source lengths 3,3,7 and covering 3,3,5. | [Prime-end NOTE §5 “Covering”, “Immersion”, “Old real edges and filtered proper restrictions”](../independent_audits/real_primitive_tip_family_prime_end_identification_20261116/NOTE.md#5-attachment-covering-and-immersion-explicit-tables); [Unconditional NOTE “Hostile review: correction”](../independent_audits/real_primitive_tip_family_unconditional_20261116/NOTE.md); source-locked [PR #68 manifest](../native_wave_transfer/experiment_manifests/tip_pr68.json). | [uniform/verify.py](../independent_audits/real_primitive_tip_family_uniform_20261116/verify.py), [unconditional/verify.py](../independent_audits/real_primitive_tip_family_unconditional_20261116/verify.py), [prime-end discrete Lean](../independent_audits/real_primitive_tip_family_prime_end_identification_20261116/RealPrimitiveTipPrimeEndDiscrete.lean), [TipKKLTreeMarking.lean](../../TipKKLTreeMarking.lean); **KKL Appendix A.1/A.3.1–A.3.4** (R7) for proper restriction semantics. |
| **9. Edges, spectral and closed crests.** Cut images \((2,4,4,3,0)\) give (7); incidence yields zero types. | [Uniform NOTE §2 proof](../independent_audits/real_primitive_tip_family_uniform_20261116/NOTE.md); [Prime-end NOTE §5 old edges](../independent_audits/real_primitive_tip_family_prime_end_identification_20261116/NOTE.md); [native PR #68 manifest](../native_wave_transfer/experiment_manifests/tip_pr68.json), [native p4 manifest](../native_wave_transfer/experiment_manifests/primitive4_tip12.json). | [uniform/verify.py](../independent_audits/real_primitive_tip_family_uniform_20261116/verify.py), [unconditional/verify.py](../independent_audits/real_primitive_tip_family_unconditional_20261116/verify.py), [RealPrimitiveTipDiscrete.lean](../independent_audits/real_primitive_tip_family_uniform_20261116/RealPrimitiveTipDiscrete.lean), verify_chain.py. Perron–Frobenius theorem R8 or direct positive eigenvector/positive power. |
| **10. Physically admissible round gate.** Equation (8), whole disks for finite and large \(p\); separate native \(p=3,4\) waves. | [Unconditional NOTE “Source-defined radial witness”](../independent_audits/real_primitive_tip_family_unconditional_20261116/NOTE.md); [Canonical-width NOTE §§1–2](../independent_audits/real_primitive_tip_family_canonical_width_20261116/NOTE.md#2-certified-round-lower-witnesses-theorem-value-rate); [Uniform NOTE §3](../independent_audits/real_primitive_tip_family_uniform_20261116/NOTE.md#3-one-explicit-width-normalization-and-why-it-is-not-canonical). | [unconditional/verify.py](../independent_audits/real_primitive_tip_family_unconditional_20261116/verify.py), [canonical-width/verify.py](../independent_audits/real_primitive_tip_family_canonical_width_20261116/verify.py), both native regenerate.py --check. |
| **11. Harmonic Wave-width identity, with the correct analytic boundary.** Log-strip heights \(2\pi,\pi,\pi\) yield (9), but not a general Wave equality. | [Uniform NOTE §2, (7) and its final proof paragraph](../independent_audits/real_primitive_tip_family_uniform_20261116/NOTE.md); [Native RESULT/specification](../native_wave_transfer/RESULTS.md), [Canonical-width NOTE §1](../independent_audits/real_primitive_tip_family_canonical_width_20261116/NOTE.md); [Prime-end NOTE §5](../independent_audits/real_primitive_tip_family_prime_end_identification_20261116/NOTE.md). | Symbolic coefficients in [native PR #68 manifest](../native_wave_transfer/experiment_manifests/tip_pr68.json) and [uniform/results.json](../independent_audits/real_primitive_tip_family_uniform_20261116/results.json); **KKL Appendix A.2 (conformal width), A.3.2 Lemma A.11 (only inequality)** (R7), classical extremal rectangle formula R9, plus the stated geometric univalence/homotopy. |
| **12. Sharp separation of proved convergence, finite conditional transport, and numerical conjectures.** Round witness tends to (10); selected 4-push \(c_p^*\) finite only, canonical \(W_p^*\) unknown. | [Canonical-width NOTE §§2–4](../independent_audits/real_primitive_tip_family_canonical_width_20261116/NOTE.md); [Crest finite NOTE “six certified collars”](../independent_audits/crest_transport_tip_family_20261116/NOTE.md); [Crest asymptotics NOTE “Certified complete circular-collar data”, “Numerical conjecture”](../independent_audits/crest_transport_asymptotics_20261116/NOTE.md). | [canonical-width/verify.py](../independent_audits/real_primitive_tip_family_canonical_width_20261116/verify.py), [crest finite/verify.py](../independent_audits/crest_transport_tip_family_20261116/verify.py), [crest asymptotics/verify.py](../independent_audits/crest_transport_asymptotics_20261116/verify.py) and locked JSON. These finite scripts **do not prove the limiting transport conjecture**. |

### Exactly which external theorems are imported?

1. **R1 — Rouché's theorem.** L. V. Ahlfors, *Complex Analysis*, 3rd ed. (McGraw–Hill, 1979), **Ch. 4, §5.2, corollary to Theorem 18 (argument principle)**, Rouché's theorem (the version for a strict boundary inequality counting zeros with multiplicity). Used in steps 3–4, with the complete-disc error estimates checked by the cited programs.
2. **R2 — Riemann–Hurwitz formula.** O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics **81** (Springer, 1981), **§17.14, “The Riemann–Hurwitz Formula”**, the finite-branched-cover formula (and its standard bordered/Jordan-domain variant). Used to identify a connected proper degree-two component with one simple critical point in step 4.
3. **R3 — Polynomial-like straightening and connectivity.** A. Douady and J. H. Hubbard, “On the dynamics of polynomial-like mappings,” *Annales scientifiques de l'École Normale Supérieure*, 4e série, **18** (1985), 287–343, **Proposition 2** (connectedness criterion) and **Theorem 1** (Straightening Theorem), §1 (restrictions and filled Julia sets), [published article](https://doi.org/10.24033/asens.1491). Used in step 5.
4. **R4 — Almost-disjoint little Julia sets.** C. T. McMullen, *Complex Dynamics and Renormalization*, Annals of Mathematics Studies **135**, Princeton University Press (1994), **Theorem 7.3** (“Almost disjoint Julia sets”), [author's text](https://abel.math.harvard.edu/~ctm/papers/home/text/papers/real/book.pdf). Used in step 6 **only** to exclude a degree-two period-two renormalization.
5. **R5 — Misiurewicz dendrite and periodic repulsion.** M. Lyubich, *Conformal Geometry and Dynamics of Quadratic Polynomials*, **Theorem 27.4**, [author's monograph](https://www.math.stonybrook.edu/~mlyubich/book.pdf); also J. Milnor, *Dynamics in One Complex Variable*, 3rd ed., Annals of Mathematics Studies **160**, Princeton University Press (2006), §17 (subhyperbolic/PCF local connectivity); the [freely available draft](https://abel.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf) numbers **Corollary 17.4 and Theorem 17.5**. Used for global \(f\)'s postcritically finite, nonperiodic critical orbit, local connectivity/dendrite and periodic repulsion; do not transfer draft numbering to other editions without checking.
6. **R6 — Carathéodory boundary extension/prime ends.** C. Carathéodory, “Über die Begrenzung einfach zusammenhängender Gebiete,” *Mathematische Annalen* **73** (1913), 323–370, boundary-extension theorem for locally connected boundaries, applied to the slit annuli **after a crosscut**; the concrete upper/lower local-sector argument is in [prime-end NOTE §4, Lemma 5](../independent_audits/real_primitive_tip_family_prime_end_identification_20261116/NOTE.md). The external theorem is not a statement that every non-locally-connected ambient puzzle has this slit marking.
7. **R7 — KKL marking and Wave definitions/lemmas.** J. Kahn, A. Kapiamba and M. Lyubich, “MLC for parabolically bounded primitive renormalization,” **arXiv:2606.27272v1 (2026)**, [available research preprint](https://arxiv.org/abs/2606.27272v1): **§2.1** quadratic-like maps, **§2.3** prime/primitive, **§2.4** dividing fixed point, **§2.5** Hubbard tree, **§6.1 Propositions 6.5–6.6** for attachment and immersion, **Appendix A.1** proper marked paths and the \(>2\)-atom filter, **A.2.1–A.2.3** conformal/extremal width, **A.3.1** covering pushforward, **A.3.2 Lemma A.11 and Proposition A.12** set-valued restriction and width *inequality*, **A.3.4** breakable paths. The identifier is a publicly posted **preprint**, not a claim of peer-reviewed journal publication.
8. **R8 — Perron–Frobenius theorem.** F. R. Gantmacher, *The Theory of Matrices*, Vol. II (Chelsea, 1959), Ch. XIII, §2, theorem on a primitive nonnegative matrix's simple positive spectral radius. Applied after checking \(M^4>0\); the displayed eigenvector also gives a direct calculation.
9. **R9 — Extremal length/rectangle modulus and conformal invariance.** L. V. Ahlfors, *Conformal Invariants: Topics in Geometric Function Theory* (McGraw–Hill, 1973), Ch. I §§1–4 (extremal length and rectangle), and KKL Appendix A.2. The log map \(z\mapsto\log(z-m_p)\) turns the specified round collar into radial length \(L_p\) and angular heights \(2\pi\) or \(\pi\), giving (9) **for that collar**, subject to the stated KKL restriction identification.

## 4. Audit and reproducibility contract

Read [AUDIT.md](AUDIT.md) before citing this theorem as unconditional in a different meaning. In particular the archived **uniform** note predates the later interval certificates and contains one **incorrect** prose sentence about avoiding-path short arcs; the new theorem supersedes that sentence but changes no source. The older **unconditional** note predates the later all-\(p\), prime-end and canonical-width proofs and so must be read historically. No assertion is made that successful CI mechanically verifies DH straightening, Carathéodory, KKL, or every inequality in a handwritten analytic proof.

Run from repository root (all commands are read-only; **never** use a generator's --write flag):
~~~sh
python -B research/tip_family_theorem/verify_chain.py
python -B -m unittest discover -s research/tip_family_theorem -p 'test_*.py' -v
~~~
The first command invokes every named dependency verifier, checks immutable source packets, and independently crosschecks \(p=3,4,8,12,13,16\), charts, index conversion, ten/twenty labels, covering versus immersion, 3/3/7 and 3/3/5 spans, edge matrix, Wave *type*, and upper/lower radius/transport distinctions. It does not modify any tracked dependency. Separate GitHub Actions run the theorem chain, finite Lean shadows and the original Research validation/weighted Lean workflows at the exact PR commit.
