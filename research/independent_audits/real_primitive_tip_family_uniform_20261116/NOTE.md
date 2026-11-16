# The near-\(-2\) real primitive-tip family: a uniform finite theorem, six interval certificates, and the analytic boundary

**Audit dated 2026-11-16.** This is **not an unconditional theorem asserting the Native Wave Transfer Laboratory's full physical configuration for every integer \(p\ge3\)**. It proves a genuinely period-uniform *real/marked combinatorial implication* from explicit geometric hypotheses, independently certifies those hypotheses at \(p=3,4,5,6,7,8\) to the extent described below, and isolates the missing all-period analytic/existence input. A two-period extrapolation is not a proof. In particular, the **extremal-width constant is not an intrinsic function of return period**: it depends on the chosen annulus. We give one explicit, optional normalization matching the two observed ratios, with a rigorous algebraic limit.

## 1. Which tips? Exact branch and kneading

Write \(f_c(z)=z^2+c\), \(x_j=f_c^j(0)\), \(G=f_c^p\), and \(H=G^3=f_c^{3p}\). The branch in question is the **leftmost real primitive period-\(p\) window near \(c=-2\), with a three-return Chebyshev/Misiurewicz tip inside its central \(G\)-copy**. It is *not* an arbitrary real primitive component of period \(p\), and the inner period is **\(3p\)**, not \(p\). Its kneading data are the outer critical sign prefix
\[
 x_1<0,\qquad x_j>0\quad(2\le j\le p),
\]
with no earlier return to the small central interval, and the signed first-return itinerary
\[
 0\overset{G}{\longmapsto}x_p>0
 \overset{G}{\longmapsto}x_{2p}<0
 \overset{G}{\longmapsto}x_{3p}<0
 \overset{G}{\longmapsto}x_{4p}>0
 \overset{G}{\longmapsto}x_{5p}<0
 \overset{G}{\longmapsto}x_{6p}>0.
\]
At the distinguished tip the **exact polynomial equation** is
\[
 P_p(c):=x_{6p}(c)+x_{3p}(c)=0,\quad x_{3p}<0.
 \tag{1}
\]
Evenness of \(G\) then implies \(H(0)=-t\), \(H(-t)=t\), \(H(t)=t\), with \(t=x_{6p}=-x_{3p}>0\). Thus the *inner* critical orbit is precisely the real Chebyshev endpoint portrait \(0\to-t\to t\to t\). This equation alone has other roots (including period-\(p\) centers where \(x_p=0\)); it **does not uniquely characterize the desired root** without the leftmost primitive-window/kneading/real-order branch restrictions. We use **uniquely isolated local roots** for \(3\le p\le8\), not a claim of uniqueness in the whole real line or the whole window for all periods.

For clarity the five target cuts of this family are, in **increasing real order**,
\[
 a=x_{5p}<b=x_{3p}<d=x_{6p}<e=\alpha<h=x_{4p},
 \qquad G(\alpha)=\alpha,\quad \alpha>0.
 \tag{2}
\]
The three small real phase intervals are \(K_0=[x_{3p},x_{6p}]\), \(K_1=[x_{4p},x_p]\), and \(K_2=[x_{2p},x_{5p}]\). Their hull is \(T=[x_{2p},x_p]\). The physical target/central source are \(U_p=D(0,R_p)\), \(V_p=\operatorname{component}_0(G^{-1}(U_p))\), with \(R_3=1/4\) and the checked choice \(R_p=2^{-p}\) at \(4\le p\le8\). The global degree is \(2^p\); the **central restricted degree is two**, a separate assertion. For \(p=3\) this degree-two assertion is a cited analytic input; for \(4\le p\le8\) it is directly Rouché-certified.

## 2. Uniform realization theorem (conditional, with non-tautological hypotheses)

**Theorem A — finite native transfer template, for every \(p\ge3\).** Suppose a real quadratic polynomial and the integer \(p\) satisfy all the following *geometric* conditions:

1. Equation (1), the sign prefix above, and the strictly monotone two-branch real map \(G\) on \([-x_p,x_p]\), increasing on the negative half and decreasing on the positive half. It suffices for the last property that \(f_c([0,x_p])<0\) and \(f_c^j([0,x_p])>0\) for \(2\le j<p\).
2. The **strict** orbit order \(x_{2p}<x_{5p}<x_{3p}<0<x_{6p}<\alpha<x_{4p}<x_p\) and the **strict source-cut order**
   \[
   -x_p<-x_{4p}<x_{2p}<x_{5p}<-\alpha<x_{3p}<x_{6p}<\alpha<-x_{5p}<-x_{2p}<x_{4p}<x_p.
   \tag{3}
   \]
   Here \(\alpha\) is the positive fixed point of \(G\) in \((x_{6p},x_{4p})\). These are interval inequalities on the polynomial orbit, **not** hypotheses specifying the desired atom counts or transition matrix.
3. The central component \(V_p\Subset U_p\) is a proper degree-two holomorphic restriction, and the *induced physical real-tree marking* is the three-phase hull \(T\) with five ordered cuts in (2). When interpreting these purely real computations as **KKL ideal-boundary objects**, assume the cited real-Julia-interval/slit prime-end identification and KKL Appendix A.1 and §6.1 Propositions 6.5–6.6. No general nonlocally connected boundary assertion is assumed or concluded.

Then **uniformly in \(p\)**, the source tree preimage within \(V_p\) is \(T'=[-x_p,x_p]\); its complement relative to \(T\) has **one** new attached real segment \([-x_p,x_{2p})\), attached at \(x_{2p}\). The induced target/source inner ideal circles have **10/20 atoms**, respectively, and one outer whole-component atom by the stated marking convention. The attached inner source atoms, in cyclic order, are exactly \(S_{19},S_0,S_1\).

The covering action is \(f_*:S_s\mapsto I_{s\bmod10}\). The **different**, KKL set-valued immersion proper restriction \(\iota^*\) has source-to-*pullback-block* partition
\[
  P_0=[18,19,0,1,2],\ P_1=[3,4],\ P_2=[5],\ P_3=[6],\
  P_4=[7,8,9],\ P_5=[10],\ P_6=[11,12,13],\
  P_7=[14],\ P_8=[15],\ P_9=[16,17]. \tag{4}
\]
The lengths are \((5,2,1,1,3,1,3,1,1,2)\); all are end-proper, and only \(P_0\) fails full properness because attached sides land in **target interior**, not on the target ideal boundary. In particular \(\iota^*\) is **not** the function \(S_s\mapsto I_{s\bmod10}\), and there is no asserted pointwise prime-end image of an attached side.

For a proper target circle with common right real endpoint \(q\in(x_{5p},-\alpha)\), consider its crossing left intersection \(w\in(-x_{4p},x_{2p})\), or an avoiding intersection \(w<-x_p\), with whole complex circles contained in the proper source component (and the standard slit relative-endpoint homotopy/KKL filters available). Then the filtered source restriction endpoint pairs are
\[
 (S_3,S_1),\ (S_{19},S_{17})\quad\text{(crossing: 2)},
 \qquad(S_3,S_{17})\quad\text{(avoiding: 1)}.\tag{5}
\]
Their **cover-pushed** pairs are \((I_3,I_1),(I_9,I_7)\) and \((I_3,I_7)\). All three source short-arc spans have three atoms and their endpoints occupy different immersion blocks; the target path is the same relative-ideal-endpoint class. No unfiltered or arbitrary path-groupoid theorem is asserted.

The genuine **three old real edges**, counted **once per physical segment**, are
\(E_0=(x_{5p},x_{3p})\), \(E_1=(x_{6p},\alpha)\), \(E_2=(\alpha,x_{4p})\). Their edge-occurrence matrix (output rows, old input columns), characteristic polynomial and Perron root are
\[
 M=\begin{pmatrix}0&0&1\\1&0&1\\1&1&0\end{pmatrix},\qquad
 \det(tI-M)=t^3-2t-1=(t+1)(t^2-t-1),\quad
 \rho(M)=\phi=\frac{1+\sqrt5}{2}.\tag{6}
\]
A positive *left* Perron vector is \((\phi,1,\phi)\). The complete target **atomic** zero-old-edge types are \(I_0,I_2,I_5,I_8\); the source zero-old-edge types are \(S_0,S_1,S_2,S_5,S_{10},S_{15},S_{18},S_{19}\), whereas the **cover-pushed** zero-edge types are \(S_0,S_2,S_5,S_8,S_{10},S_{12},S_{15},S_{18}\). The parent crest type is \(I_0\); the two cover-pushed child crest types are \(I_2,I_8\), all zero-old-edge types. These are **closed crest type labels**, not a theorem about arbitrary fine subsectors or iterated crest transport.

If in addition a concentric wave on this physical slit satisfies the stated gate and whole-disk conditions (specified next), and the analytic KKL log-rectangle/conformal-invariance hypotheses hold on its support, then for any \(0<r_0<r_1\) its parent/child widths satisfy
\[
 W=\frac{\log(r_1/r_0)}{2\pi},\qquad
 W_+=W_-=\frac{\log(r_1/r_0)}{\pi}=2W,
 \qquad \boxed{W^{-1}=W_+^{-1}+W_-^{-1}}.\tag{7}
\]
Only the rational height coefficients in (7) are finite/algebraic consequences. The identification with actual **extremal widths** is **conditional on the analytic input**, and equality is **not a strict Wave gain**.

### Proof of Theorem A

Evenness \(G(-z)=G(z)\) and the derivative signs make \(G\) a two-sheeted real map \([-x_p,x_p]\to[x_{2p},x_p]\). All fibers of points in \(T\) have two real preimages (one at the turning value, with multiplicity two); degree two on \(V_p\) exhausts those preimages and rules out extra complex tree sheets there. The real interval is connected to zero through points mapped into \(U_p\), so it lies in \(V_p\). Hence \(T'=[-x_p,x_p]\) and (3) yields exactly one new interval \([-x_p,x_{2p})\).

The five cuts are the three Julia-phase endpoints that separate the old edges together with the dividing fixed point \(\alpha\). Their ten increasing inverse locations are **derived**, not posited as 20 labels:
\[
 (-x_{4p},\ x_{2p},\ x_{5p},\ -\alpha,\ x_{3p},\ x_{6p},\
 \alpha,\ -x_{5p},\ -x_{2p},\ x_{4p}).\tag{8}
\]
Apply \(G\) to each of these using \(x_{6p}=-x_{3p}\), evenness and the forward orbit; each cut has exactly one inverse on each monotone half. Two slit-side accesses between consecutive cuts, with one terminal atom per tip, give ten target and twenty source atoms. The orientation flip on the positive sheet gives \(S_s\mapsto I_{s\bmod10}\). Actual inclusion instead labels the outside-left interval by target *interior*; the cyclic immersion partition obtained by comparing (2) and (8) is exactly (4). The left attachment appears on upper and lower sides plus the tip, giving \(S_{19},S_0,S_1\), and these are internal to \(P_0\). End and properness follow by inspection of (4) and KKL's stated definitions. These ideal-circle interpretations require the explicitly declared prime-end hypothesis, rather than following from real inequalities alone.

An oriented circle intersects the slit twice at \(q,w\); when \(w\) lies on the new attachment it leaves two semicircles after proper restriction, otherwise it leaves one. The cut order places \(q\) at the two sides \(S_3,S_{17}\), and crossing \(w\) at \(S_1,S_{19}\). Computing the distinct-block and three-atom short-arc predicates proves (5); applying **\(f_*\)**, not **\(\iota^*\)**, proves the target pairs. Relative ideal-endpoint homotopy is the cited planar slit/prime-end input.

Finally the orbit and fixed-point identities give the five cut images in order
\( (a,b,d,e,h)\stackrel{G}{\longmapsto}(d,h,h,e,a)\). Monotonicity on each of the three old edges yields respectively the physical image edge multisets \(\{E_1,E_2\}\), \(\{E_2\}\), \(\{E_0,E_1\}\). The \(K_0\) interval between image edges in the last case is a **vertex gap**, not a fourth old edge. Counting every real segment once yields (6). Direct multiplication gives \((\phi,1,\phi)M=\phi(\phi,1,\phi)\); \(M^4\) is positive, so Perron–Frobenius gives \(\rho(M)=\phi\). The cut-to-edge incidences give the zero-edge type lists. The parent base is \((I_9,I_0,I_1)\) and the two cover-pushed bases are \((I_1,I_2,I_3)\), \((I_7,I_8,I_9)\). Lastly the logarithmic rectangle has radial length \(\log(r_1/r_0)\) and angular heights \(2\pi,\pi,\pi\); its algebraic aspect ratios and the reciprocal sum give (7), conditional on the cited analytic width identification. **None of this proof uses the numerical value of \(p\).** QED.

## 3. One explicit width normalization, and why it is not canonical

For *any* realization obeying (2)–(3), select the proposed wave
\[
 z_p=-\frac34 x_p,\quad r_{0,p}=\frac{x_p}{16},\quad
 r_{1,p}=\frac{p-1}{8p}x_p,\quad
 q=z_p+r_{1,p},\quad w=z_p-r_{1,p}.\tag{9}
\]
This is an **extra choice**, not an implication of kneading. For \(3\le p\le8\) the independent integer-interval verifier establishes *strictly* that for **all** radii in the open range \((r_{0,p},r_{1,p})\), the right endpoints lie between \(x_{5p}\) and \(-\alpha\), the left intersections lie in the attachment/source atom gate \((-x_{4p},x_{2p})\), and the whole complex largest circle maps strictly inside \(U_p\). It also checks the avoiding comparison circle with the same \(q\) and \(w_{\mathrm{avoid}}=-17x_p/16\) lies in the proper central preimage. These are **whole-disk** bounds, not sampled boundary values.

If the inequalities/analytic identification for (9) hold at some further \(p\), then the **chosen** parent width and its exact limit law are
\[
 \boxed{W_p^{\rm chosen}=\frac{\log(2-2/p)}{2\pi}},\qquad
 W_{+,p}^{\rm chosen}=W_{-,p}^{\rm chosen}=2W_p^{\rm chosen},
 \qquad\lim_{p\to\infty}W_p^{\rm chosen}=\frac{\log2}{2\pi}.\tag{10}
\]
This gives \(W_3=\log(4/3)/(2\pi)\) and \(W_4=\log(3/2)/(2\pi)\), matching the **ratios** in the two source records, although (9)'s individual radii are **not** the same as those source records. Algebraically, \(W_p\) increases on \(p\ge3\) and
\[
 0<W_3\le W_p<\frac{\log2}{2\pi},\quad
 \frac1{2\pi p}<\frac{\log2}{2\pi}-W_p
 =\frac1{2\pi}\log\frac p{p-1}<\frac1{2\pi(p-1)}.\tag{11}
\]
These bounds and the limit are **theorems about the explicitly selected ratios for all integers \(p\ge3\)**; physical admissibility of those ratios for all \(p\) is **open**.

There cannot be an intrinsic period-only width formula without an extra normalization. Already at **\(p=3\)** the source wave permits \(3/256<r<1/64\). Restricting to the proper *subannulus* \(5/384<r<1/64\) produces the **same tip, marking and crest types**, but ratio \(6/5\), hence symbolic width \(\log(6/5)/(2\pi)\), not \(\log(4/3)/(2\pi)\). Thus the assertion **"the return period determines the width" fails at the first supplied period \(p=3\)**, while the observed **finite marked structure** itself has **no detected failure up to \(p=8\)**. Even the width formula in (10) is not a canonical dynamical invariant.

## 4. What the independent verifier actually certifies

Run from repository root:

```sh
python research/independent_audits/real_primitive_tip_family_uniform_20261116/verify.py
python -m unittest discover -s research/independent_audits/real_primitive_tip_family_uniform_20261116 -p 'test_*.py' -v
```

`verify.py` imports **none** of the Native Wave Transfer regenerators; it uses Python standard-library `Fraction` and *outward-rounded integer intervals on a \(2^{-384}\) grid*. Decimal *seeds* locate possible roots and are **not proof oracles**: the program certifies opposite strict signs of \(P_p\), a strict negative interval derivative **throughout the seed window** (hence uniqueness **within that window**), then bisects and reports an adjacent \(2^{-192}\) dyadic enclosure. For \(p=3,4\), its tighter enclosure is strictly inside the separate pinned source parameter bracket; for \(p=5,6,7,8\), it gives new local interval certificates. It checks real phase signs/monotonicity, fixed \(\alpha\), all labeled polynomial cut preimages, disjoint complex phase *balls*, and all cyclic atom placements and three genuine real-edge traces. For \(p\ge4\) the expansion \(G(z)=d+A z^2+E(z)\) on \(|z|=R_p\) is enclosed by
\[
 D_{j+1}=D_j^2+c,\quad A_{j+1}=2D_jA_j,\quad
 T_{j+1}=2|D_j|T_j+(|A_j|R_p^2+T_j)^2
\]
(starting \(D_0=A_0=T_0=0\) and \(A_1=1\)). Strict \(|A|R_p^2>|d|+T_p+R_p\) proves by **Rouché** that the central preimage has degree two and is compactly contained in \(U_p\). The integer lower margins in the JSON are **rounded down** to a safe \(2^{-64}\) grid. For \(p=3\), the complex degree-two fact is **imported** from the source-locked PR #68 proof, not reinvented as a finite test.

The program independently evaluates exact complex-disk envelopes for both test circles, derives rather than loads the twenty-entry covering/immersion labels, checks filtered path restrictions, enumerates old-edge occurrences from **polynomial endpoint images**, checks the exact \(\phi\) left eigenvector, and tests the zero-edge/closed-crest labels. All computed common rows are checked *per period*, and are stored once in [`results.json`](results.json), accompanied by per-period strict parameter brackets, Rouché margins and selected wave ratios. Its `--write` option is **never** used in CI; the default is byte-for-byte read-only comparison. Adversarial tests reject a moved root, a falsified edge entry and a falsified immersion block.

The optional [`RealPrimitiveTipDiscrete.lean`](RealPrimitiveTipDiscrete.lean) verifies **only** the declared finite labeled incidence model (cover fibers, pullback blocks, matrix derived from cut images, crest types, normalized ratio bounds and integer coefficient sum). It does not formalize or purport to prove polynomial existence, local connectedness, Rouché, KKL semantics or analytic widths.

### Certification ledger

| Claim | Status |
| --- | --- |
| Theorem A's finite implications for every \(p\ge3\) **with the stated geometry/marking hypotheses** | **Proved uniformly**, elementary real topology and combinatorics; finite Lean shadow |
| Strict parameter signs, local uniqueness, real signed orbit/cut order, separate \(f_*\) and \(\iota^*\) tables, 2/1 filtered count, old edges and crests, selected wave gate, full disks for \(3\le p\le8\) | **Exact rational/interval certified**; geometric slit/KKL interpretation still conditional |
| Proper central degree-two holomorphic restriction \(4\le p\le8\) and disjoint complex phase balls \(3\le p\le8\) | **Rouché / exact ball bounds**, with ordinary analytic Rouché theorem used as a cited standard theorem |
| Central degree-two restriction at \(p=3\), identification of the entire little Julia sets with real three-phase intervals and of the *complete* KKL Hubbard tree | **Imported** from cited source (\(p=3\)); not proved by these finite computations for all \(p\) |
| Carathéodory/prime-end accesses, immersion proper-restriction rules and relative ideal-boundary homotopy | **Conditional** on KKL §6.1 and Appendix A.1/A.3.2–A.3.4 and the standard slit prime-end interpretation |
| Actual conformal extremal widths of waves and equality under cover pushforward | **Conditional** on analytic rectangle/univalence/conformal-invariance inputs, including KKL Appendix A.3 |
| Ratios \(2(p-1)/p\), coefficient harmonic law, limit and error bounds for the **chosen** annuli | **Proved for all integer \(p\ge3\) algebraically**, with physical validity only certified through \(8\) |
| Unique designated tip across the full primitive window for every \(p\); complex Julia tree/KKL marking and chosen-wave bounds for every \(p\ge9\) | **Open in this audit** (not disproved) |
| Uniform strict Wave gain, zero-old-edge **subsector** escape, closed-crest domination, H1–H4, UPTCR or MLC | **Not proved**; the equalities are not strict gain |
| Floating-point statements | **None used as certificates.** Decimal root seeds are only locators and all resulting inequalities are interval-checked |

## 5. References, scope and review hazards

- The existing original physical [`tip_pr68.json`](../../native_wave_transfer/physical_examples/tip_pr68.json), [`SPECIFICATION.md`](../../native_wave_transfer/SPECIFICATION.md) and source-locked [`RESULTS.md`](../../native_wave_transfer/RESULTS.md) give the precise \(p=3\) types and analytic dependency list; the new proof does **not** edit them.
- The merged PR [#77](https://github.com/dovvnloading/loops-research-archive/pull/77) records the \(p=4\) physical certificate, [`primitive4_tip12.json`](../../native_wave_transfer/physical_examples/primitive4_tip12.json), and its independent immutable manifest.
- The actual-old-edge physical interpretation and distinction between closed crests and open atoms are audited in [`issue40_native_attachment_edge_incidence_20261115/NOTE.md`](../issue40_native_attachment_edge_incidence_20261115/NOTE.md).
- Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/abs/2606.27272v1), §§2.1, 2.5, 6.1 Props. 6.5–6.6, Appendix A.1 and A.3.2–A.3.4: **analytic and categorical inputs**, not theorems established by this verifier.

**Hostile-review checklist resolved:** The local root seed is not a uniqueness theorem for all roots; the 20/10 counts are **inner** ideal circles, with a single whole *outer* atom per component by convention; physical \(G=f_c^p\) has global degree \(2^p\) but restricted degree **2**; the attached interval's boundary is target **interior** under inclusion; \(f_*\ne\iota^*\); old real edges are not doubled for two slit sides; open atoms are not arbitrary closed crest subsectors; log ratios are chosen, not forced by \(p\); and a positive Perron root does not overcome an actual zero-edge crest. The first **physical** period at which the observed combinatorics might fail is unknown beyond the checked \(p=8\); no extrapolation has been silently promoted to an unconditional analytic theorem.