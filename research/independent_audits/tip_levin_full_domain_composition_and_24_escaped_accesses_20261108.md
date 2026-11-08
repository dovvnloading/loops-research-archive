# The actual 3/9 ray maps compose on their entire eligible domain — and 24 original boundary accesses escape

**Date:** November 8, 2026. **Result:** a source-typed composition theorem for actual Levin renormalization-ray correspondences at the archive's nonattracting 3/9 Misiurewicz tip, together with an exact proper-path obstruction on 24 named physical ray accesses. Neither theorem is the full Kahn–Lyubich infinite-sheet localization map, a general virtual-tower assertion, or MLC.

This is a **positive cross-scale theorem**, not an extrapolation from eight matching rational angles. Its hypotheses are checked at the actual quadratic, and its proof uses prime-end access classes. The mechanism itself is classical; novelty/priority outside this archive remains unassessed.

## 1. Genuine geometry and a third (intermediate) polynomial

Write \(f(z)=z^2+c_*\), where \(c_*\) is the uniquely certified real root of \(P_{18}(c)+P_9(c)=0\) in the original rational \(2^{-128}\) bracket. The critical orbit first lands on a repelling period-nine cycle at time ten.

The source-certified quadratic-like returns \(F=f^3:V_3\to U_3\) and \(H=f^9:V_9\to U_9\) have connected, full filled sets \(K_9\subsetneq K_3\) and genuine strict phase separation. In a neighborhood of \(K_9\), \(H=F^3\). These are the physical constructions in nonattracting_tip_complex_two_scale_20261106.md and period9_tip_ramified_precritical_pair_20261107.md, not synthetic cyclic maps.

Fix a global quasiconformal hybrid straightening \(h_3\) from \(F\) to a monic centered quadratic \(g\), satisfying \(h_3\circ F=g\circ h_3\) near \(K_3\), \(h_3(K_3)=K(g)\). The critical orbit of \(F\) is

\[
0\to P_3\to P_6\to P_9\to P_{12}\to P_{15}\to P_{18}\to P_{12}.
\]

The source's first-19-orbit separation makes the preperiod exactly four and the eventual period exactly three for \(F\). The multiplier of the eventual \(F^3\)-cycle is the already certified \(3<\lambda_9<4\). Thus **the intermediate polynomial \(g\) is itself a postcritically finite Misiurewicz quadratic**. Its connected Julia set is locally connected by classical subhyperbolic theory.

Let \(L=h_3(K_9)\subsetneq K(g)\). Restricting the germs of the already proper returns within the neighborhood where the hybrid conjugacy is defined gives a proper degree-two polynomial-like representative of \(g^3\), with exactly the connected filled set \(L\). This is a representative/germ assertion; it does not falsely claim that the original round disk is preserved by the quasiconformal straightening.

### Intermediate analytic eligibility

Levin's conditions (p1)–(p2) hold for this renormalization of \(g\): (p1) is the degree-two connected polynomial-like return just described. For (p2), choose a representative \(g^3:W_1\to W\) with \(L\Subset W_1\). The Böttcher inverse for \(g\) extends continuously over the circle because \(K(g)\) is connected and locally connected. Uniform continuity at Green level zero, together with \(\operatorname{dist}(L,\partial W_1)>0\), supplies a positive level below which **no** \(g\)-external ray landing in \(L\) meets \(\partial W_1\). This is precisely the uniform all-crossings condition in Levin p. 135 and the same Carathéodory lemma independently used for the original \(f\)-scale p2.

Consequently there is a **third, genuine, source-defined Levin angle map**
\[
Q:\Lambda_{g,L}\longrightarrow\mathbb T
\]
for \(g^3\) on \(L\), onto the circle, finite-to-one and extendible to a monotone degree-one circle map. On its **eligible set** \(\Lambda_{g,L}\), and nowhere else by assumption, \(Q(8\eta)=2Q(\eta)\pmod1\).

## 2. The full-domain theorem

Let \(\Lambda_3,\Lambda_9\) be the original sets of ambient \(f\)-ray angles landing in \(K_3,K_9\), and let \(\Pi_3,\Pi_9\) be the actual Levin maps already established in levin_tip_p2_carathéodory_two_scale_20261106.md.

**Theorem 2.1 (serial ray naturality at the true tip).**
\[
\boxed{\Lambda_9=\{\theta\in\Lambda_3:\Pi_3(\theta)\in\Lambda_{g,L}\},
\qquad \Pi_3(\Lambda_9)=\Lambda_{g,L}}
\]
and for **every** eligible ray, not merely the original eight-ray table,
\[
\boxed{\Pi_9(\theta)=Q(\Pi_3(\theta))\qquad(\theta\in\Lambda_9).}
\]
Hence the equivalence induced by \(\Pi_3\) **refines** the one induced by \(\Pi_9\) on \(\Lambda_9\): equal coarse internal ray angles force equal fine internal ray angles.

**Proof.** The ambient polynomial \(f\) and intermediate quadratic \(g\) are Misiurewicz, so their Julia sets are connected and locally connected and all their external rays land. By Levin's Theorem 1, \(R^f_\theta\) and the period-three polynomial-like ray \(h_3^{-1}(R^g_{\Pi_3(\theta)})\) converge to the **same \(K_3\) prime end**, not merely to points with identical itineraries. Their physical landing point \(z\) is the same. Thus the intermediate \(g\)-ray lands in \(L=h_3(K_9)\) if and only if \(z\in K_9\), which proves the first domain equality. Levin Theorem 3(c) makes \(\Pi_3:\Lambda_3\to\mathbb T\) onto, so the same equality proves \(\Pi_3(\Lambda_9)=\Lambda_{g,L}\).

For \(\theta\in\Lambda_9\), both equivalent curves land at \(z\in K_9\). The footnote following Levin's p. 137 prime-end definition gives an exact criterion: two curves landing at one point are \(K\)-equivalent if and only if they are homotopic through curves in \(\mathbb C\setminus K\) converging to that point. Since \(\mathbb C\setminus K_3\subset\mathbb C\setminus K_9\), a \(K_3\)-equivalence homotopy is also a \(K_9\)-equivalence homotopy. The first-stage ray equivalence therefore **descends along the actual nested carriers**.

Apply Levin Theorem 1 a second time, to the intermediate polynomial \(g\) and the genuine renormalization \(g^3\) on \(L\): \(R^g_{\Pi_3(\theta)}\) is \(L\)-equivalent to its polynomial-like ray of angle \(Q(\Pi_3(\theta))\). Pull that equivalence back by the global homeomorphism \(h_3^{-1}\). Together with the previous paragraph, this makes the original \(R^f_\theta\) \(K_9\)-equivalent to the *iterated* polynomial-like ray of that angle.

The composite hybrid conjugacy for the two consecutive straightenings straightens the **same physical** \(f^9\) germ and is conformal a.e. on \(K_9\). Levin Theorems 1 and 3(e) imply uniqueness of the direct fine ray angle up to \(k/(m-1)\). Here \(m=2\), so this is \(0\pmod1\), with **no remaining rotational ambiguity**. Hence the direct map \(\Pi_9\) equals \(Q\circ\Pi_3\) on **all** \(\Lambda_9\). \(\square\)

**Important non-extension theorem.** A continuous degree-one circle map cannot intertwine multiplication by eight with multiplication by two on the **whole** circle: degrees of \(Q\circ\sigma_8\) and \(\sigma_2\circ Q\) would be \(8\) and \(2\). Levin's monotone extension of \(Q\) exists, but its semiconjugacy law applies **only to the eligible Cantor set**. Any proposed whole-circle commuting diagram is a false strengthening of Theorem 2.1.

## 3. Exactly 24 proper boundary accesses fail under physical inclusion

Write \(C_r=f^r(K_3)\) for \(0\le r<3\), \(D_{r,k}=f^{r+3k}(K_9)\) for \(0\le r,k<3\), and
\[
\Omega_3=U^0\setminus\bigcup_r C_r,\qquad
\Omega_9=U^0\setminus\bigcup_{r,k}D_{r,k}.
\]
The source proves their strict phase separation and the **actual physical inclusion** \(i:\Omega_3\hookrightarrow\Omega_9\). Let \(\mathcal A_{32}\) be the exact source-geometric 32-ray depth-ten precritical cohort in \(K_3\), from the merged alpha-puzzle/Lean certificate #56. Let \(\mathcal A_8\) be the eight ray angles landing in \(K_9\), from #55–57. The remaining 24 rays land at **12 individually known, paired points** of \(K_3\setminus K_9\).

**Lemma 3.1 (the coarse-only endpoints avoid every fine phase).** For any of the 12 coarse-only roots \(z\), \(f^{10}(z)=Z_*\) and therefore \(f^9(z)\in\{p,-p\}\subset K_9=D_{0,0}\), because \(f(p)=f(-p)=Z_*\). Since \(z\in K_3=C_0\), it avoids all \(D_{r,k}\) with \(r\neq0\). The remaining other phases \(D_{0,1}\) and \(D_{0,2}\) are invariant under \(f^9=(f^3)^3\) and are disjoint from \(D_{0,0}\); if \(z\) belonged to either, \(f^9(z)\) would belong to that same component, a contradiction. Thus
\[
\boxed{z\in K_3\setminus\bigcup_{r,k}D_{r,k},}
\]
so every one of the 12 physical endpoints is an **interior point of \(\Omega_9\)**.

**Theorem 3.2 (exact boundary survival/escape).** For every ray angle in \(\mathcal A_{32}\), a sufficiently short terminal ambient external-ray segment is a proper path in \(\Omega_3\). Under the actual inclusion \(i\), exactly **eight** remain proper in \(\Omega_9\) (those in \(\mathcal A_8\)), while exactly **24** become improper (those landing at the 12 coarse-only points). The 12 lost points occupy the four source-certified \(G=f^3\) depth-three alpha-puzzle face types in counts **2, 4, 4, 2**. All statements of this physical properness dichotomy persist in a sufficiently small **real** parameter interval around \(c_*\), with the same angle labels, by the finite strict phase conditions and the independently proved ray-bifurcation continuity.

**Proof.** A terminal ambient ray lies outside \(K(f)\), hence outside every \(C_r,D_{r,k}\), and tends to a point of \(K_3\), which is excluded from \(\Omega_3\). It is proper there. If the endpoint belongs to \(K_9\), it is still excluded from \(\Omega_9\) and remains proper. Otherwise Lemma 3.1 makes it an interior point of \(\Omega_9\); the terminal tail eventually remains in a small compact disk in that target surface, so its inverse image of that disk is not compact. Thus it is not proper. The exact counts, ray labels and four face types are given by the previously independently certified complete 32-ray/15-group alpha-puzzle and slit-pullback atlases. \(\square\)

This is a theorem about **direct paths under physical inclusion**. It does not say that the reverse restriction operation on target paths used in KL theory is empty, or rule out continuation by a complete marked localization. It makes the previously missing survival data exact for the real source: the eligible subset is **eight**, the escaped cohort is **24**.

## 4. The source-defined eight-ray graph

In cyclic ambient order, the eight rows \((\theta,\Pi_3(\theta),\Pi_9(\theta))\) are

| Ambient \(\theta\) | Coarse \(\Pi_3\) | Fine \(\Pi_9\) |
|---|---:|---:|
| \(114/511\) | \(5/7\) | \(0\) |
| \(116791/523264\) | \(81/112\) | \(1/4\) |
| \(144841/523264\) | \(87/112\) | \(1/4\) |
| \(283/1022\) | \(11/14\) | \(1/2\) |
| \(739/1022\) | \(3/14\) | \(1/2\) |
| \(378423/523264\) | \(25/112\) | \(3/4\) |
| \(406473/523264\) | \(31/112\) | \(3/4\) |
| \(397/511\) | \(2/7\) | \(0\) |

The finite graph \(Q\) maps the eight distinct coarse angles onto \(\{0,1/4,1/2,3/4\}\), with each fine angle occurring twice. The physical return multiplies ambient angles by \(512\), the coarse internal return by \(8\), and fine internal by \(2\). All eight triples satisfy these three exact modular equations. **Theorem 2.1, rather than the finite arithmetic, establishes that these eight are restrictions of one globally source-defined eligible-domain map.**

## 5. Verification, status and next proof target

The accompanying exact Python verifier independently rebuilds the **2,048 → 80 → 32** actual alpha-puzzle sieve, checks the 32 = 8 + 24 partition against the already merged 15-class, four-face physical ray atlas, and verifies all eight modular return and factorization equations. A small Lean 4 module, importing the existing kernel-verified TipActualCoarseRays, proves the finite 32/8/24 split, eight return-clock equations, injectivity of the eight coarse rational values, and four two-element fine fibers. **Lean does not certify Carathéodory, polynomial-like straightening, Levin's theorem, actual prime ends or properness.** Those are written analytic arguments with exact named source hypotheses. No statement in H1–H4, UPTCR or MLC is promoted.

The next real frontier is the **actual based infinite-sheet KL localization comparison**, with these eight surviving accesses and four original face classes equipped with their true \(O/\xi/\eta\) tile and integer-winding coordinates. The 24 escaped rays will require source-typed broken-path/continuation records; simply pretending the raw inclusion preserves their proper endpoints is now conclusively invalid.

**Attribution:** Levin's ray correspondences and uniqueness, Douady–Hubbard straightening, classical locally connected Misiurewicz dynamics, and the existing archive's source geometric certificates retain their original authorship. OpenAI GPT-6 assisted this specific proof audit, mathematical synthesis, exact tests and finite Lean verification. Independent specialist review is still required.
