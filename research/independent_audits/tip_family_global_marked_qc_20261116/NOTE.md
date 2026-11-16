# Global marked-QC transport at primitive tips: missing interface, sharp conditional implication, finite exact regressions

**Independent additive audit — 2026-11-16. Verdict: the requested unconditional global marked-domain theorem is NOT proved.** This report does not silently assert that local hybrid straightening transports all physical KKL Waves. It gives the weakest explicit two-sided curve-family comparison sufficient for canonical-width bounds, proves its numerical consequences and a general countermodel to deriving a global dilatation constant from a local modulus alone, and reruns the *unchanged* depth-two and depth-three exact certificates. No existing research or Lean file is altered.

## Status ledger (the quantifier matters)

| Claim | Actual status |
|:--|:--|
| Universal positive optimal fundamental-annulus modulus for each realized finite non-doubling renormalization of a real quadratic (and all levels of a genuinely infinitely renormalizable real quadratic) | **Published** Lyubich–Yampolsky Complex Bounds Theorem, with its doubling-near-cusp exception |
| At each such level a suitable quadratic-like restriction and a local hybrid conjugacy to its straightening | **Published** Douady–Hubbard, with a uniform *local* QC constant via a separate quantitative straightening input |
| Straightening equals the specific combinatorially designated suffix | **Requires separate tuning / signed-kneading rigidity input**; not deduced from modulus |
| Uniformly QC transport of the *entire physical marked slit*, its prime ends and the full A.1/A.3.2 Wave collection | **OPEN**; no proof in the cited literature establishes it for these designated surfaces |
| Depth-uniform width sandwich and crest ratios under a *full, two-sided*, uniformly QC marked correspondence | **Proved conditionally** in §3, with constants K' and K'^2 and no depth exponent |
| A statement weaker than existence of an ambient QC map sufficient for width comparison | **Proved as a logical reduction** in §3; the required two-sided domination remains unproved |
| Depth-two nine-row grid and independent (3,3,3) row | **Exact finite rational regressions**, using archived verifiers, not a uniform-complex-bounds certificate |
| Counterexample in the designated primitive-tip KKL family to existence of a global marked map | **Not known / not constructed**; §4 gives an abstract marked-annulus countermodel to the *purported inference* from local data, not a family counterexample |
| Effective numerical K'(mu), or canonical optimal Wave convergence for infinite towers | **OPEN** |

## 1. Correct direct-at-depth inputs and their limits

Write \(F_c(z)=z^2+c\), let \(w=(p_1,\ldots,p_d)\) be an **actually realized** real primitive tuning word with \(p_i\ge3\), and let \(n_j=\prod_{i=1}^{j}p_i\). At depth \(j\), \(R_j\) is a central *degree-two polynomial-like restriction* of \(F_c^{n_j}\); it is **not** the unrestricted degree-\(2^{n_j}\) polynomial. The parameter \(\chi_j\) of its straightening is the prescribed suffix only after the independent tuning/rigidity identifications. The penultimate straightening may be a single-level tip; the last straightening need not be in the same indexed family. For an infinite word, there is no final single-level 10/20 portrait.

**Complex bounds, one level at a time.** Lyubich–Yampolsky [LY97], p. 1220, **Complex Bounds Theorem** (not just its bounded-essential-period Theorem 1.1), gives an absolute \(\mu_0>0\) such that
\[
  \operatorname{mod}(R_j)\ge\mu_0
\]
at every realized finite non-doubling real renormalization, except where the theorem explicitly excludes a last doubling renormalization near the cusp. Their modulus is a **supremum over fundamental annuli**, not that of an arbitrary prescribed physical gate. Put \(\mu=\mu_0/2\); for each \(j\) choose *some* polynomial-like representative \(R_j:V_j\to U_j\) of fundamental modulus \(>\mu\). The halving avoids assuming the supremum is attained. Applying this theorem directly to \(F_c\) for each \(j\) does not multiply losses across earlier straightenings. The same direct application works at each finite level of a genuinely infinitely renormalizable real quadratic.

Douady–Hubbard [DH85], Ch. I §1, **Straightening Theorem 1**, produces a hybrid conjugacy
\[
  h_j R_j=F_{\chi_j}h_j
\]
on *neighborhoods of the respective little filled Julia sets*. The theorem by itself does not give a numerical dilatation or an identification of the independently selected KKL slit and external prime-end accesses. A uniform local dilatation \(K_{\mathrm{loc}}(\mu)\) follows if one additionally uses the quantitative modulus-dependent straightening statement in Lyubich's *Conformal Geometry and Dynamics of Quadratic Polynomials*, Lemma 4.33 (draft notes, p. 143), or a corresponding quantitative tubing/compactness construction. That lemma does **not** furnish an evaluable numerical function here. This is strictly local. It is not an assertion that the chosen round disks or outer KKL physical gate have modulus \(>\mu\).

A hybrid map preserves dynamical conjugacy near the small filled Julia set, the contained postcritical points and a **contained** marked finite tree. Its Beltrami coefficient vanishes almost everywhere on the filled Julia set; this is not a conformal identification of the whole complement. An ambient *real-symmetric, externally marked, family-preserving* extension remains an independent problem.

## 2. The precise physical mapping problem and the failed pullback shortcut

Let \(\Omega_{j,t}\) and \(\Omega_{j,s}\) be the **physical** target and central degree-two source slit surfaces defining the canonical KKL width at level \(j\), with their prime-end compactifications, slit sides, tree and attachment. They must not be silently replaced by an abstract polynomial-like fundamental annulus. Let \(\mathcal A_j\) denote the **entire** class of admissible A.1 marked Waves, \(\mathcal A_{j,2}\) the class with the two specified A.3.2-surviving proper children, and \(\mathcal C_j\) the specifically collared four-push crest descendants. These are sets of curve families, not merely collections of symbolic endpoint pairs.

The local terminal datum in the archive has target atoms \(I_0,\ldots,I_9\) and source atoms \(S_0,\ldots,S_{19}\). Crucially, the **degree-two covering pushforward** is \(f_*(S_s)=I_{s\bmod10}\), whereas the **proper-path immersion restriction** is a set-valued operation
\[
\begin{split}
 \iota^*(I_0)&=(S_{18},S_{19},S_0,S_1,S_2),\\
 \iota^*(I_1),\ldots,\iota^*(I_9)
 &= (S_3,S_4),(S_5),(S_6),(S_7,S_8,S_9),(S_{10}),\\
 &\quad (S_{11},S_{12},S_{13}),(S_{14}),(S_{15}),(S_{16},S_{17}).
\end{split}
\]
The proper source endpoint pairs \((3,1),(19,17),(3,17)\) have inclusive spans \(3,3,7\); **cover-pushed** target pairs have spans \(3,3,5\). All exceed the strict \(>2\) eligibility filter. The old-edge incidence matrix is \(\left(\begin{smallmatrix}0&0&1\\1&0&1\\1&1&0\end{smallmatrix}\right)\). \(I_1\) and \(I_9\) approach *opposite sides of one old real edge*, not two edges. These facts are typed **finite local** constraints, not a claim that every ancestor or infinite-level physical slit has 10/20 atoms.

A sufficient **global marked-conjugacy hypothesis** \(T_j(K')\) consists of a pair of orientation-preserving, real-equivariant \(K'\)-QC homeomorphisms
\(H_{j,s}:\Omega_{j,s}\to\Omega_{\mathrm{ref},s}\) and
\(H_{j,t}:\Omega_{j,t}\to\Omega_{\mathrm{ref},t}\) which:

1. extend as homeomorphisms of the *actual* prime-end completions; match the whole tree, its selected attachment, slit banks, all marked endpoint and ideal atoms, cyclic ordering and postcritical itinerary, and agree with the near-filled-set conjugacy on an appropriate common neighborhood;
2. respect the separately typed maps \(H_{j,t}\circ f_* = f_*^{\mathrm{ref}}\circ H_{j,s}\) on covering boundary labels, and \(H_{j,s}(\iota_j^*(\gamma))=\iota_{\mathrm{ref}}^*(H_{j,t}(\gamma))\) **as collections of proper paths**, not as an equality of point maps;
3. carry **all** A.1 Waves bijectively in both directions, including the >2 filter, the attachment/crest condition, the two selected A.3.2 children and the exact four-push collars. They must cover all supports of admissible leaves, not just a finite witness set.

Nothing in the direct complex-bounds/straightening argument proves even the first clause for the prescribed physical outer gates, much less the third. In particular a QC conjugacy near \(K(R_j)\) need not be defined on every support in \(\Omega_{j,*}\). A tree homeomorphism need not extend to the specified *ambient* external-ray accesses and independent prime-end labels. A proper immersion is not a covering pushforward, and valid symbolic finite tables alone do not yield a curve-family bijection.

**What a Sullivan-style pullback actually requires.** Once compatible initial boundary/prime-end marked maps and a correct topological conjugacy relative to *all* critical/postcritical data are supplied on an appropriate full dynamical domain, one may pull back a Beltrami structure by holomorphic branches. Off branch points the norm obeys
\[
 |f^*\nu(z)|=|\nu(f(z))|,\qquad
 (f^*\nu)(z)=\nu(f(z))\,\overline{f'(z)}/f'(z),
\]
so the \(L^\infty\) norm is not compounded by pullback; a real-symmetric initial structure retains symmetry. **But the construction cannot manufacture an initially missing marking or extend across unspecified domains and slits.** One must prove lift compatibility, inverse-branch continuation across all relevant channels, equivariance at ramification, consistency of the external boundary values and equality of the induced *full* Wave classes. In a terminal PCF case, postcritical rigidity alone does not fix those external boundary values.

Bers–Royden [BR86] extends a *previously given holomorphic motion* for a small parameter disk (standard \(1/3\) disk form). Slodkowski [S91] extends a holomorphic motion over the parameter disk to the sphere. Neither supplies a holomorphic motion of these prescribed KKL marked surfaces in the first place. If one had an equivariant motion with all marks already moving and \(|\lambda_j|\le r<1\), the standard QC estimate could give \(K'\le(1+r)/(1-r)\). **No such uniform \(r\), marked motion or equivariance has been established.** McMullen [McM94], Chs. 10–11, treats rigidity/complex bounds for renormalization; this is not a citation for a canonical full-slit Wave functor. The measurable Riemann mapping theorem is a solution procedure for a *specified* bounded Beltrami coefficient, not a source of that missing coefficient. Thus calling the intended map a "standard pullback" does not prove \(T_j(K')\).

## 3. A weaker sufficient statement and the exact constants

For a curve family \(\Gamma\) in a marked physical domain, write \(w(\Gamma)\ge0\) for its extremal **width** (finite for the matched families used below), with the source's usual convention (whether expressed directly as extremal length or the reciprocal of its transverse convention). A \(K'\)-QC homeomorphism distorts either width convention by factors in \([1/K',K']\); see [Ah66], [McM94] Appendix A. Put
\[
 W_j^*=\sup_{\Gamma\in\mathcal A_j}w(\Gamma),\qquad
 W_{\mathrm{ref}}^*=\sup_{\gamma\in\mathcal A_{\mathrm{ref}}}w(\gamma).
\]

**Two-sided cofinal domination \(D_j(C)\)** is the following *strictly weaker* sufficient hypothesis; it need not use a QC map or a bijection:

* for every \(\Gamma\in\mathcal A_j\), there exists \(\gamma\in\mathcal A_{\mathrm{ref}}\) with \(w(\Gamma)\le Cw(\gamma)\);
* for every \(\gamma\in\mathcal A_{\mathrm{ref}}\), there exists \(\Gamma\in\mathcal A_j\) with \(w(\gamma)\le Cw(\Gamma)\).

The witnesses in the two directions may differ and need not maximize anything. Each condition separately gives one inequality after taking suprema. Together they prove
\[
 \boxed{\quad W_{\mathrm{ref}}^*/C\ \le\ W_j^*\ \le\ C W_{\mathrm{ref}}^*.\quad}\tag{1}
\]
This is an elementary proved implication, **not a proof of \(D_j(C)\)** for any physical tower. The global marked \(T_j(K')\) implies \(D_j(K')\) by the QC extremal-length inequality and the full-family bijection. A mere forward image of a selected gate gives neither a reverse comparison nor an upper bound for the unrestricted supremum.

If \(L<W_{\mathrm{ref}}^*<U\), equation (1) yields the correct **strict finite-level** bounds
\[
 \boxed{\quad L/C<W_j^*<CU.\quad}\tag{2}
\]
Applied *directly at each depth* with the same \(C=K'\), and with a separately certified single-level reference, the archived [canonical-width sandwich](../real_primitive_tip_family_canonical_width_sandwich_20261116/NOTE.md) gives:

* **general indexed reference \(p_{\mathrm{ref}}\ge3\):** \(0.25/K'<W_j^*<0.78K'\);
* **certified large-period reference \(p_{\mathrm{ref}}\ge13\):** \(0.26/K'<W_j^*<0.78K'\).

The \(0.26\) lower bound cannot be applied to \(p_{\mathrm{ref}}=3\) or \(4\) merely because its large-period version is true. Nor can any arbitrary suffix automatically be treated as the indexed reference. These comparisons are conditional on \(T_j(K')\) or \(D_j(K')\) **at each level**, with a uniform \(K'\) or \(C\). There is **no \(K'^j\)** because comparison is made to the reference directly, not by composing \(j\) straightenings. Nothing here proves that \(K'\) is a function of \(\mu\).

For a **matched positive parent** width \(P\) and chosen four-push descendant width \(D\), both individually controlled above and below with the **same** \(C\), the ratio obeys
\[
 \boxed{\quad \frac{D_{\mathrm{ref}}/P_{\mathrm{ref}}}{C^2}
 \ \le\ \frac{D_j}{P_j}\ \le\
 C^2\frac{D_{\mathrm{ref}}}{P_{\mathrm{ref}}}.\quad}\tag{3}
\]
This is proved by dividing the lower descendant inequality by the upper parent inequality, and conversely; \(P_{\mathrm{ref}}>0\) and \(P_j>0\) are essential. If ratios are of *two suprema*, both parent and descendant admissible classes must separately satisfy (1); it is wrong to identify two unrelated maximizers or to infer the result from an A.1 parent family alone. For the selected \(p_{\mathrm{ref}}=3\) collared four-push coefficient in [crest transport](../crest_transport_tip_family_20261116/NOTE.md), the finite strict \(0.5676<r_3<0.5684\) yields
\[
 \boxed{\quad 0.5676/K'^2<r_j<0.5684K'^2\quad}
\]
**only** when these same selected parent/descendant collars are paired. The other finite-period coefficients and distinct notions of crest ratio are not thereby proved uniform over all \(p\).

**Infinite towers.** If a *particular* infinite real primitive itinerary exists and every finite \(j\) admits the preceding comparisons with the **same** positive constants \(L,U,C\) and appropriate uniformly bounded references, then
\[
 \frac L C\le\liminf_{j\to\infty} W_j^*
 \le\limsup_{j\to\infty}W_j^*\le CU.\tag{4}
\]
The inequalities in (4) are **non-strict**; taking a limit does not preserve strictness. The analogous liminf/limsup statement holds for a uniformly controlled sequence of defined positive selected ratios using (3). **Neither equation constructs an infinite-level KKL marked slit nor proves convergence of \(W_j^*\).** If a separate theorem proves Wave convergence and identifies the limiting canonical value with that limit, it lies in the corresponding **closed** interval. Existence of a locally connected Julia set or nested renormalizations alone does not establish convergence of extremal-width optimizers.

## 4. A genuine obstruction to the modulus-only inference (not a family counterexample)

Fix \(N\ge1\), and consider the symmetric concentric annuli
\[
 A_1=\{1<|z|<e^{2\pi}\},\qquad
 A_N=\{1<|z|<e^{2\pi N}\}.
\]
Mark the inner and outer boundary components and require any global comparison to send each to its counterpart. They share a fixed collar \(1<|z|<e^{\pi/2}\), on which the *identity* is a conformal, real-symmetric local map (dilatation \(1\)). Their moduli are respectively \(1\) and \(N\). A QC map of the **whole marked annuli** has, by modulus quasi-invariance,
\[
 N=\operatorname{mod}(A_N)\le K\,\operatorname{mod}(A_1)=K.
\]
Thus the required global dilatation can be arbitrarily large despite identical local geometry and a fixed local conjugacy. One can keep an unrelated polynomial-like germ and its little-filled-set collar fixed while changing these outer marked annular collars. This is an **explicit countermodel to the logical implication** "uniform local straightening modulus \(\Longrightarrow\) uniformly QC marked outer domains"; it is **not** a parameter in the requested primitive quadratic family. A toy example with a different number of *prescribed* slit/prime-end atoms has no label-preserving homeomorphism at all, but likewise does not establish such a mismatch for actual KKL primitives.

For the actual family the unresolved object is **precisely** a map of the *physical* prime-end/slit-side marking and an induced full A.1/A.3.2 Wave correspondence respecting both the covering \(f_*\) and the **set-valued** proper restriction \(\iota^*\), with independent uniform geometric control outside \(K(R_j)\). No specific legitimate physical Wave has been proved impossible to transport, and no actual-family counterexample is claimed. The absence of a construction is **not** a proof of nonexistence. The annulus example does show why neither \(\mu_0\) nor \(K_{\mathrm{loc}}(\mu)\) determines an unconditional \(K'(\mu)\).

If an entire global marked map were supplied with Beltrami bound \(\|\nu\|_\infty\le m<1\) independent of depth, one could *define* \(K'=(1+m)/(1-m)\) and use (2)–(4). This tautological formula does **not** estimate \(m\) from \(\mu\), nor make \(K'\) effective. Both \(\mu_0\) and the local quantitative-straightening constant used here are nonnumerical; the missing global extension has no established constant at all.

## 5. Numerical and exact finite checks, without theorem promotion

The new [verify.py](verify.py) imports the **unchanged** [depth-two verifier](../tip_family_renormalization_depth_20261116/verify.py) and [depth-three verifier](../tip_family_all_depths_20261116/verify.py), executes their complete exact outward \(2^{-512}\)/Fraction routines rather than reading approximate outputs, and demands the following locked *strict* enclosures. In the depth-two table, intervals are in units \(10^{-5}\) and Rouché lower margins in units \(10^{-6}\):

| \(p_1,p_2\) | Radial witness interval (strict) | Full plane-slit upper-envelope interval (strict) | Rouché1 / Rouché2 / normalized third, each strict \(>\) |
|:--:|:--:|:--:|:--|
| (3,3) | (25224,25225) | (76475,76476) | 127464 / 6308 / 170868 |
| (3,4) | (25854,25855) | (77250,77251) | 114089 / 1837 / 243878 |
| (3,5) | (25999,26000) | (77430,77431) | 110133 / 8030 / 261699 |
| (4,3) | (25179,25180) | (76418,76419) | 45190 / 2828 / 174909 |
| (4,4) | (25848,25849) | (77243,77244) | 41404 / 978 / 245444 |
| (4,5) | (25999,26000) | (77431,77432) | 40344 / 2609 / 262575 |
| (5,3) | (25170,25171) | (76406,76407) | 111807 / 817 / 175214 |
| (5,4) | (25847,25848) | (77242,77243) | 110887 / 286 / 245758 |
| (5,5) | (26000,26001) | (77431,77432) | 110632 / 698 / 262640 |

All nine rows verify the **physical**, theorem-import-dependent \(0.25<W^*<0.775\); the two bounds in the table are a *lower witness* and a *different upper envelope*, not exact \(W^*\). In particular the (3,3) radial witness of about 0.25224 does not settle whether its optimum exceeds 0.26.

For (3,3,3) the original exact independent packet is retested: first three Rouché gaps strictly \(>0.127470,0.006346,0.003900\), separately normalized 81-return gap \(>0.172673\), radial lower witness \(>0.252105\), and whole plane-slit envelope \(<0.764704\). This also gives the physical \(0.25<W^*<0.775\) **subject to the earlier identified analytic and topological KKL imports**, not an all-depth estimate. The verifier cross-checks that the old cover, immersion, paths and opposite edge accesses stay distinct. Adversarial tests mutate bin endpoints, one exact Rouché threshold, float inputs, period labels, depth compounding and the \(K'^2\) exponent. Unchanged source hashes are checked around the audit, no existing file is rewritten, and no verifier claims to check an analytic prime end, a QC extension or infinite convergence.

Reproduce at the repository root (Python 3.12, standard library only):
~~~sh
PYTHONDONTWRITEBYTECODE=1 python -B research/independent_audits/tip_family_global_marked_qc_20261116/verify.py
PYTHONDONTWRITEBYTECODE=1 python -B -m unittest discover -s research/independent_audits/tip_family_global_marked_qc_20261116 -p 'test_*.py' -v
~~~
The dedicated [CI workflow](../../../.github/workflows/tip-family-global-marked-qc.yml) also runs the unchanged prior finite suites, a Lean build, and requires the existing Research validation and Weighted Lean workflows to succeed on **the exact PR head SHA**. Passing CI tests only the finite programs and the formal layers actually present; it does not machine-check published complex-dynamics theorems.

## 6. Literature ledger: exact roles, not substitutes

1. **[LY97]** M. Lyubich and M. Yampolsky, *Dynamics of quadratic polynomials: complex bounds for real maps*, Ann. Inst. Fourier **47** (1997), 1219–1255, [DOI 10.5802/aif.1598](https://doi.org/10.5802/aif.1598), p. 1220 **Complex Bounds Theorem** (universal non-doubling alternative); p. 1219 definition of optimal modulus. Theorem 1.1 has a bounded-essential-period hypothesis and is **not** by itself the cited universal finite theorem.
2. **[DH85]** A. Douady and J. H. Hubbard, *On the dynamics of polynomial-like mappings*, Ann. Sci. ENS **18** (1985), 287–343, [DOI 10.24033/asens.1491](https://doi.org/10.24033/asens.1491), Ch. I §1 Straightening Theorem, Ch. I §§3–4 Beltrami and external mating. Local hybrid conjugacy and connected-filled-set uniqueness; **not** a global physical KKL marking comparison.
3. **[Ly-notes]** M. Lyubich, *Conformal Geometry and Dynamics of Quadratic Polynomials* ([lecture notes](https://www.dance-net.org/images/files/events/rtns2008/materiales/notes_lyubich.pdf)), Lemma 4.33, p. 143, quantitative modulus-dependent straightening. This is a draft lecture-note statement with editorial placeholders elsewhere, not a numeric certified \(K_{\mathrm{loc}}\).
4. **[BR86]** L. Bers and H. L. Royden, *Holomorphic families of injections*, Acta Math. **157** (1986), 259–286, extension of an already specified holomorphic motion (small parameter disk). An external marking motion is **not** supplied here.
5. **[S91]** Z. Słodkowski, *Holomorphic motions and polynomial hulls*, Proc. AMS **111** (1991), 347–355, [DOI 10.2307/2048323](https://doi.org/10.2307/2048323), extended lambda lemma. Requires an initial holomorphic motion with compatible marks; it cannot itself select one.
6. **[Sul]** Sullivan's invariant Beltrami/pullback technique, as explained in [DH85] Ch. I §§3–4, [McM94] and [Ly-notes] Ch. 2: pullback preserves \(\|\nu\|_\infty\) wherever it is defined. This gives **no initial marked map**, nor an ambient admissible-Wave naturality theorem.
7. **[McM94]** C. T. McMullen, *Complex Dynamics and Renormalization*, Annals of Math. Studies **135** (Princeton University Press, 1994), Chs. 10–11 on rigidity and real renormalization; Appendix A on QC modulus distortion, [publisher listing](https://press.princeton.edu/books/paperback/9780691029818/complex-dynamics-and-renormalization). Do not cite global rigidity as a full marked-KKL-slit extension.
8. **[Ah66]** L. Ahlfors, *Lectures on Quasiconformal Mappings* (1966), classical extremal-length/quasiconformal quasi-invariance. The distortion theorem applies **after** a map of the relevant surfaces is given; it cannot construct such a map.

**Hostile-review verdict.** Distinguished degree-two renormalized return from global iterate; local optimal annulus from arbitrary round physical gate; penultimate suffix from terminal portrait; coverage \(f_*\) from set-valued proper immersion \(\iota^*\); individual width from supremum; unproved two-sided transport from transported witnesses; \(K'^2\) from \(K'\); \(p\ge13\) from \(p\ge3\); strict finite bounds from non-strict limit bounds; an annulus countermodel to a *logical inference* from a genuine family counterexample; finite exact rational regressions from an analytic or Lean proof. The outstanding global marked-QC correspondence and numerical K'(mu) are **OPEN**, so no unconditional all-depth optimal-width sandwich is claimed.
