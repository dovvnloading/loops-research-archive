# Canonical KKL WAD versus physical opposed electrodes: a typing obstruction

**2026-11-16. Independent audit; no MLC assertion.** This addresses the
precise application question left open in
[`wave_vs_dirichlet_contact_transfer_20261115/NOTE.md`](../wave_vs_dirichlet_contact_transfer_20261115/NOTE.md),
using the *unchanged* physical tip manifest
[`results/tip_KKL_tree_marked_breakage_20261109.json`](../../../results/tip_KKL_tree_marked_breakage_20261109.json).
The conclusion is a **negative answer to the literal common-surface/electrode
identification**, not an unproved computation of canonical WAD coefficients.
In particular, **the canonical WAD, a valid marked Wave, and the existential
nearly maximal Wave selected in the KKL proof are three different notions**.

Source: Kahn–Kapiamba–Lyubich (KKL),
[*MLC for parabolically bounded primitive renormalization*, arXiv:2606.27272v1](https://arxiv.org/abs/2606.27272),
§2.5–2.6 (tree and canonical Hubbard arc diagrams), §§4–5
(canonical WAD on \(U\setminus\mathcal K\)), §6 and §6.1
(tree waves on \(U\setminus T\)), Appendix A.1
(paths and waves), A.2.1–A.2.3 (buffers and canonical WAD), A.3.1–A.3.4
(cover, immersion and restrictions). The unbuffered ideal-quadrilateral widths
and the new topological typing statements below are **analytic inputs**, not
claims that the finite Python checker formalizes complex analysis.

## 1. Which canonical object the source actually defines

The source defines **two different marked surfaces**, and their conflation
would invalidate the audit. On the actual physical tip let
\[
\begin{split}
\mathcal K&=K_0\cup K_1\cup K_2,\\
K_0&=[x_9,x_{18}],\qquad K_1=[x_{12},x_3],\qquad
K_2=[x_6,x_{15}],\\
Y_K&=U_3\setminus\mathcal K,\qquad U_3=D(0,1/4),\\
Y_T&=U_3\setminus T,\qquad T=[x_6,x_3].
\end{split}\tag{1a}
\]
These three disjoint small filled Julia intervals and their source-dependent
identification are the previously certified physical data of PR #68.
The verifier independently recomputes and encloses all six endpoints
using the unchanged dyadic parameter. The tree \(T\) connects them.

**The proof-used canonical WAD** is the canonical object on
\((Y_K,\mathcal I_{\min})\), as specified explicitly in KKL §2.6,
Proposition 4.2 and §5. Its **minimal** marking consists of the
*four entire Carathéodory boundary components*: the three small Julia sets
\(K_0,K_1,K_2\) and the outer boundary of \(U_3\).
This is a disk with **three disjoint holes**, *not* the tree annulus.
KKL §5 actually uses its horizontal-plus-vertical part,
\(X=W^{h+v}_{\rm can}(Y_K,\mathcal I_{\min})\), dropping bivertical
arc classes. Horizontal means two small-Julia endpoints and vertical
means exactly one small-Julia endpoint (KKL §2.6). Thus \(X\) is
precisely specified once the complete canonical WAD is.

Separately, **the §6 proof-selected Wave** inhabits
\((Y_T,\mathcal I_T)\), the **tree annulus** with the original ten-atom
inner marking induced by \(K_0,K_1,K_2,\alpha\) and the whole outer
component. KKL §4 and §6 specify this different marking. Although one
can also construct the canonical WAD of \((Y_T,\mathcal I_T)\) using
Appendix A.2, that would **not** be the proof-used canonical WAD
\(W_{\rm can}(Y_K)\); constructing it would not solve the requested
identification.

For each admissible simple arc class \(\gamma\) of the *actual*
minimally marked \(Y_K\), lift its two ideal boundary intervals to
\(\widetilde I,\widetilde J\) in the universal cover of \(Y_K\). Let
\(q_\gamma\) be the **unbuffered** width of their ideal quadrilateral.
The complete canonical WAD, and its exact proof-used projection, are
\[
\boxed{\begin{split}
W^{\rm can}_{Y_K,\mathcal I_{\min}}(\gamma)&=
  (q_\gamma-2)_+=\max(q_\gamma-2,0),\\
X(\gamma)&=\mathbf1_{\{\gamma\text{ horizontal or vertical}\}}
  (q_\gamma-2)_+ .
\end{split}}\tag{1}
\]
For \(q_\gamma>2\), Appendix A.2.1 deletes **two unit-square
buffers**; otherwise the leaf packet is empty. The special
minimal-marked-*annulus* clause of A.2.3 does **not** apply,
since \(Y_K\) is not an annulus. This is the source's **complete,
implicit maximal WAD construction**, rather than a hand-selected Wave,
and the proof-used truncation is specified without substituting
\(Y_T\) for \(Y_K\). The formula is not an evaluated numerical answer:
the conformal quadrilateral widths \(q_\gamma\), their positive
support, the values of \(\|W^{\rm can}\|\) and \(\|X\|\) are
**not** enclosed here. Their evaluation would require a rigorous
uniformization/cross-ratio enclosure on the actual three-hole
physical surface. No value of the separate tree Wave can be
assigned to these weights.

Moreover, KKL's *maximality* is the additive estimate
\(W_{\rm valid}(\gamma)\le W^{\rm can}(\gamma)+2\), **not** an identity
between the canonical weight and the supremum of all valid Wave widths.
The native marked circular packet \(S_{\rm full}\), of width
\(\log(4/3)/(2\pi)<1/20\), cannot even imply that a corresponding class has positive
canonical buffered weight by this estimate; the packet is on the
**different** surface \(Y_T\), so the class requires an independently
specified transfer before this comparison can even be formulated.

The §6 proof uses yet another choice: in the proof of Proposition 3.9
following Lemma 6.1, it **chooses** an \(\eta\)-controllable wide Wave
\(\mathcal A\) *nearly maximal* among such Waves, within a factor
\(1+\delta\). That is an existential choice, not a canonical
construction from \((Y_T,\mathcal I_T)\); no unique Wave or selection algorithm
at this finite tip is prescribed. Its large-width/controllability inputs
are not established for this tip. Therefore the phrase **"the
proof-selected canonical Wave" has no defined referent here**. Neither
the canonical WAD nor the exhibited \(S_{\rm full}\) can be silently
identified with that existential choice.

## 2. Exactly where electrode incidence fails

The **canonical** surface \(Y_K\), the **tree-Wave** surface \(Y_T\),
and the **physical source slit** are three different Riemann surfaces.
The native covering/immersion diagram belongs to the tree surface:

\[
\begin{array}{ccc}
X_\mathrm{src}=V_3\setminus T'&\xrightarrow{\quad f_*=G_*\quad}&
       Y_T=U_3\setminus T\\
\big\downarrow\iota&&\big\Vert\\
Y_T&=&Y_T,
\end{array}
\qquad G=f_{c_*}^3,\quad T'=[-x_3,x_3],
\quad\iota\text{ the inclusion}.\tag{2}
\]
Here \(G\) **is** a holomorphic degree-two covering on the punctured
surfaces, while \(\iota\) is a **different**, nonproper-on-attachment
holomorphic immersion. In KKL Appendix A.3, \(f_*\) pushes forward
covering lifts; \(\iota^*\) **restricts** target proper paths to the
source, potentially in several disconnected proper pieces. The dynamic
operator is \(F_*=f_*\iota^*\), not a deck-preserving conformal
identification of the two surfaces.

The complete new physical attachment and its deck-opposite are
\[
X=T'\setminus T=[-x_3,x_6),\quad
A_X=\partial_C X\subset\partial_C T',\quad
B_X=\tau A_X,\quad\tau(z)=-z.\tag{3}
\]
In the source Joukowski chart
\(z=(x_3/2)(w+w^{-1})\), \(\tau(w)=-w\). The exact source
orbit enclosures give
\[
 \ell_X=2\arccos(-x_6/x_3),\qquad
 \boxed{\frac65<\ell_X<\frac75<\pi},\tag{4}
\]
so \(A_X,B_X\) are genuinely **disjoint, positively separated** source
inner Carathéodory arcs. Their separation is *not* the problem.

The original source has twenty covering atoms \(S_0,\dots,S_{19}\).
The complete attachment comprises \((S_{19},S_0,S_1)\); a half-turn
of the source prime-end circle sends it to \((S_9,S_{10},S_{11})\).
The unchanged manifest plus exact cyclic arithmetic yield:

| Physical electrode | Source covering atoms | Images under \(f_*\) | Hosts under \(\iota^*\mathcal I\) |
|---|---|---|---|
| \(A_X\) | \(19,0,1\) | \(I_9,I_0,I_1\) | \(I_0,I_0,I_0\) |
| \(B_X=\tau A_X\) | \(9,10,11\) | \(I_9,I_0,I_1\) | \(I_4,I_5,I_6\) |

This is forced by the **two distinct** exact atom maps:
\[
 f_*(S_j)=I_{j\bmod10},\qquad
\iota^*(I_k)=\bigcup_{j\in P_k}S_j,
\quad P_0=(18,19,0,1,2),\ P_4=(7,8,9),\ P_5=(10),\ P_6=(11,12,13).
\tag{5}
\]
The sets \(P_k\) are the original attachment-aware pullback blocks,
not the covering fibers. In particular \(\iota\) is **not proper** at
\(A_X\): the complete new attachment prime-end sides map to *interior
points* of \(Y\). Its host interval is end-proper but not proper.

There is an independent, coordinate-free check of the covering collision:
\(G(z)=((z^2+c_*)^2+c_*)^2+c_*\) is even, and the certified real
monotonicity on each half of \(T'\) gives, with endpoint closures,
\[
 \boxed{G([-x_3,x_6])=G([-x_6,x_3])=[x_6,x_9].}\tag{6}
\]
Thus \(G(A_X)=G(B_X)\) as *target prime-end arcs*. **The covering
collapses the opposition**. It does not send two opposed source electrodes
to two disjoint target electrodes. The immersion is not an alternative
proper inverse because its attachment boundary maps into target interior.

For comparison, the actual, original-marked target Wave in PR #68 has
base \((I_9,I_0,I_1)\) and ends \((I_9,I_1)\). Its two surviving
\(\iota^*\)-restrictions have source endpoint pairs
\((S_3,S_1)\) and \((S_{19},S_{17})\). **Neither** has one end on
\(A_X=(S_{19},S_0,S_1)\) and the other on
\(B_X=(S_9,S_{10},S_{11})\). These are a genuine marked Wave and
proper surviving source restrictions, but *not* the canonical WAD or a
source condenser family; the pairs are used only as a control of correct
source-versus-target typing.

**Exact failed clause in the 2026-11-15 comparison theorem (6):** a
Wave must be a family **on the very cylinder**
\(C_h=(0,h)\times S^1\), with **every leaf** a connecting curve in
\(\Gamma_h(A_X,B_X)\) and both endpoints typed to those particular
source electrodes. The proof-used canonical \(W^{\rm can}_{Y_K,\mathcal I_{\min}}\) is on
\(Y_K\), the proof-selected Wave is on \(Y_T\), and neither is a
curve family on the physical source \(C_h\). No source-endpoint-respecting identification
exists via either native map in (2). Even the known native Wave's
restrictions fail the required endpoint clause. **Equation (6) cannot
be applied to the canonical target WAD at this tip.** This is a
negative *applicability verdict*, not a numerical statement that a
particular unknown canonical weight is bigger/smaller than \(D_h\).
The vacuous possibility that some canonical coefficient is zero does not
supply a nonempty electrode Wave or a positive reverse inequality.

## 3. What the physical capacity still proves; what a repaired transfer needs

The full **free-outer** source cylinder uses \(A_X,B_X\) on its inner
edge, with no outer voltage pins. As proved analytically in the preceding
note, for every \(h\in(0,1/1024]\),
\[
\left[\frac{\pi}{2h}+
 \frac4\pi\left(\frac32+\log(1+2/\ell_X)\right)\right]^{-1}
 \le D_h(\ell_X)\le\frac{2h}{\pi-\ell_X}.\tag{7}
\]
The independent exact 256-bit dyadic orbit, rational cosine/
Machin-\(\pi\)/atanh-log brackets in the new verifier establish at the
physical height \(h=1/1024\), strictly,
\[
\boxed{\frac{3}{5120}<D_{1/1024}(\ell_X)<\frac3{2560}.}\tag{8}
\]
The full physical source collar lies in \(V_3\setminus T'\), by a
**whole-collar** derivative bound, not sampled boundary points.
For the **different, exhibited noncanonical** target packets,
\(1/25<W(S_{\rm full})<1/20\) and
\(W(S_h)=h/(2\pi)\), so at this height
\(W(S_h)<D_h<W(S_{\rm full})\). These inequalities cannot be
relabelled as inequalities for \(W^{\rm can}\); (8) is a capacity
certificate **only**, not the desired canonical comparison.

A precise **sufficient correction** for a genuine Wave \(\mathcal A\)
is to exhibit a leafwise family of proper **source restrictions**
\(\mathcal R\subset\iota^*\mathcal A\) for which:

1. Every leaf of \(\mathcal A\) has a restriction in \(\mathcal R\);
   every curve of \(\mathcal R\) lies in the *actual* source collar
   \(C_h\) and joins \(A_X\) to \(B_X\), with both source prime ends
   verified **after** the A.1/A.3.2 filters.
2. A quantitative *richness/coverage* certificate holds: every Borel
   metric \(\rho\) admissible for \(\mathcal R\) can be extended to a
   metric admissible for the full \(\Gamma_h(A_X,B_X)\) with energy at
   most \(C\int\rho^2\) (or a comparably explicit dual capacity bound).
3. The immersion restriction loses at most a controlled factor of
   width: \(W(\mathcal A)\ge\kappa W(\mathcal R)\), with \(\kappa>0\).
   Neither a degree-two cover nor KKL Lemma A.11 provides this reverse
   inequality automatically.

Under these explicit **sufficient** additional assumptions, the
ordinary width monotonicity and KKL Lemma A.11 give
\[
 \boxed{\frac{\kappa}{C}\,D_h(A_X,B_X)
 \ \le\ W(\mathcal A)\ \le\ D_h(A_X,B_X).}\tag{9}
\]
Indeed condition 1 and A.11 imply
\(W(\mathcal A)\le W(\mathcal R)\le D_h\); condition 2 implies
\(D_h\le C W(\mathcal R)\); condition 3 supplies the missing lower
comparison. The conditional **upper constant is exactly 1**; the
conditional lower constant is \(\kappa/C\). If a quasiconformal rather
than conformal comparison is used, the corresponding distortion factors
must also be proved and inserted. To apply (9) to the **norm of a
canonical WAD**, first establish a wave-component decomposition and
energy accounting: a WAD coefficient/norm is not automatically a single
Wave width. No \(C,\kappa\) are certified at this tip; there is no
stage-uniform assertion.

## 4. Reproducibility and hostile-review boundary

Run from repository root:

```sh
python research/independent_audits/canonical_wad_electrode_incidence_20261116/verify.py --check-manifest
python -m unittest discover -s research/independent_audits/canonical_wad_electrode_incidence_20261116 -p 'test_*.py'
```

The verifier **recomputes**, with no binary floats: the exact source
parameter interval and outward 256-bit orbit; and checks the original ten/20
marking and nonproper attachment block against the independent cyclic partition; the full cyclic deck shift,
covering labels and independently listed immersion host labels;
attachment-image collision, electrode disjointness and source-endpoint
mismatch; whole physical collar; strict rational upper/lower capacity
brackets. It regenerates the deterministic
[`results/canonical_wad_electrode_incidence_20261116.json`](../../../results/canonical_wad_electrode_incidence_20261116.json).
Negative-control tests alter the parameter, covering map, immersion,
attachment and surviving Wave endpoints; every mutation must be
rejected. The dedicated CI workflow also runs the unchanged physical
Wave/condenser verifiers and dispatches the existing research-validation
and Lean workflows on the **exact PR head**.

**Hostile-review guards:** (0) §5 canonical \(U\setminus\mathcal K\),
§6 tree \(U\setminus T\), and source \(V_3\setminus T'\) are three
**distinct** surfaces, with different original/minimal markings;
(i) the full \(A_X\) prime-end boundary is
used, not just a short open geometric segment; (ii) the deck shift is
on the 20 **source** atoms, not a shift on target atoms; (iii)
\(f_*\) and \(\iota^*\) are computed separately, and \(\iota\)'s
nonproperness is not reinterpreted as a covering branch; (iv) exact
parameter dyadics are not rounded; (v) the source and target annular
heights are **not** conformally identified; (vi) outer condenser
boundary is free/Neumann; (vii) no Wave buffer of size 2 is ignored;
(viii) no implicit uniqueness or nonemptiness of a proof-selected
Wave is assumed; (ix) no inequality for an unknown canonical WAD
coefficient is inferred from a small valid sub-Wave; and (x) a finite
checker does not formalize a continuum prime-end or Dirichlet theorem.

**Proved (written source-dependent):** the distinct natural surfaces,
the §5 canonical \(U\setminus\mathcal K\) WAD's exact clipped-quadrilateral
*definition* and horizontal/vertical truncation, lack of
a uniquely proof-selected Wave, deck-opposed electrode collision under
\(G\), nonproper attachment under \(\iota\), failed common-electrode
hypothesis, and corrected **conditional** transfer (9).
**Finite-certified:** physical dyadic orbit and angular separation,
cover versus immersion atom maps, source Wave endpoint countercheck,
whole-collar bound, and rational enclosure (8).
**Numerical-only:** none.
**Open:** actual values/support of the buffered canonical WAD and its
§5 horizontal/vertical truncation on the three-hole surface; any
chosen §6 nearly maximal wide Wave at this finite tip; a source
restriction family with electrode incidence and richness; a positive
reverse constant; uniform control over stages/rotation; and any
prime-primitive renormalization, MLC or critical-return consequence.
This note makes no claim of independent specialist validation.
