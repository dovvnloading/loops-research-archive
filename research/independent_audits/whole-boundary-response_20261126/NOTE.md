# Uniform additive whole-boundary response calibration

## 1. Target and current status

**Target:** H2_RESPONSE_REALIZATION (open in both canonical July registers).

Exact ledger statement: "The KKL, DL25, and virtual marked surfaces admit a common bounded-terminal response form with universal extremal-energy comparison, distortion, lift multiplicity, congestion, and electrical-orientation control."

**Result class: partial, a written analytic proof with an actual quadratic application.** The response-realization program in [network_response_state.md, §6](../../mlc_unified/network_response_state.md#6-analytic-response-realization-theorem) and [BC1, §§6, 8](../../mlc_unified/bc1_finite_port_response.md) asks for a uniform comparison, not merely generalized eigenvalues on a fixed block. The following establishes the missing uniform *additive* spectral comparison on the minimal whole-component marking, for all conformal shapes at fixed topological complexity, without assuming equality of the two kernels. It also gives an exact physical kernel counterexample to the purely multiplicative version on the archive's selected actual quadratics. This is not a counterexample to the ledger as written, which allows additive and richer-state remedies.

## 2. Claim and hypotheses

Let \(S\) be a connected compact bordered Riemann surface of genus \(g\) with \(b\ge2\) analytic boundary circles \(I_1,\ldots,I_b\). In the interior use the cusp-free conformal structure and the KKL **minimal** ideal marking (each entire boundary component is one interval). The identification of the analytic bordered surface with its ideal closure is part of the hypothesis. Write \(h=2g+b-2=-\chi(S)>0\); the minimally marked annulus is treated separately.

For \(x\in\mathbb R^b\) let
\[
 {\cal E}_S(x)=\inf_{u|_{I_i}=x_i}\int_S|\nabla u|^2\,dA
              =x^T\Lambda_Sx .
\]
The infimum is over Sobolev functions with the indicated constant traces, and is the actual conformally invariant Dirichlet energy, with no factor \(1/2\). Use the whole components as terminals, retaining their labels. For every unoriented eligible KKL arc class \(\alpha\), let \(q_\alpha\) be its unbuffered universal-cover quadrilateral width and \(w_\alpha=(q_\alpha-2)_+\) its canonical WAD coefficient. The source's canonical rectangles have disjoint interiors downstairs. Form the component-incidence Laplacian
\[
 L_{\rm can}=\sum_\alpha w_\alpha(e_{s(\alpha)}-e_{t(\alpha)})
                                  (e_{s(\alpha)}-e_{t(\alpha)})^T .
\]
This is a *whole-component* response, not an incidence-faithful representation of returning arc classes: they contribute zero to this observable and must be separately retained when used by a future proof. Write \(\operatorname{osc}x=\max x_i-\min x_i\) and \(P=I-\mathbf1\mathbf1^T/b\).

**Theorem (uniform all-potential comparison).**
\[
 0\le x^T(\Lambda_S-L_{\rm can})x
 \le 4h\,(\operatorname{osc}x)^2 \quad(x\in\mathbb R^b).
 \tag{1}
\]
In particular
\[
 L_{\rm can}\preceq\Lambda_S\preceq L_{\rm can}+8hP.
 \tag{2}
\]
For the minimally marked annulus the two forms agree exactly. The constants depend on topology only, not modulus, thinness, periods, winding, electrode separation, or numerical condition numbers. No equality of kernels, positive lower bound on generalized eigenvalues, or bound on the number of raw components is assumed.

The new ingredient is a cut-wise harmonic-flow decomposition with at most \(2h\) strips, followed by lifting the cut strips into the *same* universal-cover quadrilateral per arc class. This is not a reduction to fixed-block compactness or a total-width estimate: it controls the entire quadratic form with coefficient one on the leading term.

## 3. Evidence: analytic proof

### 3.1. Lower bound, including arbitrary potentials

The Dirichlet problem with piecewise constant **whole-component** values has a unique harmonic minimizer; smoothness across each analytic boundary in local half-disk coordinates follows by Schwarz reflection after subtracting the boundary value. Linearity of the problem gives the symmetric response matrix; constants are its kernel because the surface is connected. This is the all-Dirichlet specialization of BC1 Theorem 2.1, rather than its mixed-boundary electrode problem.

KKL Appendix A.2.1–A.2.3 defines the canonical lamination using the two-square buffers and asserts that the canonical rectangle laminations descend and form a lamination. Use each of the positive rectangles in its height-one, width-\(w_\alpha\) coordinate. On every crossing segment the actual harmonic minimizer changes by \(x_{t(\alpha)}-x_{s(\alpha)}\). Cauchy–Schwarz along that segment followed by integration in its transverse coordinate gives energy at least \(w_\alpha(x_{t(\alpha)}-x_{s(\alpha)})^2\). Integrate only in the canonical rectangles; they are disjoint, so sum without multiplicity. This proves \(\Lambda_S\succeq L_{\rm can}\). In particular \(D=\Lambda_S-L_{\rm can}\) is PSD and \(D\mathbf1=0\).

The claim does not use the printed maximal-selection or Wave arguments in KKL §6, or KKL A.13, and does not identify a geometric equipotential with a freely variable electrical trace.

### 3.2. Binary cut: actual gradient strips and their number

Fix any nonempty proper subset \(A\) of boundary labels, and set \(u\) equal to the harmonic minimizer with value one on \(A\) and zero on its complement. The maximum principle gives \(0<u<1\) inside. Hopf's boundary lemma gives a nonzero normal derivative everywhere on the boundary. There are finitely many critical points inside and their orders sum to \(h\): here is the count, including arbitrary genus.

Let \(\omega=2\partial u\). In a half-disk coordinate straightening an analytic boundary its coefficient is purely imaginary on the real seam, since \(u\) is constant there. Extend by negative complex conjugation onto the reflected copy. Thus \(\omega\) is a nonzero holomorphic one-form on the Schottky double of \(S\), a closed surface of genus \(G=2g+b-1\). Its zeros on the two halves are paired and there are none on the seam by Hopf's lemma. The total zero order of a nonzero holomorphic differential on a closed genus-\(G\) surface is \(2G-2\). For this count one can apply Poincare–Hopf to the metric dual of its real part: at a zero of order \(m\) the vector-field index is \(-m\), as is seen in the local primitive coordinate \(z^{m+1}\); away from zeros the vector field is nonvanishing. Dividing the count by two gives \(\sum m=h\) on \(S\).

Use oriented gradient trajectories of \(u\), parameterized on their regular portions by increasing potential \(t=u\), i.e. the vector field \(\nabla u/|\nabla u|^2\) in any smooth conformal metric. The trajectories are metric-independent under conformal rescaling. At a critical point of order \(m\) the local holomorphic primitive has a zero of order \(m+1\) after subtraction of its value. In its local root coordinate the \(m+1\) incoming gradient branches and \(m+1\) outgoing branches are precisely the alternating rays on which the imaginary part of that primitive is zero. Consequently at most
\[
 n_{\rm bad}\le\sum_{\text{critical }z}(m_z+1)\le 2h
 \tag{3}
\]
points of the zero boundary circles initiate trajectories that end at an interior critical point. A branch whose backward continuation hits another critical point does not add another boundary endpoint. Uniqueness of the regular ODE prevents branching or merging away from a critical point.

For clarity, a maximal regular trajectory reaching neither boundary nor a critical point cannot stop at an interior potential \(t_*\): compactness and the normalized vector field extend it if it stays in a compact set disjoint from zeros. Any limit at an interior stopping potential must therefore lie in the finite critical set. Indeed, if a regular point is a limit, local flow extends past that potential, by a flow box. The accumulation set of the continuous trajectory is connected, so a finite such set is one point. The local primitive coordinate identifies that trajectory with one of the finitely many separatrix branches. Boundary endpoints at levels zero and one are transverse and regular by Hopf. The same argument in reverse covers backward trajectories. Thus the set of points failing to lie on a regular zero-to-one trajectory is contained in the finitely many separatrices and critical points. It has area zero; each regular branch is a countable union of smooth compact arcs.

Every zero circle contains a bad point, unless \(S\) is an annulus. Otherwise all points of that circle flow to the one boundary without singularity. Local smooth dependence of the flow (including both transverse boundary ends), compactness of the initial circle, and uniqueness give an embedded closed cylinder swept by that circle over \(0\le t\le1\). Its interior is open in the surface by the flow box and closed relative to the interior of the surface by compactness of the cylinder and because both end circles are in the physical boundary. Connectedness makes the cylinder the whole surface, contrary to \(h>0\). This also excludes hidden uncut annular packets in the count.

Cut the zero circles at the bad points. There are exactly \(n_{\rm bad}\) open initial intervals, and each sweeps one disjoint open strip of regular zero-to-one trajectories. On such an interval use the transverse coordinate \(s\) given by integrating \(*du\) (choose the sign for increasing coordinate). The same closed one-form is exact on its swept strip: the flow box is topologically the product of the initial interval and \(0<t<1\), and \(*du\) annihilates its gradient direction. Thus \(s\) stays constant on each trajectory. The local harmonic-conjugate coordinates \((t,s)\) give a conformal bijection, up to the choice of orientation of the two coordinates, onto \((0,1)\times(0,a)\), where \(a>0\) is the transverse flux length of the initial interval. This is finite by boundary regularity; it is positive by Hopf. In these coordinates \(u=t\), the vertical crossing width is \(a\), and the actual energy of the strip is \(a\). The strips exhaust the surface up to the exceptional area-zero set. We obtain
\[
 {\cal E}_S(\mathbf1_A)=\sum_{\text{strips }R}a_R,\qquad
 \#\{R\}\le 2h .
 \tag{4}
\]

The proper leaves in one strip are simple by strict increase of \(u\), and all are homotopic with endpoints allowed to slide on the same two entire boundary circles, by the regular flow parametrization. Their endpoint components are distinct (opposite cut values), so no leaf is boundary-subordinate under the source A.1 definition. Hence each strip has one eligible KKL arc class.

### 3.3. Class-by-class comparison in one cover, no cutoff on winding

Group the strips by their unoriented class \(\alpha\); orient each from zero to one. For each class choose one ordered pair of universal-cover ideal intervals. Each simply connected strip of that class has a conformal lift whose two electrode sides lie on exactly this pair, by the usual endpoint-sliding relative homotopy lifting property. The lifts of *different* strips are disjoint because their interiors project to disjoint strips. They need not be adjacent in the cover.

The full quadrilateral between these two ideal intervals admits the extremal metric of the height-one rectangle of width \(q_\alpha\). Every lifted crossing leaf lies in the full path family, so its metric length is at least one. Cauchy–Schwarz and integration in each lifted strip rectangle give area at least \(a_R\) there; summing over the disjoint lifts yields
\[
 \sum_{R\text{ in }\alpha}a_R\le q_\alpha\le w_\alpha+2.
 \tag{5}
\]
This argument uses the *entire* strip, not a representative path or a finite search of deck words; if desired one can first integrate over compact transverse subintervals and increase to the open strip. In particular multiple strips in the same class pay the buffer error only once. There are at most \(2h\) distinct realized classes, by (3)–(4). Every one crosses the cut. The graph energy at a binary potential is precisely the sum of canonical weights crossing that cut. Equations (4)–(5) prove
\[
 0\le \mathbf1_A^TD\mathbf1_A\le 2\,\#\{\text{strip classes}\}\le4h .
 \tag{6}
\]
The empty and full cuts have zero energy. This improves on invoking the total canonical norm, which includes classes with both endpoints on the same side of the cut.

### 3.4. Every potential, coefficient one

Because \(D\) is PSD, \(x\mapsto (x^TDx)^{1/2}\) is a seminorm. Sort the distinct values of \(x\), \(t_0<t_1<\cdots<t_k\), and use the exact decomposition
\[
 x=t_0\mathbf1+\sum_{j=1}^k(t_j-t_{j-1})\mathbf1_{\{i:x_i\ge t_j\}} .
\]
The triangle inequality and (6) bound its seminorm by \(\sqrt{4h}(t_k-t_0)\). Squaring gives (1). Since \((x_i-x_j)^2\le2\|Px\|_2^2\), (2) follows. This argument works even when the WAD has no positive coefficient and even when \(D\) has positive off-diagonal entries. One cannot infer PSD from nonnegative binary tests alone; the lower bound in §3.1 is essential. On a minimally marked annulus the source canonical foliation is the full vertical cylinder, with no two-square subtraction. Its conductance equals the whole-electrode response by the elementary cylinder Dirichlet problem, proving the exception.

The theorem is an additive comparison; on any direction with \(x^TL_{\rm can}x>0\) and \(4h(\operatorname{osc}x)^2\le\varepsilon x^TL_{\rm can}x\), it gives relative comparison with factor \(1+\varepsilon\). With the archive's cell normalization \(r_B\), divide (1) by \(r_B\); the error is at most \(4h/r_B\) times the squared oscillation, uniformly if normalized topological charge is bounded. The number of whole-component terminals itself is \(b\); this does not bound \(b\) when it is allowed to grow.

### 3.5. Actual allowed electrical operations, with the error preserved

For a finite collection of such surfaces, assign each whole electrode to a labeled node of a finite network. Gluing here means **explicitly requiring one common constant trace** at each identified node; interiors are independent. Summing the individual energies for fixed node potentials gives the exact energy of this constrained variational problem, by independent minimization. This is also the exact parallel rule on a genuinely disjoint union with shared prescribed potentials. Put \(C=\sum_j4h_j\), with zero for minimally marked annuli. The summed forms satisfy \(0\le E_{\rm surf}(z)-E_{\rm can}(z)\le C(\operatorname{osc}z)^2\). Retain a nonempty set of terminal nodes with values \(x\) and eliminate floating constant node values \(y\). Let \(y_0\) minimize the graph energy (the quotient-safe minimization exists even for disconnected components). Clip every free value to \([\min x,\max x]\); no graph edge energy increases because all graph conductances are nonnegative. The clipped values are still a minimizer and now \(\operatorname{osc}(x,y_0)=\operatorname{osc}x\). Therefore
\[
 0\le\inf_y E_{\rm surf}(x,y)-\inf_y E_{\rm can}(x,y)
 \le E_{\rm surf}(x,y_0)-E_{\rm can}(x,y_0)
 \le C(\operatorname{osc}x)^2.
 \tag{7}
\]
This gives a uniform error under any finite sequence of those exact constant-electrode identifications/eliminations; count each original component once. It neither assumes equal kernels nor multiplies fixed-block comparison constants. It is **not** a comparison for arbitrary physical cut traces or for a dynamically identified neck. It requires the constant-trace constraint; otherwise the admissible Sobolev space differs. In particular it supplies no proof of the source itinerary-faithfulness premise of BC1 Theorem 5.1.

## 4. Actual quadratic application, not a planar-model substitute

Use the selected near-\(-2\) primitive-tip family \(f_{c_p}(z)=z^2+c_p\) in the archive, \(p\ge13\). In the [all-period realization theorem](../real_primitive_tip_family_all_p_20261116/NOTE.md), \(q=4^{-p}\), \(c_p\) is the unique simple zero of \(x_{6p}(c)+x_{3p}(c)\) in the signed chart \(14q<c+2<16q,\ |x_p|<14q,\ -2<\tau=A_px_p<1/4\), with the stated positive intermediate itinerary and return signs \(+--+-+\). Here \(x_j=f_c^j(0)\), \(A_p=\prod_{j=1}^{p-1}2x_j<0\). At the root \(-1795/1000<\tau<-1785/1000\). The imported actual restriction and strict orders are (O1),(O2),(R); the lower scale bound \(|A_p|>(3/20)4^p\) is from its signed coefficient estimate. No uniqueness in an unspecified maximal window is asserted.

In the positive physical coordinate \(X_j=-A_px_{jp}\), the [physical bridge](../../tip_family_theorem/PHYSICAL_BRIDGES.md) and [canonical exclusion, §§1, 5](../canonical_width_attack_20261124/NOTE.md) identify the actual surface
\[
 Y_p=D(0,R)\setminus(K_0\cup K_1\cup K_2),\quad R=|A_p|2^{-p},
\]
\[
 K_0=[X_3,X_6],\quad K_1=[X_4,X_1],\quad K_2=[X_2,X_5],
 \qquad -R<X_2<X_5<X_3<0<X_6<X_4<X_1<R .
\]
This is the literal four-boundary surface in the canonical exclusion note, not its tree-annulus refinement and not a chosen matrix example. The physical ideal boundary at each slit is the two banks with their tips, resolved in the local square-root coordinate at each tip; the outer circle is ordinary analytic boundary. These charts are conformal, give analytic boundary circles in the bordered compactification, and identify precisely the four whole-component electrodes with the actual ideal marking. For the interior this is just the physical identity in the positive coordinate, preserving energy by conformal invariance. The strict order verifies disjoint, nondegenerate slits; the finite connectivity gives \(g=0,b=4,h=2\). There is no assumption about independent immersion MARK or all-path transport in this identification.

The cited all-class exclusion proves \(q_\alpha<1999/1000\) for every eligible \(\alpha\) on exactly this surface for \(p\ge10\). Its input includes the embedded physical peripheral rings, the two-oriented-shadow bound for returns, the collar lemma, and exact finite/tail interval bounds (5), (18), (21)–(23). We use that theorem as an existing written bound, not as numerical sampling. For the present \(p\ge13\) it gives \(L_{\rm can}=0\) and also *all* canonical returning weights zero. Formula (1) therefore gives
\[
 0<{\cal E}_{Y_p}(x)\le8(\operatorname{osc}x)^2
       \quad\text{for every nonconstant }x .
 \tag{8}
\]
Strict positivity follows from uniqueness and connectedness: a zero energy harmonic minimizer is constant. This yields, for example, an exact actual polynomial counterexample to any purely multiplicative upper comparison \(\Lambda_{Y_p}\preceq M L_{\rm can}\), for **any** finite \(M\), already at the exact root \(c_{13}\) specified above, by \(x=(1,0,0,0)\). It is not a refutation of a topology-charged response comparison, and (1) supplies the corrected all-potential statement. The actual surface theorem also applies to the certified finite selected \(10\le p\le12\) by the same four-boundary hypothesis and existing exclusion, but the following tail bound uses the signed chart and is stated only for \(p\ge13\).

There is a second genuine physical effect even though the corrected additive estimate is uniform. By (O2) and \(|X_1|=|\tau|<2\), all slits lie inside \(|z|<2\), while \(R>(3/20)2^p\). Take the whole-electrode vector \(x=e_{\rm out}\) (outer value one, all three slit values zero). Use the explicit admissible trial potential \(u=0\) for \(|z|\le2\) and \(u=\log(|z|/2)/\log(R/2)\) for \(2<|z|<R\). Direct polar integration on the actual annulus gives
\[
 0<{\cal E}_{Y_p}(e_{\rm out})\le {2\pi\over\log(R/2)}
       <{2\pi\over(p-4)\log2}, \qquad p\ge13,
 \tag{9}
\]
since \(3/40>1/16\). This function is continuous and piecewise smooth with finite energy, hence admissible in the stated Sobolev problem. Since \(\|Pe_{\rm out}\|^2=3/4\), the minimum eigenvalue of the positive form on \(\mathbf1^\perp\) is at most \(8\pi/[3(p-4)\log2]\) and tends to zero. Thus even with a fixed four-electrode labeling, bounded normalized topology and bounded response from (8), there is no uniform positive spectral floor of the exact whole-boundary form. The proper statement of the coercivity question must retain a normalization or information distinguishing this outer-neck degeneration; we do **not** assert this sequence satisfies the other hypotheses of global H3 or is an infinite tower. Each \(p\) is a different actual polynomial.

## 5. Dependencies and first point of failure

The ledger dependency path is H2_RESPONSE_REALIZATION -> H2_CALIBRATION and H2_VALUE_FEATURE_REALIZATION -> the forward/summability/cone gates -> MBTT -> H3_COERCIVITY -> H4_RIGIDITY. Arrows here mean "feeds", not a new logical implication. We claim only H2_RESPONSE_REALIZATION, partially. The direct dependency statements and the target's §6 ten clauses were checked against the two registers. The proof consumes source KKL Appendix A.1, A.2.1–A.2.3 (minimal marking, rectangles, canonical disjoint lamination), classical Dirichlet minimization, Hopf's boundary lemma, Schwarz reflection, covering-space path lifting and the Poincare–Hopf index theorem (the differential zero count was derived above), and the named already-written selected-family physical results in §4. No DL25 bounds, virtual realization theorem, KKL §6 induction, or open premise in the ledger is used to prove (1).

For the exact §6 response-realization specification:

| Clause | Scope of new result / first unmet requirement |
|---|---|
| 1 bounded future-closed ports | Exactly \(b\) whole-circle electrodes, uniformly four on the actual family. Positive self-access is electrically invisible in general; zero on the selected family. Future access refinements and universally bounded ports over all virtual blocks are not established. |
| 2 surface/terminal energy comparison | **Proved** (1)–(2) for every whole-electrode potential modulo constants, topology-additive with coefficient one. Full nonconstant traces and subdivided marking excluded. |
| 3 itinerary elimination | (7) controls genuine constant-electrode eliminations; first missing premise is that the actual restriction itinerary acts on those same constant electrodes with no omitted trace variables. |
| 4 parallel independence | Proved for disjoint component interiors with identical constrained electrode potentials, and disjoint canonical rectangle carriers in the lower bound. Arbitrary WAD support disjointness does not imply independence of actual glued surfaces. |
| 5 distortion, lift multiplicity, congestion | Identity physical coordinate (degree one, conformal), injective per-strip lifts, no double counting in (5). No comparison across DL25/KKL or virtual charts. |
| 6 labels and orientation | Preserved whole-component labels; zero-to-one strip orientation and exact endpoint lifts used. Finer ribbon/access labels and later restrictions not realized. |
| 7 Value observability | Not proved. Different classes with the same two components may have distinct Value weights; self-classes also vanish in this graph. (1) does not give a Value comparison. |
| 8 topology and standard-width charge | Explicit \(4h/r_B\) error in response units after dividing by the same \(r_B\). No control of raw marking count, standard-width term, or normalized Value units. |
| 9 gauge contraction | Not proved. Uniform additive static comparison plus (7) does not give the direction or strict factor of a complete dynamical block. |
| 10 complete traces | Constant electrode values are a prescribed boundary condition here, not a property inferred from being a dynamical equipotential. A genuine full-trace neck, welding, no-bypass and all-depth contact control remain open. |

The first barrier to extending this proof to the as-stated gate is the construction of a bounded, future-closed, access-refined electrode set with the correct trace space (clauses 1, 3, 5, 6, 10). Adjacent electrodes can force non-Sobolev jumps, and eliminating full trace functions cannot be replaced by (7). Further, translating topology charge into Value error and composing complete transitions remain separate obligations. We do not close the gate even on the selected family as a **complete block**. This is a substantive sub-clause proof and an actual parameter obstruction to a stronger comparison, not category (a), (b), or (c) for the whole ledger statement.

## 6. Reproduction and limits

From the repository root with Python 3.12:

    python -B research/independent_audits/whole-boundary-response_20261126/check_response.py
    python -B code/verify_physical_bridges.py

The new executable uses only the standard library and exact rational arithmetic. It checks a PSD residual with nonpositive and positive off-diagonal entries, all 16 binary cuts, 625 integer test vectors, a Schur elimination on 125 vectors, a non-PSD form whose binary cuts are nonnegative, and the exact rational radius and Rayleigh normalizations in (9). The output is deterministic JSON. This is regression evidence for algebra/normalization only; the analytic strip decomposition and physical proof are written mathematics, not machine-formalized or certified by those finite vectors. The existing actual-family bounds are imported as written and were not reexecuted locally. The new arithmetic test was run locally, but network access for a local full repository checkout was unavailable; the full bridge check is in the new read-only workflow. The executable is mapped to RESPONSE in the source register. No ledger, paper, theorem contract, or bridge status is changed.

**Reading boundary:** the five mandatory files were retrieved at the pinned base commit; both complete JSON registers were parsed and their target/dependency statements compared. Because of tool output limits, the large prose files were inspected by headings and target passages rather than every line; the full 195-node transitive dependency closure (58 distinct evidence references, including documentary crosswalks) was traced but not exhaustively read line by line. The proof uses only the explicitly identified source and physical premises above. This is not a completed dependency audit of the universal gate. The pinned base is 6ba50a4b452f7703c17200dd3b3bab4b117ee413.

## 7. Attribution and AI disclosure

Credit Kahn, Kapiamba and Lyubich, [MLC for parabolically bounded primitive renormalization, arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), Appendix A.1, A.2.1–A.2.3 (source definitions and canonical rectangle theorem; versioned HTML lines 1551–1609). The source explicitly permits whole-component markings and gives the distinct minimally marked annulus convention. The proof does not consume any of their presently disputed Section 6 statements. Credit the classical harmonic Dirichlet, reflection, maximum/Hopf and Poincare–Hopf theorems for the named general analysis inputs; the zero-order derivation, flow counting and cut-to-form estimates are given here. Credit Matthew Robert Wesney and the archive's earlier selected-family physical and exact interval arguments, with their attribution and restrictions preserved.

OpenAI ChatGPT GPT-6.2 was used for proof search, derivation, red-team checks of the cut/flow argument, repository inspection, test generation and drafting. No human specialist verification or independent peer review has been performed. No claim of MLC, ledger promotion, or outside researcher endorsement is made.
