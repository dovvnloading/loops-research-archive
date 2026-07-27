# Virtual tame full-return theorem: source audit, conditional proof, and exact gaps

## 1. Verdict

This note attacks the open obligation `H2_VIRTUAL_TAME_FULL_RETURN`.

The result is deliberately split into a proved implication and an unproved
realization statement.

1. Kahn--Kapiamba--Lyubich (KKL) Proposition 3.8 is not a consequence of
   per-limb occupancy, access completeness, or partial invariance. Its proof uses one
   complete small-Julia cycle, the full return \(G=(f^s,\iota_s)\), a selected
   localization of that return, a bounded critical-encounter count on the selected
   component, an ordered canonical-WAD domination witness, the Wanderers Theorem on
   that same cover, and one source-identified Value functional.
2. A conditional **Virtual Tame Full-Return Transfer Theorem** is proved in
   Section 7. Once the package in Section 6 is realized, KKL's tame contradiction
   transfers with constants independent of the cycle period \(s\) and denominator
   \(q\).
3. The current virtual-hull documents do not realize that package. In particular,
   the stagewise one-critical-orbit telescope in
   `finite_horizon_inflation.md`, Theorem 10.2 is not the localized full pullback
   used by KKL: the latter may contain several sheets and has degree \(2^{m_I}\),
   where \(m_I\) counts critical encounters inside the selected full-return
   component.
4. A quantitative coordinate forced by the full-return part of the source proof is
   not just component occupancy. It is the **localized critical-encounter
   multiplicity**
   \[
     m_I
     =
     \#\{0\le j<s:
       \text{the selected stage domain over }I
       \text{ contains the quadratic critical point}\}.
   \]
   One also needs bounded localized topology and end multiplicity. The useful
   package is
   \[
     \mathfrak c_I
     =
     \bigl(m_I,\ |\chi(V_I)|,\ |\mathcal B_I|,\ d_I\bigr),
   \]
   where \(d_I\) is the multiplicity on the distinguished starting ends in the
   Wanderers application.
5. A general rotation \(a/q\) cannot be converted to KKL's rotation \(1/q\) merely
   by relabeling limbs while retaining their cyclic order. A continued-fraction or
   molecule acceleration theorem preserving the ribbon order is an independent
   obligation.

Thus `H2_VIRTUAL_TAME_FULL_RETURN` remains open. This note does not prove a virtual
tame amplification theorem for Dudko's proposed hulls, the Master Transition Lemma,
or MLC.

## 2. Source lock

Primary sources:

- J. Kahn, A. Kapiamba, and M. Lyubich,
  [*MLC for parabolically bounded primitive renormalization*](https://arxiv.org/html/2606.27272),
  arXiv:2606.27272v1, 25 June 2026;
- D. Dudko,
  [*On the MLC Conjecture and the Renormalization Theory in Complex Dynamics*](https://arxiv.org/html/2512.24171),
  arXiv:2512.24171, especially Interpolation Problem 4.4.

The complete KKL v1 source archive was audited. The relevant hashes are:

| file | SHA-256 |
|---|---|
| `waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| `not-all-good2.tex` | `B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01` |
| `value1.tex` | `2767F71E57862DA5CF50FF7B96FC08917E24CA8F9BD2D4523C467B2E896AD83A` |

The line references below refer to those files in that archive.

The KKL tame proof is not literally self-contained in Section 5. It invokes:

- Kahn's 2006 paper for transfer of the combinatorial model to
  \(\psi\)-quadratic-like maps and for canonical-WAD pullback domination;
- McMullen's boundary-width comparison, with an alternative citation to the
  Feigenbaum work of Dudko--Lyubich;
- the Kahn--Lyubich quasi-additivity paper for routes and the Galois closure used in
  the Wanderers proof.

Those imported results remain valid inputs in KKL's category. They are not licenses
to assert their analogues for a partially invariant virtual hull.

### 2.1 Printed-source cautions

Four source issues must be quarantined rather than silently propagated.

1. `waves-with-Misha.tex`, line 698 reverses the definition of amplification. The
   controlling definition at lines 486--492 and the actual Section 5 argument use
   \[
     \mathbb W(F)\ge L\mathbb W(\mathcal RF).
   \]
2. `value1.tex`, line 12 prints a one-step factor for every \(n\), while the proof
   at lines 96--111 proves the required
   \[
     V((f^n)^*X)\le\lambda_F^{-n}V(X).
   \]
3. KKL Appendix C's finite clone equation has the exponent orientation already
   refuted in this project. The replacement used here is
   `corrected_clone_theorem_derivation.md`, including convergence of both typed
   Perron vectors.
4. `value1.tex`, lines 115--120 interchange the words "minimum" and "maximum" in
   the final sentence. The Section 5 proof uses the actual minimum and maximum in
   the usual order.

These are local source defects. None supplies a counterexample to KKL Proposition
3.8, but the clone defect prevents importing its printed algebra verbatim.

## 3. Exact source theorem and notation

To avoid the collision in KKL between the rotation numerator and the
renormalization period, use:

- \(a/q\) for the combinatorial rotation number;
- \(s\) for the period of the complete cycle
  \(\mathcal K=\{K_0,\ldots,K_{s-1}\}\);
- \(P\ge1\) for the tame/amplification control parameter;
- \(B\) for KKL's fixed parabolic-boundedness constant;
- \(G=(g,\jmath)=(f^s,\iota_s)\) for the full return;
- \(X=\mathcal W_{\rm can}^{h+v}(\mathcal U\setminus\mathcal K)\);
- \(W_R=\mathbb W(\mathcal RF)\).

KKL assumes \(a=1\), every limb contains at most \(B\) members of \(\mathcal K\),
and every member in the critical limb lands in one of the limbs with
\(|j|\le B\). It fixes \(B\) for the whole of Sections 4--6.

In this notation, Proposition 3.8 is:

> For every \(P\), if \(\mathcal U\setminus\mathcal K\) is \(P\)-tame and
> \(q,W_R\) are sufficiently large as functions of \(B,P\), then
> \(\mathbb W(F)\ge P W_R\).

The source definition of \(P\)-tame has three independent clauses:

1. every horizontal Hubbard arc has flux \(O_B(MW_R)\);
2. for arcs crossing the horizontal Hubbard diagram at least \(n\) times,
   \[
     n^2\|X|_{\mathcal A}\|=O_B(P\|X\|);
   \]
3. the Hubbard-tree complement has no \(P\)-wide controllable wave.

Calling a virtual WAD "tame" without defining these clauses on the actual marked
surface does not instantiate Proposition 3.8.

For the conditional virtual theorem, use the predicates from
`virtual_branch_assembly.md`:

- \(\operatorname{Tame}_P(F)\): all three tame clauses at the single control
  parameter \(P\);
- \(\operatorname{Amp}_P(F)\):
  \(\mathbb W(F)\ge P\mathbb W(\mathcal RF)\);
- \(\operatorname{Deg}_{Q,A}(F)\): the declared effective high-type/corridor
  parameter is at least \(Q\) and \(W_R\ge A\).

Only amplification monotonicity is automatic. No monotonicity of
\(\operatorname{Tame}_P\) is used below.

## 4. Dependency graph

The proof has the following directed structure.

```text
full KKL ambient data + parabolically B-bounded placement
        |
        +--> inner/outer translation markings
        |        |
        |        +--> Translation Marking Theorem
        |        +--> tame-to-good, bounded-length WAD
        |
        +--> full cycle return G=(f^s,iota_s)
        |        |
        |        +--> bounded-defect return / literal clone
        |        +--> localized component Uhat_I -> U_I
        |                 |
        |                 +--> bounded selected degree
        |                 +--> canonical-WAD domination
        |                 +--> ordered bad-concatenation split
        |                 +--> Wanderers tail
        |                 +--> end-proper immersion transport
        |                 +--> near self-domination
        |
        +--> primitive Hubbard transition
                 |
                 +--> full-return entropy
                 +--> both Perron eigenweights
                 +--> Value contraction
                 +--> no near self-domination

tame-to-good + no near self-domination --> amplification
```

The static occupancy trichotomy of KKL Proposition 3.7 enters before this graph. KKL
Remark 4.14 does not remove any node displayed above.

## 5. Line-by-line hypothesis ledger

"Imported" means the statement is available in the full KKL setting. "Formal"
means a corresponding abstract or topological implication is proved in this
repository. "Open" means the required virtual realization has not been proved.

| ID | source location | source input and use | exact virtual requirement | status |
|---|---|---|---|---|
| T01 | `waves`, 486--492 | prime primitive \(\psi\)-ql renormalization gives the complete cycle, canonical localization, and the correctly oriented amplification quantity | construct an actual finite-horizon correspondence and identify its predecessor/successor widths | open |
| T02 | `waves`, 497--543 | periodically repelling full filled set supplies limbs, finite Hubbard tree, primitive transition, and both forward and pullback incidences | access-complete finite ribbon/core carrier with exact source incidence | open |
| T03 | `waves`, 661--667 | rotation \(1/q\), occupancy \(\le B\), and bounded critical-limb landing | prove a ribbon-order-preserving accelerated replacement; occupancy alone is insufficient | open |
| T04 | `waves`, 698--715 | HTND means both \(q\) and \(W_R\) are large, with constants depending on \(B\) | a virtual degeneration threshold and a long-corridor threshold in the same chart | open |
| T05 | `waves`, 757--769 | tameness is bounded flux + quadratic alignment tail + no wide controllable wave | define all three on the realized virtual marked surface | open |
| T06 | `waves`, 803--824 | \(sW_R\le4\|X\|+O(s)\), using all \(s\) small-set boundaries and their width comparison | complete-cycle or separately proved virtual boundary-width comparison through the full horizon | open |
| T07 | `waves`, 913--934 | the middle limbs form an exact translation region and every relevant arc has a unique lift | selected noncritical branches must persist and preserve every declared access | open |
| T08 | `waves`, 995--1031 | inner translation marking; equality of pullback and original tree in middle limbs; shift rule; \(p_{\rm shift}\le B\) | cyclic-order-faithful prime-end marking and exact boundary action | open |
| T09 | `waves`, 1033--1049 | outer translation marking; all sides of all small sets in the corridor; no-wide-wave term | access-complete outer marking, not a chosen subset of components | open |
| T10 | `waves`, 2182--2234 | Translation Marking Theorem gives \(\|W^{\rm long}\|\le2W_{\rm std}+6N\), with \(N=2(n+1)p_{\rm shift}\) | bound marking density \(N/s\), standard width, and support realization | imported/formal error algebra; virtual realization open |
| T11 | `waves`, 1057--1086 | no-long-segment arcs localize; a good bounded-length family has at most \(3B\) translation classes | bounded number of access-faithful corridor classes after acceleration | open |
| T12 | `waves`, 1091--1123 | tameness, no amplification, width-to-weight, and T10 produce a good bounded-length family carrying \(1-\epsilon\) of \(X\) | virtual tame-to-well-controlled lemma with period-independent errors | open |
| T13 | `waves`, 964--987 | finite quantifier induction over at most \(3B\) classes resolves the opposite epsilon/length quantifiers | same induction once T11--T12 and the hammer supplied by T17+T26 hold | formal |
| T14 | `not-all-good2`, 7--27 | full return is exactly \(G=(f^s,\iota_s)\); desired output is near self-domination of \(X^g|_I\) | construct the selected complete return through time \(s\), not merely one orbit branch | open |
| T15 | `not-all-good2`, 74--105 | bounded critical-limb placement gives a return-to-middle time \(N(B)\) | bounded defect-return theorem for the accelerated virtual corridor | open |
| T16 | `not-all-good2`, 107--158 | primitivity gives \(\lambda_F^s\ge2\); cloning supplies the upper bound and corridor-uniform ratios for both Perron weights | exact literal clone certificate or a two-sided eigencone theorem; graph delay must match WAD time | conditional formal algebra; dynamical realization open |
| T17 | `not-all-good2`, 216--250; `value1`, 19--120 | Value monotonicity, \(s\)-step contraction, bounded support length, and eigenweight ratios prohibit near self-domination | same typed core/WAD incidence and one common Value frame on input and output | conditional formal; realization open |
| T18 | `not-all-good2`, 262--294 | for a fixed interval \(I\), one component \(\widehat U_I\) contains a shrunken middle interval and is contained in \(U_I\) | a selected full-return component with both inclusions on actual marked surfaces | open |
| T19 | `not-all-good2`, 296--306 | \(\deg(g|\widehat U_I)\le2^{m_I}\), using injection of critical stages into distinct members of \(\mathcal K\cap U_I\) | uniform localized critical-encounter multiplicity \(m_I\) | formal degree lemma below; bound open |
| T20 | `not-all-good2`, 310--348 | subsurface covers and filled localizations give \(g:\widehat V_I\to V_I\), plus a lifted immersion proper at selected filled-set ends | based relative-cover lift, local saturation, finite topology, and degree-one behavior at the used ends | topological fragments proved; complete realization open |
| T21 | `not-all-good2`, 358--402 | average bad, escaping, and ghost-vertical contributions yield a typical interval of fixed length | exhaustive accounting over access-complete cells and all omitted Cantor components | open |
| T22 | `not-all-good2`, 424--441 | Kahn's canonical-WAD pullback comparison produces an ordered elementary-domination witness | coefficientwise/ordered WAD witness on the selected full-return cover | open |
| T23 | `not-all-good2`, 456--491 | bounded local valence (\(6B\)) controls witnesses whose first bad member occurs at bounded concatenation depth | bounded local access and WAD incidence, not merely bounded selected components | open |
| T24 | `not-all-good2`, 493--500; `waves`, 2347--2410 | Wanderers controls the long concatenation tail; source application gives \(4\|X_I\|/m\) | explicit parameter dictionary \((X,Y,g,\mathcal A,\widehat{\mathcal A},\mathcal B,D,d)\) and admissibility of every leaf | imported theorem; virtual application open |
| T25 | `not-all-good2`, 509--545 | immersion transport requires finite topology, valid WAD, and an immersion proper and degree one at every selected starting end | prove those end conditions on the virtual localization | open |
| T26 | `not-all-good2`, 570--604 | T18--T25 produce \(Y\le X^g|_I\), exact domination by \(g^*(X^g|_I)\), and small norm loss | Virtual Near-Self-Domination Lemma | open |
| T27 | `not-all-good2`, 51--64 | T17 contradicts T26 | identical abstract contradiction | proved in Section 7 |

### 5.1 Why the full period \(s\) cannot be shortened silently

The source uses \(s\) in four different ways:

1. \(g=f^s\) is the pullback in the Value inequality;
2. the selected domain is a component of \(g^{-1}(U_I)\);
3. every intermediate stage is inspected in the degree proof;
4. \(\iota_P\) is lifted to the localized cover and then used for immersion
   transport.

A first-return map on one chosen orbit branch supplies none of Items 2--4 for the
other pullback sheets. Conversely, replacing \(s\) by several full periods permits
the same cycle component to be encountered repeatedly, destroying the injection in
T19. A longer virtual horizon must therefore be split into complete single-cycle
blocks or carry the repeated-encounter multiplicity explicitly.

### 5.2 The Wanderers parameter audit cannot be omitted

The source application at `not-all-good2.tex`, lines 493--500 is compressed to one
sentence. The theorem itself requires:

- a proper holomorphic map of bounded total degree \(D\);
- a finite family \(\mathcal B\) containing every critical value;
- all components \(\mathcal A\) of the pullback of \(\bigcup\mathcal B\);
- a selected starting family \(\widehat{\mathcal A}\) on which the map is at most
  \(d\)-to-one;
- an oriented foliation whose routes visit at least \(m-1\) intermediate members,
  end in \(\mathcal A\), and never cross back through their starting member.

For a virtual application, each symbol must be instantiated on the same localized
cover used by the WAD domination witness. A statement that the critical orbit is
marked does not prove properness, route completeness, or the \(d\)-to-one condition.

## 6. Candidate virtual tame full-return package

Fix \(P\ge1\). A virtual block has a **uniform tame full-return package at control
parameter \(P\)** if the following data and estimates exist with constants
independent of \(s,q\), the
rotation number, corridor length, and virtual depth.

### `VR0` Return-complete marked analytic carrier

There is a finite-horizon analytic correspondence through one complete primitive
cycle of duration \(s\), with:

- full stage hulls and exact full-set identities on selected components;
- every small-set, critical-orbit, core-edge, WAD, ideal-access, and localization
  label used below retained through its last use;
- a finite access-complete tree/ribbon carrier and canonical horizontal, vertical,
  and bivertical arc diagrams;
- a predecessor width \(\mathbb W(F)\) and successor width \(W_R\) in the same
  calibrated chart.

The carrier may be virtual and only finite-horizon. Global forward invariance is not
required.

### `VR1` Ribbon translation or accelerated replacement

Outside universally bounded entry and exit defects, the selected stage maps act on
the ideal marking by an exact order-preserving shift. The action supplies:

- unique noncritical lifts of every proof-used arc;
- inner and outer translation markings;
- complete access and side labels;
- marking size \(N_{\rm mark}\le C_{\rm mark}s\);
- standard width
  \[
    W_{\rm std}
    \le C_{\rm std}P W_R+E_{\rm std},
  \]
  with \(E_{\rm std}\) absorbed by the declared error budget.

For \(a/q\ne1/q\), this must be constructed by an induced or
continued-fraction return. Relabeling alone is not accepted.

### `VR2` Tame-to-well-controlled estimates

The actual canonical WAD \(X\) satisfies the virtual versions of the three tame
clauses. In addition:

\[
  c_0sW_R-C_0s\le\|X\|\le C_1sW_R+C_1s,
\tag{6.1}
\]

and the Translation Marking Theorem, flux bounds, alignment tail, and no-wave
condition imply the following source-shaped statement:

> For every \(\epsilon>0\), if the block is not \(P\)-amplifying and \(q,W_R\)
> exceed thresholds depending only on \(B,P,\epsilon\) and the package constants,
> then a good horizontal family of uniformly bounded combinatorial length carries
> at least \((1-\epsilon)\|X\|\).

The number of relevant translation classes is uniformly bounded. In addition, for
every \(\eta>0\), every single translation class carrying at least
\(\eta\|X\|\) has combinatorial length at most \(L_{\rm cls}(\eta)\) under the same
non-amplification assumption. This is the virtual form of KKL Corollary 5.3 and is
needed to resolve the opposite dependence of the two epsilon/length quantifiers.

### `VR3` Selected full-return localization

For every fixed window length \(L_1\) needed by the proof, some interval \(I\) has a
selected component
\[
  \widehat U_I\subset g^{-1}(U_I)
\]
and localizations
\[
  g:\widehat V_I\longrightarrow V_I
\]
such that:

1. a uniformly shrunken middle subwindow lies in \(\widehat U_I\subset U_I\);
2. the local complexity vector satisfies
   \[
     \mathfrak c_I
     =
     (m_I,|\chi(V_I)|,|\mathcal B_I|,d_I)
     \le\mathfrak c_0(L_1);
   \tag{6.2}
   \]
3. hence \(\deg(g|\widehat V_I)\le2^{m_I}\);
4. the lifted immersion is proper and degree one at every end used to initiate
   immersion transport;
5. every inactive Cantor component is either included or proved irrelevant to
   separation, pullback components, and routes.

### `VR4` Ordered WAD domination and Wanderers

On the surfaces in `VR3`, canonical-WAD pullback gives an ordered elementary
domination witness. Bad pieces are partitioned by the first bad occurrence.
Bounded-depth pieces obey the local incidence estimate, and the remaining routes
satisfy every Wanderers hypothesis with the parameters in (6.2).

Consequently, for every \(\delta>0\), after the source order of choices
\[
  m\ \longrightarrow\ \epsilon\
  \longrightarrow\ L_1\
  \longrightarrow\ W_R,
\]
there are horizontal WADs \(Y\le Z\), supported in one fixed localization, such that
\[
  g^*Z\dominates Y,
  \qquad
  \|Z-Y\|\le\delta\|Z\|.
\tag{6.3}
\]

Both \(Z\) and \(Y\) remain in the bounded-combinatorial-length support on which
Value and norm are uniformly comparable.

### `VR5` Typed full-return Value package

There is one exact source-identified core incidence and one Value functional \(V\)
on all WADs in (6.3), with:

1. domination monotonicity;
2. actual full-return contraction
   \[
     V(g^*Z)\le\mu^{-1}V(Z),
     \qquad \mu>1;
   \tag{6.4}
   \]
3. support comparison
   \[
     V(E)\le C_V\frac{\|E\|}{\|Z\|}V(Z)
   \tag{6.5}
   \]
   for \(0\le E\le Z\) in the declared support;
4. \(\mu\) and \(C_V\) independent of \(s,q\), rotation number, and virtual depth
   once \(B,P\) are fixed.

A sufficient realization of Item 2 is a source-faithful literal-clone certificate
with graph delay \(n\), actual WAD pullback exponent \(r\ge n\), and the corrected
clone multiplier. A fitted graph, an unframed open transfer, or an exponent
\(r<n\) is not sufficient.

### `VR6` Width-chart closure

The KKL marked width used to define amplification and the virtual degeneration
functional are compared with universal multiplicative constants and a relative or
amortized additive error. The comparison must also transport the tame predicate at
the same declared control parameter used by the static split. A bare multiplicative
width comparison is not enough: it can change the numerical amplification factor and
does not imply any monotonicity of the tame or wave predicates.

Without this clause the package proves a KKL-coordinate contradiction, not yet a
same-parameter statement about the unified virtual functional.

### `VR7` Explicit high-type and width thresholds

For each fixed \(B,P\), carry out the finite source order of choices and record:

- corridor/translation thresholds \(Q_{\rm tr},A_{\rm tr}\);
- tame-to-good thresholds \(Q_{\rm good},A_{\rm good}\);
- localization and typical-window thresholds \(Q_{\rm loc},A_{\rm loc}\);
- Wanderers and additive-error thresholds \(Q_{\rm wan},A_{\rm wan}\);
- Value/eigencone thresholds \(Q_{\rm val},A_{\rm val}\).

After the finitely many hammer gaps and heavy-class length bounds in the
translation-class induction have been selected, define
\[
  Q_t(B,P)
  =
  \max\{
    Q_{\rm tr},Q_{\rm good},Q_{\rm loc},Q_{\rm wan},Q_{\rm val}
  \},
\tag{6.6}
\]
\[
  A_t(B,P)
  =
  \max\{
    A_{\rm tr},A_{\rm good},A_{\rm loc},A_{\rm wan},A_{\rm val}
  \}.
\tag{6.7}
\]

Each entry may depend on the previously selected finite constants, hence ultimately
on \(B,P\), but not on \(s,q\), rotation number, or virtual depth. The tame closure
is invoked only when the declared combinatorial-degeneracy parameter is at least
\(Q_t(B,P)\) and \(W_R\ge A_t(B,P)\).

## 7. Derivations that are currently valid

### Lemma 7.1 (critical-encounter degree)

Let
\[
  V_0\xrightarrow{f_0}V_1\xrightarrow{f_1}\cdots
  \xrightarrow{f_{s-1}}V_s
\]
be a composable selected telescope of proper holomorphic maps, each of degree one or
two. If exactly \(m_I\) stages have degree two, then
\[
  \deg(f_{s-1}\circ\cdots\circ f_0)=2^{m_I}.
\tag{7.1}
\]

**Proof.** Degrees of proper holomorphic maps multiply under composition. Every
factor is one or two. \(\square\)

KKL bounds \(m_I\) by injecting each critical stage into a distinct member of the
single \(s\)-cycle lying in \(U_I\). In a virtual telescope, (7.1) remains valid, but
the injection is an open dynamical assertion.

### Lemma 7.2 (linear marking density absorbs the topology term)

Assume
\[
  N_{\rm mark}\le C_{\rm mark}s,
  \qquad
  \|X\|\ge c_0sW_R-C_0s.
\]
Then, for \(W_R>2C_0/c_0\),
\[
  \frac{6N_{\rm mark}}{\|X\|}
  \le
  \frac{12C_{\rm mark}}{c_0W_R}.
\tag{7.2}
\]

**Proof.** The lower bound gives
\(\|X\|\ge(c_0/2)sW_R\). Substitute the marking bound and cancel \(s\).
\(\square\)

Thus a total ideal-marking cardinality growing linearly with the period is not itself
an obstruction. Superlinear access incidence is. This is why "bounded active core"
and "bounded complete marking" must not be conflated.

### Lemma 7.3 (abstract Value obstruction)

Let \(Z\ne0\) and \(0\le Y\le Z\) be WADs. Suppose:

\[
  g^*Z\dominates Y,
  \qquad
  V(g^*Z)\le\mu^{-1}V(Z),
  \qquad
  V(Z-Y)\le C_V\delta V(Z)
\]

for \(\mu>1\). If
\[
  C_V\delta<1-\mu^{-1},
\tag{7.3}
\]
these inequalities are impossible.

**Proof.** Domination gives
\[
  V(Y)\le V(g^*Z)\le\mu^{-1}V(Z).
\]
Linearity and \(Y\le Z\) give
\[
  V(Y)=V(Z)-V(Z-Y)\ge(1-C_V\delta)V(Z).
\]
Condition (7.3) makes the lower bound strictly larger than the upper bound.
\(\square\)

This is the algebraic heart of KKL's no-near-self-domination proposition. It remains
valid for any virtual package satisfying `VR5`; it uses no satellite modulus bound.

### Theorem 7.4 (conditional Virtual Tame Full-Return Transfer)

Fix \(B,P\ge1\). Suppose a virtual block satisfies `VR0`--`VR5` and `VR7`.
Then the safe same-parameter implication holds in the realized KKL coordinate:
\[
  \operatorname{Deg}_{Q_t(B,P),A_t(B,P)}(F)
  \ \wedge\
  \operatorname{Tame}_P(F)
  \Longrightarrow
  \operatorname{Amp}_P(F).
\tag{7.4}
\]

No monotonicity of \(\operatorname{Tame}_P\) in \(P\) is used.

**Proof.** Suppose the block is \(P\)-tame and not \(P\)-amplifying.
Fix a combinatorial-length bound \(L\). Choose
\[
  0<\delta<\frac{1-\mu^{-1}}{C_V}.
\]
With the well-controlled tolerance chosen small enough as a function of
\((L,\delta)\), clauses `VR3`--`VR4` give \(Z,Y\) satisfying (6.3). Clause `VR5`
converts the norm loss into
\[
  V(Z-Y)\le C_V\delta V(Z)
\]
and gives the same-frame full-return contraction (6.4). Lemma 7.3 is a
contradiction. Consequently, for every \(L\) there is
\(\epsilon_{\rm ham}(L)>0\) such that no good family of length at most \(L\) can
carry more than
\((1-\epsilon_{\rm ham}(L))\|X\|\). This is the virtual analogue of KKL Lemma 5.2.

Now use the exact finite quantifier induction from
`waves-with-Misha.tex`, lines 964--987. The bounded-class clause of `VR2` gives a
uniform maximum \(N\) of translation classes. Starting with
\(\epsilon_0=1\), choose the heavy-class thresholds, their length bounds
\(L_{\rm cls}(\eta_n)\), and then
\(\epsilon_{\rm ham}(\max_{i\le n}L_i)\), successively for
\(1\le n\le N\). Finally choose the tame-to-good tolerance smaller than half of
all these hammer gaps. The tame-to-good family supplied by `VR2` has more mass than
the induction permits after its classes are ordered by weight. This contradiction
proves that the block is \(P\)-amplifying in the realized KKL coordinate. Every
large-corridor, successor-width, selected-degree, localization, Wanderers, and Value
premise used above is licensed by the maxima (6.6)--(6.7). \(\square\)

The theorem is a proved implication. It does not prove that Dudko's virtual hulls
satisfy `VR0`--`VR7`. Clause `VR6` is additionally required before (7.4) can be
asserted for the calibrated unified virtual predicates. That passage must preserve a
common input parameter for the static split and tame closure; unrelated parameter
changes do not compose.

## 8. Exact unresolved lemmas

The open obligation should be decomposed into the following falsifiable statements.
They are all parameterized by the same declared \(P\): their combined target is
\[
  \operatorname{Deg}_{Q_t(B,P),A_t(B,P)}(F)
  \ \wedge\
  \operatorname{Tame}_P(F)
  \Longrightarrow
  \operatorname{Amp}_P(F).
\tag{8.1}
\]
No statement below may replace \(P\) by an unrelated branch parameter without an
explicit common-parameter theorem.

### `VTR-A` Full-cycle carrier and return completeness

Every block routed by \(\operatorname{Tame}_P\) and satisfying the displayed
thresholds admits an access-complete marked analytic carrier
through one complete primitive cycle \(s\), including every sheet, end, and core edge
used by localization, Wanderers, and Value.

This is stronger than retaining the critical orbit through an unspecified number of
first returns.

### `VTR-B` Ribbon-order acceleration

Every non-neutral-routed virtual block admits finitely many induced corridors with
uniformly bounded defects on which the full marking action is an exact
cyclic-order-preserving shift, with linear marking density and uniform standard-width
charge.

The constants must be independent of the satellite period, numerator and denominator
of the rotation number, continued-fraction depth, and virtual depth.

### `VTR-C` Localized full-return complexity

For every fixed proof window \(I\), construct the selected full-return localization
and prove
\[
  \sup_I
  \bigl(
    m_I+|\chi(V_I)|+|\mathcal B_I|+d_I
  \bigr)<\infty.
\tag{8.2}
\]

Equation (8.2), rather than a selected-component count alone, is the exact uniformity
input for the degree and Wanderers constants.

### `VTR-D` Ordered canonical-WAD pullback

Prove that the virtual canonical WAD on the selected localization has an ordered
elementary-domination witness, that its first-bad decomposition is exhaustive, and
that every long witness route satisfies the Wanderers hypotheses before the declared
horizon.

Scalar extremal-width comparison is not enough; order along each concatenation is
used.

### `VTR-E` Typed core/Value realization

Identify the virtual core transition with the exact Hubbard pushforward incidence and
the WAD pullback with its transpose convention. Prove either:

- a literal fixed-cross-section clone satisfying the corrected theorem and both
  eigencone bounds; or
- a replacement full-return entropy and two-sided eigencone estimate.

The actual WAD exponent must be at least the graph delay. Perturbative retained-mass
lower bounds alone do not control Perron-coordinate ratios.

### `VTR-F` Inactive remainder and chart closure

Prove that omitted Cantor components neither add ideal intervals, separate declared
accesses, enter selected pullback components, nor alter the Value support; then compare
the realized KKL width to the unified virtual functional with a period-uniform error.

No current repository theorem proves `VTR-A`--`VTR-F` for arbitrary virtual-Molecule
blocks.

## 9. Adversarial tests

### 9.1 Repeated-critical-return degree explosion

Take \(f(z)=z^2\) and the invariant full disk \(H=\overline{\mathbb D}\). The marked
critical orbit consists only of \(0\), and there is one hull component, but
\[
  f^s:\mathbb D\longrightarrow\mathbb D
\]
has degree \(2^s\).

This is not a prime-primitive counterexample to KKL. It is an exact counterexample to
the inference
\[
  \text{full connected hull + finite critical marking + bounded component count}
  \Longrightarrow
  \text{bounded return degree}.
\]
The missing datum is critical-encounter multiplicity.

### 9.2 Rotation relabeling obstruction

Let the \(q\) limbs carry their cyclic order and let dynamics act by
\[
  j\longmapsto j+a\pmod q,
  \qquad \gcd(a,q)=1.
\]
Every cyclic-order-preserving permutation of the \(q\) labels is a rotation
\(j\mapsto j+c\). Such permutations commute with the displayed action, so conjugacy
does not change \(a\). Hence it cannot turn \(a/q\) into \(1/q\) unless
\(a\equiv1\pmod q\).

An orientation-reversing relabeling changes \(a\) to \(-a\), which still covers only
the exceptional case \(a\equiv-1\pmod q\). Therefore the general-rotation repair must
be a genuine induced map, not a notation change.

### 9.3 One selected orbit branch is not the WAD pullback

The finite locally saturated telescope in `finite_horizon_inflation.md` follows one
inverse itinerary and has total degree two. KKL instead pulls the canonical WAD back
to the selected component of the full \(s\)-fold preimage of \(U_I\). That component
can contain multiple sheets, and Wanderers analyzes concatenations among them.

Discarding those sheets may remove exactly the bad routes whose small total weight
must be proved. They cannot be declared irrelevant before `VTR-D`.

### 9.4 Access-complete marking versus selected occupancy

A virtual hull may contain few selected Cantor components while fjords, dams,
connectors, and omitted components create arbitrarily many dynamically distinct
prime-end accesses. KKL's topology term is uniform only after the complete marking
has linear density as in Lemma 7.2.

### 9.5 Vanishing elementary entropy

For long literal clones, \(\lambda_P\to1\). A one-step Value factor therefore gives no
uniform contradiction. KKL uses the full return, with \(\lambda_s^s\ge2\).
The corrected clone theorem recovers a complete-block multiplier only for an exact
source-faithful clone with a bounded reduced gate. A changing or perturbed virtual
template must prove its own complete-block multiplier and eigencone bounds.

### 9.6 Alternating neutral and primitive charts

If the full return \(s\) crosses a pseudo-Siegel/primitive interface, there is no
single source-defined canonical WAD or Value frame unless a chart transition theorem
is supplied. A valid stopping rule must either end the tame block before that
interface or include the entire transition in `VR0`, `VR5`, and `VR6`.

### 9.7 Wanderers additive constant

The Wanderers error is
\[
  C(|\chi(V_I)|,|\mathcal B_I|,D_I).
\]
Even if its leading \(2d_I/m\) term is small, unbounded localized topology or degree
can make the additive term period-dependent. Choosing \(m\) large does not repair
that failure; (8.2) is needed first.

## 10. Relation to the current repository

The following pieces are already valid and should be reused:

- `virtual_block_quotient.md`, Lemmas 7.7--7.9: topological selected
  one-critical-step factorization;
- `finite_horizon_inflation.md`, Theorem 10.2: finite local saturation for a supplied
  inverse itinerary;
- `virtual_hull_realization.md`, Definition 3.1 and Proposition 3.2:
  access-complete incidence and linear topology charge;
- `corrected_clone_theorem_derivation.md`, Theorems 3.1 and 5.1--5.2:
  the corrected fixed-cross-section scalar equation and both typed Perron vectors;
- `dynamical_corridor_certificate.md`, Corollary 4.2:
  conditional Value contraction when the literal graph delay is no larger than the
  actual WAD pullback exponent.

Their exact limitations for this branch are:

1. selected topological factorization does not produce the full localized WAD
   pullback;
2. local saturation does not calibrate canonical WADs or widths;
3. access incidence does not bound critical encounters;
4. the corrected clone theorem does not construct a virtual literal clone;
5. conditional Value contraction does not bound the WAD error or prove
   near-self-domination.

## 11. Proposed proof-ledger changes

This file does not modify the global ledger. The following changes are recommended
for the parent integration pass.

1. Keep `H2_VIRTUAL_TAME_FULL_RETURN` open.
2. Replace its single source-audit evidence anchor with this note's
   `#8-exact-unresolved-lemmas`, while retaining
   `kkl_virtual_occupancy_source_audit.md` as provenance for the separation from
   Proposition 3.7.
3. Add proved internal sub-obligations for:
   - critical-encounter degree, Lemma 7.1;
   - linear marking-density absorption, Lemma 7.2;
   - abstract Value obstruction, Lemma 7.3;
   - conditional tame full-return transfer, Theorem 7.4.
4. Split the open realization node into `VTR-A`--`VTR-F`, or at minimum record
   `VTR-C` and `VTR-D` separately. They can fail independently.
5. Add adversarial checks forbidding:
   - replacement of the localized full return by one selected degree-two orbit
     branch;
   - normalization of general \(a/q\) to \(1/q\) by a cyclic-order relabeling;
   - use of occupancy as a bound on repeated critical encounters;
   - invocation of Wanderers without its complete parameter dictionary.
