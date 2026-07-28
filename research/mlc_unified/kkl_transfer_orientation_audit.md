# KKL transfer orientation, eigenweights, and Value: source audit

## 1. Verdict

The local KKL26 TeX does **not** support an unconditional equation
\(B=T_F\) or \(B=T_F^{\mathsf T}\). Its symbol \(T_F\) is used with two
incompatible orientation cues, and the clone appendix has an additional exponent
defect. The exact safe verdict is therefore:

Write
\[
  N_{\beta\gamma}
  =
  \#\{\alpha\in\iota^*\beta:f_*\alpha=\gamma\},
\tag{1.1}
\]
where \(\beta\) is the source Hubbard edge and \(\gamma\) is the target Hubbard
edge. The convention fixed in `transfer_convention_and_frame.md` is unambiguously
\[
  B_{\gamma\beta}=N_{\beta\gamma},
\tag{1.2}
\]
so
\[
  \boxed{B=N^{\mathsf T}.}
\tag{1.3}
\]

The KKL Value equations themselves determine the two eigenweight roles:
\[
  N v=\lambda_Fv,
  \qquad
  N^{\mathsf T}w=\lambda_Fw.
\tag{1.4}
\]
Hence, in the project's source-column convention:

- \(v\) is the coordinate vector of a **left** Perron eigenfunctional;
- \(w\) is the **right** Perron eigenvector;
- KKL's Hubbard-edge Value coefficient is
  \[
    c_\beta
    =
    \bigl(v_\beta\sqrt{w_\beta}\bigr)^2
    =
    v_\beta^2w_\beta.
  \tag{1.5}
  \]

Thus, if the project writes \(\ell^{\mathsf T}B=\lambda\ell^{\mathsf T}\) and
\(Br=\lambda r\), the source-faithful identification is
\[
  \ell_\beta=v_\beta,\qquad r_\beta=w_\beta,\qquad
  c_\beta=\ell_\beta^2r_\beta.
\tag{1.6}
\]
The exponents may not be swapped.

There are then two possible disambiguations of KKL's symbol:

1. If “eigenvector for \(T_F\)” at `value1.tex`, lines 67--70, means an ordinary
   right column eigenvector, then \(T_F=N\) and
   \[
     B=T_F^{\mathsf T}.
   \tag{1.7}
   \]
2. If the arrow at line 58 is read as the image of a basis column under the
   pushforward, then \(T_F=B=N^{\mathsf T}\), while the same \(v\) used in the
   proof is a **left** eigenweight despite being called an eigenvector of \(T_F\).

The source does not choose consistently between these readings. Therefore project
documents should source-lock the raw incidence \(N\), or equivalently state the
left/right equations for \(B\), rather than say merely “same as KKL \(T_F\)” or
“transpose of KKL \(T_F\).” The project's chronological product
\(B_m\cdots B_1\) remains correct.

## 2. Source lock and audited ranges

The KKL26 v1 source snapshot is

`source-lock/KKL26-v1`.

| File | SHA-256 | Complete relevant ranges audited |
|---|---|---|
| `waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` | 512--535 (Hubbard tree and \(T_F\)); 547--599 (Hubbard arc diagrams, pullback/pushforward conventions, Value include); 2236--2318 (entire cross-section clone definition and theorem proof) |
| `value1.tex` | `2767F71E57862DA5CF50FF7B96FC08917E24CA8F9BD2D4523C467B2E896AD83A` | 4--120 (entire expanding-valuation definition, arithmetic lemmas, Value proof, and comparison proposition) |
| `not-all-good2.tex` | `B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01` | 68--158 (entire cross-section/eigenweight subsection through Proposition `prop:eigenweights`) |

This audit uses the full definitions and proofs in those ranges, not the abstract or
the prose label “pushforward matrix.”

## 3. The equations determine the typed incidence, not the \(T_F\) label

### 3.1 Core correspondence

KKL defines the Hubbard tree and edge set in `waves-with-Misha.tex`, lines
512--529. Lines 533--535 then say:

1. \(f\circ\iota^{-1}\) induces \(T_F\);
2. \(\iota\circ f^{-1}\) induces \(T_F^{\mathsf T}\);
3. their \(n\)-fold versions induce \(T_F^n\) and
   \((T_F^{\mathsf T})^n\).

Lines 587--594 define \(f_*,\iota_*,f^*,\iota^*\) on the bivertical Hubbard arcs.
The decisive coordinate identities occur in `value1.tex`, lines 57--70. KKL first
describes \(T_F\) and \(T_F^{\mathsf T}\) through
\[
  \beta\longmapsto
  \sum_{\alpha\in\iota^*\beta} f_*\alpha,
  \qquad
  \beta\longmapsto
  \sum_{\alpha\in f^*\beta}\iota_*\alpha.
\tag{3.1}
\]
It then chooses eigenweights \(v,w\) and states
\[
  \lambda_F^n v(\beta)
  =
  \sum_{\alpha\in\iota_n^*\beta}v(f_*^n\alpha),
\tag{3.2}
\]
\[
  \lambda_F^n w(\beta)
  =
  \sum_{\alpha\in(f^n)^*\beta}w((\iota_n)_*\alpha).
\tag{3.3}
\]

For \(n=1\), the right side of (3.2) is
\[
  \sum_\gamma N_{\beta\gamma}v_\gamma.
\]
Thus (3.2) is exactly the outgoing-weight equation
\[
  (Nv)_\beta=\sum_\gamma N_{\beta\gamma}v_\gamma
\]
and (3.3) is the incoming-weight equation for \(N^{\mathsf T}\). These two
equations fix the operational roles of \(v,w\).

They do not consistently fix the source symbol \(T_F\). If “eigenvector” has its
usual right-column meaning, lines 67--70 identify \(T_F=N\). If the schematic
arrow (3.1) is the image of a basis column, it instead identifies
\(T_F=N^{\mathsf T}=B\), in which case \(v\) is being used as a left
eigenfunctional. KKL never explicitly declares rows versus columns, and the clone
appendix does not resolve the ambiguity because of the independent defect in
Section 6 below.

### 3.2 What “pushforward” means here

The row-source incidence \(N\) acts on a column of future weights:
\[
  (Nv)(\text{source})
  =
  \sum_{\text{targets}}(\text{multiplicity})\,v(\text{target}).
\tag{3.4}
\]
The project's \(B\) instead acts on a column of source masses/counts:
\[
  x_{\rm target}=Bx_{\rm source}.
\tag{3.5}
\]
They encode the same directed multigraph, but their matrices are transposes. In
particular, \(B=N^{\mathsf T}\). Depending on which inconsistent cue is used to
name KKL's symbol, this becomes either \(B=T_F^{\mathsf T}\) or \(B=T_F\).
Neither naming choice changes the typed incidence or the left/right equations.

## 4. Chronological products

For varying raw row-source incidences
\[
  E_0\xrightarrow{N_1}E_1\xrightarrow{N_2}\cdots
  \xrightarrow{N_m}E_m,
\]
path counts compose chronologically as
\[
  N_{[1,m]}=N_1N_2\cdots N_m.
\tag{4.1}
\]
Indeed, the \((a,c)\) entry of \(N_1N_2\) sums over intermediate \(b\) the number
of \(a\to b\) occurrences followed by \(b\to c\) occurrences.

Set \(B_k=N_k^{\mathsf T}\). Then
\[
  B_{[1,m]}
  =
  B_m\cdots B_1
  =
  N_m^{\mathsf T}\cdots N_1^{\mathsf T}
  =
  (N_1\cdots N_m)^{\mathsf T},
\tag{4.2}
\]
which is precisely the project's chronological column-source rule.

KKL explicitly needs only a stationary \(n\)-fold identity in the audited Value
proof (`value1.tex`, line 64). Equation (4.1) for a varying cocycle is the exact
linear-algebra extension of the typed incidence, not a separately stated KKL
theorem. It avoids importing the paper's ambiguous \(T_F\) label.

## 5. Left/right eigenweights and the Value coefficient

KKL's source statements are:

- `value1.tex`, lines 67--70:
  \[
    T_Fv=\lambda_Fv,\qquad
    T_F^{\mathsf T}w=\lambda_Fw;
  \]
- lines 77--78:
  \[
    l(\beta)=v(\beta)\sqrt{w(\beta)}
  \]
  at the base level, with a compatible lifted formula;
- lines 103--111:
  \[
    \operatorname{val}(X)
    =
    \sum_\alpha X(\alpha)l(\alpha)^2,
    \qquad
    \operatorname{val}((f^n)^*X)
    \le
    \lambda_F^{-n}\operatorname{val}(X);
  \]
- lines 114--120: the Value/size comparison again uses
  \(v(\alpha)\sqrt{w(\alpha)}\).

Reading the coordinate sums rather than the ambiguous \(T_F\) labels gives,
unconditionally,
\[
  B^{\mathsf T}v=\lambda_Fv,
  \qquad
  Bw=\lambda_Fw.
\tag{5.1}
\]
Thus \(v^{\mathsf T}B=\lambda_Fv^{\mathsf T}\), proving (1.6).

The distinction is numerically visible. Let
\[
  N=
  \begin{pmatrix}1&2\\1&1\end{pmatrix},
  \qquad
  B=N^{\mathsf T}.
\]
For \(\lambda=1+\sqrt2\), one may take
\[
  v=(\sqrt2,1)^{\mathsf T},
  \qquad
  w=(1,\sqrt2)^{\mathsf T}.
\]
KKL's coefficient vector is
\[
  v^2\odot w=(2,\sqrt2),
\]
whereas swapping the left/right exponents gives
\[
  w^2\odot v=(\sqrt2,2).
\]
The two are not scalar multiples. A transpose error therefore changes Value, even
though it leaves the Perron eigenvalue unchanged.

Normalizing \(v\) or \(w\) rescales the whole valuation by a positive scalar and is
harmless within one fixed block. Swapping their roles is not a normalization.

## 6. Clone appendix does not resolve the convention

KKL's entire clone construction is in `waves-with-Misha.tex`, lines 2236--2318.
It contains a material local inconsistency, not merely an omitted row/column label.
The relevant assertions are:

1. the directed chain is
   \[
     E_0\longrightarrow E_1\longrightarrow\cdots\longrightarrow E_n
   \]
   (line 2245);
2. \(T_n\) is its pushforward matrix and \(v_n\) its Perron eigenvector
   (lines 2249--2253);
3. line 2254 literally reads
   \[
     v_n(y)=\lambda^k v_n(y),
   \tag{6.1}
   \]
   repeating \(y\) on both sides and omitting the subscript on \(\lambda\);
4. every length-\(n\) path from \(x\in E_k\) to \(y\in E_0\) creates a reduced
   edge \(x'\to y\) labeled \(k\) (line 2257);
5. that reduced edge is weighted by \(+\lambda^k\) (line 2262);
6. the restriction \(v_n|_{E_0}\) is asserted to be a right Perron eigenvector of
   the weighted reduced matrix with eigenvalue \(\lambda_n^n\) (line 2264).

These statements do not uniquely determine a correction to (6.1), and the adjacent
equations do not all fit one standard convention:

- Under the row-source/right-eigenvector convention used by the Value equations,
  the unique chain edge forces
  \[
    v_n(E_{k+1})=\lambda_n v_n(E_k).
  \tag{6.2}
  \]
  Thus \(v_n(E_k)=\lambda_n^k v_n(E_0)\).
- Under the project's target-row/source-column/right-eigenvector convention, the
  same chain forces
  \[
    v_n(E_k)=\lambda_n^{-k}v_n(E_0).
  \tag{6.3}
  \]
- For a source-column incidence, the \(n\)-step eigenvector equation at an endpoint
  \(y\in E_0\) sums the weights of all starts \(x\in E_k\). Substitution of (6.3)
  gives reduced coefficients \(\lambda_n^{-k}\), not the
  \(+\lambda_n^k\) written at line 2262.
- For a row-source incidence, the \(n\)-step equation at a start \(x\in E_k\)
  combines with (6.2); dividing back to the \(E_0\) clone again introduces the
  opposite power before one can obtain an equation for \(v_n|_{E_0}\).

Therefore the clone appendix, as hashed in Section 2, cannot serve as an independent
orientation certificate. At least one of the chain/eigenvector relation, reduced
edge orientation, or exponent sign requires correction. The literal typo at line
2254 cannot be repaired uniquely from the surrounding text. The later sentence in
`not-all-good2.tex`, lines 151--157, only uses a ratio
\(\lambda_F^k\) with \(|k|\le q\), so it does not resolve the sign.

### 6.1 Literal finite-graph counterexample to the displayed clone equation

The inconsistency is not merely terminological. Let the base graph have vertices
\[
  \{e,a,b\}
\]
and edges
\[
  e\to a,\qquad a\to e,\qquad a\to b,\qquad b\to e.
\tag{6.4}
\]
Take \(E=\{e\}\). There is no \(E\)-to-\(E\) edge, every sufficiently long path
meets \(E\), and the graph is primitive because it is strongly connected and has
cycles of lengths \(2\) and \(3\).

Its length-\(n\) clone in the literal sense of lines 2245--2247 has the chain
\[
  e_0\to e_1\to\cdots\to e_n,
\]
together with
\[
  e_n\to a,\qquad a\to e_0,\qquad a\to b,\qquad b\to e_0.
\]
Every clone is primitive: it has cycles of the consecutive lengths \(n+2\) and
\(n+3\). Its Perron root satisfies the elementary renewal equation
\[
  \lambda_n^{\,n+3}=\lambda_n+1.
\tag{6.5}
\]

For \(n\) larger than the cross-section bound, the length-\(n\) paths ending at
\(e_0\) start at \(e_2\) through \(a\to e_0\), or at \(e_3\) through
\(a\to b\to e_0\). Hence the reduced graph defined at lines 2257--2262 has one
vertex and two loops with labels \(2,3\), so the displayed definition gives
\[
  h(\lambda)=\lambda^2+\lambda^3.
\tag{6.6}
\]
The asserted equation \(h(\lambda_n)=\lambda_n^n\) would give
\[
  \lambda_n^n=\lambda_n^2+\lambda_n^3
  =\lambda_n^2(1+\lambda_n)
  =\lambda_n^{n+5},
\]
where (6.5) was used in the last equality. This is impossible because
\(\lambda_n>1\).

This counterexample is invariant under transposition. It proves that the exact
equation at lines 2270--2277 cannot be imported from the literal preceding
definitions without an additional correction. Notice that the stated asymptotic
can still be right: (6.5) gives
\[
  \lambda_n\to1,\qquad \lambda_n^n\to2=h(1).
\]
Thus the defect targets the exact finite-\(n\) equation and eigenvector bridge, not
automatically the limiting conclusion.

The smallest repair suggested by this example is to replace the reduced multiplier
\(\lambda^k\) by \(\lambda^{-k}\). Then
\[
  h_-(\lambda_n)
  =
  \lambda_n^{-2}+\lambda_n^{-3}
  =
  \lambda_n^n
\]
is exactly (6.5). This also matches the decrease of a right Perron vector along a
source-column delay chain. It is a mathematically coherent candidate correction,
not a statement contained in the hashed source. The direct block calculation in
`corrected_clone_theorem_derivation.md` subsequently proves that it is the exact
literal-clone correction for every graph satisfying the stated hypotheses.

The scalar clone equation and asymptotic conclusion do survive the independently
proved sign repair, but an exact source import must not silently attribute that
repair to KKL. In particular, a positive-weight abstract family
\[
  \widehat T_\lambda(i,j)
  =
  \sum_{e:i\to j}\lambda^{k(e)}
\tag{6.7}
\]
may be studied as a separate weighted-transfer model, but it is not the literal
cross-section clone operator. Its identification with KKL lines 2257--2264 remains
**source-invalid under the checked literal definitions**.
Transposition alone preserves the Perron root, but it does not repair an exponent
sign.

There is a second unrelated exponent typo in `value1.tex`, line 12: it states a
\(\lambda^{-1}\) bound “for every \(n\ge0\),” which is impossible at \(n=0\) for a
positive valuation. The proved and subsequently used statement at lines 97 and 111
is the coherent
\[
  \operatorname{val}((f^n)^*X)
  \le
  \lambda_F^{-n}\operatorname{val}(X).
\]

## 7. Required bridge in the project

The project may keep its source-column convention. The source-faithful repair for
the **Value argument** is:

1. **Core matrix.** Whenever a project matrix \(B\) represents KKL's directed core
   incidence, state
   \[
     B_{\gamma\beta}
     =
     \#\{\alpha\in\iota^*\beta:f_*\alpha=\gamma\}.
   \]
   Equivalently, define the raw row-source incidence \(N=B^{\mathsf T}\). Do not
   state either \(B=T_F\) or \(B=T_F^{\mathsf T}\) without declaring which reading
   of the inconsistent source notation is being used.
2. **Products.** Compare
   \[
     B_m\cdots B_1
     \quad\text{with}\quad
     N_1\cdots N_m
   \]
   through (4.2).
3. **Eigenweights.** Translate KKL \(v\) to the project left eigenweight and KKL
   \(w\) to the project right eigenweight.
4. **Value.** Use \(c=\ell_{\rm left}^2\odot r_{\rm right}\), with any
   Hubbard-intersection extension applied afterward exactly as in KKL. Do not use
   \(r^2\odot\ell\).
5. **Clone matrices.** Keep the row-source convention of
    `corrected_clone_theorem_derivation.md`. Its independently derived literal-clone
    operator is
    \[
      H(t)=t^{-1}D(tI-Q)^{-1}C=\sum_k t^{-k}R_k.
    \]
    Do not attribute that repair to KKL lines 2257--2264. A transpose preserves
    spectral radius and sends \(H(t)\) to \(H(t)^{\mathsf T}\); it does not change
    the exponent sign.
6. **WAD incidence.** Type every map by domain and codomain before composing it.
   The project's \(B=N^{\mathsf T}\) is the incoming-weight operator appearing in
   KKL's \(w\)-equation and the forward source-mass incidence. That numerical
   coincidence is not by itself a proof that a proposed WAD block \(R\) or
   incidence block \(C\) realizes KKL's pullback correspondence.

The following current phrases require this correction or an explicit bridge:

- `transfer_convention_and_frame.md`, Sections 2 and 5;
- `corridor_support_automaton.md`, Virtual Support Automaton Item 1;
- `dynamical_corridor_certificate.md`, Section 4 and Corollary 4.2;
- `virtual_support_automaton_construction.md`, `CT7`;
- `support_automaton_redteam.md`, the phrase “KKL-style source columns”;
- any source-identity clause that equates a source-column \(B\) directly with the
  KKL “core pushforward.”

The abstract spectral theorems do not need demotion merely because
\(\rho(N)=\rho(N^{\mathsf T})\). Any theorem importing KKL's exact displayed clone
equation does need a source-status correction because of Section 6. Eligibility for
KKL Value separately requires the left/right and WAD-incidence bridge above.

## 8. Adversarial regression checks

Every source-identity audit should now include:

1. **One-edge check.** For one directed occurrence \(1\to2\),
   \[
     N_{\rm row\ source}=
     \begin{pmatrix}0&1\\0&0\end{pmatrix},
     \qquad
     B_{\rm project}=
     \begin{pmatrix}0&0\\1&0\end{pmatrix}.
   \]
2. **Product check.** For noncommuting \(N_1,N_2\), verify
   \[
     B_2B_1=(N_1N_2)^{\mathsf T}.
   \]
3. **Eigenweight check.** Verify that KKL \(v\) satisfies
   \(B^{\mathsf T}v=\lambda v\), while KKL \(w\) satisfies
   \(Bw=\lambda w\).
4. **Value check.** On a nonsymmetric primitive example, verify
   \(v^2\odot w\), not \(w^2\odot v\).
5. **Clone check.** Test the chain recurrence against the sign of every
   \(\lambda^k\) weight. Do not treat transposition as a repair for the source
   inconsistency isolated in Section 6.

## 9. Exact boundary of this audit

This note settles the typed Value incidence, chronological product, and left/right
eigenweight roles for the checked KKL26 snapshot. It proves that the source symbol
\(T_F\) itself is not globally orientation-consistent, and it isolates an
independent sign/orientation defect in the clone appendix. It therefore does **not**
source-license the printed \(+\lambda^k\) equation. The independent
\(t^{-k}\) repair is proved in `corrected_clone_theorem_derivation.md`. Neither note
proves that any proposed virtual hull has a KKL core correspondence, a complete WAD
itinerary, or a Value-faithful finite quotient. Those remain realization
obligations.

## 10. Project remediation status

The live project now uses raw incidence \(N\), project
\(B=N^{\mathsf T}\), KKL \(v,w\) in project left/right roles, and Value \(v^2w\).
The global source-identification phrases listed in Section 7 were replaced by this
typed formulation. `KKL_PRINTED_CLONE_EQUATION_NO_GO` records the finite-\(n\)
counterexample as proved. `KKL_CLONE_EIGEN` is now proved internally by the exact
negative-weight Schur reduction, fixed-template limit, and both typed gate-eigenvector
limits in `corrected_clone_theorem_derivation.md`; this does not rehabilitate the
printed equation. The variable-clone estimates use that corrected theorem and still
require literal virtual-corridor realization.
