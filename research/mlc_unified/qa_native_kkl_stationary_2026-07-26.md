# QA-2: native KKL stationary-Wave proof

## 1. Scope and verdict

This report reconstructs, directly from the locked KKL TeX source, the
proof of Proposition `prop:into the critical limb` at master lines
1534--1623.  It audits the preliminary telescope, the stationary
alignment paragraph, the final component and degree, and the
renormalization-width estimate.  It does not repair the proof and does
not alter the proof ledger or manuscript.

The locked source is:

```text
research/mlc_unified/.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The included stationary auxiliary file is:

```text
research/mlc_unified/.tmp_wave_audit/not-all-good2.tex
SHA-256 B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01
```

### Binary result

The native proof is **not complete as printed**.  There are three
logically independent missing packages.

1. **Relative one-step telescope.**  Lines 1560--1579 do not prove
   \(\mathcal W(A_n\setminus A_{n+1})=O_b(1)\).  In particular, line
   1576 is false as written and is not repaired merely by replacing
   \(S_{n+1}\) with \(X_n\).
2. **Pointwise retained two-path break certificate.**  Line 1603 does
   not prove that its two topological portions are proper retained
   paths in the complete pulled marking, nor that their terminal
   covering images are distinct.
3. **Final measurable exit lamination.**  Lines 1605--1611 do not
   construct, from the source-language phrase “passes through,” an
   actual measurable lamination in the final pulled surface having one
   fixed component at one end and the complementary component package
   at the other.

There are also definite source errors:

- \(A_N\) at line 1605 is undefined; the intended family is
  \(A_{N-1}\).
- The equality at line 1569 binds \(X_{n+1}\) to \(A_{n+1}\) while the
  sentence defines \(A'_{n+1}\).
- \(\mathcal K^n\) at line 1609 has a free index; the intended package
  is \(\mathcal K^{N-1}\).
- Under the canonical filled-set interpretation of the selected
  component, the degree at lines 1593 and 1613 is \(2\), not \(1\).
  A safe source-local bound is the total degree
  \(2^{N-1}=2^{b+2}\).

The answer to the structural question in the freeze checkpoint is:

> A **pointwise**, fully marked, two-distinct-output break certificate
> at \(n=b\) and \(n=b+1\) is sufficient for the contradiction intended
> at line 1603.  A family-level doubled-width paired-Wave response is
> not a dependency of the native alignment argument.

This does **not** mean that a pointwise certificate alone completes the
proposition.  The relative telescope and final measurable exit
lamination remain family-level obligations.  They require width-faithful
and measurable assembly, but not the stronger paired-response
amplification theorem.

No status of MLC, UPTCR, VAAPC-I, or the native KKL stationary repair is
changed by this report.  All remain open.

## 2. Classification convention

Each inference below receives exactly one principal classification.

```text
verified
    Follows from the locked definitions and previously stated source
    results with the required objects correctly typed.

verified only under explicit hypotheses
    The derivation is valid once the hypotheses listed here are supplied;
    the locked paragraph does not supply all of them.

downgraded to conditional
    A printed conclusion is plausible but depends on an unproved
    intermediate construction or comparison.

false as written
    The displayed assertion, index, type, or inequality is wrong under
    its literal reading.

source mismatch
    The prose defines or invokes an object different from the object in
    the formula, or uses notation not defined at that point.

open
    The source contains no proof of the required analytic or topological
    statement and it cannot be recovered by a purely formal correction.
```

“Typographical” is used only for a symbol whose unique intended
replacement is clear.  A clear typo does not validate the mathematical
existence or estimate surrounding that symbol.

## 3. Exact indices and unbreakability

KKL set

\[
  N=b+3
  \tag{3.1}
\]

at line 1547 and define

\[
  A_0=A^{N\text{-nbr}}\setminus A^{\rm sh},
  \qquad
  A_n\subset A_{n-1}\quad(0<n<N)
  \tag{3.2}
\]

at line 1548.  Thus the complete declared list is

\[
  A_0,A_1,\ldots,A_{N-1}
  =
  A_0,A_1,\ldots,A_{b+2}.
  \tag{3.3}
\]

There is no \(A_N\).

KKL lines 1355--1357 define \(A^{r\text{-nbr}}\) leafwise: a leaf
\(\alpha\) belongs to it exactly when

\[
  F_*^j\alpha\text{ does not break under }F
  \quad\text{for every }0\leq j<r.
  \tag{3.4}
\]

A path breaks when its next untagged pushforward is not a single path
(lines 2161--2162).  Consequently, if

\[
  \alpha\in A_{n+1}\subset A_0\subset A^{N\text{-nbr}}
  \quad\text{and}\quad n+1<N,
  \tag{3.5}
\]

then the successive untagged images of \(\alpha\) remain single paths
through time \(n+1\).  This is a direct consequence of the definition;
no width estimate is involved.

For the two proof-used indices,

\[
 \begin{array}{c|c|c}
 n & A_{n+1} & \text{separator named at line 1603}\\ \hline
 b   & A_{b+1} & K_0^b,\\
 b+1 & A_{b+2}=A_{N-1} & K_0^{b+1}.
 \end{array}
 \tag{3.6}
\]

Since \(A_{N-1}\subset A_{b+1}\), a valid line-1603 inference at these
two indices would give, for every leaf of the actually defined
\(A_{N-1}\), both source-language pass-through predicates

\[
  K_0^b,\qquad K_0^{b+1}.
  \tag{3.7}
\]

This conditional indexing repair is **verified**.  It uses neither an
\(A_N\) nor an index outside (3.3).  Line 1605 is **false as written**
because it invokes \(A_N\).

The word “universal” in line 1535 is governed by the convention at line
1149 that every constant in the Wave section may depend on the fixed
parabolic bound \(b\).  Thus \(N=b+3\) is uniform in the satellite
period and rotation denominator after \(b\) is fixed, but it is not an
absolute constant independent of \(b\).

## 4. Reconstruction of the preliminary telescope

### 4.1 The intended induction

For a fixed \(0\leq n<N-1\), line 1559 sets

\[
  S_n=F_*^nA_n.
  \tag{4.1}
\]

By the definition of \(A_n\), \(S_n\) is intended to be a Wave ending
at \(BL_0\).  Because \(A_n\subset A^{N\text{-nbr}}\), the leafwise
calculation

\[
  F_*^j(F_*^n\alpha)=F_*^{n+j}\alpha,
  \qquad 0\leq j<N-n,
  \tag{4.2}
\]

does verify

\[
  S_n=S_n^{(N-n)\text{-nbr}},
  \tag{4.3}
\]

provided \(S_n\) has been constructed as the actual retained
single-path image of the occurrences in \(A_n\).  This last occurrence
qualification matters because KKL's \(F_*\) is an untagged set-valued
restriction followed by a covering pushforward.

The intended one-step scheme is:

\[
\begin{array}{ccccc}
A_n & \xrightarrow{\ F_*^{n}\ } & S_n
& \xrightarrow{\ F_*\ }&
X_n=X_{n+1}\sqcup Y_{n+1}\sqcup Z_{n+1},\\
&&&&\rotatebox{90}{\(\subset\)}\\[-2mm]
&&&&F_*^{n+1}A_n,
\end{array}
\tag{4.4}
\]

where \(X_{n+1}\) is the part ending at \(BL_0\), \(Y_{n+1}\) is over
\(BL_0\), and \(Z_{n+1}\) is subordinate to
\(\partial_{\rm C}T\setminus BL_0\).  One then wants an
occurrence-compatible source subwave \(A'_{n+1}\subset A_n\) with

\[
  F_*^{n+1}A'_{n+1}=X_{n+1},
  \tag{4.5}
\]

so maximality gives \(A'_{n+1}\subset A_{n+1}\).  If the discarded
source mass is controlled by the two extraneous output families and by
the Wave buffer, one obtains

\[
  \mathcal W(A_n\setminus A_{n+1})=O_b(1).
  \tag{4.6}
\]

Formula (4.4)--(4.6) is the intended architecture.  The locked source
does not establish all of its arrows.

### 4.2 Line 1560: Wave output and “no short leaves”

The Wave lemma at lines 2149--2152 says:

\[
 \mathcal W(Q)\leq\mathcal W(f_*Q)+O(1+\log d)
 \tag{4.7}
\]

after extracting an output Wave from a **source** Wave \(Q\) whose
whole ending multi-interval has degree at most \(d\).  It does not say
that the output has no short leaves.

To derive the first part of line 1560 for \(F_*=f_*\iota^*\), one must
first construct a retained source Wave \(Q_n\subset\iota^*S_n\), show
that every source leaf is a path in the fine marking and is not removed
by the coarse filter at lines 2096--2097, prove

\[
  \mathcal W(S_n)\leq\mathcal W(Q_n),
  \tag{4.8}
\]

and bound the degree of \(f\) on the complete ending multi-interval of
\(Q_n\).  The one-step global degree \(2\) would suffice for (4.7).
The source treats this composite use as implicit.

Even granting that implicit application, (4.7) yields an \(X_n\) with

\[
  \mathcal W(S_n)\leq\mathcal W(X_n)+O_b(1),
  \tag{4.9}
\]

but supplies no “no short leaves” clause.  That clause would follow
from a separate combinatorial statement saying that the selected
unbreakable pushforward of every leaf outside \(A^{\rm sh}\) remains
outside the new short part.  No such statement is cited or proved in
the locked paragraph.

Classification:

```text
existence of an output Wave and (4.9):
    verified only under explicit retained-source-Wave, domination,
    and ending-degree hypotheses;

the assertion that X_n has no short leaves:
    open; it is not a conclusion of the cited Wave lemma.
```

#### 4.2.1 The native input is not a certified single deck packet

There is no stronger coherence predicate on \(S_n\) elsewhere in the
stationary construction.  The exact selection condition at line 1548
is only:

> \(A_n\) is a maximal subwave such that \(F_*^nA_n\) is a Wave ending
> at \(BL_0\).

Line 1559 repeats only:

> \(S_n\) is a Wave ending at \(BL_0\).

This does not say that \(S_n\) is localized, has one fixed other end,
belongs to one lifted rectangle, or consists of one deck-span class.
The distinction is literal in the source:

- lines 1872 and 1874--1875 say that a Wave *ends at a
  multi-interval* when all leaves have an endpoint somewhere in that
  multi-interval;
- a Wave is *localized* only when it ends at a single interval
  (lines 1151 and 1872); and
- \(BL_0=\partial_{\rm C}L_0\) is a multi-interval of combinatorial
  length at most \(6b\), not a declared single interval (lines
  838--841).

The generic Wave definition supplies one connected base and its
associated ends and crest.  It does not exclude a lamination whose
lift decomposes into several deck-translated route or span packets
inside that base.  Removing the short part in the definition of
\(A_0\) also supplies no deck-span uniqueness.

This matters because the checked source does not prove KKL Lemma A.13,
and its cited annular proof prunes deck-collision classes.  If the
broad “degree on the ending multi-interval” formulation does not
control a union of several translated packets, the native predicate
above does not remove that failure mode.  The line-1560 application
therefore requires one of the following additional inputs:

1. a proof of the broad KKL Wave lemma for arbitrary Waves of the
   stated type;
2. a decomposition of \(S_n\) into coherent deck packets together with
   a relative width accounting theorem whose total discarded charge is
   \(O_b(1)\); or
3. a restricted Wave lemma using a certified cyclic collar and the
   degree/collision span of the **full Wave base**, followed by a proof
   that the actual \(S_n\) satisfies its hypotheses.

The third item cannot presently be inferred merely from
\(\deg(f;I')\) on one ending interval.  Nor can the unreviewed
full-base candidate theorem be used as established evidence.

Classification:

```text
S_n is one Wave ending at the multi-interval BL_0:
    verified as the declared selection predicate;

S_n is localized or is one coherent/common-lift deck packet:
    not stated and not derivable from that predicate;

applicability of the broad Wave lemma at line 1560:
    open pending a proof of the broad lemma or a certified restricted
    packet/full-base reduction.
```

### 4.3 Line 1565: the wrong family is used

Line 1564 decomposes \(X_n\), not \(S_{n+1}\).  The propositions invoked
at line 1565 bound:

\[
 \mathcal W(Y_{n+1}^{\rm nbr})=O_b(1)
 \tag{4.10}
\]

for a Wave over \(BL_0\), and

\[
 \mathcal W(Z_{n+1}^{\rm nbr})
 \leq
 \mathcal W(Z_{n+1}^{\rm sh})+O_b(1)
 \tag{4.11}
\]

for a localized Wave away from \(BL_0\).  The statement
\(S_{n+1}=S_{n+1}^{(N-n-1)\text{-nbr}}\) says nothing by itself about
the distinct families \(Y_{n+1}\) and \(Z_{n+1}\).

The intended replacement is the inherited pointwise fact

\[
  X_n=X_n^{(N-n-1)\text{-nbr}},
  \tag{4.12}
\]

which follows only if \(X_n\subset F_*S_n\) retains the actual
occurrence provenance in (4.2).  Then \(Y_{n+1}\) and \(Z_{n+1}\), as
subfamilies, are one-step unbreakable.  If the unproved no-short clause
from Section 4.2 also holds, then
\(Z_{n+1}^{\rm sh}=\varnothing\), and (4.10)--(4.11) give

\[
 \mathcal W(Y_{n+1})+\mathcal W(Z_{n+1})=O_b(1).
 \tag{4.13}
\]

Classification:

```text
the literal appeal to S_{n+1}:
    source mismatch;

the intended estimate (4.13):
    downgraded to conditional on occurrence-compatible inherited
    unbreakability and the missing no-short transport.
```

### 4.4 Line 1569: \(A_{n+1}\) versus \(A'_{n+1}\)

The sentence defines \(A'_{n+1}\), so its displayed equality must be
(4.5), not

\[
  F_*^{n+1}A_{n+1}=X_{n+1}.
 \tag{4.14}
\]

This symbolic correction is unambiguous.  It does not prove that an
exact \(A'_{n+1}\) exists.  Since \(F_*^{n+1}\) forgets sheet and
occurrence multiplicity, the inclusion

\[
  X_{n+1}\subset F_*^{n+1}A_n
 \tag{4.15}
\]

does not canonically select a Borel sublamination of \(A_n\) mapping
exactly onto \(X_{n+1}\).  One needs an occurrence relation or a
measurable selector, together with a proof that the selected leaves
form a Wave.

If such an \(A'_{n+1}\) is supplied, the maximality in line 1548 is
intended to give

\[
  A'_{n+1}\subset A_{n+1}
  \quad\Longrightarrow\quad
  \mathcal W(A_{n+1})\geq\mathcal W(A'_{n+1}).
 \tag{4.16}
\]

The source also does not prove existence and uniqueness of the
“maximal subwave” in line 1548; unions of different endpoint or
occurrence classes need not remain one Wave without an endpoint-class
argument.

Classification:

```text
the symbol A_{n+1} in line 1569:
    source mismatch; the intended symbol is A'_{n+1};

exact occurrence-compatible A'_{n+1} and maximality:
    open;

inequality (4.16):
    verified once those objects exist.
```

### 4.5 Line 1576: the displayed width comparison is false

After correcting line 1569, one has

\[
  X_{n+1}=F_*^{n+1}A'_{n+1}
  \subset
  F_*^{n+1}A_{n+1}=S_{n+1}.
 \tag{4.17}
\]

Therefore \(S_{n+1}\setminus X_{n+1}\) records, at best, output
occurrences coming from \(A_{n+1}\setminus A'_{n+1}\).  The left side
at line 1576,

\[
  A_n\setminus A'_{n+1},
 \tag{4.18}
\]

also contains all of \(A_n\setminus A_{n+1}\), which is exactly the
unknown family the lemma is trying to bound.  Thus

\[
 \mathcal W(A_n\setminus A'_{n+1})
 \leq
 \mathcal W(S_{n+1}\setminus X_{n+1})+O_b(1)
 \tag{4.19}
\]

has no support and is circular.  For example, at the level of the
claimed set relations, one may have
\(A_{n+1}=A'_{n+1}\), so the displayed output difference is empty,
while \(A_n\setminus A'_{n+1}\) is arbitrary.

Replacing \(S_{n+1}\) by \(X_n\) produces the plausible target

\[
 \mathcal W(A_n\setminus A'_{n+1})
 \stackrel{?}{\leq}
 \mathcal W(X_n\setminus X_{n+1})+O_b(1),
 \tag{4.20}
\]

but (4.20) does not follow from the aggregate estimate (4.9).  An
existential Wave extraction with total loss \(O_b(1)\) need not
preserve the widths of complementary occurrence subfamilies.  A
relative or buffered extraction theorem must prove that the discarded
source occurrence mass is \(O_b(1)\) and that the retained partition
corresponds to
\(X_{n+1},Y_{n+1},Z_{n+1}\).

Classification:

```text
line 1576:
    false as written;

the replacement (4.20):
    open, not a typographical consequence of the Wave lemma.
```

### 4.6 Telescope conclusion

If one independently proves

\[
  \mathcal W(A_n\setminus A_{n+1})\leq C_b
  \quad(0\leq n<N-1),
 \tag{4.21}
\]

then nestedness and \(N-1=b+2\) give

\[
\begin{aligned}
 \mathcal W(A^{N\text{-nbr}})
 &\leq
 \mathcal W(A^{\rm sh})+\mathcal W(A_0)\\
 &\leq
 \mathcal W(A^{\rm sh})
 +\mathcal W(A_{N-1})
 +\sum_{n=0}^{N-2}
   \mathcal W(A_n\setminus A_{n+1})\\
 &\leq
 \mathcal W(A^{\rm sh})
 +\mathcal W(A_{N-1})
 +O_b(b).
\end{aligned}
\tag{4.22}
\]

Thus line 1588 is **verified only under** (4.21).  The algebra is
correct; its one-step input is not established.

The minimal missing telescope theorem is not a paired-Wave response.
It is a one-output, occurrence-compatible **relative Wave extraction**
showing (4.21).

## 5. Reconstruction of the alignment paragraph

### 5.1 Selected pullback objects

Line 1597 introduces \(K_0^0\), \(\alpha^0\), and \(L_0^0\), then
selects components of their successive inverse images in the critical
limb \(L_0\).  The locked source never separately defines the initial
label \(K_0\); the canonical intended interpretation is the critical
small Julia set in the primitive cycle.  The source also alternates
between \(\alpha^n\) and \(\alpha_n\).

Existence and uniqueness of the named inverse component in \(L_0\) are
not proved in this paragraph.  They can be supplied by a selected
proper inverse-component construction, but they are not consequences
of the word “the” alone.

Classification:

```text
initial K_0 and alpha index convention:
    source mismatch;

selected inverse-component chain:
    verified only under an explicit uniqueness/selection convention.
```

### 5.2 Line 1598: component counting versus tree disjointness

The stated implication

\[
  K\subset L_0^n,\ K\in\operatorname{Comp}\mathcal K
  \quad\Longrightarrow\quad
  F(K)\subset L_0^{n-1}
 \tag{5.1}
\]

is consistent with the selected pullback definition.  Iterating it
shows that a depth-\(n\) small-Julia component in \(L_0^n\) would
produce a chain of cycle components in the critical limb.  The bound
of at most \(b\) cycle components in that limb therefore excludes a
chain of \(b+1\) distinct cycle components.

The printed conclusion is stronger:

\[
  L_0^b\cap T=\varnothing.
 \tag{5.2}
\]

The preceding sentence explicitly counts components of \(\mathcal K\),
not arbitrary edge or branch-point pieces of \(T\).  To obtain (5.2)
one needs a tree lemma saying that every nonempty intersection
\(L_0^b\cap T\) forces a cycle component in the selected predecessor
chain, with no repeated cycle member before the relevant depth.  That
lemma is not stated in lines 1597--1598.

Classification:

```text
small-Julia component counting:
    verified only under distinctness of the selected cycle itinerary;

the full disjointness L_0^b cap T = empty:
    downgraded to conditional on an omitted Hubbard-tree endpoint lemma.
```

### 5.3 Line 1600: one retained path at depth \(n\)

From \(F_*^nA_n\) being a Wave ending at \(BL_0\), the source claims
that every leaf of \(A_n\) restricts in the depth-\(n\) surface to a
path ending at \(L_0^n\).  The definition of \(F_*\) at lines
2096--2141 makes this a nontrivial claim.

At every stage a candidate restriction component must:

1. be a proper path in the source surface;
2. have both endpoints in intervals of the fine marking \(f^*\mathcal I\);
3. not be subordinate to one interval of the coarser
   \(\iota^*\mathcal I\);
4. survive the same test through all later stages; and
5. remain attached to the same occurrence of the original leaf.

The statement that the final untagged image is one path proves neither
the properness of a particular inverse component nor a complete
occurrence history for it.  KKL's itinerary proposition at lines
2099--2108 permits adjacency and same-pullback containment in place of
an actual restriction path.

Classification:

```text
line 1600:
    open as an actual complete-horizon retained-component assertion.
```

### 5.4 Line 1602: separation

The source asserts first that \(K_0^0\) separates the fixed access from
\(L_0^1\), then pulls this separation back to every depth.  This is
valid only if the selected inverse branches are homeomorphic on
neighborhoods of the separator and preserve the two named accesses.
A set-theoretic component of \(F^{-1}(K_0^{n-1})\) alone does not
preserve a marked separation statement across a branched or
multi-sheeted ambient pullback.

The final implication that \(K_0^n\) separates \(T\) from
\(L_0^{n+1}\) also consumes (5.2).

Classification:

```text
line 1602:
    verified only under selected univalent-neighborhood, access
    preservation, and the missing tree-disjointness hypotheses.
```

### 5.5 Line 1603: exact logical requirement

Fix one of the only two needed values

\[
  n\in\{b,b+1\},
  \qquad h=n+1,
 \tag{5.3}
\]

and a leaf occurrence \(\alpha\in A_h\).  If \(\alpha\) avoids the
selected separator, KKL name two portions:

\[
\begin{aligned}
 \gamma^-_\alpha &: BL_0\rightsquigarrow L_0^h,\\
 \gamma^+_\alpha &: L_0^h\rightsquigarrow
       \partial_{\rm C}T\setminus BL_0.
\end{aligned}
\tag{5.4}
\]

For these portions to contradict (3.5), the following pointwise
certificate is necessary and sufficient:

\[
\begin{split}
\operatorname{PBC}(n,\alpha):\quad&
\gamma^-_{n,\alpha},\gamma^+_{n,\alpha}
\text{ are two retained proper depth-}h\text{ components};\\
&
\text{each survives the fine-marking and coarse-subordination
filters at every stage};\\
&
(f^h)_*\gamma^-_{n,\alpha}
\ne
(f^h)_*\gamma^+_{n,\alpha}
\text{ as unparametrized terminal marked paths.}
\end{split}
\tag{5.5}
\]

If (5.5) holds, then \(F_*^h\alpha\) contains at least two paths.  This
contradicts \(h\)-step unbreakability in (3.5).  The deduction is
**verified** and is purely pointwise.

The source does not prove (5.5):

- separation gives candidate portions, not proper source components;
- an ideal endpoint at \(L_0^h\) must belong to the full fine marking;
- line 2097 can discard a component subordinate to one coarse interval;
- two distinct source components can have the same covering image;
- two sheet labels therefore do not prove two untagged output paths;
- the two portions must be tied to the same leaf occurrence and the
  same stopping horizon; and
- end-properness is proved only on end intervals and cannot silently be
  promoted to properness on the whole critical-end package.

The two open portions share a formal ideal occurrence at \(L_0^h\);
that common ideal point is not part of either open proper path.  To
exclude double-counting, their occurrence record must include at least

\[
  (\text{stage},\text{sheet},\text{parent component},
    \text{entry access},\text{exit access},
    \text{fine ends},\text{coarse ends},\text{terminal path}).
 \tag{5.6}
\]

Classification:

```text
line 1603's contradiction after (5.5):
    verified;

construction and distinctness certificate (5.5):
    open;

the printed implication without (5.5):
    unsupported.
```

### 5.6 The corrected terminal index

Assuming (5.5) at \(n=b\) and \(n=b+1\), the calculation in (3.6)
proves that every leaf occurrence in \(A_{N-1}\) has the two
source-language pass-through predicates (3.7).  This is the complete
index correction.  No statement for \(A_N\) is required or meaningful.

## 6. From pass-through to a component-to-component lamination

### 6.1 Pullback typing

The lemma statement at lines 1591--1593 is about the final pulled
surface

\[
 U^{m}\setminus\mathcal K^{m},
 \qquad m=N-1=b+2.
 \tag{6.1}
\]

The source uses \(K_0^b\) and \(K_0^{b+1}\), which were defined in the
base dynamical plane, as if they were already components of
\(\mathcal K^m\).  A typed proof must form their graph lifts under the
final immersion coordinate and prove that they are distinct components
of \(\mathcal K^m=(f^m)^{-1}(\mathcal K)\).  This does not follow from
the notation \(K_0^b\subset\mathcal K^m\).

Under that graph construction, their covering projections are

\[
 f^m(\widehat K_b)=F^2(K_0^0),
 \qquad
 f^m(\widehat K_{b+1})=F(K_0^0),
 \tag{6.2}
\]

which are distinct members of the primitive cycle.  This confirms that
there are two different candidate final components, but it does not
put any particular leaf restriction between them.

Classification:

```text
K_0^b subset K^{N-1} as printed:
    source mismatch;

existence and distinctness of the canonical graph components:
    valid under the separately proved graph realization, but absent
    from the locked paragraph.
```

### 6.2 Required final exit property

The source-language assertion that a leaf “passes through” both
successive pullback continua does not itself prove that one component
of its final immersion restriction is a proper path between them.  The
restriction can split; an end can be ambient or nonproper; a component
can be filtered; and the two shallower incidences can refine to
different final occurrence components.

The native proof needs the following family theorem.  For one fixed
final component \(Q\), every \(\alpha\in A_m\) must have a retained
proper restriction

\[
  \beta_\alpha\subset\iota_m^{-1}(\alpha)
  \cap(U^m\setminus\mathcal K^m)
 \tag{6.3}
\]

with one end on \(Q\) and the other on
\(\mathcal K^m\setminus Q\).  Moreover the collection

\[
  B=\{\beta_\alpha:\alpha\in A_m\}
 \tag{6.4}
\]

must be a measurable lamination in the declared final marking and
must satisfy the hypothesis of KKL's domination lemma:

\[
  \text{every }\iota_m^*\alpha\text{ contains a leaf of }B.
 \tag{6.5}
\]

Only then does line 2087 yield

\[
  \mathcal W(A_m)\leq\mathcal W(B).
 \tag{6.6}
\]

Line 1592 asserts only individual path existence, while line 1609
jumps directly to a lamination \(B\).  It provides no measurable
selection, no repeated-incidence convention, and no proof of (6.5).
Also, \(\mathcal K^n\setminus K\) at line 1609 has an unbound \(n\);
the only consistent replacement is
\(\mathcal K^{N-1}\setminus K\).

Classification:

```text
free index K^n at line 1609:
    source mismatch;

the implication from individual pass-through to B and (6.6):
    open;

(6.6) after a valid B satisfying (6.5):
    verified by the source domination lemma.
```

This is a family-level obligation, but it is a **one-path final exit
assembly**, not a paired-Wave response.

## 7. Final degree

### 7.1 Exact canonical degree

Take the source's intended component \(K=K_0^b\) and
\(m=b+2\).  Along the selected critical-limb pull,

\[
  F^b:K_0^b\longrightarrow K_0^0
 \tag{7.1}
\]

has degree one: each selected inverse target avoids the critical value,
so its selected inverse component is univalent.  The central small
Julia set \(K_0^0\) contains the unique critical point, hence

\[
  F:K_0^0\longrightarrow F(K_0^0)
 \tag{7.2}
\]

has degree two.  The next cycle step avoids the critical point and has
degree one:

\[
  F:F(K_0^0)\longrightarrow F^2(K_0^0).
 \tag{7.3}
\]

Therefore

\[
\deg\!\left(
 F^{b+2}:K_0^b\longrightarrow F^2(K_0^0)
\right)
=1\cdot2\cdot1=2.
\tag{7.4}
\]

The fiber-product graph coordinate conjugates this restriction to the
covering projection \(f^m\) on the canonical final component, so the
analytic and ideal-boundary degree is \(2\).  The alternative component
over \(K_0^{b+1}\) also has degree \(2\): it has \(b+1\) selected
univalent predecessor steps followed by the central degree-two step.

Thus the degree-one assertions at lines 1593 and 1613 are **false
under the canonical intended component realization**.  If the symbol
\(K_0^b\) is intended to mean some other final component, the source
does not construct that component or relate it to line 1603.

Line 1613 also writes \(F^{N-1}\) where the covering lemma is applied to
the covering projection \(f^{N-1}\).  This is a type mismatch.

### 7.2 A safe bound sufficient for the asymptotic estimate

The native big-\(O\) conclusion does not require the sharp degree.
The complete covering \(f^m\) has total degree

\[
  d_{\rm global}\leq2^m=2^{b+2}.
 \tag{7.5}
\]

Therefore, after a valid ending multi-interval for \(B\) is
constructed, KKL's pushforward-lamination lemma at lines 2075--2078
gives the unconditional fixed-\(b\) estimate

\[
  \mathcal W(B)
  \leq
  2^{b+2}\mathcal W(C)+2^{b+3}.
 \tag{7.6}
\]

With the exact canonical degree \(2\), this improves to

\[
  \mathcal W(B)\leq2\mathcal W(C)+4.
 \tag{7.7}
\]

Thus the false degree-one sentence is a real mathematical error but is
not, by itself, fatal to the fixed-\(b\) width bound.  The ending degree
must be a degree on the **whole marked ideal multi-interval** used by
the lamination lemma; a local degree at a continuum or one access is
not sufficient without a prime-end/collar transfer.

## 8. The estimate \(\mathcal W(C)\leq2\mathcal W(\mathcal RF)\)

This estimate can be reconstructed from other locked source statements
once \(C\) has been correctly constructed.

Let \(K_j=F^j(K_0^0)\) be the fixed cycle component at the first end of
\(C\), and let \(J_j=\partial_{\rm C}K_j\) be its interval in the
minimal ideal marking of \(U\setminus\mathcal K\).  If the other end of
every leaf lies on a cycle component different from \(K_j\), every leaf
of \(C\) has a subpath crossing the annular localization of \(K_j\).
This is the intended canonical pair: (6.2) gives the two distinct image
components \(F^2(K_0^0)\) and \(F(K_0^0)\).  Series monotonicity followed
by inclusion into the full annular path family gives

\[
  \mathcal W(C)\leq\mathcal W(J_j).
 \tag{8.1}
\]

KKL lines 818--823 state

\[
 \mathcal W(\mathcal RF)=\mathcal W(J_0),
 \qquad
 \frac12\mathcal W(J_0)
 \leq\mathcal W(J_j)
 \leq\mathcal W(J_0).
 \tag{8.2}
\]

Consequently,

\[
  \mathcal W(C)
  \leq\mathcal W(\mathcal RF),
 \tag{8.3}
\]

which is stronger than the factor-two assertion at line 1617.  Allowing
the harmless orientation/two-side convention still gives the printed
bound.

Classification:

```text
line 1617:
    verified only after C is a proper valid lamination with one fixed
    cycle-component end, its other end outside that component, and the
    minimal marking;

construction of such a C:
    conditional on the missing final B and a correctly typed covering
    pushforward.
```

Combining the source's looser estimate with (7.7) yields

\[
  \mathcal W(A_m)
  \leq\mathcal W(B)
  \leq4\mathcal W(\mathcal RF)+4.
 \tag{8.4}
\]

Using only the safe global degree (7.6) yields

\[
  \mathcal W(A_m)
  \leq
  2^{b+3}\mathcal W(\mathcal RF)+2^{b+3}.
 \tag{8.5}
\]

Both are \(O_b(1+\mathcal W(\mathcal RF))\).  They are
\(O_b(\mathcal W(\mathcal RF))\) only when a lower bound such as
\(\mathcal W(\mathcal RF)\geq1\) is present.  The surrounding
high-type-near-degenerate application assumes
\(\mathcal W(\mathcal RF)\) sufficiently large, but Proposition
`prop:into the critical limb` does not state that hypothesis.  Taken
literally for arbitrary positive renormalization width, its omission is
a quantifier mismatch.  A self-contained statement should either say

\[
 O_b(1+\mathcal W(\mathcal RF))
 \tag{8.6}
\]

or explicitly assume a fixed lower bound on
\(\mathcal W(\mathcal RF)\).

## 9. Clause-by-clause status table

| Source location | Printed or intended claim | QA status | Reason |
|---|---|---|---|
| 1547 | \(N=b+3\) | verified | Exact arithmetic.  “Universal” allows \(b\)-dependence only by the line-1149 convention. |
| 1548 | \(A_0,\ldots,A_{N-1}\) | verified as an index range | It does not define \(A_N\). |
| 1548 | unique maximal continuation subwave \(A_n\) | open | No endpoint-class or measurable maximality proof is supplied. |
| 1559 | \(S_n=F_*^nA_n\) is a Wave ending at \(BL_0\) | verified only under the definition of \(A_n\) | It is the property used to select \(A_n\). |
| 1559 | \(S_n\) is localized or a single coherent deck packet | open/not stated | \(BL_0\) is a multi-interval; “ending at” does not impose one lifted packet or fixed other end. |
| 1559 | \(S_n=S_n^{(N-n)\text{-nbr}}\) | verified with occurrence provenance | Direct from \(A_n\subset A^{N\text{-nbr}}\). |
| 1560--1563 | Wave \(X_n\) and aggregate width loss \(O_b(1)\) | open/conditional | Besides an actual retained source Wave, domination, and degree, the broad Wave lemma or a restricted full-base/deck-packet theorem must be proved.  The native \(S_n\) predicate does not supply packet coherence. |
| 1560 | \(X_n\) has no short leaves | open | Not a conclusion of Lemma `lem:wave`; no transport lemma is cited. |
| 1564 | three-way Wave decomposition | conditional | Needs a complete, disjoint endpoint/crest classification. |
| 1565 | use of \(S_{n+1}\) to control \(Y,Z\) | source mismatch | \(Y,Z\subset X_n\), not \(S_{n+1}\). |
| 1565--1568 | \(\mathcal W(Y)+\mathcal W(Z)=O_b(1)\) | conditional | Follows from inherited unbreakability plus no-short transport; neither is fully established for the selected output. |
| 1569 | \(F_*^{n+1}A_{n+1}=X_{n+1}\) while defining \(A'_{n+1}\) | source mismatch | Must read \(A'_{n+1}\). |
| 1569 | exact source subwave \(A'_{n+1}\) exists | open | Untagged output inclusion does not give a Borel occurrence selector. |
| 1572 | \(\mathcal W(A_{n+1})\geq\mathcal W(A'_{n+1})\) | verified conditionally | Monotonicity after actual maximal subwaves exist. |
| 1576--1578 | displayed complement inequality | false as written | \(S_{n+1}\setminus X_{n+1}\) omits the unknown \(A_n\setminus A_{n+1}\) mass. |
| 1576 intended with \(X_n\setminus X_{n+1}\) | relative complement estimate | open | Does not follow from the aggregate Wave lemma. |
| 1586--1589 | telescoping algebra | verified conditionally | Correct once every one-step complement is \(O_b(1)\). |
| 1597 | selected \(K_0^n,\alpha^n,L_0^n\) | conditional/source mismatch | \(K_0^0\) and uniqueness are not fully specified; alpha notation changes. |
| 1598 | \(L_0^b\cap T=\varnothing\) | conditional | Component counting needs an omitted tree-endpoint lemma to exclude edge-only intersections. |
| 1600 | one proper retained path ending at \(L_0^n\) | open | Complete-horizon properness, marking, filter survival, and occurrence provenance are absent. |
| 1602 | pulled separator and access order | conditional | Needs univalent selected neighborhoods and marked separation naturality. |
| 1603 | two portions imply breaking | verified only with PBC (5.5) | Distinct retained terminal paths are necessary and sufficient. |
| 1603 | PBC is supplied by the paragraph | open | Properness, filters, and terminal noncollision are not proved. |
| 1605 | use \(A_N\) | false as written | \(A_N\) is undefined. |
| 1605 corrected | \(A_{N-1}\) has both pass-through predicates | conditional but index-valid | Apply line 1603 at \(n=b,b+1\). |
| 1605 | \(K_0^b\) is a typed final component | source mismatch | Requires the graph lift into \(U^{N-1}\). |
| 1593, 1613 | final degree is \(1\) | false under canonical interpretation | The critical itinerary has exactly one degree-two stage. |
| 1609 | \(\mathcal K^n\setminus K\) | source mismatch | The intended exponent is \(N-1\). |
| 1609--1612 | final lamination \(B\) and \(\mathcal W(A_{N-1})\leq\mathcal W(B)\) | open/conditional | Needs a measurable retained fixed-component exit lamination; domination then verifies the inequality. |
| 1613 | apply covering lemma to \(F^{N-1}\) | source mismatch | The covering map is \(f^{N-1}\); \(F\) denotes the pair/dynamical relation. |
| 1613--1616 | push \(B\) to \(C\) | conditional | Valid with degree \(2\), or safely \(2^{b+2}\), on the whole marked end. |
| 1617 | \(\mathcal W(C)\leq2\mathcal W(\mathcal RF)\) | verified conditionally | Follows from local-width monotonicity and lines 818--823 once \(C\) is correctly typed. |
| 1618--1622 | final \(O(\mathcal W(\mathcal RF))\) conclusion | conditional and missing a small-width qualification | The established form is \(O_b(1+\mathcal W(\mathcal RF))\), becoming \(O_b(\mathcal W(\mathcal RF))\) in the surrounding large-width regime. |

## 10. Pointwise certificate versus paired family response

The native line-1603 proof is a contradiction to a **leafwise**
unbreakability predicate.  Its logical form is

\[
\begin{aligned}
 &\alpha\in A_{n+1}
 \ \Longrightarrow\
 F_*^{n+1}\alpha\text{ is one path},\\
 &\alpha\text{ avoids }K_0^n
 \ \overset{\operatorname{PBC}}\Longrightarrow\
 F_*^{n+1}\alpha\text{ contains two distinct paths}.
\end{aligned}
\tag{10.1}
\]

No inequality involving the widths of the two portions occurs in
(10.1).  In particular, the native proof does not need:

- two full-width source Waves parametrized by all leaves;
- a Series-law estimate for their widths;
- two Wave-lemma output inequalities;
- a lower bound of the form
  \(\max_i\mathcal W(C^i)\geq2\mathcal W(S)-C_b\); or
- an ambient terminal/output-controllability assembly.

Those clauses belong to a stronger alternative response route.  They
are not the minimal repair of line 1603.

There are nevertheless two genuine family-level obligations elsewhere:

1. the relative extraction needed for the telescope (4.21); and
2. the measurable fixed-component exit lamination (6.3)--(6.6).

Calling either of these “pointwise” would be an error.  Conversely,
requiring a doubled-width paired response for them would add hypotheses
not consumed by the native proof.

## 11. Minimal residual native theorem package

The following is the smallest source-faithful package identified by
this audit.

### Gate N1: relative stationary continuation

For every \(0\leq n<N-1\), construct an occurrence-compatible
partition of the one-step Wave output and a Borel source continuation
so that

\[
 \mathcal W(A_n\setminus A_{n+1})\leq C_b.
 \tag{11.1}
\]

The proof must explicitly control the Wave-extraction buffer on the
discarded occurrence family.  An aggregate inequality for
\(\mathcal W(S_n)\) is insufficient.  Before that relative theorem can
invoke a Wave pushforward estimate, it must also prove either the broad
KKL Lemma A.13 or a restricted coherent-packet/full-base version and
verify that the actual \(S_n\) satisfies it.  “Wave ending at
\(BL_0\)” is not such a verification.

### Gate N2: pointwise two-path break

For \(n=b,b+1\), prove \(\operatorname{PBC}(n,\alpha)\) in (5.5) for
every \(\alpha\in A_{n+1}\) that avoids \(K_0^n\).  Record the complete
data in (5.6).  This is the exact minimal repair of line 1603.

### Gate N3: final retained fixed-component exit

For \(m=b+2\), construct one measurable lamination \(B\) satisfying
(6.3)--(6.6) for a fixed actual component of
\(\mathcal K^m\).  This must include the graph-component identification,
proper prime-end landing, fine/coarse filter survival, and repeated
incidence convention.

### Gate N4: correctly typed bounded-degree pushforward

Apply the covering lemma to \(f^m\), using either the exact canonical
degree \(2\) or the safe total degree \(2^{b+2}\) on the whole ending
multi-interval.  Combine it with (8.1)--(8.2) and state the conclusion
as \(O_b(1+\mathcal W(\mathcal RF))\), or add the large-width hypothesis
needed to absorb the additive constant.

Gates N1--N4 are independent.  N2 does not prove N1 or N3.  N3 does not
repair line 1603.  N4 cannot be invoked before N3 supplies an actual
marked ending interval.

## 12. Adversarial and circularity checks

1. **Undefined terminal family.**  No use of \(A_N\) was made.  Both
   separator predicates were derived conditionally for
   \(A_{N-1}=A_{b+2}\).
2. **Two source sheets versus two images.**  Distinct source components
   were not treated as distinct covering images.  The final
   noncollision clause in (5.5) is explicit.
3. **Fine/coarse filter.**  A topological subarc was not called a KKL
   path until properness, fine endpoints, and non-subordination to a
   coarse interval were required.
4. **Same occurrence.**  The two portions must carry the same original
   leaf and horizon tag; independently selected paths cannot certify
   breaking of one leaf.
5. **No family-width inference from pointwise existence.**  The final
   lamination \(B\) was left open until measurability and domination are
   proved.
6. **No aggregate-to-relative inference.**  The Wave lemma's total
   \(O_b(1)\) loss was not used to bound a complementary subfamily.
7. **No hidden single-packet premise.**  A Wave ending at the
   multi-interval \(BL_0\) was not relabeled as a localized Wave or one
   deck-span class.
8. **No circular use of the target proposition.**  Proposition
   `prop:into the critical limb` was not used to control any residual
   Wave in its own proof.
9. **Component versus label.**  Base-plane \(K_0^r\) labels were not
   identified with final fiber-product components without the graph
   lift.
10. **Degree type.**  Continuum degree, prime-end degree, and degree on
   the whole ending multi-interval were distinguished.
11. **Safe degree fallback.**  Even without the sharp local degree, the
    total degree \(2^{b+2}\) is enough for a fixed-\(b\) estimate; the
    false degree-one claim was not preserved.
12. **Small renormalization width.**  Additive covering errors were not
    silently absorbed into \(O(\mathcal W(\mathcal RF))\) without a
    lower-width hypothesis.
13. **Line 1617 independently checked.**  Its width comparison follows
    from local-width monotonicity and the source's cycle-component
    comparison, not from the incorrect degree-one assertion.

## 13. Final QA determination

The locked proof at lines 1534--1623 cannot presently be accepted as a
complete proof of Proposition `prop:into the critical limb`.

The strongest source-faithful conclusion is:

> Conditional on the relative stationary continuation Gate N1, the
> pointwise retained two-path Gate N2 at exactly \(n=b,b+1\), and the
> measurable final exit Gate N3, the native argument closes with the
> corrected covering degree in Gate N4.  The resulting bound is
> \(O_b(1+\mathcal W(\mathcal RF))\), and is
> \(O_b(\mathcal W(\mathcal RF))\) in KKL's surrounding
> high-type/large-width regime.

The minimal next analytic gate for the alignment sentence itself is
N2, not a family-level paired-Wave response.  For the whole native
proposition, N1 is an equally prior unresolved quantitative gate and
must not be bypassed.

```text
native KKL stationary proof: open
pointwise two-path break certificate: open
relative stationary telescope: open
final retained exit lamination: open
family-level paired-Wave response: not required by the native proof
MLC: open
UPTCR: open
VAAPC-I: open
```
