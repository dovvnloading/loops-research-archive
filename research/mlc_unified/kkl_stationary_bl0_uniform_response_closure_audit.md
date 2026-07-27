# Stationary \(BL_0\) uniform-survivor response: adversarial closure audit

## Post-audit status correction (2026-07-26)

The response program audited here is now an optional alternative, not
the active native stationary dependency.  Its packet algebra remains
conditional, but the broad coefficient-one KKL Wave assertion is
refuted under the printed definitions and the proposed collision bridge
is retracted.  Gate N1,
`KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION`, is the immediate native
target.

## 1. Verdict and status

The proposed implication

\[
\begin{split}
&\text{exact occurrence Series conductance}\\
&\quad+\text{conditional paired-Wave algebra}\\
&\quad+\text{typed paired-Wave realization}\\
&\quad+\text{one uniform KKL Wave constant}\\
&\Longrightarrow
\texttt{KKL\_STATIONARY\_BL0\_UNIFORM\_SURVIVOR\_RESPONSE}
\end{split}
\tag{1.1}
\]

is **not sufficient as stated**.

Even after granting the two presently open analytic inputs in (1.1),
the conclusion available without further hypotheses is only the
packet-local estimate

\[
 \max\{\mathcal W(C_q^-),\mathcal W(C_q^+)\}
 \ge 2\mathcal W(S_q)-C_b
\tag{1.2}
\]

for each realized packet \(S_q\).  Formula (1.2) does not by itself:

1. exhaust the native survivor residual;
2. prevent input or output width from being counted more than once;
3. combine gains from different horizons or packet classes;
4. make a width-maximizing output uniformly controllable;
5. compare one packet with the ambient Wave;
6. absorb the fixed Wave-lemma loss;
7. validate either a \(V(F)\)-charge or an \(R(F)\)-charge; or
8. reproduce the baseline-plus-response assembly used in KKL's native
   small-breaking proof.

The strongest direct consequence of (1.1) is the
**dominant-packet theorem** in Section 5.  It yields terminality only
when one response packet already carries strictly more than one half
of the ambient width, with enough additional margin to absorb \(C_b\).
That is not the response clause required for a residual of an
arbitrary fixed positive ambient fraction.

The stronger **ambient assembly theorem** in Section 6 does close the
formal response implication, but it has an additional analytic
hypothesis: a width-faithful baseline-and-output assembly certificate.
This is not contained in any of the four nodes in (1.1).  It is the
exact missing bridge between packet response and a KKL terminal Wave.

Accordingly:

- `KKL_STATIONARY_EXACT_OCCURRENCE_SERIES_CONDUCTANCE` remains proved;
- `KKL_STATIONARY_CONDITIONAL_PAIRED_WAVE_RESPONSE_ALGEBRA` remains
  proved under its recorded uniform-constant hypothesis;
- `KKL_STATIONARY_TYPED_PAIRED_WAVE_REALIZATION` remains open;
- `KKL_WAVE_PUSHFORWARD_UNIFORM_PACKET_CONSTANT` remains open;
- `KKL_STATIONARY_BL0_UNIFORM_SURVIVOR_RESPONSE` remains open;
- the native stationary repair remains open; and
- VAAPC-I, UPTCR, and MLC remain open.

This note is a dependency and sufficiency audit.  It proves conditional
closure lemmas and gives abstract countermodels to overstrong logical
implications.  It does not claim that any countermodel is realized by
a quadratic polynomial.

## 2. Locked evidence and source boundary

The audited response note is

```text
kkl_stationary_bl0_survivor_analysis.md
SHA-256 5F94E965B612B710DF24B643ACDFB79FC3FC216BE0127FFA4D9C4176CB544C48
```

The ledger snapshot read in this audit is

```text
proof_obligations.json
SHA-256 D8003A5D1BC288C90CBF7050001802A7DC403E602A344A7D8B11BF7F068D0ABF
```

The KKL source is

```text
.tmp_wave_audit/waves-with-Misha.tex
SHA-256 AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5
```

The KL06 extremal-width appendix is

```text
.tmp_kl06_source/appendix.tex
SHA-256 EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3
```

The exact source clauses relevant to this audit are:

- KL06 appendix lines 39--68: Series and Parallel Laws;
- KL06 appendix lines 72--88: holomorphic transformation rule;
- KKL lines 1145--1160: ambient Wave, controllability, and terminality;
- KKL lines 1397--1416: pushing controllability;
- KKL lines 1423--1492: the native baseline-plus-breaking assembly;
- KKL lines 1534--1623: the stationary \(BL_0\)-ending argument,
  including the unsupported line-1603 step;
- KKL lines 2065--2078: covering pushforward and degree loss;
- KKL lines 2080--2097: immersion restriction and marking filter; and
- KKL lines 2147--2152: the stated Wave pushforward estimate.

The source distinctions used below are:

1. KKL terminality is ambient.  For an ambient Wave \(A\), the wider
   alternative requires a uniformly controllable Wave \(T\) with
   \[
     \mathcal W(T)>(1+\delta)\mathcal W(A).
   \tag{2.1}
   \]
2. KKL's Wave lemma supplies one Wave inside a pushforward with an
   additive \(O(1+\log d)\) loss.  It does not state an additive law
   for outputs produced from different source packets.
3. KKL's pushing-controllability lemma applies when the produced Wave
   lies in \(F_*^h A_*\) and \(A_*^{h\text{-nbr}}\) has a supplied
   controllability bound.  It does not say that every Wave produced
   from an arbitrary restriction packet is uniformly controllable.
4. In the native small-breaking proof, KKL do not use a packet gain in
   isolation.  At lines 1477--1492 they join the retained nonbreaking
   family and the response families into one Wave and only then push
   that assembled Wave forward.

The fourth point is the structural datum absent from (1.1).

## 3. Typed setup for a full survivor ledger

Fix an ambient KKL Wave \(A\) and put

\[
 a:=\mathcal W(A),\qquad
 V:=V(F),\qquad
 R:=R(F),
\tag{3.1}
\]

with \(0<a<\infty\).

Let \(\mathscr E\subset A\) be the complete nonshort,
ambient-singleton, \(BL_0\)-ending survivor residual after native
ambient-break and ambient-short leaves have been returned to their
existing buckets.

### Definition 3.1 (full charged/response ledger)

A full charged/response ledger for \(\mathscr E\) consists of a
modulus-measurable partition

\[
 \mathscr E
 =
 Z\sqcup E_V\sqcup E_R
 \sqcup\bigsqcup_{q\in Q}S_q
 \quad\pmod{\mathcal W=0},
\tag{3.2}
\]

with all of the following clauses.

1. **Modulus-null remainder.**
   \[
     \mathcal W(Z)=0.
   \tag{3.3}
   \]
   Nullity for an auxiliary transverse measure is insufficient unless
   that measure is proved to compute the proof-used extremal width.
2. **First-horizon uniqueness.**  Every physical target leaf occurs at
   exactly one first horizon and in exactly one of the four classes in
   (3.2), modulo a proved zero-width family.
3. **Borel/native typing.**  Every class is a Borel sublamination in the
   same native target surface and is measured by the same proof-used
   width.  Widths computed in source surfaces are transported by an
   explicitly stated domination or pushforward inequality.
4. **Packet cardinality or error summability.**  Either
   \[
      |Q|\le q_b<\infty
   \tag{3.4}
   \]
   with \(q_b\) depending only on the fixed parabolic bound \(b\), or
   every per-packet additive loss is accompanied by a proved summable
   error ledger.  Merely saying that every individual block has
   finitely many labels does not prove (3.4).
5. **Exact response packets.**  Every \(S_q\) has the actual full-width,
   untrimmed, paired source-Wave realization required by
   `KKL_STATIONARY_TYPED_PAIRED_WAVE_REALIZATION`.
6. **No input duplication.**  The target-to-source occurrence map is
   injective modulo width zero, or a proved multiplicity correction is
   inserted.  Different sheet or horizon tags do not by themselves
   identify different physical target leaves.
7. **Valid charge bounds.**  There are block-uniform constants
   \(v_b,r_b<\infty\) such that
   \[
   \mathcal W(E_V)\le v_b(V+1),
   \qquad
   \mathcal W(E_R)\le r_b(R+1).
   \tag{3.5}
   \]
   Each inequality must come from the geometric packet specified in
   Section 8; a label `vertical' or `small-Julia incident' is not a
   proof.

Write

\[
 s_q:=\mathcal W(S_q),
\qquad
 s:=\sum_{q\in Q}s_q,
\qquad
 e_{\rm ch}:=\mathcal W(E_V)+\mathcal W(E_R).
\tag{3.6}
\]

By the Parallel Law and (3.2),

\[
 \mathcal W(\mathscr E)
 \le e_{\rm ch}+s.
\tag{3.7}
\]

If

\[
 E_{\rm resp}:=\bigsqcup_{q\in Q}S_q,
\tag{3.8}
\]

then

\[
 \mathcal W(E_{\rm resp})\le s.
\tag{3.9}
\]

Neither (3.7) nor (3.9) is an equality in general.  General extremal
width is subadditive, not a transverse measure on arbitrary
curve-family decompositions.

### Definition 3.2 (packet output certificate)

For every \(q\in Q\), a packet output certificate consists of:

1. the two KKL Wave-lemma outputs \(C_q^-,C_q^+\);
2. a selected response Wave \(D_q\) satisfying
   \[
     \mathcal W(D_q)
     \ge
     \max\{\mathcal W(C_q^-),\mathcal W(C_q^+)\};
   \tag{3.10}
   \]
3. one of these three constructions of \(D_q\):
   - \(D_q\) is a width-maximizing member of
     \(\{C_q^-,C_q^+\}\);
   - both outputs lie in a certified common Wave \(D_q\); or
   - another declared Wave contains a maximizing output; and
4. if packet-local terminality will be invoked, an
   \(\eta_b\)-controllability certificate for this particular
   width-carrying \(D_q\), not merely for the other output.

Under the exact Series theorem, the typed packet realization, and the
uniform Wave constant, the conditional response algebra gives

\[
 \boxed{
 \mathcal W(D_q)\ge2s_q-C_b.}
\tag{3.11}
\]

Within one packet, common-output containment is enough for (3.11).
Across several packets, common containment is **not** enough to add the
right sides of (3.11).

## 4. Exact consequences of the proposed chain

### Proposition 4.1 (packet-local response only)

Grant the two open inputs
`KKL_STATIONARY_TYPED_PAIRED_WAVE_REALIZATION` and
`KKL_WAVE_PUSHFORWARD_UNIFORM_PACKET_CONSTANT`.  Then every packet in
the resulting realization has an output certificate satisfying
(3.11), provided the selected output satisfies Definition 3.2(1)--(3).

#### Proof

For one packet, exact occurrence conductance gives

\[
 s_q
 \le
 \mathcal W(B_q^-)\oplus\mathcal W(B_q^+).
\tag{4.1}
\]

The uniform KKL Wave estimate gives

\[
 \mathcal W(B_q^\pm)
 \le
 \mathcal W(C_q^\pm)+C_b.
\tag{4.2}
\]

If

\[
 M_q=
 \max\{\mathcal W(C_q^-),\mathcal W(C_q^+)\},
\tag{4.3}
\]

then both source widths in (4.2) are at most \(M_q+C_b\), so

\[
 s_q
 \le
 (M_q+C_b)\oplus(M_q+C_b)
 =
 \frac{M_q+C_b}{2}.
\tag{4.4}
\]

Thus \(M_q\ge2s_q-C_b\).  Equation (3.10) proves (3.11).
\(\square\)

No line of this proof contains \(\mathcal W(A)\), widths of other
packets, charge widths, or a controllability bound.  None of those
quantities can appear in the conclusion without another premise.

### Proposition 4.2 (finite packet dilution)

Suppose \(Q\) is finite, with \(q=|Q|\), and suppose

\[
 \mathcal W(E_{\rm resp})>\epsilon a.
\tag{4.5}
\]

Then the full response ledger and (3.11) imply only

\[
 \max_{q\in Q}\mathcal W(D_q)
 >
 \frac{2\epsilon}{q}a-C_b.
\tag{4.6}
\]

#### Proof

By (3.9),

\[
 s=\sum_qs_q\ge\mathcal W(E_{\rm resp})>\epsilon a.
\tag{4.7}
\]

Hence some \(q_*\) has

\[
 s_{q_*}\ge\frac{s}{q}>\frac{\epsilon}{q}a.
\tag{4.8}
\]

Apply (3.11) to \(q_*\). \(\square\)

Even with \(C_b=0\), (4.6) can exceed \(a\) only when

\[
 \frac{2\epsilon}{q}>1.
\tag{4.9}
\]

Because \(E_{\rm resp}\subset A\), monotonicity gives
\(\epsilon<1\) in every nonvacuous response test.  Therefore:

- for \(q\ge2\), finite-packet pigeonholing alone can never produce a
  strict wider-Wave conclusion uniformly over \(\epsilon<1\);
- for \(q=1\), it requires \(\epsilon>1/2\); and
- the QSDRA trigger for an arbitrary prescribed
  \(0<\epsilon<1\) cannot follow from packet response without an
  ambient assembly theorem.

This is a coefficient obstruction, not a technical measurability
issue.

## 5. Strongest theorem available without ambient assembly

### Theorem 5.1 (dominant-packet terminality)

Assume a packet \(S_*\subset A\) has a response Wave \(D_*\) satisfying

\[
 \mathcal W(D_*)\ge2\mathcal W(S_*)-C_b
\tag{5.1}
\]

and \(D_*\) is \(\eta_b\)-controllable.  Suppose

\[
 \mathcal W(S_*)\ge\theta a
\quad\text{for some}\quad
\theta>\frac12.
\tag{5.2}
\]

For every

\[
 0<\delta<\min\{1,2\theta-1\},
\tag{5.3}
\]

if

\[
 a>\frac{C_b}{2\theta-1-\delta},
\tag{5.4}
\]

then \(A\) is \((\delta,\eta_b)\)-terminal through the wider-Wave
alternative.

#### Proof

Equations (5.1)--(5.2) give

\[
 \mathcal W(D_*)
 \ge2\theta a-C_b.
\tag{5.5}
\]

Condition (5.4) is equivalent to

\[
 C_b<(2\theta-1-\delta)a.
\tag{5.6}
\]

Substitute (5.6) into (5.5):

\[
\begin{aligned}
 \mathcal W(D_*)
 &>2\theta a-(2\theta-1-\delta)a\\
 &=(1+\delta)a.
\end{aligned}
\tag{5.7}
\]

The supplied \(\eta_b\)-controllability and the KKL definition of
terminality prove the assertion. \(\square\)

Theorem 5.1 is the strongest ambient conclusion obtainable from one
packet and monotonicity alone.  It is useful if an independent
geometric theorem produces a dominant packet.  Full residual coverage,
a finite packet bound, and common containment of all outputs do not
produce (5.2).

## 6. The missing closure theorem: baseline and output assembly

The native KKL small-breaking proof retains a baseline family and joins
it to the response families before pushforward.  The following theorem
isolates exactly the inequality that an analogous stationary
construction must prove.

### Definition 6.1 (ambient conductance assembly certificate)

Let \(Q\) be finite.  An ambient conductance assembly certificate of
efficiency \(1/2<\alpha\le1\) consists of:

1. a retained input family \(B_{\rm in}\subset A\), with
   \[
     b_{\rm in}:=\mathcal W(B_{\rm in});
   \tag{6.1}
   \]
2. a charged or discarded input family \(E_{\rm ch}\subset A\), with
   width \(e_{\rm ch}\), such that modulus subadditivity gives the
   width-faithful ambient budget
   \[
     a\le
     b_{\rm in}+\sum_{q\in Q}s_q+e_{\rm ch};
   \tag{6.2}
   \]
3. a transported baseline Wave \(B_0\), with
   \[
     \mathcal W(B_0)\ge b_{\rm in}-E_{\rm base};
   \tag{6.3}
   \]
4. selected packet outputs \(D_q\) satisfying (3.11);
5. one actual output Wave \(T\) satisfying
   \[
     \mathcal W(T)
     \ge
     \mathcal W(B_0)
     +\alpha\sum_{q\in Q}\mathcal W(D_q)
     -E_{\rm out};
   \tag{6.4}
   \]
6. an \(\eta_b\)-controllability certificate for \(T\); and
7. uniform bounds on \(E_{\rm base}\), \(E_{\rm out}\), \(|Q|\), and
   every constant entering \(e_{\rm ch}\), independent of satellite
   period, rotation denominator, raw marking size, selector history,
   and the individual block.

Equation (6.4) is the essential new analytic assertion.  Sufficient
ways to prove it include:

- realizing \(B_0,D_q\) in pairwise disjoint open output domains, using
  equality in the KL06 Parallel Law, and proving their union lies in
  \(T\);
- constructing one common measured foliation or valid WAD in which
  their weights occupy disjoint coordinates, and then applying a
  source-licensed realization theorem which gives the lower bound
  (6.4) for its carrier Wave \(T\); or
- proving (6.4) directly by a source-specific quasi-additivity or
  domination theorem.

The following do **not** imply (6.4):

- all \(D_q\) being subsets of \(T\);
- pairwise different labels for the \(D_q\);
- pairwise different source sheets;
- pointwise noncollision without a transverse-width theorem; or
- the upper Parallel-Law bound
  \(\mathcal W(\bigcup_qD_q)\le\sum_q\mathcal W(D_q)\).

The exact case is \(\alpha=1\).  A smaller \(\alpha\) is permitted only
after proving (6.4) with that coefficient.  A slogan such as
`multiplicity at most \(\mu\)' does not automatically prove
\(\alpha=1/\mu\); the corresponding modulus inequality must itself be
established.

### Theorem 6.2 (ambient assembled survivor response)

Assume:

1. a full charged/response ledger;
2. the packet inequalities (3.11);
3. an ambient conductance assembly certificate with
   \(1/2<\alpha\le1\); and
4. for some \(0<\epsilon<1\),
   \[
      \mathcal W(E_{\rm resp})>\epsilon a.
   \tag{6.5}
   \]

Put

\[
 E_{\rm tot}
 :=
 e_{\rm ch}
 +E_{\rm base}
 +E_{\rm out}
 +\alpha |Q|C_b.
\tag{6.6}
\]

For every

\[
 0<\delta<
 \min\{1,(2\alpha-1)\epsilon\},
\tag{6.7}
\]

if

\[
 E_{\rm tot}
 \le
 \bigl((2\alpha-1)\epsilon-\delta\bigr)a,
\tag{6.8}
\]

then \(A\) is \((\delta,\eta_b)\)-terminal through the wider-Wave
alternative.

#### Proof

Let \(s=\sum_qs_q\).  From (6.2),

\[
 b_{\rm in}\ge a-s-e_{\rm ch}.
\tag{6.9}
\]

Then (6.3) gives

\[
 \mathcal W(B_0)
 \ge
 a-s-e_{\rm ch}-E_{\rm base}.
\tag{6.10}
\]

Sum the packet inequalities:

\[
 \sum_q\mathcal W(D_q)
 \ge
 2s-|Q|C_b.
\tag{6.11}
\]

Substitute (6.10)--(6.11) into (6.4):

\[
\begin{aligned}
 \mathcal W(T)
 &\ge
 a-s-e_{\rm ch}-E_{\rm base}
 +\alpha(2s-|Q|C_b)-E_{\rm out}\\
 &=a+(2\alpha-1)s-E_{\rm tot}.
\end{aligned}
\tag{6.12}
\]

Equations (3.9) and (6.5) imply

\[
 s\ge\mathcal W(E_{\rm resp})>\epsilon a.
\tag{6.13}
\]

Using (6.8), (6.12), and (6.13),

\[
\begin{aligned}
 \mathcal W(T)
 &>
 a+(2\alpha-1)\epsilon a-E_{\rm tot}\\
 &\ge(1+\delta)a.
\end{aligned}
\tag{6.14}
\]

The supplied \(\eta_b\)-controllability of \(T\) now gives KKL
terminality. \(\square\)

### Corollary 6.3 (exact assembly)

When \(\alpha=1\), Theorem 6.2 requires

\[
 e_{\rm ch}+E_{\rm base}+E_{\rm out}+|Q|C_b
 \le(\epsilon-\delta)a.
\tag{6.15}
\]

Thus a response residual of any prescribed positive ambient fraction
\(\epsilon\) can force terminality, provided:

1. the baseline is retained with coefficient one;
2. packet outputs are assembled with coefficient one;
3. the total additive loss is uniformly bounded and absorbed at the
   ambient scale; and
4. the assembled Wave, not merely each isolated output, is uniformly
   controllable.

### Corollary 6.4 (why overlap two is already critical)

If the best proved assembly coefficient is \(\alpha=1/2\), then the
response term in (6.12) has coefficient

\[
 2\alpha-1=0.
\tag{6.16}
\]

No amount of ambient width can turn the packet factor two into a
strict gain through this assembly inequality.  An output
double-counting or overlap loss of two consumes the entire paired-Wave
gain.  Therefore a bounded-overlap theorem is useful here only if its
actual conductance efficiency is strictly greater than \(1/2\), or if
the source packet has more than two independent series branches.

## 7. Controllability and selection hypotheses

The phrase `some output is controllable' is too weak.  The response
lower bound is attached to a width-maximizing output.

For each packet, one of the following is sufficient:

1. both \(C_q^-\) and \(C_q^+\) are \(\eta_b\)-controllable;
2. a specifically selected maximizing output is
   \(\eta_b\)-controllable; or
3. both outputs lie in a common \(\eta_b\)-controllable Wave \(D_q\).

For Theorem 6.2, packetwise controllability is still insufficient.
The final assembled Wave \(T\) must itself be
\(\eta_b\)-controllable.

KKL's pushing-controllability lemma can supply this only after the
following actual premises are verified:

\[
\begin{aligned}
 \mathsf{PC1}_q &:\
  D_q\subset F_*^{h(q)}A_{*,q};\\
 \mathsf{PC2}_q &:\
  A_{*,q}^{h(q)\text{-nbr}}
  \text{ is }k_0(b)\text{-controllable};\\
 \mathsf{PC3}_q &:\
  h(q)\le b+2;\\
 \mathsf{PC4}_q &:\
  \text{the complete fine/coarse marking and Wave typing survive};\\
 \mathsf{PC5} &:\
  \max_{h\le b+2}\eta(h,k_0(b))<\infty.
\end{aligned}
\tag{7.1}
\]

An input bound depending on the original arbitrary controllability
parameter \(k\) does not give the \(b\)-only response required by the
ledger.  The source-facing route identified elsewhere in the project
is to first pass to the family whose relevant unbreakable part is
\(12b\)-controllable, or to prove a new uniform theorem.

For a finite two-output packet, a scalar maximum is attained.  For an
unbounded or countable packet atlas, a global supremum need not be
attained, and the repeated additive errors need not be summable.
Thus a bounded packet atlas or an explicit approximate-maximizer and
summable-error theorem is also part of the response certificate.

## 8. Exact \(V(F)\)- and \(R(F)\)-charge requirements

### 8.1 Valid \(V(F)\)-charge

The conditional vertical theorem already in the project proves

\[
 \sum_{h=1}^{b+2}
 \mathcal W(E_{V,h})
 \le
 (2^{b+4}-4)(V+1)
\tag{8.1}
\]

only after every \(E_{V,h}\) has a proper vertical exit packet.  That
packet requires:

1. one Borel, single-valued target-to-source restriction choice;
2. a complete proper source path from the pulled-tree ideal boundary
   to the outer ideal boundary;
3. survival of the fine marking and coarse subordinate filter;
4. a genuine source lamination in its native transverse width;
5. no duplicate physical target mass;
6. a covering extension on the whole relevant ending locus;
7. a degree bound \(D_h\le2^h\) on that locus; and
8. an actual pushed family connecting the two boundary components, so
   its width is at most \(V\).

Without these clauses, `vertical' is only a route label.

### 8.2 Valid \(R(F)\)-charge

For one \(R\)-packet, the strongest audited estimate is

\[
 \mathcal W(E_{R,h})
 \le2D_h(R+1)
 \le2^{h+1}(R+1),
\tag{8.2}
\]

conditional on:

1. a proper lamination in
   \(\mathcal U^h\setminus\mathcal K^h\);
2. actual incidence from one specified pulled small-Julia component
   to its prescribed complement;
3. a selected retained source leaf for every target leaf;
4. zero width for every omitted target family;
5. fine/coarse marking survival;
6. a whole-ending-multi-interval degree bound;
7. an extracted pushed lamination with exactly the declared component
   incidence;
8. an independently licensed comparison
   \[
      \mathcal W(C_h^{\rm ren})\le2R;
   \tag{8.3}
   \]
9. no duplicate transverse mass; and
10. a packet-count bound depending only on \(b\), or a summable charge
    ledger.

In the locked local source, the final stationary alignment is used
before (8.3), and the checked passage does not independently prove
(8.3).  Thus the \(R\)-charge for the present survivor remains
conditional.  It cannot be silently inserted into (3.5).

### 8.3 The charges play different global roles

A large \(V\) gives the first KKL terminal alternative directly:

\[
 V>\delta_v a.
\tag{8.4}
\]

No analogous clause turns a large \(R\) into terminality.  When (8.4)
fails,

\[
 v_b(V+1)
 \le
 v_b\delta_v a+v_b.
\tag{8.5}
\]

The \(R\)-charge and all fixed constants require an HTND or explicit
absolute-scale hypothesis.  For example, if

\[
 E_{\rm base}+E_{\rm out}+\alpha q_bC_b\le e_b
\tag{8.6}
\]

uniformly, then

\[
 E_{\rm tot}
 \le
 v_b\delta_v a
 +(v_b+r_b)(R+1)+e_b.
\tag{8.7}
\]

Given a desired margin

\[
 \zeta=(2\alpha-1)\epsilon-\delta>0,
\tag{8.8}
\]

it is sufficient to choose

\[
 0<\delta_v\le
 \min\left\{\frac12,\frac{\zeta}{2v_b}\right\}
 \quad (v_b>0)
\tag{8.9}
\]

and require

\[
 a\ge
 \frac{2\bigl((v_b+r_b)(R+1)+e_b\bigr)}{\zeta}.
\tag{8.10}
\]

Then \(E_{\rm tot}\le\zeta a\), so Theorem 6.2 applies.  When
\(v_b=0\), condition (8.9) is unnecessary.

There is no audited universal comparison

\[
 R\le C_b(V+1).
\tag{8.11}
\]

Therefore a proof that ends with an \(R\)-term must either retain that
term or invoke the explicit absolute scale (8.10).

## 9. Explicit abstract countermodels

These models use only the extremal-width laws imported in the proposed
chain.  They show that the missing hypotheses are logically
independent of the packet inequality.  They are not asserted to be
quadratic dynamical systems.

For \(w>0\), let

\[
 Q(w)=(0,1)\times(0,w)
\tag{9.1}
\]

and let \(\Gamma(w)\) be the family of paths joining its two vertical
sides.  Then

\[
 \mathcal W(\Gamma(w))=w.
\tag{9.2}
\]

Cutting \(Q(w)\) at \(x=1/2\) gives two serial crossing families, each
of width \(2w\), and

\[
 (2w)\oplus(2w)=w.
\tag{9.3}
\]

Placing rectangles in disjoint open sets realizes exact addition of
their widths by the KL06 Parallel Law.

### Countermodel 9.1 (full coverage, no ambient response)

Let the ambient family \(A\) be the horizontal foliation of a unit
rectangle split into \(q\ge2\) parallel horizontal bands.  Let \(S_j\)
be the family in band \(j\), with

\[
 \mathcal W(A)=1,
 \qquad
 \mathcal W(S_j)=\frac1q,
 \qquad
 A=\bigsqcup_{j=1}^qS_j.
\tag{9.4}
\]

For each packet, use its two half-rectangles as the exact series
portions and take conformal output copies:

\[
 \mathcal W(C_j^-)
 =
 \mathcal W(C_j^+)
 =
 \frac2q,
 \qquad C_b=0.
\tag{9.5}
\]

Every packet attains equality in (1.2).  The packets cover the full
ambient family with no duplicate input width, and every output may be
declared uniformly controllable in this abstract model.  Place the
outputs in incompatible marked Wave classes and do not add an
unlicensed union-Wave operation.  Nevertheless:

- for \(q=2\), every output has width exactly \(1\), not strictly more
  than \(A\);
- for \(q\ge3\), every output has width strictly less than \(1\).

Thus full coverage, exact pairing, zero Wave error, and output
controllability do not imply ambient terminality.

### Countermodel 9.2 (common containment does not add outputs)

Use Countermodel 9.1 with \(q=2\).  Map every selected source output
to the same target family

\[
 T=\Gamma(1).
\tag{9.6}
\]

Then all packet outputs lie in the same controllable Wave \(T\), and
each packet response gives width \(1\).  But

\[
 \mathcal W(T)=1
\ne
 1+1.
\tag{9.7}
\]

Common containment proves only

\[
 \mathcal W(T)\ge
 \max_j\mathcal W(C_j),
\tag{9.8}
\]

not a sum.  This is the abstract form of output sheet collision or
repeated use of one output conductance coordinate.

### Countermodel 9.3 (a controllable nonmaximizer is useless)

Take one packet with two serial branch widths

\[
 x=12,\qquad y=\frac45.
\tag{9.9}
\]

Their harmonic sum is

\[
 x\oplus y
 =
 \left(\frac1{12}+\frac54\right)^{-1}
 =
 \frac34.
\tag{9.10}
\]

Let \(A\) have width \(1\), let \(S\) have width \(3/4\), take
\(C_b=0\), and take outputs of widths \(12\) and \(4/5\).
The packet inequality is exact.  Give the width-\(4/5\) output the
required uniform \(\eta_b\)-controllability certificate and give the
width-\(12\) output no such certificate.  Then `some output is
controllable' holds, but no certified controllable output is wider
than \(A\).  Controllability must attach to the width-maximizing output
or to a common Wave containing it.

### Countermodel 9.4 (missing ambient fraction)

Let \(a=1\), let one exact packet have width

\[
 s=\frac25,
\tag{9.11}
\]

and let its two source and output branches each have width \(4/5\),
with \(C_b=0\).  Then

\[
 \max\mathcal W(C^\pm)=\frac45<1.
\tag{9.12}
\]

The remaining ambient width \(3/5\) is retained but not assembled with
the output.  A factor-two packet response is not an ambient response
when the packet has at most half of the ambient width.

### Countermodel 9.5 (fixed additive loss needs absolute scale)

Let

\[
 a=1,\qquad s=\frac35,\qquad C_b=\frac3{10}.
\tag{9.13}
\]

Take two source branches of width \(6/5\), whose harmonic sum is
\(3/5\), and two output branches of width \(9/10\).  Then

\[
 \frac65=\frac9{10}+\frac3{10}
\tag{9.14}
\]

on both branches, and

\[
 2s-C_b=\frac9{10}.
\tag{9.15}
\]

The packet occupies more than half of \(A\), all inequalities are
sharp, and the output may be controllable, yet its width is below
\(a\).  The missing condition is exactly the threshold in Theorem 5.1.

### Countermodel 9.6 (duplicate packet names create phantom gain)

Let one physical packet \(S\) have width \(1/2\) and one physical
response output \(D\) have width \(1\).  Enter the same physical packet
twice in a labeled ledger:

\[
 S_1=S_2=S,
\qquad
 D_1=D_2=D.
\tag{9.16}
\]

Each labeled row satisfies the factor-two estimate.  Summing rows
would claim input width \(1\) and output width \(2\), although the
physical input and output widths are \(1/2\) and \(1\).  A first-horizon
label is not a multiplicity theorem.  Both the input occurrence map
and the output conductance coordinates must be audited before any sum
is used.

### Countermodel 9.7 (a valid numerical charge is not terminality)

Let \(A=E_R=\Gamma(1)\), set \(R=0\), and suppose only the numerical
charge

\[
 \mathcal W(E_R)\le R+1
\tag{9.17}
\]

is known.  The whole residual is covered by a charge, but no wider Wave
and no positive vertical fraction follows.  This is not a contradiction:
the charge is an error term, and at this scale it is as large as the
ambient family.  An absolute-scale hypothesis is required to absorb
it.

### Countermodel 9.8 (\(R\)-charge cannot be renamed \(V\)-charge)

For \(M>0\), set

\[
 \mathcal W(E_R)=R=M,\qquad V=0.
\tag{9.18}
\]

Then \(\mathcal W(E_R)\le R+1\), while

\[
 \frac{\mathcal W(E_R)}{V+1}=M\longrightarrow\infty.
\tag{9.19}
\]

The imported width laws impose no comparison between the independent
scalars \(R\) and \(V\).

### Countermodel 9.9 (auxiliary nullity is not modulus nullity)

Let \(Z=\Gamma(1)\), so \(\mathcal W(Z)=1\).  Equip its parameter set
with an unrelated zero measure \(\nu\).  Then \(\nu(Z)=0\), but

\[
 \mathcal W(Z)=1.
\tag{9.20}
\]

This deliberately minimal model records the logical point: a null set
for a supplied selector or auxiliary transverse measure can be
discarded only after that measure is proved to represent the native
extremal-width ledger.

## 10. Exact additional hypotheses needed for closure

The four-node chain in (1.1) must be supplemented by the following
certificates.

| certificate | exact content | why it is not already supplied |
|---|---|---|
| `FULL` | (3.2) exhausts every physical survivor leaf modulo proved extremal-width zero | typed realization may construct only the packets on which its start and marking survive |
| `FIRST/INJ` | one first horizon, one packet, and one physical target occurrence per leaf | Borel labels and sheet tags do not prevent duplicate mass |
| `COUNT` | \(|Q|\le q_b\), or a summable per-packet error ledger | one uniform \(C_b\) still accumulates once per Wave-lemma call |
| `PACKET` | exact untrimmed paired source Waves, whole-ending-set degrees, marking survival, and image identities | this is the open typed realization |
| `UW` | one Wave-error constant with documented uniform dependence | this is the open uniform-constant node |
| `MAX-CTRL` | the output carrying the lower bound is \(\eta_b\)-controllable | a controllable nonmaximizer does not yield terminality |
| `PUSH-CTRL` | the precise premises (7.1) if KKL pushing-controllability is used | packet typing alone does not place the output in the lemma's scope |
| `AMBIENT-FRAC` | either one packet has \(\theta>1/2\) of \(A\), or the full responsive residual has a fixed positive fraction and `ASSEMBLY` holds | packet width is not ambient width |
| `ASSEMBLY` | (6.2)--(6.4), with \(\alpha>1/2\), in one genuine output Wave | common containment gives a maximum, not additive conductance |
| `FINAL-CTRL` | the assembled Wave \(T\) has a \(b\)-only controllability bound | unions of controllable Waves need not form one controllable Wave |
| `V-CHARGE` | the complete proper vertical packet and the bound (8.1) | a vertical route label is not a proper crossing family |
| `R-CHARGE` | actual component incidence, whole-ending degree, (8.3), and packet-count control | the current \(R\)-charge remains doubly conditional |
| `SCALE` | (5.4) for dominant packets or (6.8)/(8.10) for assembly | fixed and \(R(F)\)-dependent errors do not vanish by rescaling labels |
| `QSDRA-LINK` | the resulting response is inserted into the native disjoint estimate without reusing \(B_A\) or charged leaves | a packet theorem is not the global stationary induction |

The source-safe implication is therefore

\[
\begin{split}
&\texttt{SERIES}
\wedge\texttt{PACKET}
\wedge\texttt{UW}
\wedge\texttt{FULL/FIRST/INJ/COUNT}\\
&\wedge\texttt{V-CHARGE/R-CHARGE}
\wedge\texttt{ASSEMBLY}
\wedge\texttt{FINAL-CTRL}
\wedge\texttt{SCALE}\\
&\Longrightarrow
\text{the response implication of Theorem 6.2}.
\end{split}
\tag{10.1}
\]

Only after `QSDRA-LINK` is proved does (10.1) supply the
`KKL_STATIONARY_BL0_UNIFORM_SURVIVOR_RESPONSE` needed by the stationary
repair.

If `ASSEMBLY` is replaced by the dominant-packet hypothesis, the
conclusion is only Theorem 5.1.  That restricted conclusion does not
imply the arbitrary-\(\epsilon\) QSDRA response.

## 11. First-failure and replacement-state certificate

A failed closure attempt must stop at the first applicable item below
and record the named data.

1. **Coverage failure:** the first physical survivor leaf absent from
   (3.2), with its horizon, access, sheet, marking, and full itinerary.
2. **Duplicate input:** the first pair of ledger rows representing the
   same physical target occurrence, with both first-horizon tags.
3. **Packet failure:** the first missing typed start, improper end,
   incomplete untrimmed segment, marking loss, non-Wave source family,
   or whole-ending-set degree failure.
4. **Wave-error failure:** the first branch for which the source proof
   does not provide the claimed common \(c_{\rm W}\), including every
   parameter on which the hidden constant depends.
5. **Output-selection failure:** the two output widths and the
   controllability status of each, identifying whether the maximizing
   one is uncontrolled.
6. **Output-collision failure:** the first two response outputs assigned
   to the same physical output conductance coordinate, including their
   deck, horizon, and WAD support data.
7. **Assembly failure:** the first baseline or response family that
   cannot be inserted into one output Wave satisfying (6.4), and the
   exact lost coefficient \(\alpha\).
8. **Final controllability failure:** the first assembled Wave whose
   number of localized pieces depends on raw period, access count, or
   selector history.
9. **Charge failure:** the first \(V\)- or \(R\)-labeled leaf for which
   the proper path, component incidence, ending-set degree, or width
   comparison is absent.
10. **Scale failure:** the explicit values of
    \(a,V,R,C_b,|Q|,E_{\rm base},E_{\rm out}\) for which the right side
    of (6.8) is negative or too small.

A sufficient conservative replacement state is

\[
\begin{split}
\mathfrak S_{\rm resp}=
\bigl(&
\text{physical leaf/first horizon},
\text{typed source pair},
\text{untrimmed target segments},
\text{ending-set degrees},\\
&
\text{two output Wave IDs},
\text{maximizing-output flag},
\text{controllability witness},
\text{output WAD coordinate},\\
&
\text{output multiplicity},
\text{baseline assembly slot},
\text{charge type and proof},
\text{all additive errors}
\bigr).
\end{split}
\tag{11.1}
\]

The output WAD coordinate and baseline assembly slot are new compared
with a purely packet-local record.  They are necessary because the
countermodels in Sections 9.1--9.2 have perfect packet records but fail
globally at output conductance assembly.

## 12. Backward dependency audit

| desired conclusion | immediate quantitative input | status |
|---|---|---|
| exact occurrence Series bound | actual disjoint untrimmed segments and exact holomorphic images | proved in the audited response note |
| packet factor-two response | Series bound, actual source Waves, whole-ending degrees, uniform Wave constant | proved conditional; typed realization and constant remain open |
| packet-local terminality | packet response, controllable maximizing/common output, \(>1/2\) ambient fraction, absolute threshold | proved here as Theorem 5.1 |
| residual response for arbitrary fixed positive fraction | packet responses, full ledger, baseline preservation, output conductance assembly with \(\alpha>1/2\), final controllability, scale | proved here as Theorem 6.2 conditional on the new analytic certificate |
| uniform \(V\)-charge | actual proper vertical packets at all horizons | conditional analytic construction remains open |
| uniform \(R\)-charge | actual component incidence, licensed \(2R\) comparison, bounded packet count | open |
| QSDRA survivor implication | Theorem 6.2 plus native disjoint-estimate insertion | open |
| stationary KKL repair | QSDRA or another complete numerical/response route, plus downstream recheck | open |

No conclusion in this table is used as one of its own hypotheses.

## 13. Final conclusion

The packet algebra is genuine progress: it removes deck noncollision as
a necessary condition for a **single packet's** factor-two width
response.  It does not yet remove the global stationary obstruction.

Within this historical optional route, the proposed constructive target
was sharper than `construct paired Waves':

> Construct the typed paired packets on the complete survivor
> residual **and simultaneously construct a baseline/output WAD
> assembly satisfying (6.2)--(6.4) with
> \(\alpha>1/2\)**.  Prove that the resulting assembled Wave has a
> \(b\)-only controllability bound.  Separately prove every \(V\)- and
> \(R\)-charge and the absolute-scale inequality (6.8).

If the construction cannot achieve \(\alpha>1/2\), the first output
collision or WAD-coordinate reuse is the exact obstruction.  The
replacement invariant must retain output conductance multiplicity and
baseline assembly data; adding more source-side access labels cannot
repair an output-side coefficient loss.
