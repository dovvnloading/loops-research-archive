# Frozen backward audit — KKL stationary relative Wave continuation

Date: 2026-07-26

## 0. Verdict and exact object

```text
AUDIT VERDICT: PASS
```

The audited object is exactly

```text
research/mlc_unified/
kkl_stationary_relative_wave_continuation.md

SHA-256
ADFC7BCD5A73CE7E7ABE12C11C3E2C4D778826B995BF9114C6F8B431EF38094F

Get-Content line count
1860
```

No edit was made to that object during this audit.

The verdict is relative exactly to the analytic import isolated in the
audited manuscript as

```text
DL_RELATIVE_DISCARD_FAMILY_BOUND.
```

That import says that the actual family discarded in the proof at DL
2830--2841 has width \(O(\log m)\).  For the degree-two stationary
cover this is one universal constant.  The audit does not infer that
bound from DL's displayed retained-width inequality.  No later step
uses any stronger property of the DL discard.

The two independently proved measurable inputs used by the frozen
file are:

| input | exact accepted snapshot |
|---|---|
| `BOREL_WIDTH_ENVELOPE_PRUNING` | `kkl_stationary_n1_borel_width_envelope_20260726.md`, SHA-256 `9F2ABD1E8DDD0E0E1B4FFC3B55B8DAF3BA64B4BCBE4E9562454A850E5E8422BE` |
| `STANDARD_BOREL_ORDERED_WAVE_REALIZATION` | `kkl_stationary_n1_borel_ordered_wave_realization_20260726.md`, SHA-256 `6F9B4085C914BD74DD5030C67F311334A4B4882594E111FF552429E4FCC9D118` |

The latter has its own frozen backward audit at
`kkl_stationary_n1_bowr_frozen_backward_audit_20260726.md`, SHA-256
`F9A6BA1C1C9875CDCF1DE1506D3540DB21400FDCAC42B7EDCC3CAD9A574FF0F3`.

This verdict concerns Gate N1 only.  It proves no terminal alignment,
Gate N2, VAAPC-I, UPTCR, rigidity, parameter-fiber, or MLC statement.

## 1. Source identity

The four immutable source hashes named in the frozen manuscript were
recomputed and match:

| source | SHA-256 |
|---|---|
| KKL `waves-with-Misha.tex` | `AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5` |
| DL `Feigen.tex` | `EB8C50CC51039A82317CF1951B1E333F23DF100773F8AD0DF0586AC7CD465DDF` |
| KL06 `appendix.tex` | `EA2BE5CC544100D7931C9992E7ED476EBBE4CCE52FAF620BFF357071CB3916F3` |
| KL06 `wad.tex` | `B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580` |

The source clauses used in the proof are inside their published scope:

- KKL 1254--1274 gives the connected pulled interval and
  combinatorial action;
- KKL 1355--1358 and 2161--2162 gives the unique untagged output of an
  unbreakable path;
- KKL 1403--1411 gives the one-step controllability decomposition;
- KKL 1524--1532 gives the away-from-critical Shift bound;
- KKL 1850--1875 gives the exact marking, subordination, Wave, end,
  base, and crest types;
- KKL 2065--2142 gives covering pushforward, filtered immersion
  restriction, domination, and \(F_*=f_*\iota^*\); and
- KKL Proposition A.14 at 2164--2168 is used only on correctly typed
  singleton source/output pairs.

The proof does not invoke the false broad coefficient-one reading of
KKL Lemma A.13.

## 2. Backward dependency map from (9.13)

The final estimate is

\[
 \mathcal W(A_n\setminus A_{n+1})\leq C_b,
 \qquad 0\leq n<N-1,
\tag{9.13}
\]

where

\[
 C_b=
 \max\{c_b^{\rm init},2^{b+1}c_b^{\rm step}\}.
\]

Its complete backward chain is:

| conclusion | immediate input | audit |
|---|---|---|
| (9.13), \(n=0\) | Proposition 8.1, (9.9) | pass |
| (9.13), \(1\leq n<N-1\) | exact saturation (9.5), sequential transfer (2.4), Proposition 7.1 | pass |
| sequential factor \(2^n\) | one degree-two full-lift bound at each of the \(n\) previous transitions | pass |
| \(c_b^{\rm step}\) | metric-envelope source loss plus the critical or noncritical target loss | pass |
| \(c_b^{\rm init}\) | bounded precritical packet plus one ordinary step | pass |
| Borelness of every \(A_n,S_n\) | Theorem 3.1, Corollary 3.2, and full output saturation | pass |

No estimate sums a loss over the number of arc classes or the rotation
denominator \(q\).

## 3. Width transfer

### 3.1 Full-lift identity

Lemma 2.1 proves

\[
 \mathcal W(p^*\Gamma)=d\,\mathcal W(\Gamma)
\]

for a degree-\(d\) unbranched conformal cover.

The upper bound pulls an admissible metric back.  For the reverse
bound, the density

\[
 \rho(y)=d^{-1/2}
 \left(\sum_{r=1}^d
 \sigma(s_r(y))^2|s_r'(y)|^2\right)^{1/2}
\]

is independent of the local ordering of inverse branches.  Minkowski's
integral inequality makes it admissible, and change of variables gives
\(\operatorname{area}(\rho)=d^{-1}\operatorname{area}(\sigma)\).
Both directions and the factor \(d\) are correct.

### 3.2 Sequential relative transfer

For \(D\subset A_n\), put \(D_j=\Phi_j(D)\).  The nesting
\(A_n\subset A_j\) gives \(D_j\subset S_j\).  At transition \(j\):

1. every \(D_j\)-leaf has at least one complete filtered restriction,
   because it is unbreakable;
2. every retained restriction maps to its unique successor in
   \(D_{j+1}\);
3. KKL domination gives
   \(\mathcal W(D_j)\leq\mathcal W(B_j)\); and
4. \(B_j\subset f^*D_{j+1}\), so Lemma 2.1 gives
   \[
   \mathcal W(D_j)\leq2\mathcal W(D_{j+1}).
   \]

Multiplication gives (2.4).  All restriction occurrences are retained
in this comparison; no collision or occurrence selector is hidden in
the factor two.

## 4. DL pruning and the metric envelope

Lemma 2.3 separates the source facts in the required order.

1. DL gives a set-theoretic injective retained subwave
   \(\mathscr B^\sharp_{\rm DL}\).
2. The isolated analytic import gives
   \[
   D_{\rm DL}:=
   \mathscr B\setminus\mathscr B^\sharp_{\rm DL},
   \qquad
   \mathcal W(D_{\rm DL})\leq c_{\rm DL}^{\rm raw}.
   \]
3. The Borel width-envelope theorem gives one Borel leaf set
   \(E_{\rm DL}\supset D_{\rm DL}\) with
   \[
   \mathcal W(E_{\rm DL})\leq c_{\rm DL}^{\rm raw}+1.
   \]
4. The actual retained family is
   \[
   \mathscr B^\sharp=\mathscr B\setminus E_{\rm DL}
   \subset\mathscr B^\sharp_{\rm DL}.
   \]
   Hence the covering remains injective on its geometric union.

The proof never asserts that \(E_{\rm DL}\) is a union of literal DL
span packets or outer buffers.  A leaf removed only by the metric
envelope is allowed.  All later source-loss estimates use only

\[
 \mathcal W(\mathscr B\setminus\mathscr B^\sharp)
 \leq c_{\rm DL}:=c_{\rm DL}^{\rm raw}+1.
\]

For a target subwave \(\mathscr E\), the proof uses only the inclusion

\[
 \mathscr B^\sharp\cap p^{-1}(\mathscr E)
 \subset p^*\mathscr E,
\]

so monotonicity and the degree-two full-lift identity give (2.6).
No common univalent neighborhood and no coefficient-one conformal
identity is assumed.

## 5. Exact target-Wave typing

The source hypothesis \(S\uparrow I\) is leafwise.  It does not imply
that the aggregate crest of \(S\) contains \(I\), so KKL Proposition
A.14 cannot be applied once to the aggregate source.

The frozen proof uses the valid two-part argument.

Fix a retained occurrence \(\beta\) over \(\gamma\).

1. \(S\uparrow I\) makes the singleton \(\{\gamma\}\) a Wave over
   \(I\).
2. Unbreakability and the filtered occurrence definition give
   \(\{f(\beta)\}\subset F_*\{\gamma\}^{\rm nbr}\).
3. Singleton KKL Proposition A.14 makes \(\{f(\beta)\}\) a Wave over
   \(F_*I\).
4. Its connected singleton base is contained in the ideal-boundary
   component \(C\) containing \(F_*I\).  Thus \(f(\beta)\) is
   subordinate to \(C\).
5. KKL 1853--1856 permits \(C\) itself as a multi-interval.  Since the
   injective image is already a proper Borel lamination and all its
   leaves are subordinate to \(C\), KKL 1874 makes the aggregate image
   a Wave subordinate to \(C\).

Singleton A.14 separately gives the leafwise direction

\[
 f(\mathscr B^\sharp)\uparrow F_*I.
\]

The proof never concludes that the aggregate target crest contains
\(F_*I\), and it never transports an aggregate source base through the
covering.

## 6. Lemmas 4.1--4.3

### 6.1 KKL-to-DL restriction

For each source leaf \(\gamma\), its complete filtered restriction
\(B_\gamma\) is a nonempty KKL Wave over
\(J=\iota^*I\).  This follows from the unbreakable case at KKL 1477;
the smaller \(I\) is permitted because the proof uses only
\(I\subset\operatorname{crest}(\{\gamma\})\) and end-properness.

The marked-circle directionalization is valid:

- each retained leaf's endpoint intervals avoid the connected \(J\);
- its boundary-side route either contains all of \(J\) or avoids it;
- if all routes avoided \(J\), choose a marking interval
  \(Q\subset J\);
- all singleton bases would then lie in the one proper multi-interval
  \(\partial_{\rm C}\mathcal T'\setminus\overline Q\);
- the aggregate base would lie there too, contradicting
  \(Q\subset J\) in the aggregate crest.

Thus every source leaf has at least one individually DL-directed
occurrence.  Taking all such occurrences preserves the lamination:
distinct inverse-image components of one leaf are disjoint, and an
intersection over two different source leaves would project under the
local immersion to an intersection of those leaves.  KKL domination
then gives

\[
 \mathcal W(S)\leq\mathcal W(B_I(S)).
\]

No occurrence selector is used.

### 6.2 Critical bound

When \(S\uparrow BL_0\), every hypothetical retained occurrence would,
by singleton A.14, give a proper target path above

\[
 F_*BL_0=\partial_{\rm C}\mathcal T.
\]

No proper boundary-parallel path can be above its entire ideal-boundary
component.  Therefore \(B^\sharp=\varnothing\), and the whole directed
restriction Wave is the metric-envelope discard:

\[
 \mathcal W(S)\leq\mathcal W(B)\leq c_{\rm DL}.
\]

This proves \(c_{\rm crit}=c_{\rm DL}\) without the broad KKL Wave
lemma.

### 6.3 Precritical bound

For \(S\uparrow BL_{q-1}\), the retained target

\[
 R=f(B^\sharp)
\]

is a proper Wave with \(R\uparrow BL_0\).  Two-step source
unbreakability gives one-step target unbreakability, so the critical
bound gives \(\mathcal W(R)\leq c_{\rm DL}\).  The only estimate on the
retained source is

\[
 B^\sharp\subset f^*R.
\]

Consequently

\[
 \mathcal W(S)
 \leq c_{\rm DL}+2\mathcal W(R)
 \leq3c_{\rm DL}.
\]

## 7. Directed packet and controlled target

The ordered-limb argument supplies the exhaustive leafwise split

\[
 S_0=S_0^+\dot\cup S_0^-,
\qquad
 S_0^+\uparrow BL_1,\quad
 S_0^-\uparrow BL_{-1}.
\]

It uses connected, noninterleaving prime-end limb blocks and never
promotes a leafwise direction to an aggregate crest.  For \(q=2\) the
two adjacent blocks coincide.  The unique maximal short subwave is
exactly the family of individually short leaves, so every \(S_0\)-leaf
is covered by this split.

A Wave ending at \(BL_0\) decomposes into at most
\(\ell(BL_0)\leq6b\) localized modules.  The \(n=1\) proof of KKL's
controllability lemma then gives one leafwise-over-\(BL_0\) module and
at most

\[
 \eta_b\leq6b+4b(2b+1)
\]

localized modules.  This use does not invoke the invalid broad
pushforward extraction.

The target trichotomy is then:

- \(C\): leaves with an endpoint in \(BL_0\);
- \(Y\): remaining leaves individually over \(BL_0\);
- \(Z_r\): residual leaves in one localized module.

The connected-base circle argument makes every \(Z_r\) subordinate to
\(\partial_{\rm C}\mathcal T\setminus BL_0\).  Since all target leaves
retain the same noncritical leafwise direction, \(Z_r^{\rm sh}\) is
empty.  Lemma 4.2 bounds \(Y\), KKL 1524--1532 bounds every \(Z_r\),
and the Parallel Law gives

\[
 \mathcal W(R\setminus C)
 \leq e_b:=c_{\rm crit}+\eta_b c_{\rm away}.
\]

## 8. Proposition 7.1

Let \(S=S^{(N-n)\text{-nbr}}\) be one noncritical directed packet.

The parent family with no metric-envelope-retained directed occurrence
is dominated by \(B\setminus B^\sharp\), hence has width at most
\(c_{\rm DL}\).  This is the only direct DL charge.

The retained target

\[
 R=f(B^\sharp)
\]

is a Wave with leafwise direction \(BL_{k+1}\) and has
\(N-n-1\) unbreakable steps left.

- If \(k+1=0\pmod q\), Lemma 4.2 bounds \(R\); the full continued core
  is taken empty.
- Otherwise the target trichotomy gives
  \(R=C\dot\cup E\) with \(\mathcal W(E)\leq e_b\).

In the second case the source core is the full untagged saturation

\[
 P_C=\{\alpha\in S:\Phi_1(\alpha)\in C\}.
\]

For every retained parent outside \(P_C\), all retained occurrences
map to \(E\).  Domination and

\[
 B_E:=B^\sharp\cap f^{-1}(E)\subset f^*E
\]

give

\[
 \mathcal W(S^\sharp\setminus P_C)\leq2e_b.
\]

The Parallel Law yields

\[
 \mathcal W(S\setminus P_C)
 \leq c_{\rm DL}+2e_b.
\]

Surjectivity \(\Phi_1(P_C)=C\) is exact: every \(C\)-leaf has a retained
source occurrence, and saturation supplies its parent.  Conversely
the definition maps every retained parent into \(C\).  No
one-occurrence selector or maximal source subwave is used.

Thus

\[
 c_b^{\rm step}
 =c_{\rm DL}+2\max\{c_{\rm crit},e_b\}
\]

works in both cases and is independent of \(q,k,n,S\).

## 9. Initial step, induction, and horizon

For \(q=2\), all of \(S_0\) is precritical and is charged before any
pushforward.  For \(q>2\), \(S_0^-\) is charged by Lemma 4.3 and
Proposition 7.1 is applied only to \(S_0^+\uparrow BL_1\).  The two
incompatible directions are never pushed and unioned.

The full initial saturation may add source leaves from \(S_0^-\) whose
untagged output already belongs to \(C_1\).  This preserves exact
surjectivity and can only reduce the discarded family.  Therefore

\[
 c_b^{\rm init}=c_{\rm pre}+c_b^{\rm step}.
\]

At later steps,

\[
 A_{n+1}=A_n\cap\Phi_n^{-1}(P_{C,n})
\]

is an exact full saturation.  Since
\(P_{C,n}\subset\Phi_n(A_n)=S_n\), its image is all of
\(P_{C,n}\), not merely a subset.  Hence

\[
 \Phi_{n+1}(A_{n+1})=C_{n+1}.
\]

The weakest call to Proposition 7.1 is \(n=N-2\).  Its source has two
unbreakable steps left and its target one, exactly the amounts required
by the precritical/critical and away bounds.  No call is made at
\(n=N-1\), no \(A_N\) is defined, and the later KKL alignment assertion
is absent.

Because \(N=b+3\), the sequential factor satisfies

\[
 2^n\leq2^{b+1}.
\]

All constants are functions of \(b\) and universal source constants:

\[
\begin{aligned}
c_{\rm DL}&=c_{\rm DL}^{\rm raw}+1,\\
c_{\rm crit}&=c_{\rm DL},\\
c_{\rm pre}&=3c_{\rm DL},\\
\eta_b&\leq6b+4b(2b+1),\\
e_b&=c_{\rm crit}+\eta_b c_{\rm away},\\
c_b^{\rm step}
 &=c_{\rm DL}+2\max\{c_{\rm crit},e_b\},\\
c_b^{\rm init}&=c_{\rm pre}+c_b^{\rm step}.
\end{aligned}
\]

No constant depends on \(q\), the number of Borel arc packets, the
Wave, or its width.

## 10. Borel occurrence and parent audit

The accepted BOWR snapshot supplies:

1. standard-Borel leaf codes and jointly Borel proper-path
   evaluations;
2. Borel prime-end endpoints;
3. a Borel countable maximal-restriction occurrence relation surviving
   both KKL filters;
4. a Borel unique untagged successor on already unbreakable families;
5. the Borel metric-envelope retained/discarded predicate; and
6. Borel full terminal-output saturation.

The actual parent partition is output-first:

\[
\begin{array}{ll}
\mathsf K &: P_C,\\
\mathsf D_{\rm bad}
 &: (S\setminus P_C)\setminus S^\sharp,\\
\mathsf D_E
 &: (S\setminus P_C)\cap S^\sharp.
\end{array}
\]

This is mutually exclusive and exhaustive.

- Every \(\mathsf D_{\rm bad}\)-parent has at least one directed
  occurrence and no retained one, so it is dominated by the one
  metric-envelope discard.
- Every \(\mathsf D_E\)-parent has a retained occurrence mapping into
  \(E=R\setminus C\), so it is dominated by \(B_E\subset f^*E\).
- A parent with no retained occurrence but with central untagged output
  belongs to \(\mathsf K\), preventing double charging.

The ledger gives no envelope leaf a fictitious DL span or outer-buffer
label.

## 11. Forbidden-inference audit

| forbidden inference | result |
|---|---|
| infer relative discarded width from the displayed DL retained-width inequality | absent |
| require a Borel predicate for each DL span packet or outer buffer | absent |
| treat extremal width as a countably additive transverse measure | absent |
| infer chartwise order-convexity of the DL deletion | absent |
| transport an aggregate source base through the covering | absent |
| promote leafwise direction to aggregate crest | absent |
| infer one common open univalent neighborhood from leafwise injectivity | absent |
| use coefficient-one width preservation on the retained family | absent |
| select one restriction occurrence and discard collisions | absent |
| use maximality of the continued source core | absent |
| invoke the later stationary alignment lemma | absent |
| use local connectivity of the Julia carrier | absent |

## 12. Final classification

No fatal gap was found in the frozen backward chain.

Relative to the explicitly named
`DL_RELATIVE_DISCARD_FAMILY_BOUND` and the two exact independently
audited measurable snapshots, the frozen manuscript proves

```text
KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION.
```

This classification does not propagate to Gate N2 or any later global
obligation.
