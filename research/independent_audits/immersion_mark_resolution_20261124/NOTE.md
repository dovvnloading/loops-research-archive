# Maximal-component pullback of the selected slit pair (MARK remains open)

**24 November 2026.** Original argument by Claude (Anthropic, Fable 5.2).
Integration review and corrections by OpenAI GPT-6 Astra Pro, including
independent mathematical/code review and Lean 4.32.0 finite verification.
No human specialist review. This note proves an elementary planar-topology
statement for an explicitly defined maximal-component restriction. Its
formula agrees with Kahn–Kapiamba–Lyubich (KKL,
[arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1)) Propositions
6.5–6.6 on the selected marked intervals, but the identification of path
restriction conventions is not established here. The proof-register rows
remain **MARK: open** and **SELECTED-ESCAPE: conditional**.

## 0. What is proved, and what remains open

`IDEAL_BOUNDARY.md` §5 and `maximal_native_wave_20261123/NOTE.md` §3 leave the
identification

\[
 \iota^*J = R_0(J):=q_0^{-1}(J)
\]

open. Section 2 shows that allowing *every* proper path whose trace lies
in \(\iota^{-1}(\gamma)\), including arbitrary hairpins, makes the
singleton premise vacuous. This diagnoses a problem with that reading;
it does not uniquely determine a replacement definition.

Here \(\iota^*_{\mathrm{mc}}\) denotes the ideal-set pullback defined using
**occurrence-indexed maximal temporal components** in §2. Section 3 proves

\[
 \iota^*_{\mathrm{mc}}X=q_0^{-1}(X),\qquad
 \iota^*_{\mathrm{mc}}O=O'.
\]

This is a written theorem for every nonempty connected inner subset and
for the outer circle, including the required maximality statement. To
read it as a statement about the native KKL operation requires the
additional source-identification premise:

**(MC)** For this embedded slit pair, KKL's path restriction in the
ideal-set maximality definition agrees with the occurrence-indexed
maximal-component convention, including the meaning of uniqueness.

Neither the hairpin contradiction nor the finite scripts prove (MC).
Under (MC), the native marking and escape conclusions follow from the
theorem; without it, the established conclusions concern the explicit
component/contour operation. No proof-register or canonical-ledger
status is promoted by this contribution.

## 1. Setting and inputs

Notation is that of `IDEAL_BOUNDARY.md` §1. The inputs are exactly:

* **(G1)** \(g:V\to U=D(0,R)\) is proper holomorphic of degree two with sole
  critical point 0, \(V\Subset U\), and \(\partial V\) is an analytic Jordan
  curve (`maximal_native_wave_20261123/NOTE.md`, Lemma 1.1).
* **(G2)** \(T=[y_2,y_1]\subset T'=[-y_1,y_1]=g^{-1}(T)\cap V\subset V\), with
  the order (O2).

Put \(\Omega=U\setminus T\), \(\Omega'=V\setminus T'\), \(\iota:\Omega'\hookrightarrow\Omega\)
the inclusion, \(f=g|_{\Omega'}\), and \(X_{\rm sl}=T'\setminus T=[-y_1,y_2)\).
Then

\[
 \Omega\setminus\Omega'=(U\setminus V)\ \sqcup\ X_{\rm sl},
 \tag{1.1}
\]

a disjoint union of two relatively closed subsets of \(\Omega\).

By `IDEAL_BOUNDARY.md` Lemmas 1–2 the ideal boundaries are
\(\partial^i\Omega=C\sqcup O\) and \(\partial^i\Omega'=C'\sqcup O'\), where
\(C,C'\) are the access circles of the slits \(T,T'\) and \(O,O'\) the outer
circles. Since \(\partial V\) is an analytic Jordan curve, \(O'\) is identified
pointwise with \(\partial V\).

Write \(\tau\in C\) for the single access at the tip \(y_2\) of \(T\), and
\(u_+,u_-\in C'\) for the upper and lower accesses of \(T'\) at \(y_2\). Let
\(A\subset C'\) be the closed arc of accesses of \(T'\) over \([-y_1,y_2]\)
(from \(u_+\) along the upper bank, round the tip \(-y_1\), back along the
lower bank to \(u_-\)), and \(A^\circ=A\setminus\{u_\pm\}=\partial_C X_{\rm sl}\).
Near every access over \((y_2,y_1]\) the two surfaces coincide, so \(\iota\)
extends to a homeomorphism \(\hat\iota:C'\setminus A\to C\setminus\{\tau\}\).
Define the monotone degree-one **contour map**

\[
 q:C'\to C,\qquad q|_{C'\setminus A}=\hat\iota,\qquad q(A)=\{\tau\}.
 \tag{1.2}
\]

This is the archive's \(q_0\) of (3.2) in angular coordinates. It is not a
boundary extension of \(\iota\): points of \(A^\circ\) are accesses to interior
points of \(\Omega\).

## 2. Source definition, trace degeneracy, and the component convention

KKL [§1.4](https://arxiv.org/html/2606.27272v1#S1.SS4) treats paths up to
reparameterization and defines properness by continuous extension to
ideal endpoints. It does not require simplicity. In
[A.1](https://arxiv.org/html/2606.27272v1#A1.SS1), a proper path \(\gamma\)
is *subordinate to* \(X\subset\partial^i V\)
if, up to homotopy rel endpoints, it lies in every neighbourhood of \(X\) in
the ideal closure. In particular its endpoints lie in \(X\), because the
intersection of all neighbourhoods of \(X\) is \(X\).

KKL [A.3.2](https://arxiv.org/html/2606.27272v1#A1.SS3.SSS2)
defines \(\iota^*\gamma\) as the set of proper paths in the source
"contained in \(\iota^{-1}(\gamma)\)", and \(\iota^*X\) as the maximal subset
\(Y\subset\partial^iV'\) with the property

\[
 \mathsf P_X(Y):\quad
 \bigl[\ \iota^*\gamma=\{\gamma'\}\ \text{and}\ \gamma'\ \text{subordinate to }Y\ \bigr]
 \Longrightarrow \gamma\ \text{subordinate to }X
 \quad\text{for every proper }\gamma .
 \tag{2.1}
\]

**Proposition 2.1 (degeneracy of the all-trace-contained-paths reading).** Suppose
that \(\iota^*\gamma\) contains every proper path of \(\Omega'\) whose trace
lies in \(\iota^{-1}(\gamma)\). Then for every \(X\) the property (2.1) holds
for every \(Y\), so \(\iota^*X=\partial^i\Omega'\).

*Proof.* If \(\iota^{-1}(\gamma)\) contains no proper path, \(\iota^*\gamma\) is
empty. If it contains a proper path \(\delta\), the hairpin following
\(\delta|_{(0,a]}\) and returning is a proper path with trace in
\(\iota^{-1}(\gamma)\). Choose two initial segments with different traces:
after fixing \(a\), a sufficiently short initial segment lies in an ideal
neighbourhood that excludes the interior point \(\delta(a)\). The resulting
hairpins are distinct even up to reparameterization. So
\(\iota^*\gamma\) is never a singleton, the hypothesis of (2.1) is never met,
and every \(Y\) qualifies. ∎

Under that reading all pulled intervals would coincide with the entire ideal
boundary. KKL Proposition 6.5 computes \(\iota^*I\) as
\(\iota^{-1}(I)\) together with the Carathéodory boundaries of the attached
components meeting \(I\), a proper subset, and Proposition 6.6 uses that the
sets \(\iota^*I\) are pairwise disjoint. Lemma A.11's hypothesis
("\(\iota^*\gamma\) contains a leaf of each \(S'_n\)") and KKL's use of
"restriction" in Lemma 4.7 motivate a component interpretation. However,
excluding the degenerate reading does not prove that a particular
alternative is the source's operation, especially for nonsimple paths.
The marked-path filters in A.3.2 are imposed after the pulled marking is
defined, so they cannot resolve that prior identification by themselves.

**Definition (maximal-component convention).** For a proper path
\(\gamma:(0,1)\to\Omega\), let \(\mathcal R_{\mathrm{mc}}(\gamma)\) be the
family of occurrences \((J,\gamma|_J)\), where \(J\) runs over connected
components of \(\gamma^{-1}(\Omega')\) for which the restriction is proper
in \(\Omega'\). Paths within an occurrence may be reparameterized, but
different occurrences are retained. Thus a singleton means exactly one
component. Lemma 3.1(a) shows that every component is proper in this setting.
Define \(\mathsf P_X^{\mathrm{mc}}(Y)\) by (2.1) with
\(\mathcal R_{\mathrm{mc}}(\gamma)=\{(J,\gamma')\}\) as its singleton
premise, and define \(\iota^*_{\mathrm{mc}}X\) as its greatest admissible
subset when one exists. Theorem 3.2 proves existence and uniqueness here.

Occurrence indexing matters: a target path can visit the same source
hairpin twice, separated by a segment in \(X_{\rm sl}\). The unindexed set
of source paths is then a singleton up to reparameterization although
there are two temporal components. Lemma 3.1(b) applies to a single
component, so deduplicating those visits would require an additional
argument. Arbitrary hairpins and loop-omitting paths are not added to
\(\mathcal R_{\mathrm{mc}}(\gamma)\) merely because their traces are contained
in the inverse trace. These are explicit model conventions, not a proof
of (MC).

## 3. The theorem

### Lemma 3.1 (all components are proper; ends of a unique restriction)

Let \(\gamma\) be a proper path in \(\Omega\).

(a) Every component \(J=(s,t)\) of \(\gamma^{-1}(\Omega')\) gives a proper path
\(\gamma|_J\) of \(\Omega'\).

(b) If \(\gamma^{-1}(\Omega')\) is a single interval \(J=(s,t)\), let \(e'\) be
the end of \(\gamma'=\gamma|_J\) at \(s\) and \(e=\gamma(0)\) the corresponding
end of \(\gamma\). Then exactly one of the following holds, and symmetrically
at \(t\):

| end \(e'\) of \(\gamma'\) | then | end \(e\) of \(\gamma\) |
|---|---|---|
| \(e'\in O'\) | \(s>0\), \(\gamma((0,s])\subset U\setminus V\) | \(e\in O\) |
| \(e'\in A^\circ\) | \(s>0\), \(\gamma((0,s])\subset X_{\rm sl}\) | \(e=\tau\) |
| \(e'\in\{u_+,u_-\}\) | \(s=0\) | \(e=\tau\) |
| \(e'\in C'\setminus A\) | \(s=0\) | \(e=\hat\iota(e')\) |

In particular, if \(e'\in C'\) then \(e=q(e')\).

*Proof.* (a) If \(s>0\) then \(\gamma(s)\in\Omega\setminus\Omega'\) is a limit of
points of \(V\), so by (1.1) \(\gamma(s)\in\partial V\cup X_{\rm sl}\). On
\(\partial V\) the point is an ideal point of \(O'\). If
\(\gamma(s)=p\in(-y_1,y_2)\), a small disc about \(p\) minus \(T'\) has two
components, the path cannot change component without crossing \(T'\), so it
converges to the upper or the lower access at \(p\). At the tip \(p=-y_1\) the
inverse Joukowski coordinate is continuous, so the path converges to the tip
access. If \(s=0\), the tail lies in \(V\), hence \(\gamma(0)\in C\) (a tail
converging to \(O\) leaves \(\overline V\)). At an access over \((y_2,y_1]\)
the surfaces coincide locally and the tail converges to \(\hat\iota^{-1}(\gamma(0))\).
At \(\gamma(0)=\tau\) the tail lies in a small disc about \(y_2\) minus
\(\mathbb R\), stays in one half, and converges to \(u_+\) or \(u_-\).

(b) If \(s>0\), the connected set \(\gamma((0,s])\) lies in
\(\Omega\setminus\Omega'\), hence by (1.1) in one of the two pieces. In
\(U\setminus V\): then \(\gamma(s)\in\partial V\), and the tail stays at
positive distance from \(T\), so \(\gamma(0)\in O\). In \(X_{\rm sl}\): then
\(\gamma(s)\in X_{\rm sl}\) gives \(e'\in A^\circ\), and a tail inside
\(X_{\rm sl}\) can leave every compact subset of \(\Omega\) only by tending to
\(y_2\), so \(\gamma(0)=\tau\). The cases \(s=0\) were treated in (a); note
\(e'=u_\pm\) forces \(s=0\), since \(\gamma(s)=y_2\notin\Omega\). ∎

### Theorem 3.2 (component pullback = contour inverse image)

For every nonempty connected \(X\subset C\) (a point, or an open, closed or half-open
arc, or all of \(C\)),

\[
 \boxed{\ \iota^*_{\mathrm{mc}}X=q^{-1}(X)\ },\qquad\text{and}\qquad
 \iota^*_{\mathrm{mc}}O=O'.
 \tag{3.1}
\]

More precisely \(\mathsf P_X^{\mathrm{mc}}(q^{-1}(X))\) holds, and every \(Y\)
with \(\mathsf P_X^{\mathrm{mc}}(Y)\) satisfies \(Y\subset q^{-1}(X)\).
Thus the greatest subset for the component convention exists and is
unique. The same holds for \(X=O\), \(Y=O'\). In this proof a unique
restriction always means a unique component occurrence as defined in §2.

*Proof.* **Maximality.** Let \(\mathsf P_X^{\mathrm{mc}}(Y)\) hold with \(X\subset C\) and
let \(y\in Y\). A null-homotopic proper loop \(\gamma'\) based at \(y\) is
subordinate to \(\{y\}\), hence to \(Y\).

* \(y\in C'\setminus A^\circ\): take \(\gamma=\gamma'\) small. It is proper in
  \(\Omega\) with both ends \(q(y)\) and is its own unique restriction. So
  \(\gamma\) is subordinate to \(X\) and \(q(y)\in X\).
* \(y\in A^\circ\), an access at \(p\in X_{\rm sl}\): let \(\gamma\) run inside
  \(X_{\rm sl}\) from \(\tau\) to \(p\), follow \(\gamma'\), and return inside
  \(X_{\rm sl}\). The slit segments lie outside \(\Omega'\), so \(\gamma'\) is
  the unique restriction, and both ends of \(\gamma\) are \(\tau=q(y)\). So
  \(\tau\in X\).
* \(y\in O'=\partial V\): join \(O\) to \(y\) inside \(U\setminus V\), follow
  \(\gamma'\) inside \(V\) near \(y\), and return to \(O\) inside
  \(U\setminus V\). The unique restriction is \(\gamma'\), but the ends of
  \(\gamma\) lie on \(O\), so \(\gamma\) is not subordinate to \(X\subset C\).
  Hence \(Y\cap O'=\varnothing\).

Thus \(Y\subset q^{-1}(X)\). For \(X=O\) the first two constructions give paths
with ends on \(C\), so \(Y\subset O'\).

**The property for \(X\subset C\), \(\tau\notin X\).** Here
\(Y=q^{-1}(X)=\hat\iota^{-1}(X)\subset C'\setminus A\). If \(\gamma'\) is the
unique restriction and is subordinate to \(Y\), both its ends lie in
\(C'\setminus A\), so by Lemma 3.1(b) \(\gamma=\gamma'\subset\Omega'\) with ends
\(\hat\iota(e')\in X\). Given a neighbourhood \(N\) of \(X\) in
\(\overline\Omega\), the set
\(N''=(N\cap\Omega')\cup\hat\iota^{-1}(N\cap C\setminus\{\tau\})\) is an open
neighbourhood of \(Y\) in \(\overline{\Omega'}\), because basic neighbourhoods
of accesses over \((y_2,y_1]\) (half-discs, or slit discs at the tip \(y_1\))
are the same in both surfaces. A homotopy of \(\gamma'\) into \(N''\) rel
endpoints is a homotopy of \(\gamma\) into \(N\) rel endpoints.

**The property for \(X\subset C\), \(\tau\in X\), \(X\ne C\).** Now
\(Y=q^{-1}(X)\supset A\). Let \(\gamma'\) be the unique restriction,
subordinate to \(Y\). By Lemma 3.1(b),

\[
 \gamma=\gamma_0*\gamma'*\gamma_1,
\]

where each \(\gamma_i\) is either trivial or a path inside
\(X_{\rm sl}\cup\{\tau\}\) joining \(\tau\) to the point under an end of
\(\gamma'\) in \(A^\circ\); the ends of \(\gamma\) are \(q(e'_0),q(e'_1)\in X\).

Choose an access \(z_0\in C\setminus X\) with \(z_0\ne\tau\), over a point
\(x_0\in(y_2,y_1]\), and a closed arc \(\rho\) in the ideal closure of
\(\Omega\), from \(z_0\) to \(O\), with interior in \(\Omega\). Choose a
vertical segment on the bank of \(z_0\) (the real segment to the right if
\(x_0=y_1\)); thus \(\rho\) is disjoint from \(X_{\rm sl}\), and for small
\(\varepsilon\) it exits the open \(\varepsilon\)-neighbourhood
\(S_\varepsilon\) of \(T'\) exactly once without reentry. Take
\(\overline{S_\varepsilon}\subset V\), and put

\[
 E=S_\varepsilon\setminus(T\cup\rho).
\]

In the physical plane, \(T\cup(\rho\cap\overline{S_\varepsilon})\) is a
compact tree meeting \(\partial S_\varepsilon\) in one point. Therefore
\(E\) is simply connected with locally connected boundary,
and \(X\) is an arc of prime ends of \(E\).

The set
\((S_\varepsilon\setminus(T'\cup\rho))\cup(C'\setminus\{\hat\iota^{-1}(z_0)\})\)
is an open neighbourhood of \(Y\) in \(\overline{\Omega'}\), since \(\rho\) is
closed and ends at \(z_0\notin X\). So \(\gamma'\) is homotopic rel endpoints in
\(\Omega'\) to \(\delta'\subset S_\varepsilon\setminus(T'\cup\rho)\). The map
sending an access at \(p\in X_{\rm sl}\) to the point \(p\) is continuous, so
this is a homotopy rel endpoints in \(\Omega\) from \(\gamma\) to
\(\delta=\gamma_0*\delta'*\gamma_1\subset E\).

Let \(N\) be a neighbourhood of \(X\) in \(\overline\Omega\). The sub-arc of
\(X\) between the two ends of \(\delta\) is compact, so \(N\cap E\) contains a
collar path \(\delta''\) along it with the same two ends. Uniformize \(E\) by
the disc; the Carathéodory extension is continuous, and two paths in the
closed disc with interiors in the open disc and common boundary endpoints are
homotopic rel endpoints by the straight-line homotopy. So \(\delta\simeq\delta''\)
in \(E\subset\Omega\), and \(\gamma\) is subordinate to \(X\).

**\(X=C\).** Every proper path with both ends on \(C\) is subordinate to \(C\)
(`IDEAL_BOUNDARY.md`, after Lemma 3), and by Lemma 3.1(b) a unique restriction
with ends in \(C'\) has \(\gamma\)-ends in \(C\).

**\(X=O\), \(Y=O'\).** If \(\gamma'\) is the unique restriction and is
subordinate to \(O'\), then by Lemma 3.1(b) both complementary pieces of
\(\gamma\) lie in \(U\setminus V\) and both ends of \(\gamma\) lie on \(O\).
For sufficiently small \(\varepsilon\), analyticity and compactness of
\(\partial V\) give a tubular inner collar. Homotope \(\gamma'\) rel endpoints into it,
\(\{z\in V:\operatorname{dist}(z,\partial V)<\varepsilon\}\). Then \(\gamma\)
lies in the annulus \(U\setminus\{z\in V:\operatorname{dist}(z,\partial V)\ge\varepsilon\}\),
disjoint from \(T\), which retracts within itself, rel \(O\), into any collar
of \(O\). So \(\gamma\) is subordinate to \(O\). ∎

### Corollary 3.3 (component marking and conditional native interpretation)

Let \(\mathcal I=\{I_0,\dots,I_9,O\}\) be the target marking of
`IDEAL_BOUNDARY.md` (7) and \(S_0,\dots,S_{19},O'\) the covering atoms of
\(f^*\mathcal I\).

1. \(\iota^*_{\mathrm{mc}}I_k=B_k\), the open blocks of the table in `IDEAL_BOUNDARY.md` §5:
   \(B_0=S_{18}S_{19}S_0S_1S_2\), \(B_1=S_3S_4\), \(B_2=S_5\), \(B_3=S_6\),
   \(B_4=S_7S_8S_9\), \(B_5=S_{10}\), \(B_6=S_{11}S_{12}S_{13}\),
   \(B_7=S_{14}\), \(B_8=S_{15}\), \(B_9=S_{16}S_{17}\) (internal joints
   included), and \(\iota^*_{\mathrm{mc}}O=O'\).
2. These eleven sets are pairwise disjoint, open and connected, and their
   complement is the ten accesses \(\hat\iota^{-1}\) of the target endpoints.
   So the component-pulled ideal marking \(\iota^*_{\mathrm{mc}}\mathcal I\)
   is defined. Under (MC) this is the marking of KKL A.3.2.
3. \(f^*\mathcal I\) refines \(\iota^*_{\mathrm{mc}}\mathcal I\): the five target cut
   locations \((y_5,y_3,y_6,a,y_4)\) are among the ten source cut locations.
   Under (MC), \(F=(f,\iota)\) therefore acts on \((\Omega,\mathcal I)\)
   in the sense of KKL A.3.4.
4. \(\iota\) is proper on every covering atom other than
   \(S_{19},S_0,S_1\). These three atoms meet the interior \(A^\circ\) of
   the attachment arc; the end-intervals \(S_{18},S_2\) of \(B_0\) do not.
   Thus the component marking has the finite properness and end-properness
   data required for combinatorial action. Under (MC), \(F\) is proper on
   \(I_1,\dots,I_9\), end-proper but not proper on \(I_0\), and acts
   combinatorially on \(C\).
5. On connected inner arcs the component operator is the contour operator:

\[
 F_{\mathrm{mc},*}:=f_*\iota^*_{\mathrm{mc}}=g_*q_0^{-1}=\Psi .
\]

   With the covering alignment \(f_*S_s=I_{s\bmod 10}\) established in
   `IDEAL_BOUNDARY.md` (9), the ordered image lists for \(I_0,\ldots,I_9\) are

   \[
   (I_8I_9I_0I_1I_2,\ I_3I_4,\ I_5,\ I_6,\ I_7I_8I_9,\ I_0,
     I_1I_2I_3,\ I_4,\ I_5,\ I_6I_7).
   \]

   This alignment is an analytic input to the finite checker; it is not
   inferred from the cut lists alone. Under (MC), \(F_*=F_{\mathrm{mc},*}\).

*Proof.* (1) is (3.1) with \(q^{-1}(I_k)\) read off from (1.2): only \(I_0\)
contains \(\tau\), and its preimage absorbs \(A\). (2)–(4) are then read from
the two cut lists; `verify.py` checks the finite bookkeeping. (5) is (3.1)
followed by the covering push-forward. ∎

Consequently the five-step saturation and the positive-subarc escape proved
for \(\Psi\) in `maximal_native_wave_20261123/NOTE.md` §§5–6 apply to
\(F_{\mathrm{mc},*}\) on this slit pair, for every selected period for which
(G1)–(G2) hold. Their interpretation as native \(F_*\) statements additionally
requires (MC). Positive-subarc escape uses the written dynamical argument;
the finite checks below concern marked runs.

## 4. Scope

* One finite-type, locally connected, embedded slit pair. Nothing here
  addresses non-locally-connected carriers (Issue #40) or the ordinary KL
  universal-cover immersion (Issue #62).
* The component formula agrees with KKL Propositions 6.5–6.6 on the marked
  intervals. Agreement of formulas is not a proof of (MC) for all proper
  paths. **Full native MARK remains open; SELECTED-ESCAPE remains
  conditional.**
* Not addressed: identification of a Wave descendant's crest with these
  interval images, the stationary pass-through statements, inner buffered
  coefficients, and every global gate (H1–H4, UPTCR).

## 5. Reproduction

```sh
python -B research/independent_audits/immersion_mark_resolution_20261124/verify.py
lake build ImmersionMarkFinite
```

The Python script derives blocks from the two cut lists and consumes the
covering alignment in (9). It checks the partition, refinement, finite
end-properness predicates, contour image table, and saturation of all 90
proper open runs of one to nine atoms within five steps. Internal joints
are included and both endpoints are excluded. It preserves the distinction
between a punctured circle (lifted span exactly ten) and the full circle
(span greater than ten). In particular, the runs with lifted endpoints
\((2,8),(3,9),(8,12),(9,13)\) are punctured after one step and full after two.
The sharp five-step bound is attained by \(I_3\) and \(I_7\).

[`ImmersionMarkFinite.lean`](../../../ImmersionMarkFinite.lean) independently
derives the finite blocks from the ordered cut ranks, checks agreement
with the archive's existing table, and kernel-checks the endpoint-aware
saturation and punctured-circle regressions with the pinned Lean 4.32.0.
All twelve theorems use `decide +kernel`; their printed axiom dependencies
are empty or only the standard `propext`. Neither checker formalizes prime
ends, homotopies, (MC), or the topology of §§2–3. Those topology statements
remain written arguments under the explicit component convention.
