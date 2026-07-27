# Marked endpoint-birth ledger

## 1. Purpose

The exact ribbon pullback theorem in
`saturated_virtual_seed_forest.md` assumes that every proof-used fan end is
the pullback of a bounded root endpoint set. A virtual carrier can violate
this by exposing new fjord, obstacle, or immersion ends at intermediate
stages.

This note gives the exact arithmetic for those endpoint births. It proves:

- bounded births **per stage** are not uniform over a long degree-one
  corridor;
- births confined to a bounded terminal window have a uniform weighted
  cost;
- the correct invariant is the total degree-weighted birth charge.

The result is finite combinatorics. It does not prove that the virtual
dynamics has a bounded birth charge.

## 2. Marked boundary sequence

Let
\[
 g_j:S_j\longrightarrow S_{j+1},
 \qquad 0\le j<N,
\tag{2.1}
\]
be proper holomorphic maps between Jordan disks, with
\[
 d_j:=\deg g_j\ge1,
\tag{2.2}
\]
and no critical point on a boundary.

Let \(P_N\subset\partial S_N\) be a finite terminal endpoint marking.
Recursively define
\[
 P_j=g_j^{-1}(P_{j+1})\cup Q_j,
\tag{2.3}
\]
where \(Q_j\subset\partial S_j\) is the finite set of endpoints first required
at stage \(j\).

Only endpoints not already in the pulled marking are genuine births. Put
\[
 B_j:=Q_j\setminus g_j^{-1}(P_{j+1}),
\qquad
 b_j:=|B_j|.
\tag{2.4}
\]
Then (2.3) is the disjoint union
\[
 P_j=g_j^{-1}(P_{j+1})\sqcup B_j.
\tag{2.5}
\]

For \(0\le a\le b\le N-1\), write
\[
 D_{a,b}:=\prod_{i=a}^{b}d_i,
\qquad
 D_{a,a-1}:=1.
\tag{2.6}
\]

## 3. Exact birth formula

### Theorem 3.1 (degree-weighted endpoint births)

The endpoint counts \(p_j:=|P_j|\) satisfy
\[
 p_j=d_jp_{j+1}+b_j
\tag{3.1}
\]
and therefore
\[
 p_0
 =
 D_{0,N-1}p_N
 +
 \sum_{j=0}^{N-1}D_{0,j-1}b_j.
\tag{3.2}
\]

**Proof.**
The boundary restriction of \(g_j\) is a degree-\(d_j\) circle covering, so
every point of \(P_{j+1}\) has exactly \(d_j\) boundary preimages. Equation
(2.5) gives (3.1).

Iterating,
\[
\begin{aligned}
 p_0
 &=d_0p_1+b_0\\
 &=d_0d_1p_2+d_0b_1+b_0\\
 &\ \vdots\\
 &=D_{0,N-1}p_N+\sum_{j=0}^{N-1}D_{0,j-1}b_j.
\end{aligned}
\]
\(\square\)

### Definition 3.2 (birth charge)

The **endpoint-birth charge seen from stage \(0\)** is
\[
 \mathfrak b_0
 :=
 \sum_{j=0}^{N-1}D_{0,j-1}b_j.
\tag{3.3}
\]

It is invariant under inserting a stage with degree one and no new endpoint.
It is not invariant under forgetting a genuine birth.

### Corollary 3.3 (necessary and sufficient count bound)

For fixed terminal degree \(D_{0,N-1}\) and terminal count \(p_N\), the
initial complete endpoint count is uniformly bounded if and only if
\(\mathfrak b_0\) is uniformly bounded.

This is an arithmetic equivalence. Geometric access completeness remains a
separate assertion determining the correct \(B_j\).

## 4. Degree-one corridor obstruction

### Corollary 4.1

If
\[
 d_0=\cdots=d_{N-1}=1,
\]
then
\[
 p_0=p_N+\sum_{j=0}^{N-1}b_j.
\tag{4.1}
\]

In particular, one genuine endpoint birth at every stage gives
\[
 p_0=p_N+N.
\tag{4.2}
\]

Thus a uniform local bound \(b_j\le1\) does not give a period-independent
complete marking when \(N\asymp q\).

### No-go consequence

The phrase “only boundedly many new sides occur at each pullback” is
insufficient for the long Wave argument. One must prove one of:

1. the total number of genuine corridor births is bounded;
2. apparent births are pullbacks/translates of already declared endpoints
   and hence have \(b_j=0\);
3. the complete marking is allowed to grow, but its contribution is
   density-normalized or amortized elsewhere.

## 5. Bounded terminal-window absorption

### Proposition 5.1

Assume:

1. \(d_j=1\) for \(0\le j<N-M\);
2. \(b_j=0\) for \(0\le j<N-M\);
3. \(d_j\le2\) and \(b_j\le b_*\) for \(N-M\le j<N\).

Then
\[
 D_{0,N-1}\le2^M
\tag{5.1}
\]
and
\[
 \mathfrak b_0
 \le
 b_*(2^M-1).
\tag{5.2}
\]
Consequently,
\[
 p_0\le2^Mp_N+b_*(2^M-1),
\tag{5.3}
\]
independently of \(N\).

**Proof.**
The first \(N-M\) factors equal one and have no births. In the terminal
window, every prefix degree is at most a power of two. Hence
\[
 \mathfrak b_0
 \le
 b_*\sum_{k=0}^{M-1}2^k
 =
 b_*(2^M-1).
\]
Theorem 3.1 gives (5.3). \(\square\)

This is the endpoint analogue of KKL's bounded auxiliary terminal fan. It
shows exactly why all new ends must be confined to a bounded defect window
or identified with existing translation orbits.

## 6. Multiple fan sheets

Let \(\mathcal V\) be a finite collection of selected source sheets over one
terminal target. Apply Theorem 3.1 on each sheet and sum. If sheet \(v\) has
terminal degree \(D_v\), terminal count \(p_N\), and birth charge
\(\mathfrak b_v\), then
\[
 p_{\rm fan}
 =
 p_N\sum_{v\in\mathcal V}D_v
 +
 \sum_{v\in\mathcal V}\mathfrak b_v.
\tag{6.1}
\]

For the dyadic profile \(D_v=2^m\), \(0\le m\le M\),
\[
 p_{\rm fan}
 =
 p_N(2^{M+1}-1)
 +
 \mathfrak b_{\rm fan},
\tag{6.2}
\]
where
\[
 \mathfrak b_{\rm fan}
 :=
 \sum_v\mathfrak b_v.
\tag{6.3}
\]

The zero-birth formula in `saturated_virtual_seed_forest.md` is the special
case \(\mathfrak b_{\rm fan}=0\).

## 7. Birth versus relabeling

An endpoint visible at a new stage is not a genuine birth if it is already
the required pullback of a declared future endpoint. Conversely, drawing two
ends similarly or assigning them the same limb label does not make either
birth vanish.

To certify \(b_j=0\), the virtual construction must give:

1. an actual endpoint \(x_{j+1}\in P_{j+1}\);
2. a selected boundary lift \(x_j\in g_j^{-1}(x_{j+1})\);
3. preservation of the prime-end/access class used later;
4. the correct cyclic position among all other marked endpoints;
5. future equivalence through the remaining horizon.

If any item fails, the endpoint must remain in \(B_j\) or be handled by a
proved quotient theorem.

### Proposition 7.1 (local carrier equality implies no birth)

Let a one-step selected correspondence have target carrier \(T\), pulled
carrier \(T'\), and immersion \(\iota\). Let \(I\) be a marked ideal interval
in a degree-one corridor. Assume:

1. \(\iota^{-1}(I)\) is one marked interval;
2. no component of \(T'\setminus T\) attaches to \(T\) at \(I\);
3. the selected polynomial map is conformal on that interval and its two
   endpoint prime ends.

Then the complete pulled marking over \(I\) has no genuine endpoint birth:
\[
 b_j(I)=0.
\tag{7.1}
\]

**Proof.**
The pullback description of an ideal interval is the union of
\(\iota^{-1}(I)\) and the ideal boundaries of components of
\(T'\setminus T\) attaching at \(I\). Assumption 2 makes the second union
empty, so the pulled interval is exactly \(\iota^{-1}(I)\). By Assumptions 1
and 3, its two endpoints are the unique boundary lifts of the two already
declared endpoints of \(I\). Thus \(Q_j\) contributes no point outside
\(g_j^{-1}(P_{j+1})\), and \(b_j(I)=0\). \(\square\)

### Corollary 7.2 (translation-corridor no-birth criterion)

If the three hypotheses of Proposition 7.1 hold on every ideal interval in
every central-corridor stage, then
\[
 b_j=0
\]
through the entire central corridor. All endpoint births are confined to
the entry/exit and terminal defect windows.

In KKL's native parabolically bounded setting, the corresponding mechanism
is the equality of the pulled and original Hubbard trees in the proper
translation region. For a virtual carrier this local equality is a new
realization theorem; it is not implied by coarse translation labels.

## 8. Virtual endpoint-birth certificate

For the long Wave branch, add the following to `VSC5`.

### `EBC1` Stage endpoint ledger

List \(P_j,Q_j,B_j\) at every proof-used fast-forward stage and identify the
covering degree \(d_j\).

### `EBC2` Translation no-birth theorem

Prove
\[
 b_j=0
\]
through the degree-one central corridor, except in universally bounded entry
and exit windows. Proposition 7.1 reduces this to local carrier equality,
absence of attached pullback components, and conformality on the marked
endpoint lifts.

### `EBC3` Terminal birth bound

Bound the terminal-window births by \(b_*(B,L)\) and the window depth by
\(M(B,L)\).

### `EBC4` Fan sum

Prove
\[
 \mathfrak b_{\rm fan}\le C_{\rm birth}(B,L)
\tag{8.1}
\]
after summing every selected auxiliary sheet.

### `EBC5` Access completeness

Prove every vertical, outgoing, lost, or amplifying leaf end lies in the
resulting \(P_j\). The arithmetic does not establish this.

`EBC1`--`EBC5` are the **Virtual Endpoint-Birth Certificate**. Proposition
5.1 then gives a period-independent complete endpoint count.

## 9. Adversarial audit

### 9.1 One birth per translation cell

Take \(d_j=1\), \(b_j=1\). Then \(p_0=p_N+N\).

**Verdict:** bounded local incidence is not a bounded complete marking.

### 9.2 Hidden high-degree early birth

Create one endpoint at stage \(j\) before many quadratic pulls. Its cost at
stage zero is
\[
 D_{0,j-1},
\]
not one.

**Verdict:** unweighted birth count is insufficient outside a pure
degree-one corridor.

### 9.3 Duplicate drawing, distinct prime ends

Two local endpoints have the same combinatorial label but lie on distinct
global prime ends.

**Verdict:** merging them falsely reduces \(b_j\); global access equivalence
must be proved.

### 9.4 Correct count, incomplete family

Omit one proof-used fjord endpoint from every \(Q_j\). Formula (3.2) still
holds for the declared sets.

**Verdict:** the recurrence validates accounting, not completeness.

### 9.5 Births confined to the terminal fan

All \(b_j\) vanish before the last \(M\) steps, and both \(b_j\) and \(d_j\)
are bounded there.

**Verdict:** Proposition 5.1 passes this adversary uniformly in \(q\).

## 10. Ledger consequence

Theorem 3.1 and Proposition 5.1 should be recorded as the proved internal
node `ENDPOINT_BIRTH_ACCOUNTING`.

Proposition 7.1 should be recorded as
`LOCAL_CARRIER_EQUALITY_NO_BIRTH`.

The live virtual Wave node remains open and must supply `EBC1`--`EBC5`.
