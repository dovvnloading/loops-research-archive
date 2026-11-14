# Seven symbols distinguish the innermost period-27 Markov component

A seven-symbol observation of left and right itineraries identifies an entire recurrent component of the archive's 26-edge real interval graph. Every six-symbol additive observation has a stronger failure. Each stationary six-symbol histogram in the inner component is exactly reproducible by mixing stationary measures on the other two components. The seventh symbol supplies a field that can bring all three path-growth rates into resonance.

The same two thresholds agree at every higher depth in the explicit substitution model derived below. The archive identifies its first three components with a specific real quadratic center of period 27. The all-depth result concerns the symbolic model. Establishing the corresponding graph identification at additional quadratic centers would be a further dynamical theorem.

## Recovering the three recurrent components

Use the pinned [period-27 manifest](https://github.com/dovvnloading/loops-research-archive/blob/0a28eb11b0a2636db5a766081b1455a346e3837c/results/period27_symbolic_marking.json). Label the consecutive open Markov intervals from 0 through 25 in increasing real order. The critical point has rank 13 among the 27 vertices. An interval with index below 13 emits L, and every other interval emits R. We study **symbolic paths** through these intervals, with multiplicities as paths. Endpoint coding conventions and counts of distinct periodic points of the polynomial play no role.

Mutual reachability gives three strongly connected components, with arrows from 0 to 1 to 2 and a direct arrow from 0 to 2. Within each component a single vertex has two outgoing edges. All other vertices have one. The complete first-return words at that vertex are as follows. A return emits the starting vertex and excludes the terminal copy.

| Depth | Vertices | Branch vertex | Short return | Long return |
|---|---:|---:|---|---|
| 0 | 2 | 8 | L | LR |
| 1 | 6 | 14 | RLR | RLRLLR |
| 2 | 18 | 12 | LLRRLRLLR | LLRRLRLLRRLRRLRLLR |

Every bi-infinite recurrent itinerary in a single component is a concatenation of these returns, up to shifting the origin. Thus its language is exactly that of the shift space defined next. Write $X_0$ for all bi-infinite L/R strings avoiding RR. Define

$$
s(L)=RLR,\qquad s(R)=LLR,\qquad X_k=\bigcup_{j=0}^{3^k-1} T^j s^k(X_0),
$$

where $T$ shifts left by one position. Indeed the two return words at depth $k=0,1,2$ equal $s^k(L)$ and $s^k(LR)$. This substitution was read from **real side itineraries**. The archive's external-angle substitution has a different alphabet interpretation.

## A sharp length for distinguishing depths

A word is **private at depth $k$** if it occurs in $X_k$ and is absent from every $X_j$ with $0\le j<k$. This definition concerns paths confined to one recurrent component. An occurrence along a transient path crossing component boundaries does not by itself classify that path.

**Theorem 1.** For every $k\ge2$ there is exactly one shortest private word $W_k$, and
$$
|W_k|=2\cdot 3^{k-1}+1,\quad W_2=LLRLLRR,\quad W_{k+1}=s(W_k)\text{ with the last two letters deleted}.
$$
At depth 1 the shortest private word is RR.

**Proof.** At depth 2, the following counts come from extending all internal paths one edge at a time and then taking sets of their L/R labels. The accompanying verifier implements this recurrence on the 26-vertex graph. The same table follows by cutting factors from the six explicit return words above and their concatenations.

| Window length | $X_0$ | $X_1$ | $X_2$ | Private at depth 2 |
|---|---:|---:|---:|---|
| 1 | 2 | 2 | 2 | 0 |
| 2 | 3 | 4 | 4 | 0 |
| 3 | 5 | 6 | 6 | 0 |
| 4 | 8 | 7 | 8 | 0 |
| 5 | 13 | 8 | 10 | 0 |
| 6 | 21 | 9 | 12 | 0 |
| 7 | 34 | 11 | 14 | 1, namely LLRLLRR |

In a substituted string, positions modulo three have the form $(\overline a,L,R)$ with $\overline L=R$ and $\overline R=L$. A window is specified by its phase and its consecutive variable entries. An LL double uniquely sets the first L at the variable position. An RR double uniquely sets the second R there.

Suppose $m=|W_k|$. A window of length $<3m-2$ meets at most $m-1$ variable positions. Their decoded input is a word in $X_k$ of length $<m$, so some $X_j$ with $j<k$ contains it. Substitution at the same phase realizes the original window in $X_{j+1}$. At length $3m-2$ there are $m$ variable positions only when the window starts and ends on variable positions. To be private, it must decode to $W_k$. This leaves exactly one candidate, the indicated truncation of $s(W_k)$.

The base word contains both L and R at interior positions. This property persists because the candidate contains fixed adjacent LR in its interior. An interior input L produces a variable R preceded by a fixed R in the candidate. An interior input R produces a variable L followed by a fixed L. Thus the candidate contains RR and LL, so it cannot occur in $X_0$, and its phase is uniquely pinned. Occurrence in $X_j$ for $1\le j\le k$ would decode to an occurrence of $W_k$ in $X_{j-1}$, a contradiction. This proves uniqueness and $m_{k+1}=3m_k-2$, giving the formula. ∎

## A second length for recognizing every inner history

A seven-symbol word can certify a visit, but most seven-symbol windows of the inner component remain compatible with earlier depths. For the period-27 graph the exact length at which **every** inner window identifies its component is 21.

**Theorem 1b.** For $k\ge1$, the shortest length at which *all* words of $X_k$ are absent from every earlier depth is $D_k=7\cdot3^{k-1}$. There is exactly one shared word $V_k$ of length $D_k-1$. It obeys $V_1=RLRLLR$ and $V_{k+1}=LR\,s(V_k)$.

**Proof.** At depth 1, enumeration of the six- and seven-symbol windows gives precisely one RR-free six-symbol window, $RLRLLR$, and no RR-free seven-symbol windows. Equivalently this follows by expanding the base returns L and LR. For every $k\ge2$, each ten-symbol window of $X_k$ contains RR. In any once-substituted sequence every triple contains a fixed L, so the source of this final substitution has no RRR. Among three successive input letters at least one is L, and its variable output R is preceded by the fixed R from the preceding block. After the first position, a length-ten window sees at least three consecutive variable positions with their predecessors.

Write $M=D_k-1\ge6$ and suppose the unique maximum-length shared word at depth $k$ is $V_k$. Any word of $X_{k+1}$ shared with $X_0$ has length at most nine. For any other earlier depth, a shared window of length at least ten contains RR and therefore has the same substitution phase in both realizations. Its variable positions decode to a shared input word of length at most $M$. Such a window has length at most $3M+2$, with equality only if two fixed symbols precede the first variable and two follow the last one. Equality forces the word $LR\,s(V_k)$. This candidate does occur at both depths, by taking the two fixed final letters of the preceding block in any extension of the two realizations of $V_k$. Since $3M+2>9$, it is the unique longest shared word overall. Thus $D_{k+1}=3D_k$. ∎

At depths 2, 3 and 4 the shortest useful observation lengths are respectively 7, 19 and 55. The worst-case compulsory observation lengths are respectively 21, 63 and 189. These statements apply to the stated recurrent languages.

## No shorter additive measurement can strictly prefer the inner component

For a shift-invariant probability $\mu$, let $F_r(\mu)$ be its vector of probabilities of all length-$r$ words. Write $F_r(P)$ for the corresponding cyclic frequencies when the period is the word $P$.

**Theorem 2.** For $k\ge2$ and $r<|W_k|$, every $F_r(\mu)$ from $X_k$ equals $F_r(\nu)$ for a convex mixture $\nu$ of invariant probabilities from shallower depths. In particular no real-valued function of $r$ successive symbols can have strictly greater maximal time average on $X_k$ than on every shallower depth. At length $|W_k|$, its indicator $1_{W_k}$ achieves a positive average on a periodic orbit of $X_k$ and vanishes on all shallower components.

**Proof.** At depth 2, group every sequence into blocks $s^2(a)$. Each block has length nine. The two possible blocks differ only in their first position. Conditional on the phase, any six-symbol window therefore depends on at most one source letter. Every invariant probability on $X_2$ is the image of an invariant probability on the phase-tagged substitution suspension. To see this, lift a probability through the compact factor map, then average its translates and take a weak limit. Invariant lift measures are uniform over the nine phases, with a common shift-invariant source distribution after choosing block origin. Consequently $F_6$ depends affinely only on the source frequency of R. The allowed range is $[0,1/2]$ since $X_0$ forbids RR, and both endpoints occur on the periodic orbits L and LR. It suffices to check these two cases.

Set $A=LLR$, $B=LRR$, $C=LRRLRL$ as cyclic words. $A$ lies in $X_0$, and $B,C$ are rotations of $s(L),s(LR)$ in $X_1$. Direct cyclic counting gives the vector identities

$$
3F_6(s^2(L))=F_6(A)+2F_6(C),\qquad
6F_6(s^2(LR))=F_6(A)+F_6(B)+4F_6(C).
$$

All 128 rational coordinates are checked independently in the verifier. These identities prove the base case, including all shorter lengths by marginalization. A window of length $3r$ in a once-substituted sequence sees exactly $r$ variable positions at any phase. Its frequency vector is a fixed linear image of $F_r$ of the source under uniform phase averaging. Substitution therefore transports any mixture identity at $r$ to one at $3r$. Applying this to arbitrary invariant lifts proves the assertion by induction, since $|W_{k+1}|-1=3(|W_k|-1)$. Finally any occurring word extends to a periodic word in $X_k$, by closing its finite source word in the golden-mean shift. ∎

This is an obstruction to *strict* selection by a linear functional on measured frequencies. A nonlinear classifier, a specific individual sequence, or an entropy term in a variational principle is a different question.

## Tuning an exact three-component resonance

Give a path weight $u>0$ per L and $y>0$ per occurrence of $W_2$, with unit weight otherwise. These count fields define a statistical model on the archive graph. They have no assigned physical units or experimental interpretation.

Write $\rho_i(u,y)$ for weighted growth in component $i$. On the two outer components the marker never occurs. In the inner component it occurs once per first return, including occurrences that straddle the return seam. This can be read from its two first-return words with their next six letters, independently of the next return choice. First-return renewal then gives $1=w_1/\rho^d+w_2/\rho^{2d}$, with these inputs.

| Depth | $d$ | $w_1$ | $w_2$ | Polynomial for the positive growth root |
|---|---:|---|---|---|
| 0 | 1 | $u$ | $u$ | $x^2-ux-u$ |
| 1 | 3 | $u$ | $u^3$ | $x^6-ux^3-u^3$ |
| 2 | 9 | $yu^5$ | $yu^9$ | $x^{18}-yu^5x^9-yu^9$ |

There is a unique positive pair $(u_*,y_*)$ where all three growth roots coincide. In terms of their common value $\rho$,
$$
u_*=(\sqrt{13}-3)/2,\qquad
\rho=(u_*+\sqrt{u_*^2+4u_*})/2,\qquad
y_*={\rho^{18}\over u_*^5\rho^9+u_*^9}.
$$
Numerically these are $u_*=0.30277564$, $\rho=0.72208381$, $y_*=18.12067677$. Reduce the middle polynomial modulo the first. Its remainder is $u^2(u^2+3u-1)((u+1)x+u)$. For positive roots this forces $u=u_*$. The third equation is linear in $y$ and gives the displayed value.

Let $Z_n$ be the sum of path weights over all length-$n$ vertex strings. At resonance there is $C>0$ such that
$$
 Z_n\sim C n^2\rho^n.
$$
Weighted closed paths have total $O(\rho^n)$. In particular, closed-orbit data alone miss the quadratic multiplicity in open histories. The common growth factor happens to be below one. Multiplying every single-step weight by $1/\rho$ makes the quadratic effect visible without an exponential scale.

**Proof of the asymptotic.** Pass to graph states consisting of six consecutive vertices. Append a vertex and assign the seven-window's marker weight and its initial vertex's L weight. Positive end weights supply any remaining L factors. The recurrent components are the corresponding internal higher-block graphs, of periods 1, 3 and 9 by their two return lengths. All other states are transient and single-vertex components without loops. The connecting paths persist through the higher-block presentation. Each irreducible diagonal block has a simple positive Perron eigenvalue, with a strictly positive residue in its resolvent at $1/\rho$. In the block resolvent the chain $0\to1\to2$ contributes a third-order pole there. Its leading coefficient between positive end vectors is strictly positive by multiplication of the three Perron projections and the nonnegative connections. No chain contains more than three recurrent classes. Each remaining peripheral pole involves at most two blocks, since the first class is primitive. Thus the generating function has a unique third-order pole on its circle of convergence. Partial fractions give the stated asymptotic. A trace of a matrix power sums powers of eigenvalues with their algebraic multiplicities, hence has no polynomial prefactor. Equivalently, a closed path cannot cross from one component to the next. This pole mechanism is the classical reducible Perron theory of Rothblum.

## Sources, novelty and reproduction

- The input graph, exact critical ranks and pinned digest are from the [archive's period-27 certificate](https://github.com/dovvnloading/loops-research-archive/blob/0a28eb11b0a2636db5a766081b1455a346e3837c/results/period27_symbolic_marking.json). The verifier reconstructs all adjacency rows from the critical-orbit ranks and checks the archive's SHA-256.
- Mossé established recognizability and studied factor complexity of constant-length substitutions. The threshold here asks when a word separates one finite substitution depth from **all preceding depths** of a golden-mean source. [Mossé, 1996](https://doi.org/10.24033/bsmf.2283)
- Locally constant observables and their polyhedral rotation sets have an established theory. The two explicit histogram identities and their sharp failure at the next window are this calculation's contribution. [Ziemian, 1995](https://www.impan.pl/en/publishing-house/journals-and-series/fundamenta-mathematicae/all/146/2/108781/rotation-sets-for-subshifts-of-finite-type)
- The index of the Perron root of a reducible nonnegative matrix is classical. Here the concrete weights and the separating word realize its three-block case in the period-27 graph. [Rothblum, 1975](https://doi.org/10.1016/0024-3795(75)90050-6)
- The spectral study of Hubbard-tree Markov matrices and tuning is established. [Lindsey, Tiozzo and Wu](https://arxiv.org/abs/2112.14590)

A targeted literature and archive search did not establish priority for these exact assertions. The archived input, the two short frequency identities and the inductive proof let readers assess the claims independently of historical priority.

Run `python3 verify_markov.py --depth 6` from this directory. To compare with a checkout directly, add `--manifest /path/to/results/period27_symbolic_marking.json`. The verifier uses the Python standard library. Its finite threshold checks reach depths 2 through 6 and lengths 7, 19, 55, 163 and 487. The induction proves the general statement.
