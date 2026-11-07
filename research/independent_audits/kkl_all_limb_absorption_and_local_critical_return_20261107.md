# Issue #40 — all-limb finite-time absorption and a length-variable native critical-return graph

**Date:** 2026-11-07. **Status:** a direct source-native absorption consequence, an exact cyclic marked-limb counting theorem, and a *conditional-on-typed-native-intervals* first-return cycle equivalence that **does not assume nondecreasing marked length**. The actual return arrows/acyclicity, non-LC attachment census, Wave-growth repair, and MLC remain **OPEN**. This note is stacked on the exact source-stretch and root-stalk sieves in PR #42, but **does not use either stretching-block placement or root prime-end identification**.

**Primary source, fixed v1:** Kahn–Kapiamba–Lyubich, [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §2.4 (limbs and cyclic order), §4 Lemma 4.8 and the immediately preceding definition of the marked Carathéodory limb intervals (each length at most `6 b`), §6.1 after Proposition 6.6 (exact `F_* L_j = L_(j+1)` for `j != 0` and `F_* L_0 = C`), Proposition 6.5 (actual full attached-component boundary pullback), Appendix A.1 and A.3.4 (ideal multi-intervals and independent closed actions). The source uses the sum of these limb lengths to bound its total original marking in the proof after Lemma 4.8. For the finite count below we state **limb tiling explicitly** rather than silently assuming a pointwise boundary quotient in a non-LC lift.

## 1. The overlooked consequence of the *whole family* of native limb identities

Fix a prime-primitive parabolically `b`-bounded stage of combinatorial rotation `1/q`. Write `C=∂_C T`, `Phi=F_*=f_* iota^*`, and let `L_0,...,L_(q-1)` denote its **actual** connected open marked limb multi-intervals, with `L_0` critical. KKL §6.1 supplies

\[
\Phi(L_0)=C,\qquad \Phi(L_j)=L_{j+1}\quad(1\le j<q),
\qquad \Phi(C)=C.
\tag{1}
\]

Use only the natural inclusion monotonicity of the genuine proper-path pullback and covering pushforward. Whenever `D` and its relevant iterates are source-admissible marked open or closed connected inputs, let

\[
 d(j)=(-j)\bmod q\in\{0,1,\ldots,q-1\}.
\]

**Theorem 1.1 (all-limb absorption).** If `L_j ⊂ D`, then

\[
\boxed{\Phi^{d(j)+1}D=C.}\tag{2}
\]

Moreover, for `0 <= s <= d(j)`, the image `Phi^s D` contains the whole forward limb `L_(j+s mod q)`, unless it has already saturated.

**Proof.** By (1), `Phi^s L_j=L_(j+s)` for `0<=s<=d(j)`. The next iterate is `Phi(L_0)=C`. Inclusion monotonicity gives `C=Phi^(d(j)+1)L_j ⊂ Phi^(d(j)+1)D⊂C`, hence equality. Saturation is absorbing, since `Phi(C)=C`. No eigenvalue, individual cut-fiber identification, length monotonicity, or local connectivity is used. □

**Corollary 1.2 (no full limb in a proper recurrent orbit).** Every **infinite entirely proper** forward orbit of typed connected original marked intervals, in particular every proper periodic orbit, avoids containing **every** full `L_j`, not just `L_0`. Otherwise Theorem 1.1 saturates it in finitely many iterations. This is a necessary condition for a native orbit, not a claim that such an orbit exists.

**Corollary 1.3 (finite critical-visit clock budget).** Suppose genuine properly typed closed crests `D_0,...,D_N` are proper, with `Phi^(m_i)D_i ⊂ D_(i+1)` for positive integers `m_i`. If `D_0` contains the entire limb `L_(q-d)` for `1<=d<q`, then **`N<=d`**. In particular an entire immediate predecessor limb `L_(q-1)` in a source crest permits at most **one** later proper crest, and the critical limb permits **none**.

**Proof.** The cumulative iterate time to `D_t` is at least `t`, and the compositions of the actual inclusions imply `Phi^(m_0+...+m_(t-1))D_0 ⊂ D_t`. By (2), the left side is `C` whenever `t>=d+1`. That contradicts properness. For `d=0` saturation is already at time one. □

This clock budget is valid with arbitrary positive visit times and **does not** identify `Phi^n(closure(J))` with `closure(Phi^n(J))`.

## 2. A stronger necessary locality constraint on every periodic critical return

The following finite theorem is independent of KKL.

**Marked limb-tiling hypothesis (TILE).** The original atom circle is a cyclic concatenation of `q>=3` nonempty connected limb blocks `L_0,...,L_(q-1)`. Their interiors comprise all original marked atoms; blocks meet only at their endpoint cuts. The critical limb has `r` atoms, its immediate **cyclic** predecessor has `a` atoms, and its immediate successor has `c` atoms. For source rotation `1/q` the latter are `L_(q-1)` and `L_1`. The source §4 definition and its total atom count motivate TILE; its exact original-marking endpoint interpretation should still be checked when applying the theorem to a particular non-LC stage.

Let `H` be the set of all **positive proper connected open marked intervals** which meet `L_0` but contain **no entire** limb `L_j` for any `j`. Its elements are candidate critical states for a proper infinite (hence periodic after finite-state repetition) orbit; **not** automatically valid native return arrows. A length-`M` **punctured-circle** interval, which is distinct from the whole circle in Appendix A, contains all marked atoms and hence entire limbs; so none belong to `H`. The exact count legitimately ranges over `1<=k<M` without conflating those two source objects.

**Theorem 2.1 (two-neighbor localization and exact total count).** Under TILE, each `J∈H` is either:

- a nonempty **proper subinterval of `L_0`**, or
- an interval crossing precisely the cut between `L_(q-1)` and `L_0`, consisting of nonempty proper terminal/initial fragments of both limbs, or
- the analogous interval crossing the cut between `L_0` and `L_1`.

In particular it cannot touch a third limb. The total number, taken over **all positive lengths**, is exactly

\[
\boxed{|H|=\frac{r(r+1)}2-1+(r-1)(a-1)+(r-1)(c-1).}\tag{3}
\]

For fixed marked length `k`, define

\[
X(k;r,n)=\max\{0,\ \min(r-1,k-1)-\max(1,k-n+1)+1\}.
\]

Then the exact count is

\[
\boxed{|H_k|=\mathbf1_{1\le k<r}(r-k+1)+X(k;r,a)+X(k;r,c).}\tag{4}
\]

If `r=1`, then **`H` is empty**. Otherwise every member has length at most `r+max(a,c)-2`.

**Proof.** An open connected arc crossing parts of three distinct cyclic limb blocks contains the **entire middle block**, contrary to the definition of `H`. If it meets `L_0`, the only permissible other blocks are therefore the immediately adjacent predecessor or successor. It cannot meet both neighbors: crossing both boundaries would contain all of `L_0`. If it stays within `L_0`, it is one of the `r(r+1)/2` nonempty contiguous atom subintervals, excluding the whole `L_0` itself. Across the predecessor boundary, choose independently `x∈{1,...,a-1}` terminal predecessor atoms and `y∈{1,...,r-1}` initial critical atoms. Each pair yields one and only one permitted interval. This gives `(a-1)(r-1)` choices. The successor boundary is analogous and the three classes are disjoint, proving (3). At a fixed length `k`, the internal subinterval count is `r-k+1` for `k<r`, while crossing pairs satisfy `x+y=k`, `1<=x<=n-1`, `1<=y<=r-1`. Solving for `y` gives (4). The length bound follows from the maximum possible fragment lengths. □

**Corollary 2.2 (uniform independent-of-q critical-cycle candidate bound).** Under TILE and the native `r,a,c<=6b` from Lemma 4.8,

\[
\boxed{|H|\le 90b^2-21b+1,\qquad\ell(J)\le12b-2\text{ for every }J\in H.}\tag{5}
\]

At `b=1`, the worst-case cycle candidate count is **70**, compared with the earlier generic internal-cut bound **110**. The bound requires neither a location for `I_str` nor marked-length monotonicity. It is a count of *original marked candidate intervals*, not non-LC prime ends or source pullback components. For `r=3,a=c=1`, there are exactly **five** possible critical states across *all* lengths; all crossing states are killed by full one-atom neighbor limbs.

**Adversarial control:** with limb atom lengths `(3,1,2,1,1)` and the first limb critical, at `k=2` the old **critical-limb-only** test leaves 4 candidate intervals, but forbidding complete *noncritical* limbs leaves only **2**. Merely checking whether `J` contains `L_0` misses two future-absorbing states.

## 3. A length-VARIABLE finite first-return cycle equivalence

The companion [first-return graph note](./kkl_native_finite_critical_cut_first_return_graph_20261106.md) works length-by-length and assumes nondecreasing proper marked length to identify all periodic critical returns. The all-limb sieve allows a different and strictly more general **cycle-detection** interface.

Assume TILE and the source-defined `Phi` is deterministic and properly typed on all considered positive connected open intervals and their necessary iterates. Define a **partial first critical-return operator** on the finite set `H`:

- For `J∈H`, take the *least* `n>=1` such that `Phi^n J` meets `L_0`, if it exists.
- Set `R(J)=Phi^n J` **only if** `Phi^s J` for each `1<=s<=n` is a proper well-typed positive open marked interval containing no whole limb and the return value lies in `H`. Otherwise leave `R(J)` undefined. No preservation of `ell(J)` is required.

All arrows are to be computed from the **real KKL** `f_*iota^*` and all attached-boundary contributions of Proposition 6.5. There is **no synthetic image-word assignment**.

**Theorem 3.1 (cycle equivalence without length monotonicity).** Under these typing assumptions,

\[
\boxed{R\text{ contains a directed cycle}\quad\Longleftrightarrow\quad
\Phi\text{ has a proper positive marked periodic orbit meeting }L_0.}\tag{6}
\]

**Proof (forward).** Concatenate the finitely many genuine positive-time `Phi` orbit segments constituting the `R` cycle. By construction, every intermediate state is properly typed and proper; their composite returns exactly to the starting interval, hence it is a proper periodic critical orbit.

**Proof (backward).** Any proper periodic critical orbit avoids every full limb by Corollary 1.2. Every critical-meeting state thus lies in `H` by TILE. The sequence of least positive returns to `L_0` along the periodic orbit gives actual `R` arrows and is itself periodic, yielding a directed cycle. **Lengths may decrease or increase along this period**; they need not form plateaus. □

**Finite certificate consequence:** To rule out the *periodic critical-return* obstruction, it would suffice to compute source-authenticated arrows on at most `90b^2-21b+1` actual original-marking candidate intervals and certify that this finite directed partial functional graph has no cycle. Such a graph admits an integer rank strictly decreasing along each arrow **iff** it is acyclic (topological ordering). The arithmetic checker in this PR verifies the **candidate set only**, and cannot attest actual arrows or such a rank.

**Important separation:** absence of periodic `Phi` states in (6) alone does **not** prove the Wave critical-visit bound when subsequent crests are permitted to be *strict enlargements* of positive-time images. Acyclicity of a deterministic first-return graph does not automatically rule out cycles in that larger inclusion relation. The remaining analytic non-LC endpoint behavior, attached-component census, proper-length monotonicity (where used by the Wave proof), and genuine WAD/Shift-Lemma arguments are still open.

## 4. Reproducibility and next source-facing action

`python research/independent_audits/verify_limb_local_cycle_sieve.py --check-manifest` exhaustively enumerates all integer circular tilings with `3<=q<=5`, every limb size `1,...,5`, every designated critical limb and every positive proper interval length. It checks (3) and (4) against *independently enumerated subsets* and checks the claimed counterexample. It also covers 240 seeded longer partitions with `q=6,9,24`, checks the `b`-uniform algebra through `b=1000`, and compares the deterministic manifest byte-for-byte. This verification concerns **only finite combinatorics**.

**Next genuinely analytic gate:** Determine the *actual* first critical-return images of the few states in `H` whose endpoints are at internal critical cuts, starting with a stage where adjacent limb atom counts are small. Each arrow must carry the complete genuine `iota^*` attachment boundaries and distinguish open from closed crests. A source-verified cycle is a precise failure certificate; a source-verified decreasing rank proves native nonreturn. Neither outcome has yet been established.

**Attribution and scope:** The whole-limb images are those proved by Kahn–Kapiamba–Lyubich. The finite-time and length-variable return reductions are consequences of that source, and their finite counting proof and adversarial regressions were developed with OpenAI GPT-6 assistance. Novelty, priority, and independent referee validation have not been established. **Issue #40, the native interval-growth bridge, Wave amplification, and global MLC remain open.**
