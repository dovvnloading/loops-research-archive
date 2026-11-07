# Issue #40 — source-native stretching-block absorption and the exact root-free gate sieve

**Date:** 2026-11-06. **Status:** a source-anchored **finite-time absorption theorem** for the *actual* Kahn–Kapiamba–Lyubich (KKL) interval action, together with an unconditional exact finite-cyclic counting theorem. Its q-independent critical-gate application still requires verifying the **placement** of the native stretching block and the existing closed-Wave source/target hypotheses; native cut acyclicity, arbitrary prime-end attachments, interval growth, and MLC remain **OPEN**.

**Primary source:** [Kahn–Kapiamba–Lyubich, arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), §6.1 Proposition 6.8 (a genuine length-≤2 *stretching multi-interval* with long corridor in its exact `F_*` image), paragraph following Proposition 6.6 (`F_* L_0=C`, `F_* L_j=L_{j+1}` for `j≠0`), Proposition 6.5 (actual attached Carathéodory boundary blocks), and Appendix A.3.2/A.3.4 (proper-path immersion pullbacks and independent open/closed actions). Related but **stronger access-conditioned** results: [root-exposure absorption](./kkl_native_root_exposure_absorption_20261106.md) in parent PR #41 and the [exact marked-root-cut sieve](./kkl_exact_root_stalk_sieve_20261106.md) in this PR.

## 1. Crucial source-safe distinction: an INTERVAL rather than a conjectured prime-end root

The proof of KKL Proposition 6.8 starts from a **planar** common attachment point `x`. Its statement, however, produces an actual original-marking multi-interval `B=I_str` of length `t=ell(B)≤2` such that

\[
\boxed{Q:=\mathbf L_{(\mathbf b,q-\mathbf b)}\ \subset\ \Phi(B),\qquad\Phi=F_*=f_*\iota^*.}\tag{1}
\]

`B` is one or two **consecutive original marking atoms** (including any internal marked cut). **Equation (1) is native and needs no choice of a singleton ideal access `a_x`.** In particular, it does **not** assert that a closed crest merely containing some planar point `x`, or one of several prime ends with impression containing `x`, must expose `Q`. A two-atom `B` is not equivalent to either neighboring atom or to their shared cut; replacing (1) by that stronger statement requires a separate actual source-access theorem.

The source gives `Phi(L_j)=L_(j+1)` for every `j≠0`, `Phi(L_0)=C`, `Phi(C)=C`, where `C` is the full inner Carathéodory circle. The genuine proper-path interval operation is inclusion-monotone on all inputs for which the asserted iteration is defined. The corridor `Q` contains the **complete** `q−2b−1` consecutive limbs `L_(b+1),...,L_(q−b−1)`.

## 2. Native theorem: every input containing `I_str` absorbs in bounded time

**Theorem 2.1 (source-native stretching-block absorption).** Fix an actual KKL parabolically `b`-bounded prime-primitive stage of rotation `1/q`, with `q≥2b+3`, and choose the actual `B=I_str` from Proposition 6.8. Let `D` be any connected original marked open multi-interval **or its closure**, and suppose `B⊂D`, with all displayed open/closed iterates properly typed. For `1≤m≤b+2`, either `Phi^m D=C` or `Phi^m D` contains at least `q−2b−1` complete distinct limbs and therefore at least this many original atoms; moreover

\[
\boxed{\Phi^{\mathbf b+3}D=C.}\tag{2}
\]

**Proof.** From the *actual* Proposition 6.8 inclusion and monotonicity, `Phi(D) ⊃ Phi(B) ⊃ Q`. Before the last limb of `Q` reaches `L_0`, every limb in `Q` advances exactly one index under `Phi`: for `0≤u≤b+1`,

\[
\Phi^u Q\supset\bigcup_{j=b+1}^{q-b-1}L_{j+u\pmod q}.\tag{3}
\]

The shifted indices are distinct. At `u=b+1`, the last index is `0`, so applying `Phi` one further time yields `Phi^(b+2)Q=C`. With `Phi^m D ⊃ Phi^(m−1)Q` we obtain the lower bound for `1≤m≤b+2` and equality `Phi^(b+3)D=C`. Absorption thereafter follows from `Phi(C)=C`. This uses *no* Perron eigenvalue, local connectivity, unproved cellwise cut-cosheaf, individual root access identification, or general nondecrease of marked length. □

**Corollary 2.2 (native short-successor exclusion).** Assume `q≥14b+1` and a genuine short successor crest `E` is a proper connected closed interval with `ell(E)<12b`. If a prior valid crest `D` **contains the entire open** `B=I_str`, then no inclusion `Phi^m(D)⊂E` can hold for any `m≥1` (assuming the required closed actions are defined). Indeed `q−2b−1≥12b`, so every positive image has too many complete marking atoms or is the full circle.

This is **a source-native terminality theorem for an entire original marked block**. It is weaker in domain than the parent PR's selected-single-prime-end root theorem but removes that theorem's most delicate source-access identification.

## 3. Exact closed-crest gate sieve using both absorbing mechanisms

The following theorem is finite cyclic combinatorics and is valid *independently of KKL*.

Let the circle have `M` consecutive open atoms labelled `0,...,M−1`. Let `L` be the open critical run with atoms `0,...,r−1`, `1≤r<M`. Fix `1≤k≤M−r`; let `J_s` be the open `k`-atom interval starting at cut `s` and `D_s=closure(J_s)` its closed crest. Let `B` be a consecutive marked block of `t∈{1,2}` open atoms, and suppose `B` has **at least one full atom** in common with `L`. Count the candidate states meeting `L` that escape **both** fatal tests:

\[
\mathcal G_{k}(L,B)=\{J_s:\ J_s\cap L\ne\varnothing,\quad L\not\subset J_s,\quad B\not\subset D_s\}.\tag{4}
\]

Since `B` consists of open atoms, `B⊂D_s` iff all its atoms are in the open core `J_s`. A boundary point alone is **not** a substitute for a full stretch atom.

**Theorem 3.1 (sharp two-terminal sieve).** For every such `M,r,k,B`,

| Source stretch-block position | Exact `|G_k(L,B)|` |
|---|---|
| `t=1`, the atom is in `L` | `r−1` |
| `t=2`, both atoms are in `L` | `r` |
| `t=2`, one atom in `L` and one outside (across a critical boundary cut) | `r−1_{k≥r}` |

**Proof.** Work in the unique integer lift furnished by `k≤M−r`. The critical-meeting start cuts are `1−k≤s≤r−1`, exactly `r+k−1` in number. The starts of length-k intervals containing a fixed contiguous `t`-atom stretch block are `b+t−k≤s≤b`, exactly `(k−t+1)_+` if `k≥t`; every one automatically meets `L` because `B` has an atom in `L`. The intervals containing *all* `L` are `r−k≤s≤0`, exactly `(k−r+1)_+` when `k≥r`.

By inclusion–exclusion, the states that avoid *both* containments number

\[
(r+k-1)-(k-t+1)_+-(k-r+1)_++(k-h+1)_+,\tag{5}
\]

where `h` is the number of atoms of the **smallest contiguous run containing `L∪B`** (because `B` touches `L`), and `(u)_+=max(u,0)`. If `t=1`, `h=r`; if `t=2` inside `L`, `h=r`; if `t=2` crossing a boundary, `h=r+1`. Substituting and distinguishing `k<r` from `k≥r` proves the table. The formulas include `r=1`, `k=1`, and two-atom blocks wrapping cut `0`. □

**Sharpness:** every listed survivor is a genuine distinct original marked interval; the stated counts need no hypothetical transition matrix or boundary-fiber assignment. They count **combinatorially eligible** input states only, not actual surviving KKL transitions. No periodicity exclusion follows from this theorem alone.

**Why the second fatal test matters:** if a two-atom `B` straddles the critical boundary, a `k≥r` interval can contain *all* `L` while missing the outside atom of `B`. Such an interval already saturates by `Phi(L_0)=C`. Omitting this condition overcounts by exactly one at every length `k≥r`.

## 4. Genuine KKL implication, with precise remaining stage-location check

In the high rotation regime `q≥24b` the actual marking satisfies `M≥q`, `r=ell(L_0)≤6b`, and a short critical crest has core length `1≤k<12b`; hence `k≤M−r` and `q−2b−1≥12b`. By Theorem 2.1 and the native `Phi(L_0)=C`, a **continuing** short-critical Wave source core `J` can neither contain the full open critical limb nor have a closed crest containing the entire source stretching interval `B=I_str`.

**Stage check still required:** certify that at least *one original marking atom* of the exact `I_str` belongs to the critical limb `L_0`. Proposition 6.8 does **not in its statement** identify `I_str`'s original atom indices relative to `L_0`, and its common planar point `x` must not be silently replaced by a distinguished marked prime-end cut.

Once this **atom-placement check** is verified in a given actual stage, Theorem 3.1 gives the following maximum number of candidate source states *per fixed short k*: `r−1` for a one-atom stretch, `r` for two atoms wholly inside the critical limb, and `r−1_{k≥r}` when the two-atom stretch straddles a critical boundary. These bounds are independent of `q` and require **no** singleton root-access identification. Summing over `K=12b−1≥r` permitted short lengths gives respective exact combinatorial capacities

\[
\boxed{(r-1)(12b-1),\qquad r(12b-1),\qquad (r-1)12b.}\tag{6}
\]

In particular, for `b=1,r=6`, the maximum source candidates are respectively **55, 66, 60**, rather than the previous generic bound **110**. These are **candidate capacities**, not actual return counts. If proper original marked length is further proved nondecreasing on the native chain and proper periodic critical returns are excluded, the same capacities bound the number of *continuing transitions*, by the exact plateau argument of PR #42. Those two missing hypotheses remain OPEN.

**Additional source-based placement restriction.** The source gives `Phi(L_j)=L_(j+1)` when `j≠0`. Thus, whenever a candidate `I_str` lies wholly inside some *single noncritical* whole open limb `L_j`, its image lies inside `L_(j+1)` and **cannot** contain the corridor `Q` of multiple full limbs. Therefore a one-atom `I_str` belonging to an ordinary limb must belong to `L_0` (since each original atom is in a single open limb); a two-atom `I_str` either touches `L_0` or, if it does not, must cross a boundary between distinct *noncritical* limb blocks. The latter is the sole remaining combinatorial placement exception **under the stated limb partition assumption**; a proof that it cannot produce the actual stretching corridor needs to inspect the genuine attached-boundary pullback at that boundary. This observation uses the actual single-limb dynamical law and source inclusion monotonicity, not an invented atom-word map.

## 5. Trust boundaries and adversarial controls

- **No false singleton-root improvement.** If a two-atom `B` shares a marked cut with a closed crest, the crest can contain this cut but **not both** stretch atoms. It is invalid to declare it terminal solely from Proposition 6.8. The sharper root-cut result of PR #42 remains conditional on proving the actual native selected-access pullback.
- **No misplaced stretch-block pruning.** If the entire `B` lies far from `L`, its coverage may forbid *zero* critical-meeting states of short length. The verifier includes an exact counterexample. A uniform `r`-bound without the overlap placement is false.
- **No fake closed/open equality.** Only `B⊂D` is needed; the proof never identifies `Phi(overline J)` with `overline(Phi(J))`. Both must be computed separately where the Wave argument uses them.
- **No analytic overreach.** The finite regression tests marked atom incidences, not universal non-LC prime-end pullbacks, attachment census, zero-edge WAD coercivity, actual native first-return acyclicity or the global MLC conjecture.

**Reproduce:** `python research/independent_audits/verify_stretching_block_sieve.py --check-manifest`. This exhaustively tests cyclic markings through `M=40`, every `r,k`, every 1-/2-atom stretch-block placement including wraps, the exact two-terminal table and both adversarial controls. Source statements are checked by human-readable proof and link, **not** by that Python script.

**Immediate remaining task:** in **one actual** prime-primitive KKL stage, write down the two `I_str` original marking indices using the true `iota^*` attachment proof of Proposition 6.8. Either (i) one atom is in `L_0`, activating the new exact root-free sieve, or (ii) both atoms straddle a noncritical limb boundary; then certify or refute the necessary closed-only cut birth from the actual Proposition 6.5 attached components. After that, compute the genuine first-return arrows among the surviving states. Neither geometric placement nor native acyclicity is claimed proved here.

**Attribution:** Native stretching input and limb dynamics are due to Kahn–Kapiamba–Lyubich. The source-safe absorption corollary, double-terminal exact counting refinement, proof exposition, and tests are research contributions assisted by OpenAI GPT-6. Novelty or independent referee validation has not been established.
