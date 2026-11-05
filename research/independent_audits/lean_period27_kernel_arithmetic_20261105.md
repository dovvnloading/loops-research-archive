# Lean-kernel arithmetic for the actual period-27 quadratic and its three-scale code

**Date:** 2026-11-05. **Status:** Two Lean 4.32.0 modules that check finite, explicitly stated exact arithmetic and symbolic computations without native-code trust, proof holes or new axioms. The dyadic-enclosure interpretation and the analytic IVT/MVT inference remain **mathematical arguments**, not fully formalized real-analysis theorems. No claim is made about proving ray landing, the KL geometric source atlas, or Mandelbrot local connectivity.

## 1. Why this increment matters

Previously the period-27 algebraic parameter, critical orbit signs and real critical-orbit order were verified by a transparent independent Python program using outward signed integer arithmetic; the published real kneading-angle and twisted permutation correspondence was a second independent Python test. This package **recomputes both layers inside Lean**, from the integer parameter bracket and finite definitions, instead of introducing a Lean axiom equating copied data.

These files are now separate default Lake targets:

- [Period27Dyadic.lean](../../Period27Dyadic.lean): the period-27 root-bracket endpoint signs, parameter derivative, 26 strict critical-orbit signs and all 27 strict orbit ranks via an actual 27-step dyadic interval recurrence.
- [Period27Kneading.lean](../../Period27Kneading.lean): 27-bit real kneading-angle recurrence, repeated airplane substitution, exact binary angle/doubling orbit, 27-state twisted-shift word orbit, 27 lexical ranks and their agreement with the real rank sequence, plus a generic phase-memory obstruction.

Every finite closed theorem uses Lean's kernel-reduced decidability check or ordinary proof construction. The modules call neither **native_decide** nor an external executable inside a proof. Their explicit printed axiom lists show only ordinary foundational Lean axioms (such as propositional extensionality, quotient soundness or choice where imported standard definitions use them), **not** a proof hole or compiler-trust axiom. Source file, toolchain and CI version are pinned in the repository.

## 2. Exact dyadic computation and the precision boundary

Let

\[
f_c(x)=x^2+c,\qquad
K=-607890580437450502081459824019535455703,
\quad c\in\left[K/2^{128},(K+1)/2^{128}\right].
\]

The Lean module represents values as signed integer intervals divided by \(U=2^{144}\). Accordingly the parameter endpoints are **integers** \(K2^{16}\) and \((K+1)2^{16}\). Its interval functions implement

\[
X_{j+1}=\operatorname{sq}_{\uparrow}(X_j)+C,
\qquad
D_{j+1}=2\,\operatorname{mul}_{\uparrow}(X_j,D_j)+1,
\qquad X_0=D_0=[0,0].
\]

The square operation computes the correct extremum at 0 when the current real interval crosses 0; every product bound is rounded outward using integer floor/ceiling division at the fixed power-of-two scale. The mathematical soundness interpretation is exactly the one explained in the earlier [real two-scale note](real_quadratic_3_9_restrictive_certificate_20261105.md): induction using \(x^2\), \(d_{j+1}=2x_jd_j+1\), and the derivative formula. The source-specific IVT and strict derivative inference are separate elementary analytic arguments, not Lean theorems here.

At this resolution, the kernel verifies **full endpoint interval equalities**, not only loose approximate signs:

\[
P_{27}(K/2^{128})\in
  [4251281,4252485]\,2^{-144}\subset(0,\infty),
\]

\[
P_{27}((K+1)/2^{128})\in
  [-8835097,-8833684]\,2^{-144}\subset(-\infty,0).
\]

It also checks that the *upper* bound of \(D_{27}\) over the entire parameter interval is strictly negative, and that \(x_1,x_3,x_9\) never vanish there. Taken with the independently explained interval soundness and continuity/differentiability facts, these inequalities isolate the unique exact-period-27 real root \(c_*\).

**Important failed precision experiment:** rounding at \(2^{-128}\) is sufficient for all 26 orbit signs and the strict 27-point order, but **not** for the two tiny endpoint signs: at that resolution, both endpoint enclosures straddle zero. The first Lean attempt therefore failed exactly where it should. Increasing precision to \(2^{-144}\) resolves the endpoint enclosure and gives the strict positive and negative numbers above. This negative audit is relevant: a proof that quietly used the coarser endpoint enclosure would have a gap.

## 3. Kernel-checked real critical orbit and exact word

For \(x_j=f_{c_*}^{\,j}(0)\), the signed integer bounds at \(2^{-144}\) establish:

- each \(x_j\), \(1\le j\le26\), is strictly nonzero and has the sign declared in the previous real certificate;
- the 27 values \(x_0,\ldots,x_{26}\) occur in strict increasing order at the following iterate indices:
  \[
  (1,19,10,16,25,7,13,22,4,6,24,15,9,0,18,12,21,3,5,23,14,8,26,17,11,20,2).
  \]

The Lean theorem **period27_dyadic_matches_symbolic_inputs** links the kernel-computed sign sequence to the kneading-angle algorithm and that exact ordering to the 27-point twisted-symbolic ranks. It does **not** simply assume a 27-element permutation equality as an axiom.

The separate kneading module starts at bit 0 and flips at each negative certified real critical-orbit value, giving the exact 27-bit block

\[
\boxed{011100100100011011100011011}
\]

and, from its binary value and denominator \(2^{27}-1\),

\[
\boxed{\theta_{\mathrm{knead}}(c_*)=\frac{59914011}{134217727}}.
\]

It checks in Lean that twice applying the airplane substitution \(0\mapsto011,\ 1\mapsto100\) produces the same binary word; the angle is a primitive period-27 doubling orbit; and it is the unique orbit element closest to \(1/2\).

## 4. Independent full 27-state twisted-shift comparison

Let \(\iota\) denote Boolean bitwise complement, \(L\) binary cyclic left rotation, and

\[
F(w)=
\begin{cases}
L(w),& \text{when }L(w)\text{ begins with 1},\\
\iota(L(w)),&\text{otherwise}.
\end{cases}
\]

The module builds the entire 27-word orbit of \(F\), checks closure and pairwise distinctness, and ranks these words lexicographically. The resulting exact 27-point cyclic rank sequence is

\[
(1,27,18,9,19,10,6,22,13,3,25,16,7,21,12,4,24,15,2,26,17,8,20,11,5,23,14).
\]

The **all_27_ranks_agree** theorem proves that this list is identical to the real-orbit ranks computed from the independently ordered physical orbit. The combinatorial formula and general interpretation come from Baker–Chen–Li–Qian, *Necklaces, permutations, and periodic critical orbits for quadratic polynomials*, *European Journal of Combinatorics* **134** (2026), 104352 ([arXiv:2508.12924v2](https://arxiv.org/html/2508.12924v2), §§2.4, 4.1 and 6.1). This is a formally validated **specific application** of that established mathematics, not a new general kneading theorem.

## 5. A necessary two-scale marking-information criterion

The existing complex polynomial-like construction maps nine physical phases onto three via \(j\mapsto j\bmod3\). This phase map alone does not carry every possible marking. For any type \(\alpha\), any nine-phase label \(L:\mathbb N\to\alpha\), and any purported memoryless downstream label \(g:\mathbb N\to\alpha\), Lean proves

\[
\Big(\forall j<9,\quad L(j)=g(j\bmod3)\Big)
\quad\Longrightarrow\quad L(0)=L(3).
\]

Equivalently, if two markings in one mod-3 fiber are distinguishable, they **cannot** factor faithfully through a phase-only map. This theorem is generic and exact; it identifies a **necessary information condition**, not a geometric contradiction in Kahn–Lyubich. To apply it to actual localization sheets or prime-end accesses, one must *first construct and distinguish the relevant geometric labels*. This remains open in [Issue #12](https://github.com/dovvnloading/loops-research-archive/issues/12).

## 6. Reproduction and proof-safety boundary

Use the repository's pinned Lean 4.32.0 toolchain:

~~~sh
lake build Period27Kneading Period27Dyadic
python research/independent_audits/verify_real_nested_3_9.py
python research/independent_audits/verify_period27_symbolic_atlas.py --check-manifest
python research/independent_audits/verify_period27_kneading_angle_permutation.py
~~~

The main [research validation workflow](../../.github/workflows/lean-proofs.yml) builds the two new modules and rejects all explicit proof holes, while the independent Python regressions continue to check the 224-bit certificate and machine-readable orbit graph.

**What Lean certifies:** the exact signed-integer/fixed-scale arithmetic results and their finite logical/symbolic consequences, as written.

**What Lean does not yet certify:** a general real-number interval arithmetic soundness library, IVT, the mean value theorem, analytic source-germ geometry, actual parameter-component root-ray identification, external-ray landing, prime-end access and sheet/coset transport, paper-specific \(K(f)=J(f)\), or any H1–H4, UPTCR, or MLC gate.

**Next strongest formalization:** prove the generic outward-rounding lemmas in Lean (preferably using a mathematical rational or real-number model with Mathlib) and then rederive the root existence/uniqueness theorem inside Lean. The required geometric KL interface remains a separate complex-dynamics problem.

**AI disclosure:** OpenAI GPT-6 performed code generation, proof development, numerical counterchecking and drafting at the archive steward's direction. GitHub CI confirms Lean compilation and checked proofs, not external expert acceptance. Original published mathematics retains its authors' attribution. No released manuscripts or source-locked ledger statuses are changed.
