# Finite support automaton for nonstationary corridors

## 1. Status

`corridor_entropy_shear_dichotomy.md` classifies one homogeneous layer transfer but
leaves changing Frobenius flags open. This note proves a finite pumping reduction for
a nonstationary bounded-dimensional transfer language.

The reduction does not discard repeated loops. It isolates them: an arbitrary corridor
word becomes a uniformly short Boolean-support skeleton with loop words inserted.
Numerical entropy or polynomial shear can accumulate only inside those retained loops.

Constructing the required finite automaton from a virtual Julia-set hull remains open.
`virtual_language_memory.md` proves that exact corridor and first-return lengths may
require explicit unbounded counters, while ordered nesting may require an explicit
word or stack. The pumping theorem here applies only after every memory-changing run
has been compiled into an exact typed checkpoint macro, or the pumping summary has
been enlarged by a finite memory congruence whose repetitions act identically on
every relevant reachable fiber. Post-hoc selection of “the safe loop” does not
satisfy this hypothesis, and every loop emission remains recorded.

## 2. Labeled transfer automaton

Let \(\mathcal A\) be a finite directed automaton with state set \(Q\),
\[
  |Q|=s.
\]
Every directed edge \(e\) is labeled by a nonnegative integer matrix
\[
  B_e\in M_d(\mathbb Z_{\ge0}).
\]
The matrices use the source-column convention of
`corridor_entropy_shear_dichotomy.md`: column \(j\) lists multiplicities leaving
source \(j\), column states evolve by left multiplication, and all automaton states
carry their endpoint core frame.
For an accepted path
\[
  w=e_1e_2\cdots e_m,
\]
write
\[
  P(w)=B_{e_m}\cdots B_{e_1}.
\tag{2.1}
\]

For a nonnegative matrix \(B\), let
\[
  \operatorname{supp}(B)_{ij}
  =
  \begin{cases}
    1,&B_{ij}>0,\\
    0,&B_{ij}=0.
  \end{cases}
\]
Products of \(0\)-\(1\) supports below use Boolean multiplication:
\[
  (S\odot T)_{ij}
  =
  \bigvee_k(S_{ik}\wedge T_{kj}).
\]

### Lemma 2.1 (support functor)

For nonnegative matrices \(A,B\),
\[
  \operatorname{supp}(AB)
  =
  \operatorname{supp}(A)\odot\operatorname{supp}(B).
\tag{2.2}
\]

**Proof.** The \((i,j)\)-entry of \(AB\) is positive exactly when some \(k\) has
\(A_{ik}>0\) and \(B_{kj}>0\). There is no cancellation because every summand is
nonnegative. \(\square\)

Thus a path prefix is summarized, at the support level, by the pair
\[
  \bigl(q_k,S_k\bigr)
  \in
  Q\times\{0,1\}^{d\times d},
\tag{2.3}
\]
where \(q_k\) is its automaton state and
\[
  S_k=\operatorname{supp}(P(e_1\cdots e_k)).
\]
There are at most
\[
  N_{\rm sup}=s\,2^{d^2}
\tag{2.4}
\]
such pairs.

## 3. Support-loop pumping

### Theorem 3.1 (finite support skeleton)

Every accepted path of length at least \(N_{\rm sup}\) has a factorization
\[
  w=\alpha\beta\gamma,
\qquad
  |\beta|>0,
\tag{3.1}
\]
such that:

1. \(\alpha\) and \(\alpha\beta\) end at the same automaton state;
2. their transfer products have the same support:
   \[
     \operatorname{supp}P(\alpha)
     =
     \operatorname{supp}P(\alpha\beta);
   \tag{3.2}
   \]
3. the shortened word \(\alpha\gamma\) is accepted and has the same final product
   support as \(w\).

Iterating this operation writes any accepted path as a path of length at most
\(N_{\rm sup}-1\) with finitely many such **prefix-face-neutral loop occurrences**
inserted.

**Proof.** The path has \(|w|+1>N_{\rm sup}\) prefix pairs (2.3), so two are equal.
Let them occur immediately before and after the nonempty subword \(\beta\). Equality
of the automaton states allows the path to be spliced after deleting \(\beta\).
Equality of the prefix supports, followed by Lemma 2.1 applied to the same suffix
\(\gamma\), proves equality of the final supports.

Each deletion strictly shortens the word. Continue until all prefix pairs are
distinct; the remaining skeleton then has at most \(N_{\rm sup}-1\) edges. Restoring
the deleted factors in reverse deletion order represents the original word by a
nested insertion history at the recorded prefix pairs. The loop occurrences cannot
in general be reordered or moved to another support face. \(\square\)

The numerical matrix \(P(\beta)\) is not removed from the dynamics. Only the finite
support skeleton is compressed.

## 4. Bounded witnesses for support entropy

Call a \(0\)-\(1\) support matrix **branch-recurrent** if one of its diagonal
components is a **cyclic strongly connected component**—it contains a
positive-length closed walk—but is not a single directed cycle. An acyclic singleton
zero block is transient and is not branch-recurrent.

### Theorem 4.1 (bounded bad-support witness)

If the automaton accepts any word \(w\) for which
\(\operatorname{supp}P(w)\) is branch-recurrent, then it accepts such a word of length
at most
\[
  N_{\rm sup}-1.
\tag{4.1}
\]

**Proof.** Choose a shortest accepted word with branch-recurrent final support. If
two prefix pairs repeat, Theorem 3.1 deletes the intervening loop and produces a
shorter accepted word with exactly the same final support, a contradiction. Hence all
prefix pairs are distinct, giving (4.1). \(\square\)

### Corollary 4.2 (algebraic support branching gives a Perron gap)

For every branch-recurrent accepted product \(P\),
\[
  \rho(P)\ge2^{1/d}.
\tag{4.2}
\]

**Proof.** A branch-recurrent strongly connected diagonal component is an irreducible
integer matrix that is not a cycle permutation. Theorem 3.1 of
`corridor_entropy_shear_dichotomy.md` gives the bound on that component. The spectral
radius of a block upper triangular matrix is the maximum of the spectral radii of its
diagonal blocks. \(\square\)

Equation (4.2) is a bare matrix statement in the displayed frame. It is not an
intrinsic entropy certificate for an open word: independent relabeling of its target
can change the spectral radius. Dynamical use requires a closed repeatable word
returning to the same framed automaton state, or a canonical source-licensed endpoint
identification. Applying KKL Value additionally requires that the resulting
endomorphism be the source-licensed primitive core transition and that its
WAD-to-core incidence and outgoing error be controlled.

## 5. What the pumping theorem leaves

If no accepted support is branch-recurrent, the finite skeleton is entropy-tame at the
support level. The inserted loops can nevertheless have unbounded numerical effect.

For
\[
  S=
  \begin{pmatrix}1&1\\0&1\end{pmatrix},
\]
the support of \(S^m\) is already constant for every \(m\ge1\), so every additional
copy is a support-neutral loop. Numerically,
\[
  S^m=
  \begin{pmatrix}1&m\\0&1\end{pmatrix}.
\]
The pumping theorem correctly preserves this loop; deleting it numerically would
erase the shear obstruction.

Changing flags can instead create a short branch-recurrent word. The upper and lower
unipotent shears
\[
  U=
  \begin{pmatrix}1&1\\0&1\end{pmatrix},
  \qquad
  L=
  \begin{pmatrix}1&0\\1&1\end{pmatrix}
\]
have a positive product \(LU\), detected within two steps.

Thus the nonstationary problem is reduced only to classifying the ordered semigroup
of contextual prefix-face-neutral loop occurrences:

1. closed, framed, source-licensed positive-entropy returns;
2. common-flag polynomial shears;
3. transient/extinction loops;
4. loops whose changing flags create a bounded branch-recurrent framed return.

The theorem bounds the Boolean skeleton, not the number or length of inserted loop
occurrences, their numerical entries, or their changing frame sequence.

## 6. Virtual support-automaton realization

### Virtual Support Automaton (`OPEN`)

Assume the Virtual Core-Cocycle Realization, Uniform Counter/Stack-Follower,
Uniform Core/WAD Dimension, and Memory-Safe Pumping Compilation theorems. After all
exact unbounded clocks are represented by universally many restricted counters, all
future-relevant ordered nesting data are retained explicitly, and memory-changing
runs are compiled at one fixed trace resolution, every virtual-Molecule corridor
admits a finite-horizon core-transfer automaton with universal \(s,d,w\) such that:

1. every actual core layer and every WAD-to-core incidence is represented by an
   accepted edge; for the raw source-to-target incidence
   \(N_{\beta\gamma}\), the project source-column map is
   \(B=N^{\mathsf T}\), and the KKL Value weights satisfy the corresponding typed
   left/right equations without relying on the source's ambiguous \(T_F\) symbol;
2. automaton concatenation is exactly the permitted dynamical concatenation, not a
   language enlargement, and every state carries enough endpoint frame/holonomy data
   to distinguish open transfers from closed returns;
3. every compressed WAD branch satisfies
   \(P_{\rm out}R_\gamma=\bar R_\gamma P_{\rm in}\), and the complete fixed family
   of future WAD/core/Value/error/shear observations factors through the quotient;
4. every pumped loop is safe on its reachable counter/stack fiber in the sense of
   `virtual_language_memory.md`, all of its emissions remain in the ordered record,
   and every support-neutral loop is either grouped
   into a closed, repeatable, source-licensed positive-entropy primitive block,
   routed to transient extinction, or preserves a common finite Frobenius flag;
5. every common-flag shear coefficient is uniformly normalized and is sectorially
   regularized or transported in the finite shear moment state;
6. the finite-horizon selected correspondence contains every edge and loop used by
   the grouping.

With this theorem, Theorem 3.1 reduces arbitrary corridor length to finitely many
support skeleton types plus the loop analysis in Items 4--5. It is the precise
nonstationary input to the Virtual Corridor Transfer Trichotomy.

## 7. Adversarial audit

The reduction fails if:

1. the automaton admits concatenations not realized by the dynamics;
2. transfer dimension or automaton state count depends on satellite depth;
3. two prefixes have the same support but different future admissibility and are
   assigned the same automaton state;
4. finite-control pumping is invoked after counters or stack words are merely
   projected away;
5. Boolean support is used for matrices with cancellation;
6. a branch-recurrent product is credited with Value contraction before closure,
   endpoint-frame identity, source identity, and primitivity are proved;
7. a common Frobenius flag is inferred from the individual flags of its letters;
8. a transient zero component is classified as branching;
9. contextual loop occurrences are reordered or treated as a finite list;
10. an open word is assigned spectral entropy that changes under target relabeling;
11. a bounded signature catalog is used to infer bounded core or WAD dimension;
12. WAD output observability is used without a transport-quotient commuting square;
13. a memory-neutral loop's numerical, critical, WAD, Value, error, or shear
    emissions are discarded.

Theorem 3.1 is exact only because the automaton state and the entire prefix support are
both retained.
