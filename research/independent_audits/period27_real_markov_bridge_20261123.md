# Exact real Markov rows from the physical period-27 quadratic

**Date:** 2026-11-23. **Base source:** `ae21998d70f5f92f4a175d297c7960e94653328d`.
**Subject:** the actual real map $f_c(x)=x^2+c$ at the uniquely isolated period-27 superattracting center.

## Result and scope

[Period27RealMarkov.lean](../../formalization/weighted/Period27RealMarkov.lean)
identifies the 26-edge real Markov table in
[the symbolic-marking manifest](../../results/period27_symbolic_marking.json)
with exact interval images and exact preimage multiplicities of the actual
quadratic. This closes a model-to-physical interpretation that the Python
[spine constructor](verify_period27_symbolic_atlas.py) previously justified
in prose using the certified orbit order.

The theorem concerns this real interval partition. It does not identify
the table with the native KKL tree operator, with the delayed clone graph,
or with a two-sided external-ray Hubbard-tree automaton. It supplies no
extremal-width comparison. Those maps and identifications retain their
separate proof obligations.

The mathematics used here is elementary classical interval dynamics. The
contribution is a project-specific, kernel-checked semantic bridge; no
worldwide novelty claim is made.

## Objects and exact quantifiers

Let $c$ lie in the certified dyadic bracket and satisfy $f_c^{27}(0)=0$.
The existence and uniqueness of such a parameter are independently proved
in [Period27RealExactPeriod.lean](../../formalization/weighted/Period27RealExactPeriod.lean).
The first 27 orbit points have the independently proved order

$$
(1,19,10,16,25,7,13,22,4,6,24,15,9,0,18,12,21,3,5,23,14,8,26,17,11,20,2),
$$

where an entry $j$ denotes $f_c^j(0)$. Write these points as
$v_0<\cdots<v_{26}$ and define the **closed** edges
$E_i=[v_i,v_{i+1}]$, for $0\le i<26$. In particular $v_{13}=0$.

Let $\pi$ be the finite permutation of ranks induced by increasing the
orbit time modulo 27. Define

$$
\ell_i=\min(\pi(i),\pi(i+1)),\qquad
u_i=\max(\pi(i),\pi(i+1)).
$$

The row predicate is exactly

$$
A_{ij}=1\quad\Longleftrightarrow\quad \ell_i\le j<u_i.
$$

For every $i,j<26$ and **every** $y\in(v_j,v_{j+1})$, the new result proves

$$
A_{ij}=1
\quad\Longleftrightarrow\quad
\exists!x\in E_i:\ f_c(x)=y.
$$

If $A_{ij}=0$, the fiber is empty. The separate whole-edge result proves

$$
A_{ij}=1\quad\Longleftrightarrow\quad E_j\subset f_c(E_i).
$$

The target-interior convention is essential to the multiplicity statement:
partition endpoints belong to both adjacent closed edges. There is no
sampling, rounding, or asymptotic quantifier in these conclusions.

## Independently checkable chain

| Transition | Proof input | Constructed map or deduction | Lean declaration |
|---|---|---|---|
| Certified orbit bounds → ordered physical vertices | Existing uniform adjacent real-orbit inequalities | `vertex c i` is the actual iterate at the recorded orbit time | `vertex_strictMono` |
| Finite successor ranks → actual endpoint dynamics | Kernel-checked rank permutation and actual equation $f_c^{27}(0)=0$ | $f_c(v_i)=v_{\pi(i)}$ | `vertex_step` |
| Ordered vertices → genuine monotone branches | Zero is exactly vertex 13 | Each edge is entirely on one side of zero; $x^2+c$ is strictly monotone there | `edge_one_side`, `quadratic_injOn_edge` |
| Endpoint values → image of every interior point | Continuity and strict monotonicity on the actual interval | $f_c(E_i)=[v_{\ell_i},v_{u_i}]$ by the intermediate value theorem | `physical_edge_image` |
| Finite row → entire physical edge coverage, and converse | Strict order of all physical vertices | Interval inclusion iff the endpoint ranks enclose the target edge | `row_iff_physical_edge_covered` |
| Finite row → physical multiplicity, and converse | Exact interval image and branch injectivity | Exactly one preimage on listed interiors and zero on omitted interiors | `row_iff_physical_preimage`, `row_iff_unique_physical_preimage` |
| Abstract parameter premises → instantiated center | Independently established actual period-27 parameter | Produces a real center satisfying all row conclusions | `exists_physical_center_with_markov_rows` |
| Computed rows → archived finite certificate | Kernel reduction of a 27-entry table | All 26 row lists match the displayed manifest rows | `markovRows_exact` |

The declaration `first_edge_omits_first_target` gives a physical negative
check: no interior point of the first target edge has a preimage in the
first source edge. Adding a spurious graph edge changes a mathematically
falsifiable assertion about the actual polynomial.

## Why this is stronger than an arithmetic certificate

The old finite calculation establishes an ordered list and computes the
images of its labels. That does not by itself assert what any point
between the labels does. Here the interval image is proved for every real
point, using the exact orbit identification, continuity, the sign of the
branch, and the intermediate value theorem. Injectivity supplies the
multiplicity one and the converse excludes entries absent from the table.

A physically counted matrix for a different tree still needs its own
vertex/edge map, orientation conventions and multiplicity proof. This
result may be reused only after those objects have actually been
identified with these real intervals.

## Written extension: every finite path counts actual preimages

Write $E_i^\circ=(v_i,v_{i+1})$ and
$I=[v_0,v_{26}]=\bigcup_{i=0}^{25}E_i$.
The exact image theorem gives $f_c(E_i)\subset I$ for every $i$, so
$f_c(I)\subset I$. Every vertex maps to a vertex by `vertex_step`.
No vertex lies in an edge interior: if $v_k\in(v_j,v_{j+1})$, strict
order would force the impossible integer inequalities $j<k<j+1$.

Fix $n\ge0$, $i,j<26$, and $y\in E_j^\circ$. Then

$$
(A^n)_{ij}
=\#\{x\in E_i^\circ:f_c^n(x)=y\}.
$$

**Proof.** For an admissible word $i=i_0,i_1,\ldots,i_n=j$, the Lean
one-step theorem gives a unique backward lift of $y$ into each preceding
closed source edge. Each lift lies in the edge interior: otherwise it
would be a vertex, whose forward image would also be a vertex, contrary
to the next point lying in an edge interior. This constructs one point
$x$ per word. Distinct words give different points, since the forward
orbit of a point is determined and distinct edge interiors are disjoint.
Conversely, any $x\in E_i^\circ$ with $f_c^n(x)=y$ has all intermediate
points in $I$ by forward invariance, and none can be a vertex because
its final image would then be a vertex. Its unique interior itinerary is
admissible by `row_iff_physical_preimage`. This gives a bijection between
length-$n$ admissible words and the displayed fiber. Matrix multiplication
counts those words by induction; for $n=0$ both sides are $1$ if $i=j$
and $0$ otherwise. All fibers are finite, with at most $2^n$ points.

This extension is a written proof using the Lean one-step theorem; its
finite-word induction and cardinality statement are not yet formalized.
It concerns preimages of a specified interior point. It asserts neither
unique infinite symbolic coding nor periodic-point counts nor equality
with topological entropy.

## A spectral correlation visible after the physical bridge

Let $A$ be the row-source, column-destination matrix of these physical
interval preimage multiplicities. The exact certificate proves

$$
\boxed{\det(\lambda I-A)=
(\lambda^2-\lambda-1)(\lambda^6-\lambda^3-1)
(\lambda^{18}-\lambda^9-1).}
$$

This is a different matrix from the archive's primitive delayed clone
graph. Its three strongly connected components are:

| Return clock $s$ | Edge indices in the component | Branch edge | Lengths of its two simple cycles |
|---|---|---|---|
| 1 | 8, 17 | 8 | 1, 2 |
| 3 | 2, 5, 11, 14, 20, 23 | 14 | 3, 6 |
| 9 | 0, 1, 3, 4, 6, 7, 9, 10, 12, 13, 15, 16, 18, 19, 21, 22, 24, 25 | 12 | 9, 18 |

In this order all intercomponent edges go from an earlier block to a later
block, making $A$ block upper triangular. Inside each $2s$-vertex block,
only the branch vertex has two successors; all others have one. Every
vertex reaches the branch, and choosing either branch successor gives a
simple first-return cycle, of length $s$ or $2s$. Thus these are the only
two simple directed cycles and they intersect at the branch.

**Determinant proof.** In the Leibniz expansion of $\lambda I-B_s$,
first expand each diagonal entry $\lambda-B_{ii}$ into its two choices.
Group the resulting terms by vertex-disjoint directed cycles, counting
a selected self-loop as a cycle of length one. The empty cycle collection
contributes $\lambda^{2s}$. The two available cycles intersect, so every
nonempty term uses exactly one. A directed cycle of length $L$ contributes
$-\lambda^{2s-L}$: the permutation sign is $(-1)^{L-1}$ and the selected
adjacency entries supply $(-1)^L$. This also covers the self-loop at $s=1$.
Consequently

$$
\det(\lambda I-B_s)=\lambda^{2s}-\lambda^s-1.
$$

Multiplying the three diagonal-block determinants proves the displayed
factorization. The [spectrum certificate](verify_period27_markov_spectrum.py)
checks the component partition, triangular order, unique branch structure,
all first-return cycles, and the absence of a branch-avoiding cycle.
It independently computes the full characteristic polynomial using exact
integer matrix traces and Newton identities. Its
[manifest](../../results/period27_real_markov_spectrum.json) records both
methods' identical coefficients. This determinant argument is written
mathematics with an exact computational certificate; it is not itself
Lean-formalized.

**What the correlation says.** Put $\varphi=(1+\sqrt5)/2$. For each
$s\in\{1,3,9\}$, the factor splits according to

$$
\lambda^s=\varphi\quad\text{or}\quad\lambda^s=-\varphi^{-1}.
$$

Its roots therefore lie on the two circles of radii
$\varphi^{1/s}$ and $\varphi^{-1/s}$, with exactly $s$ roots on each.
The whole matrix has spectral radius $\varphi$, but the smaller
spectral circles retain the return clocks 3 and 9. The single leading
eigenvalue loses information that is visible in the full spectrum.
This provides a concrete test of using a scalar growth rate as a complete
multiscale invariant: the 2-, 8-, and 26-dimensional leading block
truncations all have the same leading spectral radius while retaining
different finite return structures.

The 2- and 6-vertex components have outgoing edges to later blocks;
only the 18-vertex component is closed. Thus the full matrix is reducible.
In the row-source convention, an eigenvector for $\varphi$ vanishes on
the downstream blocks, so it does not provide an everywhere-positive
normalization of the full matrix to a Markov chain. A stochastic law on
a restricted block concerns paths surviving in that block. These graph
periods are not, by themselves, a proof about periods of a physical
invariant probability measure.

### Independent set-level identification of the return scales

The scale agreement can be verified from actual interval images, without
inferring geometry from the characteristic polynomial. Define

$$
I_k=[v_{9k},v_{9k+8}]\quad(0\le k<3),\qquad
J_k=[v_{3k},v_{3k+2}]\quad(0\le k<9).
$$

These are unions of, respectively, eight or two consecutive partition
edges. Within each family the intervals are pairwise disjoint because
strict gaps separate their endpoints. Exact unions of the certified rows
give

$$
f_c(I_k)=I_{\alpha(k)},\quad \alpha=(2,0,1),
\qquad
f_c(J_k)=J_{\beta(k)},\quad \beta=(8,7,6,1,0,2,3,4,5).
$$

Both permutations are single cycles of the declared lengths. Each fine
interval satisfies $J_k\subset I_{\lfloor k/3\rfloor}$, and the finite
identity

$$
\lfloor\beta(k)/3\rfloor=\alpha(\lfloor k/3\rfloor)
$$

shows that the inclusions commute with the actual interval maps. The
central intervals are $I_1=[v_9,v_{17}]=[f_c^6(0),f_c^3(0)]$ and
$J_4=[v_{12},v_{14}]=[f_c^9(0),f_c^{18}(0)]$.

**Proof boundary.** The verifier checks the exact finite unions, cycles,
and refinement identity. The physical statement follows because image
commutes with finite union and `physical_edge_image` identifies each edge
image. This is a written set-level application of the Lean theorem.
It constructs these real interval cycles; it does not assert any complex
collar, proper holomorphic restriction, prime-end marking, or width bound.

The cycle clocks 1, 3, 9 agree with the archive's previously certified
nested return scales. The exact identity above is derived directly from
the actual interval matrix; its proof does not assume that this agreement
identifies any additional complex domains, marked surfaces, or widths.
Any such analytic identification requires its own theorem.

### Exact Fibonacci counts in physical inverse fibers

There is also a direct all-horizon assertion about the polynomial, without
an entropy interpretation. Let $(s,b)$ be $(1,8)$, $(3,14)$ or $(9,12)$,
and let $F_0=0$, $F_1=1$, $F_{m+2}=F_{m+1}+F_m$. For every
$y\in E_b^\circ$ and every integer $m\ge0$,

$$
\#\{x\in E_b^\circ:f_c^{ms}(x)=y\}=F_{m+1}.
$$

If $n$ is not divisible by $s$, the corresponding $n$-step fiber is empty.
Indeed, a path leaving the component cannot return because the component
graph is acyclic. Every path returning to its branch splits uniquely at
successive branch visits into one of the two first-return cycles, of
lengths $s$ and $2s$. After dividing lengths by $s$, the count is the
number of compositions of $m$ into ones and twos: it has initial values
$1,1$ and the Fibonacci recurrence. The physical preimage-path bijection
proved above transfers this count to the actual polynomial. The statement
includes $m=0$, when the only point is $y$ itself.

This all-horizon counting result is a written consequence of the Lean
one-step bridge and the exact return-cycle structure. The Fibonacci/path
induction is not presently a Lean declaration. It exhibits three physical
inverse-branch clocks with the same normalized Fibonacci law; it does not
construct a new complex restriction or a marked-width estimate.

**Prior art and novelty scope.** Spectral and kneading descriptions of
interval dynamics are classical: see Milnor and Thurston,
[*On iterated maps of the interval*](https://websites.umich.edu/~kochsc/MilnorThurston.pdf),
and Rugh and Tan,
[*Kneading with weights*](https://doi.org/10.4171/JFG/24).
Lindsey, Tiozzo and Wu,
[*Master Teapots and Entropy Algorithms for the Mandelbrot Set*](https://arxiv.org/abs/2112.14590),
Lemma 9.1 gives a tuning factorization of kneading polynomials; Appendix
Proposition 11.4 relates the actual real postcritically finite Markov
matrix determinant to a kneading numerator. These are close prior art,
not evidence that the general connection is new.
The project-specific contribution is this exact three-factor certificate
for the archived physical period-27 spine and the proved map-to-matrix
identification. This is not evidence that the factorization phenomenon is
unknown in the literature. We make no claim of a new entropy theorem.
Identifying $\log\rho(A)$ with the topological entropy of an interval
restriction would require stating and checking the hypotheses of the
appropriate Markov/monotone interval-map theorem separately.

## Reproduction

With the pinned Lean 4.32.0 and mathlib version, in `formalization/weighted`:

```bash
lake build Period27RealKneading
lake env lean Period27RealMarkov.lean
```

From the repository root, reproduce the exact finite spectral certificate:

```bash
python research/independent_audits/verify_period27_markov_spectrum.py --check-manifest
```

The file prints the axioms of the physical image, row equivalence,
preimage multiplicity, negative check, finite row calculation, and
instantiated-center theorem. Verification status is recorded by the build
output; merely reading this note is not a successful Lean run.

Prepared with OpenAI GPT-6 Astra Pro assistance, including a separate
adversarial review of the interval and matrix arguments. No human
specialist review was performed during this preparation.
