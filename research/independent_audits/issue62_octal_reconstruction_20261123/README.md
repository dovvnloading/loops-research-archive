# Exact reconstruction of the physical fine-landing sets

**2026-11-23 (America/New_York). Written analytic theorem with an exact
arithmetic certificate.** This continues the
[one-third dimension proof](../issue62_landing_angle_bound_20261123/EXACT_DIMENSION.md)
by determining the actual sets themselves. The decisive step is entropy
rigidity of the full two-symbol shift, applied after a physical inverse-fiber
argument. Equality of a symbolic survivor and a landing set is proved here;
it is not an input.

## 1. The actual sets, explicitly

Retain the archive's actual parameter, quadratic-like return
\(G=f_{c_*}^3\), normalized landing map
\(L:\mathbb T\to K3\), and three disjoint physical intervals

\[
C_0=K9,\qquad C_1=G(C_0),\qquad C_2=G^2(C_0),
\qquad G(C_j)=C_{j+1\pmod3}.
\]

Put \(E_j=L^{-1}(C_j)\), \(E=E_0\cup E_1\cup E_2\), and
\(d(\theta)=2\theta\pmod1\). Define the compact octal Cantor set

\[
\mathcal C=
\left\{\sum_{n\ge1}\frac{a_n}{8^n}:a_n\in\{3,4\}\right\}.
\tag{1}
\]

**Theorem.** In the actual normalized \(G\) external-angle coordinate,

\[
\boxed{
E_1=\mathcal C,\qquad
E_0=\frac{\mathcal C}{2}\cup\frac{\mathcal C+1}{2},\qquad
E_2=\frac{\mathcal C}{4}\cup\frac{\mathcal C+3}{4}.
}
\tag{2}
\]

For the four original open seams

\[
I_0=(41/192,43/192),\quad I_1=(53/192,55/192),\quad
I_2=(137/192,139/192),\quad I_3=(149/192,151/192),
\]

the complete actual root subsets \(A_i=E_0\cap I_i\) are

\[
\boxed{A_i=(\mathcal C+t_i)/16,
\qquad(t_0,t_1,t_2,t_3)=(3,4,11,12).}
\tag{3}
\]

| Actual root subset | Affine description | Exact hull endpoints |
|---|---|---|
| \(A_0\) | \((\mathcal C+3)/16\) | \([3/14,25/112]\) |
| \(A_1\) | \((\mathcal C+4)/16\) | \([31/112,2/7]\) |
| \(A_2\) | \((\mathcal C+11)/16\) | \([5/7,81/112]\) |
| \(A_3\) | \((\mathcal C+12)/16\) | \([87/112,11/14]\) |

Each hull lies strictly inside its original open seam. These formulas describe
all irrational as well as rational landing angles. They are not just hulls:
the intervening Cantor gaps are part of the theorem.

## 2. Physical inputs and exact inverse fibers

The physical inputs are already written in the archive and are independent
of (1):

1. The connected central return is proper of degree two, with sole critical
   point \(0\); its filled set is \(K3\). Its fine intervals are the actual
   three-cycle specified above.
2. The normalized continuous landing map is onto and satisfies
   \(L\circ d=G\circ L\). The real-symmetric straightening and evenness of
   \(G\) give
   \(L(\theta+1/2)=-L(\theta)\).
3. The source-sector theorem exhausts the actual root accesses:
   \(E_0\subset I=I_0\cup I_1\cup I_2\cup I_3\).
4. The actual return \(G^3|C_0\) straightens to \(x\mapsto x^2-2\), and
   \(G^2:C_1\to C_0\) is a homeomorphism intertwining the return maps.

The exact physical locators and their hypotheses appear in
[the dimension proof, §§1–3 and 7](../issue62_landing_angle_bound_20261123/EXACT_DIMENSION.md).
In particular the actual Chebyshev identification is
[the interval-root proof, §3](../tip_interval_root_and_marked_morphism_obstruction_20261106.md);
the normalization and symmetry are
[the terminal-first-child proof, §§3 and 7](../tip_kl_terminal_first_child_20261106.md);
and the complete sector statement is
[the C4 source theorem, Lemma 5.1 and Theorem 5.2](../tip_native_C4_wake_root_sheet_naturality_20261109.md).
The rational seam data are read from stage `G`, piece `W`, in
`results/tip_kl_side_atlas.json`. Numbers in that file do not establish
these analytic inputs.

**Phase-surjectivity lemma.**

\[
d(E_j)=E_{j+1\pmod3}.
\tag{4}
\]

**Proof.** Inclusion follows from semiconjugacy. For the reverse inclusion,
take \(\theta\in E_{j+1}\) and choose \(x\in C_j\) with
\(G(x)=L(\theta)\). Such an \(x\) exists by the actual onto phase map.
For either half-angle \(\eta\) of \(\theta\), put \(u=L(\eta)\).
Then

\[
G(u)=G(-u)=L(\theta),\qquad L(\eta+1/2)=-u.
\]

The points \(u,-u\) belong to \(K3\). If they are distinct, the proper
degree-two restriction has no third preimage there. If \(u=0\), its critical
multiplicity is two and again exhausts the fiber. Since \(x\in K3\), it
equals one of these points. The corresponding half-angle belongs to
\(E_j\). This proves (4). The argument counts preimages in the actual
degree-two central restriction, not all eight roots of the polynomial
equation \(f_{c_*}^3(z)=L(\theta)\). \(\square\)

This supplies actual surjectivity, rather than assuming that forward
invariance of a landing set implies it. It uses no bound on the cardinality
of an individual landing fiber.

## 3. Entropy forces every allowed octal sequence to occur

By (4) and the complete source-sector inclusion,

\[
E_1=d(E_0)\subset d(I)
=(41/96,43/96)\cup(53/96,55/96).
\tag{5}
\]

The first interval is strictly inside \((3/8,4/8)\), and the second is
strictly inside \((4/8,5/8)\). The map
\(T=d^3\) is multiplication by eight and preserves \(E_1\). Applying
(5) to every \(T^n\theta\) shows that every octal digit of each
\(\theta\in E_1\) is 3 or 4. No terminating-octal ambiguity occurs:
such an angle eventually maps to zero, outside (5). Thus

\[
E_1\subset\mathcal C.
\tag{6}
\]

The coding map from \(\{3,4\}^{\mathbb N}\) to \(\mathcal C\) is a
homeomorphism conjugating the left shift to \(T\). The two first-level
compact cylinders are separated, and the diameter of a cylinder of length
\(n\) is \(8^{-n}/7\).

The actual conjugacy in input 4 gives
\(h_{\rm top}(G^3|C_1)=\log2\). Since the actual map
\(L:E_1\to C_1\) is an onto factor for \(T\) and \(G^3\),

\[
h_{\rm top}(T|E_1)\ge\log2.
\tag{7}
\]

Here is the elementary entropy-rigidity argument needed to turn (6) into
equality. A proper closed forward-invariant subset of the full two-symbol
shift misses some cylinder word of length \(m\). Forward invariance then
forbids this word at every position. Counting just the disjoint blocks of
length \(m\) bounds the number of length-\(n\) words by

\[
2^{m-1}(2^m-1)^{\lfloor n/m\rfloor}.
\]

Consequently its entropy is at most
\(m^{-1}\log(2^m-1)<\log2\). This contradicts (7) if the compact
set \(E_1\) is a proper subset of \(\mathcal C\). Therefore
\(E_1=\mathcal C\).

This is an application of the classical entropy-minimality principle,
with the required special case proved above. It does not use an assumption
that the earlier 96-state graph realizes physical rays.

## 4. Recovering every phase, seam, and gap

The symmetry \(C_0=-C_0\) and the half-turn formula imply
\(E_0+1/2=E_0\). Equation (4) therefore gives the *full* inverse image
\(E_0=d^{-1}\mathcal C\), the first formula for \(E_0\) in (2).
The two defining similarities of \(\mathcal C\) are

\[
\phi_3(x)=(x+3)/8,\qquad\phi_4(x)=(x+4)/8.
\tag{8}
\]

Doubling their images modulo one gives the formula for \(E_2\) in (2).
Splitting the two halves of \(E_0\) using (8) gives (3).

The hull of \(\mathcal C\) is \([3/7,4/7]\). Its central gap is

\[
J=(25/56,31/56).
\tag{9}
\]

Every component of \([3/7,4/7]\setminus\mathcal C\) is exactly
\(\phi_w(J)\), where \(w\) is a finite word over \(\{3,4\}\).
At level \(k\) there are \(2^k\) gaps, each of length
\(3/(28\cdot8^k)\). Their total length is

\[
\sum_{k\ge0}2^k\frac3{28\cdot8^k}=\frac17,
\]

the full hull length. Formula (3) transports this complete gap list to
each actual root subset. In particular a point belongs to \(A_i\) exactly
when the octal digits of \(16\theta-t_i\) are all 3 or 4. For a rational
angle this is a terminating exact decision procedure: its remainder orbit
either encounters a forbidden digit or repeats.

The earlier *full* 96-state survivor contains additional transient points
and must still not be equated with \(E\). For example \(3/56\) is in its
allowed region and doubles to \(3/28\in E_2\), so it survives forever;
yet \(3/56\notin E\) by (2). The actual set is exactly the survivor
carried by the 32-state recurrent graph component. Here “recurrent”
describes the graph states, not recurrence of every individual angle.
The new verifier independently reconstructs this induced graph from (2),
using entire Cantor-cylinder hulls, and checks its 32 vertices and 40 edges.

There is also a direct proof of equality of the complete infinite
survivors, beyond equality of their one-step edge tables. The core edges
cycle through the three phase cell families. Every phase-1 core cell is
inside octal digit cell 3 or 4. An orbit staying in the core therefore
has every third phase-1 iterate there, so its phase-1 angle belongs to
\(\mathcal C\). At phase 0, \(d\theta\in\mathcal C\) implies
\(\theta\in d^{-1}\mathcal C=E_0\). At phase 2,
\(d^2\theta\in\mathcal C\), and the core cells lie only in quarter
cells 0 and 3; hence \(\theta\in\mathcal C/4\cup(\mathcal C+3)/4=E_2\).
Conversely, the complete cylinder enclosures put every actual phase and
its image in the corresponding core cells. This proves both inclusions.
The induced core graph can have exits to dead states in the full graph;
it is not asserted to be a closed component of that larger graph.

## 5. Quantitative and path-theoretic consequences

The companion [measure and trace proof](MEASURE_AND_TRACE.md) derives
positive finite one-third-dimensional Hausdorff measure, explicit Ahlfors
regularity, and positive logarithmic capacity for these *actual* sets.
For the convention using sums of diameter powers,

\[
\mathcal H^{1/3}(\mathcal C)=7^{-1/3},\qquad
\mathcal H^{1/3}(A_i)=112^{-1/3}.
\tag{10}
\]

The positive capacity is relevant: zero angular length does not permit
discarding these roots in a finite-energy boundary argument. The companion
also separates the intrinsic angular trace operator from any unproved
comparison with physical planar Dirichlet energy.

The exact root domains and rational gap endpoints provide physical cuts
for the [connector reconstruction](../issue62_physical_connector_reconstruction_20261123/NOTE.md).
That companion must still identify each actual KL path, based meridian,
and unwrapped deck coordinate before assigning a connector word; an octal
address alone is not a based path.

## 6. Reproduction, dependencies, and scope

Run from the repository root:

```sh
python -B research/independent_audits/issue62_octal_reconstruction_20261123/verify.py --check-certificate
```

The program uses exact rational arithmetic to read the physical seam atlas,
check the doubling and octal branch inclusions, recover all four seam hulls,
decide the rational cut/anchor addresses, and independently reconstruct the
recurrent graph. Its committed certificate does not certify entropy,
Carathéodory landing, or the analytic proper-degree hypotheses. Those steps
are the written arguments above and the named physical source theorems.

All metric conclusions use the stated external-angle coordinate. No
arbitrary-boundary dimension, physical Dirichlet norm equivalence, general
KKL geometric-trace restriction, or MLC conclusion is inferred.

Prepared with OpenAI GPT-6 Astra Pro for proof development, exact arithmetic,
and independent adversarial review. Entropy minimality and the underlying
Chebyshev and landing theorems are classical inputs. Human specialist
review and a Lean formalization of the new analytic arguments remain
outstanding.
