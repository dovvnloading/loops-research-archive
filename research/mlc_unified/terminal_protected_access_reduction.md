# Terminal protected-access reduction

## 1. Result and status boundary

This note reduces existence of a terminal proper-access channel to one
exact dynamical incidence statement.  It proves

```text
TERMINAL_ACCESS_SURVIVAL_EQUIVALENCE
```

and originally isolated the proposed positive input

```text
TERMINAL_DYNAMICAL_ACCESS_NONACCUMULATION
```

The subsequent theorem
`TERMINAL_FORWARD_INVARIANT_CARRIER_DENSE_OBSTACLE_NO_GO` proves that
this proposed input is false for the actual proper forward-invariant
terminal Hubbard carrier: the relative obstacle accumulates at every
finite inner prime end.  Thus this note remains a valid equivalence and
a sharp negative diagnostic, but it is not a positive construction
route.  The replacement is the restriction/submulticurve program in
`terminal_dense_obstacle_and_submulticurve_replacement.md`.

The reduction does not prove that a KL submulticurve selected by that
replacement transports as an exact carrier-pair prime end.  It
therefore does not close
`WAVE_TO_KL_ADDRESS_ACCESS_SELECTOR`, VAAPC-I, UPTCR, or MLC.

## 2. Fixed aligned domains

Use the terminal alignment notation
\[
 e:\widetilde A\hookrightarrow\widetilde M,
 \qquad
 \widetilde A
 =
 \widetilde M\setminus\mathscr F_{\rm rel},
\tag{2.1}
\]
where both surfaces are conformal disks and
\[
 \mathscr F_{\rm rel}
 =
 p_{\mathcal T}^{-1}(K\setminus\mathcal T).
\tag{2.2}
\]
Let \(\widetilde{\mathscr F}\subset\widetilde M\) be the complete
closed, or locally finite closed, lifted obstacle ledger, with
\(\mathscr F_{\rm rel}\subset\widetilde{\mathscr F}\).  Its closure in
the prime-end disk is denoted
\[
 \mathscr F^{\rm PE}
 =
 \overline{\widetilde{\mathscr F}}^{
   \,\overline{\widetilde M}^{\,\operatorname{PE}}}.
\tag{2.3}
\]

Fix a nondegenerate compact native interval
\[
 I_0\Subset\widetilde I\subset
 \partial_{\rm PE}\widetilde M.
\tag{2.4}
\]
The compact-half-collar theorem gives an intrinsic one-sided native
collar of \(I_0\).  No relation with \(\widetilde A\) is assumed yet.

## 3. Local equality transfers prime ends

### Lemma 3.1 -- obstacle-free native collar transfer

Suppose a closed one-sided Jordan quadrilateral \(R\) and a topological
embedding
\[
 G_M:R\longrightarrow
 \overline{\widetilde M}^{\,\operatorname{PE}}
\tag{3.1}
\]
have the following properties:

1. the relative interior of the base side maps homeomorphically onto an
   open native arc \(I_R\) containing \(I_0\);
2. \(G_M(R\setminus\text{base})\subset\widetilde M\); and
3. \(G_M(R)\cap\mathscr F^{\rm PE}=\varnothing\).

Then there are a closed one-sided Jordan quadrilateral
\[
 G_A:R\longrightarrow
 \overline{\widetilde A}^{\,\operatorname{PE}}
\tag{3.2}
\]
and an open source ideal arc
\[
 J_A=G_A(\operatorname{relint}(\text{base}))
\tag{3.3}
\]
such that:

- \(G_A=G_M\) on the physical interior after the inclusion
  \(\widetilde A\subset\widetilde M\);
- the physical inclusion has the local compactified extension
  \[
  E_A
  =
  G_M\circ G_A^{-1}:
  G_A(R)\longrightarrow G_M(R);
  \tag{3.4}
  \]
- \(E_A\) is a topological embedding, maps \(J_A\) homeomorphically
  onto \(I_R\), and preserves the two flank sides and their cyclic
  order; and
- \(J_A\) is a certified proper-access arc in the sense of
  Definition 6.1 of `terminal_relative_cover_alignment.md`.

No local connectivity of \(K\), \(\mathcal T\), or either physical
boundary is used.

#### Proof

Choose a uniformization
\[
 \phi_M:\mathbb D\longrightarrow\widetilde M
\]
and put \(A'=\phi_M^{-1}(\widetilde A)\).  The prime-end
compactification of \(\widetilde M\) becomes the closed disk, and
\(G_M(R)\) becomes a closed one-sided Jordan quadrilateral based on a
circle arc.  By hypothesis 3, compactness of \(G_M(R)\), and closedness
of \(\mathscr F^{\rm PE}\), it has a closed-disk neighborhood \(N\)
satisfying
\[
 N\cap\mathscr F^{\rm PE}=\varnothing.
\tag{3.5}
\]
In the disk coordinate, equations (2.1)--(2.3) give
\[
 N\cap\mathbb D\subset A',
\tag{3.6}
\]
and hence local equality with the ambient disk on this neighborhood.

We now construct the source prime ends rather than assume them.  In a
Jordan coordinate on the disk-coordinate image of \(R\), take at every
base point the images of a standard nested family of small
semicircles contained in \(N\).  These are actual crosscuts of the
plane domain \(A'\): their endpoints lie on
\(\mathbb S^1\subset\partial A'\), their interiors lie in \(A'\) by
(3.6), their diameters tend to zero, and their distinguished
components are nested.  They therefore define a prime end of \(A'\)
whose impression is the corresponding singleton of \(\mathbb S^1\).
Distinct base points have disjoint sufficiently small crosscut chains,
so the resulting prime ends are distinct.  The crosscut-chain topology
gives continuous dependence on the base point and preservation of
boundary order.  Transport this construction through the conformal
isomorphism
\[
 \phi_M|_{A'}:A'\longrightarrow\widetilde A.
\]

Adjoin this source prime-end arc to the physical quadrilateral.  The
interior definition and the crosscut-chain topology make the resulting
map \(G_A\) continuous.  It is injective; since \(R\) is compact and
\(\overline{\widetilde A}^{\,\operatorname{PE}}\) is Hausdorff,
\(G_A\) is a topological embedding.  On the physical interior, both
\(G_A\) and \(G_M\) are the same chart into the common domain (3.6).
Hence (3.4) is well defined and is a homeomorphism of the two compact
quadrilaterals.  It maps the base and two flanks as claimed.
Condition (3.5) is exactly the ambient obstacle-closure clause in the
certified-channel definition. \(\square\)

## 4. Exact survival equivalence

### Theorem 4.1
(`TERMINAL_ACCESS_SURVIVAL_EQUIVALENCE`)

For \(I_0\) in (2.4), the following are equivalent.

1. **No obstacle incidence:**
   \[
   I_0\cap\mathscr F^{\rm PE}=\varnothing.
   \tag{4.1}
   \]
2. **Obstacle-separated native collar:** there is a quadrilateral
   \(G_M:R\to\overline{\widetilde M}^{\,\operatorname{PE}}\) satisfying
   Lemma 3.1 and whose native base contains \(I_0\).
3. **Certified source channel:** there is a certified source ideal arc
   \(J_A\) whose ambient native image contains \(I_0\).

When these conditions hold, every nondegenerate compact subinterval of
\(I_0\) that is contained in one finite strip-refinement component has
the local conformal channel-to-KL welding, provided that component has
the required tile-tagged \(\eta/\xi\) label.  A cut point, wrong-side
component, or central component remains an obstruction.  Every
certified component is stable under final-root enlargement by
Theorem 7.2.

#### Proof

\((1)\Rightarrow(2)\).
The sets \(I_0\) and \(\mathscr F^{\rm PE}\) are disjoint, with the
first compact and the second closed by definition (2.3) in the compact
prime-end disk.  This remains true when the interior ledger is only a
locally finite closed union: no finite-subledger reduction is being
made.  Thus \(I_0\) has an open closed-disk collar neighborhood
disjoint from all of \(\mathscr F^{\rm PE}\).  Uniformize
\(\widetilde M\) by the disk.  Since
\(I_0\Subset\widetilde I\), choose
\(\overline{I_R}\Subset\widetilde I\) containing \(I_0\) and then choose
the positive collar thickness small enough that the whole closed
one-sided Jordan quadrilateral lies in that obstacle-free
neighborhood.  This is Item 2.

\((2)\Rightarrow(3)\).
Apply Lemma 3.1.

\((3)\Rightarrow(1)\).
Definition 6.1 requires the compactified image of the certificate
quadrilateral to avoid \(\mathscr F^{\rm PE}\).  Its base image contains
\(I_0\), so (4.1) follows.

The welding and final-root statements are exactly Theorems 6.3, 6.4,
and 7.2 of `terminal_relative_cover_alignment.md`. \(\square\)

## 5. The refuted strong input and the remaining exact endpoint input

### Obligation 5.1
(`TERMINAL_DYNAMICAL_ACCESS_NONACCUMULATION`, refuted as a universal
positive gate)

For every actual proof-used terminal binder, construct a nondegenerate
compact interval
\[
 I_0\Subset I_{1\to0}
\tag{5.1}
\]
such that the complete lifted obstacle ledger satisfies
\[
 I_0\cap
 \overline{\widetilde{\mathscr F}}^{
   \,\overline{\widetilde M}^{\,\operatorname{PE}}}
 =
 \varnothing.
\tag{5.2}
\]
For whole-side use, prove the corresponding statement on every compact
subinterval outside the declared bounded entry, exit, and terminal
defect windows.

This is not a reformulation of the desired KL access label.  It is the
separate dynamical assertion that attachments and other obstacles do
not accumulate on the proof-used native side.  Theorem 4.2 of
`terminal_dense_obstacle_and_submulticurve_replacement.md` proves the
opposite for every proper forward-invariant carrier, and Proposition
2.1 there proves properness in KKL's locally connected native
primitive category.  Hence (5.2) fails on every nondegenerate
candidate interval in that subcategory; non-locally-connected physical
properness is recorded separately there.

Theorem 4.1 remains useful as an exact equivalence: it now certifies
why the strong collar cannot exist.  Width transfer must instead use
the proved KL submulticurve overflow relation, whose next open input is
`TERMINAL_WAVE_KL_CONNECTING_SUBFAMILY`.

### Obligation 5.2
(`TERMINAL_TAGGED_ENDPOINT_ACCESS_MATCH`, open)

For every physical KKL restriction retained by the actual proof-use
binder, compute the ordered endpoint records
\[
 \left(
  \operatorname{EndRec}_{\rm KL}
   (i(L),\overline{\widehat\delta}(0)),
  \operatorname{EndRec}_{\rm KL}
   (i(L),\overline{\widehat\delta}(1))
 \right)
\tag{5.3}
\]
from Theorem 11.4.  Prove that every protected endpoint occurrence
required by the Wave proof:

1. is not in the outer case \(P_O\);
2. is not in the central/buried case \(O_{\rm cent}\);
3. carries the correct tagged occurrence
   \[
   (i,\widehat a)\in
   (\{i_*\}\times\eta_{i_*})
   \sqcup
   (\{i_*+1\}\times\xi_{i_*+1});
   \tag{5.4}
   \]
4. satisfies the binder's ordered endpoint-subordination predicate; and
5. retains every finite incidence germ when more than one tagged access
   meets the same physical vertex.

A proof that the physical impression contains \(v_*\) is insufficient:
it must identify the actual prime-end occurrence and tile tag.  Failure
records the first endpoint tuple in (5.3), including its strip
coordinate, five-way case, and incidence set.

## 6. Adversarial sharpness

The dense one-gate hair continuum in Theorem 12.1 of
`terminal_relative_cover_alignment.md` has a full, connected,
empty-interior enlargement with one gate per attachment, but its
attachment closure meets every nonempty upper base interval.  Thus
(4.1) fails on every candidate interval and Theorem 4.1 correctly
produces no strong protected channel.

The countermodel shows that (5.2) cannot follow from fullness,
empty interior, or one-gate attachment alone.  An actual proof must use
dynamics: effective local finiteness of pullbacks, a separation estimate
in a native collar coordinate, a summable attachment-height bound, or
an equivalent source-locked nonaccumulation mechanism.
