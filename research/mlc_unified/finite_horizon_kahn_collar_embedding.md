# Finite-horizon Kahn-collar pseudo-piece embedding

## 1. The conditional theorem

### Theorem 1.1 — finite-horizon coherent collar embedding

Let

\[
 \mathbf Y_N
 \xrightarrow{\iota_{N-1}}
 \mathbf Y_{N-1}
 \longrightarrow\cdots\longrightarrow
 \mathbf Y_1
 \xrightarrow{\iota_0}
 \mathbf Y_0
\tag{1.1}
\]

be a fixed finite chain of inclusion-induced pseudo-piece immersions.  For
each \(j=0,\ldots,N-1\), assume:

1. **Central embedding.**  The source central piece maps holomorphically
   and injectively into the target central piece.
2. **Component bijection.**  The finite source-to-target tile-component
   map is bijective.
3. **Kahn annulus data.**  Every tile map is a lift of one base-annulus
   immersion
   \[
     I_j:\mathbb A(1,r_j^{1/d_j})
     \longrightarrow \mathbb A(1,r_j),
     \qquad d_j\in\mathbb Z,\quad d_j\geq2,\quad r_j>1,
   \]
   which is holomorphically immersive, extends continuously to the inner
   circle, and has oriented degree one there.  These are compatible
   uniformizations of the chain annuli
   \(A_{j+1}\) and \(A_j\), respectively.
4. **Exact gluing.**  The central/tile overlap maps commute with the
   corresponding base and universal-cover projections, all overlap maps
   are embeddings, and the only quotient identifications are the declared
   central/tile gluing identifications.
5. **Collar overlap reflection.**  On the Kahn collar adjacent to the
   inner end, the inverse image under each selected tile lift of the
   target central/tile overlap is exactly the declared source
   central/tile overlap.  If \(O^t_{j,\alpha}\) and
   \(O^s_{j,\alpha}\) are the overlaps in a corresponding target and
   source tile, then
   \[
     L_{j,\alpha}^{-1}(O^t_{j,\alpha})
     \cap\widetilde\Lambda'_{j+1,\alpha}
     =
     O^s_{j,\alpha}
     \cap\widetilde\Lambda'_{j+1,\alpha}.
   \tag{1.2}
   \]
   This equality is assumed before shrinking and is preserved by
   restriction.

Then there are coherent open inner collars

\[
 C_j\subset A_j,\qquad j=0,\ldots,N,
\tag{1.3}
\]

such that

\[
 I_j:C_{j+1}\xrightarrow{\;\cong\;}C_j
\tag{1.4}
\]

is biholomorphic for every \(j\).

Form \(\mathbf Y_j^{\mathrm{col}}\) by retaining the open central piece,
the lifts of \(C_j\) in every declared tile, and their declared overlaps.
Then every restricted map

\[
 \iota_j^{\mathrm{col}}:
 \mathbf Y_{j+1}^{\mathrm{col}}
 \hookrightarrow
 \mathbf Y_j^{\mathrm{col}}
\tag{1.5}
\]

is a holomorphic embedding.  Consequently the finite composite

\[
 F_H=
 \iota_0^{\mathrm{col}}\circ\cdots\circ
 \iota_{N-1}^{\mathrm{col}}:
 \mathbf Y_N^{\mathrm{col}}
 \hookrightarrow
 \mathbf Y_0^{\mathrm{col}}
\tag{1.6}
\]

is a holomorphic embedding.

This theorem is conditional on the five stated finite-horizon hypotheses.
For a fixed direct-decoration pair, the already proved gluing criterion
supplies clauses 1 and 2 and the declared-quotient part of clause 4 once
the tile restrictions are injective.  Clause 3 assumes the actual annulus,
immersion, modulus, and boundary-degree data; applying Kahn's lemma to
those data supplies the adjacent injective collar used below.  Neither
source supplies the overlap-reflection equality in clause 5; it is an
explicit additional analytic hypothesis.  The exact necessary quotient
condition is relative overlap cartesianity over the source-central image;
clause 5 assumes the stronger full equality as a convenient sufficient
form.  The full-tile correction in
`kl_relative_overlap_cartesianity.md` does not remove this collar
hypothesis: the canonical comparison point may lie outside the retained
collar, where collar injectivity says nothing.
The theorem does not identify these truncations with the full KL
pseudo-pieces.

The forced-collision theorem in
`kl_canonical_localization_forced_collision.md` makes this distinction
essential rather than provisional.  At a full canonical primitive stage,
the localized inclusion is noninjective because

\[
 a_*^{-1}(H_t)\supsetneq H_s.
\tag{1.6a}
\]

There is no contradiction with Theorem 1.1: that theorem retains only
collars on which injectivity and collar-relative overlap reflection are
assumed and proved.  It makes no assertion that the discarded full-annulus
sheets are absent or harmless.  The universal full-canonical embedding
route is therefore unavailable; a collision-free retained collar remains
a valid conditional local tool only when every discarded localization
coset is carried in the defect ledger.

### Theorem 1.2 — exact marked safe set

In addition to Theorem 1.1, assume:

1. \(\mathbf Y_N^{\mathrm{col}}\) and
   \(\mathbf Y_0^{\mathrm{col}}\) are conformal disks;
2. \(F_H\) extends continuously to their conformal prime-end
   compactifications; and
3. the complete pointwise complement-access footprint
   \(\Phi_H(p)\) is supplied for every source prime end in the asserted
   domain of the safe-set formula.

For a connected target ideal interval \(I\), define

\[
 \operatorname{Safe}_H(I)
 =
 \{p:\Phi_H(p)\subset I\}.
\tag{1.7}
\]

Then a connected source ideal set \(C\) is KKL-admissible for \(I\) if
and only if

\[
 C\subset\operatorname{Safe}_H(I).
\tag{1.8}
\]

Hence the maximal connected KKL-admissible sets are exactly the connected
components of \(\operatorname{Safe}_H(I)\).  There is a unique maximal
connected admissible set only after one proves that the safe set is
connected or selects one distinguished seed component.

The footprints in (1.7) need not be finite.  Finiteness of the horizon and
finiteness of the tile-component set do not imply finite access incidence.

## 2. Source lock

The local analytic input is Kahn I:

```text
.tmp_kl06_source/psiql2.tex
SHA256 E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228
```

The annulus lemma is `psiql2.tex`, lines 87--131.  In its proof, lines
118--130:

1. choose a sufficiently thin target collar \(\Lambda\);
2. take the component \(\Lambda'\) of \(I^{-1}(\Lambda)\) adjacent to the
   inner circle;
3. prove
   \[
     I:\mathbb T\cup\Lambda'
     \longrightarrow
     \mathbb T\cup\Lambda
   \]
   is a degree-one covering; and
4. conclude that \(I|_{\Lambda'}\) is an embedding.

The full pseudo-piece gluing input is KL II:

```text
.tmp_kl08_source/psiql.tex
SHA256 6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF
```

Lines 117--147 construct a pseudo-piece from central pieces and
universal-cover tiles.  Lines 169--207 distinguish the dynamical covering
arrow from the inclusion immersion and describe the tile gluing.

No checked source asserts coherent collar choices through an arbitrary
horizon, complete outer-exit footprints, final-root no-birth, or a
two-sided comparison between truncated and full KL widths.  These are not
imported.

## 3. Coherent collar construction

For one stage, Kahn's proof gives an open target inner collar
\(\Lambda_j\subset A_j\), an adjacent source component
\(\Lambda'_{j+1}\subset A_{j+1}\), and an inverse germ

\[
 \varphi_j:
 \Lambda_j\longrightarrow\Lambda'_{j+1}
\]

such that

\[
 I_j\circ\varphi_j=\operatorname{id}_{\Lambda_j}.
\tag{3.1}
\]

Both \(\Lambda_j\) and \(\Lambda'_{j+1}\) contain collars of their inner
ends.  Shrinking an inner collar preserves (3.1).

For the finite chain, consider the finitely many inverse compositions

\[
 \varphi_{j-1}\circ\cdots\circ\varphi_0,
 \qquad 1\leq j\leq N.
\tag{3.2}
\]

The domain of each composition contains an open neighborhood of the inner
end of \(A_0\).  The intersection of finitely many such domains is again
an open neighborhood of that inner end.  Choose a sufficiently thin open
inner collar

\[
 C_0
 \subset
 \bigcap_{j=1}^{N}
 \operatorname{Dom}
 (\varphi_{j-1}\circ\cdots\circ\varphi_0).
\tag{3.3}
\]

Define recursively

\[
 C_{j+1}=\varphi_j(C_j).
\tag{3.4}
\]

Equations (3.1) and (3.4) give (1.4).  This is where finiteness of the
horizon is used.  An infinite intersection of inverse-germ domains need
not contain a collar.

The choice is existential rather than canonical.  Different initial
collars \(C_0\) can produce different coherent systems.

## 4. Injectivity of every lifted collar

Let

\[
 \pi_{j+1}:\widetilde A_{j+1}\to A_{j+1},
 \qquad
 \pi_j:\widetilde A_j\to A_j
\]

be the universal covers used for one corresponding tile pair, and let
\(L_j\) be the compatible lift of \(I_j\).  Choose positive deck
generators \(T_{j+1},T_j\).  Since the annular degree is one,

\[
 L_jT_{j+1}=T_jL_j.
\tag{4.1}
\]

Suppose \(x,y\) belong to the selected lift of \(C_{j+1}\) and

\[
 L_j(x)=L_j(y).
\]

Projection and base injectivity on \(C_{j+1}\) give

\[
 \pi_{j+1}(x)=\pi_{j+1}(y).
\]

Thus \(y=T_{j+1}^kx\) for some \(k\in\mathbb Z\).  By (4.1),

\[
 L_j(y)=T_j^kL_j(x)=L_j(x).
\]

The target deck action is free, so \(k=0\) and \(x=y\).
Every selected lifted collar map is injective.

## 5. Complete quotient-collision audit

Fix one stage and suppose two source quotient classes have the same image
under \(\iota_j^{\mathrm{col}}\).

### 5.1 Central--central

Both classes have central representatives.  Clause 1 of Theorem 1.1
excludes a collision.

### 5.2 Same tile

Both representatives lie in the same lifted collar.  Section 4 excludes a
collision.

### 5.3 Different tiles

Clause 2 makes the tile-component map bijective.  Distinct source tiles
therefore enter distinct target tile copies, whose interiors are disjoint.
No collision is possible.

### 5.4 Tile--central

A target tile and the target central piece meet only in their declared
overlap.  Collar overlap reflection (1.2) therefore puts the source tile
representative in the declared source overlap.  Let \(w\) be its glued
source-central representative, and let \(z\) be the source-central
representative of the alleged collision.  Exact gluing says that the
central images of \(w\) and \(z\) agree.  Central injectivity gives
\(w=z\).  Hence the original tile and central representatives were already
related by the declared source gluing and define one source quotient
class.

These cases exhaust the quotient.  Hence
\(\iota_j^{\mathrm{col}}\) is injective.  It is a holomorphic immersion,
so it is a holomorphic embedding.  Finite composition proves (1.6).

## 6. Proof of the marked safe-set theorem

Under the additional hypotheses of Theorem 1.2, apply the proved
embedded-disk accessible-footprint theorem to \(F_H\).

For a source prime end \(p\), \(\Phi_H(p)\) consists of:

- the target prime end \(F_H(p)\), when the boundary extension lands on
  the target ideal boundary; or
- every target prime end accessible through a component of
  \(\mathbf Y_0^{\mathrm{col}}\setminus
    F_H(\mathbf Y_N^{\mathrm{col}})\)
  that lands at the interior boundary value \(F_H(p)\).

First and last traversal show that every target endpoint of a proper path
whose unique source restriction ends at \(p\) belongs to \(\Phi_H(p)\).
Conversely, a complement access to any
\(\xi\in\Phi_H(p)\), traversed into and out of a source hairpin at \(p\),
realizes \(\xi\) as a target endpoint.  Therefore a connected source ideal
set \(C\) is admissible exactly when every one of its pointwise footprints
is contained in \(I\), which is (1.8).

Nothing in this argument makes the safe set connected.  If it has several
connected components, each is a distinct maximal connected admissible
candidate.  A notation \(F_H^*I\) for one component requires a separately
declared seed or uniqueness theorem.

## 7. Omitted-sheet and outer-exit ledger

For each stage define

\[
 \mathscr D_j
 =
 \pi_0(I_j^{-1}(C_j))\setminus\{C_{j+1}\}.
\tag{7.1}
\]

The distinguished component \(C_{j+1}\) is the inner sheet retained by
the theorem.  Every other component in \(\mathscr D_j\) is an omitted
outer-return sheet over the retained target collar.

For every proof-used omitted component \(E\), a complete ledger must record

\[
 \bigl(
 E,j,\alpha_E,\sigma_E,H_E,\theta_E,
 \mathscr S_E,p^-_E,p^+_E,\Phi(E),\tau(E),\operatorname{prop}(E)
 \bigr),
\tag{7.2}
\]

where:

- \(\alpha_E\) is the tile;
- \(\sigma_E\) is the sheet;
- \(H_E\) is the based covering subgroup;
- \(\theta_E\) is the deck phase;
- \(\mathscr S_E\) is the localization-coset displacement, valued in the
  pointed coset set
  \[
   \mathscr S_{{\rm loc},j}
   =
   a_{j*}^{-1}(H_{t,j})/H_{s,j};
  \tag{7.3}
  \]
  here \(a_j\) is the based physical map underlying the full localization
  from which the collar was restricted;
- \(p_E^\pm\) are the first and last attachment accesses;
- \(\Phi(E)\) is the complete access footprint;
- \(\tau(E)\) is the complete horizon itinerary; and
- \(\operatorname{prop}(E)\) records proper, end-proper, or nonproper
  behavior.

The finite-horizon embedding theorem discards these components
geometrically.  It does not prove that Wave, covering, width, or
quasi-additivity arguments never use them.  That separate proof-use
exhaustion is necessary before a truncated carrier can replace a full one.
The quotient in (7.3) is a coset set, not an asserted group.  At a
canonical primitive stage it has a proved non-base element; replacing it
by one undifferentiated “discarded” label would erase the actual collision.
In unindexed notation the retained replacement state is exactly
\(a_*^{-1}(H_t)/H_s\).

## 8. Conditional final-root enlargement theorem

Consider old and enlarged systems satisfying Theorem 1.2 on declared
protected prime-end sets

\[
 \mathcal P_N^+\subset\partial_i\mathbf Y_N^{\mathrm{col},+},
 \quad
 \mathcal P_N\subset\partial_i\mathbf Y_N^{\mathrm{col}},
 \quad
 \mathcal P_0^+\subset\partial_i\mathbf Y_0^{\mathrm{col},+},
 \quad
 \mathcal P_0\subset\partial_i\mathbf Y_0^{\mathrm{col}}.
\]

Assume that the target protected sets contain the complete footprints of
the corresponding protected source sets.  Let

\[
 F_H^+:
 \mathbf Y_N^{\mathrm{col},+}
 \longrightarrow
 \mathbf Y_0^{\mathrm{col},+}.
\]

Assume analytic embeddings

\[
 a_N:\mathbf Y_N^{\mathrm{col},+}
 \hookrightarrow\mathbf Y_N^{\mathrm{col}},
 \qquad
 a_0:\mathbf Y_0^{\mathrm{col},+}
 \hookrightarrow\mathbf Y_0^{\mathrm{col}}
\]

such that

\[
 a_0F_H^+=F_Ha_N.
\tag{8.1}
\]

Assume also:

1. enlarged retained collars are exact inverse images of old retained
   collars;
2. proof-used retained and omitted components correspond bijectively;
3. subgroup, deck phase, itinerary, and properness data in (7.2) are
   preserved;
4. \(a_N\) and \(a_0\) have continuous boundary extensions whose
   restrictions
   \[
     a_{N,\partial}:\mathcal P_N^+\xrightarrow{\cong}\mathcal P_N,
     \qquad
     a_{0,\partial}:\mathcal P_0^+\xrightarrow{\cong}\mathcal P_0
   \]
   are cyclic-order-preserving homeomorphisms;
5. no new nonproper bridge is born; and
6. every \(p\in\mathcal P_N^+\) satisfies footprint no-birth/no-loss:
   \[
   a_{0,\partial}\bigl(\Phi_H^+(p)\bigr)
   =
   \Phi_H\bigl(a_{N,\partial}(p)\bigr).
   \tag{8.2}
   \]

For \(I\subset\mathcal P_0\), define the restricted safe sets by

\[
 \operatorname{Safe}_{H,\mathcal P_N}(I)
 =
 \{p\in\mathcal P_N:\Phi_H(p)\subset I\},
\]

and analogously for the enlarged system.  Then they are natural:

\[
 \operatorname{Safe}_{H,\mathcal P_N^+}^+
   (a_{0,\partial}^{-1}I)
 =
 a_{N,\partial}^{-1}
   \bigl(\operatorname{Safe}_{H,\mathcal P_N}(I)\bigr).
\tag{8.3}
\]

Indeed, for any \(p\in\mathcal P_N^+\), containment of the left footprint in
\(a_{0,\partial}^{-1}I\) is equivalent by injectivity and (8.2) to
containment of the old footprint at \(a_{N,\partial}(p)\) in \(I\).

Because \(a_{N,\partial}:\mathcal P_N^+\to\mathcal P_N\) is a
homeomorphism, (8.3) also transports the connected components of the
restricted safe sets bijectively.  Clause 2 is not the topological reason
for component transport; it is separate analytic data needed to justify
the footprint identity and the absence of omitted-sheet birth.  No
conclusion is asserted outside the four protected sets.  Kahn's
existential collar lemma does not imply any of clauses 1--6.

## 9. Exact failure certificates

Choose the least horizon index and first proof-use traversal at which a
required clause fails.  Record one of:

1. `CENTRAL_EMBEDDING_FAILURE`: distinct source-central points with one
   central image;
2. `ANNULUS_DATA_FAILURE`: the stage, proposed \(d_j,r_j,I_j\), and the
   first failed integer-degree, modulus, immersion, inner-extension, or
   boundary-degree clause;
3. `BASE_COLLISION`: \(u\neq v\) in the retained collar
   \(C_{j+1}\) with \(I_j(u)=I_j(v)\), plus lifted points and deck
   displacement;
4. `COMPONENT_BIJECTION_FAILURE`: either two source tile components have
   one target tile, or a declared target tile has no source preimage;
5. `GLUING_DATA_FAILURE`: a nonembedding overlap map, a failed gluing
   commutator, or an undeclared quotient identification;
6. `OVERLAP_REFLECTION_FAILURE`: a retained source tile point outside the
   declared source overlap maps into the target central/tile overlap;
7. `QUOTIENT_COLLISION`: two source quotient classes with one target
   image, classified as central--central, same-tile, different-tile, or
   tile--central;
8. `UNRECORDED_EXIT`: an \(E\in\mathscr D_j\) meeting proof-use but absent
   from (7.2), with first access and full itinerary;
9. `FOOTPRINT_ERROR`: \(p\) and
   \[
     \xi\in
     \Phi_{\mathrm{actual}}(p)
     \mathbin{\triangle}
     \Phi_{\mathrm{recorded}}(p),
   \]
   witnessed by an access path or separating crosscut;
10. `MARKED_DOMAIN_FAILURE`: a claimed endpoint conformal disk is not one,
    or a point in the asserted marked domain has no complete footprint;
11. `PRIME_END_FAILURE`: failure or nonuniqueness of the declared conformal
   prime-end extension, a cyclic-order reversal witnessed by three marked
   accesses, or boundary monodromy (nonunique physical impressions alone
   are not a failure);
12. `CRITICAL_INTRUSION`: a critical value enters a declared
   degree-one collar; or
13. `ENLARGEMENT_MISMATCH`: a new retained/omitted component, subgroup
    class, access, or nonproper bridge with no old counterpart, or a
    failure of the protected-set boundary homeomorphism or footprint
    identity.

For an incorrectly admitted \(p\), choose
\(\xi\in\Phi_H(p)\setminus I\).  A complement access to \(\xi\),
concatenated with a source hairpin at \(p\), is an explicit target proper
path refuting KKL admissibility.

## 10. Quantitative limit

The theorem proves finite-horizon topology and holomorphic embedding only.
It supplies no estimate of the form

\[
 |W_{\mathrm{KL}}-W_{\mathrm{col}}|
 \leq D_{\mathrm{out}},
\tag{10.1}
\]

and no block estimate

\[
 \sum_{\text{block}}D_{\mathrm{out}}
 \leq\delta L+E_0
\tag{10.2}
\]

uniform in satellite period, rotation number, or horizon length.

In the general degree-\(d\) category, Kahn's round source collar has

\[
 \operatorname{mod}\mathbb A(1,\rho^{1/d})
 =
 \frac{\log\rho}{2\pi d},
\]

so topologically identical access data alone cannot control its modulus
uniformly as \(d\to\infty\).  This observation does **not** by itself
prove or refute the desired period-uniform quadratic block estimate.  One
quadratic \(\psi\)-ql step has degree two, but grouped depth-\(k\)
transitions can have effective degree \(2^k\), while factoring them into
degree-two steps leaves an unbounded horizon length.  The required
quadratic estimate remains open because neither (10.1) nor (10.2), nor a
substitute controlling the accumulated omitted outer-return sheets,
appears in the checked source.

## 11. Skeptic audit

### 11.1 No full pseudo-piece embedding

Only the selected inner collars are retained.  The full canonical
primitive localization is now proved noninjective, and the abstract and
full \(\psi\)-ql counterexamples separately show why the collar theorem
cannot imply a whole-annulus conclusion in a larger category.
Some exact relative fiber-product condition is indispensable and is not a
consequence of commutation alone.  Equality (1.2) is the stronger
sufficient version assumed here.  Without relative cartesianity, a
retained source tile point can enter the part of a target central overlap
also hit by the source central piece while remaining outside the declared
source overlap, producing a tile--central quotient collision even though
the central and retained-tile restrictions are separately injective.

### 11.2 No automatic unique marked pullback

The safe set (1.7) may be disconnected.  The theorem identifies all
maximal connected candidates as its connected components; it does not
silently choose one.

### 11.3 No finite footprint inference

A finite tile set can have infinitely many complement accesses or
non-locally-connected boundary incidence.  Complete footprints remain an
analytic input.

### 11.4 No canonical collar

Kahn's collar is existential.  Coherence over one finite horizon is
obtained by finite shrinking, not by a natural choice stable under every
enlargement.

### 11.5 No proof-use exhaustion

Discarded sheets are harmless only after every Wave, Wanderers,
quasi-additivity, covering, and width path is proved to avoid them or their
effect is charged.  The ledger (7.2) records but does not bound that
effect.

### 11.6 No period-uniform metric conclusion

The theorem is qualitative.  The general varying-degree modulus example
is not substituted for the missing period-independent quadratic block
estimate.

## 12. Project status

This pass proves a conditional finite-horizon collar-truncation theorem.
It does not promote:

- `DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING`;
- `DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`;
- `DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`;
- `DIRECT_DECORATION_TRACE_COLLAR_REALIZATION`;
- VAAPC-I;
- UPTCR; or
- MLC.

On the collar branch, the immediate replacement gate is exact:
instantiate the omitted-sheet ledger (7.2), including the nontrivial
coset state (7.3), for an actual finite direct-decoration horizon; prove
complete proof-use exhaustion or a uniform defect charge; and prove the
no-birth conditions (8.1)--(8.2) under the allowed final-root enlargement.
The separate
`CANONICAL_KL_RESTRICTED_INTERFACE_CLASSIFICATION` now constructs a
relation-valued **interior** alternative for each supplied fixed
same-source datum, but its proper/end-proper response and final-root
stability remain open.  This collar theorem remains conditional and
non-gating for the false universal full-embedding route.
