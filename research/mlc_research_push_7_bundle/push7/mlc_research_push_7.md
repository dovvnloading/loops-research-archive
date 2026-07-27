# Research Push VII
## Source-complete binary contact sets, endpoint-germ itineraries, and the one-to-many pseudo-trace atlas

**Date:** 2026-07-25  
**Status:** theorem-level research draft for the marked-width MLC program.

This note does **not** prove Mandelbrot local connectivity.  It closes a sharply
specified direct-decoration subproblem: for the actual binary `f^q` pullback
system of Kahn--Lyubich, it constructs the complete all-depth contact sets,
retains endpoint sides rather than bare landing points, builds a finite
one-to-many trace-pullback atlas on the source-native pseudo-puzzle boundary,
and proves exact naturality under normalization, safe-gap carrier enlargement,
and certified finite overlay refinement.

The note makes no universal bound in the decoration parameters and does not
construct the complete mixed Wave horizon.  Uniform response/Value compression,
MBTT, coercivity, rigidity, UPTCR, and MLC remain open.

---

# Part I. Exact source package

## 1. Binary direct-decoration data

Fix the first direct-decoration puzzle of Kahn--Lyubich.  Let

\[
 P=Y^{(n-1)q+1},\qquad g=f^q.
\]

The source constructs two closed puzzle pullbacks

\[
 Q_L,Q_R\subset P,
 \qquad g_a:=g|_{Q_a}:Q_a\longrightarrow P,
 \qquad a\in\mathcal A:=\{L,R\},
\]

such that every `g_a` is univalent.  In the direct-decoration compactification
we additionally use the already audited closed-piece assertions:

\[
 Q_L\cap Q_R=\varnothing,
 \qquad
 g_a:Q_a\to P
 \text{ is a homeomorphism of closed Jordan pieces.}
\]

Write

\[
 \phi_a=g_a^{-1}:P\longrightarrow Q_a.
\]

For a word

\[
 w=a_1\cdots a_k\in\mathcal A^k
\]

put

\[
 \phi_w=\phi_{a_1}\circ\cdots\circ\phi_{a_k},
 \qquad
 D_w=\phi_w(P),
 \qquad
 h_w=g^k|_{D_w}:D_w\to P.
\]

Appending a symbol is geometric nesting:

\[
 D_{wa}=\phi_w(Q_a)\subset D_w.
\]

Prepending a symbol is inverse-sheet dynamics:

\[
 g(D_{aw})=D_w.
\]

Every `D_w` is a closed Jordan puzzle piece and every `h_w` is a conformal
homeomorphism on the interior extending homeomorphically to the closed piece.

## 2. The source boundary word

A depth-`m` puzzle boundary is a finite union of:

1. external-ray segments, and
2. arcs of the level-`m` equipotential.

For a piece `Y`, let

\[
 \Theta(Y)=(\theta_0,\ldots,\theta_{r-1})
\]

be the cyclic list of angles of its boundary rays.  The source explicitly uses
this cyclic angle representation for geometric puzzle pieces.  Thus a closed
piece has a finite typed boundary word

\[
 \mathsf B(Y)
 =
 \bigl(
   \mathsf{Ray}(\theta_i),
   \mathsf{Eq}(m;\theta_i,\theta_{i+1})
 \bigr)_{i\bmod r}.
\]

The branch `g_a` determines, for each root ray edge, the unique inverse ray edge
on `Q_a`; in Böttcher angle this is one of the solutions of

\[
 2^q\widehat\theta=\theta\pmod 1
\]

selected by the actual pullback component.  It also sends the level-`m+q`
equipotential to the level-`m` equipotential.  Therefore `B(Q_a)` is computed
from `B(P)` and the actual branch lift, not guessed from a schematic picture.

---

# Part II. Source realization of the one-step contact graphs

## 3. Finite contact graph theorem

Define the actual contact set

\[
 C_a=\partial P\cap\partial Q_a.
\]

### Theorem 3.1 - Source boundary-contact compiler

For each `a in {L,R}` let

\[
 \mathcal V_a
 =\{v_{at}:t\in\mathcal A^{n-1}\},
 \qquad v_s=\phi_s(\alpha).
\]

Then:

1. the landing vertices of `C_a` are exactly `mathcal V_a`;
2. `C_a` is the union of the maximal common subsegments of the two boundary
   rays of `P` landing at the vertices in `mathcal V_a`, together with their
   endpoint flags;
3. no nondegenerate equipotential arc belongs to `C_a`;
4. `C_a` is computable from the two finite typed boundary words
   `B(P),B(Q_a)` by exact edge matching;
5. `g_a(C_a)` is a finite subgraph of `partial P`;
6. after a finite subdivision, `g_a` maps every open contact atom
   homeomorphically onto one open root-boundary atom.

### Proof

The source's Lemma 2.1 states that the `2^n` components of the domain of `g^n`
are indexed by binary words `s`, contain the unique points

\[
 v_s=\phi_s(\alpha),
\]

and are attached to the pair of boundary rays of `P` landing at `v_s`.
If `s=at`, the corresponding depth-`n` component is contained in `Q_a`.
A common boundary-ray subarc of that component and `P` cannot be interior to
`Q_a`, because `Q_a subset P`.  It is therefore also contained in
`partial Q_a`.  This proves that every vertex in `mathcal V_a` occurs in `C_a`.

Conversely, suppose an open ray contact of `P` and `Q_a` lands at a vertex `v`
of `P`.  Lemma 2.1 supplies the unique depth-`n` component `D_s` attached at
`v`.  Since `v in Q_a` and the two first-level cylinders are disjoint closed
pieces, the first symbol of `s` must be `a`; otherwise `D_s` lies in the other
first-level cylinder.  Thus `v=v_{at}`.  This proves the exact landing-vertex
set and, after taking maximal common intervals on those rays, the exact open
contact set.

The boundary of `P` uses one equipotential level, while the boundary of `Q_a`
uses the level shifted by `q`.  Distinct equipotentials are disjoint, so no open
equipotential overlap occurs.  Outside the filled Julia set, two external rays
with different angles are disjoint.  Hence the maximal common ray intervals
are recovered by matching exact ray-angle labels and intersecting their
potential intervals.  The two typed boundary words are finite, so this is a
finite exact computation.

Finally, `g_a` is a homeomorphism of closed puzzle pieces.  On external rays it
maps angle `theta` to `2^q theta`, and on equipotentials it shifts the level by
`q`.  Subdivide at every contact endpoint and its image.  Every resulting open
contact atom maps homeomorphically to one open root atom.  QED.

## 4. Contact flags, not bare endpoints

Let `Gamma` be the finite common refinement of

\[
 \partial P,\quad \partial Q_L,\quad \partial Q_R
\]

obtained in Theorem 3.1.  Let `V(Gamma)` be its finite vertex set and
`E(Gamma)` its open edge set.

A **boundary flag** is a pair

\[
 \mathfrak f=(v,e),
 \qquad v\in\partial e,
\]

together with the side of the relevant puzzle piece and the induced cyclic
orientation.  The same landing point can carry several distinct flags.  This is
the correct endpoint object for prime-end and trace bookkeeping.

For each branch, `g_a` induces a partial flag map

\[
 \sigma_a:\mathscr F(C_a)\longrightarrow\mathscr F(\partial P).
\]

It preserves the cyclic order of flags because `g_a` is holomorphic and
univalent on the selected piece.

---

# Part III. Complete all-depth binary contacts

## 5. Normalized root-contact sets

For every finite word `w`, define

\[
 C_w=\partial P\cap\partial D_w,
\]

and its current-coordinate normalization

\[
 \widehat C_w=h_w(C_w)\subset\partial P.
\]

Set

\[
 \widehat C_\varnothing=\partial P.
\]

### Theorem 5.1 - Exact binary contact recursion

For every word `w` and symbol `a`,

\[
 \boxed{
 \widehat C_{wa}
 =g_a\bigl(\widehat C_w\cap C_a\bigr).
 }
\]

Equivalently,

\[
 C_{wa}
 =h_{wa}^{-1}
   g_a\bigl(\widehat C_w\cap C_a\bigr).
\]

### Proof

Let `z` belong to `C_{wa}`.  Since

\[
 D_{wa}\subset D_w\subset P,
\]

a point lying on both `partial P` and `partial D_{wa}` also lies on
`partial D_w`: otherwise it would be interior to `D_w subset P`, contradicting
its membership in `partial P`.  Hence

\[
 x=h_w(z)\in\widehat C_w.
\]

Since

\[
 D_{wa}=\phi_w(Q_a),
\]

we also have `x in partial Q_a`.  Thus `x in widehat C_w cap C_a`, and

\[
 h_{wa}(z)=g_a(x).
\]

This gives one inclusion.

Conversely, take `x in widehat C_w cap C_a`.  The unique point

\[
 z=h_w^{-1}(x)
\]

lies on `partial P` because `x` came from the normalized old contact, and lies
on `partial D_{wa}` because `x in partial Q_a`.  Hence `z in C_{wa}` and
`h_{wa}(z)=g_a(x)`.  QED.

## 6. Complete pairwise contact theorem

### Theorem 6.1 - All binary cylinder contacts

Let `u,v` be finite binary words.

1. If `u,v` are incomparable, then
   \[
   D_u\cap D_v=\varnothing.
   \]
2. If `v=ut`, then
   \[
   \boxed{
   \partial D_u\cap\partial D_v
   =\phi_u(C_t).
   }
   \]
3. Consequently every pairwise contact in the infinite binary pullback family
   is computed from the two one-step source graphs `C_L,C_R` by Theorem 5.1.

### Proof

At the first differing symbol, the two pieces lie in the pullbacks of the
closed disjoint pieces `Q_L,Q_R`; subsequent inverse branches preserve
disjointness.  This proves the first assertion.

If `v=ut`, then

\[
 D_v=\phi_u(D_t),
 \qquad
 D_u=\phi_u(P).
\]

Since `phi_u` is a homeomorphism of closed pieces,

\[
 \partial D_u\cap\partial D_v
 =\phi_u(\partial P\cap\partial D_t)
 =\phi_u(C_t).
\]

The recursion now gives the last assertion.  QED.

## 7. Finite state consequence

Choose the root subdivision `Gamma` so that:

- `C_L,C_R` are subcomplexes;
- every `g_a` maps contact vertices to vertices;
- every contact edge maps to one root edge.

Then every `widehat C_w` is a union of open edges and vertices of `Gamma`.
Thus the exact all-depth contact system is a deterministic finite automaton on
subcomplexes of `Gamma`:

\[
 T_a(S)=g_a(S\cap C_a).
\]

There are at most

\[
 2^{|E(\Gamma)|+|V(\Gamma)|}
\]

raw contact states for one fixed decoration block.  No uniform bound over all
decorations is claimed.

---

# Part IV. The source transient endpoint tree

## 8. The depth-`n` source bijection

The source proves that the domain of `g^n` has `2^n` components and that each
component contains exactly one `g^n`-preimage of `alpha`, attached to the pair of
boundary rays of `P` landing at that preimage.

The binary words enumerate these components.  For

\[
 s\in\mathcal A^n
\]

define

\[
 v_s=\phi_s(\alpha).
\]

Then

\[
 s\longmapsto v_s
\]

is a bijection from `A^n` to the vertex set of `P` used by the decoration fan,
and

\[
 g(v_{as})=v_s.
\]

The source's dyadic labeling is compatible with this shift: the branch symbol
records the next inverse binary digit, while forward `g` deletes that digit.

## 9. Exact prefix endpoint theorem

For a prefix `w in A^k`, `0 <= k <= n`, set

\[
 \mathcal V(w)
 =\{v_{wt}:t\in\mathcal A^{n-k}\}.
\]

### Theorem 9.1 - Source-complete transient endpoint itinerary

The landing vertices of the open ray contacts in `partial P cap partial D_w`
are exactly `V(w)`.  Moreover, for every completion `t`,

\[
 h_w(v_{wt})=v_t.
\]

The physical common ray footprints at `v_{wt}` are mapped by `h_w` to the
standard root ray footprints at `v_t`.

### Proof

For every completion `t`, the depth-`n` piece `D_{wt}` is contained in `D_w`
and is attached to the two boundary rays of `P` landing at `v_{wt}`.  A common
boundary ray of `P` and the deeper piece remains on the boundary of every
intermediate nested piece, so `v_{wt}` is a contact vertex of `D_w`.

Conversely, let `v` be the landing vertex of an open contact ray between `P`
and `D_w`.  The source depth-`n` bijection gives a unique word `s` with `D_s`
attached at `v`.  If `s` did not begin with `w`, then `D_s` and `D_w` would lie
in incomparable binary cylinders and would be disjoint, contradicting that both
contain `v`.  Thus `s=wt`.

Finally, `h_w=g^k` cancels the first `k` inverse branches:

\[
 h_w(v_{wt})
 =g^k\phi_w\phi_t(\alpha)
 =\phi_t(\alpha)
 =v_t.
\]

The same identity holds on the common ray segments.  QED.

## 10. Exact post-transient collapse

Let `mathscr R_alpha subset partial P` be the pair of complete root boundary-ray
atoms landing at the fixed point `alpha`, together with their endpoint flags.
The branch `Q_L` is the inverse sheet attached to `alpha`; since `g(alpha)=alpha`,
its boundary action fixes `mathscr R_alpha`.  The other closed first-level
piece is disjoint from `Q_L` and has no contact flag on these two rays.

### Theorem 10.1 - Synchronizing contact collapse

For every word `s in A^n`,

\[
 \widehat C_s=\mathscr R_\alpha.
\]

For every continuation `t`:

\[
 \widehat C_{sL^m}=\mathscr R_\alpha
 \quad(m\ge0),
\]

while, if `t` contains an `R`,

\[
 \widehat C_{st}=\varnothing.
\]

The same assertion holds for endpoint flags.  Consequently the complete
post-transient contact automaton has exactly two states:

\[
 \mathscr R_\alpha,
 \qquad
 \varnothing.
\]

### Proof

Theorem 9.1 with `k=n` gives one normalized landing vertex, namely `alpha`,
for every depth-`n` word.  The source component is attached to the full pair of
boundary rays of `P` at that vertex, and `h_s` maps the deeper equipotential to
the root equipotential.  Hence the normalized contact is the same complete
pair `mathscr R_alpha` for every `s`.

The left inverse branch fixes `alpha`.  Since `f^q` fixes each external ray in
the rotation orbit at `alpha`, it sends the two attached ray atoms to themselves;
the contact recursion therefore fixes `mathscr R_alpha` under `L`.

The right first-level piece is a disjoint closed piece attached to `alpha'`.
It has no open ray atom or endpoint flag in `mathscr R_alpha`; exact source
boundary-word matching verifies the empty intersection.  Thus one `R` sends
the state to the empty contact.  The empty contact is absorbing by Theorem 5.1.
QED.

### Consequence

The exponential `2^n` source fan is a finite transient endpoint inventory, not
an infinite-depth contact-memory obstruction.  After the source escape depth,
one address carries either one fixed two-sided port at `alpha` or no root
contact at all.  This does not bound the number of transient proof-used ports
across all words.

## 11. Transient normalized overlays

For `r=0,...,n`, let

\[
 \mathscr O_r
 =\bigcup_{t\in\mathcal A^r}
   \partial_{v_t}\mathbf P,
\]

where `bold P` is the pseudo-piece associated to `P` and
`partial_v bold P` is the source J-boundary port attached to the vertex `v`.

For every prefix `w` of length `k<=n`, the normalized contact-port overlay is
exactly

\[
 \mathscr O_{n-k},
\]

independent of the prefix itself.  Choosing the next symbol `a` selects the
ports indexed by `at` and the univalent map sends them to the ports indexed by
`t`.

After depth `n`, the finite contact automaton of Part III continues the atlas
for arbitrary infinite words.

---

# Part V. One-to-many trace-restriction atlas

## 12. Why the pseudo-puzzle is the correct trace surface

The source introduces pseudo-pieces precisely to make return domains canonical
and avoid relying on uncontrolled Euclidean external-ray geometry.

For a geometric piece `Y`, its pseudo-piece `bold Y` is a Riemann surface with a
finite ideal boundary decomposition:

- O-boundary arcs `lambda_i` covering the outer ideal boundary;
- J-boundary arcs `xi_i,eta_i` mapped toward the Julia set;
- the vertex port
  \[
  \partial_v\mathbf Y=\eta_i\cup\xi_{i+1}.
  \]

The pseudo-functor is natural:

1. a branched covering of puzzle pieces induces a covering of pseudo-pieces of
   the same degree;
2. an inclusion of puzzle pieces induces an immersion of pseudo-pieces;
3. the induced immersion extends continuously to the ideal boundary.

For the selected binary branches, the induced maps

\[
 \mathbf g_a:\mathbf Q_a\longrightarrow\mathbf P
\]

are univalent.

## 13. Finite source overlay

Start with the finite pseudo-boundary decomposition of `bold P`.  Subdivide it
at:

- all images of source contact endpoints;
- all vertex-port endpoints occurring in the transient source tree;
- all provisional protected/access/obstacle/electrode endpoints supplied at the
  current finite proof stage.

Pull this subdivision back to each `bold Q_a` and add the finite source
boundary vertices there.  Subdivide once more so every child open atom maps
homeomorphically onto one parent open atom.

Let

\[
 \mathscr A_P,
 \qquad
 \mathscr A_{Q_a}
\]

be the resulting finite open atom sets.

For `K in A_{Q_a}`, let

\[
 p_a(K)\in\mathscr A_P
\]

be its unique parent atom.  The relation

\[
 \operatorname{Lift}(J)
 =\{(a,K):p_a(K)=J\}
\]

is finite.  A child atom has one parent.  Because each binary pseudo-map has degree one,
a common source-refined parent atom has at most one lift in each branch; hence

\[
 |\operatorname{Lift}(J)|\le 2.
\]

The atlas is nevertheless one-to-many because a single root trace may be read
simultaneously on the left and right inverse sheets.  If a later certified
overlay refinement inserts source endpoints, the parent is refined by all of
their images first, so the same at-most-one-lift-per-branch assertion remains
true.

## 14. Intrinsic compatible trace spaces

For a pseudo-piece `bold Y` and a finite union `B` of boundary atoms, define

\[
 \mathcal T_{\mathbf Y}(B)
 =
 H^1_{\mathrm{fin}}(\mathbf Y)
 \,/\,
 \{u:\operatorname{Tr}_B u=0\},
\]

with the quotient norm induced by Dirichlet energy plus one fixed local
`L^2` normalization.  Equivalently, it is the image of the trace map equipped
with its minimum-energy norm.

For a family of child atoms over `J`, define the **compatible tuple space**

\[
 \mathcal T^{\mathrm{comp}}_J
 =
 \operatorname{im}
 \left[
  \mathcal T_{\mathbf P}(J)
  \longrightarrow
  \prod_{(a,K)\in\operatorname{Lift}(J)}
  \mathcal T_{\mathbf Q_a}(K)
 \right].
\]

This avoids treating traces meeting at a vertex as arbitrary independent
coordinates.

## 15. One-to-many trace theorem

### Theorem 15.1 - Binary pseudo-trace atlas

For every root atom `J`, the map

\[
 \mathcal R_J u
 =
 \left(
   (u|_{\mathbf g_a(K)})\circ \mathbf g_a|_K
 \right)_{(a,K)\in\operatorname{Lift}(J)}
\]

is a well-defined continuous map

\[
 \mathcal R_J:
 \mathcal T_{\mathbf P}(J)
 \longrightarrow
 \mathcal T^{\mathrm{comp}}_J.
\]

It has the following properties.

1. **Exact branch pullback.**  Each component is the actual Sobolev trace
   pullback under the source-induced univalent pseudo-map.
2. **Energy naturality.**  Pullback by `bold g_a` is conformally exact for
   Dirichlet energy.
3. **Endpoint-side fidelity.**  The flag map `sigma_a` identifies the incident
   side and cyclic position of every endpoint.
4. **Finite one-to-many incidence.**  The complete atlas is a finite directed
   multigraph.
5. **No Euclidean welding assumption.**  No global boundary uniformization or
   omitted conjugacy map is used.

### Proof

The source pseudo-map is conformal and extends continuously to the ideal
boundary.  After subdivision, every child atom maps homeomorphically to its
parent atom.  Trace pullback is therefore defined on the intrinsic Dirichlet
trace quotient.  The compatible tuple space is defined as the image of the
joint map, so endpoint compatibility is automatic.  Conformal invariance gives
the energy statement.  Finiteness follows from the finite subdivisions.  The
flag map records which incident ideal arc is used at every endpoint.  QED.

## 16. Word functoriality

For a word `w=a_1...a_k`, let `bold h_w:bold D_w->bold P` be the induced
univalent pseudo-map.

### Theorem 16.1 - Atlas composition

The direct trace pullback under `bold h_w` equals the composition of the
one-step atlas maps, with the canonical reassociation of compatible tuple
spaces:

\[
 \boxed{
 \mathcal R_w
 =\mathcal R_{a_1}\circ\cdots\circ\mathcal R_{a_k},
 }
\]

The same statement holds for endpoint flags and cyclic orders.

### Proof

Here the copied intermediate trace spaces are associated to the dynamical
chain

\[
 \mathbf D_{a_1\cdots a_k}
 \xrightarrow{\mathbf g_{a_1}}
 \mathbf D_{a_2\cdots a_k}
 \longrightarrow\cdots\longrightarrow
 \mathbf P.
\]

Contravariance of trace pullback reverses this dynamical composition and gives
the displayed order.  Both sides restrict one root trace to the same collection
of descendant atoms and compose it with the same conformal map `bold h_w`.
Restriction and composition of functions are associative.  The source
naturality lemma gives the same composition on pseudo-pieces and their ideal
boundaries.  QED.

---

# Part VI. Normalized-overlay naturality

## 17. Physical and normalized overlays

Let `mathscr O` denote the finite root pseudo-boundary overlay.  At a word `w`,
define the physical overlay by pullback:

\[
 \mathscr O_w=\mathbf h_w^{-1}(\mathscr O).
\]

The map `bold h_w` is an exact isomorphism between the physical marked overlay
and its root-normalized copy.

For a child `wa`, on `bold D_{wa}` we have

\[
 \boxed{
 \mathbf h_{wa}
 =\mathbf g_a\circ\mathbf h_w.
 }
\]

### Theorem 17.1 - Normalized-overlay naturality

For every word `w` and branch `a`, the diagrams commute simultaneously for:

1. source contact subgraphs;
2. endpoint flags and their cyclic order;
3. one-to-many trace restriction maps;
4. compatible Dirichlet trace spaces;
5. every finite response form obtained by minimizing internal traces.

In particular, two prefixes with the same normalized contact state and the same
live marked overlay have exactly the same future contact/trace behavior.

### Proof

The identity `h_{wa}=g_a h_w` is an identity of actual polynomial iterates on
the selected piece.  The source pseudo-functor sends it to the same identity on
pseudo-pieces.  Contact sets commute by Theorem 5.1, flags by the boundary
extension, and traces by Theorem 15.1.  Dirichlet minimization is over the same
physical fibers after applying the coordinate isomorphisms, so response forms
also commute.  QED.

---

# Part VII. Final-root-enlargement naturality

## 18. Safe-gap carrier enlargement

Let

\[
 K_0\subset S\subset S^+
 \subset P\setminus(Q_L\cup Q_R)
\]

be compact connected roots, as in the existing pullback-gap enlargement
theorem.  Put

\[
 S_w=\phi_w(S),
 \qquad
 S_w^+=\phi_w(S^+).
\]

### Theorem 18.1 - Safe-gap atlas invariance

Under this enlargement:

1. every puzzle piece `D_w` is unchanged;
2. every binary contact set is unchanged;
3. every endpoint itinerary and boundary flag is unchanged;
4. the complete one-to-many trace atlas is unchanged;
5. the inclusions `S_w subset S_w^+` commute with every shift and parent map;
6. only the internal cap/carrier response changes.

### Proof

The contact and trace atlas is constructed solely from the fixed puzzle pieces,
their pseudo-pieces, and the finite boundary overlay.  The safe-gap enlargement
is disjoint from `Q_L union Q_R` and from all puzzle boundary arcs, so none of
those data changes.  Injectivity of every `phi_w` gives the nested inclusions,
and `g phi_a=id` gives the commuting squares.  QED.

## 19. Certified finite overlay refinement

A more general final enlargement can add protected endpoints, obstacle walls,
electrodes, or proof-use marks on the existing boundary.  Let

\[
 \mathscr O\preceq\mathscr O^+
\]

be a finite refinement satisfying:

1. every new endpoint lies on an existing source ideal-boundary arc;
2. child endpoints are exact pullbacks of parent endpoints or explicitly typed
   source endpoints;
3. every branch map sends refined atoms homeomorphically to refined atoms;
4. every protected side and cyclic order is retained;
5. no old active atom changes its physical side status except by an explicitly
   declared wall or port insertion.

Let

\[
 \pi_P:\mathscr A_P^+\to\mathscr A_P,
 \qquad
 \pi_a:\mathscr A_{Q_a}^+\to\mathscr A_{Q_a}
\]

forget the subdivision.

### Theorem 19.1 - Refinement naturality

The refined atlas satisfies

\[
 \boxed{
 \pi_P\circ p_a^+
 =p_a\circ\pi_a.
 }
\]

On endpoint flags,

\[
 \pi_P\circ\sigma_a^+
 =\sigma_a\circ\pi_a.
\]

On trace spaces, if `Sub` denotes restriction from a coarse atom to its
compatible refined tuple, then

\[
 \boxed{
 \operatorname{Sub}_{Q_a}\circ\mathcal R_a
 =\mathcal R_a^+\circ\operatorname{Sub}_P.
 }
\]

The corresponding response forms commute after exact minimization over the new
internal subdivision traces.

### Proof

Every refined child atom lies in one old child atom and maps into one refined
parent atom lying in the old parent image.  This proves the atom square.  The
flag square is the same statement at endpoints with incident-edge data.

Both trace compositions take a coarse root trace, restrict it to exactly the
same refined image arcs, and pull those restrictions back by the same source
boundary maps.  Hence they agree pointwise.  Introducing subdivision traces and
then minimizing them reconstructs the old physical domain, so the response
forms agree.  QED.

## 20. Promotion boundary

Theorem 18.1 proves naturality of a **certified** provisional-to-final overlay
refinement.  It does not prove that an arbitrary final-root enlargement is
collision-free or proof-complete.  In particular, no-new-demand stability still
requires either:

- bijectivity on demanded refined atoms; or
- a future-observability proof that all new atoms in one coarse fiber have the
  same required outputs.

---

# Part VIII. Exact compiler and falsification certificate

## 21. Source compiler

A machine-readable source record contains:

1. the cyclic typed boundary word of `P`;
2. the two typed child boundary words;
3. exact branch image maps on edges and endpoint flags;
4. the source transient depth `n`;
5. the word-to-vertex map `s -> v_s` at depth `n`;
6. provisional and final finite overlays.

The compiler performs:

1. exact parent/child edge intersection;
2. construction of `C_L,C_R`;
3. simplicial subdivision;
4. contact-state recursion for arbitrary words;
5. complete pairwise contact queries;
6. endpoint-flag itinerary generation;
7. one-to-many atom incidence;
8. word-composition checks;
9. normalized-overlay checks;
10. enlargement-refinement semiconjugacy checks.

## 22. Failure certificate

A failed source realization must report the first one of:

- a boundary edge lacking an exact ray/equipotential type;
- a branch image not matching a root edge;
- an unrecorded contact subarc;
- a contact endpoint whose image is absent from the root subdivision;
- a bare endpoint with ambiguous incident side;
- a child atom with no unique parent atom after subdivision;
- a word contact violating the recursion;
- an endpoint itinerary violating `g(v_{as})=v_s`;
- a trace square that fails pointwise;
- a refined atom violating the enlargement semiconjugacy;
- a new final-root mark whose future observables are not constant on its coarse
  fiber.

---

# Part IX. Ledger effect and remaining global work

## 23. Proved split nodes

The note supports the following theorem-level split nodes:

1. `SOURCE_BINARY_BOUNDARY_GRAPH_COMPILER`;
2. `COMPLETE_BINARY_CONTACT_SET_RECURSION`;
3. `COMPLETE_BINARY_CYLINDER_CONTACTS`;
4. `SOURCE_TRANSIENT_VERTEX_ITINERARY`;
5. `BINARY_POST_TRANSIENT_CONTACT_SYNCHRONIZATION`;
6. `ENDPOINT_GERM_ITINERARY_ATLAS`;
7. `PSEUDO_BOUNDARY_ONE_TO_MANY_TRACE_ATLAS`;
8. `TRACE_ATLAS_WORD_FUNCTORIALITY`;
9. `NORMALIZED_OVERLAY_NATURALITY`;
10. `SAFE_GAP_FINAL_ROOT_ATLAS_INVARIANCE`;
11. `COLLISION_FREE_OVERLAY_REFINEMENT_NATURALITY`;
12. `BINARY_OPERADIC_RESPONSE_COMPILER`;
13. `MATRIX_PRODUCT_FUTURE_OBSERVABLE_QUOTIENT`;
14. `FIXED_BLOCK_KKL_VALUE_MOMENT_STATE`.

A conservative ledger should make no reduction in the original global open
count.  These nodes close the immediate binary-contact/trace-atlas task, but not
the complete mixed source construction.

## 24. What is now closed

For the actual binary direct-decoration pullback system and every supplied
finite marked overlay:

- every all-depth pairwise puzzle contact is source-computable;
- every contact endpoint is carried with its incident side and cyclic order;
- the depth-`n` endpoint tree is explicitly the source binary preimage tree;
- after depth `n`, the normalized contact system has only the persistent
  `alpha`-port state and the empty state;
- every trace atom has a finite one-to-many branch-lift atlas;
- all finite word lifts are functorial;
- normalization is exact;
- safe-gap root enlargement leaves the atlas invariant;
- certified final overlay refinement commutes exactly;
- the exact binary depth-$r$ response has a shared recursive grammar of size $O(r)$;
- every binary observable generated by a $d$-state coefficient transducer and a
  $w$-dimensional branch module has an exact future quotient of dimension at
  most $dw$;
- on one source-licensed finite terminal Hubbard tree, KKL Value has an exact
  positive second-moment realization of dimension at most
  $|E|^2(|E|^2+1)/2$.

## 25. What remains open

The following are not proved here:

- a universally bounded number of protected/obstacle/Value marks;
- construction of the complete Wave demand horizon;
- future-faithful finite compression over unbounded decoration depth;
- norm compactness of the full response/Value cocycle;
- a universal strict transition;
- MBTT;
- geometric coercivity;
- mixed-tower rigidity;
- UPTCR or MLC.

# Part X. Exact recursive response grammar and matrix-product observables

## 26. Binary response grammar

Let `B` be the full one-step Dirichlet form of the normalized pseudo-piece
between the root external terminals and the two child trace interfaces.  Let
`Q_0` be the terminal cap response.  Write `star` for exact trace gluing and
minimization on the compatible pseudo-trace spaces.

Define recursively

\[
 Q_{r+1}
 =\mathcal B\star
   \bigl(Q_r^{(L)}\oplus Q_r^{(R)}\bigr),
 \tag{26.1}
\]

where the superscripts mean that the two copies are pulled into the left and
right child coordinates by the source trace atlas.

### Theorem 26.1 - Operadic response compiler

For every `r`, `Q_r` is exactly the Dirichlet-to-Neumann response of the full
source-normalized binary depth-`r` pseudo-puzzle assembly.  The response has a
straight-line recursive specification of size `O(r)`, although its fully
expanded leaf trace space can have `2^r` ports.

The recursion commutes with normalized-overlay maps, safe-gap carrier
enlargement, and certified finite overlay refinement.

### Proof

At depth one, (26.1) is the ordinary Sobolev domain-decomposition formula.
Assume the statement at depth `r`.  The depth-`r+1` assembly is the one-step
root cell with one normalized depth-`r` assembly glued into each child.  The
source branch maps identify the actual child interfaces with the two copies of
the same compatible trace space.  Associativity of exact Dirichlet
minimization gives (26.1).  Induction proves the physical statement.  Sharing
the repeated symbol `Q_r` gives a directed acyclic response circuit with one
new node per depth.  Naturality follows from Theorems 17.1, 18.1, and 19.1.
QED.

### Scope

This is an exact grammar, not a bounded-dimensional response matrix.  It
removes exponential *description* growth for recursively compositional calls,
but an arbitrary observable that distinguishes every leaf can still force
`2^r` independent outputs.

## 27. Matrix-product observable compression

Let `M_L,M_R` be `d by d` coefficient-transition matrices and let `R_L,R_R` be
`w by w` branch-feature transports.  For a word

\[
 s=a_1\cdots a_r,
\]

put

\[
 M_s=M_{a_1}\cdots M_{a_r},
 \qquad
 R_s=R_{a_1}\cdots R_{a_r}.
\]

Let `u,v` be coefficient boundary vectors and `x` a root feature vector.

### Theorem 27.1 - Exact matrix-product future quotient

The complete depth-`r` weighted leaf observable

\[
 Z_r
 =\sum_{s\in\mathcal A^r}
   (u^\top M_s v)R_sx
\]

is computed in dimension `dw` by

\[
 \boxed{
 Z_r
 =(u^\top\otimes I_w)
 \left(
   M_L\otimes R_L+M_R\otimes R_R
 \right)^r
 (v\otimes x).
 }
 \tag{27.1}
\]

Thus every family of response/WAD/Value coefficients generated by a universal
`d`-state linear transducer has an exact future quotient of dimension at most
`dw`, independent of the transient fan size `2^r`.

### Proof

Expand the `r`-th power of the sum in (27.1).  Its terms are indexed by binary
words and equal `M_s tensor R_s`.  Contracting the coefficient factor with
`u,v` gives exactly the displayed leaf sum.  QED.

### Exact remaining source condition

To activate this theorem for KKL Value, one must prove that all proof-required
Value rows and WAD feature transports on the binary atlas are generated by a
universal finite-state linear transducer.  Equality of coarse address labels is
not enough.  If arbitrary independent coefficients on `2^r` leaves are
allowed, no universal finite-dimensional exact quotient exists.

## 28. Fixed-block KKL Value moment state

The matrix-product theorem can be activated without guessing arbitrary leaf
coefficients on one source-licensed primitive terminal block.  Let `T` be its
finite Hubbard tree, let `E=E(T)`, and put

\[
 \mathcal S=E\times E.
\]

Let `v,w` be the right and left Perron weights used in the KKL Value
construction, and let `lambda` be the core eigenvalue.  For a pullback level
`m`, every pulled bivertical arc `alpha` has the finite pair state

\[
 s_m(\alpha)=
 \bigl(f_*^m\alpha,(\iota^m)_*\alpha\bigr)\in\mathcal S.
 \tag{28.1}
\]

Define

\[
 a_{e,e'}=v(e)\sqrt{w(e')}
\]

and, for an arc `gamma` at level `m`, its state-incidence vector

\[
 z_m(\gamma)_{e,e'}
 =\sum_{\substack{\alpha:\,s_m(\alpha)=(e,e')}}
   \langle\alpha,\gamma\rangle.
 \tag{28.2}
\]

The KKL length formula becomes

\[
 \ell_m(\gamma)=\lambda^{-m}a^Tz_m(\gamma).
 \tag{28.3}
\]

For a WAD `X`, define the positive semidefinite second-moment state

\[
 \mathsf M_m(X)
 =\sum_{\gamma}X(\gamma)
   z_m(\gamma)z_m(\gamma)^T
 \in\operatorname{Sym}_+(\mathbb R^{\mathcal S}).
 \tag{28.4}
\]

### Theorem 28.1 - Exact fixed-block Value moment realization

For every WAD `X` on the source-licensed level-`m` primitive block,

\[
 \boxed{
 \operatorname{Val}(X)
 =\lambda^{-2m}
  \left\langle aa^T,\mathsf M_m(X)\right\rangle.
 }
 \tag{28.5}
\]

Thus KKL Value is exactly observable from a positive semidefinite homogeneous
state of dimension at most

\[
 \frac{|E|^2(|E|^2+1)}2.
 \tag{28.6}
\]

Suppose moreover that an actual univalent binary branch preserves the terminal
Hubbard incidence and induces a state-incidence matrix `P_a` on
`R^S`.  Then

\[
 \mathsf M(b_a^*X)=P_a\mathsf M(X)P_a^T.
 \tag{28.7}
\]

For the joint binary pullback,

\[
 \boxed{
 \mathsf M_{r+1}
 =P_L\mathsf M_rP_L^T+P_R\mathsf M_rP_R^T.
 }
 \tag{28.8}
\]

After vectorization, the exact transport matrix is

\[
 P_L\otimes P_L+P_R\otimes P_R.
 \tag{28.9}
\]

### Proof

The KKL construction assigns to a pulled bivertical arc `alpha` the coefficient

\[
 \lambda^{-m}
 v(f_*^m\alpha)
 \sqrt{w((\iota^m)_*\alpha)}.
\]

Grouping the arcs by the pair state (28.1) gives (28.3).  Substituting (28.3)
into

\[
 \operatorname{Val}(X)=\sum_\gamma X(\gamma)\ell_m(\gamma)^2
\]

and expanding gives (28.5).  A univalent branch preserves intersection
numbers and sends each realized pair state to its declared child pair state,
so its incidence vector transforms by `P_a`.  Summing the outer products gives
(28.7), and adding the two disjoint branch contributions gives (28.8).
Vectorization gives (28.9).  QED.

### Consequence and exact boundary

For one fixed terminal Hubbard tree, the exponentially many leaf Value
coefficients are not independent.  They factor through a finite positive
second-moment module.  This gives an explicit source realization of the
finite-state coefficient law used abstractly in Theorem 27.1.

The dimension in (28.6) is not yet universal: it depends on the terminal edge
set, and applying the state to a virtual block still requires an actual typed
factor from every binary trace branch to the terminal bivertical incidence.
Those are precisely the remaining `VIRTUAL_VERTEX_PACKAGE_SELECTOR` and
uniform core/WAD-dimension issues.

## 29. Next largest theorem

The next theorem should combine the finite source atlas and fixed-block Value
moment state above with universal Value/WAD observability:

### `BINARY_TRACE_VALUE_FUTURE_QUOTIENT_AND_STRICT_BLOCK_TRANSITION`

For every source-authorized direct-decoration block, after the complete proof
horizon is frozen:

1. select a uniformly controlled quotient of the one-to-many trace atlas;
2. retain every KKL Value row and WAD transport exactly;
3. isolate recurrent zero-energy endpoint modes in a finite neutral/shear
   module;
4. prove a uniform observability gap on the transient complement;
5. compare the resulting response with the primitive and neutral charts;
6. prove strict complete-block contraction with a discounted error budget.

That theorem would directly attack `H2_RESPONSE_REALIZATION`,
`H2_VALUE_FEATURE_REALIZATION`, the virtual transfer trichotomy, the discounted
error charge, and MBTT.

