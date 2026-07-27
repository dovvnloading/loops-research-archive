# Research Push VIII
## Marked pulled/immersed ideal interfaces, collared trace spaces, actual welding, and final-root naturality

**Date:** 2026-07-25  
**Status:** theorem-level research draft for the marked-width MLC program.

This note does **not** prove the Mandelbrot local connectivity conjecture.  It
closes a finite-horizon direct-decoration interface problem that remained after
the unmarked binary contact graph was constructed.  The new point is that an
interface has two different maps and two different levels of marking:

\[
 F=(f,\iota):V'\rightrightarrows V,
\]

where `f` is the covering map and `iota` is the immersion, while

1. an **action marking** must satisfy the KKL condition
   \(f^*\mathcal I\) refines \(\iota^*\mathcal I\); and
2. a generally finer **trace overlay** may retain response, access, obstacle,
   phase, and enlargement subdivisions that are not licensed as KKL ideal
   endpoints.

The note gives a finite compiler for the action marking, defines valid trace
spaces on source-native ideal collars, constructs the actual one-to-many
proper/end-proper welding, and proves normalized-word and certified final-root
naturality.  A mandatory endpoint that cannot be promoted is returned with an
exact obstruction; it may remain response-only or be repaired by an explicitly
certified slit construction.

The complete mixed Wave horizon, universal endpoint visibility, uniformly
bounded WAD/Value dimension, MBTT, coercivity, rigidity, UPTCR, and MLC remain
open.

---

# Part I. Source boundary and the exact missing object

## 1. What the direct-decoration source supplies

For the Kahn--Lyubich direct-decoration puzzle, fix

\[
 P=Y^{(n-1)q+1},\qquad g=f^q,
\]

and the two source binary pullbacks

\[
 g_a=g|_{Q_a}:Q_a\longrightarrow P,
 \qquad a\in\{L,R\}.
\]

Each `g_a` is univalent.  The pseudo-puzzle construction assigns Riemann
surfaces

\[
 \mathbf P,\qquad \mathbf Q_L,\qquad \mathbf Q_R
\]

and two maps for every branch:

\[
 \mathbf f_a:\mathbf Q_a\longrightarrow\mathbf P,
 \qquad
 \boldsymbol\iota_a:\mathbf Q_a\longrightarrow\mathbf P.
\]

The first is the degree-one covering induced by `g_a`; the second is the
immersion induced by the inclusion `Q_a subset P`.  The source pseudo-functor
constructs both maps.  Its ideal boundary is tiled by finitely many outer arcs
`lambda_i` and Julia-side arcs `xi_i,eta_i`; a vertex `v_i` carries the
Julia-side port

\[
 \partial_{v_i}\mathbf Y=\eta_i\cup\xi_{i+1}.
\]

The inclusion immersion extends continuously to this ideal boundary, but its
boundary image need not lie in the target ideal boundary.  This is precisely
why a covering-only trace atlas is incomplete.

## 2. KKL action marking

Let `V` be a hyperbolic Riemann surface without cusps.  An ideal marking
`mathcal I` is a tiling of its ideal boundary by pairwise disjoint connected
open intervals.  For

\[
 F=(f,\iota):V'\rightrightarrows V,
\]

KKL define:

- the covering pullback marking \(f^*\mathcal I\);
- the immersion pullbacks \(\iota^*I\) of target intervals;
- the induced marking \(\iota^*\mathcal I\), when the pullbacks form a partial
  ideal marking.

The pair acts on `(V,mathcal I)` exactly when

\[
 \boxed{f^*\mathcal I\text{ refines }\iota^*\mathcal I.}
 \tag{2.1}
\]

Immersion pullbacks may fail to exist or may overlap.  Properness and
end-properness are additional properties, not consequences of the interval
labels.

## 3. Two-layer marked interface

A complete finite interface is

\[
 \boxed{
 \mathfrak I_F=
 (\mathcal I,\mathscr O,
   f^*\mathcal I,\iota^*\mathcal I,
   \mathfrak p,\mathfrak e,
   \mathcal T,\mathcal W,\mathfrak F).
 }
 \tag{3.1}
\]

Here:

- `mathcal I` is the coarse action marking satisfying (2.1);
- `mathscr O` is the finite trace/access/obstacle overlay;
- `mathfrak p,mathfrak e` are the proper and end-proper flags;
- `mathcal T` is the family of valid ideal-arc trace spaces;
- `mathcal W` is the actual welding operator or end-welding relation;
- `mathfrak F` is the endpoint flag, phase, side, and cyclic-order record.

An endpoint of `mathscr O` may lie inside an interval of `mathcal I`.  Such an
endpoint is retained for response or access purposes but is not silently used
as a KKL ideal endpoint.

This separation is the central repair.  It prevents an analytically useful
trace subdivision from forcing an impossible ideal marking.

---

# Part II. Finite source model for the pulled/immersed boundary

## 4. Boundary-monotone micro-atlas

Fix one ideal-boundary component and cut it at a retained phase endpoint.  The
target component is a linearly ordered union of finitely many open micro-atoms

\[
 M_0,M_1,\ldots,M_{N-1}
\]

with vertices `0,...,N`.  The source component is similarly divided into

\[
 A_0,A_1,\ldots,A_{m-1}.
\]

After subdividing the finite pseudo-boundary tiles, the covering and immersion
have the following atom data.

1. **Covering label.**  Every `A_j` maps homeomorphically under `f` to one
   target micro-atom \(M_{c(j)}\), and every source vertex has a target vertex
   image under the covering extension.
2. **Proper immersion label.**  A source atom on which `iota` is proper maps
   homeomorphically to one target micro-atom \(M_{r(j)}\).
3. **Nonproper atom.**  If the immersion boundary image enters the target
   interior, put \(r(j)=\bot\).

The phase endpoint is retained, so no action interval crosses the chosen seam.
For the direct-decoration pseudo-puzzle, these records are read from the finite
component map in the universal-cover construction and from the continuous
boundary extension of the inclusion immersion.

## 5. Finite pullback formula

For a connected union `B` of target micro-atoms, delete from the source boundary
all proper atoms whose labels lie outside `B`.  Let \(H_\iota(B)\) be the union
of the remaining connected components that contain at least one proper atom
labelled in `B`.

### Theorem 5.1 - Boundary-monotone immersion pullback

Under the finite boundary-monotone atlas above,

\[
 \boxed{\iota^*B=H_\iota(B).}
 \tag{5.1}
\]

### Proof

Let `K` be a component used in `H_iota(B)`.  Every proper source path subordinate
to `K` can land only on a proper atom mapped into `B`; the intervening
nonproper atoms have no target ideal landing interval.  Its unique immersed
image is therefore subordinate to `B`.  Hence `K subset iota^*B`.

Conversely, a source boundary atom outside `H_iota(B)` is either a proper atom
mapped outside `B`, or is separated from every `B`-labelled atom by such a
proper blocker.  A proper path landing at that blocker has immersed image not
subordinate to `B`.  Maximality in the KKL definition therefore excludes the
atom.  This proves (5.1).  QED.

The formula is finite and falsifiable.  If a proposed pseudo-boundary table is
not boundary-monotone, the first atom where (5.1) fails is an exact source
certificate rather than a hidden trace error.

---

# Part III. Branch-adapted ideal marking compiler

## 6. Immersion-forced blocks

Consider a maximal consecutive run of nonproper source atoms.  If it has proper
neighbors labelled by target micro-atoms `p` and `q`, then the pullback hull of
the interval containing `p` and the pullback hull of the interval containing
`q` both contain the nonproper run unless `p` and `q` lie in the same target
interval.

### Theorem 6.1 - Finest immersion-admissible partition

Generate a relation by joining the two proper target labels adjacent to every
maximal nonproper source run, and take its interval-convex transitive closure in
the fixed phase order.  Its classes are contiguous target blocks

\[
 \mathcal B_0=(B_1,\ldots,B_s).
\]

Then:

1. the pullbacks \(\{\iota^*B_j\}\) are pairwise disjoint;
2. every target marking whose immersion pullbacks form a partial marking is a
   coarsening of `mathcal B_0`;
3. `mathcal B_0` is the unique finest immersion-admissible partition.

### Proof

A nonproper run adjacent to different target intervals belongs to both hulls in
(5.1), so those intervals must be merged.  Connected target intervals also
force every intervening micro-atom into the same block.  Repeating this process
gives the stated interval-convex relation, proving necessity.

After the closure, each nonproper run has proper neighbors either in the same
block or on only one side.  Formula (5.1) then assigns it to at most one target
block.  Proper atoms of different blocks are blockers.  Thus distinct
pullbacks are disjoint, proving sufficiency and fineness.  QED.

## 7. Covering refinement criterion

Let `mathcal B` be any coarsening of `mathcal B_0`.  Each connected component
`K` of \(\iota^*B\) has two source boundary vertices.  Let their covering
images be \(c_\partial(v_-),c_\partial(v_+)\).

### Theorem 7.1 - Exact action criterion

The pair `F=(f,iota)` acts on the target marking `mathcal B` if and only if

\[
 \boxed{
 c_\partial(v_-),c_\partial(v_+)
 \text{ are endpoints of }\mathcal B
 }
 \tag{7.1}
\]

for every connected component of every immersion pullback.

### Proof

The covering pullback marking is obtained by pulling back every target endpoint.
A partition `f^*mathcal B` refines the induced immersion marking exactly when
every boundary of every immersion interval is one of those covering-preimage
endpoints.  On the finite atom circle, this is precisely (7.1).  QED.

## 8. Mandatory endpoints and finite decision theorem

Let `E_req` be the target endpoints that a theorem genuinely needs as KKL ideal
endpoints.  A valid action marking must contain them.

### Theorem 8.1 - Finite marked-interface decision

There is a finite algorithm that:

1. constructs `mathcal B_0`;
2. enumerates its coarsenings that retain `E_req`;
3. tests (7.1);
4. returns a finest valid action marking, with every proper and end-proper flag;
   or
5. returns one of the exact obstructions
   
   - a mandatory endpoint splitting an immersion-forced block; or
   - a covering image of an immersion boundary that cannot be made an endpoint
     by any permitted coarsening.

### Proof

The set of coarsenings of a finite ordered partition is finite.  Theorems 6.1
and 7.1 are necessary and sufficient tests.  Properness is read atomwise.
End-properness holds exactly when both end atoms of the source pullback
component are proper.  QED.

The companion compiler implements this theorem and independently checks the
answer against exhaustive enumeration.

## 9. Action endpoints versus response-only endpoints

Let `E_trace` be every endpoint used by response, protected access, obstacles,
phase, or enlargement data.

Define

\[
 E_{\rm action}=\partial\mathcal I,
 \qquad
 E_{\rm response}=E_{\rm trace}\setminus E_{\rm action}.
\]

Endpoints in `E_response` remain in the trace overlay but are not used as ideal
marking endpoints.  If a later KKL theorem call requires one of them as an
ideal endpoint, it must be promoted and the compiler rerun.

This gives an exact no-laundering rule:

\[
 \boxed{
 \text{trace visibility does not imply ideal-action visibility.}
 }
 \tag{9.1}
\]

## 10. Certified slit repair

A failed mandatory endpoint can be repaired only by changing the analytic
interface, not by changing its label.

A **slit-repair certificate** consists of finite source and target analytic
crosscut graphs such that:

1. the graphs avoid critical values, protected collars, obstacles, and declared
   free ports;
2. the covering and immersion pull the target graph to the selected source
   graph with commuting maps;
3. cutting along the graphs separates the conflicting nonproper bridge;
4. every new cut side receives an endpoint flag and phase;
5. the cut surfaces remain in the authorized localization.

### Theorem 10.1 - Slit repair activates the compiler

After cutting along a slit-repair certificate, the covering and immersion lift
to the cut surfaces, the repaired endpoint is a genuine ideal-boundary endpoint,
and Theorems 5.1--8.1 apply to the refined finite boundary atlas.

### Proof

Cutting along a finite analytic graph replaces every graph edge by two proper
boundary sides.  The commuting pullback conditions lift both maps to the cut
surfaces.  The former nonproper bridge is separated at the chosen side, so the
new endpoint no longer splits an immersion-forced block.  The remaining claims
follow from the universal property of the slit surface and the finite compiler.
QED.

The theorem is a realization theorem **from a certificate**.  Constructing the
certificate for every future proof endpoint remains a protected-routing problem.

---

# Part IV. Valid ideal-arc trace spaces

## 11. Why a local collar definition is necessary

An ideal interval is not automatically a Euclidean boundary arc of a regular
plane domain.  The Push V audit correctly rejected the silent identification of
arbitrary Jordan-boundary traces with one fixed `H^{1/2}` space.

The pseudo-piece construction supplies a safer object.  Every ideal tile arc
lies on the boundary of one of the universal-cover pieces used to construct the
pseudo-piece.  A finite subarc has a simply connected collar inside that
universal cover.

## 12. Collared Douglas trace

Let `J` be a proper ideal subarc of a pseudo-piece `mathbf Y`.  Choose a
piecewise analytic ideal collar `C_Y(J)` inside the corresponding universal
cover tile.  It is bounded by:

- the ideal arc `J`;
- two crosscuts ending at the endpoints of `J`;
- one interior cross-section.

Define

\[
 \mathcal T_{\mathbf Y}(J)
 =\operatorname{Tr}_{J}H^1(C_{\mathbf Y}(J))
 \tag{12.1}
\]

with quotient norm

\[
 \|\tau\|_{\mathcal T(J)}^2
 =\inf_{\operatorname{Tr}_Ju=\tau}
 \left(
   \int_{C_{\mathbf Y}(J)}|\nabla u|^2
   +\left|\int_{K_J}u\right|^2
 \right),
 \tag{12.2}
\]

where `K_J` is one fixed compact normalization set in the collar.

### Theorem 12.1 - Ideal-arc trace Hilbert space

The space in (12.1) is a Hilbert trace space.  In any conformal rectangle
coordinate it is the usual `H^{1/2}` trace space on the corresponding boundary
interval, with equivalent normalized norm.  Transporting the collar by a
conformal isomorphism transports the trace space isometrically for the
Dirichlet seminorm.

### Proof

The collar is a piecewise analytic simply connected domain, so the Sobolev trace
theorem and the minimum-energy quotient construction apply.  A Riemann map to a
rectangle identifies the trace with `H^{1/2}`.  Dirichlet energy is conformally
invariant in dimension two.  The compact normalization removes the constant
kernel.  QED.

## 13. Compatible multi-arc traces

For finitely many proper arcs `J_1,...,J_r`, choose collars with disjoint deep
parts and let `C` be their union with a finite connecting core.  Define

\[
 \mathcal T_{\mathbf Y}(J_1,\ldots,J_r)
 =\operatorname{im}
 \left[
   H^1(C)\longrightarrow
   \prod_{k=1}^r\mathcal T_{\mathbf Y}(J_k)
 \right].
 \tag{13.1}
\]

This is the compatible tuple space.  It is not replaced by an arbitrary direct
sum, so common endpoint and finite-energy compatibility are retained.

## 14. Proper and end-proper trace objects

Let `K` be one connected component of \(\iota^*I\).

- If `iota` is proper on all intervals of `K`, define the full trace
  \(\mathcal T_{V'}(K)\) by (13.1).
- If `iota` is only end-proper, let `E_-(K),E_+(K)` be its proper end intervals
  and define the end-germ trace

  \[
  \mathcal T_{V'}^{\rm end}(K)
  =\mathcal T_{V'}(E_-(K),E_+(K)).
  \tag{14.1}
  \]

The nonproper middle of an end-proper multi-interval is retained in the marked
bridge word.  It is **not** assigned a fictitious physical boundary trace.

This distinction is exactly what the KKL proper/end-proper calculus requires.

---

# Part V. Actual pulled/immersed welding

## 15. Atomwise trace maps

Let `I` be a target action interval and let `K` be a proper or end-proper
component of \(\iota^*I\).

For every proper source end arc `E subset K`, the immersion has a transported
collar map and therefore a trace restriction

\[
 R_{\iota,E}:
 \mathcal T_V(I)
 \longrightarrow
 \mathcal T_{V'}(E).
 \tag{15.1}
\]

Since `f^*mathcal I` refines `iota^*mathcal I`, subdivide `E` into covering
intervals `E_l`.  For each such interval, the degree-one covering gives a
trace pushforward

\[
 P_{f,E_l}:
 \mathcal T_{V'}(E_l)
 \longrightarrow
 \mathcal T_V(f(E_l)).
 \tag{15.2}
\]

Both maps are actual maps on source-native collars.  No omitted boundary
conjugacy is present.

## 16. One-to-many welding operator

Define

\[
 \boxed{
 \mathcal W_{F,I}
 =
 \bigoplus_{K,E,E_l}
 P_{f,E_l}\circ
 \operatorname{Sub}_{E_l}\circ
 R_{\iota,E}.
 }
 \tag{16.1}
\]

The direct sum is indexed by:

- components `K` of \(\iota^*I\);
- their proper end intervals `E`;
- covering intervals `E_l subset E`.

The output retains branch, component, interval, side, phase, and endpoint flags.

### Theorem 16.1 - Actual ideal welding

The operator (16.1) is well defined and continuous on the compatible trace
spaces.

1. If `F` is proper on `I`, it is the complete trace welding for the interval.
2. If `F` is end-proper on `I`, it is the complete **end-germ** welding; the
   nonproper middle remains a typed bridge in the interface state.
3. If `nu(I)` is the number of proper lifted end arcs, then in direct-sum
   Dirichlet norm

   \[
   \|\mathcal W_{F,I}\|
   \le\sqrt{\nu(I)}.
   \tag{16.2}
   \]

4. With the compatible-image norm induced from the parent trace, the joint
   one-to-many restriction is isometric by definition.

### Proof

Every factor in (16.1) is trace restriction or conformal transport on an actual
proper collar.  The action condition guarantees that every source end is
subdivided by covering intervals rather than crossed by a covering endpoint.
The maps therefore compose.

One parent trace is copied to at most `nu(I)` disjoint proper collars.  Conformal
invariance controls each copy by the parent Dirichlet energy, giving (16.2).
The compatible-image statement follows from the minimum-energy image norm.
QED.

## 17. Complete marked interval record

The complete output for `I` is

\[
 \boxed{
 \mathfrak W_{F,I}
 =
 (\iota^*I,
  f^*\mathcal I|_{\iota^*I},
  \mathfrak p_I,\mathfrak e_I,
  \mathcal W_{F,I},
  \mathfrak b_I,
  \mathfrak F_I).
 }
 \tag{17.1}
\]

Here `mathfrak b_I` is the chronological bridge word of proper and nonproper
source intervals.  Thus a trace operator never replaces the KKL interval
combinatorics; the two are carried together.

---

# Part VI. Word and normalized-overlay naturality

## 18. Composition theorem

Let

\[
 F_1=(f_1,\iota_1),\qquad
 F_2=(f_2,\iota_2)
\]

be composable marked correspondences, and suppose the intermediate action
markings agree.

### Theorem 18.1 - Marked welding composition

After the canonical reassociation of one-to-many compatible tuple spaces,

\[
 \boxed{
 \mathcal W_{F_2\circ F_1,I}
 =
 \mathcal W_{F_2,F_{1*}I}
 \circ
 \mathcal W_{F_1,I}.
 }
 \tag{18.1}
\]

The pulled/immersed multi-intervals, proper/end-proper flags, bridge words,
endpoint flags, and cyclic orders compose in the same chronological order.

### Proof

Both sides perform the same operations on the same actual collars:
immersion restriction, subdivision by the covering marking, and covering
transport.  Restriction of Sobolev traces and composition of conformal maps are
associative.  The KKL action marking ensures the same intermediate interval
partition is used.  QED.

## 19. Binary normalized atlas

For a binary word `w`, let the actual pseudo-piece correspondence be expressed
in the root coordinate by the induced maps `mathbf h_w`.  The source identities

\[
 \mathbf h_{wa}=\mathbf f_a\circ\mathbf h_w
 \tag{19.1}
\]

and the corresponding immersion squares imply that:

- the action marking compiler has the same normalized finite input at each
  occurrence of one branch type;
- trace collars are transported from the root atlas;
- welding operators are the same root operators with word labels;
- no physical-coordinate welding map is omitted.

### Theorem 19.1 - Normalized-overlay naturality

For every finite binary word, the physical pulled/immersed interface is
isomorphic to its normalized interface, and every contact, action marking,
trace overlay, endpoint flag, properness flag, and welding diagram commutes with
normalization.

### Proof

Use (19.1), pseudo-functor naturality, Theorem 18.1, and transport the root
collars by the actual branch maps.  Every diagram is an identity of actual maps,
not a compactness assertion.  QED.

---

# Part VII. Final-root and overlay naturality

## 20. Safe-gap invariance

Suppose a carrier enlargement remains in the established first-level safe gap
and does not alter the binary puzzle pieces or their pseudo-pieces.  Then the
complete outer ideal interface (3.1) is unchanged.  Only the internal carrier
response or additional internal ports may change.

This is the exact scope of safe-gap final-root invariance.

## 21. Analytic enlargement squares

Consider old and enlarged correspondences

\[
 F=(f,\iota):V'\rightrightarrows V,
 \qquad
 F^+=(f^+,\iota^+):V^{+'}\rightrightarrows V^+
\]

and analytic embeddings

\[
 A:V\to V^+,
 \qquad
 A':V'\to V^{+'}
\]

satisfying

\[
 \boxed{
 A\circ f=f^+\circ A',
 \qquad
 A\circ\iota=\iota^+\circ A'.
 }
 \tag{21.1}
\]

Assume:

1. the maps extend injectively and cyclic-order preservingly on every proof-used
   proper ideal arc;
2. old endpoint sets are exact inverse images of the enlarged endpoint sets;
3. collars, sides, phases, and proper/end-proper flags are transported;
4. no protected or localization collision occurs.

### Theorem 21.1 - Final-root marked-interface naturality

Under (21.1):

1. covering pullbacks commute with enlargement;
2. immersion pullbacks commute with enlargement;
3. the refinement condition (2.1) is preserved;
4. the action marking and trace overlay restriction diagrams commute;
5. for every interval `I`,

   \[
   \boxed{
   A_{\rm out}^{\sharp}\,
   \mathcal W_{F^+,A(I)}
   =
   \mathcal W_{F,I}\,
   A_{\rm in}^{\sharp},
   }
   \tag{21.2}
   \]

   after matching the labelled output tuple;
6. proper/end-proper status, endpoint flags, and bridge words are unchanged.

### Proof

The first two conclusions follow by taking inverse images in the commuting
squares.  Exact endpoint inverse image makes the covering and immersion
partitions identical after restriction, so the action condition is preserved.

A trace restricted by `A` and then pulled through the old immersion is the same
function as first pulling through the enlarged immersion and then restricting
by `A'`; this is the second identity in (21.1).  The same argument with the
covering gives the output square.  Composing these equalities with subdivision
proves (21.2).  Properness and cyclic order are preserved by the assumed ideal
boundary embeddings.  QED.

## 22. Certified overlay refinement

Let `mathscr O^+` refine `mathscr O`.

- If a new endpoint is trace-only, ordinary trace restriction gives a commuting
  subdivision square.
- If it is promoted to an action endpoint, rerun Theorem 8.1.
- If the compiler rejects it, the endpoint must remain trace-only or receive a
  slit-repair certificate.

### Theorem 22.1 - Refinement naturality

Every compiler-admissible overlay refinement commutes with the action marking,
trace spaces, welding operators, and exact minimization over newly internal
subdivision traces.

### Proof

All fine traces are restrictions of the same coarse finite-energy functions.
The action marking compiler guarantees that no fine action endpoint crosses an
immersion pullback or covering interval.  Therefore restriction commutes with
each factor in (16.1).  Minimizing the fine internal traces reconstructs the
coarse Dirichlet relation.  QED.

## 23. No-new-demand criterion

Under a program extension or final-root enlargement, the old marked interface
is complete exactly when no new proof seed reaches:

- a response-only endpoint that must now be an action endpoint;
- an omitted proper lift;
- a changed proper/end-proper flag;
- a new slit or protected side;
- an old coarse trace fiber on which a new observable is nonconstant.

This is a finite dependency-reachability test once the analytic branch graph is
supplied.

---

# Part VIII. Fixed-horizon completion theorem

## 24. Main theorem

### Theorem 24.1 - Fixed-horizon marked binary interface completion

Fix one actual direct-decoration binary block and a finite source-authorized
branch horizon.  Freeze:

1. the structural binary contact and pseudo-boundary atlas;
2. every mandatory KKL ideal endpoint;
3. every trace/access/obstacle/electrode endpoint;
4. every proper or end-proper theorem call;
5. every certified final-root enlargement square.

Assume every mandatory action endpoint either:

- passes the finite compiler of Theorem 8.1; or
- has a slit-repair certificate of Theorem 10.1.

Then the complete horizon admits:

1. actual target, covering-pulled, and immersion-pulled ideal markings;
2. exact proof that `f^*I` refines `iota^*I` at every branch;
3. complete proper/end-proper and endpoint-flag records;
4. valid collared ideal-arc and end-germ trace spaces;
5. actual one-to-many welding operators and bridge words;
6. exact word and normalized-overlay naturality;
7. exact naturality under every certified final-root enlargement;
8. a finite failure certificate at the first unsupported endpoint or map.

### Proof

Every branch has a finite pseudo-boundary atlas.  Run Theorem 8.1, applying the
finite slit repair where supplied.  Theorem 12.1 and Sections 13--14 construct
the trace objects.  Theorem 16.1 constructs the actual welding.  Theorems 18.1
and 19.1 give finite-word naturality, and Theorems 21.1--22.1 give enlargement
and refinement naturality.  Finiteness of the horizon makes the union of all
records finite.  QED.

## 25. Exact status

The theorem closes the **formal and analytic marked-interface compiler** for a
fixed source-authorized direct-decoration horizon.

It does not prove that an unconstructed complete mixed Wave horizon supplies:

- every mandatory endpoint;
- a collision-free slit repair for every failed endpoint;
- universal incidence or multiplicity bounds;
- a universally bounded response/WAD/Value quotient;
- a strict mixed-block transition.

Therefore global `VAAPC-I`, the full virtual marked correspondence, H2, MBTT,
UPTCR, and MLC remain open.

---

# Part IX. Exact compiler audit

## 26. Implemented finite compiler

The companion program models one linearly cut ideal boundary component.  It:

1. computes the unique finest immersion-admissible partition;
2. enumerates all coarsenings preserving mandatory action endpoints;
3. tests the covering-refinement criterion;
4. classifies every pullback component as proper, end-proper, or neither;
5. separates promotable action endpoints from response-only overlay endpoints;
6. returns exact obstruction witnesses.

The successful fixture has:

\[
 E_{\rm action}=\{0,2,4,6,8\},
 \qquad
 E_{\rm response}=\{1,3,5,7\}.
\]

Every immersion component is end-proper but not proper.  Two independent
obstruction fixtures detect:

- a mandatory endpoint inside an immersion-forced block;
- failure of covering refinement under every permitted coarsening.

## 27. Exhaustive randomized validation

For 1,500 randomized finite atom systems with at most seven target micro-atoms,
the compiler output was compared with an independent exhaustive enumeration of
**every** target endpoint subset.

Results:

\[
 \boxed{
 \begin{array}{rcl}
 \text{compiled systems}&=&1221,\\
 \text{obstructed systems}&=&279,\\
 \text{false positives}&=&0,\\
 \text{false negatives}&=&0,\\
 \text{maximal-marking mismatches}&=&0.
 \end{array}}
\]

The computation is a finite combinatorial proof audit.  It does not substitute
for the pseudo-piece trace and naturality proofs.

---

# Part X. Ledger split and next obligation

## 28. Proved split nodes

The work supports the following fixed-horizon split nodes:

1. `FINITE_BOUNDARY_IMMERSION_PULLBACK_FORMULA`;
2. `FINEST_IMMERSION_ADMISSIBLE_MARKING`;
3. `COVERING_IMMERSION_ACTION_CRITERION`;
4. `BRANCH_ADAPTED_IDEAL_MARKING_COMPILER`;
5. `ACTION_TRACE_ENDPOINT_SEPARATION`;
6. `CERTIFIED_IDEAL_SLIT_REPAIR`;
7. `COLLARED_IDEAL_ARC_TRACE_SPACE`;
8. `END_PROPER_END_GERM_TRACE_SPACE`;
9. `ACTUAL_ONE_TO_MANY_IDEAL_WELDING`;
10. `MARKED_WELDING_WORD_FUNCTORIALITY`;
11. `NORMALIZED_MARKED_INTERFACE_NATURALITY`;
12. `CERTIFIED_FINAL_ROOT_WELDING_NATURALITY`;
13. `FIXED_HORIZON_MARKED_BINARY_INTERFACE_COMPLETION`.

No original global-open count is reduced by this split.

## 29. Immediate next source theorem

The next obligation is no longer the definition of a marked interface.  It is:

### `UNIVERSAL_MANDATORY_ENDPOINT_VISIBILITY_AND_REPAIR`

For every actual mixed virtual-Molecule proof block, construct the complete
finite horizon and prove that every proof-required KKL endpoint:

1. is branch-visible to the pulled/immersed marking compiler; or
2. has a collision-free certified slit repair;
3. transports through every final-root enlargement;
4. has universally controlled proper-lift multiplicity;
5. factors, together with all response/WAD/Value outputs, through one uniformly
   finite future-observable quotient.

After that, the dominant remaining task is the strict response/Value transition
needed for MBTT.
