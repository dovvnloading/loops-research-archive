# KL boundary markings: source types and corrected pagination

**Date:** 2026-11-06. **Target:** Issue #29, objectives 3–4.
**Review base:** `6e4e0806261ba3d3f15e9752109f9fbaced4eafa`.

## 1. Finding and scope

`O`, `xi`, and `eta` refer to genuine Kahn–Lyubich boundary terminology.
The phrase **“Paper 2's based localization O/xi/eta markings” is inaccurate**:
the source defines these arcs on a **pseudo-puzzle piece**, while the archive's
Paper 2 constructs rooted components and asks a broader, unresolved marking
transfer question. Neither an ambient ray nor a sheet of an arbitrary
localization exterior carries one of these arc labels without identifying
the relevant pseudo-piece and its tile.

This note corrects source attribution and page locators and identifies the
source interfaces of the new
[canonical comparison and native-side collision](tip_iterated_direct_canonical_localization_embedding_20261106.md).
That companion constructs an actual smaller-root localization projection,
realizes its source as an open subdomain of the direct period-nine canonical
target, and lifts a **native KL pseudo-piece of the actual canonical coarse
stage** into it. Integer deck translates give distinct fine sheets with the
same coarse image. The resulting composite has no continuous extension at
the native pseudo-piece's named `lambda_i/xi_i` and `lambda_i/eta_i` wrapping
joints. This supplies Issue #29's explicitly permitted source-defined
sheet/side collision alternative. It does not assert preservation of the
whole marked boundary or rule out separately specified protected restrictions.

The earlier [common-exterior comparison](tip_localization_refinement_peripheral_monodromy_20261106.md)
remains valid with its stated restricted domain. Its annular boundary
obstruction alone did not identify KL sides; the native construction supplies
the additional source object, correctly marked map, and actual joint
identification needed for the new conclusion.

## 2. Version-locked primary sources

**KL II:** Jeremy Kahn and Mikhail Lyubich, *A priori bounds for some infinitely
renormalizable quadratics: II. Decorations*,
[arXiv:math/0609046v2](https://arxiv.org/pdf/math/0609046v2), dated February 12,
2007 in the arXiv header; also the
[IMS 2006/6 PDF](https://www.math.stonybrook.edu/preprints/ims06-06.pdf).
Both checked PDFs have 29 pages. Their relevant **printed** page numbers
agree. In particular, the beginning of §2.1 is visibly numbered **5**,
and §3.2.4 is on the page visibly numbered **13**.

**Kahn I:** Jeremy Kahn, *A priori bounds for some infinitely renormalizable
quadratics: I. Bounded primitive combinatorics*,
[arXiv:math/0609045v3](https://arxiv.org/pdf/math/0609045v3), whose header gives
December 28, 2023 and whose title page is dated January 1, 2024.
The checked PDF has 63 pages. The unversioned
[arXiv PDF endpoint](https://arxiv.org/pdf/math/0609045) returned that same
version during this audit. The older IMS 2006/5 PDF has a different section
organization and must not be substituted for these theorem/page locators.

| Source | Statement or definition | Printed location |
| --- | --- | --- |
| KL II | Closed-pullback convention, including the warning about touching closures | §1.1 and footnote 1, p. 4 |
| KL II | Top Yoccoz puzzle, `P`, `V^0`, shallow pullbacks | §2.1, pp. 5–6 |
| KL II | Pairwise disjoint deeper pieces `Q^v` | Lemma 2.1, p. 6 |
| KL II | Modified principal nest and primitive terminal return | §2.2, pp. 7–8 |
| KL II | Path-space pseudo-pieces, universal-cover tile construction | §3.2.1, pp. 11–12; equivalence in Lemma 3.3, p. 12 |
| KL II | Dynamics and inclusion induce pseudo-piece maps | Lemma 3.4, pp. 12–13 |
| KL II | `lambda_i`, `xi_i`, `eta_i`, outer/Julia boundary, vertex attachment, continuous inclusion extension | §3.2.4, p. 13 |
| Kahn I v3 | Marked surfaces, morphisms, local pairs, local covers | §7.4.1, p. 43 |
| Kahn I v3 | Localization and functoriality | Theorem 7.12 and its proof, p. 44 |
| Kahn I v3 | The smaller marked root in dynamical localization and canonical renormalization | §§7.4.2–7.4.3, p. 45 |
| Kahn I v3 | Nested-period comparison and alternative renormalization choices | Theorem 7.13, pp. 45–46; §7.4.4, p. 46 |
| Kahn I v3 | Universal-cover boundary intervals excluding the deck limit set | §2.3, p. 11 |

These page numbers were checked against rendered PDF pages and page-separated
text, not inferred from a search result's zero-based page index. Recorded
SHA-256 digests of the downloaded PDFs are:

```text
KL II arXiv v2
ca951cb282186524c6902d30331e11ea49105e01230e61a19d60915fa07b0206

KL II IMS 2006/6
4b3c422226caa60bb60e6257993edcb7e666cd6ff4ea054b5b82d6aec281e9ce

Kahn I arXiv v3
46e7ff4d5cc8ea190e439f45b2e4ed7308c1cf588a666daa5150eeb0b435c9c0
```

## 3. What the labels actually name

Fix one KL stage and a geometric puzzle piece `Y`. Put
`K_Y=Y intersect K(f)` and `S_Y=closure(K(f) minus K_Y)`.
Its pseudo-piece `bold Y` is the source-defined path surface, equivalently
the gluing of `Y` to a separate universal-cover tile for each component of
`Y minus K_Y`.

The defining incidence is

\[
\partial_O\mathbf Y=\bigcup_i\lambda_i,\qquad
\partial_J\mathbf Y=\bigcup_i(\xi_i\cup\eta_i),\qquad
\partial^{v_i}\mathbf Y=\eta_i\cup\xi_{i+1}.
\]

The `lambda_i` cover the outer ideal boundary of the ambient stage domain.
The `xi_i,eta_i` are Julia-boundary arcs. Their attachment to consecutive
tiles specifies the vertex side. The two `lambda_i`/Julia-side joints
correspond to infinitely wrapping paths. Thus `O` names a **union of outer
arcs**, not a third independently chosen ray-side label.

This has several consequences for applying the archived ray tables:

- A physical vertex and its pair of rays identify a vertex incidence. They
  do not identify every point of either complete ideal Julia-side arc.
- A pseudo-piece tile includes unwrapped accesses. A finite list of rational
  angles cannot be substituted for its infinite-wrapping endpoints.
- The tags of two adjacent tiles matter: `eta_i` and `xi_(i+1)` meet at a
  vertex, whereas `xi_i` and `eta_i` are the two Julia sides of one tile.
- Numerical internal angles supplied by straightening are access markings.
  A hybrid straightening does not, solely by being hybrid, provide a
  conformal annular coordinate preserving those numerical angles.

An admissible ordinary-stage selection is therefore to specify `Y`, its
actual components `Y_i`, a cyclic indexing, an oriented annular covering,
and one embedding of each `Y_i` into its own tile. The source construction
then determines the outer/Julia-side incidences. It is unnecessary to
invent an independent `O/xi/eta` value for each ambient ray. A branch or
inclusion map can subsequently be compared with those tagged tiles.

## 4. Four different constructions must stay distinct

| Construction | Its defining data | What it does not supply automatically |
| --- | --- | --- |
| Kahn localization | A marked pair `(S,A)` and a local-neighborhood covering subgroup | A selected puzzle `Y`, tile index, or `xi/eta` side |
| KL pseudo-puzzle | One `psi`-quadratic-like stage, a geometric `Y`, its excluded set `S_Y`, and its path/tile construction | A comparison with a different renormalized stage merely because their filled sets are nested |
| Paper 1's sheet resolution | Actual base map, based covers, subgroup inclusion, and its resolved covering factor | The strong stage alignment that Paper 1 separately assumes for transport to KL tiles |
| Paper 2's rooted-end compactification | A fixed direct-decoration branch system and root, with finite addresses and end fibers | A second-stage satellite portrait, complete access/obstacle transfer, or KL tile markings |

Kahn's definition of a marked morphism is `A=g^{-1}(B)`. A **local cover**
additionally bijects the marked sets and covers their complements. Theorem
7.12 localizes an already supplied marked morphism; it does not manufacture
a morphism from a nesting `K_9 subset K_3`.

There is a further distinction in the primary construction itself. Kahn
§§7.4.2–7.4.3 chooses a smaller set `A subset K`, forms
`T=(U minus B) union A`, and localizes the marked pair **`(T,A)`**.
For canonical renormalization, `A` is the small root `K_p`. Thus a
renormalization inside the `G` stage at `K_9` has target marking `K_9`,
even though the surrounding stage began with filled set `K_3`.
Replacing that target marking by the entire `K_3` changes the proposed
morphism; it is not a source requirement of canonical renormalization.

The source also distinguishes different compositions. The proof of
Theorem 7.13(2), p. 46, uses the localization projection to compare
the complements of the next small-Julia cycles. Section 7.4.4 then
describes a different, postcritical-set-based renormalization chosen
to make the iterated and direct renormalizations equal. Equality of
the original canonical direct and iterated constructions is therefore
not an assumption that can be inserted without proof.

Paper 1 makes the additional alignment explicit in
[`main.tex`](../../papers/paper1_canonical_localization/main.tex),
Definition `def:strong-alignment` and the preceding section “Transport to
tiles and pseudo-pieces.” It requires based conformal identifications,
positive annular generators, component/tile labels, the selected copies,
and their central gluing, in a commuting square. Its definition
`def:whole-tile-comparison` separately records the named wrapping ends.
These are hypotheses for the archive's comparison results, not conclusions
of an arbitrary covering-space calculation.

Paper 2's
[`main_v2.tex`](../../papers/paper2_rooted_end_compactification/main_v2.tex),
Problem `prob:marking-transfer`, asks for transfer of a second portrait,
complete access and obstacle marking, terminal-return compatibility, and
naturality under authorized root enlargement. It does not define a package
named `O/xi/eta`. Paper 1's ordinary access path called `eta` is also
unrelated to the KL boundary arcs.

The older research notes already distinguish these objects. In particular,
[the accessible-footprint audit](../mlc_unified/embedded_disk_accessible_footprint_theorem.md)
§2 traces the KL boundary to its pseudo-piece construction;
[the Wave/access selector](../mlc_unified/wave_to_kl_address_access_selector.md)
§1 warns against identifying different sorts of sides by their labels;
and [the whole-tile comparison audit](../mlc_unified/canonical_resolution_kl_tile_correspondence_no_go.md)
requires an explicit end-compatible comparison datum. This source audit
restores those distinctions in the concrete tip discussion.

## 5. Source naturality and the boundary of the new comparison

KL Lemma 3.4 supplies maps induced by dynamics and by inclusion for pieces
in its specified stage construction. Its inclusion immersion extends to
the pseudo-piece ideal boundary, but §3.2.4 explicitly does **not** assert
that the whole source boundary maps into the target boundary when the
pieces differ. “Preserve every side” cannot therefore mean, without an
additional restriction, that every source boundary point must remain a
target boundary point of the same label.

At this parameter there are at least two stage choices:

\[
f\quad\text{with filled set }K(f),
\qquad
G=f^3\quad\text{with filled set }K_3.
\]

The corresponding excluded sets `S_Y` and ambient annuli differ.
The cover exteriors used in the common-exterior note,

\[
\Omega_p=U^0\setminus\bigcup_{j=0}^{p-1}f^j(K_p),
\]

are different objects again. Agreement of return germs or a finite
landed-ray correspondence does not identify these entire path surfaces.
In particular, the notation `f^3` alone does not turn a between-stage
comparison into one application of Lemma 3.4.

The new canonical comparison supplies the identified map and native source
for the specific failure proved in §6 below. A different proposed protected
or pseudo-piece transition still requires an **identified comparison on
identified path surfaces**: specify the source and target stage,
pieces, excluded sets, and copies; specify the actual map on the relevant
domains; and prove it takes the declared admissible paths and their
endpoint-fixed homotopies to the target ones. When using Kahn's
localization functor, verify its marked-pair preimage condition. When using
the KL puzzle functor, verify the relevant dynamics/inclusion diagram.
Then identify the required tagged arcs and their actual images, allowing
interior images where the source theorem allows them.

For a proposed protected restriction this obligation becomes smaller:
name the actual subdomain and ideal interval, their selected sheet and
base paths, and the exact source and target arc incidences. Continuous
extension on that declared interval can then be proved or refuted.
Neither “some collar” nor a matching physical landing point identifies
that datum on its own.

## 6. How to interpret the available obstructions

The common-exterior map is a genuine based covering, and its sheet
collisions and full ideal-circle obstruction are genuine theorems about
that map. The [access-lift and germ-alignment theorem](tip_localization_access_lifts_and_germ_alignment_20261106.md)
now determines its two open boundary intervals exactly. More decisively,
lifting the map to a universal cover of its annular target gives a
biholomorphism. Its annular fibers therefore do not themselves witness
a collision between two specified KL universal-cover tiles.

In particular, full-circle failure is consistent with the standard
relative-cover boundary construction: boundary points in the deck limit
set are omitted when adjoining the boundary of a nonsimply connected
surface from its universal cover. A disk's own conformal prime-end circle
retains those points. One must state which completion and which map are
being used. The obstruction rules out the asserted full-circle extension;
it does not silently forbid all protected boundary restrictions.

The [canonical comparison theorem](tip_iterated_direct_canonical_localization_embedding_20261106.md)
now addresses the missing source identification directly. Its Theorem 4.1
embeds the iterated fine target into the direct fine target,

\[
J:\mathcal V_{3,3}\hookrightarrow\mathcal V_9,
\qquad \mathcal U=J(\mathcal V_{3,3}).
\]

The actual canonical localization projection is
`rho:(V_(3,3),K9^it) -> (T_it,A)`, where `A` is the copy of `K9` in the
coarse canonical surface `V3`, and `T_it` deletes the other two inner fine
phases. Thus `L=rho J^{-1}` is a genuine fine-to-coarse-ambient local cover
on `U`, with the **same smaller root** marked on both sides.

For the native pseudo-piece `Pbold=Psi_Gbold(P_G)` of the actual canonical
coarse map, the companion uses the full source-defined pullback carrier
`V3^m`, not the smaller ordinary physical carrier. Its inclusion immersion
`i^m` satisfies `(i^m)^{-1}(K3)=K3^m`. The native path projection therefore
gives a correctly marked map

\[
\Pi=i^m\pi_{\mathbf P}:(\mathbf P,\mathcal A^m)
                  \longrightarrow(T_{\rm it},\mathcal A),
\qquad \mathcal A^m=(i^m)^{-1}(\mathcal A).
\]

Kahn Theorem 7.12 supplies its unique localized lift `e`, and hence
`e_dir=Je`, with `L e_dir=rho e=Pi`. A positive native annular core has
winding vector `(1,1,1)` about the three inner phase continua. Every
conjugate of the fine localization subgroup has winding vector `(k,0,0)`.
Consequently Theorem 7.1 separates every integer deck orbit into distinct
actual fine sheets with one coarse image. This is a statement about an
infinite sheet fiber, not nonfaithfulness on fixed-endpoint morphism sets
of a covering groupoid.

KL §3.2.4 identifies the two wrapping limits in each native tile as
`lambda_i intersect xi_i` and `lambda_i intersect eta_i`. Two deck orbits
converging to either joint have distinct constant images under `Pi`, so
Theorem 8.1 excludes a continuous extension of this composite at the
**source-named** joints. The assertion is about the whole glued native
pseudo-piece's ideal boundary. It does not assume that `e` has already
extended those joints to prime ends of the fine canonical disk, and it
does not identify `L` with KL Lemma 3.4's inclusion immersion. This is the
source-defined sheet/side failure allowed by Issue #29, with its actual
map and marking specified.

A separate topological obstruction excludes an entire **specified map
class**. The [root-topology and marked-morphism obstruction](tip_interval_root_and_marked_morphism_obstruction_20261106.md)
uses the exact interval root `K_9` and a four-armed embedded star in
`K_3`. The weaker arc/nonarc argument already excludes local covers:
their root bijection would be a homeomorphism of compact marked sets.
The stronger argument excludes every nonconstant holomorphic marked
morphism from the full fine root to the full coarse root. Indeed,
`A=g^{-1}(B)` and compactness make `g(A)` closed in connected `B`,
while openness of `g` makes it relatively open. Hence `g(A)=B`.
At a preimage of the four-star center, local degree `d` lifts that
star to `4d` arms, which cannot be contained in an interval.

This is an actual first failure for the complete fine-to-coarse
**root-marked** proposal, not just an omitted labeling convention.
It does not refute Kahn's canonical smaller-root construction described
in §4, whose target marking is different.
It must not be generalized to arbitrary maps of restricted pieces:
their distinguished subsets may differ from the full `K_9,K_3`,
and a KL pseudo-piece immersion is not required merely by its name
to satisfy that full-root preimage condition.

The results now distinguish two proved failures: no morphism exists in the
full-root `K9 -> K3` marked category, while the actual smaller-root
canonical projection does exist and exhibits the specified infinite sheet
fiber and native wrapping-joint obstruction. Together with the side atlas
and finite germ alignment, the latter resolves the source-identification
gap for Issue #29's collision alternative. The positive comparison and
negative boundary conclusion concern the stated target surfaces and map;
they do not assert a global isomorphism of direct and iterated dynamical
pairs. Open protected subarcs avoiding the named joints, or comparisons
retaining additional unwrapped data, require their own specified maps and
are not refuted by this certificate.

## 7. Concrete citation corrections at the review base

These are locator corrections, not changes to the cited mathematical
statements. Both checked KL II PDFs support the corrected numbers. The
four independent-audit files listed below now contain these corrections;
their earlier mathematical scope remains recorded as historical work.

| File at the review base | Existing locator | Correct locator |
| --- | --- | --- |
| `tip_puzzle_ray_tree_20261106.md`, source conventions | §2.1, pp. 4–5 | §2.1, pp. 5–6 |
| `tip_localization_refinement_peripheral_monodromy_20261106.md`, §1 | KL §§2.1–2.2, pp. 4–7 | KL §§2.1–2.2, pp. 5–8 |
| Same localization note, §1 | Kahn Theorem 7.12 and §7.4.1, p. 44, including definitions | Definitions p. 43; theorem and proof p. 44; §7.4.1 spans pp. 43–44 |
| `tip_kl_top_puzzle_and_localization_complement_20261106.md`, primary-source paragraph | §2.1 pp. 4–5; Lemma 2.1 p. 5; §2.2 pp. 6–7 | §2.1 pp. 5–6; Lemma 2.1 p. 6; §2.2 pp. 7–8 |
| `kl_tip_primitive_puzzle_and_localization_20261106.md`, primary-source paragraph | Same one-page offset | Same corrected pp. 5–6, 6, 7–8 |
| Paper 1 `extracted/F_kahn_source/definitions.tex`, definition `def:local`, and its assembled counterpart | Marked/local/local-cover definitions p. 44 | p. 43 |

The last manuscript correction is recorded here without editing its
source-locked files. Citations to **Theorem 7.12 itself on p. 44 remain
correct** and must not be shifted indiscriminately. The KL terminal-child
note cites section numbers without those erroneous page ranges.

**Verification and attribution:** this is a source/type audit, not a new
finite dynamics certificate. The inspected primary PDFs, manuscript
definitions, and named source clauses determine its claims. OpenAI GPT-6
assisted retrieval, comparison, and exposition. No human specialist review
or source-author endorsement is represented. No source-locked ledger,
H1–H4, UPTCR, or MLC status is changed.
