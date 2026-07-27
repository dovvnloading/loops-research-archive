# Kahn iterate: complementary-component and same-seed alignment

## 1. Result and exact scope

This note resolves one clause left open after
`KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION`: there is no hidden choice
of connected component in the **unfilled complementary-cover equalizer**
used to iterate a fixed Kahn \(\psi\)-polynomial-like seed.

The result is:

> For every Kahn pullback iterate, the full complementary equalizer is
> connected.  After a covering/embedding factorization
> \(i_r=e_rq_r\), its base-changed resolved intermediate space is connected
> as well.  If the same fixed \(\psi\)-ql seed is used in the
> Kahn--Lyubich direct-decoration construction, the ambient iterate
> \(\mathbf U^m\setminus K^m\) is the unique ambient complementary
> component used as the tile base; it is not an independently selected
> stagewise component.  Tilewise, for each source tile, oriented annular
> degree \(+1\) identifies the pullback of its declared target
> universal-cover tile with that connected source tile, and \(q/e\) base
> change produces one connected resolved intermediate embedded in the
> target tile.

This proves only complementary-component and fixed-seed iterate alignment.
It does **not** construct:

- a filled completion of the intermediate cover \(P_r\);
- the conformal ideal circle of such a completion;
- an \(O\)-, \(\xi\)-, or \(\eta\)-side on \(P_r\);
- a prime-end extension of \(e_r\) or \(q_r\);
- an equality between the dynamical-covering and inclusion component maps;
- the actual sheet-isolated access footprint;
- a future-faithful finite compression of the infinite sheet groupoid;
- geometric final-root no-birth; or
- any width, transition, compactness, rigidity, UPTCR, or MLC conclusion.

Thus `DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`, VAAPC-I, UPTCR, and MLC
remain open.

## 2. Locked primary sources

The proof uses the complete local copies of the official arXiv source
archives already locked in `source_ledger.md`.

1. Jeremy Kahn, *A priori bounds for some infinitely renormalizable
   quadratics: I. Bounded primitive combinatorics*,
   arXiv:math/0609045:

   - source file `.tmp_kl06_source/intro.tex`, SHA-256
     `E7DD61396FEA927903D4DE4FD386E7AAEFD0BD3E2CEE1CE6F011680AD58144E0`,
     lines 254--255 define an FJ-set to be compact, connected, full, and
     nondegenerate;
   - source file `.tmp_kl06_source/psiql2.tex`;
   - SHA-256
     `E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228`;
   - lines 16--41 define a \(\psi\)-polynomial-like map, its disk domains,
     and its FJ-set;
   - lines 155--174 prove that the inclusion immersion on the
     complementary annuli has oriented inner-boundary degree \(+1\);
   - lines 259--265 prove that, when one leg is an immersion, the
     complex-manifold pullback has the ordinary topological fiber product
     as its underlying space;
   - lines 350--399 construct one pullback iterate and prove that its
     domain is a connected disk and its new filled Julia set is connected;
   - lines 410--416 define all iterates
     \((i_r,f_r):(\mathbf U^{r+1},K^{r+1})
     \to(\mathbf U^r,K^r)\);
   - lines 446--449 identify the \(\psi\)-ql marked pairs as local disk/FJ
     pairs, in particular with connected complement.

2. Jeremy Kahn and Mikhail Lyubich, *A priori bounds for some infinitely
   renormalizable quadratics: II. Decorations*,
   arXiv:math/0609046:

   - source file `.tmp_kl08_source/psiql.tex`;
   - SHA-256
     `6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF`;
   - lines 8--31 use the same iterated domains \(\mathbf U^n\);
   - lines 95--123 construct the pseudo-piece associated with a puzzle
     piece in \(\mathbf U^m\);
   - lines 169--207 distinguish the dynamical covering arrow from the
     inclusion-induced immersion;
   - lines 231--253 define the \(O\)- and \(J\)-boundary only after the
     pseudo-piece has been constructed.

No theorem about Dudko virtual carriers is imported.

## 3. Typed iterate data

Fix a degree-\(d\) \(\psi\)-polynomial-like map and its Kahn iterates

\[
 (i_r,f_r):
 (\mathbf U^{r+1},K^{r+1})
 \longrightarrow
 (\mathbf U^r,K^r),
 \qquad r\geq 0.                                   \tag{3.1}
\]

Every \(\mathbf U^r\) is a disk, every \(K^r\Subset\mathbf U^r\) is an
FJ-set, and

\[
 X_r:=\mathbf U^{r+1}\setminus K^{r+1},
 \qquad
 Z_r:=\mathbf U^r\setminus K^r                     \tag{3.2}
\]

are connected complementary surfaces.

The next pullback is

\[
 \mathbf U^{r+2}
 =
 \{(x,y)\in\mathbf U^{r+1}\times\mathbf U^{r+1}:
   i_r(x)=f_r(y)\},                                 \tag{3.3}
\]

with

\[
 f_{r+1}(x,y)=x,
 \qquad
 i_{r+1}(x,y)=y.                                   \tag{3.4}
\]

Because \(i_r\) is an immersion, Kahn's special pullback lemma says that
the complex-manifold pullback in (3.3) has the ordinary topological fiber
product as its underlying space; no desingularization is required.
Separately, all branch values of \(f_r\) lie in \(K^r\), so \(f_r\) is
unbranched on the complementary locus.  Nothing here identifies a filled
or ideal-boundary completion of a later intermediate cover.

## 4. Complementary equalizer theorem

### Theorem 4.1 -- unique complementary component

For every \(r\geq0\), put

\[
 K^{r+2}
 =
 i_{r+1}^{-1}(K^{r+1})
 =
 f_{r+1}^{-1}(K^{r+1}).                            \tag{4.1}
\]

Then

\[
 \mathbf U^{r+2}\setminus K^{r+2}
 =
 X_r\times_{Z_r}X_r
 =
 \{(x,y)\in X_r\times X_r:i_r(x)=f_r(y)\},          \tag{4.2}
\]

and this space is connected.  Consequently the full complementary
equalizer has exactly one connected component.

#### Proof

Take \((x,y)\in\mathbf U^{r+2}\).  Kahn's membership chain is

\[
 x\in K^{r+1}
 \Longleftrightarrow
 i_r(x)\in K^r
 \Longleftrightarrow
 f_r(y)\in K^r
 \Longleftrightarrow
 y\in K^{r+1}.                                     \tag{4.3}
\]

The middle equivalence uses \(i_r(x)=f_r(y)\).  The outside equivalences
are the defining identities

\[
 i_r^{-1}(K^r)=K^{r+1}=f_r^{-1}(K^r).              \tag{4.4}
\]

Thus a point of the pullback lies outside \(K^{r+2}\) exactly when both
coordinates lie outside \(K^{r+1}\).  This proves the set identity (4.2).

Kahn proves that the pullback pair

\[
 (\mathbf U^{r+2},K^{r+2})
\]

is again a \(\psi\)-polynomial-like disk/FJ pair.  For such a local marked
pair the complement

\[
 \mathbf U^{r+2}\setminus K^{r+2}
\]

is connected.  Combining this with (4.2) proves the theorem. \(\square\)

### Corollary 4.2 -- no component choice at any finite iterate

The conclusion of Theorem 4.1 holds at every finite depth of (3.1), with
no new induction hypothesis.

#### Proof

Kahn's pullback lemma says that the output of one step is again a
\(\psi\)-polynomial-like map with the same defining disk/FJ properties.
Therefore Theorem 4.1 applies successively at every finite depth.
\(\square\)

The word “finite” is essential only because the source constructs finite
iterates.  No inverse-limit or infinite-horizon topology is inferred.

## 5. Resolved factorization under the connected equalizer

Suppose at some stage that the complementary inclusion leg has the proved
factorization

\[
 i_r|_{X_r}
 =
 e_rq_r,
 \qquad
 X_r\xrightarrow{q_r}P_r\xrightarrow{e_r}Z_r,      \tag{5.1}
\]

where \(q_r\) is a surjective covering and \(e_r\) is an embedding.
Define

\[
 E_{r+1}
 :=
 X_r\times_{Z_r}X_r,
 \qquad
 R_{r+1}
 :=
 P_r\times_{Z_r}X_r,                               \tag{5.2}
\]

where the second legs in both products are \(f_r|_{X_r}\).  Put

\[
 q_{r+1}(x,y)=(q_r(x),y),
 \qquad
 e_{r+1}(p,y)=y.                                   \tag{5.3}
\]

### Theorem 5.1 -- connected resolved base change

The space \(E_{r+1}\) is the unique complementary equalizer component.
The map

\[
 q_{r+1}:E_{r+1}\longrightarrow R_{r+1}
\]

is a surjective covering, \(e_{r+1}\) is an embedding, and

\[
 i_{r+1}=e_{r+1}q_{r+1}.                           \tag{5.4}
\]

Both \(E_{r+1}\) and \(R_{r+1}\) are connected.  Hence the resolved
base-change construction contains every sheet in one and the same
complementary component.

#### Proof

Theorem 4.1 gives

\[
 E_{r+1}
 =
 \mathbf U^{r+2}\setminus K^{r+2}
\]

and proves that it is connected.

The covering, embedding, factorization, and kernel-pair statements are the
ordinary pullback identities proved in
`KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION`.  It remains only to
record surjectivity and connectedness of the resolved intermediate.
Explicitly, injectivity of \(e_r\) gives the Cartesian identification
\[
 E_{r+1}
 \cong
 X_r\times_{P_r}R_{r+1},
\]
so \(q_{r+1}\) is the base change of \(q_r\).

Take \((p,y)\in R_{r+1}\).  Since \(q_r\) is surjective, choose
\(x\in X_r\) with \(q_r(x)=p\).  Membership in \(R_{r+1}\) gives

\[
 e_r(p)=f_r(y).
\]

Using (5.1),

\[
 i_r(x)
 =
 e_r(q_r(x))
 =
 e_r(p)
 =
 f_r(y).
\]

Thus \((x,y)\in E_{r+1}\) and

\[
 q_{r+1}(x,y)=(p,y).
\]

So \(q_{r+1}\) is surjective.  Since it is continuous and
\(E_{r+1}\) is connected, \(R_{r+1}\) is connected.  There is therefore no
second component from which proof-used sheets could be omitted.
\(\square\)

### Corollary 5.2 -- finite-horizon component alignment

Starting from one factorized seed leg, the iterated \(q/e\) construction
has a unique connected source and resolved-intermediate complementary
component at every finite stage.

#### Proof

Apply Theorem 5.1 successively.  Its output \(q_{r+1}\) is again a
surjective covering, so all hypotheses needed for the next step persist.
\(\square\)

## 6. Fixed-seed direct-decoration alignment

### Theorem 6.1 -- same-seed ambient component

Fix one \(\psi\)-ql seed which also satisfies the hypotheses of the
Kahn--Lyubich direct-decoration construction.  The domains denoted
\(\mathbf U^m\) in the pseudo-piece construction are the Kahn iterates of
that same seed.  Therefore, at every direct-decoration depth \(m\),

\[
 \mathbf U^m\setminus K^m
\]

is the connected ambient complementary annulus from Corollary 4.2; there
is no second ambient component to select.  If the
inclusion leg is transported by the \(q/e\) route, Corollary 5.2 gives one
connected resolved intermediate component containing every transported
sheet.

#### Proof

Kahn defines the complete iterate tower in `psiql2.tex`, lines 410--416.
For a fixed \(\psi\)-ql map, Kahn--Lyubich then use the natural
restriction to

\[
 \mathbf U^m\longrightarrow\mathbf U^{m-1}
\]

in `psiql.tex`, lines 29--31, and define the pseudo-piece for a puzzle
piece of depth \(m\) inside that \(\mathbf U^m\) in lines 95--123.  No
second tower or independently selected pullback component is introduced.
The component statement now follows from Corollaries 4.2 and 5.2.
\(\square\)

This theorem is conditional on one fixed seed carrying the
direct-decoration hypotheses.  It does not assert that every primitive
canonical seed has a prescribed decoration, nor does it infer a new
parameter-realization theorem.

It also does not collapse the pseudo-piece tile family.  In the KL gluing
model, the components \(Y_i\) of \(Y\setminus K_Y\) are attached to
separate copies \(\widehat A_i\) of the universal cover of the one ambient
annulus.  The covering component map and the inclusion component map are
different typed maps and need not coincide.  Theorem 6.1 proves the
identity and connectedness of the ambient iterate used to define those
copies; it does not prove a tile-family bijection, an \(O\)-side
identification, or equality of the two component maps.

### Theorem 6.2 -- tilewise resolved interior alignment

Fix one inclusion stage of the same direct-decoration chain and write
\[
 A_s=\mathbf U^{m}\setminus K^m,\qquad
 A_t=\mathbf U^{n}\setminus K^n,\qquad
 \iota:A_s\longrightarrow A_t,
\]
with the factorization
\[
 A_s\xrightarrow{q}P\xrightarrow{e}A_t,\qquad \iota=e q. \tag{6.1}
\]
Fix a **source** inclusion-tile index \(i\), and let
\(j_\iota(i)\) be its target index under KL's inclusion component map.
Write
\[
 L_i:\widetilde A_{s,i}\longrightarrow
     \widetilde A_{t,j_\iota(i)}
\]
for KL's tile lift of the inclusion.  Define the \(i\)-labelled copies
\[
 \mathcal E_i
 :=\{i\}\times
   \bigl(A_s\times_{A_t}\widetilde A_{t,j_\iota(i)}\bigr),
 \qquad
 \mathcal R_i
 :=\{i\}\times
   \bigl(P\times_{A_t}\widetilde A_{t,j_\iota(i)}\bigr). \tag{6.2}
\]
Then:

1. \(\mathcal E_i\) is connected and
   \[
     (i,x,\widetilde t)\longmapsto x:
     \mathcal E_i\longrightarrow A_s
   \]
   is the universal cover;
2. if \(\pi_s:\widetilde A_{s,i}\to A_s\) is the source-tile projection,
   then
   \[
     \Phi_i(\widetilde a)
     =
     \bigl(i,\pi_s(\widetilde a),L_i(\widetilde a)\bigr)
     :\widetilde A_{s,i}\longrightarrow\mathcal E_i       \tag{6.3}
   \]
   is the unique based cover isomorphism after the source and target
   tile basepoints are fixed by KL's chosen component embeddings;
3. the base-changed map
   \[
     q_i:\mathcal E_i\to\mathcal R_i
   \]
   is a surjective covering;
4. the projection
   \[
     e_i:\mathcal R_i\hookrightarrow
         \widetilde A_{t,j_\iota(i)}
   \]
   is an embedding and the KL interior tile immersion factors as
   \[
     e_iq_i\Phi_i=L_i;                                  \tag{6.4}
   \]
   and
5. \(\mathcal R_i\) is connected.

Thus the \(q/e\) resolution loses no interior sheet inside a declared KL
source tile.  The assertion is family-valued over the **source** tile
indices.  If \(i_1\ne i_2\) but
\(j_\iota(i_1)=j_\iota(i_2)\), the two labelled copies remain distinct
even though their underlying fiber products are canonically isomorphic.

#### Proof

Both \(A_s\) and \(A_t\) are annuli.  Kahn's proof of the
quadratic-like restriction theorem applies to every \(\psi\)-ql iterate
and shows that the inclusion immersion induces oriented degree \(+1\) on
the inner boundary.  Hence
\[
 \iota_*:\pi_1(A_s)\cong\mathbb Z
 \longrightarrow\pi_1(A_t)\cong\mathbb Z
\]
is the identity after the oriented generator is fixed.  Pulling the
universal cover of \(A_t\) back along \(\iota\), the component count is
\[
 [\,\pi_1(A_t):\iota_*\pi_1(A_s)\,]=[\mathbb Z:\mathbb Z]=1, \tag{6.5}
\]
and the subgroup of the pulled cover is
\[
 \iota_*^{-1}(\{0\})=\{0\}.                         \tag{6.6}
\]
Therefore \(\mathcal E_i\) is connected and is the universal cover of
\(A_s\).

KL realize each tile as the universal cover of the corresponding ambient
annulus.  Fix a basepoint \(y_i\in Y_i\) and the compatible lifted
basepoints determined by KL's chosen source and target component
embeddings.  Since
\[
 \pi_tL_i=\iota\pi_s,
\]
formula (6.3) maps the source tile into the pullback over \(A_s\) and
sends the chosen basepoint to the chosen pullback basepoint.  Both sides
are universal covers of \(A_s\), so based-cover uniqueness makes
\(\Phi_i\) an isomorphism.  This is the deck-phase normalization; it is
performed separately for every source index.

The square
\[
\begin{array}{ccc}
\mathcal E_i&\longrightarrow&A_s\\
\downarrow q_i&&\downarrow q\\
\mathcal R_i&\longrightarrow&P
\end{array}
\]
is the pullback of the surjective covering \(q\), so \(q_i\) is a
surjective covering.  The same pointwise calculation as in Theorem 5.1
shows that \(e_i\), the projection to
\(\widetilde A_{t,j_\iota(i)}\), is an embedding.  Substitution in the
definitions gives (6.4).  Finally,
\(\mathcal R_i=q_i(\mathcal E_i)\) is connected because \(q_i\) is
continuous and surjective. \(\square\)

The direct-decoration dynamical covering arrow has its own component map,
while the inclusion arrow treated above has another.  Even in a
degree-one branch, the source does not identify these two maps.
No later argument may replace one with the other without a separate
proof.

## 7. Why this does not yet construct the resolved \(O\)-side

The source defines the \(O\)-boundary only for the completed pseudo-piece

\[
 \mathbf Y
 =
 Y\sqcup_{e_i}\widehat A_i,
\]

whose ideal boundary is tiled by the \(\lambda_i,\xi_i,\eta_i\) arcs.
The intermediate \(P_r\) in (5.1) is presently only a connected cover on
the complementary locus.  Connectedness does not supply:

1. a disk or full-carrier completion of \(P_r\);
2. an extension of \(e_r\) to a conformal ideal circle;
3. the lift or image of each \(\lambda_i,\xi_i,\eta_i\);
4. cyclic-order preservation at wrapping and Julia vertices;
5. classification of every proper and nonproper competing lift; or
6. singleton KKL-proper-lift isolation.

Fullifying \(e_r(P_r)\) inside a target disk is not automatic: a filled
component can create or merge accesses even though the unfilled
complementary locus was connected.  Therefore Theorem 6.1 closes the
component-selection clause but not the analytic \(O\)-side clause.

The initially proposed full ideal-boundary theorem is now refuted in its
full-prime-end form by
`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY`.  Tilewise,
\(q_i:\mathcal E_i\to\mathcal R_i\) is a universal cover.  If it is
nontrivial, it cannot extend continuously through any point of its deck
limit set to a Hausdorff completion.  Kahn's own ideal bordification
therefore removes that limit set.

The same no-go exposes a necessary correction to the application scope.
KL identifies the two actual-tile annular wrapping points and extends its
actual tile composite there.  A based source-cover biholomorphism
transports those points and the composite to the resolved source disk.
Therefore any whole-tile covering/embedding
factorization of that actual map is one-sheeted.  The canonical
infinite-sheet resolution cannot be silently identified with it.

The correspondence audit is now complete in the whole-tile branch:
`CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO` proves that the
five-clause end-compatible comparison square cannot exist when the
canonical deck kernel is nontrivial.  This is not an injectivity theorem
for the actual KL immersion.  The subsequent restricted-interface
classification constructs one replacement at the interior level:

> **Canonical/KL relation proper-end response.**  For every supplied
> fixed labeled same-source datum, use the proved relation span and tagged
> maximal interior restrictions.  Realize them on the complete Wave
> horizon; compute the authorized relative ideal incidence with the actual
> KL \(\lambda,\xi,\eta\) marking; classify all proper, end-proper, and
> nonproper components; and prove exhaustion or a uniform
> Value-observable response.  The first missing alignment, endpoint,
> competing component, access merger, or unbounded response is the
> failure certificate.

## 8. Adversarial checks

### 8.1 Dropping fullness

A connected compact set in a disk can separate the disk if it has a
bounded complementary component.  Thus connectedness of \(K^{r+2}\) alone
would not prove connectedness of its complement.  The FJ/full hypothesis
and Kahn's local marked-surface conclusion are essential.

### 8.2 Dropping properness of \(f_r\)

Kahn uses properness to show that every component of the pullback domain
meets \(K^{r+2}\).  Without it, an extra component disjoint from the filled
set can occur.  The theorem is not a statement about arbitrary
equalizers.

### 8.3 Confusing connected source with connected target

Connectedness of \(E_{r+1}\) implies connectedness of \(R_{r+1}\) only
because \(q_{r+1}\) is proved surjective.  The explicit preimage
calculation in Theorem 5.1 is therefore necessary.

### 8.4 Importing the irrelevant general desingularization

Kahn discusses desingularization for a general pullback only after proving
the special lemma used here.  Since \(i_r\) is an immersion, the iterate
pullback already has the ordinary topological equalizer as its underlying
space, even over branch values of \(f_r\).  The separate branch-value
statement is used to know that \(f_r\) is unbranched on the complement,
not to repair the topology of the equalizer.

### 8.5 Replacing fixed-seed alignment by parameter existence

Theorem 6.1 says that two constructions applied to one fixed seed use the
same iterate tower.  It does not prove that every seed realizes one
specified decoration, and it does not enlarge the parameter class covered
by the source.

### 8.6 Calling connectedness an \(O\)-footprint

A connected open surface can have many inequivalent end compactifications
and infinitely many access lifts.  No footprint or KKL subordination
statement follows until the completion and endpoint maps are constructed.

### 8.7 Collapsing the KL tile family to the ambient annulus

The connected annulus \(\mathbf U^m\setminus K^m\) is the base of several
separately glued universal-cover copies \(\widehat A_i\).  Its
connectedness neither identifies those copies nor equates the covering
and inclusion component maps.  Every later endpoint theorem must remain
tilewise and retain the relevant component index.

### 8.8 Equating the dynamical and inclusion component maps

KL construct the tile-component map for the dynamical covering separately
from the tile-component map for the inclusion immersion.  The latter is
only stated to be surjective and need not be injective.  Even when
additional hypotheses make both maps bijections, they need not be equal.
Theorem 6.2 fixes one inclusion lift for each source tile; it does not
identify the two component maps.

### 8.9 Extending a composite by extending its factors

KL prove a continuous boundary extension for the composite pseudo-piece
immersion and warn that its boundary image need not lie in the target
boundary.  Continuity of \(e_iq_i\) at an ideal end does not imply that
either factor extends to a chosen compactification.  In fact,
`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY` proves that a nontrivial
universal-cover factor cannot extend over its full prime-end circle, and
`CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO` excludes the complete
canonical/actual-KL comparison square.  The later restricted-interface
classification constructs a relation-valued **interior** span for each
supplied aligned datum, but only its separately proved
domain-of-discontinuity and glued-boundary portions may be bordified.

### 8.10 Extending an infinite cover over its full prime-end circle

Rejected by
`RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY`, Theorem 6.2.  If
\(\gamma\) is a nontrivial deck transformation with attracting boundary
point \(\zeta\), then
\[
 q_i(\gamma^n z)=q_i(z),\qquad \gamma^n z\to\zeta.
\]
Continuity at \(\zeta\) would make \(q_i(z)\) independent of \(z\).
Thus the required replacement is the limit-set-excised relative boundary,
not a full factorwise prime-end completion.

## 9. Ledger effect

The internally proved obligation

`KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT`

may be promoted.  It depends on:

- `KL_CANONICAL_LOCALIZATION_FORCED_COLLISION`, for the actual Kahn
  iterate/equalizer route; and
- `KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION`, for the \(q/e\)
  base-change factorization.

It discharges only the connected complementary-component and fixed-seed
iterate-alignment clauses.  `DIRECT_DECORATION_OUTER_CAP_FOOTPRINT` must
remain open.  The whole-tile map-level correspondence between the
canonical resolved cover and the actual KL tile is now ruled out.  The
first unresolved object is a restricted comparison with complete
proof-use or defect-window control, followed by relative-boundary
correspondence; it is not selection among components of the unfilled
equalizer and not a full-prime-end factor extension.

VAAPC-I, UPTCR, and MLC remain open.
