# Actual KL tile injectivity: exact reduction and source obstruction

## 1. Result of this pass

Fix a Kahn--Lyubich direct-decoration branch

\[
 Q=Q_a\subset P,\qquad a\in\{L,R\},
\]

at a general \(\psi\)-quadratic-like stage, and let

\[
 \boldsymbol\iota:\mathbf Q\longrightarrow\mathbf P
\]

be the inclusion-induced pseudo-piece immersion.

This note first proved the following exact reduction.

> **Tile/base equivalence.**  Every universal-cover tile map induced by the
> relevant degree-one bold ambient annulus immersion is injective if and
> only if that base annulus immersion is injective.

It also proved a usable sufficient condition.

> **Properness criterion.**  A proper degree-one holomorphic immersion
> between connected annuli is a biholomorphism.  Hence full properness of
> the actual bold ambient annulus immersion would prove tile injectivity.

### 1.1 Superseding canonical-stage result

The subsequent component-level audit in
`kl_canonical_localization_forced_collision.md` resolves the canonical
seed in the negative.  For every ordinary primitively
\(p\)-renormalizable quadratic stage, \(p>1\), source localization removes
a noncentral component

\[
 X\subset (f^p)^{-1}(K_p),
\]

while target localization fills it back because
\(X\cap\mathcal K_p=\varnothing\).  A peripheral loop \(\gamma\) around
\(X\) satisfies

\[
 [\gamma]\notin H_s,\qquad (i^p)_*[\gamma]=1\in H_t.
\]

Its source lift has distinct endpoints which the localized inclusion
identifies.  Kahn's exact equalizer iteration propagates this collision to
every later bold inclusion map.  Whenever the same realized seed carries
KL direct-decoration data, the collision occurs at the exact depths

\[
 m=\nu q+1,\qquad n=(\nu-1)q+1,
\]

and forces noninjectivity of every full tile lift and of the full glued
pseudo-piece inclusion.  The parameter/stage-alignment quantifier is
recorded separately in Section 8 of the collision note.

The former universal full-embedding route is therefore unavailable.
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING` is retained only as a
non-gating classification question for restricted stages, if any.  The
universal descendants have been rerouted to a sheet-sensitive immersed
carrier retaining

\[
 a_*^{-1}(H_t)/H_s
\]

and the complete sheeted path groupoid.

The historical source audit below explains why the earlier source
statements did not license global univalence; its final open verdict is
superseded by the theorem above.

The checked KL sources do not supply either global base-annulus
injectivity or full properness.  They supply:

- an immersion on the bold ambient domains;
- degree one on the inner annular end;
- injectivity on a sufficiently thin inner collar; and
- only the end-properness needed for the little-Julia-set ends in their
  width argument.

Thus this pass does **not** prove
`DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING`.  It replaces the vague
request “prove tile injectivity” by one source-specific question:

\[
 \boxed{\text{Is the actual bold ambient annulus immersion globally
 univalent?}}
\]

If the answer is no, the first failure certificate is an actual pair of
distinct base points with the same image, together with the forced deck
collision described in Section 5.

The separate exact counterexample in
`kahn_annulus_global_injectivity_no_go.md` proves that even all abstract
hypotheses of Kahn's annulus lemma do not imply global injectivity.  It
satisfies the analytic inner-circle extension, an orientation-preserving
degree-one inner boundary map, local univalence, and the exact
\(r'=r^{1/d}\) modulus relation.  It is not an actual dynamically
generated KL block.  The canonical theorem in Section 1.1, rather than
this abstract example, now supplies the actual dynamical obstruction.

VAAPC-I, UPTCR, and MLC remain open.

## 2. Source lock

The relevant primary sources are:

- Jeremy Kahn and Mikhail Lyubich, *A priori bounds for some infinitely
  renormalizable quadratics. II. Decorations*,
  arXiv:math/0609046;
- Jeremy Kahn, *A priori bounds for some infinitely renormalizable
  quadratics. I. Bounded primitive combinatorics*,
  arXiv:math/0609045.

The local source copies and hashes are recorded in `source_ledger.md`.
Only the following source statements are used here.

### 2.1 Ordinary quadratic-like nesting

Kahn I, `pullback.tex`, lines 2--7 and 25--36, works first with an ordinary
quadratic-like map and states

\[
 U^{n+1}\subset U^n.
\]

The third map in the pullback triangle is explicitly the physical
inclusion and hence an embedding.

### 2.2 Passage to bold \(\psi\)-ql domains

Kahn I, `conclusions.tex`, lines 33--49, replaces that physical inclusion
by

\[
 i:\mathbf U^{n+1}\setminus\mathcal K
   \longrightarrow
   \mathbf U^n\setminus\mathcal K.
\]

The source calls \(i\) an **immersion**, explicitly says that this is the
significant change from the quadratic-like setting, and uses only
properness at the ends corresponding to \(\mathcal K\).

The boldface is not typographical decoration: KL II, `macros.tex`, line
261 defines

\[
 \texttt{\textbackslash BU}=\mathbf U.
\]

### 2.3 Pseudo-piece tiles and naturality

KL II, `psiql.tex`, lines 95--123, constructs a pseudo-piece from the
central puzzle piece and copies of the universal cover of

\[
 A_m=\mathbf U^m\setminus K(f).
\]

For \(Y\subset Z\), `psiql.tex`, lines 198--206, states that the relevant
map of triples

\[
 i:(\mathbf U^m,Y,K_Y)\longrightarrow
   (\mathbf U^n,Z,K_Z)
\]

is an immersion.  Its restrictions embed the finite central components,
but the induced maps between the full annular universal-cover tiles are
only asserted to be immersions.

This distinction is decisive: injectivity on the central component used
for gluing does not imply injectivity on the entire ambient annulus.

There are also two different arrows.  In `psiql.tex`, lines 186--196, the
dynamical branched covering induces isomorphisms of the corresponding
universal-cover tiles.  That is the \(\mathbf g\)-arrow.  The
direct-decoration embedding gate concerns the separate
\(\boldsymbol\iota\)-arrow induced by inclusion; its source statement is
lines 198--206 and says **immersion**.  Injectivity of \(\mathbf g\) cannot
be transferred to \(\boldsymbol\iota\).

### 2.4 What is known near the inner end

Kahn I, `psiql2.tex`, Lemma `lem:ann-immerse`, lines 87--98 and proof
lines 118--130, considers a holomorphic annulus immersion extending to the
inner circle with degree one.  It proves embedding only on a sufficiently
thin inner collar.

In the proof of the quadratic-like extension theorem, `psiql2.tex`, lines
155--177, the bold ambient immersion is uniformized by such an annulus
immersion.  The source concludes with a controlled embedded collar, not
global annular univalence.  The single-step induced homomorphism on the
oriented annular fundamental group is therefore \(+1\).  Every
deeper-to-shallower inclusion transition is a finite composition of these
single-step maps, so its induced homomorphism is again multiplication by
\(1\).  This is the degree-one input used in Section 3; it is not an
injectivity input.

### 2.5 Nonproper outer behavior

KL II, `psiql.tex`, lines 248--253, states that the pseudo-piece immersion
extends continuously to the named boundary but warns that the image of
the source boundary need not lie in the target boundary.

KL II, `moduli.tex`, lines 420--443, uses maximal initial lifts that can
terminate on the source \(O\)-boundary.  This is consistent with loss of
properness at the outer end and does not provide full properness.

No source statement above proves global base-annulus injectivity.

## 3. Abstract annular setup

Let \(A_s,A_t\) be connected annuli.  Let

\[
 \pi_s:\widetilde A_s\longrightarrow A_s,
 \qquad
 \pi_t:\widetilde A_t\longrightarrow A_t
\]

be universal covering maps.  Choose positively oriented deck generators
\(T_s,T_t\).

Let

\[
 I:A_s\longrightarrow A_t
\]

be a holomorphic immersion whose induced homomorphism on fundamental
groups has degree one.  Let

\[
 L:\widetilde A_s\longrightarrow\widetilde A_t
\]

be a lift:

\[
 \pi_t\circ L=I\circ\pi_s. \tag{3.1}
\]

After choosing compatible positive generators, lifting uniqueness gives

\[
 L\circ T_s=T_t\circ L. \tag{3.2}
\]

Indeed, both sides of (3.2) lift \(I\circ\pi_s\), and their deck
displacement is the integer \(I_*(1)=1\).

The degree-one condition is essential for the equivalence below.  For a
degree-\(d>1\) covering of annuli, a lift can be injective while the
quotient map is \(d\)-to-one.

## 4. Tile/base injectivity equivalence

### Theorem 4.1

Under the assumptions of Section 3,

\[
 \boxed{L\text{ is injective}\quad\Longleftrightarrow\quad
 I\text{ is injective}.} \tag{4.1}
\]

### Proof: base injectivity implies lift injectivity

Assume that \(I\) is injective and suppose

\[
 L(x)=L(y). \tag{4.2}
\]

Projecting by \(\pi_t\) and using (3.1) gives

\[
 I(\pi_s(x))=I(\pi_s(y)).
\]

Injectivity of \(I\) gives

\[
 \pi_s(x)=\pi_s(y).
\]

Universal-cover fibers are deck orbits, so there is a unique
\(k\in\mathbb Z\) with

\[
 y=T_s^k x. \tag{4.3}
\]

Using (3.2),

\[
 L(y)=L(T_s^k x)=T_t^kL(x). \tag{4.4}
\]

Equations (4.2) and (4.4) show that \(T_t^k\) fixes \(L(x)\).  A deck
transformation of a covering acts freely; hence \(k=0\).  Equation (4.3)
then gives \(x=y\).  Thus \(L\) is injective.

### Proof: lift injectivity implies base injectivity

Assume that \(L\) is injective and suppose, toward a contradiction, that

\[
 I(u)=I(v),\qquad u\ne v. \tag{4.5}
\]

Choose lifts \(x,y\in\widetilde A_s\) with

\[
 \pi_s(x)=u,\qquad\pi_s(y)=v.
\]

By (3.1), \(L(x)\) and \(L(y)\) project to the same point of \(A_t\).
Therefore there is a unique \(k\in\mathbb Z\) such that

\[
 L(y)=T_t^kL(x). \tag{4.6}
\]

Equivariance (3.2) gives

\[
 L(T_s^{-k}y)
 =T_t^{-k}L(y)
 =L(x). \tag{4.7}
\]

The two source points in (4.7) are distinct, because

\[
 \pi_s(T_s^{-k}y)=v\ne u=\pi_s(x).
\]

Equation (4.7) contradicts injectivity of \(L\).  Hence \(I\) is
injective.  This proves (4.1).  \(\square\)

### Audit of every hypothesis

1. Holomorphicity is not needed for the deck calculation; continuity and
   the lifting relation suffice.
2. The immersion hypothesis identifies the analytic KL setting but is not
   used to turn a noninjective base map into an injective lift.
3. Degree one is used exactly in (3.2).  It is what permits the target deck
   displacement in (4.6) to be cancelled by the same integer source deck
   displacement in (4.7).
4. Connected annuli have deck groups \(\mathbb Z\), and their universal
   covering deck actions are free.
5. No boundary local connectivity, properness, or compactness is assumed.

## 5. Exact collision certificate

Theorem 4.1 turns a base collision into a canonical tile collision.
For the actual KL stage, a failure certificate consists of

\[
 \mathfrak C_{\mathrm{tile}}
 =
 (m,n,i,j,u,v,w,x,y,k), \tag{5.1}
\]

where:

- \(m>n\) are the source and target bold ambient depths;
- \(i\) is the source tile/component and \(j=j(i)\) its target tile;
- \(u,v\in A_s=\mathbf U^m\setminus K(f)\) are distinct;
- \(w=I(u)=I(v)\in A_t\);
- \(x,y\) are chosen lifts of \(u,v\);
- \(k\) is determined by \(L(y)=T_t^kL(x)\).

The resulting exact same-tile collision is

\[
 x\ne T_s^{-k}y,
 \qquad
 L(x)=L(T_s^{-k}y). \tag{5.2}
\]

Because each universal-cover tile embeds in its source pseudo-piece before
the prescribed central overlap identifications, (5.2) is an actual
interior collision of the glued pseudo-piece map.  It is not a collision
of labels or an artifact of a finite quotient.

Conversely, a same-tile collision projects to a collision of \(I\).
Thus (5.1) is complete for this gate: no additional combinatorial label is
needed to decide same-tile injectivity, although component, sheet, and
return data remain necessary downstream.

## 6. Full properness is sufficient

### Proposition 6.1

Let \(I:A_s\to A_t\) be a proper holomorphic immersion between connected
annuli.  If its oriented annular degree is one, then \(I\) is a
biholomorphism.  In particular, every universal-cover lift of \(I\) is
injective.

### Proof

A holomorphic immersion between Riemann surfaces is a local
biholomorphism.  Therefore \(I(A_s)\) is open in \(A_t\).

A proper continuous map from a locally compact Hausdorff space to a
Hausdorff space is closed.  Hence \(I(A_s)\) is also closed in \(A_t\).
The target annulus is connected and the image is nonempty, so

\[
 I(A_s)=A_t. \tag{6.1}
\]

A proper local homeomorphism is a covering map.  For completeness, each
target point has a discrete fiber by local injectivity and a compact fiber
by properness, hence a finite fiber.  Choose pairwise disjoint local
inverse neighborhoods around the finitely many preimages; properness
excludes additional preimages after the target neighborhood is shrunk.
Thus the target has an evenly covered neighborhood.

The number \(N\) of sheets of a connected covering of annuli is the index
of the induced subgroup

\[
 I_*\pi_1(A_s)\subset\pi_1(A_t).
\]

For an orientation-preserving holomorphic annulus covering, \(I_*\) is
multiplication by \(N\).  The assumed degree is one, so \(N=1\).
Therefore \(I\) is bijective.  A bijective local biholomorphism has a
holomorphic inverse, so it is a biholomorphism.  The final assertion follows
from Theorem 4.1.  \(\square\)

### Scope

Proposition 6.1 requires properness of the whole annulus map.  Properness
at the inner end alone is not the stated hypothesis and cannot be
substituted into the proof: it does not make the image closed, does not
make all fibers compact, and does not produce an evenly covered
neighborhood at values approached from the outer source end.

This paragraph records a missing hypothesis, not a claim that every
one-end-proper degree-one immersion is noninjective.

## 7. Why the physical-nesting proof does not apply

The tempting argument is:

1. \(Q\subset P\) as physical puzzle pieces;
2. therefore
   \(\mathbf U^m\setminus K(f)\subset
     \mathbf U^n\setminus K(f)\);
3. therefore the annulus map is an inclusion;
4. therefore every universal-cover lift is injective.

Step 2 is invalid at a general \(\psi\)-ql stage.

The source central pieces \(Q\subset P\) lie in the embedded
quadratic-like restriction near the filled Julia set.  The attached tiles,
however, are universal covers of the full **bold ambient annuli**
\(\mathbf U^m\setminus K(f)\).  Their transition is induced by the bold
ambient immersion, not by a global physical inclusion.

The ordinary quadratic-like argument is nevertheless a valid positive
control.  In that model the base annulus map really is a nested inclusion,
so it is injective; Theorem 4.1 then proves tile injectivity.  The ordinary
embedded presentation also reflects its declared central/tile overlaps,
so the corrected tile-gluing criterion proves the glued pseudo-piece
embedding.

The positive control cannot be promoted to the general \(\psi\)-ql
setting without proving a conjugacy or realization that turns the whole
bold annulus immersion into an actual embedded inclusion.

## 8. Relationship to the existing no-go example

The proved map

\[
 F_a(z)=z+\frac{a}{2\pi i}e^{2\pi iz}
\]

shows that degree one, deck equivariance, and holomorphic local
univalence do not by themselves imply injectivity.  It descends to a
noninjective annulus immersion and has an exact collision.

That example is not claimed to satisfy every KL inner-end condition.
Accordingly, it cannot decide whether the narrower dynamically generated
KL class is globally univalent.  Its role is only to invalidate a proof
that uses degree and immersion alone.

Theorem 4.1 sharpens the lesson: deck algebra does not remove collisions
of distinct base points.  It transports them exactly to the tile.

An exact stronger no-go is now available.  The finite Blaschke quotient in
`kahn_annulus_global_injectivity_no_go.md` satisfies the full abstract
annulus hypotheses used in Kahn's collar lemma, with
\[
 r'=\frac{1287}{1000},\qquad r=(r')^{16},
\]
and even maps the inner circle homeomorphically to itself.  Exact Sturm and
Rouché certificates prove that it is an immersion of
\(\mathbb A(1,r')\) into \(\mathbb A(1,r)\) with a self-collision.  Thus
no proof from Kahn's stated annular hypotheses alone can upgrade the
inner-collar theorem to global injectivity.

This still does not decide whether the additional dynamically generated
KL path-space structure rules out the counterexample mechanism.

## 9. Consequence for the fixed direct-decoration pair

For the fixed pair, the following equivalence is now exact:

\[
\begin{aligned}
 &\text{global univalence of the actual bold base-annulus immersion}\\
 &\quad\Longleftrightarrow
   \text{injectivity of every corresponding universal-cover tile lift},
  \\[2mm]
 &\text{injectivity of every corresponding universal-cover tile lift}
 \quad\Longleftrightarrow\quad
 \text{injectivity of the glued pseudo-piece immersion}.
\end{aligned}
\tag{9.1}
\]

For every canonical seed covered by the forced-collision theorem, the
three equivalent statements in (9.1) are false.  The equivalence remains
useful: it transports the actual base collision, rather than an abstract
countermodel, to every full tile and then to the glued pseudo-piece.

The second equivalence is the corrected
`TILE_INJECTIVITY_GLUE_EMBEDDING_CRITERION`; it uses bijectivity of the
fixed-pair component map.  For a target component \(P_{j(i)}\),

\[
 Q\cap P_{j(i)}=Q_i.
\]

If a tile point \(x\) collides in the target quotient with
\(z\in Q\), then \(z\in Q_i\).  Overlap commutation gives

\[
 L_i(e_i(z))=\widetilde e_{j(i)}(z)=L_i(x),
\]

and tile injectivity gives \(x=e_i(z)\).  Thus the collision was already a
source gluing identification.  Conversely, glued injectivity restricts to
tile injectivity because each tile embeds in the source pseudo-piece.

The stronger equality

\[
 L_i^{-1}\!\left(\widetilde e_{j(i)}(P_{j(i)})\right)=e_i(Q_i)
\tag{9.2}
\]

is not required for interior embedding.  A point lying over
\(P_{j(i)}\setminus Q\) has no source-central mate and therefore creates
no tile--central collision.  Equation (9.2) is a non-gating central-image
saturation question that may still matter for collar or footprint
exhaustion.  The exact proof and analytic positive/negative controls are
in `kl_relative_overlap_cartesianity.md`.

## 10. Resolved collision and replacement obligation

The collision alternative is now proved for every ordinary primitive
canonical seed.  The universal program must use Route C or Route D below.
Route A survives only as a non-gating question for a separately specified
restricted class that excludes the canonical obstruction.

### Route A: restricted-class base univalence only

For a restricted noncanonical class, one may still ask whether

\[
 I_{m,n}:
 \mathbf U^m\setminus K(f)
 \longrightarrow
 \mathbf U^n\setminus K(f)
\]

is injective on the whole annulus.  This cannot be a universal hypothesis:
Section 1.1 and the collision theorem refute it at canonical primitive
seeds.  Any restricted theorem must state how it excludes the excess
component \(X\).  Sufficient structures would include:

- full properness, by Proposition 6.1;
- an embedded realization natural on the entire annulus;
- a source-specific no-overlap theorem that controls all inverse branches,
  including the outer end.

### Optional saturation audit: full overlap reflection

Full overlap reflection (9.2) is not part of the interior embedding route.
If a later footprint, carrier-exhaustion, or collar theorem needs it, that
later theorem must prove it or record the first

\[
 x\notin e_i(Q_i),
 \qquad
 L_i(x)\in\widetilde e_{j(i)}(P_{j(i)}),
\]

together with its component, sheet, access, itinerary, and whether the
target central point lies in \(Q\).  If it lies in \(Q\), tile injectivity
already rules the event out.  If it lies in \(P_{j(i)}\setminus Q\), it is
a saturation or footprint defect, not an interior quotient collision.

### Route B: actual collision -- completed

`kl_canonical_localization_forced_collision.md` constructs the complete
certificate from an excess component
\(X\subset(f^p)^{-1}K_p\), its isolating Jordan access, full \(p\)-step
component itinerary, subgroup class
\([\gamma]\in (i^p)_*^{-1}(H_t)\setminus H_s\), distinct source cosets,
and common target point.  The exact equalizer recursion transports it to
the direct-decoration depths whenever the seed is aligned.  The
replacement invariant must retain these distinct sheets through the
proper-path and complement-access calculus; quotienting them into one
ribbon-tree label is forbidden.

### Route C: replace global embedding by an immersion theorem

Prove the KKL marked pullback directly for the noninjective immersion,
with:

- every source sheet represented;
- every proper target path and every proper source restriction exhausted;
- deck subgroup and multiplicity recorded;
- every nonproper \(O,\xi,\eta\) access classified;
- proper or end-proper behavior on every proof-used ideal interval.

Route B is completed analytically.  Routes C and D, including their
uniform width and complete-horizon clauses, remain open.

### Route D: truncate to the proved embedded collar

Kahn's annulus lemma supplies an embedded inner collar.  One may therefore
define a new carrier by attaching only the lifted embedded collars to the
central piece.  Every path, component, or access leaving a collar must then
be recorded as an explicit outer-defect state.

This is not the original KL pseudo-piece: its tiles are truncated, its
ideal boundary changes, and its curve families need not have the original
pseudo-modulus.  Route D is valid only after proving:

1. a comparison theorem between the truncated-carrier widths and the full
   KL pseudo-widths used by Wave and covering arguments;
2. exhaustion of every path segment that leaves the collar;
3. a uniform bound or summable charge for the new outer-defect state; and
4. naturality of collar choices through the complete Wave horizon.

Without these results, relabeling the truncated carrier as the KL
pseudo-piece would merely hide the missing outer sheets.

## 11. Skeptic audit

1. **Physical/bold conflation.**  Rejected by the macro definition and the
   explicit source replacement of an embedding by an immersion.
2. **Degree-one shortcut.**  Rejected by the existing equivariant
   locally-univalent counterexample.
3. **Fundamental-group shortcut.**  The induced map on \(\pi_1\) controls
   deck displacement, not collisions of distinct base points.  Theorem
   4.1 proves that such collisions survive upstairs.
4. **Inner-collar shortcut.**  Kahn's collar theorem proves only a
   restricted injective subannulus.  The pseudo-piece tiles are full
   universal covers of the ambient annuli.
5. **One-end/full-properness conflation.**  Proposition 6.1 uses the whole
   map being proper.  The source does not supply that hypothesis.
6. **Component-bijection shortcut.**  Bijection of distinct tile labels
   excludes different-tile collisions only.  It says nothing about two
   points in the same tile.
7. **Dynamical/inclusion-arrow conflation.**  KL tile isomorphisms for the
   dynamical covering \(\mathbf g\) do not prove injectivity of the
   distinct inclusion immersion \(\boldsymbol\iota\).
8. **Boundary-extension shortcut.**  Continuous extension to the named
   ideal boundary does not imply that the boundary maps to the target
   boundary, much less that the interior map is proper.
9. **Counterexample scope.**  The generic no-go example remains only an
    abstract control.  The actual canonical collision is instead proved
    from the excess component \(X\), finite full pullbacks, winding, and
    the exact localization subgroups.
10. **Collar-truncation shortcut.**  The proved inner collar may define a
    new carrier only with a width-comparison theorem and explicit
    outer-defect state.  It is not the full KL tile.
11. **Full-overlap overconstraint.**  Forward commutation alone does not
    reflect target identifications, but full inverse-image reflection is
    stronger than an embedding proof needs.  Component bijectivity
    restricts a collision-relevant target overlap to \(Q_i\), and full
    tile injectivity then gives the exact relative reflection.  This does
    not remove a collar-level inverse-component or saturation hypothesis
    from any theorem that knows injectivity only on a truncated tile.
12. **Global promotion.**  The collision theorem disproves a universal
    full embedding; it proves no sheet-sensitive footprint, no uniform
    Wave-horizon theorem, and no MLC gate.

## 12. Status

This note proves:

- `KL_TILE_INJECTIVITY_BASE_ANNULUS_REDUCTION`.

Together with the separate exact certificate, the pass also proves:

- `KAHN_ANNULUS_GLOBAL_INJECTIVITY_NO_GO`.
- `KL_CANONICAL_LOCALIZATION_FORCED_COLLISION`.

It does not prove:

- `DIRECT_DECORATION_TILE_CENTRAL_OVERLAP_REFLECTION` (the stronger,
  non-gating saturation equality);
- `DIRECT_DECORATION_DEGREE_ONE_PSEUDO_EMBEDDING` for any separately
  specified restricted class; this node is non-gating;
- `DIRECT_DECORATION_OUTER_CAP_FOOTPRINT`;
- `DIRECT_DECORATION_PSEUDO_PIECE_PATH_LIFT_EXHAUSTION`;
- `VIRTUAL_WAVE_MARKED_CORRESPONDENCE`;
- VAAPC-I;
- UPTCR;
- MLC.
