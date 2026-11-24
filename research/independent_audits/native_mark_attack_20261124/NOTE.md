# Two component conventions, simple leaves, and the native finite action

**24 November 2026.** Investigation of main `9340778fa59029e1bfba88639b03dfb63115cab3`.
Written with OpenAI GPT-6 Astra Pro assistance. These are mathematical
arguments and an exact finite replay, not a Lean formalization or independent
human review.

## 1. Results and trust boundary

This note makes three distinct advances at the selected real slit interface.

1. **Repeated component occurrences do not obstruct the ideal-set formula.**
   The occurrence-indexed component convention in the
   [24 November proof](../immersion_mark_resolution_20261124/NOTE.md) can be
   replaced by the ordinary **set** of maximal restrictions modulo
   reparameterization. Both give the same greatest ideal-set pullback,
   `q^{-1}(X)`, for connected inner sets and give the outer circle for the
   outer circle. The new ingredient is a finite-repetition theorem and a
   finite-pasting argument. Equality of the two path operations is false;
   equality of their ideal-set operations is true.
2. **Simple parent leaves have no extra nontrivial trace-contained arc
   classes.** Every trace-contained proper path is homotopic relative to
   its ideal endpoints either to a full maximal component, possibly
   reversed, or to a null hairpin. This addresses simple lamination leaves
   directly, while retaining the distinction between a path, its trace,
   its homotopy class, and a repeated occurrence.
3. **A source-imported route exists for the original finite marking.** The
   selected map has KKL's actual Hubbard tree and satisfies the background
   conditions of Propositions 6.5–6.6 with rotation `1/2` and `b=2`.
   Importing those propositions therefore identifies the native action on
   the original multi-intervals and their closures without importing the
   stronger premise (MC). Together with Proposition A.14, this rules out
   nonempty unbreakable lamination chains through five successive pushes
   from a crest containing an original marked interval.

The third item is explicitly a consequence **of imported KKL propositions**.
It is not an independent repair of every definition or proof in KKL. In
particular, the source's literal all-trace-contained-paths reading still
has the vacuity problem diagnosed in the previous note. We do not silently
replace that reading or promote the archive's full `MARK` audit. The
new independent theorems in §§3–4 narrow the gap; the source-imported
application in §§5–6 has a different trust boundary.

No part of this note establishes arbitrary finer-subarc native dynamics,
width retained by a descendant, a compatible all-scale tower, or MLC.

## 2. Physical setting

Use the actual physical input package in
[the family bridge, §§1–3](../../tip_family_theorem/PHYSICAL_BRIDGES.md),
[the intrinsic class theorem](../marked_slit_path_bridge_20261123/IDEAL_BOUNDARY.md),
and the strict-boundary argument in
[the selected access note, Lemma 1.1](../maximal_native_wave_20261123/NOTE.md).
For each selected period `p >= 3`, write `g=f_c^p` and `y_j=g^j(0)`.
There are bounded Jordan disks `V` compactly contained in `U=D(0,R)` with
analytic source boundary, and `g:V -> U` is a proper degree-two map.
The actual tree and pullback tree are

\[
 T=[y_2,y_1],\qquad T'=[-y_1,y_1],\qquad
 \Omega=U\setminus T,\qquad \Omega'=V\setminus T'.
\]

The immersion is the inclusion. The complement in the target has two
disjoint relatively closed components:

\[
 \Omega\setminus\Omega'=(U\setminus V)\sqcup X_{\rm sl},
 \qquad X_{\rm sl}=[-y_1,y_2).
 \tag{2.1}
\]

Let `C,O` and `C',O'` be the genuine inner and outer ideal circles. At the
old left tip `y_2`, the target has one access `tau`; the source has two
accesses `u_+,u_-`. Let `A` be the closed arc of `C'` running from `u_+`
along the added slit, around its new tip, and back to `u_-`.
The contour map

\[
 q:C'\longrightarrow C
\]

agrees with the boundary inclusion off `A` and maps the whole `A` to
`tau`. All source ideal points over the interior of the added slit belong
to `A^o=A\setminus\{u_+,u_-\}`. This contour map is not asserted to be
the pointwise ideal extension of the inclusion.

Every maximal temporal component of a proper target path is proper in
the source. This is Lemma 3.1(a) of the previous component note. Its proof
uses the analytic outer boundary and the two banks of a real slit; no
raw-trace interpretation is used. We use this established topological
fact below.

For a proper path `gamma:(0,1)->Omega`, let `R_occ(gamma)` be the family
of maximal restrictions indexed by the connected components of
`gamma^{-1}(Omega')`. Let `R_set(gamma)` be their set after forgetting
component labels and identifying reparameterizations. The results below
also hold if reversal is included in this last identification.

For either operation `R`, define admissibility of an ideal subset `Y` for
`X` by

\[
 [R(\gamma)=\{\delta\},\quad \delta\preceq Y]
 \quad\Longrightarrow\quad\gamma\preceq X
 \quad\hbox{for every proper target path }\gamma.
 \tag{2.2}
\]

Here `preceq` is KKL A.1 subordination, with the actual relative-endpoint
homotopy class retained. The ideal-set pullback is the greatest admissible
`Y`, when such a set exists. The occurrence convention has greatest set
`q^{-1}X` for connected nonempty `X subset C` and greatest set `O'` for
`X=O`, by the previous Theorem 3.2.

## 3. Deduplicating repeated components preserves the ideal-set pullback

### Lemma 3.1. A singleton set of component paths has finitely many occurrences

If `R_set(gamma)` is a singleton, then `gamma^{-1}(Omega')` has finitely
many connected components.

**Proof.** Choose two distinct interior points `z,w` on the common
restriction. Such points exist because a proper path cannot be constant
at an interior point. Every occurrence traverses both `z` and `w`, even
if its parameterization or orientation differs. The ideal closure of
`Omega` is a compact metrizable annulus, and the proper parent extends to
a continuous map from `[0,1]` to that annulus. Fix a compatible metric and
write `d(z,w)>0`. Uniform continuity supplies `epsilon>0` such that two
parameter times less than `epsilon` apart have image distance less than
`d(z,w)/2`. Every component occurrence therefore has parameter length at
least `epsilon`. Disjoint subintervals of `(0,1)` of that minimum length
are finite in number. ∎

This is a continuity argument about one actual parent path. It imposes no
uniform bound on the number of repetitions across different paths.

### Lemma 3.2. Finite pasting of subordinate inner components

Let `X subset C` be nonempty and connected. Suppose a proper target path
has a finite nonzero number of maximal source components, and every one
of those components is subordinate to `q^{-1}X`. Then the target path is
subordinate to `X`.

**Proof.** List the component intervals in temporal order. Each component
has both ideal endpoints in `q^{-1}X subset C'`.

Every intervening nonempty closed parameter interval maps into one
component of (2.1). It cannot map into `U\setminus V`: its adjacent source
endpoint would then lie on `O'`, whereas all component endpoints lie on
`C'`. Therefore all intervening pieces lie in `X_sl`. The same argument
applies to a nontrivial initial or final segment: it lies in `X_sl`, and
the target ideal endpoint is `tau`. If there is no initial segment, the
first source endpoint maps under `q` to the initial target ideal point;
the analogous statement holds at the other end. Thus both target
endpoints belong to `X`.

If `tau` is not in `X`, no component can end on the attachment arc. An
internal end would have to be in `A^o`, which is impossible. Hence there
is a single component and no complementary prefix or suffix. The local
ideal inclusion away from `tau` transfers every subordinate homotopy
directly, exactly as in the previous one-component theorem.

Suppose now `tau in X` and `X != C`. Choose an access `z_0 in C\setminus X`
distinct from `tau` and a crosscut `rho` from `z_0` to the outer circle.
The crosscut can be chosen on the corresponding bank of the real slit,
disjoint from `X_sl`, and exiting a sufficiently thin neighborhood
`S_epsilon` of `T'` exactly once. Choose `S_epsilon` so that its closure
is contained in `V`; only the initial segment of `rho` lies in this
neighborhood. The
domain

\[
 E=S_\epsilon\setminus(T\cup\rho)
\]

is simply connected with locally connected boundary: the removed tree
meets the boundary of `S_epsilon` at the single terminal point of the
crosscut.

The source collar

\[
 (S_\epsilon\setminus(T'\cup\rho))
 \ \cup\ \bigl(C'\setminus\{q^{-1}(z_0)\}\bigr)
\]

is a neighborhood of `q^{-1}X` in the source ideal closure. Homotope each
component through proper source paths, fixing its ideal endpoints and
keeping every interior path point in `Omega'`, into this collar. At an attachment
endpoint the source access lands at its specified physical point of
`X_sl`; composing with that continuous landing map makes this a homotopy
in the target fixing the junction with the complementary slit segment.
At a shared ideal endpoint the local inclusion is continuous. There are
only finitely many components, so these finitely many homotopies and the
unchanged complementary segments paste to a continuous proper target
homotopy. The resulting entire path lies in `E`.

For any target neighborhood `N` of `X`, the compact prime-end subarc of
`X` between the two endpoints admits a collar path inside `N cap E` with
those same endpoints. Uniformize `E` by a disk. Carathéodory extension and
the straight-line homotopy in the disk show that the obtained path in
`E` is homotopic relative to its endpoints to that collar path. Thus the
parent is subordinate to every `N` and hence to `X`.

If `X=C`, the earlier endpoint analysis places both target ends on `C`.
Every path with those ends is subordinate to the complete circle, with
its actual winding retained in an annular collar. ∎

The finite condition is essential to this proof: arbitrary countably many
homotopies need not paste continuously. Lemma 3.1 supplies exactly the
finiteness required for the singleton-set premise.

### Lemma 3.3. Finite pasting for the outer circle

If a proper target path has finitely many nonzero maximal source
components and every one is subordinate to `O'`, then it is subordinate
to `O`.

**Proof.** Every component ends on `O'`, so all complementary pieces lie
in `U\setminus V`, and the target ends lie on `O`. Move every component
into a fixed sufficiently thin inner tubular collar of the analytic
curve `partial V`, fixing its endpoints. Finite pasting gives a target
homotopy into the annulus between the outer circle and a compact inner
core of `V` containing `T`. This annulus can be moved, relative to the
outer ideal endpoints and with the original winding preserved, into any
collar of `O`. ∎

### Theorem 3.4. The unindexed-set formula

For every nonempty connected inner set `X` and for the outer circle,

\[
 \boxed{\iota^*_{\rm set}X=q^{-1}X
        =\iota^*_{\rm occ}X},\qquad
 \boxed{\iota^*_{\rm set}O=O'
        =\iota^*_{\rm occ}O}.
 \tag{3.1}
\]

**Proof.** If `R_set(gamma)` is a singleton and its element is subordinate
to the displayed candidate, Lemma 3.1 makes its component family finite.
Every occurrence is subordinate to the same candidate; Lemmas 3.2–3.3
then give (2.2). Hence the candidate is admissible.

For maximality, every path with exactly one component occurrence also
has a singleton unindexed set. Therefore every `R_set`-admissible `Y` is
`R_occ`-admissible. The maximality part of the previous Theorem 3.2 forces
`Y subset q^{-1}X`, or `Y subset O'` in the outer case. ∎

This theorem is independent of KKL Propositions 6.5–6.6. It removes
occurrence deduplication from the list of genuine obstacles to the
ideal-set calculation. It does **not** prove that every path in a raw
geometric inverse trace is a maximal component.

## 4. What a simple parent allows in its inverse trace

### Theorem 4.1. Full-component or null-hairpin alternatives

Let `gamma` be a simple proper target path. A proper source path `eta`
whose trace lies in `gamma((0,1)) cap Omega'` lies in a unique maximal
component trace. Relative to its source ideal endpoints, it is homotopic
either to that entire component (possibly reversed), or to a null
hairpin subordinate to one ideal point.

**Proof.** A simple proper path has a continuous inverse parameter on its
open trace. This follows also from properness: a compact subset of the
open target stays away from the two ideal endpoints, so its inverse
parameter is confined to a compact subinterval. Composing `eta` with
this inverse parameter gives a continuous function from `(0,1)` into
`gamma^{-1}(Omega')`. Its connected image is contained in one component
`J=(s,t)`.

Parameterize that component by `delta:(0,1)->Omega'`. It is simple and
proper. Write `eta=delta o h`, with `h:(0,1)->(0,1)` continuous. Properness
forces each end of `h` to tend to `0` or `1`. Indeed, an accumulation
point in a compact interior interval would give an interior accumulation
point of `eta`; if both `0` and `1` occurred along one end, the
intermediate value theorem would force infinitely many visits to
`h=1/2`, again contradicting properness. This argument remains valid
when the two source ideal ends of `delta` coincide.

If the limiting ends of `h` are `0,1`, the homotopy

\[
 H_r(u)=\delta\bigl((1-r)h(u)+ru\bigr),\quad 0\le r\le1,
\]

fixes ideal endpoints and has its interior in the source. It joins `eta`
to `delta`. For limiting ends `1,0`, replace `u` by `1-u`.

If both limits are `0`, replace `u` by a positive function `h_epsilon(u)`
with both limits zero and image in `(0,epsilon)`. The same convex
interpolation moves `eta` into any prescribed ideal neighborhood of the
initial end of `delta`. Therefore `eta` is subordinate to that singleton
and is a null hairpin. The two limits equal to `1` are treated at the
other end. ∎

### Consequence for marked arc support

Fix the actual source covering marking and its specified immersion
blocks. Restrict attention to source paths eligible for the marking.
Any null hairpin supplied by Theorem 4.1 is subordinate to the atom
containing its ideal endpoint and is removed by the A.1/A.3.2 filters.
If its endpoint is itself a marking endpoint, it is not an eligible
marked path in the first place. The remaining relative-endpoint classes
are exactly those of eligible full maximal components. Thus passing from
component restrictions to **all trace-contained proper paths** adds no
nontrivial arc class for a simple parent.

The statement is about arc support. It does not identify a singleton of
paths modulo reparameterization: arbitrarily many backtracking
parameterizations can represent the same surviving class. Nor does it
identify multiplicities, choose one component from each leaf in a Borel
fashion, or prove an extremal-width identity. The proof also fails for
nonsimple parents: the inverse parameter on the geometric trace then need
not exist, and loop omission can change the path class.

## 5. A separate source-imported application on the original marking

The following application assumes the stated propositions in Kahn,
Kapiamba and Lyubich, [arXiv:2606.27272v1](https://arxiv.org/pdf/2606.27272v1).
They are a research preprint's theorems, not formalized results of this
archive. All page numbers below are the printed page numbers.

| Required source object or hypothesis | Verification on the selected pair |
|---|---|
| Degree-two quadratic-like map; §2.1, pp.10–11 | The physical Rouché/degree-two input gives `g:V->U`. Its sole critical point is strictly preperiodic. |
| Prime primitive little cycle; §2.3, pp.11–12 | The physical bridge constructs the actual `K0=[y3,y6]`, `K1=[y4,y1]`, `K2=[y2,y5]`, their disjoint phase neighborhoods, and rules out a competing period-two critical restriction. |
| Periodically repelling, locally connected filled set | The existing Misiurewicz/straightening input gives the dendrite and periodic repulsion for this particular map. |
| Complete native Hubbard hull; §2.5, p.13 | The real segment `[y2,y1]` lies in the filled set. In a dendrite any connected set containing its endpoints contains that segment. It is therefore exactly the smallest connected set containing the three actual little sets. |
| Native vertex set; §2.5, p.13 | The interval hull has no branch points. Adding the dividing point `a` to the three little intervals gives the five interior cut positions `y5,y3,y6,a,y4` and the ten actual ideal atoms. |
| Rotation denominator and parabolic bound; §§2.4–2.5 and §3.1, pp.12–13,19 | If `q>2`, §2.5 would make the dividing fixed point a branch point of the Hubbard hull. An interval has no such branch point, so `q=2` and rotation is `1/2`. The critical limb contains `K0,K2`; the other contains `K1`. Thus `b=2` bounds each limb, and the index window `|j|<=2` covers both residue classes. |
| Embedded tree pullback in the filled set; §6.1, pp.41–42 | The entire central inverse tree is `T'=[-y1,y1]`; inclusion is injective near the full filled set. Its only added component is `[-y1,y2)`, attached at the target tip. |

The three clauses in the source's definition of parabolically `b`-bounded
are thus satisfied. The high-type-near-degenerate condition is a separate
condition appearing in later quantitative statements; it is not an
assumption of Propositions 6.5–6.6.

**Source-imported finite-action theorem.** Taking Propositions 6.5–6.6
(pp.42–43) as inputs, the native ideal pullback of every original inner
multi-interval and its closure agrees with `q^{-1}`. The induced source
marking has the required refinement, and the native inner action is

\[
 F_*J=f_*q^{-1}J.
 \tag{5.1}
\]

**Application.** Proposition 6.5 requires the whole access boundary of
every added component meeting the interval. There is exactly one added
component here. Its complete boundary is the attachment arc `A`, with
both banks and the new terminal access. Off that attachment, the actual
source and target accesses agree. This is precisely `q^{-1}J`. The
attachment root is interior to `I0`, and is not one of the original ten
cut endpoints. Proposition 6.6 then supplies the native refinement and
combinatorial action; the physical two-fold cover supplies
`f_*S_s=I_(s mod 10)`. The source theorem, rather than a choice of raw
path convention, is doing the work in this application. ∎

The resulting action on the ten original atoms is

| Atom | Ordered atom image |
|---|---|
| `I0` | `I8,I9,I0,I1,I2` |
| `I1` | `I3,I4` |
| `I2` | `I5` |
| `I3` | `I6` |
| `I4` | `I7,I8,I9` |
| `I5` | `I0` |
| `I6` | `I1,I2,I3` |
| `I7` | `I4` |
| `I8` | `I5` |
| `I9` | `I6,I7` |

This table and its endpoint-aware five-step saturation were already
proved for the explicit contour operation. The new contribution is the
checked source-hypothesis route and its precise trust level, not a new
finite table.

### Why this does not close the independent source audit

The source's Proposition 6.5 proof is compressed; its last sentence on
printed p.42 contains the typographical phrase `I is not subordinate to I`.
More substantively, merely exhibiting a path subordinate to an attached
boundary does not spell out the universal maximality implication of
A.3.2. Importing the proposition is a legitimate theorem-application
route when that source is accepted. It does not reconstruct that missing
all-path argument and does not remove the raw-trace vacuity under the
literal reading diagnosed previously. The archive may therefore retain
its stronger independent audit as open while separately recording this
source-imported finite consequence.

Equation (5.1) is stated only for original multi-intervals and their
closures, exactly the inputs in Proposition 6.5. It is not extended here
to arbitrary endpoints inside an atom or arbitrary half-open subsets.
Those would require a separate argument or an additional source result.

## 6. A source-imported obstruction to persistent unbreakable Wave chains

For an original nonempty inner multi-interval `J`, let `s(J)` be its first
exact saturation time under the endpoint-aware action. The existing
certificate gives `s(J)<=5`; for the ten open atoms the exact times are

\[
 (2,4,4,5,4,3,4,5,4,4).
 \tag{6.1}
\]

Punctured circles must be distinguished from complete circles. In
particular, covering every open atom at one step does not prove that
every original cut endpoint is present.

**Corollary 6.1 (with the source inputs in §5 and KKL A.14).** Suppose
`A0` is a nonempty native Wave cresting over `J`. There is no sequence of
nonempty laminations

\[
 A_0,A_1,\ldots,A_{s(J)},\qquad
 A_{r+1}\subset F_*(A_r^{\rm ubr}),
 \tag{6.2}
\]

on the same marked surface.

**Proof.** Proposition 6.6 gives the combinatorial-action hypothesis at
each interval `F_*^rJ`. The second conclusion of Proposition A.14
(printed p.65) says that a lamination extracted from the pushforward of
the unbreakable part of a Wave over an interval is itself a Wave over
the image interval. Inductively `A_r` is a Wave over `F_*^rJ`.
At time `s(J)` this would be a nonempty Wave cresting over the whole
circle `C`. But a Wave's crest is its base minus its two nonempty end
multi-intervals, by A.1. Such a crest cannot contain the entire circle.
Contradiction. ∎

No width lower bound, optimizer, or measurable choice is used in this
obstruction. Conversely, the corollary does not produce a descendant,
bound the width discarded during restriction, or show that each forward
path stays simple. It is a finite-horizon obstruction to chains satisfying
the explicit lamination and unbreakability conditions in (6.2). Its
source-import dependence is the same as in §5, plus A.14.

## 7. Reproduction and remaining questions

Run

```sh
python -B research/independent_audits/native_mark_attack_20261124/verify.py
```

The verifier reuses the original cut-derived source blocks and records
all 191 distinct inputs consisting of the 100 proper open multi-intervals
(including ten punctured circles), the 90 proper closed closures, and
the complete circle. It rejects premature saturation when the lifted
open span is exactly one turn. It uses the prior geometric cut derivation
as an input, and does not certify the continuum proofs or imported KKL
propositions. It also records the explicit `q=2,b=2` finite limb census.

The remaining independent questions are now more precise:

* Arbitrary trace-contained paths are not maximal subpaths. Neither
  Theorem 3.4 nor 4.1 proves the raw A.3.2 path-as-map uniqueness
  convention.
* Theorem 4.1 handles simple parents at the level of homotopy classes.
  It supplies no support theorem for a nonsimple pushed parent and no
  width or multiplicity statement.
* The original finite marked action has a clean source-imported route.
  Native arbitrary finer-subarc action is not supplied by Proposition
  6.5 alone.
* A nonempty unbreakable lamination chain cannot persist to saturation
  under the source inputs. Obtaining quantitative surviving width, or
  converting failure of such a chain into the global stationary
  estimate, is separate.

The full `MARK`, global H1–H4, UPTCR, and MLC gates are not promoted by
this note. No canonical ledger entry is changed.
