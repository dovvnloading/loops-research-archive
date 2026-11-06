# The two KL modified principal nests terminate at their first children

**Target:** Issue #29, objective 2, and the first-child depths used in
objective 3. **Date:** 2026-11-06. **Status:** written analytic deduction
from named classical inputs, with exact finite checks; no independent human
specialist review or new Lean formalization is represented.

## 1. Precise result and conventions

Let `f(z)=z^2+c_tip` be the certified nonattracting parameter, let `G=f^3`
denote its central degree-two polynomial-like germ, and let `K3,K9` denote
the already certified filled Julia sets of the round-disk restrictions of
`f^3,f^9`. The source Kahn–Lyubich modified principal nests at these two
successive scales are

\[
\boxed{E_f^0=\operatorname{int}Y^3,
\quad E_f^1=\operatorname{int}Y^6,
\quad \chi_f=1,
\quad f^3:E_f^1\longrightarrow E_f^0,}
\]

\[
\boxed{E_G^0=\operatorname{int}Y_G^3,
\quad E_G^1=\operatorname{int}Y_G^6,
\quad \chi_G=1,
\quad G^3=f^9:E_G^1\longrightarrow E_G^0.}
\]

Both maps are proper degree-two maps between Jordan domains with
`closure(E^1)` contained in `E^0`, and their filled Julia sets are exactly
`K3` and `K9`, respectively. Thus both terminal heights equal **one**.
The second primitive period is three in `G` units and nine in physical
`f` units.

Here `Y^m,Y_G^m` are **closed** source puzzle pieces. We use their interiors
for the open domains of polynomial-like maps; this avoids confusing a
closed Jordan disk with its open interior. The tables below use the same
closed-piece convention for `P,Q_L,Q_R`.

| Datum | First stage, map `f` | Second stage, map `G=f^3` |
|---|---|---|
| Dividing vertex | ambient `alpha` | `a=alpha_G` |
| Source `q,n` | `2,1` | `2,1` |
| Separator `P` | `Y^1` | `Y_G^1` |
| First kingdom `V^0` | `Y^3` | `Y_G^3` |
| Central first child | `Y^6` | `Y_G^6` |
| Modified-nest terminal height | `chi=1` | `chi_G=1` |
| Primitive period in stage units | `p=3` | `p_G=3` |
| Physical primitive period | `3` | `9` |
| Terminal filled Julia set | `K3` | `K9` |
| Univalent separator branch | `f^2` | `G^2=f^6` |

This completes the previously missing stopping-time identification at this
specific parameter. It supplies two one-scale source packages. A marked
localization comparison between those packages remains a separate problem.

## 2. Source rule: why permanent residence in the first child terminates the nest

The primary definitions are Kahn–Lyubich,
[*A priori bounds for some infinitely renormalizable quadratics: II.
Decorations*](https://arxiv.org/pdf/math/0609046), **§§2.1–2.2**.
The proof of **Lemma 2.3** explicitly identifies the initial nest piece
as `E^0=Y^(nq+1)`. Section 2.2 defines the central first child of a critical
piece `V` using the first return time `ell` of `0`: it is the component
`W=f^(-ell)(V)|0`, with a degree-two return to `V`. A fine child is considered
only after a return iterate of the critical point exits `W`.

The stopping criterion and indexing are explicit in the primary construction
cited there, Kahn–Lyubich,
[*Local connectivity of Julia sets for unicritical polynomials*](https://www.math.stonybrook.edu/preprints/ims05-03.pdf),
**§2.2**, paragraph beginning with the termination criterion, and **§2.3**,
the primitive-renormalization paragraph. An infinite central cascade is a
polynomial-like central branch with nonescaping critical point. It terminates
the dynasty; in the uniform indexing `E^(2r)=V^r`, `E^(2r+1)=W^r`, an
immediately terminal central branch has `chi=1`. This source explicitly
allows polynomial-like input in §2.3 and defines its external rays by
straightening.

Consequently, once the first child is compactly contained and the critical
orbit under its return never leaves it, no later fine-child stopping time
needs to be found. Applying the connectedness criterion in
Douady–Hubbard,
[*On the dynamics of polynomial-like mappings*](https://pi.math.cornell.edu/~hubbard/PolyLikeMaps.pdf),
**Chapter I, §1, Proposition 2**, also gives connectedness of its filled
Julia set. These are source analytic inputs, not deductions from a finite
list of sampled iterates.

The ambient tip is strictly preperiodic to a repelling cycle. Its connected,
postcritically finite dynamics have all periodic points repelling, as used
in the prior tip/subhyperbolicity audit. The central germ has the same
property after straightening. Thus the local assumptions of the source's
first-king and primitive stopping constructions hold at both stages; the
global infinite-renormalization a priori-bounds theorem is not being applied.

## 3. An exact all-time nonescape proof at both scales

Write `x_j=f^j(0)`. The existing parameter certificate isolates the unique
root of `P18(c)+P9(c)=0` in

\[
\left(
\frac{-607918036626757496169199575185708826140}{2^{128}},
\frac{-607918036626757496169199575185708826139}{2^{128}}
\right).
\]

The root relation implies **exactly**

\[
x_{18}=-x_9,\qquad x_{19}=x_{10},\qquad x_{27}=x_{18}.
\]

Define the actual endpoint intervals

\[
I_3=[x_6,x_3]\Subset(-1/4,1/4),\qquad
I_9=[x_9,x_{18}]\Subset(-1/32,1/32),\qquad
I_9\subset\operatorname{int}I_3.
\]

The [new exact checker](verify_tip_kl_terminal_first_child.py) recomputes,
using outward integer arithmetic at resolution `2^-224`, the signs of all
intermediate images. In order from the first image to the last nonreturn
image, they are

\[
\operatorname{sgn}(f^j(I_3))_{j=1,2}=(-,+),
\qquad
\operatorname{sgn}(f^j(I_9))_{j=1}^{8}=(-,+,+,-,+,-,-,+).
\]

These intervals exclude zero strictly. The derivative identity

\[
(f^p)'(x)=2^p x\prod_{j=1}^{p-1} f^j(x)
\]

therefore proves that `G=f^3` has a unique maximum at `0` on `I3`, while
`H=f^9` has a unique minimum at `0` on `I9`. The exact endpoint images are

\[
G(x_6)=x_9\in\operatorname{int}I_3,\quad
G(x_3)=x_6,\quad G(0)=x_3;
\]

\[
H(x_9)=x_{18},\quad H(x_{18})=x_{27}=x_{18},\quad H(0)=x_9.
\]

Monotonicity on either side of the sole turning point gives

\[
\boxed{G(I_3)=I_3,\qquad H(I_9)=I_9.}
\]

This is an all-time invariant-set argument. Equality of rounded endpoint
enclosures is not used to infer any exact orbit identity. The checker
separately imports the already certified algebraic root relation.

## 4. The actual first-child boundaries are compactly separated

The [ambient landed-ray tree](tip_puzzle_ray_tree_20261106.md) proves the
actual alpha-preimage pairing by analytic inverse branches on a slit plane.
The [second puzzle's ambient-lift table](tip_internal_puzzle_ambient_lifts_20261106.md)
proves the actual internal pairings using central preimages and Levin's
landing correspondence. At each stage the normalized **stage-internal**
critical-face boundary pairs are

\[
Y^3:\quad (7/24,17/24),\ (5/24,19/24),
\]

\[
Y^6:\quad (43/192,53/192),\ (55/192,137/192),\
\hphantom{Y^6:\quad}(139/192,149/192),\ (41/192,151/192).
\]

For the second row of scales these are `G`-internal angles. Their actual
ambient `f` access labels are in the second table and are different rational
numbers. No identification of internal and ambient equipotentials is made.

The prior [top-puzzle audit](kl_tip_primitive_puzzle_and_localization_20261106.md)
proves that the first returns to `Y^3` and `Y_G^3` occur at time three in
their respective stage clocks. Thus the source's central first children are
exactly `Y^6` and `Y_G^6`.

At either stage, the four top boundary rays and eight first-child boundary
rays are disjoint. Each vertex has exactly its listed two rays, so distinct
pairs cannot denote the same vertex. The closed puzzle pieces are nested
Jordan disks. If the initial equipotential has height `h>0`, the top and
child equipotential arcs have heights `h/8` and `h/64`. Inner rays never
reach the outer equipotential, outer rays differ from all inner rays, and
the vertex sets are disjoint. Their boundaries are disjoint, proving

\[
Y^6\Subset\operatorname{int}Y^3,
\qquad Y_G^6\Subset\operatorname{int}Y_G^3.
\]

For `G`, choose the initial internal equipotential sufficiently near `K3`
that all pieces lie in the neighborhood where straightening conjugates the
degree-two germ to its normalized quadratic. This is possible because that
neighborhood contains the compact filled Julia set. Pulling the finite
quadratic puzzle back through that conjugacy gives the required physical
Jordan pieces and the holomorphic return branches. The same height argument
is then made in internal coordinates.

Finally, `I3` lies in the real spine `(-t,t)` of `int(Y^3)`, since
`t>5/16>1/4`. Similarly `I9` lies in the real spine `(-t_G,t_G)` of
`int(Y_G^3)`, since `t_G>1/32`. Each invariant interval is connected,
contains `0`, and maps into its top piece. It therefore lies in the central
component of the corresponding inverse image, namely the first child.
Every `G`-iterate of `0` remains in `Y^6`, and every `H`-iterate of `0`
remains in `Y_G^6`. Section 2's stopping rule now proves both boxed
`chi=1` assertions.

## 5. The terminal filled Julia sets equal the previously certified sets

This identification is needed before transferring the already proved
primitive phase separation. It is an equality of filled Julia sets and
analytic germs, not an equality of the chosen puzzle and round-disk domains.

For the first stage, all ambient depth-three Julia vertices have absolute
value at least `t>5/16`; the prior audit derives this by three real inverse
steps. Since `K3⊂D(0,1/4)`, it meets none of those vertices. All remaining
boundary arcs are outside `K(f)`. Connected `K3`, containing `0`, is
therefore compactly contained in `int(Y^3)`.

For the second stage, the central `G^2`-preimages of `a=alpha_G` are exactly
`±a,±b_G`, with absolute value less than `7/40`. The prior full complex
estimate proves

\[
\operatorname{Re}G(z)>7/40\quad (|z|<1/32).
\]

Consequently no central solution of `G^3(z)=a` lies in `D(0,1/32)`. This
excludes all depth-three internal Julia vertices from `K9`. Its remaining
internal ray/equipotential boundary arcs lie outside `K3`, while `K9⊂K3`.
Thus connected `K9`, containing `0`, lies compactly in `int(Y_G^3)`.

In either case the old connected set `Kp` is invariant under the relevant
return and lies in the top target. It follows that it lies in the central
first-child domain. Compare the resulting degree-two puzzle restriction
with the old degree-two round-disk restriction. The maps are the same
polynomial iterate near `Kp`; the connected set `Kp` lies in one component
of the intersection of their targets. The uniqueness statement for
equivalent polynomial-like representatives in Genadi Levin,
[*Rays to Renormalizations*](https://arxiv.org/pdf/2010.15386), **§1.2,
printed p. 2**, citing McMullen's Theorem 5.11, therefore gives equality of
their filled Julia sets.

There is no circular second-scale dependency here. The first equality
`K(E_f^1→E_f^0)=K3` uses only the ambient alpha tree and the old complex
certificate. It precedes the new `G`-internal ambient-lift table. That
table then establishes the second first-child boundary separation, followed
by `K(E_G^1→E_G^0)=K9`.

The [existing strict complex phase gaps](nonattracting_tip_complex_two_scale_20261106.md)
now apply to these actual terminal roots. At the first scale the primitive
cycle is

\[
K_{f,i}=f^i(K_3),\quad i\in\mathbb Z/3\mathbb Z.
\]

At the second scale the source's primitive cycle is

\[
K_{G,i}=G^i(K_9)=f^{3i}(K_9),\quad i\in\mathbb Z/3\mathbb Z.
\]

These three continua are pairwise disjoint. The separately certified full
physical cycle `f^j(K9)`, `j mod 9`, has nine disjoint continua; it must not
be substituted for the three-element `G` cycle when interpreting the second
stage's `q_G`, branch clocks or root arrow.

## 6. Closed separator branches and Paper 2's local hypotheses

At both stages `q=2,n=1`, so the shallow time `q` equals the Lemma 2.1
time `nq`. The source's `Q^v` are therefore exactly its two shallow
separator pieces, both of depth three:

| Source piece | First stage | Second stage |
|---|---|---|
| `P` | `Y^1`, vertices `alpha,-alpha` | `Y_G^1`, vertices `a,-a` |
| `Q_L=Q^alpha` | attached at `alpha` | `Q_(L,G)=Q_G^a`, attached at `a` |
| `Q_R=Q^(alpha')` | attached at `-alpha` | `Q_(R,G)=Q_G^(-a)`, attached at `-a` |
| Root in critical gap | `K3⋐int(Y^3)` | `K9⋐int(Y_G^3)` |

The names `L,R` follow the **source attachment convention**. At the second
scale `a` is physically positive and `-a` negative; these labels are not
instructions to use physical left/right order. The vertices `±t` or
`±t_G` are the critical kingdom's vertices, not the attachment roots of the
two `Q` pieces.

This establishes the four **local standing hypotheses of Paper 2**
([`main_v2.tex`, the standing-hypotheses environment](../../papers/paper2_rooted_end_compactification/main_v2.tex))
for the first-stage package and for the second-stage package transported
through straightening:

* **Local H1:** KL Lemma 2.1 gives two disjoint **closed** Jordan pieces
  inside `P`. Distinct open components alone would not be sufficient.
* **Local H2:** the stage-time-two restrictions are univalent, and the
  Jordan-domain Carathéodory extension gives orientation-preserving
  homeomorphisms of their closed pieces onto `P`.
* **Local H3:** `K(f)=J(f)` at the nonattracting tip. Also `K(G)=K3` has
  empty interior because it is contained in `K(f)`. Its normalized
  straightening therefore satisfies `K=J` as well.
* **Local H4:** each terminal filled Julia set is a full connected
  continuum and contains its nondegenerate interval `I3` or `I9`. It is
  compactly inside the critical depth-three piece, whose interior is
  disjoint from the two other depth-three closed pieces. Hence it lies
  in `int(P)\(Q_L∪Q_R)` as required.

These local H1–H4 are different from the global ledger entries
`H1_MARKED_CONSTRUCTION`, `H2_CALIBRATION`, `H3_COERCIVITY` and `H4_RIGIDITY`.
No status change to those entries follows. Paper 2 is stated for a normalized
quadratic polynomial; the second package is its application to the
straightened quadratic, pulled back to the degree-two germ `G`, not a claim
that the entire degree-eight polynomial `f^3` is quadratic.

The separate source root arrows have phase two modulo three:
`f^2(K3)=K_(f,2)` and `G^2(K9)=f^6(K9)=K_(G,2)`. They remain separate from
address-symbol deletion. The auxiliary extended domains `E_tilde,E_hat`
and any marks on their boundaries are not identified with newly guessed
equipotential domains by this note; their additional source constructions
must be retained wherever a later argument needs them.

## 7. Independent internal critical-value angle check

The internal table also agrees with a direct critical-value itinerary
calculation. This is an independent check, not an assumption used to infer
the seed's ambient landing in the second table.

Take a real-symmetric straightening `h` of the central germ to
`Q(w)=w^2+c_G`, with `h(0)=0`. The equivariant version follows from the
Douady–Hubbard construction: choose the annular interpolation invariant
under conjugation in **Chapter I, §4, Proposition 5**, propagate its
Beltrami structure by the real map, and use the uniqueness of the normalized
solution in **§3**. Reflection then commutes with the straightening; the
affine normalization gives real `c_G`. This is the usual symmetry argument
for the cited straightening theorem, not a numerical normalization choice.

On the real invariant core, `h` must reverse order. Otherwise the strict
maximum of `G` at `0` would be conjugated by an increasing real map to a
maximum of `Q` at `0`, contradicting its strict minimum. The exact signs of
`G^j(0)` are

\[
+,-,-,(+,-,+)^{\infty}.
\]

The signs of the normalized quadratic's critical-value orbit are therefore
`-,+,+,(-,+,-)^infinity`. Encode a negative sign by `1`. Zakeri,
[*External rays and the real slice of the Mandelbrot set*](https://www.math.stonybrook.edu/preprints/ims02-02.pdf),
**Theorem 3.3 and its proof**, gives the binary recurrence starting at
`t0=0`, keeping the next bit for a positive sign and flipping it for a
negative sign. It yields

\[
\tau_G=.011(100)^{\infty}_2
=\frac{3}{8}+\frac{4}{8(2^3-1)}
=\frac{25}{56}.
\]

The conjugate critical-value access has angle `31/56`. The normalized
straightening remains postcritically finite and nonattracting, so Zakeri's
real boundary-parameter hypothesis is met. No tuning-component identity
or rigidity theorem is inferred from this arithmetic.

## 8. Reproduction, dependencies and remaining boundary

```sh
python research/independent_audits/verify_tip_puzzle_ray_tree.py --check-manifest
python research/independent_audits/verify_tip_internal_ray_lifts.py --check-manifest
python research/independent_audits/verify_tip_kl_terminal_first_child.py
python research/independent_audits/verify_tip_kl_terminal_first_child.py --print-json
```

The last checker verifies the exact tip relation's finite certificate,
intermediate interval signs and turning directions, separation of both
first-child ray boundaries, their two-to-one return arrows, all stage and
physical clocks, and the independent internal Gray-code calculation. Python
uses only standard-library exact integers and fractions. Its JSON output
states the analytic trust boundary explicitly.

The new result closes the named modified-principal-nest stopping and
terminal-root-placement subproblem at this one algebraic parameter. The
finite source access tables are supplied by the two companion ray notes.
The separate [localization refinement note](tip_localization_refinement_peripheral_monodromy_20261106.md)
now constructs a based holomorphic comparison from a component of the
period-nine target cover restricted to the common exterior into the
period-three target cover. It proves naturality for every homotopy class
of paths and countably infinite sheet fibers, as well as an obstruction
to extension over the entire uniformizing prime-end circle. These are
statements about the specified restricted exterior and chosen component
and basepoints. They do not yet give the required filled or protected
prime-end comparison, its selected `O/xi/eta` sides, or their based access
markings. The earlier failure of the unrestricted reverse identity and
`f^6` on the proposed deleted complements is unaffected.

The exact triple-airplane identity of the separate attracting period-27
center is also a separate issue. This note changes no source-locked
465-entry ledger status, global H1–H4 gate, UPTCR claim or MLC claim.

**Attribution and AI disclosure:** OpenAI GPT-6 Astra Pro assisted the
proof search, primary-source comparison, exact checker and writing. The
imported results belong to Kahn–Lyubich, Douady–Hubbard, Levin/McMullen,
Zakeri and the ray-landing sources credited in the companion audits. No
independent human mathematical verification or source-author endorsement
has occurred in this work.
