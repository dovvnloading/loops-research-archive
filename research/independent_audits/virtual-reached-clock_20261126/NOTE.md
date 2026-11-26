# Reached cylinders: exact residual clocks, collisions and a native critical obstruction (2026-11-26)

## 1. Target

**VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION**, as stated in ledger.json:
after the actual target base is typed or uniquely selected, every demanded
finite-cylinder branch image must have the forced open pullback component,
and this reached component must be among the declared equal-depth target
cylinders at every proof-used intermediate iterate, with complete metadata
and enlargement stability. See [finite-cylinder lift, §§4–6](../../mlc_unified/finite_cylinder_commuting_lift.md).

The target is upstream of VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR and the
second-scale marking/return atlas, hence of the analytic-access portion of
H1_MARKED_CONSTRUCTION. This is the sole claimed ledger ID.

## 2. Current status

Open. **Partial**, with a proved all-word reached-component theorem and an
exact native quadratic obstruction to the *unqualified* equal-depth
univalent exhaustion assertion. Not a counterexample to the complete
demand-qualified virtual obligation: the selected direct-decoration parameter
has not been certified as a nontrivial two-step virtual block, nor has a
complete Wave demand been frozen.

## 3. Claim

For actual direct-decoration cylinders and a typed proper root return,
the reached open component is exactly computable at every time by a residual
inverse clock and a sliding degree word, and no univalent equal-depth
target cylinder can contain the reached image during the critical window of
a central return; an actual algebraic quadratic exhibits the obstruction
simultaneously on all four depth-two source words and on every deeper word.

## 4. Evidence

### 4.1 Actual reached-component theorem

Use the notation of [the direct-decoration compactification, §§3–5](../../mlc_unified/virtual_cantor_pullback_compactification.md):
closed Jordan separator \(P\), two disjoint closed Jordan pullbacks
\(Q_0,Q_1\subset P\), \(g=f^q\), inverse homeomorphisms
\(\phi_a:P\to Q_a\), conformal on interiors. For the word
\(w=a_1\cdots a_m\), let \(\phi_w=\phi_{a_1}\circ\cdots\circ\phi_{a_m}\),
\(Q_w=\phi_w(P)\), \(N=qm\). Use actual complex domains throughout.

Let \(A=A_0\subset P^\circ\) be nonempty connected and open,
\(A_i=f^i(A)\) for \(0\le i\le r\), and assume the root branch
\(F=f^r:A\to A_r\) is proper and onto. In particular the typed target at
time \(j\) is \(A_j\), not a presumed copy of \(P\). Put
\(d_i=\deg(f:A_i\to A_{i+1})\) for \(i<r\).
The one-step maps are proper: for a sequence in \(A_i\) with images
in a compact subset of \(A_{i+1}\), choose preimages in \(A\); their
\(F\)-images lie in the continuous image of that compact set in \(A_r\).
Properness of \(F\) yields a convergent subsequence in \(A\) and therefore
one in \(A_i\). The same argument applies to any consecutive composition.
All degrees are finite positive integers.

Set
\[
 U_w=\phi_w(A),\qquad D_{w,j}=f^j(U_w),\qquad
 t_j=\max(0,j-N).
\]
For every \(0\le j\le r\), the following assertions hold.

**(i) The exact reached component, not just containment.**
\(D_{w,j}\) is a connected open component of \(f^{-N}(A_j)\), with
\(f^N:D_{w,j}\to A_j\) proper onto. Its degree and the degree of the
forward branch are
\[
 \deg(f^N:D_{w,j}\to A_j)=\prod_{i=t_j}^{j-1}d_i,\qquad
 \deg(f^j:U_w\to D_{w,j})=\prod_{i=0}^{t_j-1}d_i.       \tag{1}
\]
Empty products are one. The ordered projection word consists of
\(\max(N-j,0)\) initial ones, followed by \((d_{t_j},\ldots,d_{j-1})\).
The forward word consists of \(\min(j,N)\) initial ones followed by
\((d_0,\ldots,d_{t_j-1})\).

**Proof.** For \(j\le N\), all prefixes \(f^j|_{U_w}\) are injective:
equality of two images would imply equality under \(f^N\). They are
conformal isomorphisms onto their images, and
\[
 f^{N-j}:D_{w,j}\longrightarrow A
\]
is also a conformal isomorphism (compose \(f^N|_{U_w}\) with the inverse
prefix). The \(N\)-step map from \(D_{w,j}\) is this isomorphism followed
by \(f^j|_A\). For \(j\ge N\), instead \(D_{w,j}=A_{j-N}\), and the
projection is exactly the root subchain from \(j-N\) to \(j\). The
forward map is \(f^N|_{U_w}\) followed by the root prefix of length
\(j-N\). This proves (1), properness, surjectivity and the two words.
For global component equality, a sequence in \(D_{w,j}\) converging to
a point in the open preimage \(f^{-N}(A_j)\) has images contained in
a compact subset of \(A_j\) after discarding finitely many terms.
Properness puts its limit in \(D_{w,j}\). Thus \(D_{w,j}\) is open and
relatively closed in that preimage, and connected. The same argument
shows, for \(j\le N\), that \(D_{w,j}\) is the global component of
\(f^{-(N-j)}(A)\) mapping conformally onto \(A\).

Degree one is equivalent to univalence of the reached projection.
If \(A_j\) is simply connected and the product in (1) exceeds one,
the projection contains a critical point: otherwise it would be a
connected unbranched finite covering of a simply connected domain,
hence of degree one. Without simple connectivity we do not assert
this general critical-point implication. In the central-return case
below a point witnessing criticality is given explicitly, without
any boundary regularity assumption on the other \(A_i\).
The open component theorem does not require a Jordan closure for
\(D_{w,j}\).

**(ii) Exhaustive collision census before the root.**
For \(0\le j<N\), write \(j=kq+s\), \(0\le s<q\), \(w=uav\),
\(|u|=k\), \(|v|=m-k-1\).
With \(\psi_{a,s}=f^s\circ\phi_a\) on \(P^\circ\), one has
\[
 D_{w,j}=\psi_{a,s}(\phi_v(A)),\qquad
 f^{q-s}\circ\psi_{a,s}=\operatorname{id}.                 \tag{2}
\]
Each \(\psi_{a,s}\) is the inverse of the conformal restriction to
one global open component of \(f^{-(q-s)}(P^\circ)\), by the same
properness argument as (i). Consequently two of these maps at fixed
\(s\) are either identical or have disjoint open images. Let \(b_s\)
be their number of distinct maps, either one or two. Two images in
(2) agree iff the tail \(v\) and the class of \(a\) under equality of
\(\psi_{a,s}\) agree; otherwise they are disjoint. Indeed, different
classes have disjoint images, and within a class injectivity and the
disjoint closed cylinders for the tails give the assertion. Thus the
**entire distinct reached list** at time \(j\), over all \(2^m\) source
words, has cardinality \(b_s2^{m-k-1}\). A particular entry has
exactly \(2^k\) times the size of its \(a\)-class preimages. At and
after \(N\) there is just one image, namely the indicated root phase.
This is a census of actual components, not a cardinality estimate
on a symbolic quotient. The deleted prefix must be retained as source
incidence if demand uses it; equality of target domains does not
establish equality of source histories.

For fixed \(P,\phi_0,\phi_1\), the census is independent of the choice
of nonempty open connected \(A\subset P^\circ\) (subject to the proper
root chain for (i)). If two such root domains are nested, all reached
domains are nested with exactly the same before-root collision classes.
This proves no birth of those classes in that restricted enlargement
operation. If the one-step root word is also unchanged, so are both
degree words. It says nothing about an enlargement changing \(P\),
the approved root branch, relative covers, or the proof-use inventory.
For compact subdomains of \(P^\circ\), (2) also separates distinct
image closures; arbitrary cylinder boundary contacts are not claimed.

**(iii) Critical window: impossibility independent of target choice.**
Suppose \(0\in A\) and the root degree word is \((2,1,\ldots,1)\),
as for the central quadratic first return. For every \(w\) and
\(1\le j\le\min(r,N)\), (1) gives forward degree one and reached
projection degree two. More explicitly put
\[
 z_w=\phi_w(0),\qquad y_{w,j}=f^j(z_w)\in D_{w,j}.
\]
Then \(f^{N-j}(y_{w,j})=0\), and \(0\le N-j<N\).
The chain rule forces \((f^N)'(y_{w,j})=0\).
No open univalent restriction of \(f^N\) can contain this point.
No closed Jordan cylinder on which \(f^N\) is a homeomorphism
can contain the whole open set \(D_{w,j}\) either: that would put
\(y_{w,j}\) in its interior. This refutes same-clock univalent
exhaustion even if the proposed target base is larger than \(A_j\),
and also within *any* authorized localization containing the reached
open image. For \(j>N\) the central quadratic factor has left the
projection word and entered the forward word. There is no equal-clock
univalence obstruction from that factor then, although target
authorization is still required.

This goes beyond [critical chronology and retimed telescope](../../mlc_unified/critical_chronology_and_retimed_telescope.md):
the commuting-square degree identities there presuppose maps with
specified domains; here the reached components themselves are
constructed, their full collision census is computed for every
word/depth, and a critical point rules out *every* univalent target,
without assuming a target square. It also differs from the previously
noted impossibility of a degree-two self-return entirely in the
off-critical cylinder corridor: a genuine central return is used
below, and it is the transverse projection that ramifies.

### 4.2 Exact native quadratic (no numerical root assumption)

Write \(x_i(c)=f_c^i(0)\), \(f_c(z)=z^2+c\). Define \(c_*\) to be
the unique root of \(x_6+x_3=0\) in
\[
 (-179033/100000,\ -179032/100000).
\]
The accompanying check_clock_arithmetic.py proves the endpoint signs \(-,+\) and
\(11<(x_6+x_3)'<13\) throughout the closed bracket by rational
interval arithmetic: \(x_0=d_0'=0\),
\(x_{i+1}=x_i^2+c\), \(d_{i+1}'=2x_id_i'+1\).
Here \(d_i'\) denotes a parameter derivative, not the branch degree
of §4.1. Interval multiplication uses the min/max of all four endpoint
products and interval squaring uses the minimum zero when the interval
straddles zero. The intermediate value theorem and strict monotonicity
therefore establish existence and uniqueness exactly. The certified
strict boxes for \(x_1,\ldots,x_6\) are
\[
 (-1.8,-1.79),\ (1.4,1.5),\ (1/5,1/4),\
 (-1.77,-1.7),\ (1.2,1.3),\ (-1/4,-1/5),
\]
where terminating decimals denote rationals. Put \(a=x_3(c_*)>0\).
Then \(x_6=-a\), and evenness gives \(f^3(-a)=f^3(a)=-a\).
The three disjoint boxes for \(-a,x_4,x_5\) give exact period three,
and the other four orbit points \(0,x_1,x_2,a\) lie outside that cycle.
The repelling multiplier has modulus
\(8a|x_4|x_5>8(1/5)(17/10)(6/5)>1\).
Thus the critical orbit is strictly preperiodic to a repelling cycle.
Use the standard postcritically finite Misiurewicz theorem for connected
Julia sets, empty Fatou interior of the filled Julia set and repelling
periodic points; here the unique finite critical point is bounded and
strictly preperiodic. This verifies \(K(f)=J(f)\) and the periodically
repelling standing setting, not a global MLC assertion.

**Source puzzle, not an arbitrarily selected disk.**
Use KL08 §2.1 pp. 5–6. The positive fixed point \(\beta\) is the landing
point of ray zero; the other fixed point \(\alpha\) is dividing. Both
are real; \(-1<\alpha<0\) and \(0<\beta<2\).
Conjugation reverses the cyclic order of the rays at \(\alpha\) and
commutes with their permutation by \(f\). Hence \(p/q=-p/q\) mod 1,
so the source's \(q>1\), coprime rotation has \(q=2,p=1\).
The only two angles cyclically exchanged by doubling are \(1/3,2/3\).
The preimage graph at depth one has vertices \(\alpha,-\alpha\)
and rays with angles \(1/6,1/3,2/3,5/6\).
The real interval \([-\beta,\beta]\) is invariant because
\(c_*=\beta-\beta^2>-\beta\); every point of this interval is in \(K(f)\).
The ray/equipotential graph can meet it only at its vertices.
Thus the real interval between the depth-one vertices containing 0
is in the interior of \(Y^1\), the segment left of \(\alpha\) is
in the left off-critical piece, and the segment right of \(-\alpha\)
is in the reflected off-critical piece \(Z^1\). To see the separation
directly, each pair of conjugate rays at a vertex forms a crosscut of
the real-symmetric equipotential disk; the rays are in opposite
half-planes (the only real exterior rays have angles 0 and 1/2).
The corresponding real segments on opposite sides of that vertex
belong to different complementary components.

Since \(x_2>1>-\alpha\), the satellite candidate escapes at the least
positive \(q\)-time, \(n=1\). The source's separator is exactly
\(P=Y^1\) and the escape piece is \(V^0=Y^3\), the closed component
pullback of \(Z^1\) by \(f^2\) at 0. By KL08 Lemma 2.1 with \(n=1\),
the two contained univalent \(f^2\)-pullbacks \(Q_L,Q_R\) of \(P\)
are pairwise disjoint closed puzzle disks. The puzzle boundaries are
Jordan and the proper univalent restrictions extend homeomorphically
by the Jordan boundary theorem. Symmetry \(z\mapsto-z\) of \(P\)
and evenness of \(f^2\) exchange the pullbacks attached at
\(\alpha,-\alpha\); hence \(Q_R=-Q_L\) and
\(f\circ\phi_R=f\circ\phi_L\). In particular \(b_0=2,b_1=1\).

On the whole real interval \([-1/4,1/4]\), exact rational arithmetic
gives \(f(z)<-1\) and \(f^2(z)>1\), and invariance gives \(f^2(z)\le\beta\).
Thus its \(f^2\)-image lies in the interior of \(Z^1\), and the interval,
being connected and containing 0, is in \(\operatorname{int}V^0\).
The critical orbit first returns to \(V^0\) at time 3:
\(x_1<-1\), \(x_2>1\) are outside \(P\) and \(x_3=a\) is in the
interval just located. Set \(B=(V^0)^\circ\), \(A\) the interior of
the actual central first-return pullback of \(V^0\) at time 3.
KL08 §2.2 p. 7 gives the degree-two first-child map \(f^3:A\to B\);
KL09 §2.3 p. 7 gives \(A\Subset B\) for first-kingdom returns.
The first factor contains 0, so by multiplication and total degree
two the three proper one-step degrees are \((2,1,1)\).

Moreover \(f^3([-a,a])=[-a,a]\): evenness, \(f^3(0)=a\),
\(f^3(a)=-a\), and on \((0,a]\) the derivative
\(8z f(z)f^2(z)\) is strictly negative. The interval maps into \(B\)
and is connected and contains 0, so it lies in \(A\) and is forward
invariant for the first-child map. Douady–Hubbard's connectedness
criterion now gives connected little filled Julia set \(K_0\Subset B\).
The nest stops at this primitive first return by KL08 §2.2 p. 8
and KL09 §2.3 p. 7. The critical orbit never meets \(\alpha\) (its
eventual period is three); all critical pieces used here are genuine
puzzle pieces. This establishes the native root-gap hypotheses of
the direct-decoration package, not a deeper virtual portrait.

**Failure record.** Choose \(m=2\), \(N=4\) and all four words
\(LL,LR,RL,RR\). The root branch is the actual first-return map just
constructed with \(r=3\). The physical calculation (1)–(2) is

| time \(j\) | forward degree | degree of projection \(f^4\) onto \(A_j\) | number of distinct reached components |
|---:|---:|---:|---:|
|0|1|1|4|
|1|1|2|2|
|2|1|2|2|
|3|1|2|1|

At the final time the target base \(B\subset P^\circ\) is already
typed and the reached image is nonempty, open, connected, and a
global component of \(f^{-4}(B)\). It cannot be a declared equal-depth
univalent pullback of \(B\), or be contained in any univalent cylinder
over a larger base. Explicitly the same point \(y_{w,3}\) occurs in
every reached component, namely \(-\sqrt{-c_*}\): the last residual
map \(f:D_{w,3}\to A\) sends it to 0, and \(\phi_a(0)\) is real
by real symmetry of each of the two attached disks and uniqueness
of the inverse, with \(|\phi_a(0)|\le-\alpha<1\). Hence its
\(f\)-image is negative. Thus \(f'(f^0(y_{w,3}))\) need not vanish,
but \(f(y_{w,3})=0\), so \((f^4)'(y_{w,3})=0\). The failure begins
at the first intermediate step, witnessed by \(y_{w,1}\);
it persists at the return endpoint. Any depth \(m\ge2\) has the
same degree obstruction for the full three-step return. At depth
one the window ends at step two, as (1) predicts.

This is not a hypothetical critical square or a numerical failure
of root isolation. Its underlying inverse branches, target base,
return time, and offending point are actual polynomial objects.
Complete protected Wave marking and the demand predicate are
deliberately not assumed. The example is a one-step native decoration,
and we have not shown a nontrivial virtual-copy chain or that the
specific central lifted word is a mandatory Wave continuation.
Consequently it is an exact counterexample to the unqualified
same-depth assertion, **partial for the ledger**, not a category-(c)
refutation of its full quantified statement.

### 4.3 Strongest corrected statement established here

For typed proper root branches on a fixed direct-decoration inverse
family, the component-level part of exhaustion holds with **the actual
degree-labelled reached components** in (1)–(2); if one insists on
univalent charts before the root, their clock is \(N-j\) onto \(A\),
not \(N\) onto \(A_j\). In the degree-one window the reached domain
itself is the unique global univalent component over the typed root
phase containing the image. Authorizing it as a selected marked target
remains separate. For the degree-two window, no enlargement of a
univalent target list at unchanged clock can fix the obstruction.
One must either exclude these words by an independently justified
demand rule, retain ramified projection targets with the ordered
degree data, or retime and explicitly retype the branch. The
retimed clock is not a license to use the same-exponent commuting
formula of finite_cylinder_commuting_lift.md §3. At \(j=N\) use the
identity onto the root and after that the declared root phase
transition; never extend symbolic deletion through the root.

The before-root census gives exact word ownership, source incidence,
and fixed-family enlargement compatibility, and conjugacy under
relabeling the very same actual inverse charts. It does not certify
protected-access cyclic orders, obstacle/sheet coverage after
collisions, cross-base ownership of overlapping distinct base domains,
demand-bijective final-root enlargement or invariant choice of virtual
portraits. Nor does it certify closure compactness relative to a
larger target when the root image meets that target boundary.

### 4.4 Reproduction

From the repository root run

    python -B research/independent_audits/virtual-reached-clock_20261126/check_clock_arithmetic.py
    python -B code/verify_physical_bridges.py

The first command uses only Python's standard library (CI Python
3.12), exact Fraction endpoints with no tolerance or floating point,
six orbit and derivative steps, and finite enumeration of words at
depths 1–8. It fails by assertion on a violated inequality or
table identity and writes deterministic JSON to stdout, including
the isolating bracket and table above. The finite word regression
is an arithmetic shadow only; the physical identification is
the written proof of (1)–(2), not an inference from the table.
The second command validates existing source and route wiring.
The executable is indexed under CLOCK and ENDS as a direct-decoration
phase-clock certificate; it does not alter their status or the
bridge register. The check_*.py name follows the archive's standalone
arithmetic-diagnostic convention: this is not a theorem-level model
certificate requiring a new contract-index claim (which is outside
this submission's allowed edits). The route checker continues to
require the explicit TSV row, and CI runs both existing checks.
No model theorem is invoked to prove a new
physical implication: the maps in (1)–(2) are restrictions of \(f\)
and the parameter bounds concern its literal critical orbit.

## 5. Dependencies

Main snapshot 6ba50a4b452f7703c17200dd3b3bab4b117ee413.
The direct dependencies are DIRECT_DECORATION_PULLBACK_COMPACTIFICATION
(actual inverse family), FIXED_BASE_CONNECTED_IMAGE_TARGET_UNIQUENESS
and INTERIOR_PULLBACK_COMPONENT_FORCING (distinguish containment from
component authorization). The component-equality argument above
does not require the target Jordan-boundary hypothesis of their
Lemma 4.2; it uses properness onto the actual image instead.
Supporting notes:
[virtual_scale_to_puzzle_selector](../../mlc_unified/virtual_scale_to_puzzle_selector.md)
(first decoration escape and native first-return atlas);
[critical_chronology_and_retimed_telescope](../../mlc_unified/critical_chronology_and_retimed_telescope.md)
(proper squares and degree-word distinction);
[virtual_s2_offcritical_degree_obstruction](../../mlc_unified/virtual_s2_offcritical_degree_obstruction_20260725.md),
[finite quadratic-like lift](../../mlc_unified/virtual_s2_finite_quadratic_like_lift_20260726.md),
[corrected corridor certificate](../../mlc_unified/virtual_s2_corrected_corridor_certificate_20260726.md),
[partial root transition](../../mlc_unified/virtual_s2_partial_root_transition_certificate_20260725.md),
[terminal Hubbard anchor](../../mlc_unified/terminal_hubbard_anchor.md),
and [Paper 2 native source realization](../paper2_decorations_source_realization_20261105.md).
The first three named ledger dependencies are used with their stated
scope, not promoted. No dependency on width, compactness, rigidity,
or MLC is consumed. No existing ledger, map, or register status
changes are proposed.

## 6. Boundary

Clause audit: typed native bases and actual component exhaustion with
degrees are proved; uniqueness and exact collisions are proved for
the fixed inverse family; chronological degree metadata and restricted
fixed-family enlargement are proved. Equal-depth **univalent**
exhaustion fails in the native example, and cannot hold for any
demanded central word in the indicated critical window. First
unresolved source-facing step: does the admissible virtual Wave demand
force such a word at a certified nontrivial virtual scale, or exclude
it by a source-defined chronology? No such demand or scale-two
portrait is constructed here. Complete protected prime-end, sheet,
obstacle and localization metadata, proof-use intermediate inventory,
and authorized final-root enlargement remain unproved. Cross-base
selection and end fibers remain unproved. H1_MARKED_CONSTRUCTION,
MBTT, H3_COERCIVITY and H4_RIGIDITY remain open; no MLC progress claim
beyond this local analytic restriction on the proposed construction.

Repository retrieval: the five required orientation files were fetched
in full and the two JSON ledgers parsed; long connector responses
were output-limited, so not every line of the orientation prose or
long supporting notes was individually reviewed. No claim of a
complete repository-wide dependency audit is made. The source-facing
Wave-language note named in the ledger was unavailable at its presumed
path; this is not used as evidence of a mathematical failure.
Only the stated analytic hypotheses are consumed. The standalone
arithmetic check was run locally; whole-repository verification is
the submitted workflow's responsibility (local clone unavailable).

## 7. Attribution

* Jeremy Kahn and Mikhail Lyubich, [A priori bounds for some infinitely
  renormalizable quadratics: II. Decorations](https://arxiv.org/pdf/math/0609046v2),
  §2.1 pp. 5–6 (dividing portrait, escape, separator, Lemma 2.1);
  §2.2 pp. 7–8 (first child and primitive stopping).
* Jeremy Kahn and Mikhail Lyubich, [Local connectivity of Julia sets for
  unicritical polynomials](https://arxiv.org/pdf/math/0505194), §2.3
  p. 7 (first kingdom, relatively compact first returns and primitive
  stopping). Only these qualitative puzzle/return results are imported;
  no numerical a priori modulus bound or infinite-renormalization
  theorem is used.
* Douady and Hubbard, [On the dynamics of polynomial-like mappings](https://doi.org/10.24033/asens.1491),
  Proposition 2 (connectedness criterion).
* Misiurewicz postcritically finite theorem as in Milnor,
  Dynamics in One Complex Variable, §17 (draft Corollary 17.4 and
  Theorem 17.5; see [draft](https://abel.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf));
  also the archive's [tip-family theorem, R5](../../tip_family_theorem/THEOREM.md).
  Böttcher conjugacy, Jordan boundary extension for conformal disk
  maps and the chain rule are the classical elementary analytic
  inputs.
* The repository's finite-cylinder and direct-decoration notes supply
  the earlier interfaces and notation, not the new degree-window and
  collision census proof. No attribution of the virtual realization
  theorem to the cited papers is made.

## 8. AI disclosure

GPT-6.2 (ChatGPT) performed proof search, repository and primary-source
comparison, writing, exact arithmetic verifier generation and the
standalone regression run. No human verification or peer review
was performed in this submission. The geometric argument is written
for independent review; the arithmetic regression is not a proof
assistant or a substitute for checking the imported hypotheses.
