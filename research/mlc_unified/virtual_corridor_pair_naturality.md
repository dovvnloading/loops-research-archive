# Virtual corridor pair naturality and the anchor obstruction

## 1. Purpose and verdict

This pass attempts the two open obligations

- `VIRTUAL_CORRIDOR_PAIR_NATURALITY`; and
- `VIRTUAL_ATTACHMENT_FREE_ANCHOR`.

It proves three exact results:

1. a univalent-transport construction of marked carrier-pair naturality from
   one anchor pair;
2. prime-end and cyclic-order functoriality for that construction without a
   local-connectivity assumption; and
3. a least finite attachment-orbit closure, together with an exact collision
   test.

It also proves that the published virtual-hull description does **not**
imply an attachment-free anchor. The same required packages and the same
degree-one selected-carrier dynamics admit both an attachment-free interval
pair and an interval-in-triod pair with a hidden attached branch.

Therefore neither virtual obligation is promoted. The obstruction is not
numerical: a canonical actual carrier and a KKL-style component-exhaustion
theorem are absent from the published hypotheses.

## 2. Source lock

### 2.1 Dudko

Dudko's Interpolation Problem 4.4 asks for a Virtual Molecule version of the
Near-Degenerate Regime. The following paragraph proposes partially invariant
virtual Julia sets that:

- are connected hulls of the relevant Cantor small Julia sets; and
- contain the critical orbit through an appropriate number of first returns.

The paragraph does not define a canonical hull, a stagewise pulled/immersed
carrier pair, a prime-end marking, or an attachment-free interface.

Source:

- Dzmitry Dudko, *On the MLC Conjecture and the Renormalization Theory in
  Complex Dynamics*, arXiv:2512.24171, Interpolation Problem 4.4 and the
  following paragraph:
  <https://arxiv.org/html/2512.24171>.

### 2.2 KKL

Kahn--Kapiamba--Lyubich use stronger native data. In their central range,
the proof of Proposition 5.7 has
\[
  \mathcal T'_j=\mathcal T_j
\tag{2.1}
\]
and the polynomial map carries the relevant source tree homeomorphically to
the next tree. Proposition 6.5 identifies the ideal pullback excess exactly
with Carathéodory boundaries of components of
\(\mathcal T'\setminus\mathcal T\). Proposition 6.7 again uses actual carrier
equality to prove properness on the central range.

Source:

- Jeremy Kahn, Artem Kapiamba, Mikhail Lyubich, *MLC for parabolically
  bounded primitive renormalization*, arXiv:2606.27272, Propositions 5.7,
  6.5, and 6.7:
  <https://arxiv.org/html/2606.27272>;
- local source `.tmp_wave_audit/waves-with-Misha.tex`, labels
  `prop:inner translation marking`, `prop:pullback description`, and
  `prop:improper intervals`.

### 2.3 Neutral \(\psi^\bullet\)-ql bounds

The 2025 neutral-renormalization variation extends pseudo-Siegel bounds to
\(\psi^\bullet\)-ql Siegel maps but explicitly leaves transitional scales
outside its main uniform description. It does not construct Dudko's virtual
Molecule carrier or the anchor equality required here.

Source:

- Dudko--Luo--Lyubich, *Uniform a priori bounds for neutral
  renormalization. Variation II: \(\psi^\bullet\)-ql Siegel maps*,
  arXiv:2509.23031:
  <https://arxiv.org/abs/2509.23031>.

No unpublished virtual-renormalization manuscript is imported.

## 3. The stage datum and certificate

Retain the corridor orientation \(j+1\to j\). A marked carrier-pair stage is
\[
  \mathfrak P_j
  =
  (T'_j,T_j,\eta_j,\mathcal I_j,\mathcal O_j),
\tag{3.1}
\]
where:

1. \(T'_j\) is the actual pulled carrier used in the source surface;
2. \(T_j\) is the carrier copy embedded by the immersion;
3. \(\eta_j:T_j\hookrightarrow T'_j\) is the declared inclusion;
4. \(\mathcal I_j\) is the complete proof-used prime-end marking; and
5. \(\mathcal O_j\) is the finite absorbed-or-separated obstacle ledger.

For a central transition, write
\[
  \Phi_j:T'_{j+1}\longrightarrow T'_j,
  \qquad
  \phi_j:T_{j+1}\longrightarrow T_j.
\tag{3.2}
\]

The **Univalent Pair-Naturality Certificate** consists of:

### `PN1` Actual packages

Each carrier is built from the actual Cantor small Julia sets, the prescribed
first-return orbit segment, and every dam, fjord, fan anchor, and access used
through the complete Wave horizon.

### `PN2` Univalent corridor branch

The selected central branch extends to an orientation-preserving conformal
homeomorphism between Jordan localizations and avoids the critical value.

### `PN3` Exact pair transport

Both carriers, rather than only their selected packages, satisfy
\[
  \Phi_j(T'_{j+1})=T'_j,
  \qquad
  \phi_j(T_{j+1})=T_j.
\tag{3.3}
\]

### `PN4` Commuting inclusion square

\[
  \Phi_j\circ\eta_{j+1}=\eta_j\circ\phi_j.
\tag{3.4}
\]

### `PN5` Package and obstacle equivariance

Every required package and every member of \(\mathcal O_{j+1}\) maps to its
declared stage-\(j\) package or obstacle. No omitted component enters the
selected localization.

### `PN6` Prime-end completion

The conformal branch restricts to conformal isomorphisms of the proof-used
simply connected complement components and hence extends to their prime-end
compactifications.

### `PN7` Full-horizon compatibility

The induced prime-end maps preserve the complete ideal marking, cyclic
order, attachment incidence, and every stopping-time label through the full
Wave horizon.

`PN1` is not a license to replace the actual virtual hull by an abstract
finite tree. `PN3` is the missing ambient-carrier assertion; selected root
routing alone proves only the analogous equality for \(T_j\).

## 4. Univalent transport construction

### Theorem 4.1 (one anchor pair generates a natural corridor)

Let \(0\leq j\leq k\) be a central corridor. For each \(j<k\), let
\[
  U_j:\Omega_{j+1}\longrightarrow\Omega_j
\tag{4.1}
\]
be an orientation-preserving conformal homeomorphism of Jordan
localizations. Suppose one marked anchor pair
\[
  \eta_k:T_k\hookrightarrow T'_k\subset\Omega_k
\tag{4.2}
\]
is given. Define, recursively,
\[
  T'_j:=U_j(T'_{j+1}),
  \qquad
  T_j:=U_j(T_{j+1}),
  \qquad
  \eta_j:=U_j\eta_{j+1}U_j^{-1}\bigm|_{T_j}.
\tag{4.3}
\]
Transport every package, obstacle, and ideal marking by the same maps.

Then the stages satisfy `PN2`--`PN5`. If the marked complement components
are simply connected and the anchor marking is access-complete, they also
satisfy `PN6`--`PN7`. Consequently the corridor is marked-pair natural and
its attachment support is the transport of the anchor support.

**Proof.**
Equation (4.3) gives exact transport of both carriers and immediately gives
the commuting square
\[
  U_j\circ\eta_{j+1}=\eta_j\circ U_j|_{T_{j+1}}.
\]
Transporting the finite package and obstacle ledgers gives `PN5`.

For each proof-used simply connected component \(D\) of
\(\Omega_{j+1}\setminus T'_{j+1}\), the restriction
\[
  U_j:D\longrightarrow U_j(D)
\]
is a conformal isomorphism. Functoriality of prime-end compactification gives
an orientation-preserving homeomorphism of the prime-end circles. This
statement does not require the Euclidean boundary of \(D\) to be locally
connected. It preserves cyclic order, access incidence, and the transported
finite marking. Iteration through the finite horizon proves `PN6`--`PN7`.

The Corridor Attachment Transport Theorem now identifies the attachment
support at every stage with the transported anchor support. \(\square\)

### Corollary 4.2 (attachment-free anchor)

Under Theorem 4.1, if
\[
  T'_k=T_k
\tag{4.4}
\]
at the anchor, then \(T'_j=T_j\) at every central stage and all central
attachment supports are empty.

**Proof.**
Apply (4.3) inductively. \(\square\)

### Scope qualification

Theorem 4.1 constructs the desired square only after the actual anchor pair
and exact ambient transport (4.3) are accepted as the virtual-carrier
construction. Dudko's published paragraph does not prove that independently
defined connected virtual hulls satisfy (4.3), nor that a pair satisfying
(4.4) exists at the central-to-terminal interface.

Accordingly Theorem 4.1 does not promote
`VIRTUAL_CORRIDOR_PAIR_NATURALITY`.

## 5. Exact anchor underdetermination

### Proposition 5.1 (published hull data do not force anchor equality)

The following data do not imply an attachment-free anchor:

1. a finite required package;
2. full connected source and target carriers containing that package;
3. degree-one selected-carrier dynamics avoiding the critical value; and
4. identical coarse orbit and limb labels.

**Proof.**
Work in a Jordan disk and let the required package be
\[
  S=\{-1,1\}.
\]
Let
\[
  T=[-1,1]
\tag{5.1}
\]
and let
\[
  T^{\dagger}
  =
  [-1,1]\cup[0,i].
\tag{5.2}
\]
Both are compact connected full plane continua containing \(S\). The identity
is a critical-value-free orientation-preserving univalent map on a
neighborhood of \(T^\dagger\) and restricts to the same degree-one dynamics
on \(T\).

The pair \(T\subset T\) is attachment-free. The pair
\[
  T\subset T^\dagger
\tag{5.3}
\]
has one excess component, the open vertical branch, attached at the access
represented by \(0\). The interval and the triod are not homeomorphic: the
triod has a point of valence three, while the interval does not. Hence no
homeomorphism of carrier pairs can identify (5.3) with the attachment-free
pair while fixing the required package and its order.

All four listed data are identical in the two models, but anchor equality
holds in only one. \(\square\)

### Corollary 5.2

The phrase “connected hull of the corresponding Cantor small Julia sets”
does not, by itself, select the attachment-free model. A canonical carrier
rule or a component-exhaustion theorem is necessary.

This is a counterexample to an inference from the published specification,
not a counterexample to the possible existence of a successful canonical
virtual carrier.

## 6. Finite attachment-orbit closure

When equality (4.4) is unavailable, the proof must track the components
forced into the embedded carrier by access completion.

Fix a finite resolved ribbon carrier with a finite cell set \(\mathscr C\).
Let \(C_0\subset\mathscr C\) be the cells of the proposed embedded carrier.
Let
\[
  \mathsf A:2^{\mathscr C}\longrightarrow2^{\mathscr C}
\tag{6.1}
\]
be the **attachment-completion operator**: \(\mathsf A(C)\) contains \(C\)
and every cell required by:

1. an excess component attached at a proof-used flag of \(C\);
2. access completion of a newly absorbed cell;
3. forward or backward transport through the declared finite corridor; or
4. fullification inside the fixed ambient carrier.

The operator must be proved inflationary and monotone:
\[
  C\subset\mathsf A(C),
  \qquad
  C\subset D\Longrightarrow\mathsf A(C)\subset\mathsf A(D).
\tag{6.2}
\]

### Theorem 6.1 (least finite attachment-orbit closure)

Define
\[
  C_{n+1}:=\mathsf A(C_n).
\tag{6.3}
\]
Then the sequence stabilizes after at most
\(|\mathscr C\setminus C_0|\) strict enlargements at a fixed point
\[
  C_\infty=\mathsf A(C_\infty).
\tag{6.4}
\]
Moreover:

1. \(C_\infty\) is the least attachment-complete cell set containing \(C_0\);
2. every admissible attachment-complete carrier containing \(C_0\) contains
   \(C_\infty\); and
3. if a corridor bijection \(P:\mathscr C\to\widetilde{\mathscr C}\)
   conjugates the completion operators,
   \[
     P\mathsf A=\widetilde{\mathsf A}P,
   \tag{6.5}
   \]
   then it transports the least closures:
   \[
     P(C_\infty)=\widetilde C_\infty.
   \tag{6.6}
   \]

**Proof.**
The inflationary property makes \(C_n\) increasing. Every strict step adds at
least one of the finitely many cells outside \(C_0\), so stabilization occurs
within the stated bound. At stabilization (6.4) holds.

If \(D\supset C_0\) is any fixed point, monotonicity gives inductively
\[
  C_n\subset D
\]
for all \(n\), hence \(C_\infty\subset D\). This proves minimality.
Equation (6.5) gives
\[
  P(C_{n+1})=P\mathsf A(C_n)
  =\widetilde{\mathsf A}P(C_n),
\]
so induction and stabilization prove (6.6). \(\square\)

### Definition 6.2 (closure collision invariant)

Let
\[
  \chi(C_\infty)
\tag{6.7}
\]
record:

1. every pair of selected sheets merged by the closure;
2. every central target that acquires the critical value;
3. every obstacle met by the closure;
4. every proof-used access erased or identified; and
5. every localization boundary crossed.

The pair
\[
  \mathfrak A_{\rm orb}
  :=
  (C_\infty,\chi(C_\infty))
\tag{6.8}
\]
is the **finite attachment-orbit closure invariant**.

### Corollary 6.3 (exact obstruction)

If \(\chi(C_\infty)\ne0\), no carrier obtained from \(C_0\) solely by monotone
attachment absorption can be simultaneously:

- attachment-complete;
- sheet-separated;
- critical-word compatible;
- obstacle-disjoint; and
- contained in the declared localization.

**Proof.**
Every attachment-complete enlargement contains \(C_\infty\) by
Theorem 6.1, so it retains every collision recorded by \(\chi\). \(\square\)

If \(\chi(C_\infty)=0\), the finite closure passes the topological collision
audit. This does not supply the analytic carrier, relative-cover lift,
properness, or width comparison.

## 7. Application to the planned virtual construction

The desired construction now has an exact decision tree.

### Route A: genuine anchor equality

At the central-to-terminal interface, prove the KKL-style exhaustion
statement:
\[
  \text{every pulled component meeting a proof-used central interval}
  \text{ already belongs to the immersed carrier.}
\tag{7.1}
\]
Then \(T'_k=T_k\) on the proof-used interface, Theorem 4.1 propagates equality,
and the central attachment support vanishes.

### Route B: finite attachment-orbit closure

If (7.1) fails, identify the first excess component \(X\), its attachment
access \(I\), and its complete first-return itinerary. Build
\(\mathfrak A_{\rm orb}\).

- If \(\chi\ne0\), the proposed carrier rule is impossible without changing
  the time slicing, selected sheets, or localization.
- If \(\chi=0\), promote the resolved closure to a new candidate carrier,
  reconstruct its analytic prime-end marking, and rerun the root, obstacle,
  relative-cover, and width audits.

No source checked in this pass proves (7.1) or
\(\chi(\mathfrak A_{\rm orb})=0\) for all virtual-Molecule blocks.

### Virtual attachment resolution gate

The correct downstream gate is the disjunction
`VIRTUAL_ATTACHMENT_RESOLUTION`:

1. either Route A proves an actual attachment-free anchor; or
2. Route B proves that the least attachment-orbit closure has zero
   collision, admits the required analytic prime-end realization, and has
   empty attachment support on the proof-used central intervals.

`VIRTUAL_ATTACHMENT_FREE_ANCHOR` names only the first, stronger branch.
The bounded-support theorem may depend on the disjunction; it must not
silently require Route A when Route B is sufficient.

### Canonical-carrier follow-up

The subsequent proof pass
[`canonical_virtual_interface_carrier.md`](canonical_virtual_interface_carrier.md)
shows that Route A cannot be reached from the published connected-hull
description by declaring the carrier to be inclusion-minimal: two prescribed
points have no least connected full carrier.  It also gives an actual
critical-value-free branch of \(z^2\) for which the first pulled excess is a
closed upper half-disk over an interval.  Absorbing that excess erases a
protected upper prime-end access, so its least closure has
\(\chi_{\rm access}\ne0\).

The required replacement invariant records the full attachment trace and the
partial survival map on protected accesses.  A zero collision in a quotient
that forgets either datum does not license analytic realization.

## 8. Adversarial validation

The construction must survive:

1. **Native KKL recovery:** \(T'_j=T_j\) gives the zero closure and empty
   support.
2. **Univalent quadratic model:** on a Jordan neighborhood avoiding the
   critical value, the selected branch of \(z^2+c\) is univalent and
   transports the pair and prime-end order.
3. **Hidden triod branch:** Proposition 5.1 defeats package-only and
   label-only naturality.
4. **Prime-end swap:** a set-pair bijection that reverses or exchanges marked
   accesses fails `PN6`--`PN7`.
5. **Non-locally-connected boundary:** the proof must use prime-end
   compactifications, not Euclidean boundary extension.
6. **Late root enlargement:** every attachment-orbit closure is rerun through
   the component-collision partition.
7. **Critical crossing:** a target acquiring the critical value sets
   \(\chi\ne0\) and terminates the degree-one construction.
8. **Horizon leakage:** the completion operator includes every attachment
   exposed through the full Wave horizon, not only one period.
9. **Cover mismatch:** a zero topological collision flag does not imply the
   relative-cover subgroup lift or end-properness.

## 9. Exact conclusion

The marked-pair naturality square can be constructed functorially from one
actual anchor pair by transporting the entire pair through univalent corridor
branches. Prime-end naturality then follows without local connectivity.

The unresolved point is the disjunction between an actual attachment-free
anchor and a collision-free analytic realization of the least
attachment-orbit closure. These are alternative sufficient routes, not
logically equivalent assertions. Dudko's published connected-hull description does
not decide this: Proposition 5.1 is an exact countermodel, and the quadratic
protected-access example in
[`canonical_virtual_interface_carrier.md`](canonical_virtual_interface_carrier.md)
is an exact nonzero analytic collision. Therefore
`VIRTUAL_CORRIDOR_PAIR_NATURALITY`,
`VIRTUAL_ATTACHMENT_FREE_ANCHOR`, and
`VIRTUAL_ATTACHMENT_RESOLUTION` remain open.

### Connector-realization update

`protected_regulated_connector.md` now proves that an actual protected
ribbon-routing certificate produces one full anchor carrier and that this
carrier, its crosscut-chain marking, and its ribbon order transport exactly
through every univalent Jordan corridor branch. Thus arbitrary connector
choice is no longer part of the conditional transport theorem.

The anchor certificate itself remains open in the actual virtual-Molecule
category. The proved free-component criterion first reduces its connector
part to `VIRTUAL_COMMON_FREE_COMPONENT`: one component of the completed free
routing domain must have simultaneous singleton ports to all required
root-shadow clusters. `VIRTUAL_PROTECTED_ROUTING_CERTIFICATE` must then
realize the complete component, sheet, obstacle, localization, and
critical-word data. Equality with the immersed carrier copy remains a
separate component-exhaustion requirement.

`virtual_common_free_component.md` further proves that the common component
exists if the frozen forbidden inventory admits pairwise disjoint full
augmented atom/obstacle packets and every original atom retains an explicit
free singleton port.  The actual
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE` remains open, and even its proof
would construct only the protected root connector.  It would not prove
equality with the immersed carrier copy, relative-cover compatibility, or
the attachment-free anchor.  Hence corridor-pair naturality remains open.

The later fixed-packet audit proves that, once the actual assignment and
full-packet univalent maps exist, closure and individual-port transport are
automatic and processing order is irrelevant.  It does not construct those
maps, prove the unique closure collision-free, or establish anchor equality.
