# Canonical virtual interface carrier and component-exhaustion obstruction

## 1. Purpose and exact verdict

This pass attacks the proposed canonical interface carrier at the
central-to-terminal boundary of a virtual Wave corridor.  It does not assume
that the phrase "connected hull" selects a carrier.

Four conclusions are proved.

1. A finite proof-use ledger determines a unique minimal **inventory** of
   components, orbit points, accesses, return words, and obstacles.  This is
   bookkeeping, not a connected planar carrier.
2. On a fixed finite resolved cell universe, monotone geometric completion has
   an order-independent least fixed point and agrees with the finite
   attachment-orbit closure precisely when the quotient records every
   completion implication.
3. There is no least connected full planar carrier containing even two
   prescribed points.  Thus inclusion, transport, fullification, and access
   completion do not canonically supply the connectors missing from Dudko's
   public virtual-hull description.
4. A critical-value-free branch of the quadratic map \(f(z)=z^2\) has an
   explicit first pulled-carrier excess whose monotone absorption erases a
   protected prime-end access.  Its complete one-stage itinerary and collision
   invariant are computed below.

The fourth item is the required exact obstruction.  It is not a counterexample
to the possible existence of a more structured virtual carrier, to MLC, or to
the unavailable virtual-renormalization program.  It proves that the data and
completion operations currently available in public sources do not imply the
requested attachment-free anchor or a collision-free analytic realization.

Consequently

- `VIRTUAL_CANONICAL_INTERFACE_CARRIER`,
- `VIRTUAL_CORRIDOR_PAIR_NATURALITY`,
- `VIRTUAL_ATTACHMENT_FREE_ANCHOR`, and
- `VIRTUAL_BOUNDED_ATTACHMENT_SUPPORT`

remain open.

## 2. Source lock and theorem boundary

### 2.1 Dudko's public statement

Dudko's Interpolation Problem 4.4 asks for a Virtual Molecule version of the
Near-Degenerate Regime.  The following paragraph describes partially invariant
virtual Julia sets only as connected hulls of the relevant Cantor small Julia
sets containing the critical orbit through an appropriate number of first
returns.  It gives no canonical connector, pulled/immersed carrier pair,
complete access marking, component-exhaustion theorem, relative-cover lift, or
uniform attachment bound.

Source:

- Dzmitry Dudko, *On the MLC Conjecture and the Renormalization Theory in
  Complex Dynamics*, arXiv:2512.24171, Interpolation Problem 4.4 and the
  paragraph following it:
  <https://arxiv.org/html/2512.24171#S4.SS5>.

### 2.2 KKL's stronger native carrier

Kahn--Kapiamba--Lyubich work with the full cycle of small filled Julia sets and
its Hubbard tree.  In their central range the source proof has actual carrier
equality.  Their ideal pullback formula then identifies every additional ideal
piece with a component of pulled-carrier excess attached to the old interval,
and their properness argument uses the same actual equality.  These are
carrier-specific hypotheses, not consequences of translation labels.

Source:

- Jeremy Kahn, Alex Kapiamba, and Mikhail Lyubich, *MLC for parabolically
  bounded primitive renormalization*, arXiv:2606.27272, Propositions 5.7, 6.5,
  and 6.7:
  <https://arxiv.org/html/2606.27272>;
- local source `.tmp_wave_audit/waves-with-Misha.tex`, labels
  `prop:inner translation marking`, `prop:pullback description`, and
  `prop:improper intervals`.

The component exhaustion in KKL comes from the native full cycle and Hubbard
tree.  No checked statement transfers that exhaustion to Dudko's proposed
virtual hull.

### 2.3 Availability check

The KKL bibliography describes
*Virtual renormalization: interpolating between primitive and satelite regimes*
by Dudko--Kahn--Lyubich as in preparation.  Exact-title, author, and
"Virtual Molecule" arXiv searches performed on 2026-07-23 found no public
manuscript.  No result from that unavailable work is imported.

## 3. Frozen interface certificate

Fix one finite declared Wave horizon \(0\leq j\leq N\), with the existing
orientation \(j+1\to j\).  An **analytic interface certificate** is
\[
  \mathfrak A
  =
  (U^-,U^+,F,\mathscr K,\mathscr O,\mathscr G,\mathscr R,\mathscr W;
    \mathscr Q),
\tag{3.1}
\]
with the following typed entries.

1. \(U^-\) and \(U^+\) are the selected source and target localizations.
2. \(F:U^-\to U^+\) is the relevant first-return or
   antirenormalization branch, with its degree and complete critical word.
3. \(\mathscr K\) contains the actual required Cantor small Julia components,
   including every touching cluster.
4. \(\mathscr O\) contains every prescribed critical-orbit point through the
   declared stopping time, with its iterate index.
5. \(\mathscr G\) is the ordered complete proof-used access and prime-end
   marking, not merely a list of landing points.
6. \(\mathscr R\) records root ancestry, parent routing, return word, limb,
   selected sheet, and every forward or pullback component name.
7. \(\mathscr W\) partitions every encountered ambient component, orbit point,
   fjord, and dam into `absorbed` or `separated`, with a localization witness.
8. \(\mathscr Q\) is the proof-use ledger.  Each Wave, Wanderers,
   quasi-additivity, covering, and width invocation records its source and
   target component, iterate length, critical encounters, accesses, obstacles,
   and curve family.

The certificate is **source complete** if every object referenced by
\(\mathscr Q\) occurs with all of its typed data in
\(\mathscr K\cup\mathscr O\cup\mathscr G\cup\mathscr R\cup\mathscr W\), and
every forward or inverse image used by \(\mathscr Q\) is recorded through its
last use.

### Proposition 3.1 (minimal proof-use inventory)

For a finite ledger \(\mathscr Q\), the intersection of all source-complete
inventories is source complete.  It is the unique minimal source-complete
inventory, denoted \(\operatorname{Inv}(\mathscr Q)\).

#### Proof

For each proof invocation \(q\in\mathscr Q\), let
\(\operatorname{supp}(q)\) be the finite typed list of components, orbit
indices, accesses, obstacles, return words, and curve families explicitly
read by that invocation.  Include all stage images and preimages between the
first declaration and last use of each entry.  Then
\[
  \operatorname{Inv}(\mathscr Q)
  =
  \bigcup_{q\in\mathscr Q}\operatorname{supp}(q).
\tag{3.2}
\]
Every source-complete inventory contains this union.  The union is itself
source complete because every reference made by every \(q\) is included with
its finite transport history.  Hence it is the intersection and the unique
minimum. \(\square\)

This proposition proves that omissions can be audited.  It does not prove
that the listed compacta lie in one connected full continuum, that the
continuum is dynamically admissible, or that the list has universal
cardinality.

## 4. Completion on a fixed finite resolved universe

Let \(\mathscr C\) be a fixed finite set of geometric cells.  A state
\(C\subset\mathscr C\) contains the cells currently absorbed into the carrier.
For each of the six proposed operations--required-package inclusion,
transport closure, fullification, access completion, ambient attachment
resolution, and collision-ledger update--let
\[
  A_\alpha:2^{\mathscr C}\longrightarrow2^{\mathscr C}
\]
be its resolved cell rule.

The rule is admissible only if it is inflationary and monotone.  Define
\[
  A(C):=\bigcup_\alpha A_\alpha(C),
  \qquad
  C_{n+1}:=A(C_n).
\tag{4.1}
\]

### Theorem 4.1 (finite geometric saturation)

The sequence in (4.1) stabilizes after at most
\(\lvert\mathscr C\setminus C_0\rvert\) strict enlargements.  Its limit
\(C_\infty\) is the least common fixed point of all \(A_\alpha\) containing
\(C_0\).  Applying enabled rules asynchronously in any fair order gives the
same \(C_\infty\).

#### Proof

The union \(A\) is inflationary and monotone.  Thus the iterates form an
increasing chain, and every strict iterate adds a cell.  Finiteness gives the
stated stabilization bound.

If \(D\supset C_0\) is fixed by every \(A_\alpha\), then \(A(D)=D\).
Monotonicity gives \(C_n\subset D\) inductively, so \(C_\infty\subset D\).
This proves minimality.

For an asynchronous fair iteration, every intermediate state is contained in
\(C_\infty\), again by monotonicity.  At stabilization, fairness makes it a
common fixed point containing \(C_0\), so minimality forces equality with
\(C_\infty\). \(\square\)

### Proposition 4.2 (quotient agreement and presentation invariance)

Let \(\pi\) map geometric objects to the cells of \(\mathscr C\).
The geometric saturation projects exactly to \(C_\infty\) if and only if
\(\pi\) is:

1. **implication complete:** every geometric forcing relation projects to one
   of the rules \(A_\alpha\); and
2. **implication sound:** every cell implication has a geometric witness.

If \(P:\mathscr C\to\widetilde{\mathscr C}\) is a cell bijection satisfying
\[
  P A_\alpha=\widetilde A_\alpha P
\tag{4.2}
\]
for every rule, then \(P(C_\infty)=\widetilde C_\infty\).

#### Proof

Completeness gives
\(\pi(\operatorname{Sat}(H))\subset C_\infty\) stage by stage; soundness gives
the reverse inclusion.  Equation (4.2) conjugates every finite iteration, so
it conjugates the stabilized fixed points. \(\square\)

The qualification in Proposition 4.2 is essential.  A quotient that forgets
an access, an attachment trace, or an ambient component may have zero
collision while the planar carrier does not.

## 5. No canonical least connected carrier

The finite fixed-point theorem starts only after a resolved universe and its
connector cells have been supplied.  Dudko's public phrase "connected hull"
does not supply them.

### Theorem 5.1 (nonexistence of a least full connected hull)

There is no least compact connected full subset of the plane containing the
two-point package
\[
  S=\{-1,1\}.
\tag{5.1}
\]
This remains true with identity dynamics, an empty obstacle set, and an empty
additional orbit package.

#### Proof

Let \(A_+\) and \(A_-\) be respectively the upper and lower semicircles with
endpoints \(-1\) and \(1\).  Each is an arc, hence a compact connected full
plane continuum containing \(S\).  They satisfy
\[
  A_+\cap A_-=S.
\tag{5.2}
\]
If a least full connected carrier \(H\) containing \(S\) existed, then
leastness would give \(H\subset A_+\) and \(H\subset A_-\).  Therefore
\(S\subset H\subset S\), so \(H=S\), which is disconnected.  This is a
contradiction. \(\square\)

### Corollary 5.2 (connector datum is unavoidable)

Package inclusion, identity transport, fullification, and access completion
do not determine a connected carrier.  At least one additional geometric
datum is necessary, such as a regulated connector system together with its
isotopy/access class and a proof of forward coherence.

The word "minimal" cannot replace that datum: Theorem 5.1 rules out a minimum
under inclusion.

## 6. Exact analytic access-collision obstruction

The next example is stronger than the interval/triod underdetermination.  It
uses an actual degree-one branch of a quadratic polynomial and produces a
nonzero collision invariant.

Let
\[
  f(z)=z^2,\qquad
  I=[1,2],\qquad
  m=\frac32,
\tag{6.1}
\]
and let
\[
  Q
  =
  \left\{
    z:\left|z-\frac32\right|\le\frac12,\ 
    \operatorname{Im}z\ge0
  \right\}
\tag{6.2}
\]
be the closed upper half-disk with diameter \(I\).  Put
\[
  U^-=\left\{z:\left|z-\frac32\right|<1\right\},
  \qquad U^+=f(U^-).
\tag{6.3}
\]
Since \(U^-\subset\{\operatorname{Re}z>1/2\}\), \(f\) is injective and has
nonzero derivative on \(U^-\).  Thus
\[
  F:=f|_{U^-}:U^-\longrightarrow U^+
\tag{6.4}
\]
is an orientation-preserving conformal homeomorphism of Jordan domains.

Define the stage-zero carrier pair and its transported stage-one pair by
\[
  T_0=I,\quad T'_0=Q,\qquad
  T_1=f(I),\quad T'_1=f(Q).
\tag{6.5}
\]
Within the selected branch,
\[
  T'_0=F^{-1}(T'_1),\qquad
  T_0=F^{-1}(T_1).
\tag{6.6}
\]
Both \(T'_0\) and \(T'_1\) are full connected continua, and the branch avoids
the critical point and critical value.

For \(T_0\), declare the upper access
\[
  p_0^+(m)
\tag{6.7}
\]
represented by the curve \(m+it\), \(0<t<1/2\).  Its transported access is
\[
  p_1:=F_*p_0^+(m)
\tag{6.8}
\]
landing at \(m^2=9/4\).

### Proposition 6.1 (first excess and complete itinerary)

The pulled-carrier excess has the single component
\[
  X_0=T'_0\setminus T_0=Q\setminus I.
\tag{6.9}
\]
Its attachment trace is
\[
  \tau_{T_0}(X_0)
  :=
  \overline{X_0}^{\,T'_0}\cap T_0
  =I.
\tag{6.10}
\]
With the ordered proof-used marking
\(\mathscr G_0=(p_0^+(m))\), its first attachment access is
\(p_0^+(m)\).  Its complete horizon-one itinerary is
\[
\begin{array}{c|c|c|c|c|c}
  j&X_j&\text{attachment trace}&\text{marked access}
   &\text{sheet}&\text{critical word}\\ \hline
  0&Q\setminus I&I&p_0^+(m)&\text{right}&0\\
  1&f(Q\setminus I)&f(I)&p_1&\text{right}&0 .
\end{array}
\tag{6.11}
\]
The parent route is the transported root route
\(X_0\mapsto X_1\); there is no intermediate return and no critical
encounter.

#### Proof

The relative interior of the convex half-disk above its diameter is
connected, giving (6.9).  Its closure meets the diameter in all of \(I\),
giving (6.10).  The access in (6.7) is the sole member of the ordered marking,
so it is first.  Conformality of \(F\) transports the component, attachment
trace, sheet, and access.  The critical word is \(0\) because
\[
  0\notin U^-,\qquad 0\notin U^+,\qquad F'(z)=2z\ne0
\]
on \(U^-\).  This exhausts the one-stage horizon. \(\square\)

### Theorem 6.2 (protected-access collision)

Every monotone attachment-complete enlargement of the immersed carrier
\(T_0\) that absorbs \(X_0\) erases the protected upper access
\(p_0^+(m)\).  The same is true of \(p_1\) after transport.  Hence the least
closure has collision invariant
\[
  \chi(C_\infty)
  =
  \bigl(
    \varnothing,\,
    \varnothing,\,
    \varnothing,\,
    \{p_0^+(m),p_1\},\,
    \varnothing
  \bigr),
\tag{6.12}
\]
in the order
\[
  (\chi_{\rm sheet},\chi_{\rm crit},\chi_{\rm obs},
    \chi_{\rm access},\chi_{\rm loc}).
\]

#### Proof

Absorbing \(X_0\) and retaining \(T_0\) forces the enlarged carrier to contain
\(Q\).  But \(Q\) contains a relative upper half-neighborhood of \(m\).
Therefore no curve in \(U^-\setminus Q\) can land at \(m\) from the upper
side.  The access represented before absorption by \(m+it\) is absent from
the prime-end boundary of the enlarged upper complement localization.
Further monotone enlargement cannot restore a complement access through a
set already contained in the carrier.

Conformality transports this statement to \(F(Q)\) and \(p_1\).  The two
selected sheets do not merge, no critical point or value enters, no obstacle
is present, and both carriers remain compactly contained in their
localizations.  Thus access erasure is the first and only collision, giving
(6.12). \(\square\)

### Corollary 6.3 (the proposed analytic realization is not implied)

For the certificate (6.1)--(6.8), no monotone enlargement can be both
attachment complete and natural on the complete protected access marking.
In particular, a zero cell-level collision obtained by forgetting
\(p_0^+(m)\) is a false positive.

## 7. Replacement invariant and required interface

The finite invariant must retain more than absorbed cells.  For every excess
component \(X\), define its **geometric attachment trace**
\[
  \tau_T(X)
  :=
  \overline X^{\,T'}\cap T
\tag{7.1}
\]
where the closure is taken in the actual pulled carrier \(T'\) (equivalently
in the ambient localization when \(T'\) is closed there).  This is not
\(X\cap T\): because \(X\) is a component of \(T'\setminus T\), that latter
intersection is always empty.  A prime-end attachment record is separate
data: it consists of the protected crosscut chains whose selected sides
accumulate on \(\tau_T(X)\).  Define the **protected-access survival
relation**
\[
  \sigma_X:\mathscr G(T)\dashrightarrow
  \mathscr G\bigl(\operatorname{Full}(T\cup X)\bigr).
\tag{7.2}
\]
The replacement invariant is
\[
  \mathfrak A_{\rm prot}
  =
  \bigl(
    C_\infty,\chi(C_\infty),
    \{\tau_T(X)\}_X,\{\sigma_X\}_X
  \bigr).
\tag{7.3}
\]

An interface enlargement is admissible only if every proof-used access lies
in the domain of every relevant \(\sigma_X\), survives injectively, and keeps
its cyclic order.  The invariant (7.3) is presentation invariant only under
maps that preserve the full attachment traces and conjugate the access
survival relations, not under coarse cell-label equivalence.

For the example above,
\[
  \tau_{T_0}(X_0)=I,\qquad
  p_0^+(m)\notin\operatorname{dom}\sigma_{X_0}.
\tag{7.4}
\]
Therefore the current interface must be replaced in one of the following
exact ways:

1. choose and prove a regulated, forward-coherent connector system before
   fixing the protected access marking;
2. retime the block so the multi-access attachment lies in a declared defect
   window rather than the degree-one central corridor; or
3. change the localization and selected carrier pair so the excess component
   is separated rather than monotonically absorbed.

Deleting the protected access is not a valid replacement when the Wave or
width proof uses it.

## 8. Why KKL component exhaustion does not transfer

In KKL's native central corridor, the full-cycle construction proves that
every relevant pullback component is already a component of the declared
cycle.  The Hubbard tree is then built from that cycle, and the actual
central carrier equality eliminates the attachment support.

The checked virtual-hull statement supplies none of the following:

1. a connector rule selecting one carrier among those in Theorem 5.1;
2. a theorem that every connector image stays in the declared parent carrier;
3. a single-attachment-trace or protected-access-survival condition;
4. equality between the polynomially pulled carrier and the copy embedded by
   the immersion; or
5. exhaustion of ambient Cantor components meeting central ideal intervals.

Thus the desired statement
\[
  \text{every pulled component meeting a proof-used central interval
  already lies in the immersed carrier}
\tag{8.1}
\]
cannot be derived from the public hypotheses.  Theorem 6.2 shows that simply
absorbing the first failure of (8.1) can destroy the marking that the
naturality theorem is required to preserve.

## 9. Analytic gates not discharged by zero collision

Even if a future construction gives
\(\chi(C_\infty)=0\), it must still prove:

1. Jordan localizations and univalent collars for the actual full carriers;
2. exact equalities
   \(g_j^{-1}(H_{j+1})=H'_j=\iota_j^{-1}(H_j)\);
3. the relative-cover subgroup inclusion;
4. core properness and end-properness;
5. complete prime-end marking and cyclic order;
6. a bounded defect-window endpoint charge; and
7. analytic width comparisons with constants independent of period,
   rotation number, and corridor length.

The fixed-topology quadratic-like rescaling counterexample in
`finite_horizon_inflation.md` shows independently that topological collision
freedom cannot imply a uniform width estimate.

## 10. Adversarial audit

The construction was cross-examined as follows.

| Attack | Result |
|---|---|
| KKL native central-range specialization \(T'\cap\mathcal L_{[B,q-B-2]}=T\cap\mathcal L_{[B,q-B-2]}\) | No pulled excess meets a proof-used central interval, so the local attachment trace is empty and no protected central access is erased.  No global equality \(T'=T\) is asserted. |
| Actual quadratic degree-one branch | Equations (6.1)--(6.6) use \(z^2\) on a Jordan disk wholly inside the right half-plane. |
| Hidden ambient branch | The interval/triod model remains a valid underdetermination test. |
| No least connector | Theorem 5.1 defeats "take the minimal connected full hull." |
| Completion-order dependence | Theorem 4.1 proves independence only after every monotone rule and candidate cell are fixed. |
| Quotient hides access | Theorem 6.2 becomes invisible if the midpoint upper prime end is omitted. |
| Prime-end swap | Admissibility of (7.2) requires injection and cyclic-order preservation. |
| Non-locally-connected carrier | The definition uses prime ends and access relations, not Euclidean boundary extension. |
| Late root enlargement | All future forcing relations must enter the fixed universe before \(C_\infty\) is computed. |
| Critical-window crossing | It sets \(\chi_{\rm crit}\ne\varnothing\) and invalidates the degree-one branch. |
| Incomplete horizon | Proposition 3.1 includes every stage through the last proof use. |
| Relative-cover mismatch | It remains a separate analytic gate even when \(\chi=0\). |
| Collision-free topology but bad width | The rescaling no-go keeps width calibration independent. |

No constant is asserted in this pass.  In particular, no period-, rotation-,
or depth-independent analytic bound is inferred from the finite closure.

## 11. Promotion decision and next theorem

The following results may be recorded as proved:

- finite minimal proof-use inventory;
- finite geometric saturation on a fixed implication-complete universe;
- nonexistence of a least connected full carrier;
- the explicit quadratic protected-access collision; and
- necessity of the protected attachment-trace invariant (7.3).

The virtual obligations are not promoted.  Their exact replacement target is:

> For each actual virtual-Molecule block, construct a regulated,
> forward-coherent connector system from the simultaneous root pullback;
> prove that every pulled excess component has an explicitly recorded
> attachment trace and injective protected-access survival map through the
> complete Wave horizon; and prove KKL-style component exhaustion on the
> central corridor, placing every remaining nonempty trace in a uniformly
> bounded defect window with compatible relative-cover lifts.

Until this theorem is proved, full pair transport remains conditional on an
anchor that the public theory does not construct.

### Connector-realization update

The subsequent pass
`protected_regulated_connector.md` proves that any actual finite protected
ribbon-routing certificate has a full connected carrier with singleton
connector traces, injective cyclic-order-preserving prime-end survival, and
univalent naturality. This closes the abstract topological realization
step, but not the virtual dynamical selection.

The first live input is now
`VIRTUAL_PROTECTED_ROUTING_CERTIFICATE`: construct the lamination-lifted or
puzzle-cell regulated root tree for the actual virtual-Molecule block and
prove that every projection fiber, edge, and fullification component avoids
the protected collar tails while the iterated pullback components realize
all packages, routes, sheets, and critical words.

### Free-component update

`virtual_protected_routing_domain.md` now proves that the connector part of
collar avoidance is equivalent to an exact planar condition. After the
complete future inventory is frozen, one component of the free routing
domain must have simultaneous singleton ports to every required root-shadow
cluster. If it does, a finite spanning-tree construction supplies the
protected connector; if it does not, the first separating collar or
obstacle is monotone-unrepairable within the current localization.

Thus arbitrary connector choice is no longer a gap.
`VIRTUAL_COMMON_FREE_COMPONENT` is the first open dynamical assertion,
followed by root component routing, critical words, future access
completeness, and uniform complexity. No public source currently proves
that common-component assertion.

### Augmented-atom refinement

`virtual_common_free_component.md` now proves a sufficient theorem for the
common-component assertion.  A future-complete assignment of every frozen
forbidden piece to connected atom or obstacle seeds gives full augmented
packets.  If those packets cover the inventory, remain pairwise disjoint
inside the localization, and every original atom retains an explicit free
singleton port, compacta Alexander duality makes their common complement
connected.  The free-component theorem then constructs the protected
connector.

The source-faithful assignment, post-fullification disjointness, and
surviving ports are the open
`VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE`.  A packet merger or port loss
refutes that attempted sufficient construction, not automatically
`VIRTUAL_COMMON_FREE_COMPONENT`; the latter fails only with an actual
separator in the original frozen free domain.  Therefore the virtual
canonical interface carrier is not promoted.

The later fixed-packet audit in
`augmented_packet_closure_audit.md` removes completion order and global
 port-arc untangling as separate choices.  For a fixed typed assignment the
 completed packets are unique; same-label merger, localization, and empty
 exposure defects persist monotonically; and individual unprotected ports
 can be truncated in disjoint packet neighborhoods.  The open input is now
 the stopped virtual Wave horizon and its no-late-dependency certificate,
 then the actual typed inventory, zero collision of its unique closure,
 original-atom exposure, complete-horizon transport, and uniform incidence
 or faithful compression.
