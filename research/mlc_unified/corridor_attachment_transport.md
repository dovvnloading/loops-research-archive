# Corridor attachment transport

## 1. Purpose and status

This note proves an exact reduction of the central part of the Virtual
Bounded Attachment-Support Theorem.

The polynomial root-carrier certificate controls selected pullback
components. It does not control the pair formed by:

1. the pulled carrier used to define the source surface; and
2. the carrier copy embedded by the immersion.

The missing comparison is not equality at every corridor stage. It is enough
to construct a natural marked homeomorphism of these **carrier pairs** along
the degree-one corridor and prove that one anchor pair is attachment-free.
Attachment support then transports bijectively to every central stage.

The transport theorem below is proved. Realizing its hypotheses for Dudko's
virtual Julia sets remains open.

## 2. Source boundary

Dudko's Interpolation Problem 4.4 proposes partially invariant virtual Julia
sets: connected hulls of the relevant Cantor small Julia sets, containing the
critical orbit through an appropriate number of first returns. The public
statement does not specify:

- a canonical connected hull;
- compatibility of the pulled and immersed carrier copies;
- prime-end naturality along a degree-one corridor; or
- an attachment-free anchor.

KKL use stronger native data. In the proof of their Proposition 5.7 they set
\[
  \mathcal T_j=\mathcal T\cap\mathcal L_j,
  \qquad
  \mathcal T'_j=F^{-1}(\mathcal T)\cap\mathcal L_j,
\]
and prove, throughout the central range,
\[
  \mathcal T'_j=\mathcal T_j
  \quad\text{and}\quad
  f:\mathcal T'_j\longrightarrow\mathcal T_{j+1}
  \text{ is a homeomorphism}.
\tag{2.1}
\]
Their Proposition 6.5 identifies every extra ideal pullback piece with the
Carathéodory boundary of a component of
\(\mathcal T'\setminus\mathcal T\) attached at the old interval. Their
Proposition 6.7 again uses the equality in (2.1) to obtain properness on the
central range.

Thus KKL have stagewise equality, which is stronger than the pair-naturality
criterion proved below. No checked source supplies that criterion for
Dudko's virtual carrier.

Sources rechecked on 2026-07-23:

- Dudko, *On the MLC Conjecture and the Renormalization Theory in Complex
  Dynamics*, Interpolation Problem 4.4 and the paragraph following it;
- Kahn--Kapiamba--Lyubich, *MLC for parabolically bounded primitive
  renormalization*, Propositions 5.7, 6.5, and 6.7;
- local KKL source `.tmp_wave_audit/waves-with-Misha.tex`, labels
  `prop:inner translation marking`, `prop:pullback description`, and
  `prop:improper intervals`.

## 3. Marked carrier pairs

For \(0\leq j\leq N\), let
\[
  \eta_j:T_j\hookrightarrow T'_j
\tag{3.1}
\]
be an inclusion of compact carriers. The excess is
\[
  E_j:=T'_j\setminus\eta_j(T_j).
\tag{3.2}
\]
Let \(\mathcal I_j\) be a finite access-complete ideal marking of \(T_j\).
For \(I\in\mathcal I_j\), let \(\mathcal A_j(I)\) be the family of
components of \(E_j\) attached at \(I\), in the sense of the exact KKL-form
pullback description. Put
\[
  \operatorname{Att}_j
  :=
  \{I\in\mathcal I_j:\mathcal A_j(I)\ne\varnothing\}.
\tag{3.3}
\]

### Definition 3.1 (marked pair naturality)

The transition from stage \(j+1\) to stage \(j\) is **marked-pair natural**
if there are orientation-preserving homeomorphisms
\[
  \Phi_j:T'_{j+1}\longrightarrow T'_j,
  \qquad
  \phi_j:T_{j+1}\longrightarrow T_j
\tag{3.4}
\]
such that
\[
  \Phi_j\circ\eta_{j+1}=\eta_j\circ\phi_j,
\tag{3.5}
\]
and:

1. \(\phi_j\) bijects \(\mathcal I_{j+1}\) with \(\mathcal I_j\);
2. \(\Phi_j\) extends to the proof-used prime-end compactifications; and
3. the extension preserves the marked accesses, their cyclic order, and the
   relation “the excess component \(X\) is attached at \(I\)”.

The prime-end clauses are assumptions, not consequences of a set-theoretic
homeomorphism of arbitrary non-locally-connected carriers.

## 4. Attachment transport theorem

### Theorem 4.1 (pair naturality transports attachment support)

Suppose the transition from stage \(j+1\) to stage \(j\) is marked-pair
natural. Then \(\Phi_j\) induces, for every
\(I\in\mathcal I_{j+1}\), a bijection
\[
  \mathcal A_{j+1}(I)
  \longleftrightarrow
  \mathcal A_j(\phi_j(I)).
\tag{4.1}
\]
Consequently,
\[
  \operatorname{Att}_j
  =
  \phi_j(\operatorname{Att}_{j+1}).
\tag{4.2}
\]
The same correspondence preserves the number and cyclic order of all
proof-used prime-end sides exposed by the attached components.

**Proof.**
By (3.5),
\[
\begin{aligned}
  \Phi_j(E_{j+1})
  &=
  \Phi_j\bigl(T'_{j+1}\setminus\eta_{j+1}(T_{j+1})\bigr)\\
  &=
  T'_j\setminus\eta_j(T_j)
  =
  E_j.
\end{aligned}
\tag{4.3}
\]
A homeomorphism maps components bijectively to components. Hence
\(\Phi_j\) bijects the components of \(E_{j+1}\) with those of \(E_j\).
The prime-end extension and the last clause of marked-pair naturality say
that a component is attached at \(I\) exactly when its image is attached at
\(\phi_j(I)\). This proves (4.1), and (4.2) follows immediately.

The prime-end extension is orientation preserving and carries the complete
marked access set at \(I\) to the complete marked access set at
\(\phi_j(I)\). It therefore preserves both cardinality and cyclic order.
\(\square\)

### Corollary 4.2 (one-anchor reduction)

If every transition in a degree-one central corridor is marked-pair natural,
then all attachment supports are identified:
\[
  \operatorname{Att}_j
  =
  \phi_j\phi_{j+1}\cdots\phi_{k-1}
  (\operatorname{Att}_k)
\tag{4.4}
\]
for \(j<k\). In particular, if one anchor stage \(k\) has
\[
  \operatorname{Att}_k=\varnothing,
\tag{4.5}
\]
then every stage in the corridor has empty attachment support.

**Proof.**
Iterate (4.2). \(\square\)

### Corollary 4.3 (persistent defects cannot be hidden)

Assume a degree-one corridor of length \(N\) is marked-pair natural. If one
stage has nonempty attachment support, every stage has nonempty attachment
support. If, in addition, every nonempty support exposes at least one genuine
new proof-used endpoint, then the endpoint-birth charge satisfies
\[
  \mathfrak b_0\geq N.
\tag{4.6}
\]

**Proof.**
Nonemptiness is invariant by Corollary 4.2. Under the additional endpoint
hypothesis, \(b_j\geq1\) for all \(j\). Every prefix degree is one, so the
endpoint-birth formula gives
\[
  \mathfrak b_0=\sum_{j=0}^{N-1}b_j\geq N.
\]
\(\square\)

The endpoint hypothesis in Corollary 4.3 is essential: an attached component
need not create a newly declared proof-used endpoint unless the marking is
access-complete for that component.

## 5. Why root routing is still insufficient

The degree-one root-pullback certificate gives a homeomorphism
\[
  f:H_{j+1}\longrightarrow H_j
\tag{5.1}
\]
between the selected polynomial carrier components. This controls the lower
row of the desired square (3.5). It does not construct a homeomorphism of the
pulled ambient carriers \(T'_{j+1}\to T'_j\), does not prove that the
immersion copies commute with that map, and does not supply the prime-end
extension.

Thus
\[
  \text{degree-one root routing}
  \not\Longrightarrow
  \text{marked-pair naturality}.
\tag{5.2}
\]

A finite countermodel is a path carrier \(T=\{a-b\}\) embedded in the tree
\(T'=\{a-b-x\}\). Preserve the path labels and the map on \(T\), but at the
next stage attach the ambient leaf \(x\) at a different marked vertex. The
selected carrier map remains a homeomorphism, while no commuting
homeomorphism of marked pairs exists and the attachment support changes.

## 6. Refined virtual target

The central part of the Virtual Bounded Attachment-Support Theorem now splits
into two exact open obligations.

### `VCPN` Virtual corridor pair naturality

For every virtual Wave corridor, construct the pulled/immersed carrier pairs
and orientation-preserving degree-one maps satisfying (3.4)--(3.5), with
access-complete prime-end extensions and exact compatibility with every
proof-used interval.

### `VAFA` Virtual attachment-free anchor

Construct one stage in each central virtual corridor at which the pulled
carrier has no excess component attached to a proof-used central interval.

By Corollary 4.2, `VCPN` and `VAFA` imply empty attachment support throughout
the central corridor. The remaining entry, exit, and terminal-window bounds,
relative-cover lifts, and end-properness are still separate parts of the
Virtual Bounded Attachment-Support Theorem.

## 7. Adversarial tests

1. **Carrier-only conjugacy.** Preserve \(T_{j+1}\to T_j\) but move one
   ambient leaf of \(T'_{j+1}\). Equation (3.5) fails and support need not
   transport.
2. **Set-pair conjugacy without access conjugacy.** Preserve
   \(T\subset T'\) set-theoretically but exchange two prime-end accesses at
   one attachment. Component support is preserved while the Wave marking is
   not.
3. **One persistent hidden branch.** A single nonempty support at an anchor
   repeats through the whole natural corridor and produces linear endpoint
   leakage whenever it exposes a genuine endpoint.
4. **False anchor.** Equality of coarse limb labels does not imply
   \(\operatorname{Att}_k=\varnothing\); the anchor must be checked on the
   actual pulled and immersed carriers.
5. **Non-degree-one transition.** If a target contains the critical value,
   two sheets can merge. The homeomorphisms in (3.4) are then unavailable and
   Theorem 4.1 cannot be applied across that transition.

## 8. Exact conclusion

Central attachment control no longer requires an independent carrier-equality
proof at every long-corridor stage. It requires a marked naturality square for
the carrier pair plus one genuine attachment-free anchor. This is a strict
reduction, not a solution of the virtual construction: neither input is
present in Dudko's published Problem 4.4 statement.

## 9. Subsequent anchor pass

`virtual_corridor_pair_naturality.md` proves that one actual anchor pair,
transported in its entirety through critical-value-free conformal corridor
branches, supplies the marked-pair naturality square and its prime-end cyclic
order without assuming local connectivity.

That pass also proves that Dudko's published connected-hull data do not force
the required anchor. An interval and an interval embedded in a triod contain
the same required package and have the same degree-one selected dynamics,
while only the latter has attached excess. The replacement invariant is the
least finite attachment-orbit closure; a collision in that closure persists
under every monotone attachment-complete enlargement.
