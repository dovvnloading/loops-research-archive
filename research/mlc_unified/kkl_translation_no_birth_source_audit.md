# KKL translation-corridor no-birth source audit

## 1. Purpose and status

This note source-locks the exact mechanism by which the long translation
corridor in Kahn--Kapiamba--Lyubich (KKL) avoids accumulating new ideal
endpoints. It then states the minimal abstract reduction that a virtual
carrier must realize.

There are three logically different claims:

1. KKL's ideal-interval pullback description and proper-corridor theorem are
   **imported only in KKL's native parabolically bounded Hubbard-tree
   category**.
2. The attachment-support reduction below is a proved abstract consequence
   of that description and of the endpoint-birth ledger.
3. A period-independent attachment-support theorem for Dudko's virtual hull
   is **open**.

No claim in this note imports the unpublished DKL virtual-renormalization
manuscript or promotes the virtual Wave branch.

## 2. Checked source

Source:

- Jeremy Kahn, Artem Kapiamba, Mikhail Lyubich, *MLC for parabolically
  bounded primitive renormalization*, arXiv:2606.27272.
- Checked public HTML on 2026-07-23.
- Checked local arXiv source
  `.tmp_wave_audit/waves-with-Misha.tex`, especially lines 1225--1286.

KKL use a periodically repelling prime primitively renormalizable
\(\psi\)-quadratic-like map. Put
\[
 \mathcal T'=f^{-1}(\mathcal T).
\]
The covering \(f\) and immersion \(\iota\) act from
\(\mathcal U'\setminus\mathcal T'\) to
\(\mathcal U\setminus\mathcal T\).

### Imported KKL Proposition 6.5

For a multi-interval \(I\) of the ideal marking \(\mathcal I\), or the
closure of one, KKL prove
\[
 \iota^*I
 =
 \iota^{-1}(I)
 \mathbin{\cup}
 \bigcup_{\substack{
  X\text{ a component of }\mathcal T'\setminus\mathcal T\\
  X\text{ meets }\mathcal T\text{ at }I
 }}
 \overline{\operatorname{Cara}X}.
\tag{2.1}
\]

This is an exact list of the possible extra ideal pieces under restriction
by the immersion. It is not merely a comparison of labels or cardinalities.

### Imported KKL Proposition 6.7

For parabolic occupancy bound \(B\), KKL prove that the induced interval
action \(F_*\) is proper on the central limb range
\[
 \mathcal L_{[B,q-B-2]}.
\tag{2.2}
\]
Their proof uses the actual carrier equality
\[
 \mathcal T'\cap\mathcal L_{[B,q-B-2]}
 =
 \mathcal T\cap\mathcal L_{[B,q-B-2]}.
\tag{2.3}
\]
The reason given is that every component of
\(F^{-1}(\mathcal K)\) in this range is already a component of the original
cycle \(\mathcal K\). Equation (2.1) then gives properness.

The public HTML numbers these as Propositions 6.5 and 6.7. The corresponding
local source labels are `prop:pullback description` and
`prop:improper intervals`.

## 3. What the source does and does not prove

Equations (2.1)--(2.3) prove the following native statement:

> In KKL's central translation corridor, the immersion exposes no new
> ideal-boundary component attached to an old marked interval.

Consequently, in the endpoint-birth notation of
`marked_endpoint_birth_ledger.md`, the corresponding native corridor has
\[
 b_j(I)=0
\tag{3.1}
\]
for each proof-used central interval \(I\), after the KKL source and target
markings have been identified as in their construction.

This conclusion is specific to the source's Hubbard tree and full cycle of
small filled Julia sets. KKL do not prove (2.3) for:

- a connected hull of Cantor small Julia sets;
- a partially invariant pseudo-Siegel or virtual carrier;
- an arbitrary selected pullback-component saturation;
- a finite cell-tree quotient of such a carrier.

In particular, “the dynamics is translation-like” does not imply (2.3).

## 4. Abstract attachment-support reduction

Consider a finite sequence of marked carrier correspondences
\[
 (T_j',T_j,\iota_j),\qquad 0\le j<N,
\]
with ideal interval markings \(\mathcal I_j\). Assume each proof-used
interval \(I\in\mathcal I_{j+1}\) has the pullback description
\[
 \iota_j^*I
 =
 \iota_j^{-1}(I)
 \cup
 \bigcup_{X\in\mathcal A_j(I)}
 \overline{\operatorname{Cara}X},
\tag{4.1}
\]
where \(\mathcal A_j(I)\) is the family of components of the pulled-carrier
excess \(T_j'\setminus T_j\) attached at \(I\).

Define the **attachment support**
\[
 \operatorname{Att}_j
 :=
 \{I\in\mathcal I_{j+1}:\mathcal A_j(I)\ne\varnothing\}.
\tag{4.2}
\]

### Theorem 4.1 (attachment support localizes endpoint births)

Assume:

1. every interval outside \(\operatorname{Att}_j\) has one selected
   degree-one immersion lift;
2. the polynomial map is conformal on that interval and on its endpoint
   prime ends;
3. the endpoint marking is access-complete.

Then
\[
 b_j(I)=0
 \qquad
 \text{for every }I\notin\operatorname{Att}_j.
\tag{4.3}
\]

If, in addition, there are fixed constants \(M,b_*\) such that

4. \(\operatorname{Att}_j=\varnothing\) for \(0\le j<N-M\);
5. at each of the remaining \(M\) stages, the total number of genuine new
   endpoints contributed by all attachment components is at most \(b_*\);
6. all boundary degrees in the last \(M\) stages are at most two;

then the degree-weighted birth charge satisfies
\[
 \mathfrak b_0\le b_*(2^M-1),
\tag{4.4}
\]
independently of \(N\).

**Proof.**
If \(I\notin\operatorname{Att}_j\), the second union in (4.1) is empty.
The hypotheses are then exactly those of Proposition 7.1 in
`marked_endpoint_birth_ledger.md`, which gives (4.3).

Hypotheses 4--6 say that all births lie in a terminal window of depth \(M\),
with at most \(b_*\) births per stage and degree at most two. Proposition 5.1
of the same ledger gives (4.4). \(\square\)

### Corollary 4.2 (native KKL central no-birth)

KKL Proposition 6.5 supplies (4.1), while the carrier equality in the proof
of KKL Proposition 6.7 makes the attachment support empty on the central
range (2.2). Therefore KKL's native central corridor realizes (4.3).

This corollary does not identify a virtual carrier with \(\mathcal T\).

## 5. The corrected virtual target

Global equality of the pulled and original virtual carriers is stronger than
the long-Wave endpoint estimate needs. The proof-minimal open target is:

### Virtual Bounded Attachment-Support Theorem

For every occupancy/control bound \(B\) and Wave depth \(L\), construct the
virtual marked carrier through the complete Wave horizon so that:

1. every proof-used ideal interval has an exact pullback description of the
   form (4.1);
2. the degree-one central fast-forward corridor has empty attachment
   support;
3. every attachment outside it lies in entry, exit, or auxiliary terminal
   windows of depth \(M(B,L)\);
4. those windows expose at most \(b_*(B,L)\) genuine endpoints per stage;
5. all selected endpoint lifts preserve their prime-end access and cyclic
   order;
6. the relative-cover immersion is proper or end-proper on precisely the
   intervals required by the Wave itinerary decomposition.

Theorem 4.1 would then give a period-independent endpoint-birth charge.

## 6. Why saturation alone does not close the target

The canonical construction in `saturated_virtual_seed_forest.md` makes a
chosen source carrier a component of the pullback of its chosen target.
That does not compare the pulled carrier \(T_j'\) with the carrier \(T_j\)
embedded by the immersion. Extra components of \(T_j'\setminus T_j\) can
still attach along central ideal intervals.

Thus the implications
\[
 \text{pullback-component saturation}
 \Longrightarrow
 \text{empty attachment support}
\tag{6.1}
\]
and
\[
 \text{equal translation labels}
 \Longrightarrow
 \text{empty attachment support}
\tag{6.2}
\]
are both invalid without an additional geometric theorem.

## 7. Falsification checklist

A claimed virtual proof must survive:

1. **Hidden branch:** add one pulled carrier component attached to a central
   interval without changing its old limb label.
2. **Distributed defects:** put one attachment in every degree-one stage;
   the unweighted local complexity stays bounded while the total birth count
   is \(O(q)\).
3. **Early quadratic birth:** introduce one endpoint before several
   quadratic pulls; its initial charge is multiplied by the preceding
   degree.
4. **Access collision:** keep endpoint cardinality fixed but merge two
   distinct prime-end accesses needed by different Wave leaves.
5. **Immersion failure:** preserve the set-theoretic carrier equality while
   choosing relative-cover subgroups for which the immersion does not lift
   or is not end-proper.

Passing only the first two tests does not discharge the last three.

## 8. Exact conclusion

The KKL source confirms that zero corridor births come from a local carrier
equality, not from period cancellation. The virtual problem is now reduced
to bounding the attachment support of the actual pulled virtual carrier.
That theorem remains open and is a precise part of the Virtual Seed
Certificate and the Virtual Endpoint-Birth Certificate.

## 9. Pair-naturality refinement

The subsequent proof in `corridor_attachment_transport.md` reduces the
central equality target further. If the actual pulled and immersed carrier
pairs are related along the degree-one corridor by commuting
orientation-preserving homeomorphisms that extend to the complete marked
prime ends, then attachment components and their supporting intervals
transport bijectively. One genuinely attachment-free anchor stage therefore
forces empty support throughout the entire central corridor.  The same
conclusion is sufficient if the least attachment-orbit closure is proved
collision-free, analytically realized, and empty on every proof-used central
interval.

This does not follow from root component routing: the selected polynomial
carrier may move homeomorphically while an ambient pulled branch moves to a
different marked access. The live virtual inputs are now the marked-pair
naturality square and `VIRTUAL_ATTACHMENT_RESOLUTION` (attachment-free
anchor or collision-free realized closure), in addition to the bounded
defect windows and relative-cover conditions already listed above.
