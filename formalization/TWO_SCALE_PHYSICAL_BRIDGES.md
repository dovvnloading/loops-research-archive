# From the 3/9 certificates to the dynamical plane

The archive uses two different real quadratics in this calculation. For both write
$f_c(z)=z^2+c$, $P_0=0$, $P_{j+1}=P_j^2+c$. Use $c_0$ for the
period-27 **center** and $c_t$ for the **tip**, the root of $P_{18}+P_9$
in its separate bracket. Each bracket is $(k/2^{128},(k+1)/2^{128})$. The center has
$k=-607890580437450502081459824019535455703$ and the tip has
$k=-607918036626757496169199575185708826140$. Below, a *written* implication has a proof to
review in the linked source. A *kernel* result concerns the statement in
the named Lean file. An *open* step has a stated mathematical target.

## Parameters, returns and rays

### D1. Orbit enclosures to a real center (kernel)

Outward interval bounds for the polynomial recurrence and its derivative give opposite endpoint signs for $P_{27}$ and a strictly negative derivative throughout the specified dyadic bracket. Continuity gives a root, strict monotonicity gives uniqueness there, and exclusion of earlier returns gives exact period 27. Its superattracting cycle has an open basin, so the hypothesis $K(f)=J(f)$ needed for Paper 2 fails here. [Existence](weighted/Period27RealCenter.lean), [uniqueness](weighted/Period27RealUniqueness.lean), [exact period](weighted/Period27RealExactPeriod.lean), [bracket and basin proof](../research/independent_audits/real_quadratic_3_9_restrictive_certificate_20261105.md).

### D2. Center word to a component and exterior sheets (written)

Buff–Floyd–Koch–Parry §4.4 identifies the signed kneading angles with rays landing at the **component root** of this exact-period real center. Zakeri §2 computes the root rays of the triple airplane tuning by substitution. The identical normalized periodic rays determine a unique component, whose center is $c_0$. Separately, boundedness of the critical orbit gives a global exterior Böttcher coordinate. In that coordinate $f^6$ multiplies angles by 64, giving 64 inverse angles per exterior ray, at positive potential. These are sheets in the escaping basin. [Component proof](../research/independent_audits/period27_center_tuning_identification_20261106.md), [exterior domain and inverse branches](../research/independent_audits/period27_exterior_ray_pullback_20261106.md).

### D3. Tip enclosures to a Misiurewicz polynomial (exact certificate + written)

For $Q=P_{18}+P_9$ check endpoint signs and $-71<Q'<-70$ on the tip bracket. At its unique zero $x_j=P_j(c_t)$ satisfies $x_{18}=-x_9$, hence $x_{19}=x_{10}$. Pairwise disjoint enclosures for $x_0,\ldots,x_{18}$ give exact preperiod 10 and period 9. The product of $2x_j$ for $10\le j\le18$ lies in $(3,4)$. The subhyperbolic and Fatou–Julia theorems apply to this strictly preperiodic-to-repelling critical orbit and give connected locally connected $K(f)=J(f)$. [Theorem A and arithmetic](../research/independent_audits/period27_misiurewicz_tip_ray_access_20261106.md), [analytic inputs and theorem numbers](../research/independent_audits/levin_tip_p2_carathéodory_two_scale_20261106.md).

### D4. Intervals to actual real first returns (written)

At $c_t$, take $I_3=[x_6,x_3]$ and $I_9=[x_9,x_{18}]$. Verify nesting, pairwise disjoint forward phases for each period and avoidance of 0 by the intermediate phases. Monotonicity on the two halves of each interval and its endpoint and critical values give $f^p(I_p)=I_p$. Disjointness rules out an intermediate return. At $c_0$ use its own parameter, endpoint and phase inequalities. [Tip §3](../research/independent_audits/period27_misiurewicz_tip_ray_access_20261106.md), [center §§2–3](../research/independent_audits/real_quadratic_3_9_restrictive_certificate_20261105.md).

### D5. Disk margins to polynomial-like maps and physical phases (written)

Write $f^p(z)=x_p+a_pz^2+h_p(z)$ with $|h_p(z)|\le T_p(R)$ on the source disk. On its boundary check $|a_p|R^2>|x_p|+T_p(R)+R_{\rm target}$. Rouché counts two preimages with multiplicity for each target point. The critical value is in the target, and the sole critical point 0 accounts for both local sheets. The boundary gap gives a relatively compact proper component $V_p$. Avoidance of intermediate critical points up to the boundary gives a regular boundary. Riemann–Hurwitz gives a disk. Critical-orbit containment gives connected $K_p$. Check phase-disk disjointness and $f^{3k}(U_9)\subset V_3$ for $k=0,1,2$ to deduce $f^j(V_9)\subset f^{j\bmod 3}(V_3)$, $0\le j<9$. These inclusions give the physical meaning of the clock projection. The inner shrink radius is $27/1024$ at the tip and $13/512$ for the center neighborhood. [Tip margin checks](../TipComplexMargins.lean), [tip domain proof](../research/independent_audits/nonattracting_tip_complex_two_scale_20261106.md), [center disk and parameter quantifier](../research/independent_audits/complex_two_scale_quadratic_like_certificate_20261105.md).

### D6. Tip addresses to landed rays (written)

Apply Zakeri §3, Theorems 3.1 and 3.3 to D3 and the signed critical-value itinerary. The angles $116791/261632$ and $1-116791/261632$ label parameter rays at $c_t$ and dynamical rays at $x_1$. In the dynamical plane, lift rays off the critical-value slit by the two inverse branches, treating the double preimage at 0 separately. Forward iteration supplies the period-nine subportrait. For the specified depth-ten inverse fiber the independent exhaustion proof starts with the complete two-ray periodic class, uses univalence before the critical encounter and counts $2(512-1)+1=1023$ distinct inverse points, one with four rays. The complete-periodic-class argument fixes the target at $P_{10}(c_t)$ and uses an orbit-portrait argument to exclude extra landing rays. [Landing proof](../research/independent_audits/period27_misiurewicz_tip_ray_access_20261106.md), [subportrait arithmetic](../TipRayPortrait.lean), [complete initial portrait](../research/independent_audits/tip_nested_full_precritical_ray_census_and_levin_ladder_20261107.md), [inverse-branch and exhaustion proof](../research/independent_audits/tip_full_precritical_global_ray_lamination_and_single_flip_20261107.md).

### D7. Eligible ambient rays to two internal ray maps (written)

Put $\Lambda_p=\{\theta:L_f(\theta)\in K_p\}$ using the actual landing map at the tip. The distance from $K_p$ to $\partial V_p$ is positive. Uniform continuity of the extended inverse Böttcher map sends sufficiently short low-Green-level segments of **all** eligible rays inside that distance. Thus every crossing of $\partial V_p$ has a uniform positive ambient Green level, satisfying Levin (p2). D5 supplies (p1). Levin's theorems now define $\Pi_p$ on $\Lambda_p$. Straighten $f^3$ by $h$, verify (p1) and (p2) for the intermediate return on $h(K_9)$, and call its angle map $Q$. Access homotopies in the complement of $K_3$ remain in the complement of $K_9$. Transport the intermediate homotopy by $h^{-1}$. Uniqueness of the normalized degree-two access gives $\Pi_9=Q\circ\Pi_3$ on $\Lambda_9$. This argument concerns prime ends of these carriers. Within the 32 marked coarse ray tails, 24 land at 12 points interior to the fine exterior and thus lose properness there. [Green-level proof](../research/independent_audits/levin_tip_p2_carathéodory_two_scale_20261106.md), [composition and 24 tails](../research/independent_audits/tip_levin_full_domain_composition_and_24_escaped_accesses_20261108.md).


### D8. A single critical collision under real parameter variation (written)

Let $Z(c)$ continue $P_{10}(c_t)$ as a fixed point of $f_c^9$. The implicit-function theorem applies because its multiplier $\lambda$ is in $(3,4)$. Differentiate $P_{19}-P_{10}=(P_{18}-P_9)(P_{18}+P_9)$ at $c_t$ and use the fixed-point equation. It gives $(P_{10}-Z)'=(P_{18}-P_9)(P_{18}'+P_9')/(\lambda-1)<0$ there. For the equation $f_c^{10}(z)=Z(c)$, the unique double inverse at 0 is quadratic in the local spatial coordinate and this parameter derivative is nonzero. Its two continuations are exchanged around the parameter. Every other inverse point is simple, hence persists on a disk. Pairing the four critical rays on either real side also requires the two sector inverses, conjugation and repelling-ray persistence. The resulting flip concerns this depth-ten fiber in a sufficiently small real neighborhood. [Transversality, Theorem 1.1](../research/independent_audits/period9_tip_phase_parameter_transversality_20261107.md), [ramification and one transposition](../research/independent_audits/period9_tip_ramified_precritical_pair_20261107.md), [real-side pairing proof](../research/independent_audits/period9_tip_real_ray_pairing_bifurcation_20261107.md).

## Physical covers and marked sides

**L1. Identify the fiber before applying the sheet kernel.** Fix a connected
based cover of the actual exterior, basepoint $x$, chosen lift and subgroup
$H=p_*\pi_1(\widehat\Omega,\hat x)$. Lift a loop $g$ from that lift and
record its endpoint. Path and homotopy lifting give the same endpoint for
$g,h$ exactly when $gh^{-1}\in H$ (paths concatenate in traversal order).
Connectedness makes the map onto the fiber. This gives the coordinate $Hg$
with right monodromy. The kernel in Lean uses $a^{-1}b\in H$. The change
of representative is $Hg\mapsto g^{-1}H$. For a based map $a$ admitting a lift between these covers, functoriality of path lifting sends this endpoint to the one represented by $a_*g$. The lift criterion is $a_*(H_s)\subseteq H_t$. Thus a loop in
$a_*^{-1}H_t\setminus H_s$ separates two source lifts with one target
endpoint. In Paper 1's ordinary primitive canonical seed the physical
witness is a peripheral loop about an excess component. Its winding around
that component excludes membership in $H_s$. The component is filled on the
target side, where the loop contracts. The corresponding factorization is
on the complementary covers. [Kernel](weighted/LocalizationSheetKernel.lean),
[primitive seed and excess loop](../papers/paper1_canonical_localization/extracted/C_forced_collision/),
[based pullback component and embedding](../papers/paper1_canonical_localization/extracted/D_resolution/).

**L2. Identify the actual smaller-root projection.** At $c_t$ label the
nine physical obstacles $D_{r,j}=f^{r+3j}(K_9)$ for $0\le r,j<3$.
The fine root is $D_{0,0}=K_9$. The stage-$f^9$ straightening has
critical orbit $0\mapsto d\mapsto d^2+d\mapsto d^2+d$, hence
$d^3(d+2)=0$. Exact preperiod excludes zero. Straightening thus makes
$K_9$ an arc. Its endpoints $x_9,x_{18}$ are joined by the already
invariant real interval inside it, so $K_9=[x_9,x_{18}]$.
The physical $K_3$ contains a four-arm star. For a Kahn morphism with
full marks one needs $K_9=g^{-1}(K_3)$. The open mapping theorem and
compactness would force surjectivity onto $K_3$. A local holomorphic
power map over the star forces branching in its inverse, impossible in an
interval. With $K_9$ as the mark on both sides, deleting the two noncentral
inner roots from the coarse localized target and localizing again gives an
iterated surface. The based cover comparison and the root charts give a
strict open embedding $J$ into the direct fine surface. On its image the
fine-to-coarse projection is $L=\rho\circ J^{-1}$. For each native tile
of the canonical coarse pseudo-piece its core winds once around each of
three inner roots. A nonzero power has nonzero winding about an excluded
root, whereas all conjugates of the single-root subgroup have zero such
winding. The lifts are therefore distinct by L1 and have the same projected
point by deck invariance. [Full-root obstruction](../research/independent_audits/tip_interval_root_and_marked_morphism_obstruction_20261106.md),
[smaller-root map, domains and actual collision, §§2–8](../research/independent_audits/tip_iterated_direct_canonical_localization_embedding_20261106.md).

**L3. Identify the source of each ideal point.** For each of the stages $f$ and
$G=f^3$, apply the KL puzzle definitions with $q=2,n=1$. Permanent
residence of the returning critical orbit in the first child, boundary
separation and the filled-set comparison identify the terminal maps
$Y^6\to Y^3$ on their interiors, with stage time 3 and physical times
3 and 9. In the **ordinary** $G$-piece $W=Y_G^6$, KL II §3.2 glues four
annular universal tiles along open seams. The ordinary immersion
$j_W:\Psi_G(W)\to\widehat T_9$ is rooted on the geometric piece. The
following deductions use this source and the **uncompactified** fine
target. [First-child proof](../research/independent_audits/tip_kl_terminal_first_child_20261106.md),
[source atlas for the two stages](../research/independent_audits/tip_kl_pseudopiece_side_atlas_20261106.md).

| Source point or path | Test on the physical map | Result and proof |
|---|---|---|
| Finite outer points, finite vertices, or strict inner points landing in the fine exterior | Check a regular evenly covered neighborhood. For a vertex, use the $W\to V^0$ naturality diagram to identify the local branch. | Local extension to an ordinary fine-cover point. [Boundary proof §§2–5](../research/independent_audits/tip_native_full_W_ideal_circle_pointwise_extension_20261109.md). |
| Strict inner points with landing in $D_{0,1}\cup D_{0,2}$ | The projected limit lies outside $T_9$. Any compactly accumulating lift would project there by continuity. | Escape from every compact set. [Target trichotomy](../research/independent_audits/tip_native_finite_J_side_target_trichotomy_20261109.md). |
| Strict inner points landing on $K_9$ | For a ray in a gluing seam, the other tile with the same parent at shift zero agrees with the root section on a positive-height segment. Nonzero native shifts are detected by winding. Different-parent lifts are distinguished by the difference of windings about the two excluded obstacles, computed on the physical Jordan wakes. | In the strict ideal-side domain only the zero-shift mate extends at the root. The sector-exhaustion argument is needed to apply this test to all eligible angles. [All-integer lifts](../research/independent_audits/tip_native_root_deck_monodromy_20261109.md), [wake and sector proof](../research/independent_audits/tip_native_C4_wake_root_sheet_naturality_20261109.md). |
| Eight infinitely winding outer/inner joints | Deck translates of two interior tile points converge to the same joint. Their distinct physical projections each stay constant. | Uniqueness of a projected limit rules out extension. [Joint proof §4](../research/independent_audits/tip_native_full_W_ideal_circle_pointwise_extension_20261109.md). |
| Proper target path under the ordinary $W\to V^0$ immersion | Use the same positive-height strip path in two distinct source tiles with one parent. Verify that both tails meet original ideal sides in both source tiles and in the parent. | At least two proper restrictions for those representatives. KKL's marked restriction also requires the specified subordination and refinement. [Two-channel construction](../research/independent_audits/tip_native_KL_two_proper_restrictions_and_KKL_marking_gate_20261109.md). |

**L4. Literal nine-generator words (open).** For each of the 88 original
finite-side instances one needs a path from the common fine basepoint, its
prescribed KL connector, a separately fixed rooted reference homotopy class,
and oriented intersections against the nine physical cuts. Reduce their
ordered crossing word and compare with an independent representative.
Changing the rooted reference by the $m$-th power of the root meridian
right-multiplies the word by $b_{00}^{-m}$, while preserving the
root-membership decision. The classification of eight zero-shift mates and
80 nonroot rows therefore supplies no unique literal connector word. The
archive records zero of 88 such words. [Source data, gauge and missing certificates](../research/independent_audits/issue62_connector_words_20261116/NOTE.md).

## End components and protected planar carriers

### P2.1. Words to connected components (written, one scale)

Let $P$ be a closed Jordan disk, and $Q_0,Q_1\subset P$ disjoint closed Jordan pullbacks. The chosen iterate maps each $Q_a$ homeomorphically onto $P$ by a degree-one branch, with inverse $\phi_a$. Verify that the nondegenerate full terminal root $K_0$ lies in $\operatorname{int}P\setminus(Q_0\cup Q_1)$. For the assertion that all fibers lie in $J(f)$, also verify $K(f)=J(f)$ (D3 at the tip). Map a finite word $w$ to $\phi_w(K_0)$. Map an infinite word to the nested intersection of its closed cylinders. Compactness gives a continuum. Distinct addresses separate at a clopen cylinder or an isolated root address. Eventual agreement on each prefix gives closed graph and continuity of the projection from points to addresses. Thus the component quotient realizes the address space. The inverse homeomorphism commutes with these intersections, so symbol deletion agrees with the actual iterate off the root. [Compactification, component quotient and exact partial shift](../papers/paper2_rooted_end_compactification/main_v2.tex).

### P2.2. Phase clock to source time (written when geometrically realized)

A shallow branch has time $q$. Selecting two deep pullbacks from KL Lemma 2.1 gives time $\tau=nq$. The terminal root arrow is $K_0\mapsto f^{\tau\bmod p}(K_0)$. Its derivation uses $f^p(K_0)=K_0$. Disjoint nonzero phases prevent an unmarked return to the base unless $p\mid\tau$. Physical branch disjointness and containment of the root in the gap must be checked for the selected pieces. At the tip L3 supplies two local packages. A continuous cross-scale map on all ends still requires the selected transition, transported access chains, sheets and compatible contact incidence. [Clock lemma](../Paper2Phase.lean), [source and deep-branch hypotheses](../research/independent_audits/paper2_decorations_source_realization_20261105.md).

### P3.1. Closure identities to planar fill (written on compacta)

For compact $C\subset\mathbb C$, the exterior of a disk containing $C$ belongs to one unbounded complementary component. Any unbounded component meets that exterior. Fill $C$ by taking the complement of this unique component. It is compact, contains $C$, is monotone by nesting of unbounded components, and applying fill again leaves it fixed. These facts prove absorption and order independence for finite packets of compacta. An instantiation of the Lean operator on all subsets needs a separately justified domain or extension. [Kernel](weighted/ProtectedCarrierLogic.lean), [planar definition and proof](../papers/paper3_protected_carriers/extracted/A_intro/preliminaries.tex), [fixed-packet audit](../papers/paper3_protected_carriers/extracted/E_packets/audit.tex).

### P3.2. Routing to a protected connector (written under a fixed forbidden inventory)

Exhibit simultaneous disjoint landing arcs with singleton contact to every required atom in **one component** of the physical free domain. Shorten these ports, use the one-ended slit lemma to retain connectivity, and join their interior endpoints by a finite embedded tree avoiding the fixed collars and obstacles. Conversely, removing the atoms from an admissible routing leaves its tree and half-open ports connected in that component. This tests existence in a specified plane configuration. A graph drawing by itself supplies neither the landing arcs nor their collar clearance. [Free-component theorem](../papers/paper3_protected_carriers/extracted/D_criterion/criterion.tex), [ribbon realization and crosscut order](../papers/paper3_protected_carriers/extracted/C_certificates/certificates.tex).

### P3.3. Rank ledger to a separation count (written under finiteness)

For pairwise disjoint full plane continua $A_i$ attached to a compact connected $C$, put $B_i=C\cup A_1\cup\cdots\cup A_i$ and $T_i=C\cap A_i\ne\varnothing$. Compact-pair Čech Mayer–Vietoris gives a short exact sequence from reduced degree-zero cohomology of $T_i$ into degree-one cohomology of $B_i$ and onto the kernel of the cohomology restriction induced by $T_i\hookrightarrow B_{i-1}$. The latter restriction is surjective. Alexander duality identifies degree-one rank with bounded complementary components $\sigma$. Assume the complements of $C$ and each $T_i$ have finitely many components and let $c_i$ be the finite number of connected components of $T_i$. The two sequences then give $\sigma(B_i)=\sigma(B_{i-1})+c_i-1-\sigma(T_i)$. To specialize the rational Lean rank proof, realize the two sequences over the same coefficient field and prove the component and rank identifications for these compacta. [Abstract rank lemma](weighted/AttachmentDefectLedger.lean), [geometric sequences and exact assumptions](../papers/paper3_protected_carriers/extracted/G_separation/separation_budget.tex).

### P3.4. Finite carriers to a limit (conditional)

Supply a decreasing sequence of nonempty compact full continua and fixed disjoint full atoms, with every trace nonempty and connected at every stage. Compact nested intersection preserves each trace. The complement of the limiting connector is the increasing union of connected complements containing infinity. Apply the connected-trace attachment theorem. Fixed obstacle avoidance and relative-collar clearance give protected access under the source theorem's extra hypotheses. Ordinary Hausdorff convergence can create a disconnected trace and a new hole. Construction of such decreasing envelopes for the required dynamical stages remains open. [Nested-limit theorem and explicit counterexample](../papers/paper3_protected_carriers/extracted/G_separation/separation_budget.tex).


To reproduce representative exact inputs from the repository root, run

```sh
python3 research/independent_audits/verify_period27_misiurewicz_tip.py --check-manifest
python3 research/independent_audits/verify_tip_complex_domains.py --check-manifest
python3 research/independent_audits/verify_tip_levin_composition_escape.py --check-manifest
python3 research/independent_audits/verify_tip_native_full_W_ideal_circle_types.py --check-manifest
python3 research/independent_audits/issue62_connector_words_20261116/verify_connector_words.py --check-manifest
```

Each command checks its finite input. The cited covering, landing,
uniformization and compactness arguments supply the separate mathematical
implications. The universal same-carrier H1–H4 construction remains open.
