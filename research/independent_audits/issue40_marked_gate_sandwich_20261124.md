# Issue #40 — finite-host marked-gate sandwich (2026-11-24)

Companion to issue40_monotone_model_prime_end_bridge_20261124.md. This note advances its remaining marked-path comparison by using the *interval assertion* of KKL Proposition 6.5, rather than assuming the physical immersion extends at every old access. It is a theorem under specified native identification hypotheses, not an unconditional resolution of #40.

## 1. Hypotheses and claim

Use the setting and transfer maps m_A,m_B of the companion Theorem 1 for saturated lifts A⊂B of nondegenerate full locally connected dendrites A_0⊂B_0 in the plane model. Assume B has empty interior, B_0\A_0 has finitely many connected components, and the original finite marking on C_A is precisely the lift of a marking on C_{A_0} whose cuts have singleton m_A-fibers. We work with actual inclusions of complementary collars (or immersions identified with such inclusions in a neighborhood of the compacta). No global properness of that immersion is assumed.

For the proper-path interval pullback, use the two source assertions of KKL Prop. 6.5 (arXiv:2606.27272v1): it is a connected interval, and consists of the proper old boundary preimages together with the complete contours of attached components meeting the specified old open or closed interval. In particular these are not ordinary preimages of sets under a holomorphic covering. The covering f and its boundary map p are separate.

**Claim.** There is a continuous cyclic-order-preserving monotone collapse r_0:C_{B_0}→C_{A_0} given by the full model attachment contours. For every original open or closed marked interval I=m_A^{-1}(I_0), the complete physical proper-path pullback, *using the assertions of Prop. 6.5*, satisfies

    iota^* I = m_B^{-1}(r_0^{-1}(I_0)).                     (1)

This establishes equality on the finite marked interval algebra; it is not asserted on arbitrary unmarked subarcs. It does not require singleton fibers at interior attachment hosts. The source's Prop. 6.5 is an input to the proof, not independently derived here from the maximal-set definition of Appendix A.3.2.

## 2. Model contour collapse

Exteriorize A_0 to the unit circle. For each component X_0 of B_0\A_0, its exteriorized closure meets that circle at one host angle e (the connectedness and analytic-uniqueness argument in §4 of the companion note). Group the finitely many components at each host. In the exteriorized obstacle L_0 the disk is joined to the corresponding compact groups Y_e, each meeting the disk exactly at e. These groups are mutually disjoint. All are full and locally connected: for an individual component, the exteriorizing coordinate extends to the unique root by the unique host limit; the extension is a homeomorphism of the compact component closure to its exteriorized closure. A finite union of these continua at a common root remains locally connected. Fullness follows from fullness and empty exterior interior of the combined obstacle, as in the companion note.

Away from the finite host angles the circle is a smooth boundary arc of the exteriorized obstacle. Each such open arc has a continuous one-to-one conformal boundary identification with an open arc of the new prime-end circle (local analytic reflection). Their cyclic order is preserved: the inclusion between complementary disks near infinity has positive degree one, and disjoint collar arcs preserve cyclic order. More explicitly, one can use radial test arcs from regular circle points to a common enclosing Jordan curve, chosen in the exterior and in cyclic order, so their prime-end order cannot interlace differently.

The closed gaps between the regular arcs are exactly the contours of the groups Y_e, including the two extreme gates over e. To see the absence of other boundary pieces, the landing map in the exteriorized coordinate is continuous since L_0 is locally connected. The landing image of the closed gap between two regular arcs at e is connected, contains e, and cannot contain another regular boundary arc (each regular point has its unique access on that arc). It therefore stays in the group at e: any other group is disjoint, separated from it by regular arcs. Conversely every source end landing in the group belongs to its gap; it cannot belong to a regular arc or a distinct group. This also handles the single-host case by treating the complementary regular arc as a punctured circle.

Collapse each such gap to e and identify each intervening regular arc with its original old arc. This gives the continuous monotone degree-one r_0. An equivalent characterization is the landing map in exteriorized coordinates followed by the continuous map that fixes the unit circle and sends each attached group to its single host. In particular an old source point whose model landing lies in A_0 has old limiting angle given by r_0. This is a contour code, not an extension of the model inclusion on the attached material.

## 3. Outer containment from the actual component census

Write R=r_0 m_B, a continuous monotone map C_B→C_{A_0}. For any original marked open or closed I_0, put J=R^{-1}(I_0). It is respectively an open or closed connected interval, with the whole-circle and punctured-circle cases retained. If I_0 is punctured at a host, J is the complement of the whole closed fiber over that host, not just the complement of a selected gate.

The physical components of B\A correspond bijectively to model components by monotonicity and saturation. For each component, its old host angles belong entirely to m_A^{-1}(e), where e is the model host. Each physical source contour belonging to that component is contained in the inverse image of the corresponding full model contour gap, by the impression formula in the companion Theorem 1; the same holds for the root gates at the ends of that contour. Thus every such contour included by Prop. 6.5 for I lies in J. This holds even if several physical internal accesses project to the same host, and whether I includes or excludes a marked endpoint.

For the old-boundary part of the union, if a source prime end maps properly under the physical inclusion to an old angle a, the model exterior-coordinate identity and Theorem 1 imply R(beta)=m_A(a). (A source end with model landing outside A_0 cannot have a proper old boundary image.) Consequently the proper old inverse images of I also lie in J.

By the union assertion of Prop. 6.5,

    iota^* I ⊂ J.                                           (2)

It is important that the containment concerns entire component contours, not just their physical landing roots. In particular it would not follow solely from a matching of the distinct physical graph edge names.

## 4. Reverse containment by the two extreme gates

Exteriorize the *physical* A to the disk. For each added component X, the closure of its exteriorized material meets the unit circle only inside the physical fiber m_A^{-1}(e) over its model host e. This follows from the actual old exterior coordinate identity in the companion note. There are finitely many host fibers, disjoint compact arcs or points, because there are finitely many components. All exteriorized material is bounded. Away from those compact fibers there is therefore a neighborhood of each point of the unit circle containing no attached material. In that neighborhood the source boundary is a regular analytic circle arc. Local analytic reflection in the two uniformizations gives a proper one-to-one old-boundary chart. This step uses absence of attached material near the arc, not local connectivity of A.

Take an original cut c_0. Its physical old fiber is a single angle c. If c_0 is not a host, this proper chart exists across c. If c_0 is a host, the host fiber is the singleton c; since the other finitely many host fibers are separated from c, there is a regular open arc on **each** side of c, ending at c, on which the physical inclusion is proper. The two lifted arcs in C_B approach the two extreme gates of R^{-1}(c_0). Here is why there is no extra hidden interval between such a limit and the extreme gate: on the regular arcs, R equals the old m_A coordinate, approaches c_0 from the respective side, and is nondecreasing in cyclic coordinates. As R is a continuous monotone surjection, limits of inverse images of points tending monotonically to c_0 from either side are precisely the two endpoints of its entire closed fiber. The two regular arcs may approach a common gate when the fiber is degenerate.

Now let I_0 be a proper nonempty open marked multi-interval. The two inward regular arcs at its boundary cuts have actual proper old images in I. Their source arcs belong to iota^*I by Prop. 6.5, and have points arbitrarily near the two ends of J, from within J. Since iota^*I is an interval contained in J by (2), it contains all of J. This proves (1) in the open case. If I_0 is a punctured circle, use its two ordered sides at the omitted cut; J is an open interval, and the same argument works. No assertion that a punctured circle equals a closed full circle is used.

For the closure of an interval with distinct boundary cuts, J also includes the complete two endpoint fibers. The *outer* extreme gates of these fibers have a continuous old boundary image equal to the corresponding old marked cut. Indeed their model landing is at the old root, all physical old cluster angles lie in the singleton fiber of that cut, and properness on the compactified collar gives no other limit. Thus both extreme gates belong to the proper old boundary inverse image of the closed I. Alternatively their inclusion is part of the complete endpoint-contour rule of Prop. 6.5. By connectedness of the pullback and (2), the entire closed J is included. For the full circle, apply the open case to each open atom and the closed case to each closure, and use monotonicity of the source pullback to include the union, which is the entire source circle. There are at least two distinct cuts in the application here. This proves the claim, including all endpoint births. Notice that local properness is established only on the necessary inward arcs and extreme gates; no global identification of all old ideal ends has been presumed.

In this proof the comparison with model contours uses Prop. 6.5's meaning of a component meeting a marked interval at its attachment access(es). If instead that proposition is intended as a planar-point incidence rule with no access specification, it is ambiguous at a marked point having more than one access. In that reading the source must be clarified before applying (1); a mere assertion of one common planar root does not identify a boundary interval.

## 5. The dynamical marked identity

With the actual covering square of the companion Theorem 3, (1) gives the following identity of *sets* for all these marked I:

    F_* I = m_A^{-1}(p_0 r_0^{-1}(I_0)).

To justify equality, not just projection, note that m_A p=p_0 m_B and p is a positive degree-d covering. For every model b, p maps the entire fiber m_B^{-1}(b) **onto** m_A^{-1}(p_0(b)): the d model preimages of a target point partition the d actual preimages of each physical point in its fiber, each contributing exactly one. More explicitly, the monotone lifts and the positive degree give ordered fibers, and the d disjoint physical inverse-image arcs of the target fiber map onto it, one arc in each model-preimage fiber. For a singleton target fiber the argument reduces to d points and monotonicity; in general apply the continuous nondecreasing lifts at the endpoints of the target fiber to get the same conclusion. Thus every model image of a saturated set is realized with its entire physical fiber. This step is not a general property of semiconjugacies of arbitrary maps; the positive covering and degree equality are used.

As a consequence the combinatorial lengths, proper/full/punctured status, and closed endpoint contributions agree with the model exactly, at every iterate whose domain is in the original marked algebra. It is no longer necessary to assume a pointwise boundary extension of the actual immersion at interior wild hosts.

## 6. Native status and residual checks

For KKL §2.5's saturated carrier model and §6.1's actual pullback, the hypothesis of finitely many model extra components follows **if** the single planar attachment assertion of Prop. 6.8 is available for the actual T,T': all model component closures then meet the same model root. The Kiwi model has finite valence (finite external-angle classes), and distinct components rooted at that point lie in distinct branches of the dendrite with that point removed. This implication does not require that common root to be preperiodic. The argument also allows multiple finite host angles.

Remaining source-specific checks before an unconditional claim:

1. Verify the exact canonical little Julia sets and full tree of the pseudo-ql germ are the saturated lifts of the specified model sets; verify the marking is the original side marking over singleton model cuts. See the companion §3, including rational-ray characterization and forward invariance of the finite vertex contact sets. The theorem is not about arbitrary sets projecting onto the tree.
2. Verify Prop. 6.5 uses access-sensitive incidence, not a planar-root convention, and that its connected-interval assertion holds for all the closed inputs used here. This theorem deliberately takes that proposition as an input; it is not an independent proof of its underlying maximal proper-path definition for every wild set. For the closed extreme gate, proper limiting at that gate is the pointwise compactified-collar assertion; if the source definition of properness requires more than that (a whole relatively open neighborhood), use the complete endpoint-contour rule instead and verify the gate inclusion there.
3. Finish the model graph-side trace and the small-Julia-side nonreturn proof for the exact marked vertices. These are model-level dynamical checks now, not a need for a global physical prime-end homeomorphism. No modulus/width estimate transfers under this topological argument alone.

This is a written conditional analytic proof and a marked identity reduction, not a new CI result or external peer review. It should not be used to close #40 until the hypotheses and source semantics above have been independently authenticated.
