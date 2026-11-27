---
ledger: NOV26_OPEN_3P_MODULUS
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; Lean proof development and independent AI scope review
human_review: none
---

<a id="uniform-three-return-collar-20261127"></a>

# Uniform selected three-return collars

Ledger statement being addressed:

> Uniform physical three-return modulus: Two strict Rouche margins do not bound all arbitrarily shrunk 3p collars by one universal physical modulus (F04).

## Claim

This contribution constructs a canonical collar for the actual normalized three-return, with a fixed outer disk of radius 1/6 and a source containment radius of 3/20. The new step is simultaneous control of the full intermediate phase domains, so that no unquantified shrinking is needed. The final all-period realization theorem is compiled: for every integer p>=3, it constructs an actual selected quadratic parameter with a proper holomorphic physical restriction, exact signed fibers, a contractible source, a genuine physical ring domain, a trapped critical orbit, and a uniform physical Dirichlet-energy bound. The entire closed target and all three source phases lie inside an actual proper degree-two ambient p-return source, which lies inside the archive's original p-return component. The exact finite cases p=3,...,16 and analytic tail p>=17 supply all estimates.

## Evidence

The normalization is F(z)=f_c^p(d*z)/d with d=f_c^p(0)>0, outer radius 1/6 and inner radius 3/20. The source W is the connected component containing zero of the complete inverse image of the outer disk under F^3. This selects W from the actual polynomial rather than supplying a domain or a degree as input.

The strongest compiled all-period statement is:

```lean
UniformThreeReturnRenormalization.exists_uniform_three_return
    (p : Nat) (hp : 3 <= p) :
  Exists fun c : Real =>
    UniformThreeReturnRenormalization.PhysicalRenormalization c p
```

Its `collar : UniformCollar c p` field contains proved properties of the literal domains just defined. These include the physical reciprocal-capacity bound, exact physical fiber cardinality, source contraction, full closure, and an exact count of two complementary components for the open connected physical collar. The separate `selected_two_sheet_cover` theorem gives actual `Fin 2` evenly covered neighborhoods away from the critical value. The final record also includes properness and global complex differentiability of the literal physical iterate, contractibility in the physical coordinate, physical phase disjointness, ambient inclusion, and trapping of every physical critical iterate. Its sole input is p>=3; no parameter, domain, degree, modulus, or phase estimate is assumed in the existence theorem.

In physical coordinates, put U=D(0,d/6), let W be the central component of (f_c^(3p))^(-1)(U), and let A be U minus closure(W). The theorem gives closure(W) contained strictly in D(0,3*d/20), so the strict physical gap is d/60. The actual map W -> U is proper and holomorphic. The fiber over f_c^(3p)(0) has cardinality one; every other fiber in U has cardinality two. The physical sets W, f_c^p(W), and f_c^(2p)(W) are pairwise disjoint. The collar A is open and connected and has exactly two complementary components.

`ThreeReturnEstimates.lean` proves for every actual signed tip constructed by PR #238, for p >= 17:

- the whole closed band 3/20 <= |z| <= 1/6 maps outside the target by a strict additional margin 1/500;
- throughout the whole outer disk, |F(z)-1| < 51/1000 and |F^2(z)-(1-kappa)| < 19/100;
- all three phase images remain in the actual approximation disk of radius 23/20;
- F^3(0) lies inside the same fixed target disk.

`ThreeReturnAnnulus.lean` constructs a global Lipschitz potential at every physical scale d>0, zero on any inner plate contained in the closed disk of radius 3*d/20 and one outside the disk of radius d/6. Its actual planar Dirichlet energy is at most 19*pi < 60, so the reciprocal Lipschitz variational capacity exceeds 1/60. The integral uses the real Frechet derivative and planar Lebesgue measure. This is not an asserted identification with a uniformizing-annulus modulus.

`ThreeReturnDomain.lean` proves that the whole canonical component has compact closure strictly inside the inner barrier; the restriction is proper in the literal subspace topologies and covers the entire fixed target disk. It also proves invariance under z -> -z.

`ThreeReturnDegree.lean` proves F^3(z)=F^3(w) if and only if z=w or z=-w on the complete outer disk, and for the analytic tail proves that the actual complex derivative vanishes there exactly at zero. Its final theorems identify the critical fiber as {0}, every other fiber as {z,-z} with distinct points, and the corresponding exact set cardinalities. These are statements about the actual polynomial values, not assigned degree labels.

`FiniteThreeReturnCertificates.lean` independently kernel-checks the new fixed-radius integer inequalities for all fourteen archived parameter boxes p=3,...,16. Its certificate includes every intermediate factor in the complete three-return divided difference. `FiniteThreeReturnCollars.lean` now proves its real and complex soundness: actual parameter existence, the signed critical relation, the full annular exclusion with the same 1/500 margin, the exact signed collision relation on the full outer disk, and strict fixed phase enclosures. Thus both the finite cases and the analytic tail supply the same raw hypotheses of the canonical-domain construction.

`ThreeReturnCovering.lean` upgrades this census to a literal two-sheet covering after deleting the critical value. It constructs local sheets in open half-planes from the signed collision theorem, and uses properness to produce evenly covered neighborhoods whose fiber set is `Fin 2`.

`ThreeReturnCollar.lean` now assembles these results into `CanonicalCollar c p`. The theorem `actual_canonical_collar` supplies every field for every `ActualTip p c` with p >= 17, and `exists_actual_canonical_collar` supplies such an actual parameter for every such p. The physical domain is proved equal to the component containing zero of the complete physical f_c^(3p) pullback of D(0,d/6). Its actual closure is strictly inside D(0,3*d/20), and the capacity and reciprocal-capacity bounds apply to this closure. The generic assembly takes only the orbit scale, critical-value inequality, boundary inequality and actual collision relation, permitting an independent finite-certificate input.

`ThreeReturnPhysical.lean` proves the image and exact fibers of the literal physical f_c^(3p) map, the strict physical gap d/60, and pairwise disjointness of the three phase domains. `FiniteFirstReturnCertificates.lean` supplies two additional kernel-checked finite certificates: the enclosing p-return has a strict barrier on radius 23/20 and no extra signed sheets there, and the physical enclosing target disk lies inside the archive's original p-return target.

`ThreeReturnContraction.lean` proves that the entire selected source is contractible. It lifts a radial contraction of the punctured target through the actual covering. Closedness and the singleton critical fiber extend that lift continuously over the critical point and the final contraction time. The generic theorem takes the same raw boundary and collision hypotheses as the collar construction, so it applies to the finite cases as well as the analytic tail.

`ThreeReturnFullness.lean` proves that the chosen source closure is full, without replacing it by a different hull. The closed central pullback component is identified with the closure of the open source; the maximum modulus principle excludes bounded complementary components. A radial clamp proves connectedness of the physical collar. Its two actual complementary components are identified and counted: their set has cardinality exactly two. The physical collar is explicitly proved open and connected.

`ThreeReturnParent.lean` constructs a proper degree-two ambient p-return component with normalized target radius 23/20. Exact fiber exhaustion puts the whole closed three-return target disk and all three source phases inside this ambient source. After scaling, this ambient component lies inside the archive's original p-return component, since its actual target disk is contained in the original target. The exceptional original radius 1/4 at p=3 is preserved; the other original target radii are 2^(-p). `FiniteFirstReturnBounds.lean` proves the complete finite certificate soundness, including the strict scale comparison and strict phase bounds required by this construction. `ThreeReturnParentTopology.lean` proves contractibility of this actual ambient source in both normalized and physical coordinates.

`ThreeReturnRealization.lean` proves properness for the literal physical subspace map, global holomorphy of f_c^(3p), and physical transport of the source contraction and all phase images. If H=F^3 and a=H(0), the signed relation gives H(a)=-a and H(-a)=-a. Exact fiber exhaustion puts both a and -a inside the chosen source, so every critical iterate stays there and H^(n+2)(0)=-a for every n. `UniformThreeReturnRenormalization.lean` assembles the finite and analytic-tail inputs into the final theorem above.

### Exact certificate mechanism

The finite scale is S=2^512. Write d in [Dlo/S,Dhi/S], let A3lo be the certified absolute lower quadratic coefficient of the 3p iterate, X3hi the absolute upper critical value, and T3 its complete nonlinear remainder bound on physical radius Dhi/(6*S). The new integer inequality

```text
135*A3lo*Dlo^2 > 6000*S^2*(X3hi+T3) + 1012*S^2*Dlo
```

implies the entire-band escape margin 1/500. Every intermediate time j=1,...,3p-1 has deviation_j < absLo(x_j), so no factor of the complete even divided difference can vanish. The ambient p-return uses the analogous exact inequality with coefficients 529, 900 and 400, proving an additional circle escape margin 1/10. The physical comparison with the original p-return target is checked directly as 23*Dhi*RpDen < 20*S. This keeps the exceptional p=3 value honest: the convenient tail estimate d<=12/4^p is false there and is not used.

### Validation and reproduction

All eighteen new Lean files have compiled locally with pinned Lean 4.32.0. They register 146 public theorems, alongside definitions and private proof helpers. The full root project built successfully (89 jobs), and the root transitive-axiom audit passed for 44 modules and 2,222 declarations. The non-draft contribution checker passes. The existing CI performs the full weighted build and audits every weighted declaration at the pull-request head; its final result is reported in the PR.

From the repository root:

```sh
lake build
python code/verify_lean_coverage.py --audit root
python code/contribute.py check --base origin/main --pr-title '[NOV26_OPEN_3P_MODULUS] uniform canonical physical three-return collars'
```

From formalization/weighted:

```sh
lake build
```

Then from the repository root:

```sh
python code/verify_lean_coverage.py --audit weighted
```

The existing source scan rejects proof escapes, and the transitive audit permits only the repository's existing foundational axioms propext, Classical.choice and Quot.sound. No new axiom, proof placeholder, workflow modification, or status-record change is introduced.

## Dependencies

- NOV26_TIP_THEOREM and the actual finite and all-period primitive-tip estimates cited by research/tip_family_theorem/AUDIT.md, finding F04.
- Existing exact real interval and complex remainder infrastructure in the repository.
- PR #238, now merged into main, supplies the independent analytic-tail actual-parameter construction and complete p-return divided difference. Its crossing-curve result is not this contribution's claim. This branch has been synchronized with that merged main revision.

## Boundary

The proposed result remains **partial** for the ledger row for mathematical reasons, independently of draft or review status. The uniform bound concerns the fixed selected collar, not every arbitrarily shrunken collar. Its reciprocal-capacity invariant is defined in the extended nonnegative reals; capacity positivity and finiteness of that reciprocal have not been formalized. No equality or one-sided comparison with classical conformal modulus or the standard extremal length of all joining curves is asserted. Such a one-sided comparison would suffice for a classical lower modulus bound; a full uniformization theorem is not logically necessary.

Canonical here means that the disks and pullback components are fixed once the actual parameter is selected. It does not mean a globally unique parameter, a maximal collar, or an intrinsic period-only Wave width. The analytic tail consists of the actual signed tips constructed in PR #238 in its certified broad near-minus-two and narrow-coefficient chart. Identification with the archive's narrower unique signed kneading chart, in particular its 14*4^(-p)<c+2<16*4^(-p) bounds, has not been formalized. Inclusion in the original p-return component is proved for the actual same parameter; equality of ambient components is not claimed.

The result is uniform over integer periods at one actual quadratic level; it does not automatically transfer to iterated renormalizations of general analytic germs. No minimal original f-period, straightening theorem, or identification of the entire filled Julia set with an interval is asserted. The explicit derivative-zero census in ThreeReturnDegree is an analytic-tail theorem; the all-period statements use the exact signed fibers and punctured covering. No canonical KKL marking, Wave width, MLC, or H1-H4 conclusion is claimed.

## Attribution

The existing archive supplies the tip normalization, coefficient enclosures, and strict outer Rouché margins. This work targets the additional uniform inner containment and simultaneous phase control, not a repetition of those estimates. The contribution uses the repository's CC0 terms.
