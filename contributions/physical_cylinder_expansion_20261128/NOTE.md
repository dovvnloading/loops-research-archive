---
ledger: NOV26_OPEN_SUBSECTOR
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; Lean proof development and independent mathematical scope review
human_review: none
---

<a id="physical-cylinder-expansion-20261128"></a>

# Uniform physical angular expansion and precritical mesh

## Claim

For every integer period \(p\ge17\) and every actual selected signed-tip parameter \(c\), the literal return
\[
\Phi=f_c^{3p},\qquad f_c(z)=z^2+c
\]
expands the explicit physical cosine-coordinate distance by at least \(30/19\) on each complete real branch of its orbit-defined central invariant interval. The constants are independent of both the period and the subsequent cylinder depth.

Write
\[
d=f_c^p(0)>0,\quad
F(z)=f_c^p(dz)/d,\quad H=F^3,\quad t=-H(0),\quad r=dt.
\]
The actual critical relation gives
\[
r=f_c^{6p}(0)=-f_c^{3p}(0)>0,\qquad K_0=[-r,r].
\]
The carrier equality, endpoint values, and invariance are proved in Lean. Here \(K_0\) denotes this specific real orbit interval; the new proof does not assert an additional identification with a complex filled set.

Define directly in the original dynamical plane
\[
\theta_c(z)=\arccos\!\left(-\frac{\operatorname{Re}z}{f_c^{6p}(0)}\right).
\]
For any \(z,w\in K_0\) lying on the same closed side of the actual critical point,
\[
\boxed{\quad
\frac{30}{19}\,|\theta_c(z)-\theta_c(w)|
\le
|\theta_c(\Phi(z))-\theta_c(\Phi(w))|.
\quad}
\tag{1}
\]
This is the main quantitative statement. Its physical coordinate is fixed by the critical orbit; no straightening, metric, conjugacy, or expansion estimate is an input.

Every actual depth-\(n\) sign cylinder consequently has the pairwise diameter bound
\[
\boxed{\quad |z-w|\le r\pi(19/30)^n.\quad}
\tag{2}
\]
The itinerary is read from the signs of the literal iterates \(f_c^{3pj}(z)\), for every \(0\le j<n\). It is not an assigned symbolic transition system.

Moreover, every real subinterval \((u,v)\subset K_0\) whose length exceeds \(r\pi(19/30)^n\) contains an actual precritical point:
\[
\boxed{\quad
v-u>r\pi(19/30)^n
\ \Longrightarrow\
\exists j<n,\ \exists x\in(u,v),\ f_c^{3pj}(x)=0.
\quad}
\tag{3}
\]
The strict threshold and the strict time bound are retained in the Lean statement. The convention permits \(j=0\), so the witness may be the critical point itself.

**Validation:** all seven modules compile in the repository's Lean project at [proof commit b819caed22e4067df3dee2f26015df136190f235](https://github.com/dovvnloading/loops-research-archive/commit/b819caed22e4067df3dee2f26015df136190f235). The [weighted build and transitive dependency audit](https://github.com/dovvnloading/loops-research-archive/actions/runs/46134457837) passed, including every new declaration. The audit permits only `propext`, `Classical.choice`, and `Quot.sound`; no proof holes or new axioms are used. [Research validation](https://github.com/dovvnloading/loops-research-archive/actions/runs/46134457938), [contribution intake](https://github.com/dovvnloading/loops-research-archive/actions/runs/46134457919), and all other workflows also passed on that commit.

## Evidence

### The new actual-map estimate

The existing construction supplies \(117/1000\le t\le119/1000\). For every real pair in that entire central interval, the complete normalized p-return has an even divided difference
\[
F(x)-F(y)=(x^2-y^2)S(x,y).
\]
The archive's full-iterate secant estimate gives
\[
179/100\le -S(x,y)\le9/5
\]
on the larger normalization disk. Direct actual-orbit estimates give
\[
F([-t,t])\subset[97/100,1001/1000],\qquad
F^2([-t,t])\subset[-4/5,-17/25].
\]

The exact three-return factorization is
\[
H(x)-H(y)=(x^2-y^2)D_H(x,y),
\]
where
\[
D_H=(-S(x,y))(F(x)+F(y))
(-S(F(x),F(y)))
(-(F^2(x)+F^2(y)))
(-S(F^2(x),F^2(y))).
\]
Every factor has a proved positive lower bound. Thus
\[
\frac{9457574011}{625000000}
\le D_H(x,y)\le
\frac{1459458}{78125},
\]
and in particular
\[
\boxed{15\le D_H(x,y)\le19.}
\tag{4}
\]
The products use the complete high-degree polynomial returns, including diagonal secants. There is no Taylor truncation and no replacement of the actual dynamics by the limiting quadratic.

### From the native secants to the explicit angular metric

Set \(h(x)=-H(tx)/t\). Evenness of \(H\) makes the physical coordinate map \(x\mapsto-dtx\) an exact conjugacy to \(\Phi\). The signed critical relation gives \(h(0)=1\) and \(h(\pm1)=-1\).

For \(0\le x\le y\le1\), (4) gives
\[
15t(y^2-x^2)\le h(x)-h(y)\le19t(y^2-x^2).
\]
Put \(A=15t\), \(B=19t\). Taking the derivative of the actual secant inequality gives
\[
-h'(x)\ge2Ax.
\]
Applying the upper secant estimate at both actual endpoints gives
\[
1-h(x)\le Bx^2,\qquad 1+h(x)\le B(1-x^2).
\]
These two estimates control the endpoint singularities simultaneously:
\[
\sqrt{1-h(x)^2}\le Bx\sqrt{1-x^2}.
\]
Consequently the cosine-coordinate expansion factor is at least \(2A/B=30/19\). The formal proof uses monotonicity of
\[
x\longmapsto \arccos(h(x))+(2A/B)\arccos x
\]
on the whole closed positive branch. This includes its endpoints by continuity. Evenness gives the negative branch with the same constant.

Iteration along an arbitrary shared actual sign itinerary proves (2). Its contrapositive forces a sign disagreement before time \(n\). The intermediate value theorem for the literal polynomial iterate then places a zero strictly inside the original interval, proving (3).

### Lean declarations

| Module | Role |
|---|---|
| [ActualThreeReturnExpansion](../../formalization/weighted/ActualThreeReturnExpansion.lean) | Complete native factorization and the uniform bounds \(15\le D_H\le19\). |
| [AngularCylinderExpansion](../../formalization/weighted/AngularCylinderExpansion.lean) | Secants imply closed-branch angular expansion and all-depth cylinder contraction. |
| [ActualThreeReturnNormalization](../../formalization/weighted/ActualThreeReturnNormalization.lean) | Actual critical radius, endpoint relations, differentiability, evenness, and exact physical conjugacy. |
| [ActualThreeReturnCylinders](../../formalization/weighted/ActualThreeReturnCylinders.lean) | Physical itineraries and all-depth pair bounds for literal quadratic iterates. |
| [CylinderCriticalHit](../../formalization/weighted/CylinderCriticalHit.lean) | Interior precritical witness from the strict cylinder-size threshold. |
| [PhysicalCentralCarrier](../../formalization/weighted/PhysicalCentralCarrier.lean) | Exact orbit-interval identification, physical invariance, and main theorem (1). |
| [PhysicalCylinderEscape](../../formalization/weighted/PhysicalCylinderEscape.lean) | Main physical precritical mesh theorem (3) and unconditional parameter existence. |

The main native declarations are:

- PhysicalCentralCarrier.physical_angular_expansion;
- PhysicalCentralCarrier.physicalInterval_eq;
- ActualThreeReturnCylinders.physical_cylinder_pair_bound;
- PhysicalCylinderEscape.physical_precritical_mesh;
- PhysicalCylinderEscape.exists_uniform_physical_precritical_mesh.

### Advance over the archived result

[Theorem 6.1 of the maximal native-wave note](../../research/independent_audits/maximal_native_wave_20261123/NOTE.md) already proves eventual zero-edge contour escape, with a clock measured after an unspecified hybrid straightening. Its Theorem 6.2 already allows arbitrarily long delays for sufficiently small positive subarcs. Neither qualitative escape nor the impossibility of a size-independent clock is claimed as new here.

The new bound is one-step expansion in the explicit, orbit-normalized *physical* cosine coordinate, uniform in the unbounded period range. It supplies a period-independent size-to-time bound when physical length is measured relative to \(r\) and time is counted in three-returns. The original quadratic hitting time is \(3pj\). A topological conjugacy alone supplies no such explicit modulus; the proof obtains it directly from the actual polynomial.

The analytic principle converting quadratic secants to angular expansion is classical calculus. General expansion theory for critically preperiodic maps is also classical; for background see [Lyubich's dynamics text, section 27.1.2](https://www.math.stonybrook.edu/~mlyubich/book.pdf). Those background facts are not used as a substitute for the new quantitative native inequality. A search for prior work did not locate this specific estimate, but does not establish worldwide priority.

## Dependencies

The proof uses the existing actual signed-tip existence theorem, the actual normalized p-return and its exact secant factorization, the quantitative actual parameter and critical-orbit estimates, and the signed critical relation from the repository. The underlying declarations are in NearTwoTip, GlobalCrestEstimates, GlobalCrestSourceGates, QuadraticCrestDividedDifference, and ThreeReturnRealization.

Mathlib supplies real calculus, trigonometric inverse functions, continuity and the intermediate value theorem. No additional axiom is declared. The source registration and transitive dependency audit are part of the existing repository CI.

Local Lean is unavailable in this workspace. Reproduce with the repository's pinned Lean 4.32.0 project:

~~~sh
cd formalization/weighted
lake exe cache get
lake build ActualThreeReturnExpansion AngularCylinderExpansion \
  ActualThreeReturnNormalization ActualThreeReturnCylinders \
  CylinderCriticalHit PhysicalCentralCarrier PhysicalCylinderEscape
~~~

Then run the existing source and dependency checks:

~~~sh
python code/verify_lean_coverage.py
python code/verify_lean_coverage.py --audit weighted
python code/contribute.py check
~~~

## Boundary

This is a partial quantitative advance on NOV26_OPEN_SUBSECTOR, for the orbit-defined central real interval of the actual selected primitive family with \(p\ge17\).

The real precritical mesh is not itself a proof that the explicit contour action equals the native KKL immersion restriction on arbitrary finer subsectors. Marked prime-end transport, whole attachment-fiber transport for arbitrary Waves, retained descendants, and crest inheritance remain separate requirements. The full ledger obligation remains open.

The cylinder words here describe inverse branches of one actual three-return. They are not arbitrary nested tuning words. No assertion about arbitrary renormalization depth or NOV26_OPEN_DEPTH_GATES is made. The finite periods \(3\le p\le16\) are outside this contribution.

Closed branch cylinders may share precritical endpoints. The proof does not assert unique binary addresses at those endpoints, or a size-independent escape time for every positive subinterval. No MLC conclusion or ledger-status change is proposed.

## Attribution

The canonical family and its earlier physical parameter, orbit, and secant estimates belong to the archive and its prior contributors. This contribution develops the new complete three-return secant estimate, its explicit physical angular expansion, and the resulting physical precritical mesh. OpenAI GPT-6 Astra Pro performed the proof development and independent scope and mathematics checks; no human specialist review has occurred.
