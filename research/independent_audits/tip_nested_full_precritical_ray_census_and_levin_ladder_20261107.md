# A complete 1024-sheet precritical ray census and an exact 3/9 Levin access ladder

**Date:** 2026-11-07, Eastern time. **Status:** an analytically proved, finitely typed, **actual polynomial** theorem for the repository's nonattracting period-3/9 Misiurewicz tip. It establishes the complete precritical fiber over one repelling nine-cycle point, the exact source-domain memberships **1024 / 16 / 4**, its unique parameter-space branch transposition, **all 2048 ambient inverse-ray angles**, and a new complete **eight-ray two-scale Levin-angle table**. The latter is a *selected finite ray-access correspondence*, **not** the complete Kahn–Lyubich local-cover sheet/coset functor. No H1–H4, UPTCR, or MLC gate is closed; no global originality/priority claim is made. General orbit-portrait/Levin/covering mathematics is classical and explicitly attributed below.

## 1. Independent source spine and precise imported theorems

- The real quadratic `f_c(z)=z²+c` at the **exact** root `c_*` of `G(c)=P18(c)+P9(c)` in the source-certified `2^-128` rational bracket has critical preperiod **10**, eventual period **9**, and the nine-cycle is repelling; see [the Misiurewicz-tip certificate](period27_misiurewicz_tip_ray_access_20261106.md). It proves `P_j(c_*) != P10(c_*)` for every `0<=j<10` by signed dyadic interval separation.
- The **actual** `F3=f_c^3:V3(c)->U3` and `F9=f_c^9:V9(c)->U9`, with `U3=D(0,1/4)` and `U9=D(0,1/32)`, are proper degree-two polynomial-like maps, and `K9(c_*)⊂K3(c_*)`; the strict analytic domain margins persist for sufficiently small complex parameter perturbations. See [actual complex two-scale certificate](nonattracting_tip_complex_two_scale_20261106.md) and [ramified precritical pair](period9_tip_ramified_precritical_pair_20261107.md). **The little filled sets need not remain connected for perturbed parameters.**
- Milnor, [*Periodic Orbits, External Rays and the Mandelbrot Set*](https://archive.numdam.org/item/AST_2000__261__277_0/), **Lemma 2.7**: in the primitive orbit-portrait case (return permutation of rays is the identity), **at most two rays** land at each point of a periodic orbit. Here `r=1` follows from the presence of one return-fixed ray and orientation-preserving cyclic permutation on the finite ray landing set. This theorem gives *completeness*, not merely existence.
- Zakeri's [real Misiurewicz ray theorem](https://arxiv.org/abs/math/0210382), applied in the archive's exact tip certificate, gives two rays at the critical value and four at the critical point. The source's periodic orbit portrait supplies two named **repelling nine-cycle rays** at `Z_*=P10(c_*)` with angles `228/511` and `283/511`. Both are fixed by angle multiplication by `512=2^9`.
- Levin, [*Rays to Renormalizations*](https://arxiv.org/abs/2010.15386), **Theorems 1 and 3(b),(d),(e)**: given the verified `(p1),(p2)` hypotheses at the **one parameter `c_*`**, each `p=3,9` has a source-defined angle map `Pi_p` on ambient rays landing in `Kp`, satisfying `Pi_p(2^p theta)=2 Pi_p(theta)` and possessing a **continuous monotone degree-one extension**. Internal rays corresponding to different landing points cannot be the same ray. The degree is two, so the straightening rotation ambiguity is trivial. The [source-checked 3/9 angle note](levin_tip_p2_carathéodory_two_scale_20261106.md) gives `Pi3(114/511)=5/7`, `Pi3(397/511)=2/7`, and `Pi9(114/511)=Pi9(397/511)=0`.

**Source-name caution.** `Pi3` and `Pi9` are *Levin renormalization-ray maps*, not the physical `f^6` angle map, the entire external ray fibration, or Kahn's based localization cover. The new eight-ray table below is computed at `c_*`, where Levin's hypotheses are established. It is **not** silently asserted for nearby disconnected little Julia sets.

## 2. The complete primitive nine-cycle portrait: exactly two rays

Let `Z(c)` denote the analytic continuation of the repelling nine-periodic point `Z_*=P10(c_*)` from merged [PR #52](https://github.com/dovvnloading/loops-research-archive/pull/52), with multiplier `3<lambda_*<4` at the center. Define

\[
 t_-=\frac{228}{511},\qquad t_+=\frac{283}{511}.
\]

### Theorem 2.1 (complete period-nine orbit-ray portrait)

For all real `c` sufficiently close to `c_*`, the set of **all** ambient dynamical rays landing at `Z(c)` is exactly `{t_-,t_+}`. Every one of the nine points `f_c^j(Z(c))`, `0<=j<9`, also has exactly **two** landing rays, whose angles are

\[
 \boxed{\{2^j t_-,\ 2^j t_+\}\pmod1.}
 \tag{2.1}
\]

Thus the source's 18-angle table, formerly documented as **at least** 18 rays, is the **complete** period-nine orbit portrait, at the tip and throughout a sufficiently small real interval.

**Proof.** The two named period-nine rays land at the repelling point at `c_*`, and the classical repelling-periodic-ray stability theorem transports their landings to `Z(c)` for sufficiently close real parameters. Both angles satisfy `512t=t mod1`. The angular action induced by `f_c^9` on the finite, cyclically ordered set of all rays landing at a repelling periodic point is an orientation-preserving cyclic permutation. Since this permutation has at least one fixed point, its cyclic shift must be zero: *every* landing ray is fixed by `f_c^9`. We are in Milnor's primitive (`r=1`) case. His Lemma 2.7 gives valence at most two. Our two distinct rays attain the bound. The other eight orbit points are locally unramified image points of the same periodic orbit, and `f_c` maps the complete ray set bijectively around the repelling cycle, giving (2.1). `□`

No assumption of local connectivity for arbitrary nearby real Julia sets is required: **periodic rational rays at a repelling point land**, and the local portrait is stable. Every sufficiently close real `c` lies in `[-2,1/4]`, where the ambient filled Julia set is connected.

## 3. The 1024-sheet geometric fiber and its unique branch cycle

Let

\[
 H_c(z)=f_c^{10}(z)-Z(c),\qquad
 \mathscr P_c=H_c^{-1}(0).
 \tag{3.1}
\]

### Theorem 3.1 (global depth-ten precritical fiber, exact local braid)

At `c=c_*`, `H_c` has degree `1024`, has **exactly one multiple root**, namely `0` of multiplicity **two**, and therefore exactly `1023` distinct roots. The other `1022` roots are simple.

There is a complex parameter disk `D` about `c_*` such that:

1. for every `c∈D\{c_*}`, all `1024` roots of `H_c` are simple;
2. `1022` roots are individually holomorphic functions of `c` on the **whole disk**;
3. the remaining two form **exactly one simple square-root branch point**, with `s_±(c)^2=R(c)` and `R'(c_*)=-kappa`, `0.276<kappa<0.277` (merged [PR #53](https://github.com/dovvnloading/loops-research-archive/pull/53));
4. the full analytic root covering over `D\{c_*}` has monodromy **cycle type**

\[
 \boxed{(2)(1^{1022})}.\tag{3.2}
\]

After the two-fold ramified base change `c=c_*+u²`, **all 1024 root sheets admit holomorphic labels** in a disk in `u`.

**Proof.** For every `z`, the chain rule gives

\[
 (f_c^{10})'(z)=\prod_{j=0}^{9}2f_c^j(z).
\]

If `z∈\mathscr P_{c_*}` is a multiple root, then `f_{c_*}^j(z)=0` for some `0<=j<=9`. The target equation gives

\[
 P_{10-j}(c_*)=f_{c_*}^{10}(z)=Z_*=P_{10}(c_*).
\]

The tip has **minimal critical preperiod 10**, and its first ten critical orbit values `P_0,...,P_9` are all distinct from `P_10`. Thus `j=0`, `z=0`. At zero,

\[
 f_c^{10}(z)=f_c^9(c+z²),
\]

and the coefficient of `z²` at the tip is `(f_{c_*}^9)'(c_*)=A_9`, strictly between `-4.27` and `-4.26` by PR #53. So `0` is an **exact double root**, not higher. A degree-1024 polynomial with one double root and all others simple has exactly `1023` distinct zeros. Standard holomorphic implicit-function theory continues each of the other `1022` roots separately in a common small disk. The exact locally factored equation from PR #53 and its simple discriminant zero give a single transposition on the remaining two. Shrinking the parameter disk if needed excludes every other collision, proving (3.2) and the ramified analytic labels. `□`

**New independent exact check.** The bundled signed-dyadic verifier re-encloses every `P_j(c_*)`, `0<=j<=10`, and certifies

\[
 \boxed{\min_{0\le j<10}|P_j(c_*)-P_{10}(c_*)|>\frac1{2048}.}\tag{3.3}
\]

This strict quantitative bound makes the “only one multiple root” argument explicit instead of relying on an unverified preperiod label.

## 4. Why the *same physical inverse fiber* has 16 coarse but only 4 fine members

Write `p(c)=f_c^8(Z(c))`. The exact return identities from PR #53 give

\[
 f_c(p)=Z(c),\quad f_c(-p)=Z(c),\quad
 f_c^9(p)=f_c^9(-p)=p,\quad f_c^9(s_±)=-p.
 \tag{4.1}
\]

For all sufficiently close **complex** parameters, the four points `p,-p,s_+,s_-` belong to `K9(c)⊂K3(c)` (at the tip the last two coincide). The existing component/phase-domain proof applies even without nearby connectedness of the little filled sets.

### Lemma 4.1 (stage-selective degree principle)

Let `F=f^r:V→U` be a proper degree-two polynomial-like restriction with filled set `K_F`, and suppose distinct points `v_+,v_-∈K_F` satisfy `f(v_+)=f(v_-)=w`. For any `m>=1`,

\[
 \boxed{\#\{z∈K_F:f\circ F^m(z)=w\}
 =2^{m+1}\quad\text{counted with local multiplicity}.}
 \tag{4.2}
\]

**Proof.** For `z∈K_F`, invariance gives `F^m(z)∈K_F`; the equation `f(F^m(z))=w` is exactly `F^m(z)∈{v_+,v_-}`. Each of the two target points has **precisely `2^m` preimages counting multiplicity** in the central polynomial-like return, because `F` is proper degree two and `K_F=\bigcap_{j>=0}F^{-j}(V)` is completely invariant under `F` on the domain. Their inverse fibers are disjoint since `v_+≠v_-`, proving the claim. `□`

### Theorem 4.2 (actual nested 1024/16/4 fiber census)

For every sufficiently close parameter `c`, with multiplicity,

\[
 \boxed{\#\mathscr P_c=1024,\qquad
 \#(\mathscr P_c\cap K_3(c))=16,\qquad
 \#(\mathscr P_c\cap K_9(c))=4.}\tag{4.3}
\]

At `c=c_*`, the corresponding numbers of **distinct points** are `1023,15,3`; for `c≠c_*` sufficiently close they are `1024,16,4`. In particular the **same physical 10-step precritical set has exactly 12 coarse-stage-only points**, distinct from the four fine-stage members (at the tip, 12 coarse-only points distinct from the three fine members).

**Proof.** `f^{10}=f\circ f^9`. On `K3`, the physical nine-iterate is `F3^3`, and on `K9` it is `F9`. Since `f(w)=Z` has the **two distinct roots** `w=p,-p`, both of which lie in each filled set, Lemma 4.1 applied to `(r,m)=(3,3)` and `(9,1)` gives `2^(3+1)=16` and `2^(1+1)=4`. The ambient 10-step polynomial has degree `1024`. All these stage roots belong to the total fiber, whose **only** multiple root is the near-zero double point at the tip (Theorem 3.1). Since `0∈K9⊂K3`, subtracting one from each multiplicity total at `c_*` gives `1023,15,3` distinct roots; away from the tip every root is simple. Since `K9⊂K3`, the difference has exactly 12 distinct points in either case. `□`

This exact **4:1 coarse/fine inverse-fiber ratio** comes from the *actual different polynomial-like stage restrictions*, not a substitution of the physical `f^6` angle map or a synthetic groupoid. It is a finite realization of a geometric branching distinction relevant to cross-scale marking designs. It does **not** assert that the 16- and 4-point fibers constitute all KL `O/xi/eta` pseudo-piece accesses.

## 5. Every one of the 2048 angular inverse rays is accounted for

For `t∈{t_-,t_+}` and `k=0,...,1023`, define the **exact rational ambient angles**

\[
 \boxed{\theta_{t,k}=\frac{t+k}{1024}.}\tag{5.1}
\]

There are precisely **2048 distinct** such rational angles. At every sufficiently close **real** parameter (including `c_*`), the rays of all 2048 angles land at the roots of `H_c` and none of the roots admits any additional ambient landing ray.

**Proof.** By Theorem 2.1, the image ray at `t` is a ray landing at `Z(c)`, and the only rays landing there are `t_-,t_+`. Since the filled Julia set is connected for real `c∈[-2,1/4]`, the global Böttcher map is a conformal isomorphism on the entire escaping basin. Pull back a terminal segment of either landing ray under `f_c^{10}`. For every root `z` of `H_c` of local degree `m(z)`, exactly `m(z)` lifts of each target ray end at `z`; they are ordinary Böttcher rays with some angles among (5.1). Conversely, **any** ambient ray landing at such a root maps to one of the two rays at `Z(c)` and hence is among the 2048 angles. The sum of local multiplicities of `H_c` is `1024`, so the complete ray-access count is `2×1024=2048`. At the tip, the critical root `0` has **four** rays and each of the other 1022 roots has **two**; off the tip, all 1024 roots have **two** each. The stage counts (4.3) therefore represent **exactly 32 external-ray accesses into `K3` and 8 into `K9`** for every sufficiently close real `c`.

This is a **complete access census within the specified depth-ten repelling preimage fiber**, not a census of *all rays landing anywhere in `K3` or `K9`*. The analytic continuation of the roots exists on a complex parameter disk, but the full global Böttcher-ray statement is restricted to the connected-Julia **real** parameters; no global complex ray motion is inferred.

## 6. The complete eight-ray K9 census—and *new* precise Levin internal angles

The four fine preimages are `p,-p,s_+,s_-` off the tip; the complete corresponding **eight ambient angles** are as follows:

\[
\begin{aligned}
 p &: \{114/511,\ 397/511\},\\
 -p &: \{283/1022,\ 739/1022\},\\
 \{s_+,s_-\} &: \{a,b,d,e\},\\
 a&=116791/523264,\quad b=144841/523264,\\
 d&=378423/523264,\quad e=406473/523264.
\end{aligned}\tag{6.1}
\]

At the tip `s_+=s_-=0`, bearing all four rays. For real `c<c_*`, the pairings are `{a,e}` at `+sqrt(R)`, `{b,d}` at `-sqrt(R)`; for `c>c_*`, they are `{a,b}` at the upper imaginary point, `{d,e}` at the lower point (merged [PR #54](https://github.com/dovvnloading/loops-research-archive/pull/54)). Antipodality of the quadratic Böttcher coordinate gives the `-p` angles from the `p` angles, while the `p` rays come from the genuine period-nine orbit. All **eight** are distinct, belong to the set (5.1), and are **all** fine-stage rays by Theorems 4.2–5.1.

### Theorem 6.1 (exact source-defined two-scale Levin ray ladder at the tip)

At `c=c_*`, for these **eight genuine ambient rays**, the complete values of the actual Levin maps `Pi3` and `Pi9` are:

| Ambient ray angle (strict circular order) | Landing point | `Pi3` internal angle | `Pi9` internal angle |
| --- | --- | --- | --- |
| `114/511` | `p` | `5/7` | `0` |
| `a=116791/523264` | `0` | **`81/112`** | **`1/4`** |
| `b=144841/523264` | `0` | **`87/112`** | **`1/4`** |
| `283/1022` | `-p` | **`11/14`** | **`1/2`** |
| `739/1022` | `-p` | **`3/14`** | **`1/2`** |
| `d=378423/523264` | `0` | **`25/112`** | **`3/4`** |
| `e=406473/523264` | `0` | **`31/112`** | **`3/4`** |
| `397/511` | `p` | `2/7` | `0` |

In particular **`Pi3` distinguishes all eight** selected ambient accesses, while **`Pi9` identifies them in precisely four pairs**:

\[
\boxed{\begin{array}{ll}
\Pi_9^{-1}(0)\cap\mathcal A=\{114/511,397/511\},
& \Pi_9^{-1}(1/4)\cap\mathcal A=\{a,b\},\\
\Pi_9^{-1}(1/2)\cap\mathcal A=\{283/1022,739/1022\},
& \Pi_9^{-1}(3/4)\cap\mathcal A=\{d,e\}.
\end{array}}\tag{6.2}
\]

Here `A` is **only the eight-angle set (6.1)**. These are actual source-defined Levin maps, not custom circle maps.

**Proof.** The previous checked 18-angle enumeration and Levin monotone theorem give

\[
 \Pi_3(114/511)=5/7,\quad \Pi_3(397/511)=2/7,
 \quad \Pi_9(114/511)=\Pi_9(397/511)=0.
\]

The rays at `-p` are the **antipodal** rays of `p`: `283/1022` comes from `397/511`, while `739/1022` comes from `114/511`. Under `g3=f³` they map to the same rays as their respective `p` counterparts. Under internal doubling their angles must therefore be preimages of the same values, differing by either `0` or `1/2`. They **cannot be equal** to the `p` counterparts' internal angles: each internal ray has one landing point, whereas `p≠-p` and Levin's correspondence preserves the landing point in the straightening. Thus

\[
 \Pi_3(283/1022)=2/7+1/2=11/14,
 \quad\Pi_3(739/1022)=5/7+1/2=3/14.
\tag{6.3}
\]

The identical argument at fine scale, with `Pi9(p rays)=0`, gives `Pi9(-p rays)=1/2`.

Now use the actual `f9` ray images from the angle arithmetic:

\[
512a=512d=283/1022,\qquad512b=512e=739/1022\quad(\bmod1).
\tag{6.4}
\]

Levin's `Pi3` semiconjugacy applied three times gives

\[
8\Pi_3(a)=8\Pi_3(d)=11/14,
\quad8\Pi_3(b)=8\Pi_3(e)=3/14\quad(\bmod1).
\]

The source **degree-one monotone extension** and strict ambient cyclic order yield the *lifted* intervals

\[
\begin{split}
5/7&\le\widetilde\Pi_3(a)\le\widetilde\Pi_3(b)\le11/14,\\
17/14&\le\widetilde\Pi_3(d)\le\widetilde\Pi_3(e)\le9/7.
\end{split}\tag{6.5}
\]

In each interval there is **exactly one** solution of `8x = the required rational target mod 1` for each named angle. These solutions are `81/112`, `87/112`, `137/112` and `143/112`, i.e. the four values in the table modulo 1. This uniqueness is checked with exact `Fraction` arithmetic in the standalone verifier; it is also an immediate bounded-integer calculation. For `Pi9` the same monotone lift places `a,b` between the internal values `0` and `1/2` and `d,e` between `1/2` and `1`; semiconjugacy under `512` then yields the unique preimages `1/4` and `3/4`, respectively. All other table values were fixed before this step. `□`

**Dynamical consistency.** In the outer scale the critical quartet's internal angles are **four distinct preperiodic period-three angles** (`81,87,25,31` over `112`). In the fine scale they are identified in two pairs (`1/4,1/4,3/4,3/4`). The finite **two-scale quotient of this precisely delimited eight-ray set** therefore has a genuine, source-derived 2-to-1 pattern. It is not an established map between the *whole* internal straightening circles, and the extra `12` coarse-stage points have not been given their individual angular addresses in this note.

### Theorem 6.2 (complete **32-angle internal census**, with a forced finite bijection)

The period-three straightening's **entire** internal ray set over the *16-point* depth-ten central fiber is the following explicitly defined, 32-element set:

\[
\boxed{\mathcal A_3^{\mathrm{int}}=
\left\{\frac{q+k}{8}:q\in
\left\{\frac27,\frac57,\frac3{14},\frac{11}{14}\right\},
\ k=0,\ldots,7\right\}.}\tag{6.6}
\]

Each angle occurs **once**. The outer Levin map `Pi3` is a **bijection from the 32 ambient rays landing in** `K3\cap\mathscr P_{c_*}` **onto** `\mathcal A_3^{\mathrm{int}}`. The eight source-labelled rows of Theorem 6.1 are part of this 32-element bijection. The other **24 internal angle values** are completely listed in the machine-readable manifest, although their individual ambient source-angle labels are not yet identified in this work. By contrast, the *eight* ambient period-nine rays map exactly **two-to-one** under `Pi9` to the four internal angles `{0,1/4,1/2,3/4}`.

**Proof.** The two physical target points `p` and `-p` belong to `K3`. Theorem 6.1 determines **four distinct** internal rays landing there, with angles `5/7,2/7,3/14,11/14`. A standard polynomial-like straightening gives a genuine connected quadratic filled set on which the return `g3=f³` is conjugate to a degree-two polynomial. Every preimage under three iterations of `g3` of either target point is a member of the 16-point central fiber established in Theorem 4.2, and conversely. Pulling back each of the four internal rays three times gives **eight** internal ray angles `x` with `8x=q mod1`. The four target angles have disjoint inverse sets, so the result is **32 distinct internal angles**, precisely (6.6). Their rays land at the 16 central preimage points, with the critical double preimage at the tip accounted for by local degree.

Levin Theorems 1 and 3(c) establish that every one of these internal rays corresponds to **at least one ambient external ray sharing its landing point** in `K3`. Each such landing point lies in the physical equation `f^{10}(z)=Z_*`. By Theorem 5.1 there are **exactly 32 ambient rays** landing in that same stage-selected fiber. Since `Pi3` is a function, 32 different target values require at least 32 different source angles; equality forces **one and only one ambient ray for each internal angle**. Therefore `Pi3` is bijective on this selected finite set. The fine-stage statement is the exhaustive eight-angle table in Theorem 6.1. `□`

**Scope.** This does not make `Pi3` globally injective on all external-ray angles landing in `K3`, nor does it identify the remaining 24 ambient angles with KL pseudo-piece sides. It is a **complete, finite, source-defined internal-angle census** of one genuine polynomial preimage fiber. The calculation uses source-supplied Levin surjectivity and full component membership; its 32-element arithmetic is independently checked.

## 7. Consequences, acceptance test and boundaries

**A genuinely realized finite access interface.** The previously known data separated the period-3/9 external rays and their individual Levin maps, but did not compute the **complete eight-ray ladder** at the precritical defect. We now have (a) exact stage counts `1024/16/4`, (b) one and only one local branch transposition, (c) exactly `2048/32/8` ambient access angles, and (d) a complete **eight-ray source-derived pair of Levin markings** and a 32-ray **outer Levin bijection** at the true branch defect. The only new finite rays are preimages of the repelling orbit's exact periodic rays, not independently chosen model labels.

**Still not a Kahn localization-sheet comparison.** Kahn's canonical localization sheet groupoid is an **infinite coset-valued cover** on a different marked Riemann surface. It cannot be replaced by the degree-1024 physical inverse-point fiber or the eight Levin ray angles. No `O/xi/eta` pseudo-piece-side natural transformation or full Carathéodory border welding is proved. Similarly, the complex root monodromy does not claim globally continued ray labels outside the Mandelbrot connectedness locus.

**The strongest next stage:** identify the 12 remaining `K3\K9` precritical points with **their actual source-side access class and the exact 24 ambient inverse-ray angles** (2 per point), respecting the already verified KL 3/9 pseudo-piece side atlas, or find the first obstructed side/coset. This is now a **finite 12-point, 24-ray** source-alignment task rather than an undefined 1024-sheet search. At the tip an exact source-defined access map should be tested against the 8-ray ladder above; it must not conflate the two distinct internal angle targets.

**Trust and attribution.** All nontrivial source inputs are cited above. The deterministic checker validates exact orbit-value gaps, the full 2048-angle finite census, all cyclic orders and the uniqueness of the internal modular solutions. It does **not** independently verify the imported proper degree-two polynomial-like maps, external-ray landing theorems, Levin analytic maps or infinite-dimensional local-cover functoriality; those are separately written/imported theorems. This is archive-specific synthesis and finite realization assisted by OpenAI GPT-6; mathematical originality beyond this archive and independent specialist review are unestablished. MLC and every global gate remain OPEN.

**Reproduce:**

```sh
python -m py_compile research/independent_audits/verify_tip_nested_full_ray_census.py
python research/independent_audits/verify_tip_nested_full_ray_census.py --check-manifest
```
