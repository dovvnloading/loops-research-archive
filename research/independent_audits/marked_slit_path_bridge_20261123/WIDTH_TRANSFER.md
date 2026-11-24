# Every admissible finite-slit Wave: a conformal comparison proof

**2026-11-23. Written proof, subject to the explicitly cited dynamical
inputs; not a Lean formalization or an MLC proof.** This note supplies the
class-inclusion and metric arguments for the selected finite slit surfaces.
The companion [ideal-boundary proof](IDEAL_BOUNDARY.md) constructs their
KKL ideal compactifications and retains the actual winding of each path.
The [current dynamical bridge](../../tip_family_theorem/PHYSICAL_BRIDGES.md),
§§1–3, supplies the selected real parameter, the actual interval trees,
and their proper central return. No different surface is substituted.

The conclusion concerns the independent unbuffered A.1 suprema. It does
not identify a buffered canonical WAD, a maximizing lamination, a common
parent realizing both child optima, or an iterated amplification.
Only the companion's intrinsic compactification, covering marking and
same-lift A.1 class theorem are used. No immersion-pulled marking, outer
pullback lemma, or complete geometric-trace restriction theorem is an
input. The full MARK obligation remains open.

## 1. Exact objects and the path selection that is needed

Fix one selected period p. Write y_j = x_{jp}, a for its dividing fixed
point, U = D(0,R), V for the central component of G^{-1}(U), and

\[
 T=[y_2,y_1],\quad T'=[-y_1,y_1],\quad
 \Omega=U\setminus T,\quad \Omega'=V\setminus T'.
\]

The target three-atom base is (I_9,I_0,I_1). The source bases are
(S_1,S_2,S_3) and (S_17,S_18,S_19). A parent Wave in the asserted class
has crest containing I_0, so every leaf has one endpoint in I_9 and the
other in I_1. An end cannot include I_0 without removing it from the
crest. Both endpoints also cannot belong to the same remaining atom:
subordination to this proper base fixes their common base lift, and the
same-lift criterion then makes the path subordinate to that one atom,
which A.1 excludes. Marked paths have endpoints inside atoms, not at
their junctions. The same reasoning puts each upper child's endpoints
in S_1 and S_3, and each lower child's endpoints in S_17 and S_19.

For the target put m=(y_2+y_1)/2, r=(y_1-y_2)/2, and

\[
 \Pi_P(w)=m-r\cosh w,\qquad w=s+it,\quad s>0.
\]

Its period is 2πi. The full inverse image of Ω is its actual universal
cover, rather than an assumed round strip. Put

\[
 a_P=\arccos\frac{m-y_5}{r},\qquad
 b_P=\arccos\frac{m-y_3}{r},\qquad 0<a_P<b_P<\pi.
\]

The electrode windows for the left-tip base are

\[
 E_-=\{s=0:-b_P<t<-a_P\},\qquad
 E_+=\{s=0:a_P<t<b_P\}.
\tag{1}
\]

The same-lift criterion of the companion proof implies that **every**
parent leaf has a lift with endpoints in these two windows. A leaf with
another winding cannot be subordinate to this same proper base arc.
This is a consequence of the path's subordination, not a shortest-distance
decision on its two endpoint labels. Conversely, a curve inside the
lifted physical domain with these endpoints projects to this relative
class whenever its projection is simple.

For the upper source child use

\[
 \Pi_C(w)=y_1\cosh w.
\]

Its source electrodes lie on the upper bank at
(-y_4,y_2) and (y_5,-a). If

\[
 a_C=\arccos(y_4/y_1),\quad b_C=\arccos(-y_2/y_1),\quad
 c_C=\arccos(-y_5/y_1),\quad d_C=\arccos(a/y_1),
\]

then 0<a_C<b_C<c_C<d_C<π and the ordered rail endpoints are

\[
 (e_1,e_2,e_3,e_4)
   =(\pi-d_C,\pi-c_C,\pi-b_C,\pi-a_C).
\tag{2}
\]

The electrodes are (e_1,e_2) and (e_3,e_4). Reflecting all four points
preserves their cross-ratio. The same-lift criterion applies to every
eligible source child, including every proper representative admitted by
the source definitions. The lower class is the complex conjugate of the
upper one.

## 2. Embedded quadrilaterals supply genuine lower bounds

Let Q be one of the following regions in the target w-plane:

* the right semidisk {s>0, |w|<H}, with b_P<H<π; or
* the right circular segment {s>0, |w+d|<L}, whose diameter
  endpoints are ±iT, where b_P<T<π, d=(T²-h²)/(2h),
  and L=(T²+h²)/(2h).

Assume the explicit full-domain inequality puts Π_P(Q) in U.
The map Π_P is injective on {s>0, |t|<π}. Indeed
cosh u=cosh v implies u=v+2πik or u=-v+2πik; the second possibility
has opposite real parts, and the first has k=0 in this strip. Its
derivative is nonzero there. Thus Π_P maps Q conformally into Ω.

Uniformize the Jordan quadrilateral Q, with the two electrode windows
as distinguished opposite sides, to a rectangle. The open foliation by
straight segments joining those sides pulls back to disjoint, simple
proper curves. Their endpoints lie in the open windows (1). Each region
Q is contained in the same lifted physical domain and the two endpoints
lie in one lift of the designated left-tip base. The same-lift criterion
therefore supplies a homotopy into every collar of that base. This does
not require an arbitrary leaf's imaginary excursion to stay between
its endpoint coordinates.

Every projected leaf is subordinate to (I_9,I_0,I_1), and no leaf is
subordinate to an arc containing at most two atoms: any such arc would
have to contain both nonadjacent endpoint atoms with the same lift.
The entire foliation has both end atoms, so its minimal base is the
specified three-atom base, with crest the access closure of I_0 (the
middle open atom and its two junctions). It is an actual A.1 Wave.

If the rectangle has horizontal length l and vertical height h and its
leaves are horizontal, their width is h/l. For any admissible density,
Cauchy–Schwarz on each horizontal segment, followed by integration in
height, gives energy at least h/l. The constant density 1/l attains
that value. The width of this fixed family in the ambient Ω is the
same: restrict an ambient admissible density to Q for one inequality
and extend the rectangle metric by zero outside Q for the other.
This proves the lower bound without identifying all-path extremizers
with all admissible physical Waves.

The elementary maps used in the earlier arithmetic remain correct:

\[
 w\longmapsto\frac{2Hw}{H^2-w^2}
\]

maps the right semidisk to the right half-plane, with imaginary diameter
coordinate t sent to 2Ht/(H²+t²). The circular segment is mapped to a
wedge by (w-iT)/(w+iT), then to a half-plane by the power
π/(2 arctan(h/T)), using the continuous branch on that wedge. The
Schwarz–Christoffel rectangle formula gives K(k)/K(k'), where the
symmetric four-electrode ratio is k=(B-A)/(B+A).
These are the exact same formulas evaluated by the archived rational
interval routines; no numerical optimizer is used.

For p=3,4, the full-domain certificates use h=83/100,88/100 and T=31/10.
For 5≤p≤12 they use H=7/5. For the remaining selected periods they
use H=5/2. The actual inequalities are
|m|+r cosh h<R, or the corresponding bound with H. Equivalently, the
arithmetic uses M=(-A_p)m and r_hat=(-A_p)r and proves
|M|+r_hat cosh h<(-A_p)R in the positive scaled coordinate.
They control the whole region because
|cosh(s+it)|≤cosh s. Checking a single ray or its endpoints would not
provide this argument.

## 3. Upper metrics: the precise covering inequality

Let Π:H→C\L be either logarithmic Joukowski cover, with
H={Re w>0}, and let D be the actual finite physical surface. Let
\(\widetilde D=\Pi^{-1}(D)\). Suppose σ is an admissible finite-area
density on H for **all** curves joining the two chosen electrode
windows. Define on D

\[
 \rho(z)^2
   =\sum_{w\in\Pi^{-1}(z)}
       \frac{\sigma(w)^2}{|\Pi'(w)|^2}.
\tag{3}
\]

This formula includes the conformal Jacobian. Equivalently one may
write the square-sum in local logarithmic coordinates as in the
earlier notes, but it is not an identity between Euclidean densities
in different coordinate planes without this factor.

For any selected physical leaf γ, §1 supplies a lift \(\widetilde\gamma\)
joining the prescribed windows. Pointwise on its lift,
\(\rho(\Pi(w))|\Pi'(w)|\geq\sigma(w)\). Hence

\[
 \int_\gamma\rho\,|dz|
 \geq\int_{\widetilde\gamma}\sigma\,|dw|\geq1.
\tag{4}
\]

Thus the very same ρ is admissible for every leaf of every Wave in
the fixed physical class. Change of variables on evenly covered
patches and Tonelli's theorem give

\[
 \int_D\rho^2\,dA
       =\int_{\widetilde D}\sigma^2\,dA
       \leq\int_H\sigma^2\,dA.
\tag{5}
\]

Finite energy implies the sum is finite almost everywhere. At exceptional
points retain the literal nonnegative sum, possibly infinite, so (4)
still holds; it is not silently replaced by an arbitrary a.e. version
on a set where one of the required curves might travel.

The Schwarz–Christoffel rectangle metric for the four rail electrodes
is admissible for every locally rectifiable curve in H joining them:
its rectangle image crosses the prescribed opposite sides, so the
necessary coordinate displacement gives length at least one.
For continuous paths that fail local rectifiability, its positive smooth
density has infinite length on a compact subpath where rectifiability
fails; equivalently use generalized metric length throughout. Thus the
argument does not discard any continuous A.1 path.
Its full energy is

\[
 E=\frac{K(k)}{K(\sqrt{1-k^2})},\qquad
 k^2=\frac{(e_2-e_1)(e_4-e_3)}
            {(e_3-e_1)(e_4-e_2)}.
\tag{6}
\]

For (2), this is exactly
((b_C-a_C)(d_C-c_C))/((c_C-a_C)(d_C-b_C)).
Equations (3)–(5) prove C_p^±≤E for the entire physical child
classes. They do not require the projection of every curve in the
upper envelope to be simple, admissible, or a Wave: the inclusion
needed for an upper bound is from the physical class into the envelope.

The identical argument gives the parent upper envelope, using (1).
Restricting to the finite lifted outer envelope before taking its
modulus can sharpen that bound. It never asserts equality of width
upstairs and downstairs under a noninjective cover.

## 4. The omitted-box saving is valid on the entire source

For the child cover Π_C(w)=y_1 cosh w, a unit box

\[
 B=(s_0,s_0+1)\times(0,1)
\]

is outside \(\widetilde{\Omega'}\) whenever y_1 sinh(s_0)>R. Indeed

\[
 |\Pi_C(s+it)|^2
     =y_1^2(\sinh^2s+\cos^2t)>R^2,
\]

whereas V⊂U=D(0,R). This excludes the entire box from every lift
of the actual source. Restrict σ to \(\widetilde{\Omega'}\) before
periodizing. No selected lifted path meets the removed box, so its
length in (4) is unchanged. Equation (5) improves to

\[
 \int_{\Omega'}\rho^2\,dA
       \leq E-\int_B\sigma^2\,dA.
\tag{7}
\]

There is no subtraction of energy from a box traversed by another
eligible winding; exclusion was from the full inverse image, not from
one drawn representative.

For completeness, a Schwarz–Christoffel primitive on H has derivative,
up to the constant that cancels upon normalization,
\(\prod_{j=1}^4(w-ie_j)^{-1/2}\). On B, 0<e_j<π<4 implies
|w-ie_j|<s_0+5. The electrode-gap rectangle side has length at most
π/√((b_C-a_C)(d_C-c_C)): over the gap substitute t between its two
middle endpoints and bound the two remaining factors below by the
adjacent gap lengths; the residual beta integral is π.
Consequently

\[
 \int_B\sigma^2\,dA>
 \frac{(b_C-a_C)(d_C-c_C)}{16(s_0+5)^4}.
\tag{8}
\]

The finite exact certificates verify that this exceeds 1/5,000,000
for their listed s_0 values. This proves the claimed strict source
upper saving, with no assumption about which Wave attains a supremum.

## 5. Repair of the all-period arithmetic seam

The cited orbit estimate is

\[
 |X_{j,p}+u_j|
 \leq\left(30\cdot15246+\frac{88(4^j-1)}3\right)4^{-p},
 \qquad j=2,3,5.
\tag{9}
\]

The original limiting-gain implementation instead divided the first
term by three as well. The error is 304920·4^{-p} in each such
coordinate radius. Correcting the formula is necessary even though
the old executable returned PASS.

The corrected broad p=13 box has the outward parent-width enclosure
(0.658663060,0.749148532), so that box alone cannot establish >2/3.
The repair uses the actual p=13 parameter, certified by the existing
signed-chart root and derivative routine. Propagating its critical orbit
and A_13 gives (0.701260568,0.701260571). The correctly widened p=14
box gives (0.690181183,0.712667273), and all subsequent boxes are
nested inside it by the explicit coefficient times 4^{-p}.
Both estimates retain the original strict lower bound >2/3.

The code and its new regression compare the parent enclosure against
the independently implemented upstream child input bounds. A second
test explicitly records the insufficient p=13 broad box and the
successful actual p=13 case. The infinite tail remains a written
deduction from the bound (9); no finite test proves (9).

Combining §§1–4 with the corrected arithmetic gives, on the same
specified finite surfaces,

| Periods | Parent lower bound | Each child upper bound | Defect lower bound |
|---|---:|---:|---:|
| p=3 | 49/100 | 487/500 | 300/23863 > 1/100 |
| p=4 | 511/1000 | 197/200 | 7400/100667 > 7/100 |
| 5≤p≤12 | 581/1000 | 247/250 | 43500/143507 > 3/10 |
| p=13, then p≥14 | 2/3 | 63/50 | 11/126 > 1/100 |

All displayed bounds are strict. Each child class has positive width:
use a sufficiently thin embedded collar rectangle between subintervals
of its two open electrodes; its leaves have the selected three-atom
base. Reflection preserves the actual domain and markings, so
C_p^+=C_p^-=C_p. Positivity, the lower parent family and the universal
upper metrics therefore imply, writing l_p and u_c for the numerical
parent floor and child cap in a row of the table,

\[
 \frac1{C_p^+}+\frac1{C_p^-}-\frac1{P_p}
 >\frac2{u_c}-\frac1{l_p}.
\]

This is a comparison of independently optimized classes. For a single
pairable parent whose every leaf contains both designated proper children,
the hypotheses of KKL Lemma A.11 give the other, harmonic-combination
inequality. Nothing here creates the joint parent or makes the independent
defect an iteratable width amplifier.

## 6. The limiting cusp must not be called a KKL outer circle

The auxiliary limit C\[a,b] is conformal to a punctured disk. Infinity
is a cusp. In the upper-half-plane universal model its cyclic deck
group is parabolic, has one limit point, and the KKL ideal boundary
formula gives only the noncuspidal inner ideal circle. KKL A.1 starts
with cusp-free surfaces. Thus the limiting plane-slit calculations
may be used as inner-marked conformal comparison calculations, but
their infinity is not a whole outer ideal-circle atom in the native
KKL category.

This correction has no effect on the finite physical theorem above:
both finite surfaces are annuli of finite positive modulus, their
outer ideal circles are present, and all inequalities were proved
on those surfaces before any limit was taken. In particular no
convergence of the unrestricted suprema was needed.

## 7. Sources, verification and review status

The primary source for the path classes, Wave bases and restrictions is
[Kahn–Kapiamba–Lyubich, arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1),
Appendix A.1 and A.3.2. Lemma A.11 supplies the separately qualified
pairable-family inequality. The ideal-boundary specialization is proved
in the companion note. Schwarz–Christoffel rectangle uniformization,
conformal invariance, covering path lifting, Cauchy–Schwarz and Tonelli
are the classical inputs; their applications and all comparison
directions are displayed above.

Reproduce the corrected arithmetic from the repository root:

    python -B -m unittest discover -s research/independent_audits/tip_family_limiting_wave_gain_20261116 -p 'test_verify.py' -v
    python -B research/independent_audits/tip_family_finite_p_wave_gain_20261116/verify.py

These commands certify the exact finite arithmetic and rejection of
the old under-enclosure, not the analytic theorems. The arguments were
developed and adversarially reviewed with OpenAI GPT-6 Astra Pro.
Human specialist review has not occurred. The full non-locally-connected
issue #40, prescribed connector words in #62, general H1–H4, UPTCR and
MLC are not settled by this finite-slit result.
