# Inner classes in the real primitive-tip buffered canonical WAD: exact uniform enclosures, **not** a support verdict

> **Current proof status.** V2 conditions the peripheral width bounds used here on H1, H2 and H4. Identifying each actual ideal class and its transverse normalization is a separate geometric step. [Proofs and remaining hypotheses](../../tip_family_theorem/PHYSICAL_BRIDGES.md)

**2026-11-16. Additive independent audit. Status: PARTIAL.** The merged
[outer/collar audit](../tip_family_buffered_wad_20261116/NOTE.md) excludes
**every** outer-incident admissible ideal class for selected periods
\(p\ge11\), but leaves the six inner endpoint types open. This note proves:

* **Qualitative finiteness:** KKL A.2.2–A.2.3 already implies that for **each
  fixed** \(p\ge3\), all but at most **ten** simple admissible classes,
  including returning inner classes, satisfy \(q_\gamma\le2\). This is
  **not** an effective list of ten classes and does **not** give one common
  finite list as \(p\) varies.
* **New exact universal classwise inner upper bounds:** every admissible
  class incident on \(K_0,K_1,K_2\), respectively, has
  \(q_\gamma<351/100,5/2,57/20\). The sharper six-type bounds below
  include the correct double counting of returning arcs. These bounds
  hold for **each** selected \(p=3,\ldots,12\) and **every** \(p\ge13\).
* **New two-sided bounds for three *specified* direct classes:** for
  \(K_2\)-to-\(K_0\), \(K_0\)-to-\(K_1\), and \(K_2\)-to-\(K_1\), taking
  the path through the **upper half** of the actual target disk, each
  \(p=3,\ldots,12\) has a positive strictly rational lower bound on
  \(q_\gamma\). A single such bound is obtained for **all** \(p\ge13\)
  from the p13 normalized orbit enclosure and a fixed subdisk. The
  verifier prints every lower bound, without floating-point evaluation.
  None exceeds the buffer threshold 2, so none certifies a positive weight.
* **Exact period-separated norm upper bounds** for \(p=3,\ldots,10\),
  in addition to the inherited \(0\le\|W_{\rm can}\|<619/200\) for
  \(p\ge11\). The lower norm endpoint remains **zero**.

**Not proved:** an effective finite deck-word/intersection cutoff, an
exhaustive set of inner representatives, a \(q_\gamma\) comparison with 2
for *any* inner class, a zero/positive canonical WAD verdict, or a positive
lower norm bound. In particular this is **not** the completed task's
requested canonical buffered amplification theorem. Neither the KKL
support-cardinality theorem nor an unbuffered Wave gain can be used as a
substitute for a positive canonical coefficient.

## 1. Exact surface, classes, and the finite-but-unlisted result

Use the *actual* minimally marked surface
\[
Y_{K,p}=D(0,R_p)\setminus(K_{0,p}\cup K_{1,p}\cup K_{2,p}),\qquad
R_3=1/4,\quad R_p=2^{-p}\ (p\ge4),
\]
with \(K_0=[x_{3p},x_{6p}]\), \(K_1=[x_{4p},x_p]\), and
\(K_2=[x_{2p},x_{5p}]\), where \(x_j=f_{c_p}^{j}(0)\).
These three intervals and the **outer** circle are the four full ideal
boundary components; do not replace them with the ten marked atoms of
\(\Omega_p=D(0,R_p)\setminus[x_{2p},x_p]\), nor with the twenty
source atoms. Write \(\xi=(-A_p)z\), \(A_p=[z^2]G_p<0\), so the
strict real order is
\[
\xi_{2p}<\xi_{5p}<\xi_{3p}<0<\xi_{6p}<\xi_{4p}<\xi_p.
\]
The inward-pointing outer disk has normalized radius \(\rho_p=(-A_p)R_p\).

For a simple *A.1-admissible* unoriented class \(\gamma\), KKL A.2.3
uses the ideal quadrilateral between the two associated ideal interval
**lifts** in the universal cover. Denote its *unbuffered* width by
\(q_\gamma\), and its canonical weight by
\[
w_\gamma=(q_\gamma-2)_+,\qquad
\|W_{\rm can}\|=\sum_\gamma w_\gamma.
\tag{1}
\]
A legitimate self-endpoint arc uses distinct lifts of its single
boundary component; a boundary-parallel arc in the same lift is not
A.1-admissible. There are infinitely many simple isotopy classes at
some of the six inner endpoint types.

**Finiteness theorem (direct application of KKL).** KKL A.2.3 says the
canonical foliations form a lamination, so \(W_{\rm can}\) is a valid WAD.
KKL A.2.2 bounds the support of every valid WAD by
\(3|\chi(Y)|+|\mathcal I|\). For the four-holed sphere,
\(\chi=-2\) and \(|\mathcal I|=4\), hence
\[
\#\{\gamma:q_\gamma>2\}\le 10.\tag{2}
\]
This **does** prove "all but finitely many inner classes have
\(q_\gamma\le2\)" for each fixed period, without assuming any finite
winding cutoff. It does **not** provide a computable cutoff or label the
exceptional ten; the number ten is not "ten endpoint types" and
not an enumeration of the inner candidates. Neither (2) nor continuity
in the parameter supplies a single finite support container for all
\(p\ge13\).

The source is Kahn–Kapiamba–Lyubich,
[MLC for parabolically bounded primitive renormalization,
Appendix A.1, A.2.1–A.2.5](https://arxiv.org/html/2606.27272v1).
The topology and existing rational annuli are inherited **read-only**
from the merged [buffered audit](../tip_family_buffered_wad_20261116/NOTE.md);
the exact root packets and all-period normalized chart remain those
of its named predecessors.

## 2. Elliptic/AGM bounds for *every* inner class

For each full inner ideal circle \(I\), the cyclic-cover argument in
the prior audit proves for **every** admissible incident lift pair,
including returning pairs,
\[
q_\gamma\le E(1-e^{-\ell_I}),\quad
E(s)=\frac{K(\sqrt{s})}{K(\sqrt{1-s})},\quad
\ell_I=\pi\mathcal W(I),\quad
\ell_I\le\frac{2\pi^2}{\log t_I},\tag{3}
\]
where the disjoint embedded *physical three-hole* Joukowski collars
have fixed parameters
\(t_{K_0}=11\), \(t_{K_1}=49\), \(t_{K_2}=25\).
The last inequality uses inverse-annulus-modulus convention and the
essential cyclic-cover inclusion, not a physical two-electrode
condenser mislabeled as a canonical ideal rectangle.

For \(0<r<1\) and \(\ell_I<2\log(1/r)\), we have
\(k'=e^{-\ell_I/2}>r\). By the classical
\(K(k)=\pi/(2\operatorname{AGM}(1,k'))\) and monotonicity,
\[
q_\gamma
 <\frac{\operatorname{AGM}(1,\sqrt{1-r^2})}
         {\operatorname{AGM}(1,r)}
 \le\frac{1-r^2/4}{\operatorname{AGM}(1,r)}.
\tag{4}
\]
For the last step, the AGM is at most its first arithmetic iterate
\((1+\sqrt{1-r^2})/2\le1-r^2/4\). Set \(a_0=1,b_0=r\) and
\(a_{n+1}=(a_n+b_n)/2\), \(b_{n+1}=\sqrt{a_nb_n}\).
The sequence \(b_n\) increases to the AGM, so replacing four geometric
iterates by *dyadic downward* square-root rounds gives an exact lower
bound on the denominator in (4).

| Incident inner boundary \(I\) | \(r<e^{-\ell_I/2}\) | Exact strict \(q_\gamma\) cap |
|:--|:--:|--:|
| \(K_0\) | \(1/62\) | \(351/100=3.51\) |
| \(K_1\) | \(3/38\) | \(5/2=2.5\) |
| \(K_2\) | \(2/43\) | \(57/20=2.85\) |

The verifier checks \(2\pi^2/\log t_I<2\log(1/r)\) using the
*existing* exact Machin and atanh rational enclosures, then checks
\((1-r^2/4)/b_4\) strictly against the rational cap. It does not use
Python `float`, decimal approximations, a numerical elliptic routine,
or an assumed hyperbolic uniformization of the four-hole surface.
The infinite-class implication (3)–(4) is **analytic**, not proved by
executing the finite Python arithmetic.

Using the inherited \(W_{\rm can}(I)<B_I\) with
\((B_0,B_1,B_2)=(2621/1000,323/200,1953/1000)\), and KKL's
local-weight inequality, returning classes count **twice**. Consequently
for every \(p\ge3\) and every admissible class of the indicated type:

| Inner endpoint type | Exact **strict** two-sided class bound |
|:--|:--|
| \((K_0,K_0)\) | \(0<q_\gamma<6621/2000\) |
| \((K_0,K_1)\) | \(0<q_\gamma<5/2\) |
| \((K_0,K_2)\) | \(0<q_\gamma<57/20\) |
| \((K_1,K_1)\) | \(0<q_\gamma<5/2\) |
| \((K_1,K_2)\) | \(0<q_\gamma<5/2\) |
| \((K_2,K_2)\) | \(0<q_\gamma<57/20\) |

These are two-sided *coarse* bounds, **not** threshold decisions:
every upper endpoint still exceeds 2 and \(q_\gamma>0\) is automatic
for an ideal quadrilateral. For example, the bound on
\((K_0,K_0)\) is \(2+B_0/2\) rather than \(2+B_0\); treating the
self arc as a single local incident endpoint would be wrong.

## 3. Certified *nontrivial* lower enclosures for three direct inner classes

There is also a simple source-faithful lower construction that avoids a
Fuchsian solver. In conformal \(\xi\)-coordinates choose the **upper
halfdisk** \(H_\rho=\{\Im\xi>0,\ |\xi|<\rho\}\). It is simply
connected and embeds in the actual three-slit surface: all slits lie
on its real diameter. For each chosen ordered inner pair \(K_i<K_j\),
choose rational electrodes \([a,b]\Subset K_i\) and
\([c,d]\Subset K_j\) along the upper side of the slits, with
\(-\rho<a<b<c<d<\rho\).

The conformal map
\[
T_\rho(z)=\left(\frac{\rho+z}{\rho-z}\right)^2:
H_\rho\longrightarrow\mathbb H
\tag{5}
\]
puts them on two ordered real-axis intervals. Its exact crossratio is
\[
s=\frac{(T_\rho(b)-T_\rho(a))(T_\rho(d)-T_\rho(c))}
{(T_\rho(c)-T_\rho(a))(T_\rho(d)-T_\rho(b))}\in(0,1).
\tag{6}
\]
The subquadrilateral between these two electrode arcs has ideal width
\(E(s)\). Because its path family lifts **inside the single direct
upper-side class** of the universal cover, monotonicity of extremal
width under inclusion yields
\[
\boxed{q_{\gamma_{ij}^{\rm upper}}\ge E(s)>s^{1/4}.}
\tag{7}
\]
Indeed the AGM formula says
\(E(s)=\operatorname{AGM}(1,\sqrt{s})/
\operatorname{AGM}(1,\sqrt{1-s})\); the numerator is at least
\(s^{1/4}\) by the arithmetic-geometric-mean inequality and the
denominator is at most 1. This lower bound is conservative: it does
not identify the *full* ideal quadrilateral modulus.

For each **separate** selected chart \(p=3,\ldots,12\), the verifier
takes the *rightmost* interval upper bound of every left slit endpoint
and the *leftmost* interval lower bound of its right endpoint, hence
its rational subelectrode is truly inside that slit. It chooses
\(\rho\) to be the inherited outward **lower** bound for the normalized
physical target radius, so the halfdisk is genuinely contained.
The finite certificates are the exact rational values in the verifier
output for the three pairs \((K_2,K_0),(K_0,K_1),(K_2,K_1)\), each
rounded **down**, with a strict fourth-power comparison. No
interpolation between periods is used.

The strict rational lower certificates printed by the verifier are:

| Selected period | \(q_{\gamma_{K_2K_0}^{\rm upper}}>\) | \(q_{\gamma_{K_0K_1}^{\rm upper}}>\) | \(q_{\gamma_{K_2K_1}^{\rm upper}}>\) |
|:--|--:|--:|--:|
| \(3\) | \(207/500\) | \(119/500\) | \(27/250\) |
| \(4\) | \(409/1000\) | \(59/250\) | \(27/250\) |
| \(5\) | \(217/500\) | \(271/1000\) | \(3/20\) |
| \(6\) | \(439/1000\) | \(139/500\) | \(161/1000\) |
| \(7\) | \(441/1000\) | \(279/1000\) | \(163/1000\) |
| \(8\) | \(441/1000\) | \(279/1000\) | \(41/250\) |
| \(9\) | \(441/1000\) | \(279/1000\) | \(41/250\) |
| \(10\) | \(441/1000\) | \(279/1000\) | \(41/250\) |
| \(11\) | \(441/1000\) | \(279/1000\) | \(41/250\) |
| \(12\) | \(441/1000\) | \(279/1000\) | \(41/250\) |
| Every \(p\ge13\) | \(427/1000\) | \(53/200\) | \(77/500\) |

They are rigorously rounded *below* the halfdisk subquadrilateral
width, which is itself only a lower bound for the true ideal width.
They cannot be read as buffered weights or q-value approximations.

For **every** \(p\ge13\), the inherited uniform p13-model error box
contains all six real \(\xi_{jp}\), and the actual normalized radius
obeys \(\rho_p>(3/20)2^p\ge(3/20)2^{13}\). The verifier uses
\(\rho=(3/20)2^{13}\) and the *same three fixed rational electrodes*
inscribed in the **p13 outer error box**. They therefore work in every
later selected physical surface. This is a genuine uniform
\(p\ge13\) lower enclosure; it does not substitute a sampled p13
parameter for the all-period tail.

All three named classes are A.1-admissible, simple and unoriented when
projected (their endpoints lie on *different* complete ideal circles).
Their lower bounds are strictly positive but below 2; in particular
\(q_\gamma>0\) says **nothing** about
\(w_\gamma=(q_\gamma-2)_+\). The verifier does **not** apply this
lower construction to returning classes or winding-class variants.

## 4. Period by period and uniform norm bounds

The same inner three collars are proved in every selected chart. For
\(p=3,\ldots,10\) the already-certified outer carrier has
\[
t_{\rm out}(p)=(23/10,2,4,8,16,32,64,128)
\quad\text{for }p=3,\ldots,10.
\]
As the outer-incident weights have **not** been excluded for these
periods, KKL A.2.4–A.2.5 gives only
\[
0\le\|W_{\rm can}(Y_{K,p})\|
 < \tfrac12\left(\frac{6189}{1000}+
                  \frac{2\pi}{\log t_{\rm out}(p)}\right).
\tag{8}
\]
With exact rational \(\pi\) and \(\log\) intervals, the checker
rounds the right-hand side strictly upward to the nearest \(1/1000\):

| \(p\) | \(3\) | \(4\) | \(5\) | \(6\) | \(7\) | \(8\) | \(9\) | \(10\) |
|:--|--:|--:|--:|--:|--:|--:|--:|--:|
| \(\|W_{\rm can}\|<\) | 6.867 | 7.627 | 5.361 | 4.606 | 4.228 | 4.001 | 3.850 | 3.742 |

For \(p=11,12\) separately and **every** \(p\ge13\), the
predecessor's cyclic-cover proof eliminates all outer incidence. Thus
\[
0\le\|W_{\rm can}(Y_{K,p})\|<619/200\quad(p\ge11),\tag{9}
\]
unchanged by the present inner bounds. The projection
\(W_{\rm can}^{h+v}\) has no larger norm. Equations (8)–(9) do **not**
prove strict positivity at either the level of any class or the total
norm; an upper bound cannot be inverted to get a positive coefficient.

## 5. What exact extremal subproblem remains

For each \(p\ge11\), the only possible support types are
\((K_0,K_0),(K_0,K_1),(K_0,K_2),(K_1,K_1),(K_1,K_2),(K_2,K_2)\).
For \(p=3,\ldots,10\) the four outer-involving types must additionally
be decided; the present audit makes no claim to have eliminated them.

The **missing effective theorem** is a uniform certificate that supplies,
for each selected finite period and the all-p tail, a *concrete* finite
set of A.1-admissible simple deck words containing every inner
\(q_\gamma>2\) class, together with rigorous crossratio enclosures for
every candidate. If four ideal lift endpoints are ordered
\(a<b<c<d\), and
\(s=((b-a)(d-c))/((c-a)(d-b))\), then the exact support predicate is
\[
q_\gamma>2\quad\Longleftrightarrow\quad
s>12\sqrt2-16.\tag{10}
\]
Thus **one** certified candidate with
\(s>12\sqrt2-16\) establishes positive canonical weight; conversely
all candidates with \(s\le12\sqrt2-16\), *and* a complete exclusion
of all other simple deck words, prove vanishing. An endpoint enclosure
with a merely numerical crossratio, or a fixed winding search without
a tail theorem, is inadequate. A lower or upper analytic comparison
from (4)/(7) that straddles 2 cannot decide (10).

The KKL bound (2) gives the needed *existence of finite support per
surface*, but neither an algorithm to locate that support nor a
uniform-in-\(p\) word cutoff. The three halfdisk lower bounds concern
only three specific direct classes and do not solve the other classes.
In particular **whether \(W_{\rm can}\equiv0\) in this family, or has
certified positive weight on even one class, remains OPEN**.

## 6. KKL amplification and independent unbuffered gain

The merged
[physical M-discharge](../tip_family_hypothesis_M_discharge_20261116/NOTE.md)
proves, relative to its explicit external dynamical/topological
inputs, the A.1 independent-supremum unbuffered gain
\[
D_p=1/C_p^++1/C_p^--1/P_p>1/100\quad(p\ge3),
\qquad D_p>11/126\quad(p\ge13).
\]
Those parent and child suprema concern respectively
\(\Omega_p=U_p\setminus T_p\) and
\(\Omega'_p=V_p\setminus T'_p\), **not** the four-boundary
\(Y_{K,p}\). On the *specified* unbuffered parent/child extremal
competitor classes, the established width envelopes are below 2,
so their literal buffered coefficients are zero. This prevents
amplification by *inverting* those coefficients. It does not prove
vanishing of the distinct \(Y_{K,p}\) canonical WAD or invalidate the
unbuffered \(D_p\) result.

In Appendix A.3, \(f_*=(G_p)_*\) is the **unbranched covering
pushforward**, while \(\iota^*\) is the **different immersion
restriction** which filters proper source pieces. They must not be
identified; the actual attachment makes the immersion nonproper.
A positive inner canonical coefficient, if eventually certified,
would still need a source-faithful, leafwise projection/pullback
comparison and the relevant §6 near-maximal Wave selection before a
KKL buffered-WAD amplification argument for \(D_p\) follows.
This note proves **neither** the positivity premise **nor** that
transfer. It asserts no counterexample to KKL or conclusion about MLC.

## 7. Reproduce, numerical scope and hostile review

From the repository root, without changing any existing file:

```sh
python -B research/independent_audits/tip_family_buffered_wad_inner_20261116/verify.py
python -B -m unittest discover -s research/independent_audits/tip_family_buffered_wad_inner_20261116 -p 'test_*.py' -v
```

The new verifier imports the predecessor *read-only*, reruns its exact
selected-root and all-p physical collar certificates, checks all three
inner cyclic lengths against rational AGM cutoff premises, computes
all six upper type bounds, and constructs the rational halfdisk
subelectrodes in **each** chart. It checks every crossratio by exact
integer/Fraction operations, taking dyadic downward square-root
rounds and strictly downward fourth-root rounds. The finite CI gate
adds adversarial tests for false arc/cut order, an undersized physical
disk, an unjustified elliptic cutoff, nonpositive arithmetic input,
and no-positive-support scope markers.

**Analytic inputs not formalized in Python:** KKL's canonical lamination
and support theorem; the prior cyclic-cover/geodesic-length theorem;
annular extremal-width monotonicity; the conformal upper-halfdisk map
and ideal SC quadrilateral formula; and the AGM formula for elliptic
integrals. **Exact or interval-certified:** all inherited selected charts,
three embedded collars for every finite and tail period, rational
\(\ell_I\) and AGM premises, all typewise \(q\) caps, all inscribed
real electrodes and strict rational crossratios, all three selected
lower bounds per chart, and all stated norm arithmetic. **Numerical-only
results:** none. **Unproved:** effective inner class enumeration,
self/winding class two-sided *sharp* bounds, any inner decision at 2,
canonical support/positivity, all-period positive norm lower bound,
and the buffered-WAD-to-unbuffered-Wave amplification transfer.

All files are additive. The dedicated new CI workflow requires a
new-files-only diff, executes the verifier and adversarial tests, and
triggers the **unchanged** Research validation and Weighted Lean
workflows at the **exact PR head SHA**. Passing CI establishes the
finitely checked implications of the stated analytic results, not the
missing extremal subproblem.