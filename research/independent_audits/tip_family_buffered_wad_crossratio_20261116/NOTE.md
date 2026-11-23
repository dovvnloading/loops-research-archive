# Physical endpoint cross-ratios for the primitive-tip inner WAD: rigorous comparison bounds and a symmetry obstruction

**2026-11-16 — ADDITIVE / PARTIAL / support still OPEN.** This is a
read-only sequel to the merged [inner audit](../tip_family_buffered_wad_inner_20261116/NOTE.md)
and its [outer audit](../tip_family_buffered_wad_20261116/NOTE.md).
The new result is a *two-sided rational enclosure of the exact elliptic
modulus of the physical upper-halfdisk comparison quadrilateral*, for each
of three distinct-inner-hole pairs at each selected period `p=3..12` and
uniformly for **every** `p>=13`. It sharpens the inherited rigorous
*lower* bound on each named upper direct class by using the actual
elliptic/AGM formula rather than `s^(1/4)`. This does **not** enclose the
true universal-cover ideal-lift cross-ratio, and therefore does **not**
decide a single canonical buffered weight.

A second, analytic observation **refutes the proposed universal strict
single-direct minimization**: the upper and lower `K2--K1` arcs around
`K0` are distinct admissible simple classes, exchanged by reflection;
therefore their extremal lengths (and their `q`) are exactly equal.
Any valid effective word-cutoff theorem must include such ties.

## 1. Section 5's precise task and what it is *not*

For selected `p>=3`, put `f_c(z)=z^2+c`, `x_j=f_{c_p}^j(0)`,
`G_p=f_{c_p}^p`, `A_p=[z^2]G_p<0`, and
`R_3=1/4`, `R_p=2^-p (p>=4)`. KKL's **actual minimally marked**
three-slit, four-boundary surface is

\[
Y_{K,p}=D(0,R_p)\setminus(K_0\cup K_1\cup K_2),\quad
K_0=[x_{3p},x_{6p}],\quad K_1=[x_{4p},x_p],\quad
K_2=[x_{2p},x_{5p}].
\]

The strict normalized order is `K2 < K0 < K1`. With
`xi=(-A_p)z`, the normalized radius is `rho_p=(-A_p)R_p`.
These are **three whole ideal boundary circles**, plus the outer circle;
they are not the ten marked atoms on the different tree annulus.

For an A.1-admissible *simple* unoriented homotopy class `gamma`, let
`(a,b)` and `(c,d)` be distinct ideal interval **lifts in the universal
conformal cover**, with `a<b<c<d` after Möbius normalization. Then

\[
s_\gamma=\frac{(b-a)(d-c)}{(c-a)(d-b)},\qquad
q_\gamma=E(s_\gamma),\quad
E(s)=\frac{K(\sqrt{s})}{K(\sqrt{1-s})}.
\]

The elliptic Landen identity gives the exact threshold

\[
q_\gamma>2\iff s_\gamma> s_*:=12\sqrt2-16,
\quad s_*^2+32s_*-32=0,\quad 0<s_*<1. \tag{1}
\]

For a **rational** `0<s<1`, the verifier checks the sign of
`s*s+32*s-32` using integer fractions. This is a valid exact test of
`s>s_*` *only if `s` genuinely bounds the relevant ideal-lift
cross-ratio*. Section 5 requires (i) certified actual lift endpoints
for every candidate, and (ii) an **effective finite set of deck words
that contains every `q_gamma>2` class**, for each `p=3..12` and
uniformly in the tail. The KKL A.2.2 support bound `<=10` per surface
is **not** an enumeration or a uniform word cutoff. In particular,
plugging the physical slit endpoints into (1) without a conformal
uniformization is invalid.

For `p>=11` only the six inner types remain possible. For `p=3..10`
**four additional outer-incident types remain open**; this sequel has
not ruled them out.

## 2. Exact physical comparison cross-ratios

For `I<J` in the ordered set `K2,K0,K1`, write the complete physical
normalized slit endpoint quadruple as `a<b<c<d`, where `[a,b]=I`,
`[c,d]=J`. This is *not* the four ideal endpoints in (1). In the
physical upper halfdisk

\[
H_\rho=\{\Im\xi>0,\ |\xi|<\rho\}\subset Y_{K,p},
\]

the map `T_r(z)=((r+z)/(r-z))^2` to `H` gives the *comparison*
cross-ratio

\[
s_H(a,b,c,d;r)=
\frac{(b-a)(d-c)}{(c-a)(d-b)}
\frac{(r^2-ab)(r^2-cd)}{(r^2-ac)(r^2-bd)}. \tag{2}
\]

It satisfies `0<s_H<s_infty<1`, where the first factor is `s_infty`.
The formula follows exactly from
`T_r(y)-T_r(x)=4r(y-x)(r^2-xy)/((r-y)^2(r-x)^2)`.
It increases when `a,c` decrease or `b,d` increase. It also increases
strictly with `r>max |a,b,c,d|`: setting `t=r^2`,

\[
\frac{s_H}{s_\infty}=1-
 \frac{t(c-b)(d-a)}{(t-ac)(t-bd)},
\quad \frac{d}{dt}\frac{t}{(t-ac)(t-bd)}=
 \frac{abcd-t^2}{(t-ac)^2(t-bd)^2}<0. \tag{3}
\]

The strict derivative sign is valid because `t^2>|abcd|`.
Consequently the **true physical** `s_H` lies between these exact
corner evaluations:

* lower: inward electrodes `[xi_left.high,xi_right.low]` for each slit,
  at the certified **lower** normalized physical radius;
* upper: outward electrodes `[xi_left.low,xi_right.high]` for each slit,
  at the certified **upper** radius in each finite chart. In the all-`p`
  tail there is no common upper radius, so use `r=+infty` in (2), i.e.
  the first factor alone.

The predecessor's interval reconstruction independently checks all
selected roots `p=3..12`, their physical radii and collar separations.
For every `p>=13`, the p13 normalized model error box contains the six
true normalized endpoints and `rho_p>(3/20)2^p>=(3/20)2^13`. Therefore
the same fixed rational corner computations yield **uniform**, not
sampled, tail bounds. No interpolation between finite periods occurs.

Write `s_lo < s_H < s_hi` for the outward rational intervals printed
by the verifier. Applying the exact AGM identity

\[
E(s)=\frac{\operatorname{AGM}(1,\sqrt{s})}
           {\operatorname{AGM}(1,\sqrt{1-s})}                 \tag{4}
\]

with `128`-bit outward `isqrt` rounding, seven arithmetic/geometric
iterations and `b_n<=AGM<=a_n` gives strict rational output
`E_lo < E(s_H) < E_hi`. In the code the actual AGM geometric upper
iterate is intersected with its arithmetic upper bound to avoid a
one-ulp **false** ordering assertion. Every grid round is explicitly
strict, including when the value is on the grid.

**Interpretation:** the upper-halfdisk comparison paths lie in the named
upper-side simple arc class, so extremal-width monotonicity proves

\[
\boxed{q_{\gamma_{IJ}^{\rm upper}}>E_{lo}.}                 \tag{5}
\]

But `E_hi` bounds only `E(s_H)` in the **proper subdomain** `H_rho`.
It is **not** an upper bound on the ideal-quadrilateral
`q_{gamma_{IJ}^{upper}}` in the universal cover. Even when the physical
comparison has `s_H<s_*`, it does **not** follow that `q_gamma<=2`.
Both comparisons must keep this direction straight. The verifier emits
three pairs `K2-K0`, `K0-K1`, `K2-K1` at each `p=3..12` and in the
tail, with exact outward rational cross-ratio and elliptic-width
brackets. It supplies no self-endpoint lower comparison construction.


**Certified period-by-period physical comparison enclosures.** In the
three `s_H` columns, `L..U` means strictly `L/10^9 < s_H < U/10^9`;
in the three `E_H` columns, it means strictly
`L/1000 < E(s_H) < U/1000`. All bounds are exact rational outward
enclosures for the *complete physical slit endpoints* and the actual
physical radius; the `>=13` row is uniform for every later period.
These are **not** intervals enclosing the ideal-lift `s_gamma`.
The certified direct-class **true `q_gamma` lower bound** is the left
endpoint of its `E_H` column divided by 1000, while its true upper
comes only from the separate six-type caps in §3.

| p | `s_H` K2--K0 | `s_H` K0--K1 | `s_H` K2--K1 | `E_H` K2--K0 | `E_H` K0--K1 | `E_H` K2--K1 |
|:--|--:|--:|--:|--:|--:|--:|
| 3 | 29581976..29581978 | 3230471..3230473 | 137108..137110 | 499..501 | 368..370 | 268..270 |
| 4 | 28078343..28078345 | 3153149..3153151 | 139957..139959 | 495..497 | 367..369 | 268..270 |
| 5 | 35659224..35659226 | 5445025..5445027 | 509238..509240 | 515..517 | 392..394 | 302..304 |
| 6 | 37427892..37427894 | 5973551..5973553 | 673864..673866 | 519..521 | 397..399 | 310..312 |
| 7 | 37860691..37860693 | 6102571..6102573 | 721592..721594 | 520..522 | 398..400 | 312..314 |
| 8 | 37968191..37968193 | 6134599..6134601 | 733967..733969 | 520..522 | 398..400 | 313..315 |
| 9 | 37995015..37995017 | 6142590..6142592 | 737089..737091 | 520..522 | 398..400 | 313..315 |
| 10 | 38001717..38001719 | 6144586..6144588 | 737871..737873 | 520..522 | 398..400 | 313..315 |
| 11 | 38003393..38003395 | 6145085..6145087 | 738066..738068 | 520..522 | 398..400 | 313..315 |
| 12 | 38003811..38003813 | 6145210..6145212 | 738115..738117 | 520..522 | 398..400 | 313..315 |
| >=13 | 33394143..42851588 | 4949773..7425507 | 563909..934149 | 509..533 | 387..410 | 305..323 |

## 3. Genuine class brackets and the reflection counterexample

The complete classwise **strict upper** bounds from the predecessor's
AGM/cyclic-cover and local-weight arguments continue to hold for
**every** simple admissible class, including returning and winding
classes. A self arc contributes twice to local weight:

| Endpoints | Certified true `q_gamma` upper | Certified true lower |
|:--|--:|:--|
| K0--K0 | `6621/2000` | `q_gamma>0` (no singled-out direct) |
| K0--K1 | `5/2` | named upper direct: `q_gamma>E_lo` from (5) |
| K0--K2 | `57/20` | named upper direct: `q_gamma>E_lo` from (5) |
| K1--K1 | `5/2` | `q_gamma>0` (no singled-out direct) |
| K1--K2 | `5/2` | named upper direct: `q_gamma>E_lo` from (5) |
| K2--K2 | `57/20` | `q_gamma>0` (no singled-out direct) |

The period-specific `E_lo` values are printed by
`python -B research/independent_audits/tip_family_buffered_wad_crossratio_20261116/verify.py`.
Unlike its inherited `s^(1/4)` lower bound, (4) is a two-sided
*elliptic comparison* calculation and strengthens the known lower
bound; no resulting true-class bracket separates `q_gamma` from `2`.
No claim is made that these are globally optimal enclosures.

**Analytic obstruction to the proposed strict single-direct rule.**
Because `K2 < K0 < K1`, take a simple proper arc `gamma_+` from `K2`
to `K1` through the upper halfdisk and its complex-conjugate arc
`gamma_-` through the lower halfdisk. Choose endpoints corresponding
under conjugation. The concatenation of one with the reverse of the
other winds around `K0`; modulo free endpoint moves on `K2,K1`, this
cannot contract through the removed `K0`. Hence `gamma_+` and
`gamma_-` are distinct simple A.1-admissible unoriented classes.
Complex conjugation is anti-conformal on the real-symmetric physical
surface, so it preserves extremal length and width:

\[
\operatorname{EL}(\gamma_+)=\operatorname{EL}(\gamma_-),\qquad
q_{\gamma_+}=q_{\gamma_-}.                               \tag{6}
\]

With the specified upper class used as reference, the lower class has a
nontrivial **relative** deck word, yet is not strictly longer.
Thus the user's proposed proof that **all** non-direct classes are
strictly worse than **the** upper direct class cannot hold as stated;
reflection pairs have to be admitted or quotient out by symmetry.
Deck-word triviality is itself relative to reference lifts and
peripheral representatives; it is not a coordinate-free class label.
Equation (6) does *not* show that either class has positive weight.

## 4. What is known for every period and what amplification does not follow

For `p=3..10`, the four outer-incident types are not excluded. The
inherited exact bounds (upper strict; lower non-strict) are:

| p | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|:--|--:|--:|--:|--:|--:|--:|--:|--:|
| `||W_can|| <` | 6.867 | 7.627 | 5.361 | 4.606 | 4.228 | 4.001 | 3.850 | 3.742 |

For `p=11,12` and **every** `p>=13`, all outer-incident classes are
excluded and

\[
0\le\|W_{\rm can}(Y_{K,p})\|<619/200\quad(p\ge11).   \tag{7}
\]

For every `p>=3` the KKL cardinality bound says that at most **ten**
classes have `q_gamma>2`. It provides neither the candidates nor an
all-`p` word cutoff. The exact **positive-support verdict remains OPEN
for every period**: no class has been shown to satisfy `q_gamma>2`,
and no exhaustion of all classes with `q_gamma<=2` is available.
Thus there is no certified positive norm lower endpoint. These
nonnegative upper norm bounds also hold for `W_can^{h+v}`.

The independently proved unbuffered A.1 supremum gain remains

\[
D_p=1/C_p^++1/C_p^--1/P_p>1/100\quad(p\ge3),
\quad D_p>11/126\quad(p\ge13),                         \tag{8}
\]

relative to the explicitly stated dynamical and topological inputs of
[physical M-discharge](../tip_family_hypothesis_M_discharge_20261116/NOTE.md).
The specified parent/child unbuffered competitors there have `q<2`
and hence zero literal buffered coefficients. Their surfaces and
markings differ from `Y_{K,p}`; neither (5) nor (8) proves positive
buffered canonical weight or a KKL buffered-WAD amplification transfer.
Crucially, `f_*=(G_p)_*` is **unbranched covering pushforward** whereas
`\iota^*` is **immersion restriction** that filters proper source
pieces; these are distinct, and the actual immersion has a nonproper
attachment. A new leafwise, source-faithful comparison and §6 Wave
selection would still be needed even if a positive inner weight were
certified. No counterexample to KKL or conclusion about MLC is asserted.

## 5. Reproduce, verification boundary, hostile review

```sh
python -B research/independent_audits/tip_family_buffered_wad_crossratio_20261116/verify.py
python -B -m unittest discover -s research/independent_audits/tip_family_buffered_wad_crossratio_20261116 -p 'test_*.py' -v
```

The verifier calls the immutable predecessor chain, including the
selected-root and all-period checks, and uses only `Fraction`, integer
`isqrt`, exact interval endpoints and finite rational loops. Adversarial
regressions reject reversed endpoints, an undersized halfdisk,
misordered/colliding slits, invalid elliptic inputs, inappropriate
threshold domains and non-strict interval rounding; the output marks
**physical** comparison upper bounds separately from **actual** class
upper bounds. All new files live in this new directory and its
dedicated workflow; no old file is edited. The new PR workflow checks
the additions-only diff and requires the **unchanged** Research
validation and Weighted Lean checks on the exact PR head SHA.

**Exact finite checks:** every slit/radius interval corner and order;
identity (2) in rational arithmetic; 128-bit outward square roots;
seven-step AGM arithmetic bounds; strict grid rounding; threshold
polynomial sign; the existing p3..12 and all-p interval/AGM/collar
results. **Analytic arguments, not proved by execution:** conformal
halfdisk map; cross-ratio and radius monotonicity (3); AGM/complete
elliptic identity (4), modulus monotonicity and width inclusion;
reflection and distinctness (6); KKL canonical lamination/cardinality;
the predecessor's peripheral cyclic-cover bounds.
**Numerical-only:** none (no floating-point routine or sampled tail).
**OPEN:** true ideal-lift cross-ratios for all six inner types,
returning-arc sharp bounds, effective exhaustive deck-word cutoff,
any `q_gamma` decision relative to `2`, zero/positive canonical support
and lower norm, outer classes for `p<=10`, and any buffered-WAD
amplification implying (8). CI cannot certify an analytic theorem that
has not been proved.
