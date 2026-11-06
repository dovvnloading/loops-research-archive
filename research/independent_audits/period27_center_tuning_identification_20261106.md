# The certified real period-27 center is the threefold airplane center

**Date:** 2026-11-06.

## Target and status

**Target:** the center-identification objective in issue #29. Let `c*` be the
real exact-period-27 superattracting parameter certified in
[the real restrictive-interval audit](real_quadratic_3_9_restrictive_certificate_20261105.md).
Let `A` denote the real period-3 airplane hyperbolic component, and write
`H*W = iota_H(W)` for Douady–Hubbard tuning. Then

\[
\boxed{c_*\text{ is the unique center of }A*(A*A)=A*A*A.}
\]

**Status:** proved in classical mathematics, using the exact rational certificate
and the explicitly located parameter-ray results below. The finite input is
checked by the accompanying Python program. The imported complex-dynamical
results and their application are not Lean formalizations.

This supplies the theorem bridge left open in
[the kneading-angle audit](period27_kneading_angle_permutation_source_audit_20261105.md)
and [the three-scale symbolic audit](period27_three_scale_symbolic_marking_20261105.md).
Their arithmetic remains valid; their earlier statements that the center
identification was unproved describe the status before this note.

## 1. Sources and precise imported statements

All page numbers below are the printed page numbers of the linked PDFs.
The statements are paraphrases, with hypotheses preserved.

| Source | Exact location | Statement used |
| --- | --- | --- |
| Xavier Buff, William Floyd, Sarah Koch, Walter Parry, *Factoring Gleason polynomials modulo 2*, PDF dated August 22, 2022 ([author-hosted PDF](https://public.websites.umich.edu/~kochsc/GleasonMod2.pdf)) | §4.3, pp. 7–8; Example 4.2, p. 8 | Definition of the signed critical kneading sequence and its binary angle; the real period-3 center has angle `0.overline(011) = 3/7`. |
| Buff–Floyd–Koch–Parry (BFKP), same PDF | §4.4, p. 9 and the **first paragraph of p. 10**, in the proof of Theorem 1.5 | For a real center `c` of exact period `n >= 2`, the root of its hyperbolic component is the common landing point of the parameter rays at `theta(c)` and `-theta(c)`. The multiplier map identifies the component conformally with the unit disk; its center and root correspond to multipliers zero and one. |
| Saeed Zakeri, *External Rays and the Real Slice of the Mandelbrot Set*, arXiv:math/0210382v1 ([PDF](https://arxiv.org/pdf/math/0210382v1)) | §2, p. 5, paragraph containing equation (2.1) | Every parameter ray at a rational angle with odd denominator lands at the root of a **unique** hyperbolic component. Root angles are represented by periodic binary words as in (2.1). |
| Zakeri, same PDF | §2, p. 6, “The tuning operation,” especially equation (2.2) and its following paragraph | Tuning takes centers to centers and roots to roots, multiplies component periods, and acts on ray angles by block substitution. If a parameter ray lands at `c`, its substituted-angle ray lands at `iota_H(c)`. Tuning is associative on hyperbolic components. |

The root-ray assertion in BFKP is **unnumbered**. It is not Theorem 4.3:
Theorem 4.3 on p. 8 concerns order, admissibility, and the doubling periods of
real-center kneading angles. That theorem by itself would not supply the missing
identification of the component root. Here the decisive bridge is the explicit
root-ray assertion on p. 10. The corresponding statements in Zakeri's background
section are likewise located by page, paragraph, and equation, not by an invented
theorem number.

These assertions concern periodic rational rays, hyperbolic components, and
tuning; their use here does not assume the Mandelbrot local connectivity
conjecture or global landing of irrational rays.

## 2. Normalizations and the finite certificate

Both sources use the monic centered family

\[
f_c(z)=z^2+c.
\]

Their parameter rays use the external uniformization normalized by
`Phi(c) = c + O(1)` at infinity, with angles in `R/Z` measured in turns.
Thus conjugation changes an angle `theta` to `-theta = 1-theta`, and there is
no angular rotation between the two sources.

Define `P_n(c)=f_c^n(0)`. The archived parameter is the unique zero of `P_27`
in the open dyadic interval

\[
\frac{k}{2^{128}}<c_*<\frac{k+1}{2^{128}},\qquad
k=-607890580437450502081459824019535455703.
\]

The existing `exact_center_orbit` helper in
[`verify_period27_symbolic_atlas.py`](verify_period27_symbolic_atlas.py)
checks, using outward-rounded integer interval arithmetic on the `2^-224`
mesh, that `P_27` is positive at the left endpoint, negative at the right
endpoint, and has a strictly negative parameter derivative throughout the
interval. Continuity and strict monotonicity give existence and uniqueness of
the root. Each of the first 26 critical iterates has a strict certified sign,
so the critical point has exact period 27. In particular `c*` is a real
superattracting center, as required by the BFKP statement.

For clarity, the BFKP kneading convention is indexed at the critical **point**:
`kappa_j` is `+`, `-`, or `*` according to the sign of `f_c^j(0)`, with
`kappa_0=*`. Its binary digits satisfy

\[
t_{j+1}=
\begin{cases}
0,&\kappa_j=*,\\
t_j,&\kappa_j=+,\\
1-t_j,&\kappa_j=-.
\end{cases}
\]

The star at `j=0` gives `t_1=0`, without requiring a value of `t_0`.
At a period-27 center the next star at `j=27` resets `t_28=0`, so the block
`t_1...t_27` repeats. Applying this definition to the certified signs gives

\[
\begin{aligned}
w&=011100100100011011100011011,\\
\theta(c_*)&=0.\overline{w}
=\frac{59914011}{134217727},\\
1-\theta(c_*)&=\frac{74303716}{134217727}.
\end{aligned}
\]

Here `134217727 = 2^27-1`. This is the signed critical-point convention of
BFKP, rather than a word starting at the critical value or an angular itinerary
relative to moving partition endpoints. The checker implements this convention
directly. It also verifies exact doubling period 27 and that this angle is
uniquely closest to `1/2` in its doubling orbit; the latter is a consistency
check against BFKP Theorem 4.3, not an additional premise needed for the proof.

## 3. The root angles of the threefold tuning

The real period-3 airplane component `A` has root-ray angles `3/7` and `4/7`
(BFKP Example 4.2 and §4.4, including Figure 1 on p. 9). Their binary blocks
are `011` and `100`. With the lower-angle block assigned to the digit zero,
Zakeri's equation (2.2) therefore gives the substitution

\[
S(0)=011,\qquad S(1)=100.
\]

It acts on infinite binary expansions by concatenation. Applying it to both
root angles twice yields the following exact values.

| Component | Period | Lower-angle block | Lower root angle | Upper root angle |
| --- | ---: | --- | --- | --- |
| `A` | 3 | `011` | `3/7` | `4/7` |
| `A*A` | 9 | `011100100` | `228/511` | `283/511` |
| `A*(A*A)` | 27 | `011100100100011011100011011` | `59914011/134217727` | `74303716/134217727` |

The upper block is the bitwise complement of the lower one at every stage.
All the displayed angles are nonzero, nondyadic rationals with odd reduced
denominators and the displayed exact doubling periods. Consequently no choice
between the two expansions of a dyadic rational enters the substitution.

To justify that these are actual root rays, start from the two rays landing
at the root of `A`. By the landing implication following Zakeri (2.2), applying
`S` gives rays landing at the image of that root under `iota_A`. Tuning respects
roots, so this image is the root of `A*A`. Applying the same argument again
gives the two rays at the root of `A*(A*A)`. Period multiplication gives period
27, and associativity identifies this component with `A*A*A`.

## 4. Proof of center identification

Let `H_*` be the hyperbolic component containing `c*`. The exact certificate
shows that `c*` is a real center of exact period 27. BFKP §4.4, p. 10 therefore
identifies the two rays at the root of `H_*` as the rays at

\[
\theta(c_*)=\frac{59914011}{134217727},\qquad
-\theta(c_*)=\frac{74303716}{134217727}.
\]

Section 3 gives the same rays at the root of `H=A*(A*A)`. In particular, the
single ray at `59914011/134217727` lands at the root of both `H_*` and `H`.
Its reduced denominator is odd. The unique-component statement in Zakeri
§2, p. 5 forces `H_*=H`. The multiplier conformal isomorphism gives precisely
one point of multiplier zero in that component. Since `c*` has multiplier
zero, it is its unique center. This proves the displayed claim.

The proof identifies the actual hyperbolic component, rather than only a
period, a matching finite word, or a candidate orbit permutation. The complex
parameter-ray implication is supplied explicitly by the cited source result.

## 5. Reproduction, dependencies, and boundary

Run from the repository root, using Python 3 with assertions enabled:

```sh
python3 -B research/independent_audits/verify_period27_center_tuning_identification.py
```

Recorded verification: **PASS**, Python **3.12.14**, November 6, 2026.

The program emits machine-readable JSON. It reports the Python version, exact
parameter bracket, arithmetic mesh, all 26 strict signs, the binary kneading
block, and all three rational tuning pairs. Its finite checks reuse only the
existing exact interval machinery and Python's standard-library rational
arithmetic. No floating-point root finder, ray plot, or numerical landing
estimate is used. It explicitly labels the analytic bridge as an imported
result rather than a machine-checked theorem.

This proves the old superattracting center's component identity. It does not
identify that center with a nonattracting tip parameter: its filled Julia set
has attracting Fatou components, so `K(f)=J(f)` is false there. Nor does this
note prove any puzzle-piece boundary identification, parameter-ray
correspondence beyond the component-root pair, polynomial-like domain,
ambient marked renormalization, uniform Carathéodory estimate, or any global
ledger obligation. Those are separate obligations. In particular the component identity
does not discharge an unverified hypothesis of a Kahn–Lyubich or Levin theorem.

**Attribution and review:** this note and checker were prepared with OpenAI GPT-6
assistance. No human specialist review is claimed. The mathematical content
imported from BFKP and Zakeri is attributed at its exact source location; the
repository's exact real-orbit certificate supplies the finite hypotheses.
