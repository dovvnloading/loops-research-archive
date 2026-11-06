# An exact nonattracting 3/9 quadratic: Misiurewicz tip, actual landing rays, and a physical access collision

**Date:** 2026-11-06. **Evidence:** exact signed-dyadic interval certificate plus explicitly cited classical theorems. **Scope:** one real postcritically finite (strictly preperiodic) quadratic polynomial, two real restrictive returns, external parameter/dynamical rays, and critical-point accesses. This does **not** construct the Kahn–Lyubich two-scale puzzle/prime-end/localization-sheet atlas. It does not prove H1–H4, universal tower closure, or Mandelbrot local connectivity (MLC).

## 1. Why a new parameter is necessary

The period-27 center `c_*` in the archive has `f_c^27(0)=0`. Since `f'_c(0)=0`, the return `f_c^27` has a **superattracting fixed point** at `0`. A sufficiently small open disk is attracted to the periodic cycle. Thus the filled Julia set has nonempty interior and `K(f_c) != J(f_c)` at that center. This strictly contradicts Paper 2's hypothesis H3; no choice of external ray labels or finite sheet memory can change it. The same failure persists in the certified attracting parameter neighborhood already recorded in the archive.

The appropriate response is to construct a **different nonattracting parameter**, instead of promoting a false same-center Paper 2 application. The following one is explicit and has the same *real* outer/inner return periods 3 and 9.

## 2. The exact algebraic parameter and its orbit

Set `P_0(c)=0`, `P_{j+1}(c)=P_j(c)^2+c`, and

\[
G(c)=P_{18}(c)+P_9(c),\qquad
K=-607918036626757496169199575185708826140.
\]

**Theorem A (an exactly isolated Misiurewicz parameter).** There is exactly one real `c_tip` in the rational interval

\[
\boxed{\quad\frac{K}{2^{128}} < c_{\mathrm{tip}} < \frac{K+1}{2^{128}}\quad}
\]

such that `G(c_tip)=0`. It satisfies

- `-2<c_tip<-1`, with `c_tip ≈ -1.7865105445443247573853` (display only);
- the critical point has **exact preperiod 10 and eventual exact period 9**;
- the resulting 9-cycle is repelling and its return multiplier is strictly between 3 and 4;
- all first 19 orbit points `x_j=P_j(c_tip)` for `j=0,...,18` are pairwise distinct;
- `c_tip` lies more than `2^-32` away from the previously certified period-27 center, so the center's small attracting disk has not been silently reused.

**Proof and exact certificate.** The companion Python verifier uses an interval `[a,b]` represented by signed integers in units `2^-224`. Addition is exact. Multiplication encloses the minimum/maximum of the four corner products after rounding outward; squaring takes lower bound zero if the interval crosses zero. Induction gives enclosure for every `P_j(c)` on the whole parameter interval. Simultaneously, the derivative recursion

\[
D_0=0,\quad D_{j+1}=2P_jD_j+1
\]

is enclosed for all parameters (the recurrence is the genuine calculus derivative by elementary induction). At the two *exact rational* bracket endpoints, the verifier certifies `G(K/2^128)>0` and `G((K+1)/2^128)<0`, and throughout the entire bracket it certifies

\[
-71<G'(c)<-70.
\]

The intermediate value theorem and strict derivative bound give the existence and uniqueness. At that root, `x_18=-x_9`. Evenness of `f(z)=z²+c` then gives `x_19=f(x_18)=f(-x_9)=x_10`; forward iteration gives `x_{j+9}=x_j` for all `j>=10`. All `x_0,...,x_18` are pairwise distinct by strict disjoint interval enclosures, proving that no earlier entry into the cycle or smaller cycle is possible. The actual multiplier

\[
(f^{9})'(x_{10})=\prod_{j=10}^{18} 2x_j
\]

is enclosed strictly between `3` and `4`, establishing repulsiveness. These tests use no floating-point arithmetic. The polynomial is therefore a **real Misiurewicz quadratic**; standard Fatou–Julia theory then supplies `K=J` (a strictly preperiodic-to-repelling critical orbit has no bounded periodic Fatou basin; there are no wandering Fatou components). This last implication is an imported analytic result, not something computed by the script. \(\square\)

## 3. Two *physical real* restrictive intervals at the new point

Define

\[
I_3=[x_6,x_3],\qquad I_9=[x_9,x_{18}].
\]

The exact interval checker proves the **strict** nesting `I_9 ⊂ int(I_3)`, `x_9<0<x_18`, and distinct, pairwise disjoint physical images `f^j(I_p)` for `0<=j<p` at each `p=3,9`. All nonzero intermediate images avoid `0`, so `f^p` has no additional critical point on `I_p`; its only critical point is `0`.

For `p=3`, the endpoint/critical-value images are `f³(x_6)=x_9`, `f³(x_3)=x_6`, and `f³(0)=x_3`; the first is strictly inside `I_3`. For `p=9` they are `f⁹(x_9)=x_18`, `f⁹(x_18)=x_27=x_18`, and `f⁹(0)=x_9`. Here `x_27=x_18` follows from `x_19=x_10`. Monotonicity on the two sides of the sole critical point shows

\[
\boxed{f^3(I_3)=I_3,\qquad f^9(I_9)=I_9.}
\]

This certifies real restrictive first returns in one physical dynamical plane, independently of the center's attracting-window complex disks. **It does not prove that these particular real intervals extend to the complete KL puzzle with all desired Jordan pieces, access sides, and source sheet groupoid.** The complex quadratic-like realizations at this *new* parameter require their own domain/source verification.

## 4. Exact parameter rays **and** dynamical rays at the Misiurewicz tip

The signed critical-value orbit `x_1,x_2,...` has symbols `1` for negative and `0` for positive. The exact checker finds a nine-symbol prefix and a nine-symbol repeating block:

```text
critical-value sign itinerary: 100101101 (100101100)∞
```

S. Zakeri, *External Rays and the Real Slice of the Mandelbrot Set*, §3, Theorems **3.1** and **3.3** (printed pp. 8–9), proves for a real Misiurewicz parameter that its unique conjugate parameter-ray pair lands at that parameter, and its corresponding **dynamical-plane** ray pair lands at its **critical value**. His proof of Theorem 3.3 explicitly computes the lower angle `τ` from the signs `ε_j=sgn(f^j(c))`: start with digit `t_0=0`, retain the current digit for `+` and flip for `−`. This is *applicable here because the new parameter is Misiurewicz*, unlike the earlier center-to-root comparison, which cannot be justified by simply equating words.

The resulting binary angle is

\[
\tau(c_{\mathrm{tip}})=0.\underbrace{011100100}_{9\text{ digits}}
\overline{\underbrace{100011011}_{9\text{ digits}}}
=\boxed{\frac{116791}{261632}}.
\]

The other angle is `1-τ=144841/261632`. They are **preperiodic** under doubling (strict preperiod 9, exact tail period 9), not the **periodic root** angles of the hyperbolic component. The exact checker independently verifies their 9+9 doubling itinerary, matching angular kneading, symmetry, and Zakeri's Theorem **3.7** angle-admissibility condition. Zakeri's Theorem **3.1** supplies the actual landing statements; exact arithmetic by itself does not.

**A second source match (actual tuning-tip identity).** Zakeri's §2, equation (2.2), describes Douady–Hubbard tuning on **parameter** angles. The airplane substitution is `σ(0)=011`, `σ(1)=100`; applying it twice gives `σ²(0)=011100100` and `σ²(1)=100011011`. At the Chebyshev tip `c=-2`, the unique ray angle `1/2` has binary expressions `0.1000...` and `0.0111...`; substituting both gives **exactly the two fractions above**. Since rational parameter rays have unique landing points, the tuning theorem and the independently recovered ray pair show that

\[
\boxed{c_{\mathrm{tip}}=\iota_A(\iota_A(-2))}
\]

where `A` is the *real period-3 airplane* component and `ι_A` is the classical tuning embedding. This identifies the **twice-tuned real Misiurewicz tip**, not the different period-27 *superattracting center*; the latter component identity must be established separately using renormalization straightening/real kneading rigidity.

## 5. Four **actual** critical-point access rays; a first nonfaithful `f⁶` ray map

Because `f(z)=z²+c_tip` has the unique preimage `f^{-1}(c_tip)={0}` of local degree 2, each of the two rays landing at the critical value lifts to **two rays landing at `0`**. They are all distinct by their angles. There are no other rays at `0`: every ray there maps to a ray at the critical value, which Theorem 3.1 limits to the two named angles. The following is an **actual dynamical-plane landing table**, not a prospective Hubbard-tree edge table:

| Exact angle at `0` | `f` ray angle at `c_tip` | `f⁶` ray angle at `x_6` | Landing fact |
|---|---|---|---|
| `116791/523264` | `116791/261632` | `2327/8176` | Lands at critical point `0` |
| `144841/523264` | `144841/261632` | `5849/8176` | Lands at critical point `0` |
| `378423/523264` | `116791/261632` | `2327/8176` | Lands at critical point `0` |
| `406473/523264` | `144841/261632` | `5849/8176` | Lands at critical point `0` |

The four fractions are in strict cyclic angle order as displayed. For example, the distinct rays at `116791/523264` and `378423/523264` **both land at `0`** and are mapped by the actual physical iterate `f⁶` to the same ray at angle `2327/8176`, landing at `x_6`. This is a **genuine nonfaithful external-access map under the six-iterate time difference** between the 9- and 3-return clocks, now at a nonattracting parameter where `K=J`.

**Critical scope restriction:** `f⁶` on these identified critical-point ray accesses has not been shown to equal the *source-defined KL 9-to-3 prime-end or localization-cover functor*. This table does not name a KL puzzle depth, `O/ξ/η` access side, coset, or Paper-1 sheet. Thus it is an actual geometric *first-failure witness for an unmarked ray-forgetting map*, but **not** a certified failure of any genuine fully marked KL transport theorem. Nor does it identify all Julia-tree or automaton rays.

## 6. Dependency ledger and reproduction

| Obligation | Outcome |
|---|---|
| Exact nonattracting real parameter with period-3/9 restrictive returns | **Proved** (integer interval arithmetic + IVT/MVT) |
| Strictly preperiodic critical orbit, repelling period-9 cycle, `K=J` | **Proved**, with the last Fatou–Julia deduction imported |
| Exact rational **Misiurewicz-tip** ray and critical-value **dynamical** ray landing at `c_tip` | **Proved via Zakeri Theorems 3.1/3.3**, with all fractions checked |
| Identity with twice-tuned Chebyshev tip | **Deduced using Zakeri §2 angle tuning and unique rational-ray landing** |
| Four landing critical-point accesses and concrete `f⁶` ray collision | **Deduced from degree-two local preimage geometry**, checked angles |
| `c_*` equals triple-airplane *superattracting* center | **Still open as a separately documented straightening/kneading identification** |
| Source KL complete 9-to-3 marked atlas and Paper-1 sheet/coset transport | **Not established**; explicit puzzle depths, Jordan boundaries, prime-end sides, groupoids still missing |
| H1–H4, UPTCR, MLC | **Open; no changes** |

Run from repository root:

```sh
python research/independent_audits/verify_period27_misiurewicz_tip.py --check-manifest
```

The script uses **only Python standard-library integers and `fractions.Fraction`**. It checks the `2^-128` isolating interval, the strict derivative interval, first-return phase disjointness, real restrictive endpoints, the 9-cycle multiplier, all ray fractions, angle admissibility, and the `f⁶` collision, and compares its JSON output byte-for-byte with [`results/period27_misiurewicz_tip.json`](../../results/period27_misiurewicz_tip.json). It does not kernel-check the external analytic theorems, does not run floating-point ray tracing, and does not upgrade the source-locked 465-entry proof ledger.

**Primary-source reference:** Saeed Zakeri, *External Rays and the Real Slice of the Mandelbrot Set*, §2 pp. 4–7, formula (2.2); §3 pp. 8–10, Theorems 3.1, 3.3, 3.7 and Lemma 3.4. [Author's PDF](https://www.math.stonybrook.edu/preprints/ims02-02.pdf). Classical polynomial/renormalization straightening and the source KL paper remain separate inputs; no independent expert mathematical referee has confirmed this new archive deduction.

**Attribution and review:** OpenAI GPT-6 prepared the derived computation and argument using the preexisting archive and cited primary mathematics. The *source theorems* are imported, not claimed as newly proved. Mathematical interpretation should be independently reviewed before use in a peer-reviewed manuscript.