# Issue #40 — exact marked-cut resolution and total improper-end escape for a holomorphic Wave

**Date:** 2026-11-07. **Status:** two independently proved theorems on an *actual* quadratic-like immersion/covering: an exact quantitative formula for which near-saturation leaves remain admissible under a finite original marking, including the essential one-/two-atom exception; and an explicit full-width **failure of direct proper-path transport** through the immersion. This is an adversarial, source-typed bridge audit for [PR #50](https://github.com/dovvnloading/loops-research-archive/pull/50), not a prime-primitive KKL counterexample, a canonical Wave amplification theorem, or MLC.

**Source rules:** Kahn–Kapiamba–Lyubich (KKL), [arXiv:2606.27272v1](https://arxiv.org/html/2606.27272v1), Appendix **A.1** (a marked path is excluded if it is subordinate to a multi-interval of length at most two; original cuts are part of the data), **A.2.2–A.2.3** (valid lamination and the canonical +2 bound), **A.3.2** (the immersion `iota^*` is a *restriction* of TARGET proper paths, not a general pushforward of SOURCE paths), and §6.2 (breakable/unbreakable Wave splitting). In §6, the *native* marking is given by **sides of small-Julia vertices on the Hubbard tree**. A convenient refinement is not automatically that marking. PR #50 supplied the exact Joukowski source family and the unmarked semicircle modulus.

## 1. The genuine holomorphic source and its two distinct ideal ends

Fix `0<h<=1/4` and `0<epsilon<sin(h/2)`. Set

\[
 c=-1-\epsilon,\quad b=\epsilon(1+\epsilon),\quad
 P_c(z)=z^2+c,\quad T=[c,b],\quad T'=[c,-c],\quad
 X=(b,-c]. \tag{1}
\]

Choose `U=D(0,5)`, `U'=P_c^{-1}(U)`, `V=U\setminus T`, `V'=U'\setminus T'`. Then `iota:V'\hookrightarrow V` is the **actual inclusion immersion**, and `P_c:V'->V` is the separate unbranched degree-two covering. The exact Joukowski coordinate on the source inner boundary is

\[
 \Psi_{T'}(w)=\frac{1+\epsilon}{2}(w+w^{-1}),\qquad
 \Psi_{T'}(e^{i\theta})=(1+\epsilon)\cos\theta.\tag{2}
\]

The true excess-tree Carathéodory boundary is the closed ideal arc

\[
B_X=\{|\theta|\le\arccos\epsilon\},\quad
\tau B_X=B_X+\pi,\quad \tau(w)=-w.
\]

They are disjoint for `epsilon>0`, separated by gaps of size `d=2arcsin(epsilon)`. Write `r0=arcsin(epsilon)`, `R=h/2`. In the conformal logarithmic cylinder `0<t<h`, define the **actual source proper path**

\[
\gamma_r(s):\quad (t,\theta)=(r\sin s,\ \pi/2+r\cos s),
\quad 0<s<\pi,\quad r_0<r<R.\tag{3}
\]

Its two inner-boundary physical limits under (2) are

\[
 x_r=(1+\epsilon)\sin r,\qquad
 y_r=-(1+\epsilon)\sin r.\tag{4}
\]

Because `epsilon<sin r<1`,

\[
 b=(1+\epsilon)\epsilon<x_r<1+\epsilon=-c,
 \qquad c=-(1+\epsilon)<y_r<0<b.\tag{5}
\]

Thus **one endpoint belongs to `X\setminus\{b\}\subset V`, while the other belongs to the old tree `T`**. Both are true boundary ends of the source `V'` (since `T'` contains both). The companion packet centered at `3pi/2` has the same two endpoint types with their order reversed. No pointwise boundary extension of `iota` is assumed.

## 2. Theorem A — an exact original-marking resolution law

Let `I` be **any finite ideal marking** of the source inner circle, with marked cuts `C(I)`; outside-boundary marking plays no role in the calculation. For the gap center `theta0=pi/2`, work in the unwrapped angular interval `(theta0-R,theta0+R)`. Form the multiset of positive distances `|e-theta0|` of *distinct* marked cuts `e` lying in this interval; there are no repeated cuts, though two cuts can have equal distances. Let

\[
 s_2(I)=\begin{cases}
 \text{second-smallest of these distances},&\text{if at least two cuts exist},\\
 R,&\text{otherwise}.
 \end{cases}
\]

All assertions can ignore the **finitely many** radii for which a leaf endpoint lands exactly on a marked cut; deleting finitely many radii does not change extremal width.

**Theorem A (exact cut-scale sieve, with the global two-atom exception).** Write `N` for the number of marked open atoms on the inner boundary circle. If `N>=3`, a leaf `gamma_r` of (3) is an admissible path in KKL Appendix A.1 for the marking `I` **if and only if**

\[
\boxed{r>s_2(I)\quad (N\ge3).}\tag{6}
\]

If `N<=2`, **no such leaf is admissible**, regardless of the locations of its cuts: the *entire* inner circle is already a marked multi-interval of length at most two, to which these boundary-parallel paths are subordinate.

Consequently the sublamination `S_+(I)` of admissible leaves has **exact** conformal width

\[
\boxed{
\mathcal W(S_+(I))=
\begin{cases}0,&N\le2,\\
\displaystyle\frac1\pi\left[\log\frac{R}{\max(r_0,s_2(I))}\right]_+,&N\ge3.\end{cases}
}\tag{7}
\]

where `[x]_+=max(0,x)`. The original, unfiltered family has width `(1/pi)log(R/r0)`. Formula (7) holds regardless of whether the admissible leaves use one or several marked homotopy classes; it is a width statement for their explicitly defined **source sublamination**, not an assumed original-KKL canonical WAD coefficient.

*Proof.* A lifted leaf `gamma_r` is boundary-parallel in the annulus to the **unique** short angular support `[theta0-r,theta0+r]`; the opposite boundary arc represents the other winding class, not the same proper-path homotopy rel endpoints. For generic `r`, the marked length of the smallest connected marked support of the short boundary-parallel arc is `min(N, 1+#\{e\in C(I):|e-theta0|<r\})`: the cap at `N` matters when the short support crosses **every** marked cut and comes back to the initial atom. When `N>=3`, this length exceeds two exactly if at least two cuts lie in the open angular support, establishing (6). When `N<=2`, the entire circle of length at most two supports every such leaf, so none is admissible. For `N>=3`, the admissible radii form `(max(r0,s2),R)`, up to finitely many points; for `N<=2`, this family is empty. On the corresponding Euclidean half-annulus, admissibility of a conformal metric for the semicircles forces `\int_0^pi rho(r,s)r ds>=1`; by Cauchy–Schwarz the energy is at least `(1/pi)\int dr/r`. The metric `rho=1/(pi r)` on the admitted half-annulus and zero elsewhere attains equality, proving (7). Deleting finitely many radial leaves changes neither bound. `□`

**Sharp examples and marking-minimality.**

- **Adversarial two-cut marking with both cuts inside the short gap:** choose just the two gate cuts `theta0-r0,theta0+r0`, and take `r0<r<R`. The old unqualified second-nearest-cut rule would falsely call every leaf admissible. In fact there are only `N=2` marked atoms; the full inner circle is a multi-interval of length two, so **every leaf is inadmissible**. This is the precise reason for the `N>=3` hypothesis in (6) and (7).

- **Six-cut marking of PR #50:** cuts at both attachment gates and at the two gap centers; each gap has `s2=r0`, so **all** near-saturation leaves are admissible.
- **Four-cut gate marking:** use only the four *real, physical* prime-end accesses of `+b` and `-b` (the two endpoints of each attached/deck-opposite block). There are exactly two marked cuts at distance `r0` from each gap center. Both packets are still fully admissible; the extra critical-point cuts of PR #50 are **unnecessary** for this particular statement. Each short-gap leaf has minimal marked support length **three**, not four.
- **Coarse two-atom marking:** cut at the two gap centers `pi/2,3pi/2`. Each packet has only one cut in its `R`-neighborhood, so `s2=R` and **no leaf** is admissible despite unchanged positive geometric width.
- For **both** disjoint packets to admit even a nonempty open range of radii, each of the disjoint angular neighborhoods of its gap center must contain at least **two** original cuts. Thus at least **four** distinct inner cuts are necessary, and the gate marking attains the minimum. This counts **source marking** cuts, not original KKL vertices.

There is also an exact **fractional-loss law**. Suppose `R` is fixed, `r0->0`, and a moving marking has at least three inner atoms and two local cuts at distances `s2=r0^beta` for some `0<beta<1`. Then

\[
 \boxed{\lim_{r_0\to0}\frac{\mathcal W(S_+(I))}{\mathcal W(S_+)}=\beta.}\tag{8}
\]

If `s2` remains bounded away from zero (or fewer than two local cuts exist), the ratio is zero. If `s2=O(r0)`, the ratio is one. **Thus the native marking's angular cut scale, not just its number of atoms, controls the leading logarithmic Wave width.** In a genuine KKL stage the needed cut locations must be obtained from *its actual original vertex-side marking*, never supplied by refinement after the fact.

## 3. Theorem B — the *whole* wide source packet loses a proper target end

**Theorem B (actual all-leaf improper-end escape).** For every `r0<r<R`, the **direct immersed image** `iota∘gamma_r` is **not a proper path in `V`**. Indeed its one end converges to the point `x_r` of the **interior** of `V`, whereas the other approaches `T`. The same is true of every leaf of the opposite packet `S_-`. Consequently no nonempty sublamination of these explicitly constructed packets has a proper *leafwise direct image* under the inclusion immersion; this holds **for every choice of the source ideal marking**. Nevertheless, when the four-cut or six-cut marking is used, the source lamination has the exact diverging width

\[
 \boxed{\mathcal W(S_+)=\frac1\pi\log\frac{h}{2\arcsin\epsilon}\to\infty
 \quad(\epsilon\downarrow0).}\tag{9}
\]

In particular, for every `M>0`, there is an actual degree-two quadratic-like covering/immersion and an Appendix-A-admissible marked source Wave of width `>M` whose **every leaf has an improper direct immersion image**.

*Proof.* Equation (5) shows `x_r` lies in the open target region `U\setminus T`: it is strictly to the right of the old segment endpoint `b` and strictly inside the disk `U`. Select a closed Euclidean disk `K_r` centered at `x_r`, of radius less than `(x_r-b)/2` and less than `(5-x_r)/2`; then `K_r\Subset V`. A terminal subarc of `iota∘gamma_r` lies in `K_r`, so the inverse image of `K_r` in the leaf parameter interval is not compact: the immersed path is not proper. Equation (5) also proves the second end lies on `T`, hence it remains proper. The opposite packet is the same calculation under angular translation by `pi`. The unfiltered modulus (9) is the exact semicircle calculation of PR #50; with the four-cut marking Theorem A confirms admissibility for every generic radius, and source canonical maximality yields the corresponding `W_can >= [W(S_+)-2]_+` for its one marked arc class. Choosing `epsilon` sufficiently small makes the right-hand side arbitrarily large. `□`

**Crucial typing caveat.** KKL A.3.2 defines `iota^*` by **restricting TARGET proper paths** to their proper SOURCE components. A source leaf whose **direct image** is not proper can nevertheless arise as a *broken source component of the restriction of a longer target path*. Theorem B does **not** say that `iota^*` of every target Wave is empty, nor that KKL's breakable/escape estimates are false. It proves a sharp **non-implication**: arbitrary large source-Wave/canonical-WAD width cannot be pushed *directly* through a nonproper immersion to obtain a positive target proper-Wave width. Such width requires **escaped-end accounting, a valid continuation, or a separately proved geometric domination**.

## 4. What this resolves and what it leaves open

For the explicit holomorphic test family, the old idea “wide source deck-odd full condenser => wide properly transported Wave” is false without additional proper-end hypotheses. The two distinct obstructions have now been measured exactly:

1. **Marking resolution:** a source Wave retains width only down to the scale of its **second-nearest original marked cut**, formula (7). Four genuine attachment/deck-opposite gate cuts suffice in this example, but KKL's original small-Julia marking has **not** been proved to supply them.
2. **Immersion escape:** even at full marking resolution, every semicircle leaf ends at a physical point of `T'\setminus T` that is **interior in the target**, formula (5). Entire unbounded source Wave width can fail direct proper transport.

This suggests a falsifiable next native theorem: under a true prime-primitive KKL critical attachment, either its original vertex-side marking has the two required cut accesses on a proof-used gap *and* its proper-path restriction contributes a quantitatively charged surviving/escaped WAD packet; **or** one must switch to source-defined saturation or an independently justified vertical-width/Shift-Lemma alternative. Neither that dichotomy nor the WAD comparison is yet proved.

The two-cut exception is a mathematical scope correction found during PR #51 review; it changes neither the four-/six-cut witnesses nor the direct-immersion escape theorem. The exact physical parameter family here is attracting of period two, with an **invariant selected slit**, not the complete KKL prime-primitive Hubbard tree. The immersion result is source-authentic for these real holomorphic sets, but it is **not** a counterexample to the intended KKL Wave Lemma or MLC. All ledger statuses remain OPEN, including Issue #40, native interval-growth nonreturn, Wave amplification, H1–H4, and MLC. Independent specialist review and novelty assessment remain necessary. OpenAI GPT-6 assisted this proof, counterexample design, and exact verification.
