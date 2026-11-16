# Native Wave Transfer Laboratory — satellite marking v2 (additive)

**Contract and scope.** v1 (`SPECIFICATION.md`, `regenerate.py`, primitive p=4,
period-four-center refusal, and period-two Misiurewicz-tip refusal) stays
unchanged. This v2 records **what the published satellite theory defines**, and
separately labels exact deductions and missing analytics. In particular it is
*not* an extension of Kahn–Kapiamba–Lyubich's (KKL) primitive Wave Lemma to a
satellite. Per-field citation and status are mandatory and machine-checked in
[`source_contracts/satellite_v2_field_sources.json`](source_contracts/satellite_v2_field_sources.json).

## Primary sources (exact locations)

* **[AL, §2.10, conditions R1–R3 and final paragraph]** Artur Avila and
  Mikhail Lyubich, *The Full Renormalization Horseshoe for Unimodal Maps of
  Higher Degree*, Publ. Math. IHÉS (2011),
  [DOI:10.1007/s10240-011-0034-2](https://www.numdam.org/item/10.1007/s10240-011-0034-2.pdf).
  The little filled Julia sets are `K(g_m)=f^m(K(g))`; R3 permits contacts at
  a marked beta-fixed point, and the final paragraph calls the renormalization
  **satellite** iff the little Julia sets touch. The beta point is marked, not
  counted as a new attached tree component.
* **[Ly, Part II §9.1, “Space between Julia bouquets”]** Mikhail Lyubich,
  *Dynamics of Quadratic Polynomials, I–II*,
  [text](https://www.math.stonybrook.edu/~mlyubich/Archive/Selected/puzzle.pdf).
  Touching little Julia sets at a common periodic point form a *bouquet*.
  This distinguishes phase contact from disjoint primitive little Julia sets.
* **[KL, §§1, 2.2]** Jeremy Kahn and Mikhail Lyubich, *A priori bounds for
  some infinitely renormalizable quadratics: III. Molecules*,
  [arXiv:0712.2444](https://arxiv.org/abs/0712.2444). The molecule condition
  keeps primitive renormalization combinatorics away from satellite types;
  it supplies **no satellite Wave transport theorem**.
* **[DLS, Definition 2.1, §§2.1–2.2, Appendix C]** Dzmitry Dudko,
  Mikhail Lyubich and Nikita Selinger, *Pacman Renormalization and
  Self-Similarity of the Mandelbrot Set near Siegel Parameters*, JAMS 33
  (2020), [DOI:10.1090/jams/942](https://doi.org/10.1090/jams/942).
  Sector cuts, boundary identifications and rotation data are part of pacman
  renormalization, **not** definitions of an `iota^*` Wave on this quadratic-like
  slit. Appendix C discusses the Molecule Conjecture; it does not license
  identifying a pacman sector with a KKL proper-path restriction.
* **[DS, §2, paragraph on Hubbard-tree edges following Definition 2.2,
  Lemma 2.3]** Dzmitry Dudko and Dierk Schleicher, *Core Entropy of Quadratic
  Polynomials*, Arnold Math. J. 6 (2020),
  [DOI:10.1007/s40598-020-00134-y](https://doi.org/10.1007/s40598-020-00134-y).
  The finite postcritically finite Hubbard-tree Markov incidence matrix and its
  Perron root are **different** from a KKL old-edge Wave transfer operator.
* **[KKL, arXiv:2606.27272v1, §§2.3–2.5, §6.1 Props. 6.5–6.6,
  Appendix A.1, A.3.2–A.3.4]** Jeremy Kahn, Alex Kapiamba and Mikhail
  Lyubich, *MLC for parabolically bounded primitive renormalization*,
  [v1](https://arxiv.org/abs/2606.27272v1).
  The primitive disjoint-tree ideal boundary, pullback immersion, proper path
  filters and extremal Wave widths are **not** established in those sections
  for contacting little Julia sets. The unchanged v1 proof and manifests
  supply primitive benchmark values, not satellite facts.

## Satellite mark: two *ambient* phases, one *central-return* little Julia set

Let `P(c)=c^3+2c^2+2c+2`, `c_*` its unique real zero, `a=c_*^2+c_*`,
`f(z)=z^2+c_*` and `G=f^2`. Retain the **existing** exact 128-bit adjacent
root isolator and uniform Rouché certificate from the v1 tip refusal. The
central quadratic-like return is `G:V->U`, `U=D(0,1)`,
`V=component(G^-1(U),0)`, degree **2**. Distinguish this from the global degree
**4** of `f^2`. Polynomial reduction modulo `P` gives

`f(a)=f(-a)=-a`, `f(c_*)=a`, `f(-a)=-a`,
`G(z)+a=(z^2-a^2)(z^2-c_*^2)`.

Consequently the **return** has the *single* invariant inner interval
`K0=[-a,a]`; its real tree pullback in `V` is `Tprime=T=K0`. The **ambient**
`f`-phases of the renormalization are `K0` and `K1=f(K0)=[c_*,-a]`, with
`K0 intersect K1={-a}`. Also `f(K1)=K0`. This is the contact bouquet in
[AL §2.10; Ly Part II §9.1], not three disjoint central-return intervals.
The shared contact `q=-a` is **fixed under f**, with negative repelling
multiplier `f'(q)=-2a`; the two real incident arms exchange under `f`,
so the local cyclic arm rotation is **1/2** for `f`, and **0** for `G`.
This rotation is *derived from exact real dynamics*, not a claim that DLS
identifies a pacman for this specific example.

**Accesses must name the slit.** In `U\K0`, `q` is a *tip* of the return
slit and has one prime-end tip access. In the complement of the *ambient*
real bouquet `K0 union K1=[c_*,a]`, `q` is an *interior point* of the
interval and has two local sides (upper and lower). These are **different
complements**. [KKL Appendix A.1] motivates access marking, but the local
one-tip/two-side identification here is elementary planar slit topology;
its extension to the full canonical satellite prime-end/sector atlas remains
**cited-but-unformalized**, not a KKL theorem.

## Replacement for “attachment” and proper restrictions

* Keep **return inverse-tree attachments** as components of `Tprime\T`
  (KKL §6.1 on its primitive domain); here there are **none**. **Separately**
  record one **phase contact vertex** `q` joining the two ambient phases
  (AL §2.10; Ly §9.1). A shared contact is *not* an attachment or three new
  `small_julia_intervals` (those v1 values stay refused). This is an explicitly
  local bookkeeping split; AL/Ly do not define KKL `AttachmentCensus` v2.
* A curve with `q` in its **interior** does not lie in `U\K0` and is **not a
  proper curve in that complement**. A curve **ending at** the slit-tip access
  is a different object. Local lifts of such an endpoint have a computable
  unramified germ count, but the KKL proper-path/subordination filters for
  **whole paths** have no satellite definition here [KKL §6.1, Appendix
  A.1/A.3.2; DLS §2 cuts do not supply one]. No fake assignment to either
  upper or lower *ambient* side is allowed.
* Keep the operations typed separately: **covering** `f_*` is induced from
  `G:V\K0 -> U\K0`; **immersion pullback** `iota^*` is induced from the
  literal inclusion `iota:V\K0 -> U\K0` [KKL §6.1]. Since
  `G^-1(q) cap V={-a,+a}` and both derivatives are nonzero, a proper
  target slit-tip endpoint has **two local covering lift germs** (one at
  each source tip, both multiplicity 1). Inclusion has **one local germ** at
  `-a` (multiplicity 1). These are *local contact-endpoint multiplicities*,
  **not** the primitive `2/1` filtered full-sheet count, and are **not**
  complete atomic `f_*`/`iota^*` tables. Inclusion need not be globally
  proper on an arbitrary whole path.

## Independent finite edge invariant, and Wave boundary

The invariant **ambient** real Hubbard-tree hull `H=[c_*,a]` has vertices
`c_* < -a < 0 < a` and edges `E0=[c_*,-a]`, `E1=[-a,0]`,
`E2=[0,a]`. By interval monotonicity, `f(E0)=E1 union E2`,
`f(E1)=E0`, `f(E2)=E0`. The DS §2 convention, output edge in each row,
input edge in each column, yields

```
M = [[0,1,1],
     [1,0,0],
     [1,0,0]],
char_M(t) = t(t^2-2),  rho(M)=sqrt(2).
```

This matrix is **not** the v1 `G` old-edge matrix (the one-vertex central
return still has no old edges); comparing `sqrt(2)` to primitive
`(1+sqrt(5))/2` is a comparison of **different operators**, not a width
inequality or degradation argument. The Markov matrix is irreducible but
period-two imprimitive; its negative eigenvalue `-sqrt(2)` is not a Wave
loss. The rational/polynomial checks certify the image census and the
identity `M^3=2M` (and hence the stated Perron root).

A **marked KKL Wave** would need a specified target ideal-boundary
base/crest, admissible proper paths, their `iota^*` restrictions,
`f_*`-pushed endpoints and the extremal width of the resulting homotopy
family [KKL Appendix A.3.2–A.3.4]. Neither AL, KL, DLS nor KKL supplies the
necessary satellite-contact choice/filtration or a width-transfer theorem
for this physical example. **Do not invent one.** Satellite parent/child
**exact Wave widths are undefined** in this v2 contract (`null`, not zero),
and whether width is preserved, lost or forced to degrade is
**undetermined**. In particular the loss of the *primitive certificate* is
not a proof of loss of analytic width. DLS pacman sector moduli and the
DS Markov Perron root cannot be substituted for a KKL Wave width.

## Source status, reproducibility and guards

`source_contracts/satellite_v2_field_sources.json` cites each output leaf
(field paths include `primitive_comparison.p3.*` and `.p4.*`). Status
`exact-derived` means a strict rational/polynomial computation under the
existing input, **not** a result literally defined in the paper;
`published` would mean directly defined there; `unformalized` marks an
analytic input or absence of a source-defined extension. Unknown/new
fields, unknown source IDs and missing citation/status values fail closed.

`regenerate_satellite_v2.py --check` is read-only and compares the full
UTF-8 JSON serialization (sorted keys, 2-space indentation, terminal
newline, ASCII escaped) to the immutable manifest. Only `--write` can
regenerate it. It source-locks both primitive baseline manifest blobs;
**neither their bytes nor any v1 file is edited.**
Run `python -m unittest discover -s research/native_wave_transfer -p 'test_*.py' -v` for positive and adversarial cases. The CI step is
separate and does not freeze outputs.
