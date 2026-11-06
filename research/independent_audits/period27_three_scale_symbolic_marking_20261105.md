# A three-scale exact symbolic marking candidate at the period-27 quadratic center

**Update, 2026-11-06:** the [center-identification proof](period27_center_tuning_identification_20261106.md) now identifies the period-27 center with `A*A*A` and authenticates the component-root ray pair. This dated audit's earlier status language records the stage before that source bridge; its symbolic and real Markov computations remain unchanged.

**Date:** November 5, 2026. **Status:** Exact algebraic/finite combinatorial certificate and a reproducible 26-edge **real interval** Markov graph. **Not** a certified parameter-ray identification, Julia-side external-ray automaton, prime-end atlas, or Paper-1 sheet transport theorem. MLC and every global gate remain open.

## Research question and why this is a useful increment

Merged PR #10 supplies actual *complex* quadratic-like returns of periods 3 and 9, embedded in the same quadratic dynamical plane. It does not assign external rays, prime-end markings or covering sheets to their pieces. Recent work of Eduardo Ventilari Sodré, *Quadratic Hubbard trees, automata, and ray connections*, [arXiv:2611.04190v1](https://arxiv.org/abs/2611.04190) (November 2026), gives an algorithm for constructing a Hubbard-tree **external-angle automaton** from angled internal addresses, orbit portraits and forbidden regions. In particular, §§2.3 and 2.5 specify the angular kneading convention and tuning substitution. The older admissibility and Hubbard-tree classification is due to Bruin and Schleicher ([arXiv:0801.4662](https://arxiv.org/abs/0801.4662)); parameter-realized and abstract trees must not be conflated.

This increment performs the **arithmetic and symbolic prefix of the source-alignment job**, for one exact PCF center, without treating symbolic data as evidence of landing.

## The exact polynomial

Use the same unique algebraically isolated real parameter \(c_*\) as the merged real and complex 3/9 certificates:

\[
  \frac{K}{2^{128}}<c_*<\frac{K+1}{2^{128}},\qquad
  K=-607890580437450502081459824019535455703,
  \quad f_c(z)=z^2+c,\quad f_{c_*}^{27}(0)=0.
\]

Let \(x_j=f_{c_*}^{j}(0)\), with \(x_{27}=x_0=0\). The root-existence and uniqueness signs, strict parameter derivative, and all real orbit-sign comparisons are inherited from the **same** outward-rounded signed-integer arithmetic at resolution \(2^{-224}\), not a rounded value of \(c_*\). None of \(x_1,\ldots,x_{26}\) is zero. The critical period is exactly 27.

## The exact candidate angle pairs

The airplane component of period 3 has characteristic root-angle pair \(3/7=0.\overline{011}_2\), \(4/7=0.\overline{100}_2\) (see the standard parameter-ray descriptions and the paper's §2.5 tuning rule). Define the **binary substitution** \(\sigma(0)=011,\ \sigma(1)=100\). Iterating the substitution on each periodic word gives:

| Angular period | Lower candidate angle | Upper candidate angle | Periodic binary blocks |
|---|---|---|---|
| 3 | \(3/7\) | \(4/7\) | `011` / `100` |
| 9 | \(228/511\) | \(283/511\) | `011100100` / `100011011` |
| 27 | \(59914011/134217727\) | \(74303716/134217727\) | `011100100100011011100011011` / `100011011011100100011100100` |

The two numerators at each level sum to the denominator \(2^n-1\), giving reflection symmetry. Signed-integer modular arithmetic verifies that each angle has **exact** period \(n\) under doubling \(D(\theta)=2\theta\bmod1\). The word substitution obeys \(\operatorname{shift}^3\circ\sigma=\sigma\circ\operatorname{shift}\) for periodic binary words, so it is compatible with accelerating the angular time by a factor of three; this is only symbolic time compatibility.

### Three exact angular-kneading identities

For a periodic rational angle \(\theta\), define its kneading itinerary using the circle partition bounded by \(\theta/2\) and \((1+\theta)/2\), labeling the counterclockwise open half-circle between these preimages `1`, its complement `0`, and endpoints `*`. This is Sodré §2.3's definition. Every comparison of \(D^j\theta\) against the two partition endpoints is carried out using **integers over denominator \(2(2^n-1)\)**.

Both candidate angles at a given period have the same star-periodic kneading sequence:

| Angular period | Exact common angular kneading | \(\rho\)-internal address |
|---|---|---|
| 3 | `10*` | \(1\to2\to3\) |
| 9 | `10010110*` | \(1\to2\to3\to6\to9\) |
| 27 | `10010110110010110010010110*` | \(1\to2\to3\to6\to9\to18\to27\) |

For each `*`-periodic word, the script chooses the unique 0/1 replacement for `*` whose resulting periodic kneading sequence has the final period in its internal address. It then independently reconstructs that address from the exact \(\rho\)-operator, \(\rho(s)=\min\{k>s:\nu_k\neq\nu_{k-s}\}\). This calculation **does not assert an angled internal address or the rotation number of every bifurcation**: the address entries are un-angled.

## Why these words match the actual polynomial at all three scales

The derivative of the physical return at the critical point has the local expansion

\[
  f_{c_*}^p(z)=x_p+a_p z^2+O(z^4),\quad
  a_1=1,\quad a_{j+1}=2x_j a_j.
\]

The exact interval certificate gives \(a_1>0,\ a_3<0,\ a_9>0\). Thus, for the return \(F_p=f^p\), the orientation-normalized **real** critical-value kneading symbol of \(F_p^j(0)=x_{pj}\) is `1` if \(a_p x_{pj}<0\), `0` if \(a_p x_{pj}>0\), and `*` on return to zero. This is a **declared real sign convention**; its exact match with an angular kneading sequence is a computed identity, not a theorem identifying the corresponding rays.

| Physical return | Relative critical period | Orientation sign | Verified oriented real kneading | Matching angular period |
|---|---|---|---|---|
| \(f\) | 27 | \(+\) | `10010110110010110010010110*` | 27 |
| \(f^3\) | 9 | \(-\) | `10010110*` | 9 |
| \(f^9\) | 3 | \(+\) | `10*` | 3 |

**This is the primary concrete advance:** three different physical return times agree, under the correct orientation convention, with the three scales of the *same* tuning substitution. It prevents the common error of comparing an angular word at a shorter return scale to the unadjusted sign word of the original quadratic.

## A second exact artifact: a 26-edge real Markov spine

The 27 distinct points \(\{x_0,\ldots,x_{26}\}\) can be strictly sorted from the outward interval enclosures. The extreme points are \(x_1=c_*<0\) and \(x_2=c_*^2+c_*>0\). The certificate verifies \(|x_1|>|x_2|\); since \(0\) is among the orbit vertices,

\[
 f_{c_*}([x_1,x_2])=[x_1,x_2].
\]

Order the orbit points and join consecutive vertices by closed real intervals. No edge contains the critical point 0 in its interior; \(f\) is strictly monotone on each edge, and each pair of image endpoints is again from the 27-cycle. Therefore every edge maps onto a consecutive union of Markov edges. All resulting directed incidences are **exact** and reproducible, without sampling a single orbit point numerically.

The 26 rows are provided in [`results/period27_symbolic_marking.json`](../../results/period27_symbolic_marking.json), along with the exact vertex order, a SHA-256 fingerprint of the adjacency list and the nested interval endpoints. In the 0-based ordering, the period-3 restrictive interval spans vertex ranks 9–17 and the period-9 interval spans 12–14. The graph is an **invariant real Markov partition**; we emphatically do **not** claim this graph is Sodré's two-sided **external-ray** automaton or that each edge corresponds to one accessible prime end.

## Reproduction and status

~~~sh
python research/independent_audits/verify_period27_symbolic_atlas.py --check-manifest
python research/independent_audits/verify_period27_symbolic_atlas.py --print-json
~~~

The first command checks the root isolation, all orbit interval orders, all rational-angle arithmetic, every return-kneading identity, all internal addresses, and full byte-for-byte equality of the machine-readable manifest. It requires only Python's standard library and the existing certified dyadic interval helper.

**Exact mathematical scope:** one fully specified PCF real quadratic; three symbolic angular periods; one real Markov partition. This is a novel **project-specific compilation**, not a claim of new classical kneading/tuning theory, a new MLC parameter class, or a completed KL source alignment.

## Next noncircular theorem and first-failure tests

The useful follow-up is a *source-locked real-PCF tuning identification*:

1. **Parameter identification.** Establish from a precise classical real-kneading rigidity/tuning theorem (not merely the string identity) that the algebraic \(c_*\) belongs to the triple-airplane tuning component with the above characteristic period-27 parameter ray pair. State the theorem and its hypotheses exactly; if it does not apply, record the first mismatch.
2. **Landing and orbit portrait.** For that actual parameter, certify landing and separation of all rays and characteristic points **used by the 3/9 puzzle construction**, not just the two candidate root angles. A finite angular language alone is not sufficient.
3. **Prime-end and sheet transport.** On the same physical germ, compare both 3/9 return scales, source KL puzzle pullbacks, prime-end cyclic order, the canonical localization sheet groupoid and protected obstacles. Test whether the 9-to-3 forgetful map identifies sheets or accesses that the marked construction must retain.
4. **Nonattracting transfer.** The exact \(c_*\) lies in a superattracting parameter region and fails Paper 2's \(K(f)=J(f)\) standing hypothesis throughout the certified nearby disk. A separate suitable boundary or tip parameter, with fresh analytic proof, is required for the source-specific application.

A result satisfying steps 1–3 would turn the exact *candidate* atlas here into a mathematically grounded access and sheet certificate. A verified failure in step 3 would identify a concrete missing invariant. Until then **H1**, **H2**, **H3_COERCIVITY**, **H4**, UPTCR and MLC remain open, as does Paper 2's source-specific alignment for this example.

## Primary-source and attribution record

- Eduardo Ventilari Sodré, *Quadratic Hubbard trees, automata, and ray connections*, [arXiv:2611.04190v1](https://arxiv.org/pdf/2611.04190) (November 2026), §§2.3, 2.5 and §§3–4. This supplies the angular kneading definition, tuning rule and the stated *full* external-ray automaton problem; it is **not** an endorsement of this archive.
- Henk Bruin and Dierk Schleicher, *Admissibility of kneading sequences and structure of Hubbard trees for quadratic polynomials*, [arXiv:0801.4662](https://arxiv.org/abs/0801.4662); journal publication in *Journal of the London Mathematical Society* (2008). Distinguishes realizable versus abstract kneading data.
- Adrien Douady and John Hubbard, *On the dynamics of polynomial-like mappings*, *Ann. Sci. Éc. Norm. Sup.* **18** (1985), 287–343, for the polynomial-like framework used in merged PR #10.

**AI assistance and review:** OpenAI GPT-6 assisted with research search, candidate discovery, exact integer implementation, test design and writing under the repository steward's direction. The exact certificate is deterministic and separately checked in GitHub Actions; the source-level landing and marking argument has **not** been proven, and independent specialist referee review has **not** been completed. The released manuscript PDFs, proof ledger and global claim statuses are unchanged.
