---
ledger: NOV26_OPEN_OPTIMAL_LIMIT
result: partial
ai: OpenAI ChatGPT, GPT-6 Astra Pro; research, Lean development, and independent AI review
human_review: none
---

<a id="child-wave-limit-20261128"></a>

# Actual source exhaustion and the complete geometric child limit

Ledger statement being addressed:

> Canonical optimal widths and convergence: Exact W_p*, equality W_p*=W_p,2*, optimizer attainment and convergence to the limiting-domain maxima remain open (F16).

## Claim

**Development checkpoint: Lean compilation is pending.** The mathematical
statements below have been implemented, but they are not certified until
the unchanged weighted workflow builds them and completes its transitive
proof audit. The external KKL-width identification is a separate, still
unproved boundary described below.

Write `f_c(z)=z^2+c`, `x_j=f_c^j(0)`, `d=x_p>0`, and

\[
 U_p=D(0,2^{-p}),\qquad
 V_p=\operatorname{component}_0((f_c^{p})^{-1}(U_p)),\qquad
 \widehat V_p=d^{-1}V_p.
\]

For every certified actual tip of period `p >= 17`, the proposed source
theorem is the literal component inclusion

\[
 \overline D\left(0,\frac14\sqrt{\frac{2^{-p}}d}\right)
 \subseteq\widehat V_p,
 \qquad
 \frac{2^{\lfloor p/2\rfloor}}{16}
 \le\frac14\sqrt{\frac{2^{-p}}d}.
 \tag{1}
\]

The source is the repository's existing `TwoLevelOuterDomain.source`;
it is not replaced by the disk in (1). Every compact subset of the plane
is consequently eventually contained in these actual normalized sources.

The concrete child family uses the full slit `[-d,d]`, the upper-bank
ending intervals `(-x_(4p),x_(2p))` and `(x_(5p),-e_p)`, and the source
`V_p`. Here `e_p=d*actualAlpha` is a proved fixed point of the same
physical return, and `actualAlpha` is the unique fixed point in
`[0,23/20]`, lying in `(0.518,0.519)`. Leaves are arbitrary continuous
simple arcs. Their open traces avoid the slit, and a fixed-endpoint
homotopy inside `V_p` minus the slit connects each leaf to an upper-half
plane reference. A Wave has pairwise disjoint open leaves and Borel
geometric support. Its modulus uses Hausdorff arclength and area measure.

Let `C_p^geom` be the supremum of those moduli over **all** such Waves.
The limiting problem has the plane as ambient domain, slit `[-1,1]`, and
the six cuts

\[
 (-1,-Q_k^4(0),Q_k^2(0),Q_k^5(0),-\alpha_k,1),
 \qquad Q_k(z)=1-kz^2,
\]

where `k` is the existing uniquely certified limiting relation root and
`alpha_k` is its positive fixed point. Denote this full geometric
supremum by `C_infty^geom`. The implemented conclusions are

\[
 \frac1{3\pi}\le C_p^{\rm geom}<\infty,
 \qquad \frac1{3\pi}\le C_\infty^{\rm geom}<\infty,
 \qquad C_p^{\rm geom}\longrightarrow C_\infty^{\rm geom}.
 \tag{2}
\]

For `p >= 30` the implemented effective bound is

\[
 \left|C_p^{\rm geom}-C_\infty^{\rm geom}\right|
 \le 1600(6\cdot3906\cdot23646)4^{-p}C_\infty^{\rm geom}
       +\frac{3\pi}{\lfloor p/2\rfloor-8}.
 \tag{3}
\]

No optimizing family is assumed. The physical and normalized suprema
are proved equal by dilation, including transport of the whole relative
homotopy. The parameter is also connected to the archive's literal signed
chart in both directions; the final endpoint uses its unique selected
root rather than an unspecified sequence of choices.

## Evidence

Started from main commit `f05f1b9dc8f5fc6eeb68491da2eb44eca6d6cec9`,
then integrated main `637266b909d5e7566d8e39141f3b135e3405f38f`, which
contains the independent global physical-tip recognition and uniqueness
results used by the parameter bridge. Draft PR: #272.

The source chain is registered by `code/contribute.py lean-add`; the
existing contribution check and source-coverage check pass. These checks
are not Lean compilation. The first weighted run, `46130496356`, built
the six generic child modules (`Model`, `Transport`, `Compression`,
`Finite`, `Scaling`, and `Limit`). The second run, `46131510342`, also
built `ActualChildSource`, `ActualChildParameter`, `ActualChildMarks`,
`ActualChildSupremum`, and `ActualChildRate`. The positive test-family
module still had elaboration errors; the full endpoint and final
transitive proof audit remain pending.

| Module | Main theorem or role |
| --- | --- |
| `ActualChildSource` | `closedBall_subset_normalizedSource`, `innerRadius_lower`, `eventually_compact_subset` |
| `ActualChildParameter` | `ArchivedChart.restrictive_interval`, `archivedSelectedTip_iff_actualTip`, `actualTip_iff_eq_canonicalParameter` |
| `ActualChildMarks` | Literal physical cuts, unique actual fixed cut, quantitative convergence of all six marks |
| `ChildSlitModel`, `ChildSlitTransport`, `ChildSlitCompression` | Complete geometric families, source-contained homotopies, Borel whole-family transport |
| `ChildSlitFinite`, `ChildSlitScaling` | Finiteness and exact dilation equality |
| `ChildSlitLimit` | Uniform whole-family exhaustion with moving marks and moving sources |
| `ActualChildSupremum` | `physicalChildWidth_eq_actual`, `physical_child_optimum_real_converges` |
| `ChildSlitPositive`, `ActualChildPositive` | Hausdorff-to-angular length bridge and the uniform physical lower bound `1/(3*pi)` |
| `ActualChildRate` | `physical_child_real_error` |
| `SelectedChildLimit` | `selected_child_real_limit`, `selected_child_real_error`, `selected_source_exhaustion` for the unique archived chart root |

### Proof of the source estimate

Put `t=2^(-p)`, `S=4^p`, and `R=sqrt(t/d)/4`. The existing actual-tip
bound is `d <= 12*t^2`, while `S*t^2=1`. Thus

\[
 S(dR)^2=\frac{Sdt}{16}\le\frac{3t}{4}.
\]

The complete nonlinear orbit-displacement theorem applies on the scaled
disk `|w| <= dR` and gives `|f_c^p(w)-d| <= t/4`. Since
`d <= 12t^2` and `p >= 17`, its image lies strictly inside `D(0,t)`.
The scaled closed disk is connected, contains zero, and is contained in
the full polynomial inverse image. The connected-component theorem then
places every point in the **anchored central component** `V_p`. The
period-only lower radius in (1) follows from the existing bound on `t/d`.

### Why the chart bridge is a converse

`ArchivedChart` repeats the source's finite product, strict parameter
box, return size, tau range, positive prefix, and six signs. It contains
neither the collision equation nor an assumed invariant interval.
`ArchivedSelectedTip` adds precisely `x_(6p)+x_(3p)=0`.

For a chart point, put `r=200d`. The complete displacement bound controls
all intermediate phases on `[-r,r]`; they have the required branch signs.
The return is therefore decreasing with the squared real input there.
The same estimates give `|x_(2p)| <= 6d` and `|x_(3p)| <= 169d`.
If `x_(2p)<-d`, branch order forces first `x_(3p)<=x_(2p)` and then
`x_(4p)<=x_(2p)<0`, contradicting the chart's fourth-return sign.
Hence `[-d,d]` is invariant. The existing global physical recognition
theorem now applies, proving the reverse implication to `ActualTip`.
The forward implication follows from the existing sharp parameter and
itinerary estimates. Uniqueness is inherited from the existing physical
signed-tip theorem; it is not claimed as a new uniqueness theorem.

### Why taking the full supremum is legitimate

The cutoff estimate is uniform over the entire Wave. It splits its
trace family into bounded and escaping leaves, with a common admissible
escape density of area `3*pi/N`. The bounded subfamily's support is not
assumed Borel. Instead the entire original Wave and all its witnessing
homotopies are mapped by the existing soft coordinate compression. Its
image is Borel, stays in a bounded source, and retains every bounded leaf
literally. Six-mark transport then compares this bounded Wave with a
Wave in the actual source using the disk inclusion (1). This proves the
two inequalities before taking the supremum, so no extremizer or
measurable selection of near-extremizers is involved.

With the limiting endpoint radius below five, (1) pays for
`N=floor(p/2)-8` dyadic shells. The sum of the six mark errors is at most
`6*3906*23646*4^(-p)`. The existing scalar distortion estimate gives (3).

For positivity, concentric upper semicircles centered at `-3/4` with
radii in `(1/10,3/20)` fit the four literal electrodes and the unit disk
inside the normalized source. Lipschitz domination of Hausdorff measure
proves that every geometric admissible density is admissible for the
actual angular arclength integrals. The archived circular energy
inequality then gives `1/(3*pi)`. This is a positivity certificate, not
a claim that this circular witness is optimal.

Local Lean is not currently installed. The workspace filesystem has
approximately 14 MB available, whereas the official Lean 4.32.0 archive
alone requires approximately 559 MB. Compilation will therefore use the
existing pull-request CI; source checks alone are not proof validation.

## Dependencies

- `NearTwoTip.ActualTip`, its existing existence theorem, and
  `TwoLevelPerturbation.orbit_displacement` with its full nonlinear remainder.
- `GlobalPrimitiveTipUniqueness`, integrated from main, for physical
  signed-tip recognition and uniqueness. Its sharp chart estimates are
  reused and credited.
- `ActualParentMarks` for return normalization and parameter/orbit errors;
  `GlobalCrestSourceGates` for the actual positive fixed point;
  `LoopsLimitingCrestParameter` for the limiting root and orbit bounds.
- The archived Hausdorff modulus, whole-family compression, escape-density,
  small-mark motion, and real distortion arithmetic. Their analytic content
  is reused, with the source-domain homotopy requirement retained explicitly.
- The literal parameter and domain specification in
  `research/tip_family_theorem/THEOREM.md`, section 1; the child electrodes
  in `research/independent_audits/maximal_native_wave_20261123/H3_WIDTH.md`,
  sections 1 and 3. The latter's external ideal-boundary claims are not
  imported as Lean assumptions.

## Boundary

- **Validation:** all new theorem claims are pending compilation at this
  checkpoint. Source scans or a written proof do not substitute for CI.
- **Canonical quantity:** `C_p^geom` is the explicitly defined full
  source-contained geometric supremum above. This packet does not yet
  prove its equality with the external KKL A.1 optimum `C_p^+`. The
  archive's written ideal-slit atlas explains the intended equality,
  but no Lean ideal-boundary/subordination/minimal-base framework exists
  in the repository. Creating a new predicate with the name "KKL" would
  not prove that equality. Consequently (2)--(3) must not be advertised as
  a settled canonical KKL-width convergence theorem.
- **Reference class:** for an arbitrary ambient domain, `UpperClass`
  means that some source-contained upper-half-plane reference exists.
  It can be a union of relative classes when the domain has upper-half
  plane holes. This packet does not prove that all such references in
  the actual source are homotopic to one arbitrarily thin slit collar.
  That source-specific class identification is part of the missing
  canonical comparison, not something implied by the name `UpperClass`.
- **Direct canonical objects:** the source in (1) and the signed chart in
  the parameter bridge are literal objects from the archive. Those
  statements require no equality of width definitions. The disk is a
  proved subset of the source, not a replacement for it.
- **Novelty:** parent-supremum convergence, circular energy estimates,
  physical signed-tip uniqueness, and classical extremal-length
  continuity are prior work. Porting their arguments or compiling them
  does not itself establish new mathematics. The attempted new portion
  is the actual-source child convergence and its effective quantitative
  estimate. Worldwide priority is not certified by this packet or by CI.
  In particular, **qualitative compact exhaustion of the exact source is
  already written** in the November 16 limiting-gain note and the
  November 23 correction, in each case immediately after equation (5).
  Their scaling `lambda_p=-A_p` differs from `1/d_p` by the uniformly
  bounded positive factor `kappa_p`. The effective inradius in (1)
  strengthens that argument quantitatively; its mechanism is prior work.
  The child convergence method is a close extension of the archived
  parent method. Under a requirement of a decisive new canonical theorem,
  compiling this extension alone does not meet that requirement.
- **Extremal questions:** no exact optimal value, optimizer attainment,
  paired optimum, covering-compatible simultaneous maximizer, or equality
  `W_p^*=W_(p,2)^*` is established.
- **Global scope:** the ledger entry remains open. The work does not
  establish global H1--H4, UPTCR, or MLC, nor identify an entire maximal
  primitive component. The selected chart assertion is restricted to
  `p >= 17`.

## Attribution

The prior actual parent-width convergence and quantitative rate are
credited to `contributions/marked_wave_supremum_limit_20261127/NOTE.md`.
The complete child transport/cutoff argument is an adaptation of those
proofs, not an independent claim to their general method. Qualitative
source exhaustion is credited to
`research/independent_audits/tip_family_limiting_wave_gain_20261116/NOTE.md`
and `research/independent_audits/tip_family_wave_gain_correction_20261123/NOTE.md`,
in each case the paragraph after equation (5). The physical
parameter recognition and uniqueness are credited to
`contributions/global_primitive_window_20261128/NOTE.md`. The selected
slit atlas, child electrodes, independent extremal problems, and circular
test families come from the existing maximal-native-wave and earlier
gain packets cited there. All new implementation and review in this
packet were AI-assisted by OpenAI ChatGPT, GPT-6 Astra Pro. No human
mathematical review has been recorded.
