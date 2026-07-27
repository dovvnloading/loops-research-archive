# Quantifier-correct assembly of the virtual trichotomy

## 1. Purpose and status

KKL closes its static amplification/tame/wave trichotomy by choosing the
*wave-input* control parameter first, invoking the static split at that same
parameter, and then applying the tame theorem at the same parameter. This
ordering is logically essential.

This note proves the abstract quantifier assembly and records a countermodel
to an unsafe alternative. It does not prove the Virtual Section-4 Interface,
the Virtual Tame Full-Return Lemma, or the Virtual Long-Iterate Wave Lemma.

Primary source map:

- KKL Proposition 3.7: static split;
- KKL Proposition 3.8: same-parameter tame closure;
- KKL Proposition 3.9: source-stated wave closure which, if supplied as a
  hypothesis after its bounded-visits and stationary proof repairs, supplies
  a possibly larger wave-input parameter for a requested output factor;
- proof of KKL Theorem 3.6: composition in precisely this order.

See
[KKL](https://arxiv.org/html/2606.27272)
and `kkl_virtual_occupancy_source_audit.md`.

The abstract assembly below is conditional and remains valid as a logical
implication.  It is not a project certification of KKL Proposition 3.9;
`KKL_PARABOLIC_WAVE_AMPLIFICATION` is open.

## 2. Abstract predicates

Fix an occupancy/access bound \(B\). For a virtual block \(F\), write:

- \(\operatorname{Amp}_L(F)\): \(F\) has amplification factor \(L\);
- \(\operatorname{Tame}_P(F)\): \(F\) is tame at control parameter \(P\);
- \(\operatorname{Wave}_P(F)\): \(F\) has a controllable wave of width
  parameter \(P\);
- \(\operatorname{Deg}_{Q,A}(F)\): the combinatorial degeneracy parameter is
  at least \(Q\) and the successor width is at least \(A\).

Only amplification is assumed monotone:
\[
  P\ge L,\quad \operatorname{Amp}_P(F)
  \Longrightarrow
  \operatorname{Amp}_L(F).
\tag{2.1}
\]
No monotonicity of `Tame` or `Wave` is assumed. This is deliberate: their
definitions contain several inequalities, and changing the control parameter
can weaken some requirements. Any monotonicity used in an application must be
proved from the actual definitions.

## 3. Three branch interfaces

### S4. Static trichotomy

For every \(P\ge1\), there is \(A_0(B,P)<\infty\) such that, if the Virtual
Section-4 Interface is realized and the successor width is at least
\(A_0(B,P)\), then
\[
  \operatorname{Amp}_P(F)
  \ \vee\
  \operatorname{Tame}_P(F)
  \ \vee\
  \operatorname{Wave}_P(F).
\tag{S4}
\]

### T. Same-parameter tame closure

For every \(P\ge1\), there are thresholds \(Q_t(B,P)\) and \(A_t(B,P)\) such
that
\[
  \operatorname{Deg}_{Q_t(B,P),A_t(B,P)}(F)
  \ \wedge\
  \operatorname{Tame}_P(F)
  \Longrightarrow
  \operatorname{Amp}_P(F).
\tag{T}
\]

The same parameter \(P\) on both sides is the safe interface. A more general
version is possible, but it must provide an explicit common input parameter
for the static split and both branch closures.

### W. Wave parameter selector

For every requested output factor \(L\ge1\), there is
\[
  P_w(B,L)\ge L
\tag{3.1}
\]
and thresholds \(Q_w(B,L)\), \(A_w(B,L)\) such that
\[
  \operatorname{Deg}_{Q_w(B,L),A_w(B,L)}(F)
  \ \wedge\
  \operatorname{Wave}_{P_w(B,L)}(F)
  \Longrightarrow
  \operatorname{Amp}_L(F).
\tag{W}
\]

The selector \(P_w\) is not required to be uniform in \(L\), but every
constant must be independent of period, rotation number, and virtual depth
once \(B,L\) are fixed.

## 4. Assembly theorem

### Theorem 4.1 (quantifier-correct branch assembly)

Assume (2.1), (S4), (T), and (W). Fix \(L\ge1\), set
\[
  P=P_w(B,L),
\tag{4.1}
\]
and define
\[
  Q_*(B,L)
  =
  \max\{Q_t(B,P),Q_w(B,L)\},
\tag{4.2}
\]
\[
  A_*(B,L)
  =
  \max\{
    A_0(B,P),
    A_t(B,P),
    A_w(B,L)
  \}.
\tag{4.3}
\]
If the Virtual Section-4 Interface is realized and
\[
  \operatorname{Deg}_{Q_*(B,L),A_*(B,L)}(F)
\tag{4.4}
\]
holds, then
\[
  \operatorname{Amp}_L(F).
\tag{4.5}
\]

**Proof.**
Invoke (S4) at the single parameter \(P\).

1. If \(\operatorname{Amp}_P(F)\), then \(P\ge L\) and (2.1) gives
   \(\operatorname{Amp}_L(F)\).
2. If \(\operatorname{Tame}_P(F)\), the thresholds in (4.2)--(4.4) permit
   (T), giving \(\operatorname{Amp}_P(F)\), and then (2.1) gives
   \(\operatorname{Amp}_L(F)\).
3. If \(\operatorname{Wave}_P(F)\), equations (4.1)--(4.4) permit (W),
   giving \(\operatorname{Amp}_L(F)\).

The three cases exhaust (S4). \(\square\)

### Corollary 4.2 (uniformity audit)

If \(B\) is universal and every threshold in (S4), (T), and (W) depends only
on its displayed arguments, then \(Q_*(L)\) and \(A_*(L)\) are independent of
period, rotation number, and virtual transition depth.

If \(B\) is not universal, Theorem 4.1 gives only a \(B\)-dependent statement.
It does not produce the uniform Master Transition Lemma.

## 5. Parameter-mismatch no-go

### Proposition 5.1 (unrelated branch inputs do not compose)

The following data do not imply \(\operatorname{Amp}_L(F)\):

1. the static split (S4) for every parameter;
2. a tame implication only at one input \(P_t\),
   \(\operatorname{Tame}_{P_t}\Rightarrow\operatorname{Amp}_L\);
3. a wave implication only at a different input \(P_w\),
   \(\operatorname{Wave}_{P_w}\Rightarrow\operatorname{Amp}_L\);
4. no monotonicity or common-input theorem for `Tame` and `Wave`.

**Proof.**
Take \(P_t\ne P_w\). Define all amplification predicates to be false. Set
\[
  \operatorname{Tame}_{P_t}(F)=\mathrm{false},
  \qquad
  \operatorname{Wave}_{P_w}(F)=\mathrm{false},
\]
so both branch implications hold vacuously. At \(P_t\), let
\(\operatorname{Wave}_{P_t}(F)\) be true; at every other parameter, including
\(P_w\), let \(\operatorname{Tame}_P(F)\) be true. The static disjunction
holds for every \(P\), yet \(\operatorname{Amp}_L(F)\) is false. \(\square\)

The countermodel is logical rather than dynamical. Its role is to prove that
parameter synchronization is a genuine proof obligation, not a presentational
preference.

### Proposition 5.2 (threshold mismatch no-go)

Even with synchronized control parameter, a large-width premise for (S4)
does not imply the high-type or width thresholds required by (T) and (W)
unless all thresholds are combined as in (4.2)--(4.3).

**Proof.**
Choose a block whose successor width lies above \(A_0(B,P)\) but below
\(A_t(B,P)\), or whose combinatorial degeneracy lies below \(Q_w(B,L)\).
Then (S4) applies but the corresponding closure premise does not. \(\square\)

## 6. Required form of the virtual branch lemmas

The three open virtual results should therefore be stated so that:

1. the Section-4 split is invoked at one declared \(P\);
2. the tame theorem accepts `Tame(P)` and returns `Amp(P)`, or supplies an
   explicit common-parameter replacement;
3. the wave theorem supplies \(P_w(B,L)\ge L\) and accepts `Wave(P_w)`;
4. all large-width, period, selected-degree, and stopping-horizon thresholds
   are displayed before taking their maximum;
5. no monotonicity of tameness or wave width is used silently;
6. the amplification direction is
   \(\mathbb W(F)\ge L\,\mathbb W(\mathcal R F)\).

Once the three analytic interfaces exist in this form, Theorem 4.1 closes
their branch logic. The remaining passage to the unified entropy/shear
dichotomy and the Master Transition Lemma still requires calibration,
summable error control, and routing across the neutral and puzzle charts.
