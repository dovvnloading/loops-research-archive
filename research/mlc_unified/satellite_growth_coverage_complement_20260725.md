# Satellite-growth coverage complement audit

## Purpose and status

This is a separate source-locked audit for the active MLC proof attempt. It
does not modify the main manuscript or either original PDF.

The current imported closures are sufficient conditions. This note tests
whether their hypotheses are logically exhaustive at the level of satellite
rotation data. They are not. The witness below is deliberately only a finite
combinatorial-data witness; it is **not** asserted to be the rotation data of
an already constructed limiting quadratic parameter.

## Witness

Set, for (m\geq 0),

    q_m = m+3,       p_m = 1,       t_m = p_m/q_m = 1/(m+3).

Then (p_m) and (q_m) are coprime, (q_m\to\infty), and

    0 < t_m < 1/2.

Thus every finite entry is an allowed nonzero satellite rotation datum.

## Failure of the imported growth tests

1. In the pure satellite specialization of the Cheraghi--Shishikura
   quadratic-growth class, one needs (q_{m+1}\geq q_m^2) after the
   threshold. Here (q_{m+1}=q_m+1<q_m^2) for every (q_m\geq 2).

2. For Levin's satellite specialization of Theorem 1, the renormalization
   period is (n_m=n\,q_0\cdots q_{m-1}). Hence

       log q_m / n_m <= log(m+3)/(n 3^m) -> 0,

   so the required positive limsup is absent, even if (n=1).

3. Levin's Theorem 2 test gives

       |t_{m+1}|^(1/q_m)
         = (1/(m+4))^(1/(m+3)) -> 1,

   so its strict (<1) limsup condition is not met.

4. Levin's Theorem 7 cannot apply because its (Y0a) quantity satisfies

       |t_m| q_0...q_{m-1}
         = (q_0...q_{m-1})/(m+3) -> infinity.

   Moreover, for every fixed beta>0, its (Y1) ratio is bounded above by

       (m+3)/(q_0...q_{m-1})^2 <= (m+3)/3^(2m) -> 0.

The companion validator evaluates these expressions on a 40-entry prefix and
locks both source PDFs by SHA-256. It is a transcription and coverage check,
not an analytic proof of existence or nonexistence of a limiting parameter.

## Consequence for the global proof

The QG_N and Levin closures cannot be combined into a universal MLC theorem by
an exhaustion argument. A valid global proof needs at least one of the
following new inputs:

* prove that every *realizable* unbounded-satellite tower eventually enters a
  source-covered growth class, together with the missing realizability and
  limit argument; or
* prove a new pseudo-Siegel/a-priori-bound theorem for the complement; and
* separately solve the virtual-Molecule interpolation and marked rigidity
  problem.

The first item is not known from the checked sources, and the finite witness
does not pretend to settle the realizability question. The global MLC target
therefore remains open and must stay open in the ledger.

## Source lock

* Cheraghi--Shishikura, *Satellite renormalization of quadratic polynomials*,
  arXiv:1509.07843v1, <https://arxiv.org/pdf/1509.07843>.
* Levin, *Rigidity and non local connectivity of Julia sets of some quadratic
  polynomials*, arXiv:0710.4406v4, <https://arxiv.org/pdf/0710.4406>.

The machine certificate records the local source hashes and writes no original
artifact.
