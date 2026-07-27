# Levin Theorem 7: extended fast-satellite parameter branch

## 1. Purpose and status

This is a separate addendum to the Levin branch certificate. It records the
broader parameter-rigidity criterion in Theorem 7 of the same source. It does
not modify original documents.

The key correction is that the simple condition

    limsup |t_(m+1)|^(1/q_m) < 1

is not the full reach of Levin's method. Theorem 7 uses three conditions on
the satellite bifurcation sequence. The source even notes that sequences can
satisfy those conditions while the root expression tends to 1.

The imported conclusion is:

    Theorem 7: (Y0a) + (Y0b) gives convergence of the cascade;
    (Y1) additionally gives Mandelbrot local connectivity at the limit.

The Julia-set conclusion requires the separate condition (S), which is not
needed for MLC and is not promoted here.

## 2. Source lock

Source:

* G. Levin, *Rigidity and non local connectivity of Julia sets of some
  quadratic polynomials*, arXiv:0710.4406v4,
  https://arxiv.org/pdf/0710.4406.

Local source hash:

    8E5A59B111C0D841D5DEB3AB7ADB12B556896A2916C1E4CC8418FE41789335CD

The theorem and conditions are on the source's printed pages 10--11.

## 3. Exact imported conditions

Let t_m = p_m/q_m be nonzero rational internal arguments in lowest terms.
Products below are over the indicated integer ranges.

Levin's conditions are:

    (Y0a) sup_m |t_m| q_0 q_1 ... q_(m-1) < infinity;

    (Y0b) inf_m
      log( |p_(m-1) q_(m-1)| / |t_m| )
      / (q_0 q_1 ... q_(m-2)) > 0;

    (Y1) there exists beta > 0 such that

      limsup_m q_m /
        max{ (q_0 ... q_(m-1))^2,
              exp(beta q_0 ... q_(m-2)) } > 0.

For the successive satellite hyperbolic components W_m obtained by attaching
the next component at internal argument t_m:

* (Y0a)+(Y0b) imply convergence to a limit parameter;
* adding (Y1) implies MLC at the limit parameter;
* adding (S) concerns non-local connectivity of the limiting Julia set and
  is not required for the MLC promotion.

These are imported source conditions, not replacements for the virtual-Molecule
theorem.

## 4. Explicit root-to-one construction

The theorem's conditions are not merely a restatement of the earlier
fast-small-rotation criterion. Fix beta > 0, choose q_0,q_1 >= 2, set p_m=1,
and for m >= 2 define

    P_(m-2) = q_0 q_1 ... q_(m-2),
    q_m = ceil( exp(beta P_(m-2)) ).

Then:

1. (Y0a) holds because
   P_(m-1)/q_m is bounded and tends to zero; the exponential q_m
   dominates P_(m-1)=P_(m-2)q_(m-1).
2. (Y0b) holds because
   log(q_(m-1)q_m)/P_(m-2) has a positive lower asymptotic bound beta.
3. (Y1) holds with the same beta after the exponential term dominates
   P_(m-1)^2.
4. The earlier root expression satisfies

       |t_(m+1)|^(1/q_m)
       = q_(m+1)^(-1/q_m) -> 1,

   because log(q_(m+1))/q_m is asymptotic to
   beta P_(m-1)/exp(beta P_(m-2)), which tends to zero.

Thus the criterion genuinely extends the previously recorded
limsup-root-less-than-one branch.

The construction is a combinatorial witness for the hypotheses. The theorem
still requires the source's satellite cascade realization.

## 5. What this repairs

The unbounded-satellite partition now includes:

* Cheraghi--Shishikura QG_N quadratic-growth cascades;
* Levin Theorem 1 exponential numerator/denominator branches;
* Levin Theorem 2 fast-small-rotation cascades;
* Levin Theorem 7 cascades satisfying (Y0a),(Y0b),(Y1), including some
  root-to-one sequences;
* the remaining unbounded satellite complement, where these conditions are
  not established;
* virtual bounded-type satellite and virtual near-neutral Molecule towers;
* global mixed towers and MLC.

Do not infer that every sequence failing the simple root test satisfies
Theorem 7. The three product conditions are independent proof obligations.

## 6. Machine validation

The companion validator:

* locks the source hash;
* checks that Theorem 7, (Y0a), (Y0b), and (Y1) occur in the source pages;
* checks finite exact witnesses for the growth pattern;
* checks numerically that the explicit construction's root expression moves
  toward 1 on the finite tested prefix; and
* records original_artifacts_written=false.

This validates transcription and scope, not Levin's analytic theorem.

Original documents remain untouched.

