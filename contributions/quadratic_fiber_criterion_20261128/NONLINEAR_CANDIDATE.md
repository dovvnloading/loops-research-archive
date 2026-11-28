# Nonlinear candidate and the missing boundary argument

Historical record of the rejected interpolation candidate, written before the retained mixed-series criterion. See [NOTE.md](NOTE.md) for the current result and validation status.

Status at this earlier checkpoint: candidate analysis before formalization; no new theorem had been accepted.
This file advances the investigation beyond the previous spectral screen by
writing an exact actual-family bridge to local connectivity, and then identifying
why the available certificate does not pass the requested novelty test.

## 1. Actual parameter interpolation

Let P_0(c)=0 and P_{n+1}(c)=P_n(c)^2+c. For c,d in C and 0<=t<=1, write

    p=(1-t)c+t d,
    x_n=P_n(c),  y_n=P_n(d),
    a_n=(1-t)x_n+t y_n,
    Delta_n=x_n-y_n,
    e_n=P_n(p)-a_n.

Direct quadratic polarization gives

    e_0=0,
    e_{n+1}=2 a_n e_n+e_n^2-t(1-t)Delta_n^2.                 (1)

The signed complex square must be retained. Replacing it by an absolute-value
majorant loses the only potentially new cancellation mechanism.

Equation (1) is elementary algebra, not a novelty claim. It concerns the
actual parameter p and its actual critical orbit.

## 2. A precise candidate with a complete MLC bridge

Define M by bounded critical orbit:

    M={c in C : there exists B with |P_n(c)|<=B for every n}.

The following proposed certificate would imply local connectivity at c.
It is recorded to make the desired bridge concrete, not submitted as new.

**Proposed sufficient condition.** Let c belong to M. Suppose there is r>0
such that for every d in M with |d-c|<r and every t in [0,1], there are complex
numbers u_n and nonnegative real numbers rho_n, with u_0=rho_0=0, satisfying

    |u_{n+1}-2a_n u_n-u_n^2+t(1-t)Delta_n^2|
      +2|a_n+u_n|rho_n+rho_n^2 <= rho_{n+1},                (2)

and the sequence |a_n+u_n|+rho_n is bounded.

**Implication to actual MLC.** Put w_n=e_n-u_n. From (1),

    w_{n+1}=2(a_n+u_n)w_n+w_n^2
             -(u_{n+1}-2a_nu_n-u_n^2+t(1-t)Delta_n^2).

Induction using (2) yields |w_n|<=rho_n. Thus

    |P_n(p)|<=|a_n+u_n|+rho_n,

so p belongs to the genuine M. Consequently M intersect B(c,s) is star-shaped
with center c for every 0<s<=r: a segment from c to any d in this set stays
in M and in the same ball. It is path connected and relatively open in M.
These sets form a connected relative neighborhood basis at c. This is local
connectivity at c in the ordinary subspace topology.

The bridge does not rename an arbitrary predicate as M or assume an arbitrary
relation is a combinatorial fiber.

## 3. Why this candidate is not accepted

Condition (2) is a standard invariant-disk/validated-shadowing certificate
applied to the explicitly derived scalar recurrence. Its proof is the
triangle inequality and induction. The nonlinear forcing is specific to the
quadratic family, but the currently available proof has not extracted a new
cancellation theorem from it.

Moreover, the conclusion of local star-shapedness is much stronger than
local connectivity. No boundary parameter satisfying this certificate by a
new dynamical mechanism has been established. A hypothesis that simply
takes u_n=e_n and rho_n=0 is circular: its boundedness is the boundedness we
are trying to prove. That choice is expressly not accepted as a criterion.

Therefore this statement fails the requested standard of a genuinely new
idea. It is not being formalized as the requested result.

## 4. Curved paths and the exact unsolved step

Allow p(t)=(1-t)c+t d+beta(t), and write P_n(p(t))=a_n+s_n. Then

    s_0=0,
    s_{n+1}=2a_n s_n+s_n^2-t(1-t)Delta_n^2+beta(t).          (3)

A viable continuation would construct beta and control (3) using an algebraic,
one-sided cancellation mechanism forced by actual dynamics, compatible with
boundary parameters, without assuming the bounded corrected orbit.

Uniform holomorphic solvability is insufficient as a new boundary mechanism:
a nonconstant holomorphic parameter family contained in M has open image by
the open mapping theorem. Ordinary complex inverse-function control therefore
gives interior behavior, or a constant family. This observation is classical
and is not submitted as a new obstruction.

The missing result is precisely the nonuniform or real-only nonlinear control
needed to produce connected relative neighborhoods at a boundary parameter.
No such theorem has been proved here.

## 5. Closest classical transfer result

G. Levin, W. Shen, S. van Strien, *Positive Transversality via transfer operators
and holomorphic motions*, Nonlinearity 33 (2020), arXiv:1902.06732:
https://arxiv.org/pdf/1902.06732

Their transfer-operator/holomorphic-lifting framework already treats the
finite critical-relation determinant and bounded-lift transversality mechanism.
Appendix A treats sector-regular lifting for real families. Merely introducing
a mixed susceptibility matrix, a phase cone, or a finite determinant formula
does not establish novelty. An infinite, nonuniform actual-fiber extension
would need its own proof and is not supplied by those finite identities.

## 6. Formalization status

No candidate in this file has passed both novelty and a complete new proof.
No new theorem is counted, and no new result has been submitted to Lean CI.

At this checkpoint, the absent local compiler was partially repaired: the official Lean 4.32.0
binary checked a small core theorem through its documented module setup.
This is toolchain verification only, not a theorem in this PR. Mathlib and the
complete archive build remain available through repository CI.

At this checkpoint, the user-required task was still incomplete. The later retained criterion and its actual local-connectivity endpoint are recorded in NOTE.md.
