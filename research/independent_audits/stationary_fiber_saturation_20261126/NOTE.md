# Stationary geometric carrier: fiber saturation and the remaining obstruction

Date: 2026-11-26. Working proof packet, opened for incremental review.

## Target and scope

This packet follows the actual quadratic construction in [stationary predecessor lift](../stationary_nonlc_predecessor_lift_20261126/NOTE.md), especially its explicit distinction between the least physical carrier S and the full monotone lift T*. It targets the unresolved saturation/access identifications in KKL_STATIONARY_NONLC_SELECTED_GEOMETRIC_CONTINUUM_LIFT and KKL_STATIONARY_MONOTONE_FULL_LIFT_IDENTIFICATION. No global ledger promotion, analytic width estimate, or MLC claim is intended.

Use the hypotheses and notation of that note: X=K(f)=J(f) is a full empty-interior continuum, hence hereditarily unicoherent; p:X→Y is the Kiwi monotone dendrite quotient, pf=gp; nonsingleton fibers have pairwise disjoint forward images, each of which is a complete fiber; K_i are the disjoint primitive cycle of compact connected little filled Julia sets with f(K_i)=K_(i+1 mod P). Let S be their least physical continuum hull, B their model hull and T*=p^{-1}(B).

## First lemma: periodic continua cannot share a wandering fiber

Let A,D be disjoint subcontinua of X with f^m(A)⊂A and f^m(D)⊂D for some common positive m. Then p(A) and p(D) are disjoint.

Proof. Otherwise a complete fiber C meets both A and D. It is nonsingleton, so C and f^m(C) are disjoint by the stated wandering-fiber property. Both continua A∪C∪D and A∪f^m(C)∪D are connected, since each connecting fiber meets both A and D. Their intersection is exactly A∪D, a disconnected set. This contradicts hereditary unicoherence. QED.

This generalizes the predecessor note's disjoint periodic-mark argument to any two forward-invariant continua sharing a return time (surjectivity on them is unnecessary). The essential imported hypothesis is the wandering-fiber property; no statement about arbitrary monotone quotients follows.

## Research question

The existing note establishes p(S)=B, S⊂T*, and exact selected-component equality for T*, but does not identify S=T* or its marked accesses. The next steps will distinguish a genuine dynamical obstruction from purely topological ambiguity; all proved and conditional statements will be explicitly scoped.

AI disclosure: OpenAI GPT-6.2 assisted proof search and exposition; no independent human verification at opening.
