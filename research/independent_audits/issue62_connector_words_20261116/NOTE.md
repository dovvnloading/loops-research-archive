# Issue #62: KL connector-word gauge and fail-closed physical certificate boundary

**2026-11-16. Result: 0 certified based F9 words; 88 still null.** This is a source-check and a nontrivial exact word-gauge theorem, **not** a physical polygonal KL-connector reconstruction. It does not close Issue #62. The preceding 88-row source census and its conditional root / proper-tail conclusions are retained without modification.

**2026-11-23 correction to the construction target.** The single common
fine-root start and coarse-exterior-only path prescription below cannot
represent all 88 specified native tile lifts. The archived C4 wake
obstruction implies that 44 rows, including four native root rows, are
unreachable from a root-normalized lower-parent start in that path domain.
The exact native tile images occupy two coarse inverse-image components.
Use either an initial path inside W followed by a coarse annular path, as
the original KL category permits, or two initial fine sheets. The
[two-component proof and row manifest](../maximal_root_landing_20261123/NOTE.md)
give the obstruction and the corrected alternatives. The gauge algebra
here remains valid for specified paths; it does not prove those paths
exist with the originally proposed simultaneous prescriptions. No null
word has been replaced by a fabricated crossing certificate.

## 1. Re-reading the ORIGINAL path definition

Kahn--Lyubich, *A priori bounds ... II: Decorations*, arXiv:math/0609046v2, original printed **pp. 11--13**, Section 3.2.1 and Lemmas 3.3--3.4 (https://arxiv.org/pdf/math/0609046), defines a path space for a geometric piece Y of depth m:

- the path starts **somewhere in Y**, ends in the carrier U^m minus S_Y, with S_Y the closure of K(G) minus K_Y;
- whenever its prefix ends in K_Y, that prefix must be homotopic **relative endpoints** to a path within Y (the footnote gives the more restrictive after-first-exit option);
- equivalence is by homotopy **through this restricted path space with the terminal endpoint fixed**;
- Lemma 3.3 identifies each annular component with a copy of the universal cover of U^m minus K(G), accessed from one simply connected component Y_i of Y minus K_Y.

Thus Lemma 3.3 supplies the **path category and its classifying property**, not a canonical physical piecewise-linear representative for an arbitrary ideal J endpoint. It does NOT give a list of polygon vertices, a single global based whisker from the common fine basepoint, or nine signed fine-cut crossings. The choice of an embedding of each Y_i into a copy of the annular universal cover is explicitly part of the second definition. Lemma 3.4 gives the W-to-V immersion, not the missing fine nine-cut markings. Section 3.2.4 distinguishes original lambda outer sides, xi/eta J sides and their infinitely wrapping joints; the eight original open seams are not ideal J sides.

At the actual G=f^3 stage W=Y_G^6, the prior exact atlas fixes four seams, respective parent routes 0,1->0 and 2,3->1, and the *within-annulus* unwrapped coordinate origin (angle 0 at height h/256). These are not the same as specifying a physical path from the ONE common based fine root x to every source tile, nor a physical matching fine-rooted path. The G straightening angle-height coordinate is quasiconformal/topological; it cannot be substituted as literal Euclidean polygon coordinates for rigorous nine-cut intersection arithmetic.

## 2. An exact, necessary noncanonicity that a word extractor must handle

Use the archived compatible based basis of Gamma=F(b00,b01,b02,b10,...,b22), H=<b00>, right monodromy on left cosets H\Gamma, and the COARSE peripheral beta0=b00*b01*b02. Fix a physical endpoint y in the common fine exterior close enough to its K9 landing point, a coarse admissible path kappa_prime:x->y, and a rooted reference kappa:x->y inside W minus K9. If these paths are explicitly specified, define the **based loop**

    g = [kappa_prime * inverse(kappa)] in Gamma.

The word is invariant when either path is moved by an endpoint-fixed *admissible homotopy* **that also remains in the fine exterior**, with the basepoint and fine basis fixed. However, the rooted W section of PR #60 does **not** single out a unique homotopy class of kappa: for every m in Z, precomposing kappa by the rooted meridian loop b00^m is still a W-compatible rooted connector and chooses the **same lifted sheet**. The new literal based loop is

    g_new = g * b00^(-m).                                            (A)

This is right multiplication, **not** the coarse left prefix beta0^n*g. In a free group all words in (A) are distinct for different m. In particular, **even a specified coarse connector does not yield a unique literal g until the rooted reference path is fixed as a path class, not merely as a root sheet**.

The root membership test is invariant under (A): g is in H iff g*b00^(-m) is in H. But the left coset coordinate need not be invariant: for g outside H and m nonzero, H*g and H*g*b00^(-m) differ because H is a malnormal free factor of F9. For example, the purely algebraic nonroot test g=b01 changes to b01*b00^(-1), distinct even as H-left cosets; no assertion is made that either word is a physical KL connector. The changing coordinate reflects changing the endpoint reference frame, NOT two different physical source sheet lifts.

If a coarse globally based prefix B with word u is independently specified, and the reference simultaneously changes by a root loop b00^m, then

    g_new = u * g * b00^(-m).                                        (B)

The native deck translation in an ORIGINAL KL tile cannot automatically be replaced by the globally based word beta0^n: the initial tile whisker and its possible conjugator must first be certified. For a **specified** based beta0 prefix, though, the prior all-integer law H*beta0^n*g != H*beta0^k*g for n != k is correct, since winding about D(0,1) gives n-k. In particular beta0 must not be collapsed to b00. Complete F9 cancellation is indispensable: the nontrivial commutator [b01,b02] has all nine signed winding sums zero and still lies outside H.

A simultaneous basepoint change along u identifies old loops with u*g*u^(-1) and **also** sends H to u*H*u^(-1). Root membership is invariant in this transported pair. Keeping the old H or the old named nine-cut basis while conjugating only g is an erroneous "basepoint invariance" claim.

**Proof of the malnormal step.** Write F9=H*Q with Q freely generated by the other eight meridians. For any g outside H, strip the maximal H syllables at both ends to obtain a double-coset representative with Q syllables at both ends. Conjugating any nontrivial h in H by this representative leaves Q syllables and cannot lie in H. Thus H intersect g^(-1) H g is trivial. Equality H*g*b00^(-m)=H*g*b00^(-k) would force g*b00^(k-m)*g^(-1) into H, hence k=m. This argument covers all integer m,k and all nonroot words, not just the finite executable test set. It uses a fixed basis and the physical identification of H as the root stabilizer imported from Kahn's localization.

## 3. Source-row status and what exact arithmetic does (and does not) prove

The new deterministic word_status.json repeats all **88** exact strict original finite J-side instances from the merged audit. Each row retains its source ray/anchor tile/source tile/V parent/shift/xi-or-eta/unwrapped angle, exact fine angle, physical landing target, original proof role, and the prior fine sheet claim, and explicitly records FIVE null fields: the coarse and rooted physical path, signed intersections with the nine cuts, the based basis-change certificate, and the reduced based defect word. The verifier validates original exact rational open-seam / V-collapse inequalities, reruns the original detailed source verifier, and enforces 8 same-parent zero-deck mates versus 80 nonroot rows.

The annotation "in_H" for those eight and "outside_H" for the other 80 is a **necessary group consequence conditional on the imported KL/Kahn/Caratheodory/Jordan-wake physical sheet theorem** in merged PR #64 and the rooted reference comparison. It is NOT an independently measured physical signed-cut word or a new analytic root-convergence certificate. There are **zero** new certified crossings, polygonal segments, path-subordination certificates, or F9 words. Neither an interval arithmetic nonintersection proof nor an "all paths are subordinate" claim can be made from rational *angles* alone.

The new verifier uses exact Fraction comparisons and checks all 325 freely reduced F9 words of length at most two over nine generators for: cancellation, the right-H reference gauge, invariance of root membership, distinction of nonroot reference cosets, correct noncommutative coarse prefix order, candidate root shift, and consistent basepoint conjugation. An adversarial in-memory mutation inserting even the EMPTY (identity) word is explicitly rejected. The Lean file imports the archived concrete nine-letter normalizer and checks only finite discrete control examples, NOT physical geometry, ideal prime ends, infinite malnormality or source analytic hypotheses.

## 4. Actual construction gate (not performed here)

To replace an individual null, one must exhibit: (i) an identified **actual** source ideal row and representative endpoint y at positive height, with a certified physical G-carrier region; (ii) an endpoint-fixed KL Lemma 3.3 path and the *start-whisker from the common physical x*, with subordination/homotopy checked in U_G^6 minus S_W; (iii) a separately fixed W\K9 rooted reference homotopy class; (iv) explicit interval enclosures for actual physical path vertices and nine disjoint signed cuts in Omega9, all segment/cut intersections, and the conjugating paths into this archive's based b_rj basis; (v) a second representative/homotopy computation, followed by a nonabelian reduced-word equality and root membership test. Ray angle and tile integer alone never certify (ii)--(iv).

**Issue #62 status:** Criterion 1 (typed finite J witness cohort) remains inherited and conditional on analytic landing; the exact source census is rechecked. Criterion 2 (the FULL specified physical connector groupoid and literal words) is **NOT MET: 0/88 words**, though the correct path category and new reference-gauge rule are recorded. Criterion 3 (all integer word behavior and proper endpoints) has exact formal-algebraic controls and prior conditional 8/80 source-side outcomes, **NOT new physical F9 words or an unqualified KKL unique restriction**. Criterion 4 (new full physical source certificate and specialist-confirmed KKL proper restriction) remains **OPEN**. The 465-entry ledger, H1--H4, UPTCR and MLC are unchanged; independent specialist analytic review is outstanding.

Reproduce: python research/independent_audits/issue62_connector_words_20261116/verify_connector_words.py --check-manifest. The dedicated workflow also runs the old source checker, research provenance/README integrity checks, the full registered Lean build and the standalone faithful discrete Lean module. **No existing file is changed.**
