# Paper 3 Draft II — release QA

Date: 2026-07-27

## Release verdict

The theorem spine survived independent adversarial proof review. The release
has zero known mathematical, citation, source, build, PDF-integrity, or visual
layout defects after the checks below. It is suitable for circulation as a
serious paper draft. Independent expert peer review remains appropriate before
making an absolute correctness claim.

Release artifact:
`output/pdf/protected_planar_carriers.pdf`

- Pages: 72
- Bytes: 439,213
- SHA-256:
  `0F42AAA820AE4627298E3741341FD2F5916A98C4CDD4AA8CA9C8BA2714796717`

## Mathematical QA

- Audited every numbered theorem, proposition, lemma, corollary, definition,
  example, warning, and open problem against its proof and downstream uses.
- Repaired the compact atom-tail inventory, the fixed-inventory persistence
  statement, null-chain and relative-collar conventions, single-atom and
  zero-edge cases, empty-intersection handling, degenerate atoms, and the
  `N=0` packet case.
- Made the access-collision example formal and synchronized its transported
  access under the conformal branch.
- Verified the attachment exact sequence, separation-rank ledger, full/full
  criterion, Hausdorff defect examples, nested-limit theorem, certificate
  realization, free-component criterion, packet lemma, and audit theorem.
- Corrected Alexander duality to the compacta/Čech form and stated the
  locally-contractible singular-cohomology limitation explicitly.
- Removed assertions not supplied by the proofs, including undeclared
  prime-end access from ribbon sides and overbroad CW-type claims.

## Literature and priority QA

- Verified and narrowed the Hubbard-tree, Kahn–Lyubich, Kahn–Kapiamba–Lyubich,
  Moore decomposition, Carathéodory extension, and Dudko descriptions.
- Added the original Janiszewski reference and made the
  Janiszewski–Mullikin/unicoherence/multicoherence priority boundary explicit.
- Presented the separation ledger as a classical
  Alexander-duality/Mayer–Vietoris consequence packaged for the carrier
  formalism, with no priority claim for the contact-count invariant.
- Marked the two project self-citations as unpublished/in-preparation and
  replaced product-specific AI acknowledgments with a neutral responsibility
  statement.

## Automated release gates

The release script assembles the source, performs two clean Tectonic builds,
requires byte-identical PDFs, and then runs strict source/PDF checks.

Final results:

- 114 unique labels; 75 resolved references; 17 resolved citation keys.
- 33 numbered statement environments.
- Zero unresolved inserts, duplicate labels, environment mismatches, macro
  conflicts, consecutive duplicate words, replacement characters, missing
  citations, overfull boxes, or underfull boxes.
- 27/27 font programs embedded.
- 499 bounded annotations; 255 valid named destinations; 55 valid outline
  entries.
- One consistent Letter page box, zero rotations, no empty pages, encryption,
  forms, JavaScript, embedded files, executable actions, or malformed links.
- Correct title, author, subject, keywords, producer, creator, and deterministic
  creation date metadata.

## Visual QA

Every page of the final 72-page PDF was rendered with Poppler and inspected in
contact sheets. Title pages, contents, dense proof pages, all seven figures,
the comparison table, the provenance table, acknowledgments, and references
received enlarged checks. The comparison table was anchored before Section 5
to prevent a float from interrupting the opening paragraph.

No clipping, overlap, blank page, broken glyph, malformed equation, stranded
heading, illegible figure, or bad page transition remains known.
