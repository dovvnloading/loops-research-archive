from __future__ import annotations

import hashlib
import json
from pathlib import Path

from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_LEFT
from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import inch
from reportlab.platypus import (
    KeepTogether,
    LongTable,
    PageBreak,
    Paragraph,
    SimpleDocTemplate,
    Spacer,
    Table,
    TableStyle,
)


ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research" / "mlc_unified" / "output" / "pdf" / "mlc_subresearch_corrections_proposal_20260724.pdf"
LEDGER = ROOT / "research" / "mlc_unified" / "proof_obligations.json"
ORIGINALS = [
    ROOT / "research" / "mlc_unified" / "output" / "pdf" / "marked_width_mlc_manuscript.pdf",
    ROOT / "research" / "mlc_unified" / "latex" / "build" / "main.pdf",
]


NAVY = colors.HexColor("#102A43")
BLUE = colors.HexColor("#1F5A85")
TEAL = colors.HexColor("#0E7490")
PALE_BLUE = colors.HexColor("#EAF3F8")
PALE_TEAL = colors.HexColor("#E8F6F7")
PALE_AMBER = colors.HexColor("#FFF4D6")
PALE_RED = colors.HexColor("#FDECEC")
INK = colors.HexColor("#17212B")
MUTED = colors.HexColor("#52606D")
GRID = colors.HexColor("#CBD5E1")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest().upper()


def esc(value: object) -> str:
    return (
        str(value)
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


def p(text: object, style):
    return Paragraph(esc(text).replace("\n", "<br/>").replace("  ", "&nbsp; "), style)


def rich(text: str, style):
    return Paragraph(text, style)


styles = getSampleStyleSheet()
styles.add(ParagraphStyle(
    name="CoverTitle", parent=styles["Title"], fontName="Helvetica-Bold",
    fontSize=25, leading=29, textColor=NAVY, alignment=TA_CENTER,
    spaceAfter=10,
))
styles.add(ParagraphStyle(
    name="CoverSub", parent=styles["Normal"], fontName="Helvetica",
    fontSize=12, leading=16, textColor=MUTED, alignment=TA_CENTER,
    spaceAfter=8,
))
styles.add(ParagraphStyle(
    name="Lead", parent=styles["Normal"], fontName="Helvetica",
    fontSize=11, leading=15, textColor=INK, spaceAfter=8,
))
styles.add(ParagraphStyle(
    name="Body2", parent=styles["BodyText"], fontName="Helvetica",
    fontSize=9.2, leading=12.6, textColor=INK, spaceAfter=6,
))
styles.add(ParagraphStyle(
    name="Small", parent=styles["BodyText"], fontName="Helvetica",
    fontSize=8.0, leading=10.5, textColor=INK, spaceAfter=4,
))
styles.add(ParagraphStyle(
    name="Tiny", parent=styles["BodyText"], fontName="Helvetica",
    fontSize=7.1, leading=9.1, textColor=INK, spaceAfter=2,
))
styles.add(ParagraphStyle(
    name="H1x", parent=styles["Heading1"], fontName="Helvetica-Bold",
    fontSize=15.5, leading=19, textColor=NAVY, spaceBefore=10, spaceAfter=7,
    keepWithNext=True,
))
styles.add(ParagraphStyle(
    name="H2x", parent=styles["Heading2"], fontName="Helvetica-Bold",
    fontSize=11.2, leading=14, textColor=BLUE, spaceBefore=8, spaceAfter=5,
    keepWithNext=True,
))
styles.add(ParagraphStyle(
    name="BoxTitle", parent=styles["Heading3"], fontName="Helvetica-Bold",
    fontSize=10.0, leading=12.5, textColor=NAVY, spaceAfter=3,
))
styles.add(ParagraphStyle(
    name="TableHead", parent=styles["BodyText"], fontName="Helvetica-Bold",
    fontSize=7.8, leading=9.6, textColor=colors.white,
))
styles.add(ParagraphStyle(
    name="TableCell", parent=styles["BodyText"], fontName="Helvetica",
    fontSize=7.7, leading=9.7, textColor=INK,
))
styles.add(ParagraphStyle(
    name="TableCellSmall", parent=styles["BodyText"], fontName="Helvetica",
    fontSize=7.0, leading=8.6, textColor=INK,
))
styles.add(ParagraphStyle(
    name="URL", parent=styles["BodyText"], fontName="Courier",
    fontSize=6.9, leading=8.7, textColor=BLUE, wordWrap="CJK",
))
styles.add(ParagraphStyle(
    name="Footer", parent=styles["Normal"], fontName="Helvetica",
    fontSize=7.4, leading=9, textColor=MUTED,
))
styles.add(ParagraphStyle(
    name="Callout", parent=styles["BodyText"], fontName="Helvetica",
    fontSize=9.1, leading=12.5, textColor=INK, leftIndent=7, rightIndent=7,
    spaceAfter=0,
))


def bullet(text: str, level: int = 0):
    indent = 10 + level * 10
    return rich(f"<font color='#0E7490'>&bull;</font>&nbsp;&nbsp;{esc(text)}", ParagraphStyle(
        f"Bullet{level}", parent=styles["Body2"], leftIndent=indent,
        firstLineIndent=-8, spaceAfter=3,
    ))


def numbered(n: int, text: str):
    return rich(f"<font color='#0E7490'><b>{n}.</b></font>&nbsp;&nbsp;{esc(text)}", ParagraphStyle(
        f"Num{n}", parent=styles["Body2"], leftIndent=15,
        firstLineIndent=-12, spaceAfter=4,
    ))


def callout(title: str, text: str, fill=PALE_BLUE, border=TEAL):
    data = [[rich(f"<b>{esc(title)}</b><br/>{esc(text)}", styles["Callout"] )]]
    t = Table(data, colWidths=[7.1 * inch])
    t.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, -1), fill),
        ("BOX", (0, 0), (-1, -1), 0.8, border),
        ("LEFTPADDING", (0, 0), (-1, -1), 9),
        ("RIGHTPADDING", (0, 0), (-1, -1), 9),
        ("TOPPADDING", (0, 0), (-1, -1), 7),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 7),
    ]))
    return t


def make_table(rows, widths, header=True, small=False, background=PALE_BLUE):
    sty = styles["TableCellSmall" if small else "TableCell"]
    converted = []
    for i, row in enumerate(rows):
        converted.append([
            Paragraph(esc(cell), styles["TableHead"] if header and i == 0 else sty)
            for cell in row
        ])
    t = LongTable(converted, colWidths=widths, repeatRows=1 if header else 0,
                  hAlign="LEFT")
    cmds = [
        ("GRID", (0, 0), (-1, -1), 0.35, GRID),
        ("VALIGN", (0, 0), (-1, -1), "TOP"),
        ("LEFTPADDING", (0, 0), (-1, -1), 5),
        ("RIGHTPADDING", (0, 0), (-1, -1), 5),
        ("TOPPADDING", (0, 0), (-1, -1), 4),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
    ]
    if header:
        cmds += [("BACKGROUND", (0, 0), (-1, 0), NAVY),
                 ("TEXTCOLOR", (0, 0), (-1, 0), colors.white)]
        if len(rows) > 1:
            cmds.append(("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.white, background]))
    t.setStyle(TableStyle(cmds))
    return t


def page_decor(canvas, doc):
    canvas.saveState()
    w, h = letter
    canvas.setStrokeColor(GRID)
    canvas.setLineWidth(0.45)
    canvas.line(doc.leftMargin, h - 0.47 * inch, w - doc.rightMargin, h - 0.47 * inch)
    canvas.setFont("Helvetica", 7.4)
    canvas.setFillColor(MUTED)
    canvas.drawString(doc.leftMargin, 0.38 * inch, "MLC sub-research audit - separate artifact - 2026-07-24")
    canvas.drawRightString(w - doc.rightMargin, 0.38 * inch, f"page {doc.page}")
    canvas.restoreState()


def load_ledger():
    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = data["obligations"]
    counts = {s: sum(x["status"] == s for x in obligations) for s in data["statuses"]}
    return data, obligations, counts


def build():
    data, obligations, counts = load_ledger()
    originals = [(path, sha256(path)) for path in ORIGINALS if path.exists()]
    OUT.parent.mkdir(parents=True, exist_ok=True)

    doc = SimpleDocTemplate(
        str(OUT), pagesize=letter, rightMargin=0.7 * inch, leftMargin=0.7 * inch,
        topMargin=0.67 * inch, bottomMargin=0.58 * inch, title="MLC Conjecture Sub-Research Audit and Closure Proposal",
        author="Codex - read-only sub-research audit",
    )
    story = []

    # Cover
    story += [Spacer(1, 0.45 * inch)]
    story.append(rich("MLC Conjecture:<br/>Sub-Research Audit and<br/>Closure Proposal", styles["CoverTitle"]))
    story.append(rich("Corrections, gap-closing plan, and verification record", styles["CoverSub"]))
    story.append(Spacer(1, 0.18 * inch))
    story.append(callout(
        "Status boundary",
        "This is a separate corrective sub-document. It does not modify or replace the main manuscript, its source files, or its PDFs. The Mandelbrot local connectivity conjecture remains open; this report proposes a disciplined route toward closing the remaining analytic gates.",
        fill=PALE_AMBER, border=colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.24 * inch))
    story.append(rich("Prepared: 2026-07-24 | Workspace: Loops | Source lock: 2026-07-24", styles["CoverSub"]))
    story.append(Spacer(1, 0.32 * inch))
    story.append(callout(
        "Executive verdict",
        "The program has already repaired many false shortcuts. The remaining weak point is not the conditional implication to MLC; it is the missing source-faithful analytic realization of a virtual carrier, its protected marking and finite-horizon transport, and the uniform WAD/Value transition needed for coercivity and rigidity.",
        fill=PALE_TEAL, border=TEAL,
    ))
    story.append(PageBreak())

    story.append(rich("1. Readout at a glance", styles["H1x"]))
    story.append(p("The machine-readable proof ledger currently contains 256 obligations: "
                   f"{counts.get('proved', 0)} proved internally, {counts.get('imported', 0)} imported, and {counts.get('open', 0)} open. "
                   "The local audit reports an acyclic dependency graph and keeps the target MLC open. These numbers are a process readout, not a probability of success." , styles["Lead"]))
    story.append(make_table([
        ["What is strong now", "What is not yet closed"],
        ["The source boundary is explicit: native KKL results are not silently promoted to mixed virtual towers.", "An actual virtual root/cell/branch package is not yet realized uniformly across the required two-step satellite and Wave settings."],
        ["The unmarked scalar-width route is blocked by a proved no-go for unbounded satellite relative periods.", "Protected prime-end access, attachment-free routing, and complete component ownership remain construction gates."],
        ["The corrected plan uses backward amplification or a rigorously inverted forward contraction, not an invalid forward lower recurrence.", "A uniform WAD/Value state, finite-dimensional core, memory-safe pumping, and explicit error budget remain open."],
        ["The UPTCR package is stated as an open proposition, with a conditional implication to MLC.", "Coercivity and parameter rigidity are downstream and cannot be inferred from compact encodings or numerical pictures."],
    ], [3.48 * inch, 3.48 * inch], small=False, background=PALE_TEAL))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Recommended change of emphasis",
        "Stop expanding the universal theorem statement until one nontrivial finite virtual block is realized end-to-end with the full proof-use horizon. Use that block as a falsifiable integration fixture, then lift only the properties that survive its red-team and source checks.",
        fill=PALE_RED, border=colors.HexColor("#B42318"),
    ))

    story.append(rich("2. Audit method and provenance", styles["H1x"]))
    story.append(p("The audit was read-only with respect to existing research artifacts. I inspected the unified README, manuscript/status text, proof ledger, research log, dependency and adversarial audits, and the latest push-assessment notes. I then ran the repository's proof/dependency checker and transfer-regression suite, and re-evaluated the Feigenbaum experiment through imported functions without writing its result file.", styles["Body2"]))
    story += [bullet("Local machine audit: audit_proof.py -> ledger valid; 256 obligations; imported=16, proved=182, open=58; target MLC=open."),
              bullet("Local red-team suite: audit_transfer_regressions.py -> all diagnostic transfer regressions passed."),
              bullet("Numerical cross-check: cascade delta = 4.66920159553749..., c_F = -1.40115518909205..., fixed-point alpha = 2.50290787509585..., fixed-point residual about 1.33e-15, operator eigenvalue about 4.6692015361."),
              bullet("Interpretation limit: these checks validate internal consistency and numerical reproduction; they do not prove analytic realization, uniformity, coercivity, rigidity, or MLC."),
    ]
    story.append(rich("Original PDF hashes recorded before this new artifact was generated:", styles["H2x"]))
    hash_rows = [["Original artifact (read-only)", "SHA-256"]]
    for path, digest in originals:
        hash_rows.append([str(path.relative_to(ROOT)), digest])
    story.append(make_table(hash_rows, [4.6 * inch, 2.35 * inch], small=True, background=PALE_BLUE))
    story.append(p("Transparency note: an earlier read-only snapshot recorded a different hash for marked_width_mlc_manuscript.pdf. Before final generation, both existing PDF paths had the same 22:32 timestamp, length, and SHA-256. No recoverable prior copy was found in the workspace; this sub-research generator only reads those paths and writes the new filename below.", styles["Small"]))

    story.append(rich("3. External validity check", styles["H1x"]))
    story.append(p("The public literature check supports the current boundary of the project. The newest KKL preprint proves a priori bounds and MLC for a class of infinitely renormalizable parameters with primitive renormalization that can approach the cusp; it does not state an all-parameter proof. Dudko's ICM 2026 note presents the broader renormalization/MLC landscape and near-degenerate program. BLOT's result explicitly rules out a priori bounds in the satellite case with unbounded relative periods. The inference used here is therefore conservative: the universal mixed-tower closure still requires new work beyond those scoped results.", styles["Body2"]))
    story.append(make_table([
        ["Source", "Validated use in this sub-research"],
        ["Kahn-Kapiamba-Lyubich, arXiv:2606.27272 (2026)", "Import only the theorem in its stated parabolically bounded primitive class; use its Thin-Thick, Value, Wanderers, and Wave tools as source-facing inputs, not as a virtual-carrier realization theorem."],
        ["Dudko, arXiv:2512.24171 (2025; ICM 2026 proceedings)", "Treat the virtual/near-degenerate discussion as a research program or interface target unless a specific construction theorem is proved and its hypotheses match."],
        ["Blokh-Levin-Oversteegen-Timorin, arXiv:2205.03157; CMP 406 (2025)", "Use the satellite upper-modulus/no-a-priori-bounds result as a hard design constraint against an unmarked universal scalar modulus."],
    ], [2.35 * inch, 4.6 * inch], small=False, background=PALE_AMBER))
    story.append(Spacer(1, 0.08 * inch))
    story.append(p("The web check is not used to certify the local manuscript's new lemmas. It is used to prevent scope drift when deciding what may be imported and what must be proved locally.", styles["Small"]))

    story.append(rich("4. Where the process is now", styles["H1x"]))
    story.append(p("The 58 open obligations fall into dependency layers. The important observation is that the open count is not 58 independent mathematical walls; several nodes are umbrella gates. The repair must therefore attack high-leverage upstream realizations first.", styles["Body2"]))
    story.append(make_table([
        ["Layer", "Open count", "Readout", "Priority"],
        ["Virtual analytic realization (VIRTUAL_*)", "26", "The carrier, component package, target selector, end behavior, accesses, and marked correspondence are still source-facing constructions.", "1 - unlock a finite realized block"],
        ["H1 marked construction", "4", "Finite horizon inflation, cell-tree/access realization, and the global marked construction depend on the virtual geometry.", "2 - derive from the fixture"],
        ["H2 response and transition", "20", "Uniform core/WAD dimension, memory, Value observability, clone/transfer trichotomy, calibration, and error summability remain open.", "3 - only after geometry"],
        ["Transport and direct structural gates", "3", "Direct end prime-end cofinality, mapping telescope, and finite-horizon assembly require actual embeddings, properness, and marking action.", "1/2 - part of the fixture"],
        ["Terminal closure", "5", "MBTT, H3 coercivity, H4 rigidity, UPTCR, and MLC remain open endpoints; UPTCR is the conditional package leading to MLC.", "4 - downstream"],
    ], [1.45 * inch, 0.7 * inch, 3.55 * inch, 1.4 * inch], small=True, background=PALE_BLUE))
    story.append(rich("4.1 The actual bottleneck chain", styles["H2x"]))
    story.append(p("A realistic dependency chain is:", styles["Body2"]))
    for i, text in enumerate([
        "source-defined virtual base and selected components",
        "safe localization, critical chronology, and component ownership",
        "protected access/attachment ledger and prime-end action",
        "frozen complete proof-use horizon and branch language",
        "WAD/Value incidence and response-state realization",
        "uniform backward transition or strict forward contraction",
        "nondegenerate marked compactness and parameter rigidity",
        "MLC via the already stated conditional reduction",
    ], 1):
        story.append(numbered(i, text))
    story.append(callout(
        "Critical separation",
        "A conditional interface theorem can be correct while its geometric hypotheses are still missing. The PDF keeps those layers separate: proved local theorems are promoted as interfaces, but not as evidence that the virtual object exists.",
        fill=PALE_BLUE, border=BLUE,
    ))

    story.append(rich("4.2 Highest-leverage open gates", styles["H2x"]))
    story.append(make_table([
        ["Gate family", "Why it blocks downstream work", "Required repair"],
        ["VIRTUAL_FINITE_WORD_ROOT_PORTRAIT_AUTHORIZATION; VIRTUAL_DISCONNECTED_MARKING_TRANSFER", "Without an actual next-scale root portrait, finite word labels do not define domains, maps, or branches.", "Construct the second-scale portrait inside a certified safe gap; record domains, iterates, critical words, component/sheet ownership, and root-enlargement naturality."],
        ["VIRTUAL_ROOT_CARRIER_SEPARATION; VIRTUAL_COMMON_FREE_COMPONENT; VIRTUAL_PROTECTED_ROUTING_CERTIFICATE", "A combinatorial ribbon or tree does not guarantee a planar full carrier or a common free component.", "Prove a completed packet/obstacle/fullification certificate with actual ports, collision ledger, and a protected connector."],
        ["VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR; VIRTUAL_REACHED_CYLINDER_COMPONENT_EXHAUSTION", "Commutation gives a lift only after a target component has been selected; it does not choose the target word.", "Prove actual containment in an authorized target family, component exhaustion, uniqueness, and compatibility with parent, shift, root, metadata, and enlargement."],
        ["VIRTUAL_WAVE_HORIZON_CERTIFICATE; VIRTUAL_WAVE_DEMAND_SCHEMA; VIRTUAL_WAVE_MARKED_CORRESPONDENCE", "A finite trace cannot be used to construct the horizon whose trace it is.", "Freeze a prefix-local demand schema first; compute the maximal finite horizon; then extract the trace and re-audit extension stability."],
        ["H2_RESPONSE_REALIZATION; H2_UNIFORM_CORE_WAD_DIMENSION; H2_VALUE_FEATURE_REALIZATION", "A finite signature, finite port list, or response scalar does not bound analytic dimension or make Value observable.", "Prove a source-faithful bounded response module, or retain the complete finite vector of Value moments and prove its transport."],
        ["H3_COERCIVITY; H4_RIGIDITY", "Compact symbolic encodings can contain collapsed or inadmissible analytic limits.", "Prove nondegenerate analytic subsequential limits and a connected shrinking parameter-neighborhood basis; only then close UPTCR."],
    ], [2.1 * inch, 2.45 * inch, 2.55 * inch], small=True, background=PALE_TEAL))

    story.append(rich("5. Corrections to weak inferences", styles["H1x"]))
    story.append(p("The following repairs are the most important corrections to preserve in all future additions. Each one is already reflected in the local red-team material; this section turns them into a concise operating standard for the next subtask.", styles["Body2"]))
    story.append(make_table([
        ["Weak inference to reject", "Correct replacement", "Acceptance test"],
        ["A parameter-copy word is an analytic dynamical branch.", "A word is only a label until a domain, iterate, component, and map are source-identified.", "Every branch record has an actual domain/codomain, integer iterate, critical word, degree, localization, and component owner."],
        ["Commutation of iterates chooses a target cylinder.", "Commutation is a conditional identity after target-base typing and component selection.", "A connected-image target theorem is applied inside one fixed, pairwise-disjoint authorized target family; cross-base ownership is separately proved."],
        ["An interior univalent polynomial restriction maps a Jordan disk to a Jordan disk.", "Require a closure embedding onto a relatively compact Jordan subdisk, or work in an explicitly controlled prime-end image domain.", "The closure map is injective and the image boundary/type is checked, not inferred from interior univalence."],
        ["A finite terminal Hubbard-tree trace is the infinite virtual Cantor package.", "Keep the infinite carrier and finite proof-use trace as separate fields; use a quotient only with joint future observability.", "Every claimed observable is constant on each quotient fiber after every declared finite continuation."],
        ["Finite control plus finite horizon implies a finite automaton.", "Retain exact counters and, if source-realized, a stack; pump only memory-neutral reachable fibers or exact macros.", "The pumping summary is a configuration congruence for all declared endpoint, WAD, Value, critical, and error outputs."],
        ["A positive entropy label implies usable expansion.", "Entropy is certified only on an actual closed, repeatable, framed return with the correct incidence and pullback exponent.", "The returned transfer is source-faithful, irreducible/non-permutation where claimed, and the Value/WAD inequality has the actual exponent."],
        ["Compactification proves coercivity.", "Compactification supplies topology; coercivity must exclude collapse, pinching, loss of properness, and loss of admissible marking.", "Every bounded sequence has an admissible nondegenerate marked analytic limit with preserved proof-use structure."],
        ["Native KKL rigidity transfers automatically to mixed virtual towers.", "Import native rigidity only in its native category; prove mixed-category rigidity as a separate theorem.", "Each use states and checks the exact native hypotheses or cites a proved transfer theorem."],
    ], [2.0 * inch, 2.7 * inch, 2.4 * inch], small=True, background=PALE_BLUE))

    story.append(rich("6. Close proposal: a staged proof kernel", styles["H1x"]))
    story.append(p("The proposal below is deliberately narrower than the universal UPTCR statement. It is a close proposal because it creates a sequence of falsifiable certificates whose uniform version would discharge the current open gates, while a failure produces a concrete counterexample or missing hypothesis instead of another informal extension.", styles["Body2"]))

    story.append(rich("Work package A - certificate contract and one finite fixture", styles["H2x"]))
    story.append(p("Define a typed Block Certificate v1 for one nontrivial virtual block. It should be a proof-use record, not a new theorem slogan. Required fields:", styles["Body2"]))
    for text in [
        "source and target bases, authorized localizations, actual domains and codomains, and all return exponents;",
        "stagewise critical word, local degree, component owner, sheet/deck phase, and the one declared quadratic stage;",
        "full obstacle and attachment trace, protected accesses, prime-end endpoints, cyclic order, and collision invariant;",
        "finite horizon demand graph, branch language, stopping index, final-root enlargement, and no-late-dependency result;",
        "relative-cover lift data, proper/end-proper flags, and every analytic/prime-end commuting square;",
        "WAD-to-core incidence, KKL Value moments, response state, counters/stack, and calibrated error budget;",
        "dependency IDs, source evidence, proof status, and a machine-checkable distinction between imported/proved/conditional/open claims.",
    ]:
        story.append(bullet(text))
    story.append(callout(
        "Acceptance test A",
        "The certificate must be instantiable for one actual two-step satellite-copy block without reading any downstream bound, rigidity statement, or MLC conclusion. The static checker must reject undefined maps, missing component ownership, non-authorized target bases, late horizon dependencies, and unproved marking preservation.",
        fill=PALE_TEAL, border=TEAL,
    ))

    story.append(rich("Work package B - analytic realization before abstraction", styles["H2x"]))
    story.append(p("Use the direct-decoration safe gap as the first test environment. Construct the actual second-scale root portrait, its finite-word pullbacks, the selected root carrier, and the protected access system. Do not infer this data from parameter-copy combinatorics or from the terminal Hubbard tree. If the construction fails, record the failure tuple explicitly: missing domain, collision, non-Jordan image, lost access, unresolved component, or unauthorized target.", styles["Body2"]))
    story.append(callout(
        "Acceptance test B",
        "The fixture has an end-to-end planar realization: all requested finite branches exist, the selected target components are unique, the carrier is full in its authorized localization, protected accesses survive, the relative-cover action is embedded/proper on the declared cores, and the stagewise degree ladder is verified.",
        fill=PALE_BLUE, border=BLUE,
    ))

    story.append(rich("Work package C - horizon-first marked transport", styles["H2x"]))
    story.append(p("Freeze the proof-use demand schema from prefix-local data before any Wave stopping execution. Compute the maximal finite horizon, retain every branch/component/critical/access/WAD/Value/error record, and only then form the finite trace or future-faithful quotient. Re-run the final-root extension audit after every enlargement.", styles["Body2"]))
    story.append(callout(
        "Acceptance test C",
        "The horizon is sound and complete for every cited theorem call in the fixture; its branch language is prefix-closed; every marked analytic and prime-end square commutes; and horizon extension introduces no hidden dependency without triggering a re-audit.",
        fill=PALE_AMBER, border=colors.HexColor("#C98A00"),
    ))

    package_d = [
        rich("7. Close proposal: transition, coercivity, and rigidity", styles["H1x"]),
        rich("Work package D - response and Value transition", styles["H2x"]),
        p("Only after the fixture is realized should the response program be applied. The response state must be source-faithful and compositional. The KKL Value coordinate cannot be discarded because a total WAD weight or unweighted port response looks finite; retain the independent Value moments unless a row-space/observability proof makes them redundant. Likewise, a finite support signature does not bound analytic transfer dimension.", styles["Body2"]),
        make_table([
        ["Transition branch", "What must be proved", "Failure disposition"],
        ["Tame / Value branch", "A WAD/Value inequality with actual pullback exponent and uniform coefficient comparability or a finite retained Value vector.", "Keep the Value moments; do not compress to a scalar response."],
        ["Translation-clone branch", "Correct typed incidence orientation, corrected negative-weight clone equation, primitive/non-permutation return, bounded dimension, and explicit entropy gap under realized WAD transport.", "Quarantine any printed equation that fails a matrix counterexample; report the corrected theorem and its extra hypotheses."],
        ["Neutral / shear branch", "A complete transfer trichotomy with transient extinction, sectorial regularization, or finite shear state; frame and Frobenius changes included.", "Do not assign entropy to a gauge-dependent or non-repeatable label."],
        ["Error budget", "Universal calibrated relative/additive/discounted charge over complete blocks.", "If error exceeds the contraction margin, the block is not closed; do not hide it in a universal constant."],
        ], [1.35 * inch, 4.0 * inch, 1.75 * inch], small=True, background=PALE_TEAL),
        callout(
        "Acceptance test D",
        "For the realized fixture, produce an explicit potential and either a backward inequality L_parent >= lambda L_child - C with lambda>1, or a strict forward contraction that is inverted in an error-stable gauge. Constants must be independent of satellite period, chain length, and proof-horizon size except for an explicitly allowed finite prefix.",
        fill=PALE_RED, border=colors.HexColor("#B42318"),
        ),
    ]
    story.append(KeepTogether(package_d))

    story.append(rich("Work package E - analytic coercivity and parameter rigidity", styles["H2x"]))
    story.append(p("The last stage cannot be discharged by the future-observable compactification alone. The required result is a nondegenerate analytic compactness theorem for the marked carriers, maps, relative covers, protected prime ends, response forms, and Value features. Then prove the parameter-side statement that nested connected relative neighborhoods form a basis with diameters tending to zero, or cite an exactly applicable trivial-fiber theorem. Shrinking diameters without connectedness or basis control is insufficient.", styles["Body2"]))
    story.append(make_table([
        ["Gate", "Minimum evidence for closure"],
        ["H3_COERCIVITY", "Every bounded calibrated sequence admits a subsequence converging to an admissible, nondegenerate marked analytic renormalization with preserved proof-use data."],
        ["H4_RIGIDITY", "The marked tower determines connected relative parameter neighborhoods forming a neighborhood basis and shrinking to the parameter, or a precise theorem supplies the same conclusion."],
        ["UPTCR", "All six clauses hold uniformly for every infinitely renormalizable quadratic polynomial, with constants chosen before the tower."],
        ["MLC", "Apply the existing conditional implication only after UPTCR is genuinely proved; keep the target open until then."],
    ], [1.65 * inch, 5.45 * inch], small=True, background=PALE_BLUE))

    story.append(rich("8. Execution order and stop rules", styles["H1x"]))
    story.append(p("This is the recommended next-run order for the long-running goal:", styles["Body2"]))
    for i, text in enumerate([
        "Freeze Block Certificate v1 and its linter; no universal theorem promotion in this step.",
        "Select the smallest nontrivial two-step satellite-copy fixture and realize it analytically in the safe gap.",
        "Compile its complete prefix-local demand schema and Wave horizon; re-run extension and collision audits.",
        "Build the response/Value module on the realized fixture and prove the transition inequality with explicit constants.",
        "Attempt the first coercivity lemma for the fixture; identify exactly which constants or nondegeneration input remain non-uniform.",
        "Only after the fixture passes, generalize by a theorem with hypotheses that are visibly stable under satellite period and chain extension.",
    ], 1):
        story.append(numbered(i, text))
    story.append(callout(
        "Stop rule",
        "If Work Package B fails, do not continue to Work Package D by abstract substitution. Produce a failure certificate and revise the carrier/interface. If Work Package D cannot supply a uniform transition on the realized fixture, do not claim that the formal UPTCR statement is close; narrow the target or identify the missing analytic theorem.",
        fill=PALE_AMBER, border=colors.HexColor("#C98A00"),
    ))

    story.append(rich("9. Verification checklist for the next iteration", styles["H1x"]))
    story.append(p("The checklist below is intended to be copied into the next subtask's work log. A checked box means the corresponding mathematical artifact exists and has evidence, not merely that a prose sentence mentions it.", styles["Body2"]))
    checklist = [
        ("C1", "Actual source/target bases and authorized components are defined.", "VIRTUAL_FINITE_WORD_ROOT_PORTRAIT_AUTHORIZATION; VIRTUAL_CYLINDER_TARGET_ADDRESS_SELECTOR"),
        ("C2", "Every selected branch has a domain, iterate, critical word, degree, localization, and component owner.", "VIRTUAL_RETURN_BASE_ATLAS; MAPPING_TELESCOPE"),
        ("C3", "The carrier is full/nonseparating in the stated localization and all obstacles are included.", "VIRTUAL_ROOT_CARRIER_SEPARATION; VIRTUAL_PROVISIONAL_COMPLEMENT_PAIR"),
        ("C4", "All protected accesses, prime-end phases, and attachment traces survive the construction.", "VIRTUAL_UNPROTECTED_ATOM_EXPOSURE; VIRTUAL_ACCESS_ACTION_CERTIFICATE"),
        ("C5", "The proof-use horizon is frozen before stopping and complete under extension.", "VIRTUAL_WAVE_HORIZON_CERTIFICATE; VIRTUAL_WAVE_DEMAND_SCHEMA"),
        ("C6", "The finite trace/quotient is future-faithful for every declared observable.", "VIRTUAL_VERTEX_PACKAGE_SELECTOR; H2_MEMORY_SAFE_PUMPING_COMPILATION"),
        ("C7", "WAD/Value incidence is typed and compositional; all required Value moments are retained or proved observable.", "H2_RESPONSE_REALIZATION; H2_VALUE_FEATURE_REALIZATION"),
        ("C8", "The transition has a real contraction/expansion inequality with a complete error budget.", "H2_CALIBRATION; H2_FORWARD_CONTRACTION_CALIBRATION; MBTT"),
        ("C9", "Analytic limits are nondegenerate and marked; parameter neighborhoods form a basis.", "H3_COERCIVITY; H4_RIGIDITY"),
        ("C10", "Only after C1-C9 pass is MLC promoted from open.", "UPTCR; MLC"),
    ]
    rows = [["ID", "Acceptance criterion", "Ledger anchors"]]
    rows.extend(list(x) for x in checklist)
    story.append(make_table(rows, [0.42 * inch, 4.05 * inch, 2.63 * inch], small=True, background=PALE_BLUE))

    story.append(rich("10. Work log and handoff", styles["H1x"]))
    story.append(make_table([
        ["Event", "Recorded result"],
        ["Local inventory", "Existing research package contains the main manuscript PDF, source manuscript, 256-item proof ledger, extensive local theorem notes, research log, source ledger, adversarial audit, and reproducibility code."],
        ["Dependency validation", "audit_proof.py passed with an acyclic graph and MLC=open; current counts are 16 imported, 182 proved, 58 open."],
        ["Red-team validation", "audit_transfer_regressions.py passed all listed diagnostic regressions, including orientation, Value incidence, memory/fiber safety, clone multiplier, attachment transport, end obstructions, and telescope counterexamples."],
        ["Numerical validation", "Feigenbaum computation independently re-evaluated through imported functions without writing the existing JSON result; values agree with the repository's reference values to displayed precision."],
        ["Web validation", "Current public records checked for KKL (2026), Dudko (2025/ICM 2026), and BLOT (2022 preprint / 2025 CMP). Scope statements were kept conservative."],
        ["Deliverable boundary", "This PDF is new. Existing main PDFs and source documents were read only; their pre-generation hashes are recorded above. A pre-existing hash change was detected between read-only snapshots and is disclosed above; no recoverable prior copy was found."],
    ], [1.35 * inch, 5.75 * inch], small=True, background=PALE_TEAL))
    story.append(Spacer(1, 0.1 * inch))
    story.append(callout(
        "Handoff",
        "The next meaningful deliverable should be a Block Certificate v1 plus one realized finite virtual block and its complete horizon audit. If that artifact passes, it will justify a narrower transition theorem. If it fails, it will identify the exact analytic obstruction that must be repaired before any universal MLC claim can be credible.",
        fill=PALE_BLUE, border=BLUE,
    ))

    story.append(PageBreak())
    story.append(rich("11. References", styles["H1x"]))
    refs = [
        ("[W1]", "J. Kahn, A. Kapiamba, and M. Lyubich, MLC for parabolically bounded primitive renormalization, arXiv:2606.27272 (submitted 2026-06-25).", "https://arxiv.org/abs/2606.27272"),
        ("[W2]", "D. Dudko, On the MLC Conjecture and the Renormalization Theory in Complex Dynamics, arXiv:2512.24171 (2025; to appear in ICM 2026 proceedings).", "https://arxiv.org/abs/2512.24171"),
        ("[W3]", "A. Blokh, G. Levin, L. Oversteegen, and V. Timorin, Maps with no a priori bounds, arXiv:2205.03157; Commun. Math. Phys. 406, 141 (2025).", "https://arxiv.org/abs/2205.03157"),
        ("[W4]", "Publisher record for W3, DOI 10.1007/s00220-025-05303-8.", "https://doi.org/10.1007/s00220-025-05303-8"),
        ("[L1]", "Unified MLC proof program README and source-locked status boundary.", "research/mlc_unified/README.md"),
        ("[L2]", "Machine-readable proof ledger and dependency graph.", "research/mlc_unified/proof_obligations.json"),
        ("[L3]", "Conditional closure proposition: Universal Protected-Tower Compactness and Rigidity.", "research/mlc_unified/mlc_closure_proposition.md"),
        ("[L4]", "Research Push II assessment and integration record.", "research/mlc_unified/research_push_2_assessment_and_integration.md"),
        ("[L5]", "Virtual Cantor-package realization and finite-trace interface.", "research/mlc_unified/virtual_cantor_package_interface.md"),
        ("[L6]", "Virtual language/memory audit and future-observable compactification.", "research/mlc_unified/virtual_language_memory.md"),
        ("[L7]", "Transfer regression checker and proof audit scripts.", "research/mlc_unified/audit_transfer_regressions.py; research/mlc_unified/audit_proof.py"),
    ]
    for tag, title, link in refs:
        story.append(rich(f"<b>{esc(tag)}</b> {esc(title)}", styles["Body2"]))
        story.append(p(link, styles["URL"]))
        story.append(Spacer(1, 0.03 * inch))

    story.append(Spacer(1, 0.25 * inch))
    story.append(callout(
        "Final status",
        "This sub-research document closes a process gap: it turns the current open-gate inventory into an ordered, testable repair program. It does not close the MLC conjecture. The mathematical target remains open until the analytic realization, transition, coercivity, and rigidity gates are proved with the stated uniformity.",
        fill=PALE_AMBER, border=colors.HexColor("#C98A00"),
    ))

    doc.build(story, onFirstPage=page_decor, onLaterPages=page_decor)
    print(OUT)
    print(json.dumps({"counts": counts, "original_hashes": {str(p): h for p, h in originals}}, indent=2))


if __name__ == "__main__":
    build()
