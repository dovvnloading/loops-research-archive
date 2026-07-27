from pathlib import Path

from pypdf import PdfReader, PdfWriter
from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_LEFT
from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import inch
from reportlab.platypus import (
    BaseDocTemplate,
    Frame,
    PageTemplate,
    Paragraph,
    Spacer,
    Table,
    TableStyle,
    PageBreak,
    KeepTogether,
)


ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "research" / "mlc_unified" / "output" / "pdf" / "mlc_subresearch_corrections_proposal_20260724.pdf"
APPENDIX = ROOT / "research" / "mlc_unified" / "tmp" / "pdfs" / "mlc_actual_closure_appendix_20260725.pdf"
OUT = ROOT / "research" / "mlc_unified" / "output" / "pdf" / "mlc_subresearch_corrections_proposal_actual_closure_attempt_20260725_v24.pdf"

NAVY = colors.HexColor("#12304A")
BLUE = colors.HexColor("#1F608F")
TEAL = colors.HexColor("#087F8C")
PALE_BLUE = colors.HexColor("#E7F2F7")
PALE_TEAL = colors.HexColor("#E7F5F4")
PALE_AMBER = colors.HexColor("#FFF4D8")
PALE_RED = colors.HexColor("#FDEBEB")
MUTED = colors.HexColor("#5B6A78")


def esc(s):
    return (s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))


styles = getSampleStyleSheet()
styles.add(ParagraphStyle("AppendixTitle", parent=styles["Title"], fontName="Helvetica-Bold", fontSize=25, leading=30, textColor=NAVY, alignment=TA_LEFT, spaceAfter=10))
styles.add(ParagraphStyle("AppendixSub", parent=styles["Normal"], fontName="Helvetica", fontSize=12, leading=16, textColor=MUTED, spaceAfter=12))
styles.add(ParagraphStyle("H1x", parent=styles["Heading1"], fontName="Helvetica-Bold", fontSize=18, leading=22, textColor=NAVY, spaceBefore=8, spaceAfter=7, keepWithNext=True))
styles.add(ParagraphStyle("H2x", parent=styles["Heading2"], fontName="Helvetica-Bold", fontSize=13, leading=16, textColor=BLUE, spaceBefore=7, spaceAfter=4, keepWithNext=True))
styles.add(ParagraphStyle("Bodyx", parent=styles["BodyText"], fontName="Helvetica", fontSize=9.5, leading=13, textColor=colors.HexColor("#1E2A35"), spaceAfter=6))
styles.add(ParagraphStyle("Leadx", parent=styles["BodyText"], fontName="Helvetica", fontSize=11, leading=15, textColor=colors.HexColor("#1E2A35"), spaceAfter=8))
styles.add(ParagraphStyle("Smallx", parent=styles["BodyText"], fontName="Helvetica", fontSize=8, leading=10.5, textColor=MUTED, spaceAfter=4))
styles.add(ParagraphStyle("URLx", parent=styles["BodyText"], fontName="Courier", fontSize=7.5, leading=9.5, textColor=BLUE, spaceAfter=4))
styles.add(ParagraphStyle("TableHeadx", parent=styles["BodyText"], fontName="Helvetica-Bold", fontSize=8.5, leading=10, textColor=colors.white))
styles.add(ParagraphStyle("Tablex", parent=styles["BodyText"], fontName="Helvetica", fontSize=8.1, leading=10.2, textColor=colors.HexColor("#1E2A35")))
styles.add(ParagraphStyle("CalloutTitlex", parent=styles["BodyText"], fontName="Helvetica-Bold", fontSize=9.5, leading=12, textColor=colors.HexColor("#1E2A35"), spaceAfter=2))
styles.add(ParagraphStyle("CalloutBodyx", parent=styles["BodyText"], fontName="Helvetica", fontSize=9.3, leading=12.5, textColor=colors.HexColor("#1E2A35")))


def p(text, style="Bodyx"):
    return Paragraph(esc(text), styles[style])


def rich(text, style="Bodyx"):
    return Paragraph(text, styles[style])


def callout(title, body, fill, border):
    t = Table([[rich(f"<b>{esc(title)}</b>", "CalloutTitlex")], [p(body, "CalloutBodyx")]], colWidths=[7.08 * inch])
    t.setStyle(TableStyle([
        ("BACKGROUND", (0, 0), (-1, -1), fill),
        ("BOX", (0, 0), (-1, -1), 1.1, border),
        ("LEFTPADDING", (0, 0), (-1, -1), 10),
        ("RIGHTPADDING", (0, 0), (-1, -1), 10),
        ("TOPPADDING", (0, 0), (-1, -1), 7),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 7),
    ]))
    return t


def table(rows, widths, background=PALE_BLUE):
    converted = []
    for ri, row in enumerate(rows):
        converted.append([
            rich(esc(str(cell)), "TableHeadx" if ri == 0 else "Tablex") for cell in row
        ])
    t = Table(converted, colWidths=widths, repeatRows=1, hAlign="LEFT")
    commands = [
        ("BACKGROUND", (0, 0), (-1, 0), NAVY),
        ("GRID", (0, 0), (-1, -1), 0.35, colors.HexColor("#B8C9D8")),
        ("VALIGN", (0, 0), (-1, -1), "TOP"),
        ("LEFTPADDING", (0, 0), (-1, -1), 6),
        ("RIGHTPADDING", (0, 0), (-1, -1), 6),
        ("TOPPADDING", (0, 0), (-1, -1), 5),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 5),
    ]
    for ri in range(1, len(rows)):
        commands.append(("BACKGROUND", (0, ri), (-1, ri), background if ri % 2 else colors.white))
    t.setStyle(TableStyle(commands))
    return t


def decor(canvas, doc):
    w, h = letter
    canvas.saveState()
    canvas.setStrokeColor(colors.HexColor("#C5D5E0"))
    canvas.setLineWidth(0.6)
    canvas.line(doc.leftMargin, h - 0.42 * inch, w - doc.rightMargin, h - 0.42 * inch)
    canvas.setFont("Helvetica", 7.4)
    canvas.setFillColor(MUTED)
    canvas.drawString(doc.leftMargin, 0.38 * inch, "MLC actual closure attempt - appendix - 2026-07-26")
    canvas.drawRightString(w - doc.rightMargin, 0.38 * inch, f"page {doc.page}")
    canvas.restoreState()


def build_appendix():
    APPENDIX.parent.mkdir(parents=True, exist_ok=True)
    doc = BaseDocTemplate(
        str(APPENDIX), pagesize=letter, leftMargin=0.7 * inch, rightMargin=0.7 * inch,
        topMargin=0.62 * inch, bottomMargin=0.58 * inch,
        title="MLC Actual Closure Attempt - Proof Frontier",
        author="Codex - separate research artifact",
    )
    frame = Frame(doc.leftMargin, doc.bottomMargin, doc.width, doc.height, id="normal")
    doc.addPageTemplates([PageTemplate(id="main", frames=frame, onPage=decor)])
    story = []
    story.append(Spacer(1, 0.12 * inch))
    story.append(rich("Appendix: actual MLC closure attempt", "AppendixTitle"))
    story.append(p("This appendix is added to the earlier sub-research proposal. It changes the active objective from documenting a conditional route to attempting the actual theorem. The main manuscript and original PDFs remain read-only.", "AppendixSub"))
    story.append(callout(
        "Status boundary",
        "The Mandelbrot local connectivity conjecture is not proved here. The purpose of this appendix is to identify the first source-faithful analytic theorem required for a real proof and to record why the existing virtual-carrier interface cannot be promoted.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.12 * inch))

    story.append(rich("A.1 The actual target", "H1x"))
    story.append(p("The local proof ledger contains 256 obligations: 182 proved internally, 16 imported, and 58 open. The conditional implication UPTCR => MLC is not the same as proving UPTCR. The first decisive gap is the construction of actual dynamical-plane renormalization data for unbounded satellite and virtual near-molecule scales.", "Leadx"))
    story.append(table([
        ["Layer", "Current state", "What a real closure must add"],
        ["Conditional endgame", "UPTCR => MLC is recorded as a conditional reduction.", "A proof of every UPTCR clause with source-faithful hypotheses."],
        ["Virtual carrier", "Finite traces and pullback compilers are conditional interfaces.", "An actual carrier, return maps, domains, accesses, critical chronology, and marking."],
        ["Analytic compactness", "H3 coercivity and H4 rigidity are open.", "Nondegenerate marked limits and shrinking connected parameter pieces."],
        ["Global scope", "MLC remains open in the local ledger and current primary sources.", "Coverage of every remaining unbounded/mixed renormalization sequence."],
    ], [1.25 * inch, 2.65 * inch, 3.18 * inch], PALE_TEAL))

    story.append(rich("A.2 Literature boundary", "H1x"))
    story.append(p("Kahn-Kapiamba-Lyubich prove beau bounds and rigidity for parabolically bounded families of prime primitive types. Their introduction explicitly identifies further primitive classes and the virtual renormalization program as remaining work. Dudko's survey names the remaining unbounded satellite bounds as Problem 4.3 and the virtual-Molecule interpolation as Problem 4.4. These papers are valuable inputs, not an all-parameter proof.", "Bodyx"))
    story.append(table([
        ["Source", "What can be imported", "What cannot be imported"],
        ["KKL 2026", "Theorem A-C in the stated parabolically bounded prime primitive class.", "A universal theorem for arbitrary mixed or virtual towers."],
        ["Dudko 2025/2026", "The regime taxonomy, known bounded/neutral results, and the stated proof frontier.", "The conjectural unified renormalization operator or virtual near-molecule interpolation."],
        ["Local program", "Conditional reductions, exact local lemmas, and adversarial no-go results.", "The existence of the missing analytic virtual objects."],
    ], [1.25 * inch, 2.85 * inch, 2.98 * inch], PALE_BLUE))
    story.append(p("Primary sources: https://arxiv.org/html/2606.27272 and https://arxiv.org/html/2512.24171", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.3 Uniform near-molecule rigidity theorem", "H1x"))
    story.append(p("The next theorem target is intentionally analytic rather than symbolic:", "Leadx"))
    story.append(callout(
        "Theorem target",
        "For every infinitely renormalizable quadratic polynomial whose scales contain unbounded satellite or virtual near-molecule levels, construct actual normalized first-return data and prove analytic realization, uniform degeneration control, marked transport, and connected parameter neighborhoods with diameters tending to zero.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(table([
        ["Required output", "Minimum certificate"],
        ["Analytic realization", "Actual domains/codomains, iterate, critical orbit, and hybrid normalization for every selected return."],
        ["Uniform control", "A ql modulus bound or a pseudo-Siegel/sectorial replacement with a proved compactness estimate."],
        ["Marked transport", "Ideal/access marking and protected postcritical data transported through the return and chart changes."],
        ["Rigidity", "Connected relative parameter neighborhoods forming a basis and shrinking to the parameter."],
    ], [1.65 * inch, 5.43 * inch], PALE_AMBER))

    story.append(rich("A.4 Two-branch proof strategy", "H1x"))
    story.append(table([
        ["Branch", "Proof obligation", "Closure test"],
        ["E: renorm-expanding", "Build actual puzzle/parapuzzle returns, expansion on every proof-relevant branch, distortion transfer, and parameter-scale decay.", "Nested parameter pieces have diameter tending to zero; invoke the Yoccoz rigidity endgame."],
        ["B: renorm-balanced", "Construct a nondegenerate normalized marked limit and prove ql, cylinder, sectorial, pseudo-Siegel, or virtual near-molecule compactness plus parameter rigidity.", "Marked limits remain admissible and the parameter fiber is a singleton."],
    ], [1.35 * inch, 3.95 * inch, 1.78 * inch], PALE_RED))
    story.append(p("The universal form of this dichotomy is not yet a theorem. It is therefore a proof target, not a status promotion.", "Smallx"))

    story.append(rich("A.5 First attempted lemma", "H1x"))
    story.append(p("If a problematic renormalization sequence has a normalized subsequence with a nondegenerate marked analytic limit and the associated parameter pieces have uniformly bounded puzzle Teichmuller diameter, then the parameter fiber is a singleton and the pieces shrink to the parameter. This is the standard rigidity endgame and matches the local conditional reduction.", "Bodyx"))
    story.append(callout(
        "Obstruction found",
        "The current sources and local program do not prove either hypothesis in the mixed virtual regime. A finite word, terminal Hubbard tree, or compact symbolic encoding does not construct the analytic map, preserve prime ends, or prevent collapse. That is exactly why H3_COERCIVITY and H4_RIGIDITY remain open.",
        PALE_RED, colors.HexColor("#B42318"),
    ))
    story.append(Spacer(1, 0.08 * inch))
    story.append(rich("A.5a First failed finite square", "H2x"))
    story.append(p("The new certificate virtual_s2_corridor_root_compatibility_failure_20260725.md isolates the first domain-typing failure. The outer inverse branch phi_w is defined on the outer puzzle piece P, while the native terminal return is f^p_term:A_0 -> B. The checked sources give A_0 compactly contained in B and K_0 compactly contained in the outer piece, but do not give A_0 or B contained in the outer piece, or an analytic extension of phi_w to those domains. Therefore the attempted conjugate phi_w o f^p_term o phi_w^{-1} is not an analytic map on stated domains. This is a concrete corridor failure, not a symbolic objection.", "Bodyx"))

    story.append(PageBreak())
    story.append(rich("A.6 Concrete next proof certificate", "H1x"))
    story.append(p("Next research object: one explicit unbounded-satellite or near-molecule sequence, not another universal interface. It must contain:", "Leadx"))
    for i, item in enumerate([
        "the actual quadratic polynomial and nested return domains",
        "all return times and critical-value images",
        "normalized maps and hybrid coordinate changes",
        "protected access and prime-end data",
        "the relevant modulus, extremal-width, or pseudo-Siegel estimate",
        "the parameter parapuzzle and relative-boundary control",
        "a failure certificate if any field cannot be constructed",
    ], 1):
        story.append(rich(f"<font color='{TEAL.hexval()}'><b>{i}.</b></font> {esc(item)}", "Bodyx"))
    story.append(Spacer(1, 0.08 * inch))
    story.append(callout(
        "Stop condition",
        "If the first explicit certificate cannot be built, record the exact missing domain, collision, lost access, or degeneration mechanism. Do not promote the universal theorem or claim MLC from the failed construction.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(rich("A.7 Evidence record", "H1x"))
    story.append(table([
        ["Check", "Result"],
        ["Local ledger audit", "Valid ledger; 256 obligations; target MLC remains open."],
        ["Transfer regression suite", "All diagnostic transfer regressions passed; these are consistency tests, not analytic existence proofs."],
        ["Primary literature check", "Current public sources confirm scoped results and an unresolved global frontier."],
        ["Deeper virtual-scale attempt", "virtual_s2_failure_certificate_20260725.json records the first missing object Xi_2 and keeps the affected obligations open."],
        ["Off-critical degree lemma", "Finite outer cylinders are univalent; any degree-two Xi_2 return must cross a separately constructed critical/root transition."],
        ["Partial root certificate", "virtual_s2_partial_root_transition_certificate_20260725.md records the native degree-two root return and ideal side, but not the virtual corridor-to-root bridge."],
        ["Finite-decoration branch", "finite_decoration_branch_closure_20260725.md closes the bounded-decoration branch using the source's beau a priori bounds and explicit MLC corollary."],
        ["Bounded-type ql branch", "bounded_type_ql_branch_closure_20260725.md records Dudko's Theorem 4.1: bounded-type ql-combinatorics have a priori bounds and MLC."],
        ["Unbounded-satellite sector bridge", "unbounded_satellite_sector_bridge_attempt_20260725.md proves the sector chronology and records the first missing analytic comparison map."],
        ["Quadratic-growth satellite branch", "satellite_quadratic_growth_branch_closure_20260725.md imports Cheraghi-Shishikura Theorem D: QG_N satellite fibers shrink exponentially and MLC holds at the parameter."],
        ["Levin fast-satellite branches", "levin_fast_satellite_branch_closure_20260725.md imports Levin's exponential-growth and fast-small-rotation MLC conclusions."],
        ["Levin Theorem 7 extension", "levin_theorem7_extended_branch_closure_20260725.md records the broader (Y0a),(Y0b),(Y1) criterion, including root-to-one witnesses."],
        ["Artifact boundary", "This appendix is a new PDF artifact. Original manuscript and original PDFs are not written."],
    ], [1.65 * inch, 5.43 * inch], PALE_BLUE))
    story.append(PageBreak())
    story.append(rich("A.8 Unbounded-satellite sector bridge", "H1x"))
    story.append(p("The latest sector-renormalization source gives a precise compact symbolic model for a near-neutral degeneration. This pass tests whether that model can be transferred to an arbitrary satellite quadratic-like return with relative period tending to infinity.", "Leadx"))
    story.append(callout(
        "Arithmetic result proved",
        "For the sector parameters theta_n, signs epsilon_n, digits a_bar_n, and return recurrences p_[n], Q_[n], direct substitution gives Q_[n] theta - p_[n] = (epsilon_1 ... epsilon_n) theta_0 ... theta_n. Therefore the closest-return error has an exact product formula, and a first digit tending to infinity records theta tending to zero together with an explicit parabolic infinity symbol.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(table([
        ["Layer", "What is now checked", "Limit"],
        ["Sector chronology", "Orientation, return digits, sign-sensitive recurrence, and closest-return error.", "Valid in Lim's rigid-rotation/neutral-sector model."],
        ["Parabolic compactification", "An unbounded first digit is retained as infinity rather than discarded.", "Topological/symbolic only."],
        ["Satellite return", "A normalized ql return with Q_sat tending to infinity.", "No source-faithful comparison to the neutral model yet."],
        ["MLC transfer", "Would require pseudo-Siegel bounds plus marked parameter transport.", "Still open."],
    ], [1.35 * inch, 3.35 * inch, 2.38 * inch], PALE_BLUE))
    story.append(p("Primary sources: https://arxiv.org/html/2607.11408v1 and https://arxiv.org/html/2512.24171", "URLx"))

    story.append(rich("A.9 The failed analytic square", "H1x"))
    story.append(p("Let R_j be satellite quadratic-like returns, alpha_j their marked periodic point, and L_j(z)=alpha_j+s_j z a candidate normalization. The attempted transfer forms G_j=L_j^{-1} o R_j o L_j and compares it with f_theta(z)=exp(2 pi i theta)z+z^2 using the limiting multiplier. A valid comparison H_j must preserve the critical orbit, access/prime-end marking, return chronology, annular moduli, and parameter parapuzzle boundaries on a region containing the full pseudo-Siegel nest.", "Bodyx"))
    story.append(callout(
        "First missing analytic field",
        "The checked sources give the neutral model and its pseudo-Siegel bounds, but do not give H_j from an arbitrary satellite return to that neutral model on the required domain. Matching the multiplier, or invoking an unqualified hybrid straightening, does not preserve the needed annuli, accesses, and parameter boundaries. The missing theorem is a uniform satellite-to-sector comparison package.",
        PALE_RED, colors.HexColor("#B42318"),
    ))

    story.append(PageBreak())
    story.append(rich("A.10 Machine evidence and repaired gap map", "H1x"))
    story.append(p("Companion validation script: 80-digit Decimal arithmetic checks the sector recurrence/product identity for three ordinary irrational inputs and one near-zero input with first digit 8100. It returns SECTOR_ARITHMETIC_VALID. This validates the transcription and chronology only; it does not numerically prove MLC or the analytic bridge.", "Leadx"))
    story.append(table([
        ["Certificate", "Status"],
        ["validate_sector_bridge_attempt.py", "Passed; maximum displayed absolute identity error below 2.4e-72 across the listed tests."],
        ["unbounded_satellite_sector_bridge_attempt_20260725.json", "Parsed successfully; original_artifacts_written=false."],
        ["SECTOR_ARITHMETIC", "Proved from the published recurrence."],
        ["PARABOLIC_SYMBOL", "Proved as a compact-symbol statement."],
        ["SATELLITE_TO_SECTOR_ANALYTIC_COMPARISON", "Open: full-domain conformal or uniformly controlled quasiconformal comparison H_j."],
        ["UNBOUNDED_SATELLITE_MLC", "Open; this is Dudko's Problem 4.3 in the checked survey."],
        ["VIRTUAL_MOLECULE_INTERPOLATION", "Open; the primitive-to-satellite carrier and critical horizon remain unbuilt."],
        ["MLC", "Open; the global target is not promoted."],
    ], [2.45 * inch, 4.63 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.16 * inch))
    story.append(KeepTogether([callout(
        "Current conclusion",
        "This pass closes the sector chronology defect and narrows the unbounded-satellite gap to one explicit analytic comparison theorem. It does not close Problem 4.3, Problem 4.4, or the MLC conjecture. The research goal remains active; original documents remain untouched.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    )]))

    story.append(PageBreak())
    story.append(rich("Imported satellite rigidity closures (A.11)", "H1x"))
    story.append(p("The literature audit found two source-faithful satellite branches that should be removed from the undifferentiated open bucket. These are parameter-rigidity theorems and do not claim uniform postcritical a priori bounds.", "Leadx"))
    story.append(table([
        ["Branch", "Exact hypothesis", "Conclusion"],
        ["Cheraghi-Shishikura QG_N", "Modified continued-fraction entries grow quadratically within and between blocks; the source supplies an existential threshold N.", "Finite satellite parameter fibers have diameter at most C lambda^n; rigidity and MLC at the limit parameter."],
        ["Levin exponential growth", "limsup log(abs(p_m))/n_m > 0; for satellite subsequences, limsup log(q_m)/n_m > 0 suffices.", "MLC at the parameter."],
        ["Levin fast-small rotation", "All levels satellite; q_m tends to infinity; limsup abs(t_{m+1})^(1/q_m) < 1.", "MLC at the limit parameter; Julia LC may fail."],
        ["Levin Theorem 7", "Conditions (Y0a), (Y0b), and (Y1) on the product growth and rotation data.", "MLC at the limit parameter; includes some root-to-one sequences."],
    ], [1.55 * inch, 3.15 * inch, 2.58 * inch], PALE_TEAL))
    story.append(p("Primary sources: https://arxiv.org/pdf/1509.07843 and https://arxiv.org/pdf/0710.4406", "URLx"))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Scope correction",
        "These theorems close named growth subclasses only. They do not imply that every unbounded satellite sequence satisfies a growth condition, and they do not construct the missing virtual-Molecule carrier or interpolation theorem.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))

    story.append(rich("A.12 Updated global gap map", "H1x"))
    story.append(table([
        ["Status", "Branches"],
        ["Closed/imported", "Finite decorations; bounded-type ql; QG_N quadratic-growth satellites; Levin exponential-growth satellites; Levin fast-small-rotation cascades; Levin Theorem 7 (Y0a/Y0b/Y1) branch."],
        ["Still open", "Unbounded satellites failing these growth tests; virtual bounded-type satellite towers; virtual near-neutral Molecule towers; mixed renormalization; global MLC."],
        ["Verification", "Both new source validators pass with locked SHA-256 hashes; original_artifacts_written=false; global ledger remains 256 obligations with MLC open."],
    ], [1.35 * inch, 5.73 * inch], PALE_BLUE))
    story.append(Spacer(1, 0.16 * inch))
    story.append(KeepTogether([callout(
        "Current conclusion",
        "The active proof frontier is now smaller: the remaining satellite problem is the complement of several explicit theorem-covered growth classes, plus the virtual-Molecule interpolation. The global MLC goal remains active and is not promoted to complete.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    )]))

    story.append(PageBreak())
    story.append(rich("A.13 Coverage-complement audit", "H1x"))
    story.append(p("The imported QG_N and Levin closures are sufficient criteria, not an exhaustive classification. The new companion audit tests the finite satellite data q_m=m+3, p_m=1, t_m=1/(m+3). Every entry is coprime, nonzero, and lies in the allowed rotation interval, but the sequence fails each imported growth test.", "Leadx"))
    story.append(table([
        ["Imported test", "Exact failure for q_m=m+3"],
        ["Cheraghi-Shishikura QG_N", "q_(m+1)=q_m+1<q_m^2, so pure-satellite quadratic denominator growth fails."],
        ["Levin Theorem 1", "log(q_m)/(q_0...q_(m-1)) tends to 0, not a positive limsup."],
        ["Levin Theorem 2", "|t_(m+1)|^(1/q_m)=(1/(m+4))^(1/(m+3)) tends to 1, not below 1."],
        ["Levin Theorem 7", "(Y0a) diverges and (Y1) tends to 0 for every fixed beta>0."],
    ], [2.05 * inch, 5.03 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Important logical boundary",
        "This is a coverage counterexample at the level of finite admissible rotation data, not an existence theorem for a limiting quadratic parameter. It blocks an invalid exhaustion argument; it does not prove that the witness is realized by an infinitely renormalizable polynomial. Closing the complement requires a new realizability-plus-pseudo-Siegel theorem, followed by the virtual-Molecule interpolation and rigidity step.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(p("Machine certificate: validate_satellite_coverage_complement.py. Primary sources: https://arxiv.org/pdf/1509.07843 and https://arxiv.org/pdf/0710.4406", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.14 Transitional bridge theorem", "H1x"))
    story.append(p("The neutral pseudo-Siegel machinery is not directly applicable to a rational satellite return. The source's psi-bullet-ql theorem assumes an actual Siegel disk and full covering-embedding data for the iterated fiber products; its transitional-scale case also requires external input. The next theorem must therefore supply a satellite-to-neutral bridge with five independent gates.", "Leadx"))
    story.append(table([
        ["Gate", "Required source-faithful output"],
        ["B1 Neutralization", "Actual holomorphic family and limit recovering the marked satellite return, with domains, critical orbit, return time, hybrid normalization, and access marking."],
        ["B2 psi-bullet-ql admissibility", "Degree-two proper map, Siegel restriction, and covering embeddings for every fiber-product iterate."],
        ["B3 Transitional control", "Uniform vertical/peripheral bound or a quantified exponential boost surviving satellite pullback."],
        ["B4 Parameter transfer", "Uniformly controlled transfer of tilings, accesses, critical chronology, and parapuzzle boundaries."],
        ["B5 Infinite assembly", "Summable or telescoping distortion and non-invariance errors over the unbounded tower."],
    ], [1.63 * inch, 5.45 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "First unavoidable obstruction",
        "At a rational satellite root the marked cycle is parabolic, not Siegel. Matching only the multiplier or rotation number therefore does not produce the neutral theorem's hypotheses, and hybrid straightening does not automatically preserve the full pseudo-Siegel nest and parameter boundaries. B1--B5 remain unproved; the global MLC target stays open.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(p("Primary sources: https://arxiv.org/html/2509.23031 and https://arxiv.org/html/2512.24171", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.15 Exact parabolic satellite anchor", "H1x"))
    story.append(p("The smallest nontrivial satellite anchor can be constructed exactly. Set lambda=exp(2*pi*i/3), z_alpha=lambda/2, and c_(1/3)=z_alpha-z_alpha^2=-1/8+(3/8)*sqrt(-3). Then f_c has a fixed point with multiplier lambda, so f_c^3 has multiplier 1. In the coordinate w=z-z_alpha, one iterate is w -> lambda*w+w^2.", "Leadx"))
    story.append(table([
        ["Exact check", "Result"],
        ["Third-iterate multiplier", "lambda^3=1; the fixed point is parabolic for f_c^3."],
        ["Quadratic coefficient of f_c^3", "0, by 1+lambda+lambda^2=0."],
        ["Cubic coefficient of f_c^3", "0, by the same primitive-third-root cancellation."],
        ["Quartic coefficient", "(9+sqrt(-3))/2, nonzero; the cylinder/Lavaurs scale is genuine."],
    ], [2.25 * inch, 4.83 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Bridge repair",
        "The finite anchor rules out treating a rational satellite root as a Siegel map. The uniform theorem must first construct a marked parabolic/cylinder pair and transitional map, then connect it to sector or pseudo-Siegel control while preserving Ecalle phase, critical access, and parameter boundaries. The exact anchor is proved; uniform cylinder bounds, Molecule hyperbolicity, virtual interpolation, and global MLC remain open.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(p("Machine certificate: validate_parabolic_satellite_anchor.py. Source context: https://arxiv.org/html/2512.24171, Sections 3.5--3.8.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.16 Finite primitive-root family sweep", "H1x"))
    story.append(p("The single 1/3 anchor is not an isolated numerical coincidence. A second exact validator works in the cyclotomic quotient Q[x]/(Phi_q(x)) and computes the local germ g(w)=lambda*w+w^2 through degree q+1 for every order q from 2 through 16.", "Leadx"))
    story.append(table([
        ["Exact finite check", "Result for q = 2,...,16"],
        ["Multiplier data", "lambda is represented by x; Phi_q(x)=0 and x^q=1 in the exact quotient."],
        ["Parameterization", "z_alpha=lambda/2 and c=lambda/2-lambda^2/4 give an exact fixed point with multiplier lambda."],
        ["Iterated germ", "The coefficient of w in g^q is 1; coefficients of w^2 through w^q are all exactly zero."],
        ["Parabolic term", "The coefficient of w^(q+1) is nonzero in Q[x]/(Phi_q(x)) for every checked order."],
        ["q=3 cross-check", "The coefficient is x+5; at x=(-1+sqrt(-3))/2 this is (9+sqrt(-3))/2, matching A.15."],
    ], [1.75 * inch, 5.33 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "What this closes",
        "The local finite anchor family is now exact and reproducible through q=16. It verifies that every checked primitive satellite order enters a genuine parabolic normal form, so the bridge must carry cylinder/Lavaurs data rather than silently substitute a Siegel disk.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(callout(
        "What this does not close",
        "A finite sweep is not an all-q theorem, does not give uniform cylinder moduli or Ecalle-phase transport, and does not realize an arbitrary infinite satellite tower. The remaining global obstruction is still the source-faithful marked parabolic-to-cylinder-to-parameter bridge, followed by Molecule interpolation and rigidity.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Machine certificate: validate_parabolic_root_family.py; output: parabolic_root_family_20260726.json; all exact checks passed; original_artifacts_written=false. Source context: https://arxiv.org/html/2512.24171.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.17 Source-backed no-bound obstruction", "H1x"))
    story.append(p("A new primary-source audit rules out a tempting shortcut for the unbounded-satellite complement. Blokh--Levin--Oversteegen--Timorin give an upper bound for a satellite polynomial-like cycle whose relative period is s. In the quadratic degree-two case, the bound specializes to 2*pi/log(4*(s+1)).", "Leadx"))
    story.append(table([
        ["Source-backed fact", "Closure consequence"],
        ["(d_star-1) mod(U minus K_star) < d_star(d_star-1)pi/log(4(s+1)).", "For d_star=2 and s tending to infinity, the available upper bound tends to zero."],
        ["The theorem applies to satellite PL cycles with unbounded relative periods.", "A uniform positive lower ql modulus cannot cover the unbounded-satellite branch."],
        ["The estimate is an upper bound, not a lower-bound failure certificate for every individual return.", "It does not prove non-local-connectivity and does not settle MLC."],
    ], [3.55 * inch, 3.53 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Bridge target repaired again",
        "The remaining proof must tolerate degenerating root/fundamental annuli and retain the parabolic cylinder, Lavaurs transitional map, Ecalle phase, critical access, and parameter-boundary data. A source-faithful closure cannot simply promote the unbounded satellite returns to uniformly bounded quadratic-like maps.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Status",
        "The no-bound estimate narrows the obstruction but does not provide the missing cylinder-to-parameter rigidity theorem. Unbounded satellite MLC and virtual-Molecule interpolation remain open, so the global objective remains active.",
        PALE_RED, colors.HexColor("#B42318"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Machine certificate: validate_unbounded_satellite_no_bounds.py; output: unbounded_satellite_no_bounds_20260725.json. Primary source: https://publications.hse.ru/pubs/share/direct/1052158150.pdf.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.18 Elephant Eyes branch closure audit", "H1x"))
    story.append(p("A newly checked 2026 source covers a genuinely unbounded but precisely typed branch. Kahn--Lyubich assume an even quadratic-like map with connected Julia set, both fixed points repelling, Elephant Eye sector combinatorics, rotation 1/q, and renormalization period p=q+b with bounded b while q tends to infinity.", "Leadx"))
    story.append(table([
        ["Branch field", "Audited result"],
        ["Combinatorics", "Source E1--E3: rotation 1/q, central-sector uniqueness, and p=q+b with bounded b."],
        ["Analytic estimate", "The source proves a priori bounds using uniform thin--thick decompositions and an amplification theorem."],
        ["MLC status", "Section 8 states the corresponding MLC conclusion, but explicitly invokes Ecalle--Voronin-cylinder little copies and the DLP project, marked in preparation."],
        ["Global implication", "This branch is removed from the unclassified a-priori-bound bucket; arbitrary unbounded towers and the cylinder-copy dependency remain open."],
    ], [1.55 * inch, 5.53 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Import boundary",
        "The a-priori-bound theorem is source-locked and imported for the stated Elephant Eyes class. The MLC consequence is kept dependency-audited rather than promoted as an independent completed proof, because the source cites a DLP result that it labels in preparation. This prevents a hidden source-status error while still closing the analytic branch that the paper actually proves.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Remaining global gap",
        "The missing theorem must still handle unbounded satellite towers outside p=q+O(1) Elephant Eye combinatorics, supply the Ecalle-cylinder little-copy/parameter transfer in a published source-faithful form, and solve virtual-Molecule interpolation and rigidity.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Machine certificate: validate_elephant_eye_branch.py; output: elephant_eye_branch_20260725.json; source SHA-256 locked; original_artifacts_written=false. Source: https://arxiv.org/html/2601.21905.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.19 Neutral-attractor rigidity correction", "H1x"))
    story.append(p("A current public 2026 sector-renormalization note records a stronger neutral branch than the older survey-level gap map. It reports that sector renormalizations of neutral quadratic polynomials can be chosen precompact and capture the critical orbit well. Its compactification keeps infinity entries, simple parabolic bifurcations, the full Lavaurs-Epstein tower, top/bottom Lavaurs data, parabolic blow-ups, and cyclic critical-orbit order.", "Leadx"))
    story.append(table([
        ["Neutral branch field", "Source-locked result and boundary"],
        ["Combinatorial theorem", "Theorem 1.1 ([DLL26]) states that the full renormalization attractor for neutral quadratic polynomials is combinatorially rigid and, modulo conformal conjugacy, conjugate to the shift on the natural-extension compactification."],
        ["Rigidity mechanism", "The proof summary uses uniform complex bounds for neutral cascades and an affine conjugacy between combinatorially equivalent cascades; the Brjuno subcase has an analytic translational-cascade model."],
        ["Degeneration data", "Infinity entries encode simple parabolic bifurcation, while Lavaurs enrichment and critical-orbit order are retained rather than collapsed."],
        ["Status", "The public note identifies [DLL26] as a 2026 manuscript. This audit imports the reported neutral-attractor result with that status visible; it does not silently treat it as an independently published proof."],
        ["Independent cross-check", "A 10 June 2026 Stony Brook seminar listing describes the same result as rigidity for all irrational rotations and all possible parabolic bifurcations, with pseudo-Siegel bounds in the proof. This corroborates scope, not the unpublished proof itself."],
    ], [1.65 * inch, 5.43 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Branch closure contribution",
        "The neutral-cascade rigidity interface is no longer an entirely unaddressed obligation if the cited manuscript theorem is accepted. This repairs the neutral branch of the gap map and preserves the parabolic/cylinder data needed at infinity.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Global MLC boundary",
        "The theorem does not construct a comparison from every arbitrary unbounded satellite quadratic-like return to the neutral attractor. It also does not supply virtual-Molecule interpolation, critical-horizon transport, or global parameter rigidity. Unbounded satellite MLC outside the typed branches and the global MLC conjecture therefore remain open.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Machine certificate: validate_neutral_attractor_rigidity.py; output: neutral_attractor_rigidity_20260725.json; source SHA-256 locked; original_artifacts_written=false. Primary source: https://arxiv.org/html/2607.11408v1. Cross-check: https://www.math.stonybrook.edu/cal/agenda.php?LocationID=10. Core theorem reference in primary source: [DLL26], manuscript.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.20 Current global-status audit", "H1x"))
    story.append(p("The final web cross-check was aimed at the user's actual objective: whether a complete global MLC theorem is already available and can be imported to close the remaining ledger. The checked sources do not support that conclusion.", "Leadx"))
    story.append(table([
        ["Checked source", "What it establishes", "Boundary relevant to global MLC"],
        ["Dudko, arXiv:2512.24171", "Defines MLC as a conjecture and summarizes the current program as remaining unbounded satellite cases plus interpolation between positive- and zero-entropy regimes.", "This directly matches the open H4/virtual-Molecule interfaces in the local ledger."],
        ["Kahn--Kapiamba--Lyubich, arXiv:2606.27272", "Proves a priori bounds and MLC for a class of parabolically bounded primitive infinitely renormalizable parameters.", "The abstract says 'a class'; it is not a theorem for every quadratic parameter or every satellite tower."],
        ["Lim, arXiv:2607.11408v1 plus the SBU seminar listing", "Neutral-attractor rigidity is reported for the neutral renormalization branch, with parabolic enrichments retained.", "The result does not supply the arbitrary satellite-to-neutral comparison or virtual-Molecule parameter interpolation."],
    ], [1.63 * inch, 2.85 * inch, 2.6 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.16 * inch))
    story.append(callout(
        "Accurate conclusion",
        "The research packet now closes or imports several explicit subclasses and repairs the neutral-attractor status map, but the global MLC conjecture is not solved by the checked literature or by the local computations. The remaining proof target is a source-faithful satellite/cylinder-to-parameter bridge together with virtual-Molecule interpolation and rigidity.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(p("Primary sources: https://arxiv.org/html/2512.24171 and https://arxiv.org/abs/2606.27272. Neutral branch sources: https://arxiv.org/html/2607.11408v1 and https://www.math.stonybrook.edu/cal/agenda.php?LocationID=10. This page records a status audit, not a claim of completion; original documents remain untouched.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.21 KKL frontier taxonomy and next theorem", "H1x"))
    story.append(p("The June 2026 KKL paper gives a sharper source-locked description of what remains. It classifies prime-type families by eventual limb depth l, continued-fraction height h, and continued-fraction depth d, separating bounded satellite, near-parabolic, near-neutral, and virtually-satellite regimes.", "Leadx"))
    story.append(table([
        ["Regime", "Source taxonomy", "Closure status"],
        ["Anti-molecule / bounded satellite", "l, h, d bounded.", "Covered by bounded-combinatorics results already imported in this packet."],
        ["Near-parabolic", "h unbounded, l and d bounded.", "KKL closes a parabolically bounded primitive subfamily; the general primitive case remains beyond that theorem."],
        ["Near-neutral", "d unbounded, l bounded.", "Neutral sectorial rigidity and bounds are source-backed, but rational satellite/cylinder transfer remains unproved."],
        ["Virtually-satellite", "l unbounded.", "Virtual near-molecule primitive renormalization is listed as in preparation; carrier, interpolation, and rigidity remain open."],
    ], [1.65 * inch, 2.25 * inch, 3.18 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Critical wording correction",
        "The KKL paper says the neutral theory is believed to be promotable to all forms of unbounded satellite renormalization. That is a research direction, not a theorem. The same paper lists virtual renormalization as in preparation. Neither statement can close the global objective without the missing analytic and parameter-rigidity proofs.",
        PALE_RED, colors.HexColor("#B42318"),
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Next exact theorem target",
        "Prove a source-faithful sectorial/cylinder extension for every realizable unbounded satellite tower, then prove the virtual carrier and parameter interpolation for l tending to infinity. These are now the named global interfaces, not an undifferentiated gap.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Machine certificate: validate_kkll_global_taxonomy.py; output: kkll_global_taxonomy_20260725.json; source SHA-256 locked; original_artifacts_written=false. Source: https://arxiv.org/html/2606.27272. The global MLC target remains open.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.22 All-q resonance cancellation lemma", "H1x"))
    story.append(p("The finite primitive-root sweep can be strengthened, but only in a clearly delimited direction. For a primitive q-th root lambda and the local quadratic germ g(w)=lambda*w+w^2, the q-th iterate has no terms of degrees 2 through q for every q. The proof is a formal commutation argument, not a numerical extrapolation.", "Leadx"))
    story.append(table([
        ["Step", "Exact argument"],
        ["Set F", "F=g^q; F'(0)=lambda^q=1."],
        ["Use commutation", "F o g = g o F because both maps are iterates of g."],
        ["Let m be first nonzero degree", "If F(w)=w+a_m*w^m+O(w^(m+1)), then comparing degree m gives a_m*lambda^m=a_m*lambda."],
        ["Use primitivity", "a_m != 0 implies lambda^(m-1)=1, hence q divides m-1 and m is at least q+1."],
        ["Exclude identity", "g^q is a polynomial of degree 2^q, so it cannot equal the identity polynomial; the first nonzero term exists."],
    ], [2.05 * inch, 5.03 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "What is now closed",
        "The cancellation range w^2 through w^q is an all-q theorem. The machine certificate independently expands the iterate and checks commutation for q=2,...,32, while the proof itself does not depend on that finite range.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "What remains separate",
        "This lemma does not prove that the degree-(q+1) coefficient is nonzero for every q. The exact finite sweep proves nonzero coefficients only for q=2,...,16. It also supplies no uniform cylinder/Lavaurs modulus, Ecalle-phase transport, satellite-to-neutral comparison, virtual-Molecule interpolation, or global parameter rigidity.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Research consequence",
        "The next local theorem is an all-q nondegeneracy result for the specific quadratic satellite roots. Even if that is proved, the global MLC target still requires the unbounded-satellite cylinder-to-parameter bridge and the l-unbounded virtual-renormalization theorem identified in A.21.",
        PALE_RED, colors.HexColor("#B42318"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Machine certificate: validate_parabolic_commutation_lemma.py; output: parabolic_commutation_lemma_20260725.json; all checks passed; original_artifacts_written=false. Proof note: parabolic_commutation_lemma_20260725.md. Source context for the standard degeneracy terminology: https://www.math.univ-toulouse.fr/~buff/Preprints/DegenerateParabolic/DegenerateParabolic.pdf. The global MLC target remains open.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.23 Trace-plumbing correction: the collar promotion fails", "H1x"))
    story.append(p("The latest trace-plumbing research push contains a valid local calculation and an invalid geometric promotion. The full Dirichlet-to-Neumann formula for a genuine Neumann-wall rectangle, its Hilbert-space Schur complement, and the finite Fourier audit are retained. The proposed identification of every dynamically pulled parent/child equipotential pair with one serial rectangle is rejected.", "Leadx"))
    story.append(table([
        ["Layer", "Audited status"],
        ["Local analytic calculus", "Proved for an actual width-one rectangle: mode-by-mode harmonic extension gives the exact response with A*coth(RA), -A*csch(RA), and constant mode 1/R. The 500-trial finite audit passes."],
        ["Response composition", "Proved only when the interfaces carry the same complete parameterized trace space; Schur-complement gluing is exact under that hypothesis."],
        ["Scalar collapse", "Valid only for an explicitly shorted constant trace space. A nonconstant cosine trace has positive energy while its mean-only scalar model gives zero."],
        ["Dynamical collar promotion", "Not proved and in fact false in the proposed form: a pullback under z -> z^(2^q) changes angular width Delta to Delta/(2^q)."],
        ["Correct open node", "DIRECT_DECORATION_TRACE_COLLAR_REALIZATION: retain unequal trace footprints, side ports, actual cell response, phase, and accumulated resistance in the physical nested end."],
    ], [1.75 * inch, 5.33 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Exact no-go",
        "If a full parent arc and a full pulled child arc were opposite equipotential sides of one rectangle bounded by the same two rays, their angular widths would have to agree. For every q >= 1 and every positive Delta, Delta/(2^q) is strictly smaller than Delta. The obstruction is exact, not numerical.",
        PALE_RED, colors.HexColor("#B42318"),
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Repair to the proof program",
        "Do not promote the local trace theorem to END_PLUMBING_TRACE_RESPONSE_CONTROL for arbitrary nested ends. First construct a direct-decoration collar with the actual unmatched boundary pieces and a future-closed multi-port trace response, or prove a different physical interface theorem. Positive resistance of individual cells is also insufficient for a finite strict margin unless total resistance crosses the explicit threshold.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Global consequence",
        "This correction removes a tempting but invalid shortcut; it does not close MLC. H2 response realization, MBTT, coercivity, rigidity, the unbounded-satellite bridge, and the global MLC target remain open.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Machine certificate: validate_trace_collar_no_go.py; output: trace_collar_no_go_20260725.json; exact checks q=1,...,32 and four positive widths; original_artifacts_written=false. Independent source audit: research_push_4_assessment_and_integration.md. The global MLC target remains open.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.24 Conditional trace-complete response theorem", "H1x"))
    story.append(p("The corrected collar target can be stated as a precise conditional theorem. It retains every actual boundary trace and treats unmatched parent/child footprints as ports, rather than identifying them with one scalar serial neck.", "Leadx"))
    story.append(table([
        ["Required certificate", "Role in the theorem"],
        ["Uniform interface type", "A universal bound on retained ports, with every future-relevant side component represented."],
        ["Uniform reference charts", "After normalization, cells come from finitely many Lipschitz reference domains with uniform trace extension/restriction bounds."],
        ["Uniform coercivity", "Normalized Dirichlet forms are bounded above and below on the quotient by componentwise constants."],
        ["Trace-compatible gluing", "Every matched and unmatched port has a phase-preserving restriction/extension map that is future-closed."],
        ["Response-safe elimination", "Eliminated traces have uniform coercivity and the chosen homogeneous response gauge is weak-operator lower semicontinuous."],
    ], [2.05 * inch, 5.03 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Conditional conclusion",
        "Under these five certificates, Lax-Milgram gives the full response form modulo componentwise constants; exact gluing is Hilbert-space infimal convolution/Schur complement; Loewner bounds pass through elimination; normalized responses have weak-operator convergent subsequences; and a strict response transition survives once actual accumulated resistance crosses its explicit threshold.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "What this repairs",
        "The theorem provides the correct analytic interface for a non-rectangular physical annular difference. It allows unequal angular footprints and side ports, and it identifies exactly which data must be retained for phase, protection, and future pullbacks.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "What is still unproved",
        "The five source-facing certificates are not established for every direct-decoration, virtual, or mixed tower. Therefore this conditional theorem does not close END_PLUMBING_TRACE_RESPONSE_CONTROL, MBTT, coercivity, rigidity, or MLC.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Proof note: direct_decoration_trace_response_conditional_20260725.md. Machine cross-checks: validate_trace_collar_no_go.py, the 500-trial full-trace audit, and audit_transfer_regressions.py. Original artifacts remain untouched.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.25 Formal recurrence for the first parabolic coefficient", "H1x"))
    story.append(p("The all-q commutation lemma proves cancellation through degree q. A separate exact recurrence isolates the first resonant coefficient for g(w)=lambda*w+w^2, and a critical-point count closes its all-q nondegeneracy.", "Leadx"))
    story.append(table([
        ["Object", "Exact formula"],
        ["Formal coordinate", "phi(z)=z+b_2 z^2+b_3 z^3+..."],
        ["Nonresonant coefficients", "b_n = S_n/(lambda^n-lambda), 2 <= n <= q, with S_n=sum_{i=1}^{n-1} b_i b_(n-i) and b_1=1."],
        ["Resonant coefficient", "A=S_(q+1)=sum_{i=1}^q b_i b_(q+1-i)."],
        ["q-th iterate", "[w^(q+1)] g^q = q*lambda^(q-1)*A."],
        ["Exact field", "All expressions are evaluated in Q[x]/(Phi_q(x)); the denominators are nonzero by primitivity."],
        ["All-q nondegeneracy", "For the degree-two polynomial, the root-of-unity basin count gives one parabolic basin cycle, so the multiplicity is exactly q+1."],
    ], [1.75 * inch, 5.33 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Finite certificate",
        "validate_parabolic_resonance_recurrence.py evaluates the recurrence and independently expands g^q in the exact cyclotomic field. For q=2,...,16 the predicted and direct coefficients agree, all intermediate coefficients vanish, and the resonant coefficient is nonzero.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "All-q local closure",
        "For a primitive q-th multiplier, the q-th iterate has multiplicity m+1 with m=kq, and its immediate parabolic basins form k cycles. Each cycle contains a critical point. The quadratic germ has one finite critical point; infinity belongs to the superattracting basin at infinity. Hence k=1, m=q, and the degree-(q+1) coefficient is nonzero for every q.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Global boundary",
        "Even an all-q nondegeneracy proof would only repair one local anchor. It would still leave the source-faithful arbitrary unbounded-satellite cylinder-to-parameter bridge, virtual-Molecule interpolation, and global rigidity obligations open; MLC is not promoted to complete.",
        PALE_RED, colors.HexColor("#B42318"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Machine certificate: validate_parabolic_resonance_recurrence.py; output: parabolic_resonance_recurrence_20260725.json; all checks passed; original_artifacts_written=false. Research note: parabolic_resonance_recurrence_20260725.md. Basin-count cross-checks: https://www.math.montana.edu/geyer/2016-fall-m597/materials/s2016-complex-dynamics-notes.pdf and https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/article/abs/on-the-number-of-critical-points-in-parabolic-basins/BB15221F8AB70937D675B98CFD9585F1.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.26 Exact global frontier after source re-audit", "H1x"))
    story.append(p("The global objective requires coverage of every renormalization family, not only the local parabolic anchor. The current KKL source gives an exact boundary for what its new theorem closes and what still requires a new bridge.", "Leadx"))
    story.append(table([
        ["Renormalization regime", "Source-locked status"],
        ["Anti-molecule / bounded satellite", "Completed by the established quadratic-like theory; MLC follows in the bounded-combinatorics regime."],
        ["Parabolically bounded prime primitive", "KKL Theorems A--C: beau bounds, bounded puzzle Teichmuller diameter, and rigidity for this stated family."],
        ["General near-parabolic primitive", "KKL identifies only a subcase; the theorem is not universal in unbounded h."],
        ["Near-neutral / unbounded satellite", "Neutral pseudo-Siegel and sectorial tools exist, but the source notes transitional external input and does not give the arbitrary satellite-to-parameter transfer."],
        ["Virtually-satellite", "The virtual near-Molecule renormalization/carrier and interpolation theorem remain unbuilt or in preparation."],
    ], [2.15 * inch, 4.93 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Narrowest valid virtual target",
        "Before invoking KKL's Section-4 trichotomy on a virtual block, construct an access-complete finite-tree carrier; bound every marked interval per limb; prove the successor-width/WAD comparison for the full retained cycle; prove restriction multiplicity and faithful flux/wave extraction; and state the large-width amplification threshold. Component occupancy alone is insufficient.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Required separation",
        "The static Section-4 interface does not prove the tame branch or the long-iterate wave branch. Those require separate full-return construction, Value/entropy control, fiber-product pullbacks, proper/end-proper interval dynamics, selected degree bounds, and itinerary-complete stopping certificates.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Global status",
        "This re-audit closes a source-attribution weakness and narrows the virtual proof target, but it does not prove the missing analytic carrier or parameter rigidity. Therefore the global MLC conjecture remains open in the active ledger.",
        PALE_RED, colors.HexColor("#B42318"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Source audit: https://arxiv.org/html/2606.27272, Sections 1.1--1.3; supporting taxonomy: https://arxiv.org/html/2512.24171. Local note: kkl_virtual_occupancy_source_audit.md. Original documents remain untouched.", "URLx"))
    story.append(PageBreak())
    story.append(rich("A.27 Corrected scale-two corridor certificate", "H1x"))
    story.append(p("A source re-audit corrected the first attempted virtual scale-two failure. The earlier note treated the terminal primitive domains as potentially outside the outer puzzle piece. The checked Kahn--Lyubich decoration and principal-nest sources instead give the nested chain A0 = W^r subset B = V^r subset V0 subset P, where V0 is the first kingdom and P is the outer decoration puzzle piece.", "Leadx"))
    story.append(table([
        ["Certificate field", "Validated native statement"],
        ["Outer chart", "P = Y^(n-1)q+1 has actual univalent pullbacks Q_L,Q_R inside P under g = f^q."],
        ["Terminal domains", "The primitive return has A0 subset B subset V0 subset P; both A0 and B lie in the domain of every finite outer inverse branch."],
        ["Conjugated return", "phi_w o f^p_term o phi_w^(-1): phi_w(A0) -> phi_w(B) is a well-typed proper degree-two map."],
        ["Actual iterate", "f^(p_term+qm) on phi_w(A0) maps to the common native base B; it is not automatically a virtual self-return."],
        ["Marking", "The native Hubbard-tree ideal side transports through the univalent chart, but complete virtual access/Wave data are not yet selected."],
    ], [1.65 * inch, 5.43 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Correction",
        "The domain-typing objection is closed for the source-defined native corridor. The remaining obstruction is the virtual state-space and return-base choice: the finite cylinder does not by itself identify a first-return of the original polynomial at the virtual scale.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Exact residual",
        "To promote the bridge, construct the scale-two state space, prove component and access selection, choose the actual iterate versus conjugated transition, and verify critical chronology, protected prime ends, obstacle ownership, and full Wave-demand naturality. Until then VIRTUAL_DISCONNECTED_MARKING_TRANSFER, VIRTUAL_CANTOR_PACKAGE_REALIZATION, VIRTUAL_RETURN_BASE_ATLAS, protected routing, UPTCR, and MLC remain open.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Machine check",
        "validate_virtual_s2_corrected_corridor.py passed all source-anchor, nesting, symbolic conjugacy, degree, and boundary checks. Output: virtual_s2_corrected_corridor_20260726.json; original_artifacts_written=false.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Research note: virtual_s2_corrected_corridor_certificate_20260726.md. Public status cross-check: KKL Theorem A--C is scoped to parabolically bounded prime primitive families, while Dudko's Problem 4.4 asks for the virtual near-Molecule interpolation. Sources: https://arxiv.org/html/2606.27272 and https://arxiv.org/html/2512.24171. The global MLC target remains open; original documents remain untouched.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.28 Finite virtual quadratic-like lift", "H1x"))
    story.append(p("The corrected corridor square yields a stronger finite theorem. For every finite direct-decoration word w, the pulled continuum K_w = phi_w(K_0) is the filled Julia set of a genuine degree-two quadratic-like map, even though that map is a conjugated return rather than an iterate of the original polynomial.", "Leadx"))
    story.append(table([
        ["Field", "Finite theorem"],
        ["Domains", "A_w = phi_w(A_0) is compactly contained in B_w = phi_w(B)."],
        ["Map", "F_w = phi_w o F_term o phi_w^(-1): A_w -> B_w is proper of degree two."],
        ["Filled Julia set", "K(F_w) = phi_w(K_0) = K_w by the exact iterate-conjugacy identity."],
        ["Dynamics", "f^(q|w|) maps K_w to K_0; this supplies parent/shift data but does not turn F_w into an iterate."],
        ["Marking", "Finite terminal degree, chronology, ideal side, and finite prime-end data transport through phi_w."],
    ], [1.55 * inch, 5.53 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Finite realization closed",
        "This repairs the earlier finite construction: K_w is not merely a nested continuum or symbolic label. It has an actual open quadratic-like return with a connected filled Julia set and transported terminal data.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Infinite-end boundary",
        "For an infinite address omega, the maps F_(omega|m) have changing domains and charts. The checked sources still provide no nondegenerate normalized limit, uniform modulus bound, limiting return base, complete protected marking, or parameter-rigidity transfer. Thus the virtual Cantor/end and global MLC gates remain open.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Machine check",
        "validate_virtual_s2_finite_quadratic_like_lift.py passed source-anchor, degree, iterate-conjugacy, filled-Julia survival, and scope-boundary checks. Output: virtual_s2_finite_quadratic_like_lift_20260726.json; original_artifacts_written=false.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Research note: virtual_s2_finite_quadratic_like_lift_20260726.md. This closes a finite analytic module only; the global MLC target remains open and original documents remain untouched.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.29 Fixed-modulus infinite-end no-go", "H1x"))
    story.append(p("The finite quadratic-like lift does not by itself force the infinite-address fibers to shrink. An interface-level holomorphic countermodel shows why a fixed terminal modulus is insufficient: a normalized Riemann map from the disk onto a symmetric ellipse tangent at two boundary points preserves a nondegenerate real segment under all iterates.", "Leadx"))
    story.append(table([
        ["Claim tested", "Result"],
        ["Finite lift", "Every finite conjugated return remains degree two and has the same quadratic-like modulus."],
        ["Ambient conclusion", "Not valid: nested univalent images can retain a nondegenerate boundary continuum."],
        ["Countermodel", "For a symmetric ellipse E_r inside the unit disk, a normalized map phi:D -> E_r preserves [-1,1], and the intersection of phi^m(closed D) contains [-1,1]."],
        ["Required repair", "Construct pairwise serial separating annuli or an equivalent divergent-width/protected-collar theorem for every actual infinite address."],
        ["Scope", "This refutes an inference from the current interface; it is not a counterexample to MLC and is not claimed to arise from a quadratic polynomial."],
    ], [1.55 * inch, 5.53 * inch], PALE_AMBER))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Exact boundary",
        "The fixed annulus B_w minus A_w is not automatically a serial separator: the next child cylinder lies in a different side component of Q_w minus B_w. Therefore modulus invariance cannot replace the missing corridor/trace geometry.",
        PALE_RED, colors.HexColor("#B42318"),
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Machine check",
        "validate_finite_modulus_infinite_end_no_go.py passed the ellipse containment, symmetry, preserved-segment, modulus-invariance, and scope-boundary checks. Output: finite_modulus_infinite_end_no_go_20260726.json; original_artifacts_written=false.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Research note: finite_modulus_infinite_end_no_go_20260726.md. The active global target remains MLC; original documents remain untouched.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.30 Unbounded-satellite modulus source re-audit", "H1x"))
    story.append(p("A locked primary-source audit now fixes the exact obstruction in the unbounded-satellite branch. Blokh--Levin--Oversteegen--Timorin prove that native root-annulus moduli can collapse as satellite relative periods grow. This is a correction to the proof target, not a proof or counterexample to MLC.", "Leadx"))
    story.append(table([
        ["Source statement", "Source-faithful consequence"],
        ["Rational degree d: mod(A) < 2^(2d-2)*pi/log(4*(s+1)).", "For degree two the looser rational bound is 4*pi/log(4*(s+1))."],
        ["Polynomial degree d: mod(A) < 2^(d-1)*pi/log(4*(s+1)).", "For a quadratic polynomial the exact bound is 2*pi/log(4*(s+1)), tending to zero as s tends to infinity."],
        ["Theorem B: nondegenerate Hausdorff limit, q_n -> infinity, and no parabolic periodic domain containing the limit.", "The corresponding fundamental moduli tend to zero."],
        ["Proposition ex:Ex: a real quadratic Lavaurs sequence with a parabolic 3-cycle.", "Nondegenerate limits and q_n -> infinity can coexist with annulus moduli bounded below; the no-parabolic hypothesis is essential."],
    ], [2.65 * inch, 4.43 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Exact correction",
        "The quadratic-polynomial constant is 2*pi, not 4*pi. The 4*pi expression is the valid but weaker rational-function bound. The validator checks both source formulas and the elementary epsilon threshold s > exp(2*pi/epsilon)/4 - 1.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "What this repairs",
        "It closes the unsupported assumption that unbounded satellite denominators retain a uniform native quadratic-like modulus lower bound. The active target must instead use serial separating geometry, a near-parabolic/Ecalle cylinder response, or an actual virtual carrier with a proved divergent-width/collar theorem.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "What remains open",
        "Modulus collapse is not local connectivity. The source does not provide the critical chronology, protected accesses, parameter-marking transfer, finite-horizon summability, or global coverage needed to close MLC. The parabolic/near-parabolic branch remains the live analytic bridge.",
        PALE_RED, colors.HexColor("#B42318"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Locked source: https://arxiv.org/abs/2205.03157; extracted source SHA-256 ED8F55AE8DE9667488AD91B4175AB40BFD2E3B7179D8141397F4A17B5B80DF6; source lines 290--300, 355--377, 870--887. Local note: unbounded_satellite_modulus_source_reaudit_20260726.md.", "URLx"))
    story.append(PageBreak())
    story.append(rich("A.31 Two-case serial-separation target", "H1x"))
    story.append(p("The source re-audit determines the minimum replacement theorem for the global proof. Individual native moduli may become arbitrarily small, so the desired conclusion must be phrased in terms of controlled accumulated separation rather than a single-scale lower bound.", "Leadx"))
    story.append(table([
        ["Case", "Required actual certificate", "Current status"],
        ["N: parabolic or near-parabolic limit", "Actual domains and return iterates; Ecalle/cylinder response; critical chronology; protected accesses; parameter marking; finite-horizon summability.", "Not proved; this is the active transitional bridge."],
        ["P: non-parabolic limit", "Protected actual collars or crosscuts with divergent accumulated separation, compatible with the marked virtual/direct construction even when each native modulus tends to zero.", "Not supplied by Theorem B; requires a new serial-width theorem."],
        ["Global endgame", "Singleton dynamical fibers plus connected parameter neighborhoods shrinking to the parameter across every mixed tower.", "MLC remains open in the ledger."],
    ], [1.35 * inch, 3.95 * inch, 1.78 * inch], PALE_BLUE))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Logical boundary",
        "Theorem B is a case detector for native modulus collapse, not the protected-collar theorem. The Lavaurs construction prevents silently treating the parabolic exception as covered. A real closure must prove the N/P transfer and then connect it to parameter rigidity.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Machine check",
        "validate_unbounded_satellite_modulus_source_reaudit.py passed source hashes, theorem anchors, exact degree-two constants, monotone decay, epsilon thresholds, the Theorem B hypothesis anchor, and the Lavaurs boundary anchor. Output: unbounded_satellite_modulus_source_reaudit_20260726.json; original_artifacts_written=false.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("This appendix records a repaired proof target, not a completed MLC proof. Original manuscript and original PDFs remain untouched.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.32 Serial-annulus singleton bridge", "H1x"))
    story.append(p("A standard extremal-length theorem closes the analytic implication that the finite-lift interface was missing: if actual nested, pairwise-disjoint annuli surround one end fiber and their moduli have divergent sum, the end fiber is a point. This is a proved bridge, not yet a dynamical realization.", "Leadx"))
    story.append(table([
        ["Hypothesis", "Required meaning"],
        ["Serial placement", "The annuli are pairwise disjoint and nested around the same end fiber; no side-component bypass is allowed."],
        ["Common localization", "All inner components lie in one bounded region with one fixed outer cross-section."],
        ["Divergent resistance", "The sum of the conformal moduli of the annuli is infinite."],
        ["Conclusion", "Grötzsch inequality forces the nested inner intersection to be a singleton."],
    ], [1.65 * inch, 5.43 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Exact theorem",
        "Lyubich, Proposition 6.16: for a nest of disjoint annuli, divergent total modulus implies that the intersection of the corresponding inner components is a singleton. The proof combines Grötzsch superadditivity with finiteness of the modulus when both complementary components are non-singletons.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Machine model",
        "For round annuli with m_n=1/(n+1), r_n=exp(-2*pi*sum_{j<=n}m_j), the checked modulus is exactly m_n and r_n tends to zero. With m_n=2^(-(n+1)), the sum is finite and the limiting radius is exp(-2*pi)>0. The validator checks both cases.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Dynamical boundary",
        "The Kahn--Lyubich direct-decoration source supplies univalent pullbacks and finite separating pieces attached to boundary rays, but not the annulus, serial placement, common outer cross-section, no-bypass condition, and divergent modulus sum for every infinite address. Therefore the direct/virtual realization and global MLC gates remain open.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Machine check: validate_serial_annulus_singleton_bridge.py passed; output serial_annulus_singleton_bridge_20260725.json; original_artifacts_written=false. Source: https://www.math.stonybrook.edu/~mlyubich/book.pdf. This theorem does not close MLC by itself.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.33 Weak welding-graph compactification", "H1x"))
    story.append(p("The fixed-coordinate norm-precompactness requirement is too strong for uncontrolled word-dependent weldings. A valid alternative is to retain the full welding and response as a weak-operator compact state, provided common trace spaces and uniform bounds are actually proved.", "Leadx"))
    story.append(table([
        ["State field", "Compact-state treatment"],
        ["Entrance/exit welding", "Bounded operators on one separable trace Hilbert space; retain weak-operator limits."],
        ["Full response", "Positive operators 0 <= Q_n <= C_Q I; Loewner bounds pass to weak limits."],
        ["Welding relation", "Graph projections converge to a positive contraction; the limit may be a relaxed relation, not an invertible map."],
        ["Observables", "Bounded Value/phase observables are included in the diagonal subsequence state."],
    ], [1.65 * inch, 5.43 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Proved abstract repair",
        "On a separable Hilbert space, uniformly bounded operator families have a weak-operator convergent subsequence by diagonal extraction on a countable dense set. Positive response caps and closed Loewner inequalities survive. Graph projections record the welding without silently restoring invertibility.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Why this matters",
        "The finite permutation example remains uniformly separated in operator norm, so norm compactness is genuinely unavailable. Weak retention avoids that false requirement while keeping the complete response and welding as state data.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Still required for MLC",
        "The dynamics must still provide one common trace space, uniform welding/response bounds, lower coercivity, protected-marking and Value compatibility, no-bypass control, and a strict transition stable under a possibly relaxed welding relation. The global MLC gates remain open.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Machine check: validate_weak_welding_graph_compactification.py passed; output weak_welding_graph_compactification_20260725.json; original_artifacts_written=false. This is an abstract compact-state alternative, not a completed direct-decoration realization or MLC proof.", "URLx"))

    story.append(PageBreak())
    story.append(rich("A.34 Dyadic Böttcher external-trace isometry", "H1x"))
    story.append(p("The checked decoration source supplies dyadic external-angle inverse lifts, but only sectorwise. After normalization to unit angular intervals, the homogeneous H^(1/2) trace seminorm is exactly invariant under each affine lift. This gives a uniform external-sector component of the welding state.", "Leadx"))
    story.append(table([
        ["Input", "Validated consequence"],
        ["Dyadic inverse lift", "T(theta)=(theta+k)/2^q on one declared sector; the sector integer k is retained."],
        ["Intrinsic trace norm", "The Jacobian factor s^2 cancels the denominator factor s^2 in the homogeneous H^(1/2) seminorm."],
        ["Uniformity", "The normalized lift has exact norm one, independent of q, depth, and physical angular footprint."],
        ["Scope", "External sector only; no global common k, physical/core welding, or protected multisector identification is inferred."],
    ], [1.65 * inch, 5.43 * inch], PALE_TEAL))
    story.append(Spacer(1, 0.14 * inch))
    story.append(callout(
        "Closed external component",
        "For one declared Böttcher sector and one compatible dyadic inverse lift, the normalized intrinsic trace transport is an exact isometry. This removes period-dependent distortion from that external coordinate layer.",
        PALE_TEAL, TEAL,
    ))
    story.append(Spacer(1, 0.12 * inch))
    story.append(callout(
        "Residual physical gate",
        "The source has multiple sectors and permits sector-dependent inverse integers. The missing theorem is the bounded physical Böttcher-to-core welding, with endpoint protection, all-depth contact closure, coercivity, and Value compatibility. The weak welding compact state is the proposed interface if norm compactness fails.",
        PALE_AMBER, colors.HexColor("#C98A00"),
    ))
    story.append(Spacer(1, 0.1 * inch))
    story.append(p("Machine check: validate_dyadic_bottcher_external_trace_isometry.py passed source anchors, exact scale cancellation, period independence, and sectorwise scope checks; output dyadic_bottcher_external_trace_isometry_20260725.json; original_artifacts_written=false.", "URLx"))

    doc.build(story)


def merge():
    OUT.parent.mkdir(parents=True, exist_ok=True)
    reader = PdfReader(str(BASE))
    appendix = PdfReader(str(APPENDIX))
    writer = PdfWriter()
    for page in reader.pages:
        writer.add_page(page)
    for page in appendix.pages:
        writer.add_page(page)
    writer.add_metadata({
        "/Title": "MLC Conjecture Sub-Research Proposal with Actual Closure Attempt",
        "/Author": "Codex - separate research artifact",
        "/Subject": "A source-faithful active attempt toward the Mandelbrot local connectivity conjecture",
    })
    with OUT.open("wb") as stream:
        writer.write(stream)


if __name__ == "__main__":
    build_appendix()
    merge()
    print(OUT)
