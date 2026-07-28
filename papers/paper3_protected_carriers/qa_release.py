"""Zero-tolerance static and PDF-integrity checks for Paper 3 Draft II."""

from __future__ import annotations

import hashlib
import math
import re
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path
from urllib.parse import urlparse

from pypdf import PdfReader
from pypdf.generic import (
    ArrayObject,
    DictionaryObject,
    IndirectObject,
    NameObject,
)


ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "main_v2.tex"
SKELETON = ROOT / "skeleton_v2.tex"
PDF = ROOT / "paper3_draft2.pdf"
BUILD_PDF = ROOT / "build_v2" / "main_v2.pdf"
LOG = ROOT / "build_v2" / "main_v2.log"
ASSEMBLER = ROOT / "assemble.py"

EXPECTED_METADATA = {
    "/Title": (
        "Protected planar carriers: separation ledgers and "
        "access-preserving routing"
    ),
    "/Author": "Matthew Robert Wesney",
    "/Subject": "Planar continuum theory and access-preserving routing",
    "/Keywords": (
        "plane continuum, prime end, Alexander duality, protected access, "
        "connector, filled hull, Hausdorff limit"
    ),
}
BOX_TOLERANCE = 1e-6

FAILURES: list[str] = []
WARNINGS: list[str] = []
METRICS: dict[str, object] = {}


def fail(message: str) -> None:
    FAILURES.append(message)


def warn(message: str) -> None:
    WARNINGS.append(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def indirect_key(value: object) -> tuple[int, int] | None:
    if isinstance(value, IndirectObject):
        return value.idnum, value.generation
    reference = getattr(value, "indirect_reference", None)
    if isinstance(reference, IndirectObject):
        return reference.idnum, reference.generation
    return None


def resolve(value: object) -> object:
    """Resolve a pypdf indirect object while leaving direct objects unchanged."""
    if isinstance(value, IndirectObject):
        return value.get_object()
    return value


def finite_rectangle(value: object) -> tuple[float, float, float, float] | None:
    """Return a normalized, finite four-number rectangle or None."""
    try:
        values = tuple(float(item) for item in value)  # type: ignore[arg-type]
    except (TypeError, ValueError, OverflowError):
        return None
    if len(values) != 4 or not all(math.isfinite(item) for item in values):
        return None
    left, bottom, right, top = values
    if right + BOX_TOLERANCE < left or top + BOX_TOLERANCE < bottom:
        return None
    return left, bottom, right, top


def rectangle_contains(
    outer: tuple[float, float, float, float],
    inner: tuple[float, float, float, float],
) -> bool:
    return (
        inner[0] >= outer[0] - BOX_TOLERANCE
        and inner[1] >= outer[1] - BOX_TOLERANCE
        and inner[2] <= outer[2] + BOX_TOLERANCE
        and inner[3] <= outer[3] + BOX_TOLERANCE
    )


def fresh_assembly_bytes() -> bytes | None:
    """Assemble into a temporary file and return its bytes."""
    if not ASSEMBLER.exists():
        fail(f"missing release assembler: {ASSEMBLER}")
        return None
    with tempfile.TemporaryDirectory(prefix="paper3_release_qa_") as temp_dir:
        output = Path(temp_dir) / "main_v2_fresh.tex"
        result = subprocess.run(
            [
                sys.executable,
                str(ASSEMBLER),
                "--skeleton",
                SKELETON.name,
                "--output",
                str(output),
            ],
            cwd=ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
        METRICS["fresh_assembly_exit_code"] = result.returncode
        if result.returncode != 0:
            diagnostic = (result.stdout + "\n" + result.stderr).strip()
            fail(f"fresh source assembly failed: {diagnostic}")
            return None
        if not output.exists():
            fail("fresh source assembly reported success but produced no output")
            return None
        return output.read_bytes()


def embedded_font_status(font_reference: object) -> tuple[bool, int, str]:
    """Return (fully embedded, embedded-stream count, diagnostic)."""

    def descriptor_streams(descriptor_reference: object) -> tuple[bool, int, str]:
        descriptor = resolve(descriptor_reference)
        if not isinstance(descriptor, DictionaryObject):
            return False, 0, "missing FontDescriptor"
        streams = 0
        for key in ("/FontFile", "/FontFile2", "/FontFile3"):
            stream_reference = descriptor.get(key)
            if stream_reference is None:
                continue
            stream = resolve(stream_reference)
            try:
                data = stream.get_data()  # type: ignore[attr-defined]
            except Exception as exc:  # pypdf must be able to decode the program
                return False, streams, f"{key} is unreadable: {exc}"
            if not data:
                return False, streams, f"{key} is empty"
            streams += 1
        if streams == 0:
            return False, 0, "FontDescriptor has no embedded font program"
        return True, streams, ""

    font = resolve(font_reference)
    if not isinstance(font, DictionaryObject):
        return False, 0, "font resource is not a dictionary"
    subtype = str(font.get("/Subtype", ""))
    if subtype == "/Type3":
        char_procs = resolve(font.get("/CharProcs"))
        if not isinstance(char_procs, DictionaryObject) or not char_procs:
            return False, 0, "Type3 font has no CharProcs"
        for name, char_proc_reference in char_procs.items():
            char_proc = resolve(char_proc_reference)
            try:
                if not char_proc.get_data():  # type: ignore[attr-defined]
                    return False, 0, f"Type3 glyph {name} is empty"
            except Exception as exc:
                return False, 0, f"Type3 glyph {name} is unreadable: {exc}"
        return True, len(char_procs), ""
    if subtype == "/Type0":
        descendants = resolve(font.get("/DescendantFonts"))
        if not isinstance(descendants, ArrayObject) or not descendants:
            return False, 0, "Type0 font has no descendant font"
        stream_count = 0
        for descendant_reference in descendants:
            descendant = resolve(descendant_reference)
            if not isinstance(descendant, DictionaryObject):
                return False, stream_count, "invalid Type0 descendant font"
            okay, streams, diagnostic = descriptor_streams(
                descendant.get("/FontDescriptor")
            )
            stream_count += streams
            if not okay:
                return False, stream_count, diagnostic
        return True, stream_count, ""
    return descriptor_streams(font.get("/FontDescriptor"))


def scan_source() -> None:
    for path in (SOURCE, SKELETON, ASSEMBLER, PDF, BUILD_PDF, LOG):
        if not path.exists():
            fail(f"missing required release file: {path}")
    if FAILURES:
        return

    source_bytes = SOURCE.read_bytes()
    source = SOURCE.read_text(encoding="utf-8")
    skeleton = SKELETON.read_text(encoding="utf-8")
    log = LOG.read_text(encoding="utf-8", errors="replace")

    METRICS["source_chars"] = len(source)
    METRICS["source_lines"] = source.count("\n") + 1
    METRICS["assembled_source_sha256"] = hashlib.sha256(source_bytes).hexdigest()

    assembled_bytes = fresh_assembly_bytes()
    if assembled_bytes is not None:
        METRICS["fresh_assembly_sha256"] = hashlib.sha256(assembled_bytes).hexdigest()
        if assembled_bytes != source_bytes:
            fail(
                "assembled source is stale: main_v2.tex differs byte-for-byte "
                "from a fresh skeleton/fragment assembly"
            )

    if "%%INSERT" in source or "[MISSING INSERT" in source:
        fail("assembled source still contains an insertion marker")

    labels = re.findall(r"\\label\{([^{}]+)\}", source)
    label_counts = Counter(labels)
    duplicates = sorted(label for label, count in label_counts.items() if count > 1)
    if duplicates:
        fail(f"duplicate labels: {duplicates}")

    refs: set[str] = set()
    for command in ("ref", "eqref", "pageref", "autoref", "cref", "Cref"):
        refs.update(re.findall(rf"\\{command}\{{([^{{}}]+)\}}", source))
    unresolved_refs = sorted(refs - set(labels))
    if unresolved_refs:
        fail(f"unresolved source references: {unresolved_refs}")

    cites: set[str] = set()
    for group in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^{}]+)\}", source):
        cites.update(key.strip() for key in group.split(",") if key.strip())
    bibitems = re.findall(r"\\bibitem\{([^{}]+)\}", source)
    bib_counts = Counter(bibitems)
    duplicate_bib = sorted(key for key, count in bib_counts.items() if count > 1)
    if duplicate_bib:
        fail(f"duplicate bibliography keys: {duplicate_bib}")
    missing_bib = sorted(cites - set(bibitems))
    if missing_bib:
        fail(f"citation keys without bibliography entries: {missing_bib}")
    unused_bib = sorted(set(bibitems) - cites)
    if unused_bib:
        warn(f"uncited bibliography entries: {unused_bib}")

    METRICS["labels"] = len(labels)
    METRICS["references"] = len(refs)
    METRICS["citations"] = len(cites)
    METRICS["bibliography_entries"] = len(bibitems)

    theorem_envs = (
        "theorem",
        "proposition",
        "lemma",
        "corollary",
        "definition",
        "example",
        "warning",
        "openproblem",
    )
    theorem_count = 0
    for env in theorem_envs:
        pattern = re.compile(rf"\\begin\{{{env}\}}")
        for match in pattern.finditer(source):
            theorem_count += 1
            head = source[match.end() : match.end() + 500]
            if "\\label{" not in head:
                line = source.count("\n", 0, match.start()) + 1
                warn(f"{env} beginning at line {line} has no nearby label")
    METRICS["numbered_statement_environments"] = theorem_count

    begin_counts = Counter(re.findall(r"\\begin\{([A-Za-z*]+)\}", source))
    end_counts = Counter(re.findall(r"\\end\{([A-Za-z*]+)\}", source))
    if begin_counts != end_counts:
        fail(f"environment begin/end count mismatch: {begin_counts - end_counts}; "
             f"extra ends: {end_counts - begin_counts}")

    dangerous_markers = (
        "??",
        "PLACEHOLDER",
        "FIXME",
        "TODO",
        "[MISSING",
        "Lorem ipsum",
        "turn0",
        "turn1",
        "cite",
    )
    for marker in dangerous_markers:
        if marker in source:
            fail(f"source contains forbidden marker {marker!r}")

    forbidden_unicode = {
        "\u2010": "Unicode hyphen",
        "\u2011": "nonbreaking hyphen",
        "\u2012": "figure dash",
        "\u2013": "en dash",
        "\u2014": "em dash",
        "\u2212": "Unicode minus",
        "\u00a0": "nonbreaking space",
        "\ufeff": "byte-order mark",
    }
    for character, name in forbidden_unicode.items():
        if character in source:
            locations = [
                index + 1
                for index, line in enumerate(source.splitlines())
                if character in line
            ]
            fail(f"source contains {name} at lines {locations[:20]}")

    if re.search(r"(?<!\\)[ \t]+$", source, re.MULTILINE):
        warn("assembled source contains trailing whitespace")

    uncommented_source = "\n".join(
        re.sub(r"(?<!\\)%.*", "", line) for line in source.splitlines()
    )
    duplicate_words: list[str] = []
    for match in re.finditer(
        r"\b([A-Za-z][A-Za-z'-]{1,})\b[ \t\r\n]+\1\b",
        uncommented_source,
        flags=re.IGNORECASE,
    ):
        line = uncommented_source.count("\n", 0, match.start()) + 1
        duplicate_words.append(f"line {line}: {match.group(1)!r}")
    METRICS["duplicate_word_occurrences"] = len(duplicate_words)
    if duplicate_words:
        fail("consecutive duplicate words in assembled source: " + "; ".join(duplicate_words))

    log_errors = (
        r"undefined references?",
        r"undefined citations?",
        r"Emergency stop",
        r"Fatal error",
        r"Overfull \\[hv]box",
        r"Missing character",
        r"multiply defined",
    )
    for pattern in log_errors:
        matches = re.findall(pattern, log, flags=re.IGNORECASE)
        if matches:
            fail(f"build log matches {pattern!r}: {len(matches)} occurrence(s)")
    underfull = len(re.findall(r"Underfull \\hbox", log))
    METRICS["underfull_hbox_warnings"] = underfull
    if underfull:
        fail(f"build log contains {underfull} underfull hbox warnings")

    if "No statement labeled" in skeleton and "open or conditional" in skeleton:
        METRICS["scope_discipline_statement_present"] = True


def scan_pdf() -> None:
    """Perform strict, release-blocking structural checks on the PDF."""
    if not PDF.exists() or not BUILD_PDF.exists():
        return

    pdf_bytes = PDF.read_bytes()
    METRICS["pdf_bytes"] = len(pdf_bytes)
    if not re.match(br"%PDF-1\.[0-9]", pdf_bytes[:8]):
        fail("release file has no valid PDF header")
    if not pdf_bytes.rstrip().endswith(b"%%EOF"):
        fail("release PDF does not end with an EOF marker")
    eof_markers = pdf_bytes.count(b"%%EOF")
    startxref_markers = pdf_bytes.count(b"startxref")
    METRICS["pdf_eof_markers"] = eof_markers
    METRICS["pdf_startxref_markers"] = startxref_markers
    if eof_markers != 1 or startxref_markers != 1:
        fail(
            "release PDF is not a single clean revision "
            f"(EOF markers={eof_markers}, startxref markers={startxref_markers})"
        )

    release_hash = sha256(PDF)
    build_hash = sha256(BUILD_PDF)
    METRICS["release_sha256"] = release_hash
    METRICS["build_sha256"] = build_hash
    if release_hash != build_hash:
        fail("stable release PDF differs byte-for-byte from build_v2/main_v2.pdf")

    try:
        reader = PdfReader(str(PDF), strict=True)
    except Exception as exc:
        fail(f"strict PDF parse failed: {exc}")
        return
    METRICS["pdf_pages"] = len(reader.pages)
    METRICS["pdf_encrypted"] = reader.is_encrypted
    if reader.is_encrypted:
        fail("release PDF is unexpectedly encrypted")
        return
    if len(reader.pages) == 0:
        fail("release PDF has no pages")
        return

    metadata = reader.metadata
    METRICS["pdf_metadata"] = {
        key: str(value) for key, value in (metadata or {}).items()
    }
    if metadata is None:
        fail("release PDF has no document-information metadata")
    else:
        for key, expected in EXPECTED_METADATA.items():
            actual = metadata.get(key)
            if str(actual or "").strip() != expected:
                fail(
                    f"PDF metadata {key} is missing or incorrect: "
                    f"{actual!r} != {expected!r}"
                )
        for key in ("/Creator", "/Producer", "/CreationDate"):
            if not str(metadata.get(key) or "").strip():
                fail(f"PDF metadata {key} is missing or empty")
        creation_date = str(metadata.get("/CreationDate") or "")
        if creation_date and not re.fullmatch(
            r"D:\d{14}(?:Z|[+-]\d{2}'\d{2}')?", creation_date
        ):
            fail(f"PDF CreationDate has invalid syntax: {creation_date!r}")

    page_ref_to_number: dict[tuple[int, int], int] = {}
    box_signatures: dict[str, set[tuple[float, float, float, float]]] = {
        name: set()
        for name in ("MediaBox", "CropBox", "BleedBox", "TrimBox", "ArtBox")
    }
    rotations: set[int] = set()
    empty_text_pages: list[int] = []
    empty_content_pages: list[int] = []
    annotations = 0
    annotation_refs: dict[tuple[int, int], int] = {}
    broken_links: list[str] = []
    extracted_parts: list[str] = []
    fonts: dict[object, dict[str, object]] = {}
    seen_resource_dictionaries: set[object] = set()
    malformed_resources: list[str] = []

    def walk_resources(resources_reference: object, context: str) -> None:
        if resources_reference is None:
            malformed_resources.append(f"{context}: missing Resources dictionary")
            return
        resource_key: object = indirect_key(resources_reference)
        resources = resolve(resources_reference)
        if not isinstance(resources, DictionaryObject):
            malformed_resources.append(f"{context}: Resources is not a dictionary")
            return
        if resource_key is None:
            resource_key = id(resources)
        if resource_key in seen_resource_dictionaries:
            return
        seen_resource_dictionaries.add(resource_key)

        font_map = resolve(resources.get("/Font"))
        if font_map is not None and not isinstance(font_map, DictionaryObject):
            malformed_resources.append(f"{context}: Font resource is not a dictionary")
        elif isinstance(font_map, DictionaryObject):
            for resource_name, font_reference in font_map.items():
                font_key: object = indirect_key(font_reference)
                font = resolve(font_reference)
                if font_key is None:
                    font_key = id(font)
                if font_key not in fonts:
                    if not isinstance(font, DictionaryObject):
                        malformed_resources.append(
                            f"{context}: font {resource_name} is not a dictionary"
                        )
                        continue
                    embedded, stream_count, diagnostic = embedded_font_status(
                        font_reference
                    )
                    to_unicode_reference = font.get("/ToUnicode")
                    to_unicode_valid = False
                    if to_unicode_reference is not None:
                        try:
                            to_unicode_valid = bool(
                                resolve(to_unicode_reference).get_data()
                            )
                        except Exception as exc:
                            malformed_resources.append(
                                f"{context}: font {resource_name} has an "
                                f"unreadable ToUnicode map: {exc}"
                            )
                    fonts[font_key] = {
                        "resource_name": str(resource_name),
                        "base_font": str(font.get("/BaseFont", "")),
                        "subtype": str(font.get("/Subtype", "")),
                        "embedded": embedded,
                        "embedded_streams": stream_count,
                        "diagnostic": diagnostic,
                        "to_unicode": to_unicode_valid,
                        "context": context,
                    }

        for category in ("/XObject", "/Pattern"):
            child_map = resolve(resources.get(category))
            if child_map is None:
                continue
            if not isinstance(child_map, DictionaryObject):
                malformed_resources.append(
                    f"{context}: {category} resource is not a dictionary"
                )
                continue
            for child_name, child_reference in child_map.items():
                child = resolve(child_reference)
                if isinstance(child, DictionaryObject) and child.get("/Resources"):
                    walk_resources(
                        child.get("/Resources"),
                        f"{context} {category} {child_name}",
                    )

    named_destinations = reader.named_destinations

    def validate_destination(destination: object, context: str) -> None:
        if isinstance(destination, str):
            if destination not in named_destinations:
                broken_links.append(
                    f"{context}: unknown named destination {destination!r}"
                )
            return
        destination = resolve(destination)
        if isinstance(destination, ArrayObject) and destination:
            key = indirect_key(destination[0])
            if key is None:
                key = indirect_key(resolve(destination[0]))
            if key is None or key not in page_ref_to_number:
                broken_links.append(
                    f"{context}: destination page object is not in the page tree"
                )
            return
        if isinstance(destination, DictionaryObject):
            key = indirect_key(destination.get("/Page"))
            if key is None or key not in page_ref_to_number:
                broken_links.append(
                    f"{context}: destination dictionary has an invalid page"
                )
            return
        broken_links.append(f"{context}: malformed or empty destination")

    for page_number, page in enumerate(reader.pages, 1):
        key = indirect_key(page)
        if key is None:
            fail(f"page {page_number} has no indirect page-tree reference")
        elif key in page_ref_to_number:
            fail(
                f"page-tree object {key} is reused by pages "
                f"{page_ref_to_number[key]} and {page_number}"
            )
        else:
            page_ref_to_number[key] = page_number

        page_boxes = {
            "MediaBox": finite_rectangle(page.mediabox),
            "CropBox": finite_rectangle(page.cropbox),
            "BleedBox": finite_rectangle(page.bleedbox),
            "TrimBox": finite_rectangle(page.trimbox),
            "ArtBox": finite_rectangle(page.artbox),
        }
        for name, box in page_boxes.items():
            if box is None:
                fail(f"page {page_number} has an invalid {name}")
            else:
                box_signatures[name].add(box)
                if box[2] - box[0] <= 0 or box[3] - box[1] <= 0:
                    fail(f"page {page_number} has a zero-area {name}: {box}")
        media_box = page_boxes["MediaBox"]
        if media_box is not None:
            for name in ("CropBox", "BleedBox", "TrimBox", "ArtBox"):
                other_box = page_boxes[name]
                if other_box is not None and not rectangle_contains(
                    media_box, other_box
                ):
                    fail(
                        f"page {page_number} {name} lies outside MediaBox: "
                        f"{other_box} versus {media_box}"
                    )

        rotations.add(int(page.get("/Rotate", 0) or 0) % 360)
        if str(page.get("/Type", "")) != "/Page":
            fail(f"page {page_number} has invalid /Type {page.get('/Type')!r}")
        if page.get("/AA") is not None:
            fail(f"page {page_number} contains prohibited additional actions")
        walk_resources(page.get("/Resources"), f"page {page_number}")

        try:
            contents = page.get_contents()
            content_data = contents.get_data() if contents is not None else b""
        except Exception as exc:
            fail(f"page {page_number} content stream is unreadable: {exc}")
            content_data = b""
        if not content_data:
            empty_content_pages.append(page_number)

        try:
            text = page.extract_text() or ""
        except Exception as exc:
            fail(f"page {page_number} text extraction failed: {exc}")
            text = ""
        extracted_parts.append(text)
        if not text.strip():
            empty_text_pages.append(page_number)

    for page_number, page in enumerate(reader.pages, 1):
        for annotation_ref in page.get("/Annots", []):
            annotations += 1
            annotation_key = indirect_key(annotation_ref)
            if annotation_key is not None:
                old_page = annotation_refs.get(annotation_key)
                if old_page is not None:
                    fail(
                        f"annotation object {annotation_key} is shared by pages "
                        f"{old_page} and {page_number}"
                    )
                annotation_refs[annotation_key] = page_number
            annotation = resolve(annotation_ref)
            if not isinstance(annotation, DictionaryObject):
                fail(f"page {page_number} contains a malformed annotation")
                continue
            subtype = annotation.get("/Subtype")
            if subtype == NameObject("/Widget"):
                fail(f"page {page_number} contains a prohibited form widget")
            if annotation.get("/AA") is not None or annotation.get("/JS") is not None:
                fail(f"page {page_number} annotation contains JavaScript/actions")

            rectangle = finite_rectangle(annotation.get("/Rect"))
            if rectangle is None:
                fail(f"page {page_number} {subtype} annotation has an invalid rectangle")
            else:
                crop_box = finite_rectangle(page.cropbox)
                if crop_box is not None and not rectangle_contains(crop_box, rectangle):
                    fail(
                        f"page {page_number} annotation rectangle lies outside CropBox: "
                        f"{rectangle} versus {crop_box}"
                    )

            appearances = resolve(annotation.get("/AP"))
            if isinstance(appearances, DictionaryObject):
                for appearance_name, appearance_reference in appearances.items():
                    appearance = resolve(appearance_reference)
                    if (
                        isinstance(appearance, DictionaryObject)
                        and appearance.get("/Resources") is not None
                    ):
                        walk_resources(
                            appearance.get("/Resources"),
                            f"page {page_number} annotation {appearance_name}",
                        )

            destination: object | None = annotation.get("/Dest")
            action = annotation.get("/A")
            if destination is not None and action is not None:
                fail(f"page {page_number} annotation contains both /Dest and /A")
            if destination is not None:
                validate_destination(destination, f"page {page_number} annotation")
            if action is not None:
                action = resolve(action)
                if not isinstance(action, DictionaryObject):
                    fail(f"page {page_number} annotation has a malformed action")
                    continue
                if any(
                    action.get(key) is not None for key in ("/JS", "/Next", "/AA")
                ):
                    fail(
                        f"page {page_number} annotation contains a chained or "
                        "scripted action"
                    )
                action_type = action.get("/S")
                if action_type == NameObject("/GoTo"):
                    validate_destination(
                        action.get("/D"), f"page {page_number} GoTo action"
                    )
                elif action_type == NameObject("/URI"):
                    uri = str(action.get("/URI") or "").strip()
                    parsed = urlparse(uri)
                    if not uri or parsed.scheme.casefold() not in {
                        "http",
                        "https",
                        "mailto",
                    }:
                        fail(f"page {page_number} has an invalid URI action: {uri!r}")
                else:
                    fail(
                        f"page {page_number} contains prohibited action type "
                        f"{action_type!r}"
                    )

    METRICS["pdf_page_boxes"] = {
        name: sorted(signatures) for name, signatures in box_signatures.items()
    }
    METRICS["pdf_rotations"] = sorted(rotations)
    METRICS["pdf_annotations"] = annotations
    METRICS["pdf_named_destinations"] = len(named_destinations)
    if len(box_signatures["MediaBox"]) != 1:
        fail(
            "inconsistent PDF media boxes: "
            f"{sorted(box_signatures['MediaBox'])}"
        )
    if rotations - {0}:
        fail(f"unexpected page rotations: {sorted(rotations)}")
    if empty_content_pages:
        fail(f"pages with empty content streams: {empty_content_pages}")
    if empty_text_pages:
        fail(f"pages with no extractable text: {empty_text_pages}")
    if broken_links:
        fail("broken internal PDF links: " + "; ".join(broken_links))
    if malformed_resources:
        fail("malformed PDF resources: " + "; ".join(malformed_resources))

    font_records = list(fonts.values())
    METRICS["pdf_fonts"] = len(font_records)
    METRICS["pdf_embedded_font_programs"] = sum(
        int(record["embedded_streams"]) for record in font_records
    )
    METRICS["pdf_fonts_with_tounicode"] = sum(
        bool(record["to_unicode"]) for record in font_records
    )
    unembedded_fonts = [
        (
            record["base_font"],
            record["subtype"],
            record["context"],
            record["diagnostic"],
        )
        for record in font_records
        if not record["embedded"]
    ]
    if not font_records:
        fail("release PDF exposes no font resources")
    if unembedded_fonts:
        fail(f"fonts without embedded programs: {unembedded_fonts}")
    malformed_fonts = [
        record
        for record in font_records
        if not record["base_font"]
        or record["subtype"] not in {"/Type0", "/Type1", "/TrueType", "/Type3"}
    ]
    if malformed_fonts:
        fail(f"font resources with missing/unknown identity: {malformed_fonts}")
    composite_without_mapping = [
        record["base_font"]
        for record in font_records
        if record["subtype"] == "/Type0" and not record["to_unicode"]
    ]
    if composite_without_mapping:
        fail(
            "composite fonts without usable ToUnicode maps: "
            f"{composite_without_mapping}"
        )

    for name, destination in named_destinations.items():
        if not str(name).strip():
            fail("PDF contains an empty named-destination key")
        try:
            destination_page = reader.get_destination_page_number(destination)
        except Exception as exc:
            fail(f"named destination {name!r} cannot be resolved: {exc}")
            continue
        if destination_page is None or not 0 <= destination_page < len(reader.pages):
            fail(
                f"named destination {name!r} resolves outside the page tree: "
                f"{destination_page!r}"
            )

    outline_entries = 0

    def scan_outline(items: object) -> None:
        nonlocal outline_entries
        if not isinstance(items, list):
            fail("PDF outline hierarchy is malformed")
            return
        for item in items:
            if isinstance(item, list):
                scan_outline(item)
                continue
            outline_entries += 1
            if not isinstance(item, DictionaryObject):
                fail(f"PDF outline entry is malformed: {type(item).__name__}")
                continue
            title = str(item.get("/Title") or "").strip()
            if not title:
                fail("PDF outline contains an entry with an empty title")
            try:
                outline_page = reader.get_destination_page_number(item)
            except Exception as exc:
                fail(f"outline entry {title!r} cannot be resolved: {exc}")
                continue
            if outline_page is None or not 0 <= outline_page < len(reader.pages):
                fail(
                    f"outline entry {title!r} resolves outside the page tree: "
                    f"{outline_page!r}"
                )

    try:
        scan_outline(reader.outline)
    except Exception as exc:
        fail(f"PDF outline cannot be parsed: {exc}")
    METRICS["pdf_outline_entries"] = outline_entries
    if outline_entries == 0:
        fail("release PDF has no navigational outline")

    root = resolve(reader.trailer.get("/Root"))
    if not isinstance(root, DictionaryObject):
        fail("PDF trailer has no valid catalog")
    else:
        if root.get("/Type") != NameObject("/Catalog"):
            fail(f"PDF catalog has invalid /Type {root.get('/Type')!r}")
        for prohibited_key in ("/AcroForm", "/AA", "/JavaScript"):
            if root.get(prohibited_key) is not None:
                fail(f"PDF catalog contains prohibited {prohibited_key}")
        names = resolve(root.get("/Names"))
        if names is not None and not isinstance(names, DictionaryObject):
            fail("PDF catalog /Names entry is malformed")
        elif isinstance(names, DictionaryObject):
            for prohibited_key in (
                "/JavaScript",
                "/EmbeddedFiles",
                "/AlternatePresentations",
            ):
                if names.get(prohibited_key) is not None:
                    fail(f"PDF name tree contains prohibited {prohibited_key}")
        open_action = root.get("/OpenAction")
        if open_action is not None:
            open_action = resolve(open_action)
            if isinstance(open_action, DictionaryObject):
                fail("PDF catalog OpenAction is an executable action")
            else:
                validate_destination(open_action, "catalog OpenAction")

    extracted = "\n".join(extracted_parts)
    METRICS["pdf_extracted_text_chars"] = len(extracted)
    METRICS["pdf_replacement_characters"] = extracted.count("\ufffd")
    if "\ufffd" in extracted:
        fail("extracted PDF text contains Unicode replacement characters")
    for marker in ("??", "PLACEHOLDER", "FIXME", "TODO", "\ue200cite"):
        if marker in extracted:
            fail(f"extracted PDF text contains forbidden marker {marker!r}")

    expected_phrases = (
        "PROTECTED PLANAR CARRIERS",
        "Attachment exact sequence and separation ledger",
        "Protected Free-Component Criterion",
        "Nested-limit stability",
        "References",
    )
    for phrase in expected_phrases:
        if phrase.casefold() not in extracted.casefold():
            fail(f"expected PDF phrase not found: {phrase!r}")


def main() -> int:
    for label, scanner in (("source", scan_source), ("PDF", scan_pdf)):
        try:
            scanner()
        except Exception as exc:
            fail(f"unexpected {label} QA exception: {type(exc).__name__}: {exc}")

    print("Paper 3 Draft II release QA")
    print("===========================")
    for key in sorted(METRICS):
        print(f"{key}: {METRICS[key]}")
    if WARNINGS:
        print("\nWARNINGS")
        for message in WARNINGS:
            print(f"- {message}")
    if FAILURES:
        print("\nFAILURES")
        for message in FAILURES:
            print(f"- {message}")
    if FAILURES or WARNINGS:
        return 1
    print("\nPASS: zero warnings and no static-source or PDF-integrity failures")
    return 0


if __name__ == "__main__":
    sys.exit(main())
