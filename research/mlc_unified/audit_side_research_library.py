from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

from pypdf import PdfReader


ROOT = Path(__file__).resolve().parent
PDF_ROOT = ROOT / "output" / "pdf"
TMP_ROOT = ROOT / "tmp" / "pdfs" / "side_research_library_20260725"
MANIFEST = ROOT / "external_inputs" / "side_research_library_20260725" / "manifest.json"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest().upper()


def normalize(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def version_key(path: Path) -> tuple[int, str]:
    name = path.stem
    if name == "mlc_subresearch_corrections_proposal_20260724":
        return (-1, name)
    match = re.search(r"_v(\d+)$", name)
    if match:
        return (int(match.group(1)), name)
    return (0, name)


def main() -> None:
    TMP_ROOT.mkdir(parents=True, exist_ok=True)
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)

    pdfs = sorted(PDF_ROOT.glob("*.pdf"), key=lambda path: path.name)
    records: list[dict[str, object]] = []
    for pdf in pdfs:
        reader = PdfReader(str(pdf))
        text = "\n\n".join(page.extract_text() or "" for page in reader.pages)
        normalized = normalize(text)
        text_path = TMP_ROOT / f"{pdf.stem}.txt"
        text_path.write_text(text, encoding="utf-8")
        metadata = reader.metadata or {}
        records.append(
            {
                "name": pdf.name,
                "bytes": pdf.stat().st_size,
                "sha256": sha256(pdf),
                "pages": len(reader.pages),
                "text_chars": len(text),
                "normalized_text_sha256": hashlib.sha256(
                    normalized.encode("utf-8")
                ).hexdigest().upper(),
                "metadata": {
                    "title": metadata.get("/Title"),
                    "author": metadata.get("/Author"),
                    "subject": metadata.get("/Subject"),
                    "creator": metadata.get("/Creator"),
                    "producer": metadata.get("/Producer"),
                    "creation_date": metadata.get("/CreationDate"),
                    "modification_date": metadata.get("/ModDate"),
                },
                "encrypted": bool(reader.is_encrypted),
                "extracted_text": str(text_path.relative_to(ROOT)),
            }
        )

    side_records = [
        record
        for record in records
        if str(record["name"]).startswith("mlc_subresearch_")
    ]
    side_records.sort(key=lambda record: version_key(PDF_ROOT / str(record["name"])))
    for index, record in enumerate(side_records):
        record["sequence_index"] = index
        if index == 0:
            record["previous_name"] = None
            record["normalized_prefix_of_next"] = None
            continue
        previous = side_records[index - 1]
        previous_text = normalize(
            (ROOT / str(previous["extracted_text"])).read_text(encoding="utf-8")
        )
        current_text = normalize(
            (ROOT / str(record["extracted_text"])).read_text(encoding="utf-8")
        )
        record["previous_name"] = previous["name"]
        record["previous_normalized_prefix"] = current_text.startswith(previous_text)
        record["normalized_character_growth"] = len(current_text) - len(previous_text)

    manifest = {
        "schema": "mlc-side-research-library-audit-v1",
        "source_root": str(PDF_ROOT),
        "pdf_count": len(records),
        "side_research_pdf_count": len(side_records),
        "records": records,
        "revision_sequence": [record["name"] for record in side_records],
    }
    MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(
        f"pdfs={len(records)} side_research={len(side_records)} "
        f"manifest={MANIFEST.relative_to(ROOT)}"
    )
    for record in side_records:
        print(
            f"{record['sequence_index']:02d} "
            f"pages={record['pages']:>3} "
            f"chars={record['text_chars']:>7} "
            f"prefix={record.get('previous_normalized_prefix')} "
            f"{record['name']}"
        )


if __name__ == "__main__":
    main()
