"""Download exact versions and generate a source-location/checksum certificate.

Not a proof checker. PDF page/line coordinates refer to pypdf extraction, not
printed TeX lines. No mathematical conclusion is inferred from token matches.
"""
import argparse
import hashlib
import io
import itertools
import subprocess
import json
import re
import time
from pathlib import Path
from urllib.request import Request, urlopen

from pypdf import PdfReader

HERE = Path(__file__).resolve().parent
BASE = '9f39af35723e1ebe8f94963f1dbd71d54d4309a9'
PDF_SHA256 = {"KKL":"4c08805384b473dc0e55d76491c52c9fbe7c027e6da301f2c365a170ed7d9140","DL":"e88462e43b3c172cf309d5b3d38caa21ee8f43876bac1e07cce84b309dfb8c6b"}
PROOF_BLOBS = {
    "research/mlc_unified/kkl_stationary_relative_wave_continuation.md": "aa9f13d13c4f9fdac4550e32c22e947e9d7831d3",
    "research/mlc_unified/kkl_stationary_n1_integration_audit_20260726.md": "3c35f778affc85061a453a9023091aa993a5cd08",
    "research/mlc_unified/kkl_stationary_n1_frozen_backward_audit_20260726.md": "640aaa4b31142749f7a25d652e91ba4a51aefe81",
    "research/mlc_unified/kkl_stationary_n1_borel_ordered_wave_realization_20260726.md": "8096df508def24afb61a5b295405069768ba58ba",
    "research/mlc_unified/kkl_stationary_n1_borel_width_envelope_20260726.md": "7e7afddfe849b17eb224728d80e3eb7a37040eb8",
    "research/mlc_unified/kkl_stationary_n1_dl_relative_discard_bound_20260726.md": "5bb4f27820b2a96f594d04a0442336c6d6246073",
    "research/mlc_unified/kkl_stationary_n1_degree_two_directionalization_audit_20260726.md": "e440e1c6a947b12c9186e6d9d4987e721e1853ec",
    "research/mlc_unified/kkl_stationary_n1_bowr_frozen_backward_audit_20260726.md": "40725193c96b2c23bbbd03b06c12a61ab4fe83de",
    "research/mlc_unified/kkl_stationary_retained_realization_source_audit.md": "17d09499a8bbebdeab4f8ecac0d7e0a5c995087f",
    "research/mlc_unified/qa_extremal_wave_2026-07-26.md": "1260e3612251db8f164cce7f8bec0e7d8b026160",
    "research/mlc_unified/qa_native_kkl_stationary_2026-07-26.md": "408fab92bf866f6f7bcedfacd1a13f1ef684b78e"
}
EXPECTED_STATUS = {
    'DL_NATIVE_RECTIFIABLE_RELATIVE_DISCARD_BOUND': 'imported',
    'N1_PREPRUNING_BOREL_WAVE_ATLAS': 'proved',
    'N1_BOREL_RECTIFIABLE_CORE_REDUCTION': 'proved',
    'DL_RELATIVE_DISCARD_FAMILY_BOUND': 'proved',
    'BOREL_WIDTH_ENVELOPE_PRUNING': 'proved',
    'STANDARD_BOREL_ORDERED_WAVE_REALIZATION': 'proved',
    'KKL_STATIONARY_ONE_RETAINED_CHAIN': 'proved',
    'KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION_ANALYTIC': 'proved',
    'KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION': 'proved',
    'KKL_PARABOLIC_WAVE_STATIONARY_PROOF_REPAIR': 'open',
}
SOURCES = {
    "KKL": ("2606.27272v1", ["Theorem A", "Theorem C", "Theorem D", "Theorem 3.6",
        "Proposition 3.9", "Lemma 6.1", "Proposition 6.6", "Lemma 6.14",
        "Proposition 6.20", "Proposition 6.21", "Proposition 6.22", "Proposition 6.23",
        "Lemma 6.24", "(6.25)", "(6.26)", "(6.27)", "(6.28)", "(6.29)",
        "(6.30)", "Lemma 6.31", "(6.34)", "A.1. Ideal markings",
        "Lemma A.10", "Lemma A.11", "Proposition A.12", "Lemma A.13",
        "Proposition A.14", "Lemma A.15"]),
    "DL": ("2309.02107v3", ["Lemma 5.1", "Lemma 5.2"]),
}


def download(url):
    for attempt in range(3):
        try:
            with urlopen(Request(url, headers={"User-Agent": "KKL-source-audit/1.0"}), timeout=90) as r:
                return r.read()
        except OSError:
            if attempt == 2:
                raise
            time.sleep(3 * (attempt + 1))


def locations(pdf, needles):
    reader = PdfReader(io.BytesIO(pdf))
    hits = {needle: [] for needle in needles}
    for page_no, page in enumerate(reader.pages, 1):
        lines = (page.extract_text() or "").splitlines()
        # tolerate inter-word whitespace and ligatures introduced by extraction;
        # search one or two lines, preserving the first extracted line number.
        for i, line in enumerate(lines):
            window = re.sub(r"\s+", "", line + " " + (lines[i+1] if i+1 < len(lines) else ""))
            current = re.sub(r"\s+", "", line)
            for needle in needles:
                token = re.sub(r"\s+", "", needle)
                if token in current or (token in window and token not in re.sub(r"\s+", "", lines[i+1] if i+1 < len(lines) else "")):
                    hits[needle].append({"pdf_page": page_no, "extracted_line": i+1})
    return len(reader.pages), hits


def proof_inputs():
    root = HERE.parents[2]
    objects = {}
    for path, expected in sorted(PROOF_BLOBS.items()):
        raw = (root / path).read_bytes()
        actual = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        if actual != expected:
            raise ValueError(f"Changed pinned proof input {path}: {actual} != {expected}")
        objects[path] = {"git_blob": actual, "sha256": hashlib.sha256(raw).hexdigest()}
    # The ledger is read from the pinned base (not a potentially newer main).
    raw = subprocess.check_output(["git", "show", f"{BASE}:ledger.json"], cwd=root)
    if hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest() != "659da1da97288d7e2d927b2b59873af13e9da1e1":
        raise ValueError("Pinned base ledger blob mismatch")
    ledger = {item["id"]: item for item in json.loads(raw)["obligations"]}
    for key, status in EXPECTED_STATUS.items():
        if ledger[key]["status"] != status:
            raise ValueError(f"Unexpected base ledger status: {key}")
    seen = set()
    active = set()
    def walk(key):
        if key in active:
            raise ValueError(f"Cycle at {key}")
        if key in seen:
            return
        active.add(key)
        row = ledger[key]
        if row["status"] not in ("proved", "imported"):
            raise ValueError(f"Unclosed dependency {key}")
        for dep in row["deps"]:
            walk(dep)
        active.remove(key)
        seen.add(key)
    walk("KKL_STATIONARY_RELATIVE_WAVE_CONTINUATION")
    return {"base": BASE, "proof_objects": objects, "ledger_sha256": hashlib.sha256(raw).hexdigest(),
            "checked_status": EXPECTED_STATUS, "n1_dependency_closure": sorted(seen)}


def finite_saturation():
    """Check the finite set identities only, not analytic or geometric hypotheses."""
    count = 0
    for size in range(1, 5):
        for outputs in itertools.product(range(3), repeat=size):
            image = set(outputs)
            for selected in itertools.product((False, True), repeat=3):
                packet = {j for j in image if selected[j]}
                kept = {i for i, j in enumerate(outputs) if j in packet}
                lost = set(range(size)) - kept
                assert {outputs[i] for i in kept} == packet
                assert {outputs[i] for i in lost} == image - packet
                count += 1
    for b in range(1, 257):
        N = b + 3
        assert N - 2 == b + 1
        assert all(2**n <= 2**(b+1) and N-n >= 2 for n in range(N-1))
    return {"finite_maps_and_packets_checked": count, "horizon_b_range": [1, 256],
            "scope": "set saturation and index arithmetic only"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cache", type=Path, help="optional external directory containing <id>.pdf files")
    parser.add_argument("--output", type=Path, default=HERE / "source_lock.json")
    args = parser.parse_args()
    result = {"schema": 1, "scope": "source identity and extraction only; not proof of Lemma 6.24", "sources": {}}
    for name, (version, needles) in SOURCES.items():
        url = "https://arxiv.org/pdf/" + version
        path = args.cache / (version + ".pdf") if args.cache else None
        raw = path.read_bytes() if path and path.is_file() else download(url)
        if not raw.startswith(b"%PDF-"):
            raise ValueError(f"{url}: not a PDF")
        if hashlib.sha256(raw).hexdigest() != PDF_SHA256[name]:
            raise ValueError(f"{version}: pinned PDF SHA-256 mismatch")
        pages, hits = locations(raw, needles)
        for required in (["Lemma 6.24", "Lemma A.13"] if name == "KKL" else ["Lemma 5.2"]):
            if not hits[required]:
                raise ValueError(f"{version}: missing {required}; inspect extraction")
        if name == "KKL" and pages != 73:
            raise ValueError(f"{version}: expected 73 PDF pages, got {pages}")
        result["sources"][name] = {"version": version, "pdf_url": url, "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest(), "pdf_pages": pages, "locations": hits}
    result["proof_inputs"] = proof_inputs()
    result["finite_saturation"] = finite_saturation()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    args.output.write_text(rendered, encoding="utf-8")
    print(rendered)


if __name__ == "__main__":
    main()
