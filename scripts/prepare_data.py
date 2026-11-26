#!/usr/bin/env python3
"""Build lossless, source-linked research data for the browser.

The original results and ledger remain the authority. JavaScript cannot exactly
represent every JSON integer in these certificates, so integers outside its safe
range are emitted as decimal strings. No theorem status is inferred or promoted.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from urllib.parse import quote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "public" / "data"
REPOSITORY = "https://github.com/dovvnloading/loops-research-archive"
MAX_SAFE_INTEGER = 2**53 - 1
DATASETS = {
    "ledger": ("ledger.json", "Original obligation statuses and later research updates; proved does not mean Lean-checked."),
    "symbolic": ("results/period27_symbolic_marking.json", "Exact finite symbolic marking, not certified parameter-ray landing."),
    "tip": ("results/period27_misiurewicz_tip.json", "Exact finite real-algebraic and angular certificate; analytic landing inputs remain imported."),
    "portrait": ("results/period27_tip_ray_portrait.json", "Exact rational orbit portrait. Chords represent combinatorial pairings, not physical external rays."),
    "puzzle": ("results/tip_puzzle_ray_tree.json", "Finite ambient alpha-ray tree through depth six; unassigned localization remains unassigned."),
    "domains": ("results/tip_complex_domains.json", "Exact rational margins with written classical topological deductions; target radii are not source-domain shapes."),
    "markov": ("results/period27_real_markov_spectrum.json", "Finite real Markov spine and spectrum; no general MLC conclusion."),
    "renewal": ("results/clone_renewal_clock_20261123.json", "Finite exact quotient-ring regressions; separate numerical diagnostics are not certified enclosures."),
    "root-geometry": ("results/tip_root_interval_geometry.json", "Finite certified root-interval geometry within the source's stated scope."),
    "readout": ("results/clone_resonant_readout_20261123.json", "Finite resonant readout experiment within the source's stated scope."),
}
ARCHIVE_DIRS = {"code", "docs", "figs", "formalization", "papers", "research", "results"}
ROOT_ARCHIVE_SUFFIXES = {".md", ".lean", ".pdf", ".cff", ".toml"}
ROOT_ARCHIVE_NAMES = {"LICENSE", "lean-toolchain", "lake-manifest.json", "requirements.txt", "ledger.json", "ledger.js"}


def tracked_files() -> list[str]:
    try:
        raw = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT)
        return sorted(p for p in raw.decode().split("\0") if p)
    except (subprocess.CalledProcessError, FileNotFoundError):
        candidates = [p for p in ROOT.iterdir() if p.is_file()]
        candidates += [p for directory in ARCHIVE_DIRS for p in (ROOT / directory).rglob("*") if p.is_file()]
        return sorted(str(p.relative_to(ROOT)) for p in candidates)


def source_commit() -> str:
    # A Site has its own Git history. Never invent GitHub links to an application-
    # only merge commit: retain the public upstream revision while its research
    # inputs are unchanged. Later research changes fall back to their own history.
    pin = ROOT / ".openai" / "research-source.json"
    if pin.is_file():
        revision = json.loads(pin.read_text()).get("commit", "")
        if len(revision) == 40 and all(c in "0123456789abcdef" for c in revision):
            try:
                subprocess.check_call(["git", "cat-file", "-e", revision + "^{commit}"], cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                unchanged = subprocess.run(["git", "diff", "--quiet", revision, "--", "ledger.json", "results", "research", "formalization", "*.lean", "papers"], cwd=ROOT).returncode == 0
                if unchanged:
                    return revision
            except (subprocess.CalledProcessError, FileNotFoundError):
                pass
    try:
        return subprocess.check_output(
            ["git", "log", "--first-parent", "-1", "--format=%H", "--", "ledger.json", "results", "research", "formalization", "*.lean", "papers"],
            cwd=ROOT, text=True,
        ).strip() or "unversioned"
    except (subprocess.CalledProcessError, FileNotFoundError):
        return "unversioned"


def lossless(value):
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return str(value) if abs(value) > MAX_SAFE_INTEGER else value
    if isinstance(value, list):
        return [lossless(item) for item in value]
    if isinstance(value, dict):
        return {key: lossless(item) for key, item in value.items()}
    return value


def source_url(path: str, commit: str, fragment: str = "") -> str:
    revision = commit if commit != "unversioned" else "main"
    return f"{REPOSITORY}/blob/{revision}/{quote(path, safe='/')}" + (f"#{fragment}" if fragment else "")


def resolve_evidence(reference: str, files: set[str], by_name: dict[str, list[str]]):
    parsed = urlsplit(reference)
    if parsed.scheme in ("http", "https"):
        return None, reference, "external"
    path, _, fragment = reference.partition("#")
    path = path.removeprefix("./")
    if path in files:
        return path, fragment, "direct"
    scoped = "research/mlc_unified/" + path
    if scoped in files:
        return scoped, fragment, "mlc_unified"
    matches = by_name.get(Path(path).name, [])
    if len(matches) == 1:
        return matches[0], fragment, "unique_filename"
    return None, fragment, "unresolved"


def is_archive_file(name: str) -> bool:
    parts = Path(name).parts
    if not parts or any(part in {"__pycache__", "node_modules", ".lake", ".git"} for part in parts):
        return False
    return parts[0] in ARCHIVE_DIRS or (len(parts) == 1 and (
        Path(name).suffix in ROOT_ARCHIVE_SUFFIXES or name in ROOT_ARCHIVE_NAMES))


def write_json(path: Path, value) -> bytes:
    encoded = (json.dumps(lossless(value), ensure_ascii=False, indent=2) + "\n").encode()
    path.write_bytes(encoded)
    return encoded


def main() -> None:
    OUTPUT.mkdir(parents=True, exist_ok=True)
    files = set(tracked_files())
    by_name = defaultdict(list)
    for name in sorted(files):
        by_name[Path(name).name].append(name)
    commit = source_commit()
    entries = []
    inputs = sha256()
    ledger_counts = None
    unresolved = []
    for key, (path, scope) in DATASETS.items():
        raw = (ROOT / path).read_bytes()
        inputs.update(path.encode() + b"\0" + raw + b"\0")
        value = json.loads(raw)
        if key == "ledger":
            obligations = value["obligations"]
            actual_counts = dict(Counter(item["status"] for item in obligations))
            if actual_counts != value["counts"]:
                raise ValueError("Ledger counts disagree with obligation statuses")
            ids = [item["id"] for item in obligations + value.get("research_updates", [])]
            if len(set(ids)) != len(ids):
                raise ValueError("Duplicate IDs across the ledger and research updates")
            for kind in ("obligations", "research_updates"):
                for row in value.get(kind, []):
                    evidence = str(row.get("evidence", ""))
                    resolved, fragment, method = resolve_evidence(evidence, files, by_name)
                    row["evidence_path"] = resolved
                    row["evidence_resolution"] = method
                    row["evidence_url"] = (fragment if method == "external" else
                                           source_url(resolved, commit, fragment) if resolved else None)
                    if method == "unresolved":
                        unresolved.append({"id": row["id"], "evidence": evidence})
                    verifier = row.get("verifier")
                    if isinstance(verifier, str) and verifier in files:
                        row["verifier_url"] = source_url(verifier, commit)
            ledger_counts = {
                "obligations": len(obligations),
                "research_updates": len(value.get("research_updates", [])),
                **actual_counts,
            }
            value["provenance"] = {
                "source_commit": commit,
                "status_note": "Original source statuses retained. A proved ledger entry may be a written or conditional result; it is not automatically kernel-checked.",
                "mlc_status": "MLC remains open",
            }
        payload = write_json(OUTPUT / f"{key}.json", value)
        entries.append({
            "id": key, "file": f"{key}.json", "source_path": path,
            "source_url": source_url(path, commit), "source_sha256": sha256(raw).hexdigest(),
            "sha256": sha256(payload).hexdigest(), "bytes": len(payload), "scope": scope,
        })
    catalog_revision = commit
    upstream_blobs = {}
    try:
        for record in subprocess.check_output(["git", "ls-tree", "-rz", "--full-tree", catalog_revision], cwd=ROOT).decode().split("\0"):
            if record:
                metadata, filename = record.split("\t", 1)
                upstream_blobs[filename] = metadata.split()[2]
    except (subprocess.CalledProcessError, FileNotFoundError):
        pass
    catalog = []
    for name in sorted(files):
        if is_archive_file(name) and (ROOT / name).is_file():
            suffix = Path(name).suffix.lower()
            kind = ("paper" if suffix == ".pdf" else "formalization" if suffix == ".lean" else
                    "certificate" if suffix == ".json" else "verifier" if suffix == ".py" else
                    "figure" if suffix in {".svg", ".png", ".jpg", ".jpeg"} else "document")
            # Updated application documents remain available locally; an immutable
            # upstream link is used only when its blob matches the packaged file.
            from hashlib import sha1
            raw_file = (ROOT / name).read_bytes()
            blob_hash = sha1(b"blob " + str(len(raw_file)).encode() + b"\0" + raw_file).hexdigest()
            pinned = upstream_blobs.get(name) == blob_hash
            catalog.append({"path": name, "title": Path(name).stem.replace("_", " "),
                            "kind": kind, "bytes": (ROOT / name).stat().st_size,
                            "sha256": sha256((ROOT / name).read_bytes()).hexdigest(),
                            "url": source_url(name, catalog_revision) if pinned else name,
                            "source_revision": catalog_revision if pinned else None,
                            "source_location": "upstream" if pinned else "packaged",
                            "local_url": name})
    write_json(OUTPUT / "catalog.json", {"source_commit": commit, "catalog_revision": catalog_revision, "files": catalog})
    write_json(OUTPUT / "manifest.json", {
        "schema": "loops-research-data-v1", "source_repository": REPOSITORY,
        "source_commit": commit, "input_sha256": inputs.hexdigest(),
        "integer_encoding": "Integers outside ±(2^53−1) are lossless decimal strings.",
        "mlc_status": "MLC remains open", "counts": ledger_counts,
        "datasets": entries, "catalog_file": "catalog.json", "archive_files": len(catalog),
        "unresolved_evidence": unresolved,
    })
    print(f"Prepared {len(entries)} datasets; {ledger_counts}; {len(catalog)} archive files; "
          f"{len(unresolved)} existing unavailable evidence references explicitly retained.")


if __name__ == "__main__":
    main()
