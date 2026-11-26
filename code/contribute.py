#!/usr/bin/env python3
"""Contributor entry point: pick an open obligation, start a packet, check it.

    python code/contribute.py next            open obligations nobody has claimed
    python code/contribute.py show ID         statement, prerequisites, evidence, dependants
    python code/contribute.py start ID SLUG   create contributions/SLUG_YYYYMMDD/NOTE.md
    python code/contribute.py check           the checks CI runs on a contribution PR
    python code/contribute.py lean-add FILE --packet DIR   register a Lean file in the build
    python code/contribute.py targets         regenerate OPEN_TARGETS.md (maintainers)

Standard library only. The ledger (ledger.json) is the authority; this script
reads it, ranks open obligations, and checks the shape of a contribution. It
does not judge mathematics and never changes a theorem's status.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import subprocess
import sys
import urllib.error
import urllib.request
from collections import defaultdict
from pathlib import Path

REPO = "dovvnloading/loops-research-archive"
REPO_URL = f"https://github.com/{REPO}"
ROOT = Path(__file__).resolve().parents[1]
INBOX = "contributions"
TARGETS_MD = "OPEN_TARGETS.md"
TARGETS_JSON = "results/open_targets.json"
RESULTS = {
    "closes": "a complete proof of the obligation exactly as the ledger states it",
    "partial": "a proved subcase, reduction or lemma toward the obligation",
    "counterexample": "the statement as written fails; the construction is given",
    "obstruction": "a named route to the obligation cannot work, with proof",
    "correction": "an error in a source, citation, statement or dependency",
    "evidence": "a reproducible computation; evidence only, not a proof",
}
SECTIONS = ("Claim", "Evidence", "Dependencies", "Boundary", "Attribution")
PLACEHOLDER = "REPLACE"
# A contribution proposes; the maintainer records. These files hold the public
# status record or the rules themselves, so a contribution PR leaves them alone.
RECORD = (
    "ledger.json", "ledger.js", "ResearchLedger.lean", "README.md", "RESEARCH_MAP.md",
    "REFEREE_REPORT.md", "CONTRIBUTING.md", "AGENTS.md", "CLAUDE.md", "GEMINI.md",
    TARGETS_MD, TARGETS_JSON, "research/mlc_unified/proof_obligations.json",
    "marked_width_mlc_manuscript.pdf", "code/contribute.py", "code/test_contribute.py",
    f"{INBOX}/README.md", f"{INBOX}/NOTE_TEMPLATE.md",
)
RECORD_PREFIXES = (".github/",)
LEAN_REGISTRATION = (
    "lakefile.toml", "formalization/weighted/lakefile.toml",
    "formalization/physical_bridge_index.json", "formalization/physical_bridge_sources.tsv",
)
STALE_DAYS = 14
SCRIPT_TIMEOUT = 900


# ---------------------------------------------------------------- ledger ----

def assumptions(row: dict) -> list[str]:
    raw = row.get("hyp", "none")
    if not raw or raw == "none":
        return []
    return [re.sub(r"\s+", "", part) for part in raw.split(",")]


class Ledger:
    def __init__(self, root: Path):
        data = json.loads((root / "ledger.json").read_text(encoding="utf-8"))
        self.rows = data["obligations"]
        self.updates = data.get("research_updates", [])
        self.by_id = {row["id"]: row for row in self.rows}
        self.pre = {
            row["id"]: list(dict.fromkeys([*row["deps"], *assumptions(row)])) for row in self.rows
        }
        self.dependants = defaultdict(set)
        for key, prerequisites in self.pre.items():
            for item in prerequisites:
                self.dependants[item].add(key)

    def downstream(self, key: str) -> set[str]:
        seen: set[str] = set()
        pending = [key]
        while pending:
            for item in self.dependants[pending.pop()]:
                if item not in seen:
                    seen.add(item)
                    pending.append(item)
        return seen

    def open_prerequisites(self, key: str) -> list[str]:
        return [p for p in self.pre[key] if self.by_id[p]["status"] == "open"]

    def open_rows(self) -> list[dict]:
        rows = [row for row in self.rows if row["status"] == "open"]
        return sorted(rows, key=lambda row: (-len(self.downstream(row["id"])), row["id"]))

    def ready(self) -> list[dict]:
        return [row for row in self.open_rows() if not self.open_prerequisites(row["id"])]

    def blocked(self) -> list[dict]:
        return [row for row in self.open_rows() if self.open_prerequisites(row["id"])]


def tracked(root: Path) -> list[str]:
    try:
        raw = subprocess.check_output(["git", "ls-files", "-z"], cwd=root)
        return [name for name in raw.decode("utf-8").split("\0") if name]
    except (subprocess.CalledProcessError, FileNotFoundError):
        return [p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()]


def evidence_path(reference: str, files: list[str]) -> str | None:
    """Same resolution as scripts/prepare_data.py: direct, mlc_unified, unique name."""
    path = reference.partition("#")[0].removeprefix("./")
    if not path or "://" in reference:
        return None
    known = set(files)
    if path in known:
        return path
    if "research/mlc_unified/" + path in known:
        return "research/mlc_unified/" + path
    matches = [name for name in files if name.rsplit("/", 1)[-1] == path.rsplit("/", 1)[-1]]
    return matches[0] if len(matches) == 1 else None


# ---------------------------------------------------------------- claims ----

def fetch_open_pulls() -> list[dict] | None:
    """Open pull requests on the public repository, or None when offline."""
    request = urllib.request.Request(
        f"https://api.github.com/repos/{REPO}/pulls?state=open&per_page=100",
        headers={"Accept": "application/vnd.github+json", "User-Agent": "loops-contribute"},
    )
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if token:
        request.add_header("Authorization", f"Bearer {token}")
    try:
        with urllib.request.urlopen(request, timeout=20) as response:
            return json.loads(response.read().decode("utf-8"))
    except (urllib.error.URLError, TimeoutError, ValueError, OSError):
        return None


def claimed_ids(pulls: list[dict], open_ids: set[str], today: dt.date | None = None) -> dict:
    """Map ledger ID -> the open pull requests whose title or `ledger:` line names it."""
    today = today or dt.datetime.now(dt.timezone.utc).date()
    claims: dict[str, list[dict]] = defaultdict(list)
    for pull in pulls:
        named = set(re.findall(r"[A-Z][A-Z0-9_]{2,}", pull.get("title") or ""))
        for line in (pull.get("body") or "").splitlines():
            match = re.match(r"\s*ledger\s*:\s*(.+)$", line, re.IGNORECASE)
            if match:
                named.update(re.findall(r"[A-Z][A-Z0-9_]{2,}", match[1]))
        updated = (pull.get("updated_at") or "")[:10]
        try:
            idle = (today - dt.date.fromisoformat(updated)).days
        except ValueError:
            idle = 0
        for key in sorted(named & open_ids):
            claims[key].append({
                "number": pull.get("number"), "url": pull.get("html_url"),
                "idle_days": idle, "stale": idle > STALE_DAYS,
            })
    return dict(claims)


# --------------------------------------------------------------- packets ----

def parse_note(text: str) -> tuple[dict, dict]:
    """Return (front matter, {section title: body}) of a NOTE.md."""
    meta: dict[str, str] = {}
    body = text
    if text.startswith("---"):
        head, _, body = text[3:].partition("\n---")
        for line in head.splitlines():
            key, sep, value = line.partition(":")
            if sep and key.strip() and not key.startswith(" "):
                meta[key.strip().lower()] = value.strip()
    sections: dict[str, str] = {}
    title = None
    for line in body.splitlines():
        heading = re.match(r"##\s+(.+?)\s*$", line)
        if heading:
            title = heading[1]
            sections[title] = ""
        elif title is not None:
            sections[title] += line + "\n"
    return meta, sections


def ledger_ids(meta: dict) -> list[str]:
    return [item for item in re.split(r"[,\s]+", meta.get("ledger", "")) if item]


def note_problems(text: str, ledger: Ledger) -> list[tuple[str, str]]:
    """(problem, fix) pairs for one NOTE.md."""
    problems = []
    meta, sections = parse_note(text)
    ids = ledger_ids(meta)
    known = set(ledger.by_id) | {row["id"] for row in ledger.updates}
    if not ids:
        problems.append((
            "front matter has no `ledger:` line",
            "name the obligation this work addresses, for example `ledger: MAPPING_TELESCOPE`; "
            "`python code/contribute.py next` lists them",
        ))
    for key in ids:
        if key not in known:
            problems.append((
                f"`{key}` is not an ID in ledger.json",
                "copy the ID exactly from `python code/contribute.py next` or ledger.json",
            ))
    result = meta.get("result", "")
    if result not in RESULTS:
        problems.append((
            f"front matter `result:` is {result!r}",
            "use one of: " + ", ".join(RESULTS),
        ))
    for key in ("ai", "human_review"):
        if not meta.get(key) or PLACEHOLDER in meta[key]:
            problems.append((
                f"front matter `{key}:` is empty",
                "name the AI system and model used (or `none`)" if key == "ai" else
                "say what a person checked, or `none`",
            ))
    for title in SECTIONS:
        content = sections.get(title)
        if content is None:
            problems.append((f"section `## {title}` is missing", "keep every heading of the template"))
        elif not content.strip() or PLACEHOLDER in content:
            problems.append((
                f"section `## {title}` is empty or still has template text",
                "write the section; a short honest answer is fine",
            ))
    return problems


def packet_of(path: str) -> str | None:
    parts = path.split("/")
    if len(parts) >= 3 and parts[0] == INBOX:
        return f"{INBOX}/{parts[1]}"
    return None


# ---------------------------------------------------------------- output ----

def out(text: str = "") -> None:
    print(text)


def wrap(text: str, width: int = 96, indent: str = "    ") -> str:
    lines, line = [], ""
    for word in text.split():
        if line and len(line) + 1 + len(word) > width - len(indent):
            lines.append(indent + line)
            line = word
        else:
            line = f"{line} {word}".strip()
    return "\n".join(lines + [indent + line])


def describe(ledger: Ledger, row: dict, files: list[str]) -> str:
    key = row["id"]
    path = evidence_path(row["evidence"], files)
    lines = [
        f"{key}   [{row['status']}]   {len(ledger.downstream(key))} obligations depend on it",
        wrap(row["statement"]),
        "    prerequisites: " + (", ".join(
            f"{p} [{ledger.by_id[p]['status']}]" for p in ledger.pre[key]) or "none"),
        f"    where it is stated: {path or row['evidence']}"
        + (f"  (anchor #{row['evidence'].partition('#')[2]})" if "#" in row["evidence"] and path else ""),
    ]
    return "\n".join(lines)


# -------------------------------------------------------------- commands ----

def cmd_next(args, root: Path) -> int:
    ledger = Ledger(root)
    files = tracked(root)
    ready, blocked = ledger.ready(), ledger.blocked()
    pulls = None if args.offline else fetch_open_pulls()
    claims = claimed_ids(pulls, {row["id"] for row in ledger.open_rows()}) if pulls is not None else {}
    if args.json:
        out(json.dumps({
            "claims_checked": pulls is not None,
            "ready": [{"id": row["id"], "downstream": len(ledger.downstream(row["id"])),
                       "claimed_by": claims.get(row["id"], [])} for row in ready],
        }, indent=2))
        return 0
    out(f"{len(ready)} of {len(ready) + len(blocked)} open obligations have every prerequisite closed.")
    out("Most depended-on first. Choose one yourself; any of them is real work.\n")
    free = 0
    for row in ready:
        active = [c for c in claims.get(row["id"], []) if not c["stale"]]
        stale = [c for c in claims.get(row["id"], []) if c["stale"]]
        if active and not args.all:
            continue
        free += not active
        out(describe(ledger, row, files))
        if active:
            out("    CLAIMED by " + ", ".join(f"PR #{c['number']}" for c in active))
        elif stale:
            out("    stale claim (no activity for over two weeks): "
                + ", ".join(f"PR #{c['number']}" for c in stale) + "; you may take it")
        out()
    if pulls is None:
        out("Claims were not checked (offline). Look at the open pull requests before you start:")
        out(f"  {REPO_URL}/pulls")
    else:
        hidden = len(ready) - free
        out(f"{free} unclaimed" + (f"; {hidden} already claimed by an open pull request "
                                  "(use --all to see them)" if hidden and not args.all else "") + ".")
    out("\nEvery other open obligation (waiting on one of the above) is in OPEN_TARGETS.md.")
    out("Next: python code/contribute.py show ID   then   python code/contribute.py start ID your_slug")
    return 0


def cmd_show(args, root: Path) -> int:
    ledger = Ledger(root)
    row = ledger.by_id.get(args.id)
    if row is None:
        close = [key for key in ledger.by_id if args.id.upper() in key][:8]
        out(f"No obligation named {args.id}." + (" Did you mean: " + ", ".join(close) if close else ""))
        return 1
    files = tracked(root)
    out(describe(ledger, row, files))
    waiting = ledger.open_prerequisites(args.id)
    if row["status"] == "open":
        out("    ready to work on: " + ("yes, every prerequisite is closed" if not waiting else
                                        "its open prerequisites come first: " + ", ".join(waiting)))
    direct = sorted(ledger.dependants[args.id])
    if direct:
        out("    used directly by: " + ", ".join(direct[:12]) + (" ..." if len(direct) > 12 else ""))
    if row.get("clauses"):
        out("    source clauses: " + row["clauses"])
    out("\nExisting bridge and contract references for this row:")
    out(f"  python -B code/verify_physical_bridge_contracts.py --claim {args.id}")
    return 0


def cmd_start(args, root: Path) -> int:
    ledger = Ledger(root)
    row = ledger.by_id.get(args.id)
    if row is None:
        out(f"No obligation named {args.id}. Run: python code/contribute.py next")
        return 1
    slug = re.sub(r"[^a-z0-9]+", "_", args.slug.lower()).strip("_")
    if not slug:
        out("Give a short slug in lowercase words, for example: telescope_degree_count")
        return 1
    name = f"{slug}_{dt.date.today():%Y%m%d}"
    folder = root / INBOX / name
    if folder.exists():
        out(f"{INBOX}/{name} already exists; choose another slug.")
        return 1
    template = (root / INBOX / "NOTE_TEMPLATE.md").read_text(encoding="utf-8")
    note = template.replace("LEDGER_ID", args.id, 1).replace("STATEMENT", row["statement"], 1)
    folder.mkdir(parents=True)
    (folder / "NOTE.md").write_text(note, encoding="utf-8", newline="\n")
    branch = f"contrib/{slug.replace('_', '-')}-{dt.date.today():%Y%m%d}"
    out(f"Created {INBOX}/{name}/NOTE.md for {args.id}.\n")
    out("Claim it now, before doing the work, so nobody duplicates it:")
    out(f"  git checkout -b {branch}")
    out(f"  git add {INBOX}/{name} && git commit -m \"[{args.id}] start {slug}\"")
    out("  gh repo fork --remote        # only if you cannot push to the repository itself")
    out("  git push -u origin HEAD")
    out(f"  gh pr create --draft --title \"[{args.id}] <what you intend to show>\" "
        f"--body-file {INBOX}/{name}/NOTE.md")
    out(f"\nThen work inside {INBOX}/{name}/, commit as you go, and run:")
    out("  python code/contribute.py check")
    return 0


def git(root: Path, *command: str) -> str:
    return subprocess.run(["git", *command], cwd=root, capture_output=True, text=True,
                          encoding="utf-8", errors="replace").stdout


def changed_files(root: Path, base: str | None) -> tuple[list[str], list[str], str]:
    """(present, deleted, base used) relative to the merge base with the main line."""
    candidates = [base] if base else ["upstream/main", "origin/main", "main"]
    for ref in candidates:
        merge_base = git(root, "merge-base", ref, "HEAD").strip()
        if merge_base:
            break
    else:
        raise SystemExit(
            "Cannot find the main branch to compare against. Run `git fetch origin main` "
            "(or pass --base REF) and try again."
        )
    present, deleted = set(), set()
    for line in git(root, "diff", "--name-status", "--no-renames", merge_base).splitlines():
        status, _, path = line.partition("\t")
        (deleted if status == "D" else present).add(path)
    present.update(p for p in git(root, "ls-files", "--others", "--exclude-standard").splitlines() if p)
    return sorted(present), sorted(deleted), ref


class Report:
    def __init__(self):
        self.lines: list[str] = []
        self.failures = 0

    def ok(self, text: str) -> None:
        self.lines.append(f"PASS  {text}")

    def warn(self, text: str) -> None:
        self.lines.append(f"NOTE  {text}")

    def fail(self, text: str, fix: str) -> None:
        self.failures += 1
        self.lines.append(f"FAIL  {text}\n      Fix: {fix}")


def run_tool(root: Path, command: list[str], timeout: int) -> tuple[bool, str]:
    environment = dict(os.environ, PYTHONUTF8="1", PYTHONDONTWRITEBYTECODE="1")
    try:
        done = subprocess.run(command, cwd=root, capture_output=True, text=True, encoding="utf-8",
                              errors="replace", timeout=timeout, env=environment)
    except subprocess.TimeoutExpired:
        return False, f"timed out after {timeout} seconds"
    tail = "\n".join((done.stdout + "\n" + done.stderr).strip().splitlines()[-12:])
    return done.returncode == 0, tail


def check(root: Path, base: str | None, pr_title: str | None, run_scripts: bool) -> Report:
    report = Report()
    ledger = Ledger(root)
    present, deleted, used = changed_files(root, base)
    touched = present + deleted
    packets = sorted({p for p in map(packet_of, touched) if p})
    report.warn(f"compared with {used}: {len(touched)} changed files, {len(packets)} contribution packets")

    if targets_stale(root):
        report.fail(
            f"{TARGETS_MD} and {TARGETS_JSON} do not match ledger.json",
            "run `python code/contribute.py targets` and commit both files (maintainers only; "
            "a contribution PR does not edit ledger.json)",
        )
    else:
        report.ok("open-target list matches ledger.json")

    if not packets:
        report.warn(f"no folder under {INBOX}/ is changed, so there is no contribution packet to check")
        return report

    primary: list[str] = []
    for packet in packets:
        note = root / packet / "NOTE.md"
        if not note.is_file():
            report.fail(f"{packet}/ has no NOTE.md",
                        "create it with `python code/contribute.py start ID slug`, or copy "
                        f"{INBOX}/NOTE_TEMPLATE.md")
            continue
        text = note.read_text(encoding="utf-8")
        problems = note_problems(text, ledger)
        for problem, fix in problems:
            report.fail(f"{packet}/NOTE.md: {problem}", fix)
        if not problems:
            meta, _ = parse_note(text)
            primary.append(ledger_ids(meta)[0])
            report.ok(f"{packet}/NOTE.md names {', '.join(ledger_ids(meta))} (result: {meta['result']})")
        if not re.fullmatch(r"[a-z0-9_]+_\d{8}", packet.split("/")[1]):
            report.fail(f"{packet}: folder name must be lowercase_words_YYYYMMDD",
                        "rename it, for example telescope_degree_count_20261126")

    misplaced = [p for p in present if p.endswith(".lean") and packet_of(p)]
    for path in misplaced:
        report.fail(
            f"{path}: Lean files are not compiled from a packet folder",
            f"move it to formalization/weighted/ (Mathlib) or the repository root (core Lean), "
            f"then run `python code/contribute.py lean-add <new path> --packet {packet_of(path)}`",
        )

    for path in touched:
        if path in RECORD or path.startswith(RECORD_PREFIXES):
            report.fail(
                f"{path} is part of the public status record or the project rules",
                "revert it (`git checkout <base> -- " + path + "`). A contribution proposes; say in "
                "NOTE.md what should change and the maintainer records it after review",
            )
    outside = [p for p in touched if not packet_of(p) and p not in RECORD
               and not p.startswith(RECORD_PREFIXES) and p not in LEAN_REGISTRATION
               and not p.endswith(".lean") and not re.fullmatch(r"formalization/PHYSICAL_BRIDGES\w*\.md", p)]
    if outside:
        report.warn("also changes files outside the packet: " + ", ".join(outside[:8])
                    + (" ..." if len(outside) > 8 else "")
                    + ". Keep them only if the contribution needs them.")

    if pr_title is not None:
        missing = [key for key in dict.fromkeys(primary) if key not in pr_title]
        if missing:
            report.fail(
                f"the pull request title does not name {', '.join(missing)}",
                f"retitle it `[{missing[0]}] what the contribution shows`; the title is how "
                "others see the obligation is taken",
            )
        elif primary:
            report.ok("pull request title names the ledger ID")

    lean_changed = any(p.endswith(".lean") or p in LEAN_REGISTRATION for p in touched)
    python = sys.executable
    if lean_changed or misplaced:
        for label, script, fix in (
            ("Lean source registration and proof-escape scan", "code/verify_lean_coverage.py",
             "every Lean file must be a registered build target and contain no sorry, admit, axiom, "
             "native_decide, unsafe or implemented_by; `python code/contribute.py lean-add FILE "
             "--packet DIR` does the registration"),
            ("source and theorem index", "code/verify_physical_bridges.py",
             "the message names the unlisted file or theorem; `python code/contribute.py lean-add "
             "FILE --packet DIR` lists every public theorem of FILE for you"),
        ):
            passed, tail = run_tool(root, [python, "-B", script], 300)
            if passed:
                report.ok(label)
            else:
                report.fail(f"{label} failed:\n{indent(tail)}", fix)
        report.warn("Lean proofs are compiled and axiom-audited by the Lean workflows on the pull "
                    "request; locally run `lake build <Module>` if Lean is installed")

    scripts = sorted(p for p in present if packet_of(p)
                     and re.fullmatch(r"(check|verify)[\w.-]*\.py", p.rsplit("/", 1)[-1]))
    for script in scripts:
        if not run_scripts:
            report.warn(f"{script} not run (--no-run)")
            continue
        passed, tail = run_tool(root, [python, "-B", script], SCRIPT_TIMEOUT)
        if passed:
            report.ok(f"{script} exits 0")
        else:
            report.fail(f"{script} failed:\n{indent(tail)}",
                        "a check script must exit 0 from the repository root with the libraries in "
                        "requirements.txt, in under 15 minutes")
    if not scripts:
        report.warn("no check*.py or verify*.py in the packet; a written argument needs none, "
                    "a computation or exact certificate should ship one")
    return report


def indent(text: str) -> str:
    return "\n".join("      | " + line for line in text.splitlines())


def cmd_check(args, root: Path) -> int:
    title = args.pr_title if args.pr_title is not None else os.environ.get("CONTRIBUTE_PR_TITLE")
    report = check(root, args.base, title, not args.no_run)
    text = "\n".join(report.lines)
    verdict = ("\nRESULT: PASS. Push, and mark the pull request ready for review."
               if not report.failures else
               f"\nRESULT: {report.failures} to fix. Each FAIL line above says how; then run this again.")
    out(text + verdict)
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as handle:
            handle.write("### Contribution intake\n\n```text\n" + text + verdict + "\n```\n")
    return 1 if report.failures else 0


# --------------------------------------------------------------- targets ----

def build_targets(root: Path) -> tuple[str, str]:
    ledger = Ledger(root)
    files = tracked(root)
    ready, blocked = ledger.ready(), ledger.blocked()

    def record(row: dict) -> dict:
        return {
            "id": row["id"], "downstream": len(ledger.downstream(row["id"])),
            "statement": row["statement"], "prerequisites": ledger.pre[row["id"]],
            "open_prerequisites": ledger.open_prerequisites(row["id"]),
            "evidence": row["evidence"], "evidence_path": evidence_path(row["evidence"], files),
        }

    data = {
        "schema": "loops-open-targets-v1",
        "generated_by": "python code/contribute.py targets",
        "note": "Derived from ledger.json. Ready means every prerequisite is proved or imported. "
                "Downstream counts obligations that depend on the row through deps or hypotheses.",
        "counts": {"open": len(ready) + len(blocked), "ready": len(ready)},
        "ready": [record(row) for row in ready],
        "blocked": [record(row) for row in blocked],
    }
    as_json = json.dumps(data, indent=2, ensure_ascii=False) + "\n"

    def link(row: dict) -> str:
        path = evidence_path(row["evidence"], files)
        anchor = row["evidence"].partition("#")[2]
        if not path:
            return f"`{row['evidence']}` (file not in this checkout; see the evidence crosswalk)"
        return f"[{path}](./{path}{'#' + anchor if anchor else ''})"

    lines = [
        "# Open targets",
        "",
        "<!-- Generated by `python code/contribute.py targets` from ledger.json. Do not edit by hand. -->",
        "",
        f"The ledger has {len(ready) + len(blocked)} open obligations. **{len(ready)} are ready**: every "
        "prerequisite is already proved or imported, so work on them can start today. The rest wait on "
        "another open obligation.",
        "",
        "The number after each ID is how many ledger obligations depend on it, directly or through "
        "others. This page does not show who is working on what; `python code/contribute.py next` "
        "does, by reading the open pull requests. To take one, follow [AGENTS.md](./AGENTS.md).",
        "",
        "MLC remains open. Closing a row below is progress on the conditional reduction, not a proof "
        "of the conjecture.",
        "",
        "## Ready",
        "",
    ]
    for row in ready:
        lines += [
            f"### `{row['id']}` · {len(ledger.downstream(row['id']))} depend on it",
            "",
            row["statement"],
            "",
            "- Prerequisites (all closed): " + (", ".join(f"`{p}`" for p in ledger.pre[row["id"]]) or "none"),
            f"- Stated in: {link(row)}",
            "",
        ]
    lines += [
        "## Waiting on another open obligation",
        "",
        "Partial results on these are welcome; a complete proof needs the listed rows first.",
        "",
        "| Obligation | Depend on it | Open prerequisites |",
        "|---|---:|---|",
    ]
    for row in blocked:
        lines.append(f"| `{row['id']}` | {len(ledger.downstream(row['id']))} | "
                     + ", ".join(f"`{p}`" for p in ledger.open_prerequisites(row["id"])) + " |")
    return "\n".join(lines) + "\n", as_json


def targets_stale(root: Path) -> bool:
    markdown, as_json = build_targets(root)
    for name, expected in ((TARGETS_MD, markdown), (TARGETS_JSON, as_json)):
        path = root / name
        if not path.is_file() or path.read_text(encoding="utf-8").replace("\r\n", "\n") != expected:
            return True
    return False


def cmd_targets(args, root: Path) -> int:
    if args.check:
        stale = targets_stale(root)
        out(f"{TARGETS_MD}: " + ("STALE; run `python code/contribute.py targets`" if stale else "current"))
        return 1 if stale else 0
    markdown, as_json = build_targets(root)
    (root / TARGETS_MD).write_text(markdown, encoding="utf-8", newline="\n")
    (root / TARGETS_JSON).write_text(as_json, encoding="utf-8", newline="\n")
    out(f"Wrote {TARGETS_MD} and {TARGETS_JSON}.")
    return 0


# ------------------------------------------------------------------ lean ----

def cmd_lean_add(args, root: Path) -> int:
    sys.path.insert(0, str(root / "code"))
    from verify_physical_bridge_contracts import declaration_names, lean_code

    path = Path(args.file).as_posix().removeprefix("./")
    source = root / path
    weighted = path.startswith("formalization/weighted/")
    if not source.is_file() or not path.endswith(".lean") or not (weighted or "/" not in path):
        out("FILE must be an existing Lean file in formalization/weighted/ (may import Mathlib) "
            "or in the repository root (core Lean only).")
        return 1
    packet = Path(args.packet).as_posix().strip("/")
    note = root / packet / "NOTE.md"
    if packet_of(packet + "/NOTE.md") != packet or not note.is_file():
        out(f"--packet must be your folder under {INBOX}/ containing NOTE.md.")
        return 1
    text = source.read_text(encoding="utf-8")
    names = [name for name in dict.fromkeys(
        re.findall(r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:protected|noncomputable)\s+)*"
                   r"(?:theorem|lemma)\s+([^\s:(]+)", lean_code(text), re.MULTILINE))]
    if set(names) != declaration_names(text) or not names:
        out("No public theorem or lemma found in the file (or the declaration scan disagrees). "
            "A registered Lean file must state at least one named theorem.")
        return 1
    module = source.stem
    note_text = note.read_text(encoding="utf-8")
    meta, _ = parse_note(note_text)
    key = packet.split("/")[1].replace("_", "-")

    lakefile = source.parent / "lakefile.toml"
    lake = lakefile.read_text(encoding="utf-8")
    if not re.search(rf'^name = "{re.escape(module)}"$', lake, re.MULTILINE):
        lake = lake.rstrip("\n") + f'\n\n[[lean_lib]]\nname = "{module}"\n'
    targets = re.search(r"^defaultTargets = \[(.*)\]$", lake, re.MULTILINE)
    if targets and f'"{module}"' not in targets[1]:
        lake = lake[:targets.end() - 1] + f', "{module}"' + lake[targets.end() - 1:]
    lakefile.write_text(lake, encoding="utf-8", newline="\n")

    index_path = root / "formalization/physical_bridge_index.json"
    index = json.loads(index_path.read_text(encoding="utf-8"))
    entry = index.setdefault(key, {"guide": f"{packet}/NOTE.md#{key}", "theorems": {}, "obligations": []})
    entry["theorems"][path] = names
    known = set(Ledger(root).by_id)
    entry["obligations"] = list(dict.fromkeys(
        [*entry.get("obligations", []), *(i for i in ledger_ids(meta) if i in known)]))
    index_path.write_text(json.dumps(index, indent=2, ensure_ascii=False) + "\n",
                          encoding="utf-8", newline="\n")

    anchor = f'<a id="{key}"></a>'
    if anchor not in note_text:
        head, sep, rest = note_text[3:].partition("\n---\n") if note_text.startswith("---") else ("", "", note_text)
        note_text = (f"---{head}\n---\n\n{anchor}\n{rest}" if sep else f"{anchor}\n\n{note_text}")
        note.write_text(note_text, encoding="utf-8", newline="\n")

    tsv_path = root / "formalization/physical_bridge_sources.tsv"
    rows = tsv_path.read_text(encoding="utf-8").split("\n")
    if not any(row.split("\t")[0] == path for row in rows):
        new = f"{path}\t{' '.join(args.route)}"
        # Keep the row beside the other Lean files of its folder, in name order, so
        # two contributions rarely edit the same line of this shared file.
        folder = path.rpartition("/")[0]
        siblings = [i for i, row in enumerate(rows) if i and row.split("\t")[0].endswith(".lean")
                    and row.split("\t")[0].rpartition("/")[0] == folder]
        position = next((i for i in siblings if rows[i].split("\t")[0] > path),
                        (siblings[-1] + 1) if siblings else len(rows) - (rows[-1] == ""))
        rows.insert(position, new)
        tsv_path.write_text("\n".join(rows), encoding="utf-8", newline="\n")

    out(f"Registered {path}: {len(names)} public theorems, build target {module}, index entry "
        f"`{key}`, route {' '.join(args.route)}.")
    out("Run it again after you add or rename a theorem. Then: python code/contribute.py check")
    if args.route == ["METADATA"]:
        out("Route METADATA marks the file as supporting no model-to-physical claim yet. If it "
            "supports a bridge listed in formalization/PHYSICAL_BRIDGES.md, pass --route ID.")
    return 0


# ------------------------------------------------------------------ main ----

def main(argv: list[str] | None = None) -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    commands = parser.add_subparsers(dest="command", required=True)
    nxt = commands.add_parser("next", help="open obligations that are ready and unclaimed")
    nxt.add_argument("--all", action="store_true", help="also show obligations claimed by an open pull request")
    nxt.add_argument("--offline", action="store_true", help="do not ask GitHub which are claimed")
    nxt.add_argument("--json", action="store_true")
    show = commands.add_parser("show", help="one obligation in full")
    show.add_argument("id")
    start = commands.add_parser("start", help="create the packet folder for an obligation")
    start.add_argument("id")
    start.add_argument("slug")
    chk = commands.add_parser("check", help="run the contribution checks CI runs")
    chk.add_argument("--base", help="branch or commit to compare against (default: upstream/main, origin/main)")
    chk.add_argument("--pr-title", help=argparse.SUPPRESS)
    chk.add_argument("--no-run", action="store_true", help="do not execute the packet's check scripts")
    lean = commands.add_parser("lean-add", help="register a Lean file in the build and the theorem index")
    lean.add_argument("file")
    lean.add_argument("--packet", required=True)
    lean.add_argument("--route", nargs="+", default=["METADATA"])
    tgt = commands.add_parser("targets", help="regenerate OPEN_TARGETS.md from ledger.json")
    tgt.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    return {"next": cmd_next, "show": cmd_show, "start": cmd_start, "check": cmd_check,
            "lean-add": cmd_lean_add, "targets": cmd_targets}[args.command](args, root)


if __name__ == "__main__":
    sys.exit(main())
