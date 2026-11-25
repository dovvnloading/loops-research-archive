#!/usr/bin/env python3
"""Check all archive Lean sources; optionally kernel-check and audit their axioms.

The default check is a source/registration check, not a Lean proof. After the
two Lake packages are built, --audit root/weighted checks compiled declarations
with Lean 4.32's collectAxioms; --audit standalone checks each original sidecar
and a temporary copy with the same source plus an axiom audit. Only propext,
Classical.choice and Quot.sound are accepted. No generated audit is committed.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import tomllib
from pathlib import Path

from verify_lean_frontier_sync import ROOT
from verify_physical_bridge_contracts import lean_code, source_files

WEIGHTED = Path("formalization/weighted")
STANDALONE = (
    "research/independent_audits/issue62_connector_defects_20261116/RelativeDeck.lean",
    "research/independent_audits/issue62_connector_words_20261116/RelativeWordGauge.lean",
    "research/independent_audits/real_primitive_tip_family_prime_end_identification_20261116/RealPrimitiveTipPrimeEndDiscrete.lean",
    "research/independent_audits/real_primitive_tip_family_unconditional_20261116/RealPrimitiveTipUnconditionalDiscrete.lean",
    "research/independent_audits/real_primitive_tip_family_uniform_20261116/RealPrimitiveTipDiscrete.lean",
)
FORBIDDEN = re.compile(
    r"(?<![\w'])"
    r"(?:sorry|admit|sorryAx|axiom|native_decide|unsafe|implemented_by|"
    r"Lean\.ofReduceBool|Lean\.ofReduceNat)"
    r"(?![\w'])"
)


def check_trust(path: str, source: str) -> None:
    code = lean_code(source)
    problems = [
        f"{path}:{code.count(chr(10), 0, match.start()) + 1}: {match[0]}"
        for match in FORBIDDEN.finditer(code)
    ]
    if problems:
        raise ValueError("Prohibited proof/trust escape in source:\n" + "\n".join(problems))


def check_package(label: str, sources: set[str], config: dict) -> None:
    entries = config.get("lean_lib", [])
    names = [entry["name"] for entry in entries]
    defaults = config.get("defaultTargets", [])
    if len(names) != len(set(names)) or len(defaults) != len(set(defaults)):
        raise ValueError(f"{label}: duplicate library or default target")
    missing_declared = sources - set(names)
    missing_defaults = sources - set(defaults)
    if missing_declared or missing_defaults:
        raise ValueError(
            f"{label}: unregistered sources {sorted(missing_declared)}; "
            f"omitted default targets {sorted(missing_defaults)}"
        )
    for entry in entries:
        if entry["name"] in sources and entry.get("srcDir", ".") not in (".", ""):
            raise ValueError(f"{label}: local module {entry['name']} has a different srcDir")


def classify(files: set[str]) -> tuple[list[str], list[str]]:
    root = {p for p in files if Path(p).parent == Path(".")}
    weighted = {p for p in files if Path(p).parent == WEIGHTED}
    remaining = files - root - weighted
    missing = set(STANDALONE) - remaining
    unassigned = remaining - set(STANDALONE)
    if missing or unassigned:
        raise ValueError(
            f"Standalone registration mismatch: missing {sorted(missing)}; "
            f"unassigned Lean sources {sorted(unassigned)}"
        )
    return sorted(Path(p).stem for p in root), sorted(Path(p).stem for p in weighted)


def inventory() -> tuple[list[str], list[str]]:
    files = {p for p in source_files() if p.endswith(".lean")}
    root, weighted = classify(files)
    for path in sorted(files):
        check_trust(path, (ROOT / path).read_text(encoding="utf-8"))
    for label, directory, modules in (
        ("root", ROOT, root), ("weighted", ROOT / WEIGHTED, weighted)
    ):
        config = tomllib.loads((directory / "lakefile.toml").read_text(encoding="utf-8"))
        check_package(label, set(modules), config)
    toolchains = [(ROOT / path / "lean-toolchain").read_text().strip()
                  for path in (Path("."), WEIGHTED)]
    if toolchains[0] != toolchains[1]:
        raise ValueError(f"Package toolchains differ: {toolchains}")
    print(
        f"Lean source coverage: {len(files)} files = {len(root)} root + "
        f"{len(weighted)} weighted + {len(STANDALONE)} standalone; "
        "all registered, no prohibited source tokens."
    )
    return root, weighted


def audit_command(modules: list[str] | None, label: str) -> str:
    """Generate an elaborator command over actual kernel-environment constants.

    Module provenance, not declaration namespace spelling, selects the audit.
    For an appended standalone audit, none selects all current-module constants.
    Every selected module must contain at least one theorem and one declaration.
    """
    if modules is None:
        module_names = "#[Lean.Name.anonymous]"
        selection = "env.getModuleIdxFor? declName == none"
    else:
        if not modules or any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", m) for m in modules):
            raise ValueError("Expected nonempty simple Lake module names")
        module_names = "#[" + ", ".join("`" + m for m in modules) + "]"
        selection = """match env.getModuleIdxFor? declName with
        | some idx => moduleNames[idx.toNat]? == some target
        | none => false"""
    if not re.fullmatch(r"[A-Za-z_0-9./-]+", label):
        raise ValueError("Invalid audit label")
    return f'''\n\n-- Generated audit: source proof statements above remain unchanged.
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean in
run_elab do
  let env ← Lean.getEnv
  let moduleNames := env.allImportedModuleNames
  let targets : Array Lean.Name := {module_names}
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut total : Nat := 0
  for target in targets do
    let declarations : Array Lean.Name := env.constants.fold (init := #[]) fun acc declName _ =>
      let selected := {selection}
      if selected then acc.push declName else acc
    if declarations.isEmpty then
      throwError "AXIOM_AUDIT {label}: zero declarations for {{target}}"
    let mut theorems : Nat := 0
    for declName in declarations do
      match env.find? declName with
      | some (.thmInfo _) => theorems := theorems + 1
      | _ => pure ()
      let axioms ← Lean.collectAxioms declName
      let bad := axioms.filter fun ax => !allowed.contains ax
      unless bad.isEmpty do
        throwError "AXIOM_AUDIT {{declName}} has disallowed axioms {{bad.toList}}"
    if theorems == 0 then
      throwError "AXIOM_AUDIT {label}: zero theorems for {{target}}"
    total := total + declarations.size
    logInfo m!"AXIOM_AUDIT {label} {{target}}: {{declarations.size}} declarations, {{theorems}} theorems; allowed axioms only"
  logInfo m!"AXIOM_AUDIT_PASS {label}: {{targets.size}} modules, {{total}} declarations"
'''


def invoke_lean(directory: Path, source: Path) -> None:
    subprocess.run(["lake", "env", "lean", str(source)], cwd=directory, check=True)


def audit_package(label: str, modules: list[str]) -> None:
    directory = ROOT if label == "root" else ROOT / WEIGHTED
    generated = directory / ".lake" / "verification" / "AxiomAudit.lean"
    generated.parent.mkdir(parents=True, exist_ok=True)
    generated.write_text(
        "import Lean\n" + "".join(f"import {m}\n" for m in modules)
        + audit_command(modules, label), encoding="utf-8"
    )
    print(f"Auditing all {len(modules)} {label} modules using Lean.collectAxioms.", flush=True)
    invoke_lean(directory, generated)


def audit_standalone() -> None:
    directory = ROOT / ".lake" / "verification"
    directory.mkdir(parents=True, exist_ok=True)
    for i, path in enumerate(STANDALONE):
        print(f"Kernel check and axiom audit: {path}", flush=True)
        invoke_lean(ROOT, ROOT / path)
        generated = directory / f"StandaloneAudit{i}.lean"
        generated.write_text(
            "import Lean\n" + (ROOT / path).read_text(encoding="utf-8")
            + audit_command(None, Path(path).stem), encoding="utf-8"
        )
        invoke_lean(ROOT, generated)


def self_test() -> None:
    """Adversarial checks for omission/trust guards; no Lean success is inferred."""
    check_trust("comments", '''/- sorry /- axiom fake : False -/ native_decide -/
-- unsafe admit
def note := "axiom sorry \\\"native_decide\\\""
theorem honest : True := True.intro
''')
    cases = [
        lambda: check_trust("hole", "theorem bad : False := by sorry"),
        lambda: check_trust("axiom", "axiom invented : False"),
        lambda: check_trust("native", "theorem native : 1 = 1 := by native_decide"),
        lambda: check_trust("native_axiom", "#check Lean.ofReduceBool"),
        lambda: check_trust("comment", "/- unclosed"),
        lambda: classify(set(STANDALONE) | {"unregistered/Orphan.lean"}),
        lambda: classify(set(STANDALONE[1:])),
        lambda: check_package("test", {"A"}, {"lean_lib": [], "defaultTargets": ["A"]}),
        lambda: check_package("test", {"A"}, {"lean_lib": [{"name": "A"}], "defaultTargets": []}),
        lambda: check_package("test", {"A"}, {"lean_lib": [{"name": "A", "srcDir": "elsewhere"}], "defaultTargets": ["A"]}),
    ]
    for case in cases:
        try:
            case()
        except ValueError:
            continue
        raise AssertionError("An invalid source/coverage fixture was accepted")
    check_package("good", {"A"}, {"lean_lib": [{"name": "A"}], "defaultTargets": ["A"]})
    assert "zero theorems" in audit_command(["A"], "test")
    assert "zero declarations" in audit_command(None, "test")
    print(f"Lean coverage guard: {len(cases)} adversarial regressions passed.")


def test_kernel_audit() -> None:
    """Require the real Lean audit to reject bad dependencies, not syntax errors."""
    directory = ROOT / ".lake" / "verification"
    directory.mkdir(parents=True, exist_ok=True)
    fixtures = (
        ("clean", "theorem clean : True := True.intro\n", None),
        ("custom", "axiom invented : False\ntheorem bad : False := invented\n",
         "has disallowed axioms"),
        ("native", "theorem native : (1 : Nat) = 1 := by native_decide\n",
         "has disallowed axioms"),
        ("empty", "", "zero "),
    )
    for name, source, expected in fixtures:
        path = directory / f"AuditRegression_{name}.lean"
        path.write_text("import Lean\n" + source + audit_command(None, name), encoding="utf-8")
        result = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        if expected is None:
            if result.returncode or "AXIOM_AUDIT_PASS clean" not in result.stdout:
                raise ValueError(f"Clean kernel audit fixture failed:\n{result.stdout}")
        elif result.returncode == 0 or expected not in result.stdout:
            raise ValueError(f"Kernel audit did not reject {name} for the expected reason:\n{result.stdout}")
        print(f"Kernel axiom-audit regression {name}: passed", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit", choices=("root", "weighted", "standalone"))
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--test-kernel-audit", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if args.test_kernel_audit:
        test_kernel_audit()
        return
    root, weighted = inventory()
    if args.audit == "standalone":
        audit_standalone()
    elif args.audit:
        audit_package(args.audit, root if args.audit == "root" else weighted)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error))
