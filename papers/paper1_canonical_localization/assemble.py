"""Assemble main.tex from skeleton.tex + extracted cluster files.

- Replaces %%INSERT <cluster-letter>:<name> with the corresponding extracted file.
- Applies cross-cluster label unification.
- Reports duplicate labels and unresolved insertions.
"""
import os
import re
import sys

BASE = os.path.dirname(os.path.abspath(__file__))
EX = os.path.join(BASE, "extracted")

CLUSTER_DIRS = {
    "A": "A_counterexamples",
    "B": "B_criteria",
    "C": "C_forced_collision",
    "D": "D_resolution",
    "E": "E_basechange_tile",
    "F": "F_kahn_source",
    "G": "G_manuscript_ledger",
}

# label unification applied to specific clusters' content
LABEL_FIXES = {
    "E": [
        ("thm:canonical-sheet-resolution", "thm:sheet-resolution"),
        ("cor:infinite-sheet-defect", "cor:infinite-defect"),
    ],
}


MACRO_DEFS = {}
MACRO_CONFLICTS = []


def sanitize(txt, origin):
    out_lines = []
    for line in txt.splitlines():
        stripped = line.strip()
        # drop theorem-environment (re)definitions: supplied by the preamble
        if stripped.startswith("\\newtheorem") or stripped.startswith("\\theoremstyle"):
            continue
        # body-safe operators
        line = re.sub(
            r"\\DeclareMathOperator\*?\{(\\[A-Za-z]+)\}\{([^}]*)\}",
            r"\\providecommand{\1}{\\operatorname{\2}}",
            line,
        )
        # macro conflict detection, then newcommand -> providecommand
        for m in re.finditer(r"\\newcommand\{(\\[A-Za-z]+)\}(\[[0-9]+\])?\{(.*)\}\s*(%.*)?$", line):
            name_, body = m.group(1), m.group(3)
            if name_ in MACRO_DEFS and MACRO_DEFS[name_][0] != body:
                MACRO_CONFLICTS.append((name_, MACRO_DEFS[name_][1], origin,
                                        MACRO_DEFS[name_][0][:60], body[:60]))
            else:
                MACRO_DEFS.setdefault(name_, (body, origin))
        line = line.replace("\\newcommand{", "\\providecommand{")
        out_lines.append(line)
    return "\n".join(out_lines)


ENV_ERRORS = []


def check_envs(txt, origin):
    stack = []
    for m in re.finditer(r"\\(begin|end)\{([A-Za-z*]+)\}", txt):
        kind, env = m.group(1), m.group(2)
        if kind == "begin":
            stack.append(env)
        else:
            if not stack or stack[-1] != env:
                ENV_ERRORS.append(f"{origin}: \\end{{{env}}} closes {stack[-1] if stack else 'nothing'}")
                if stack:
                    stack.pop()
            else:
                stack.pop()
    if stack:
        ENV_ERRORS.append(f"{origin}: unclosed {stack}")


def load(cluster, name):
    d = os.path.join(EX, CLUSTER_DIRS[cluster])
    path = os.path.join(d, name + ".tex")
    if not os.path.exists(path):
        return None
    txt = open(path, encoding="utf-8").read()
    for old, new in LABEL_FIXES.get(cluster, []):
        txt = txt.replace(old, new)
    return sanitize(txt, f"{cluster}:{name}")


def main():
    skel = open(os.path.join(BASE, "skeleton.tex"), encoding="utf-8").read()
    missing = []

    def sub(m):
        cluster, name = m.group(1), m.group(2)
        txt = load(cluster, name)
        if txt is None or not txt.strip():
            missing.append(f"{cluster}:{name}")
            return f"% [MISSING INSERT {cluster}:{name}]"
        return f"% ---- begin {cluster}:{name} ----\n{txt}\n% ---- end {cluster}:{name} ----"

    out = re.sub(r"%%INSERT ([A-G]):([A-Za-z_0-9]+)", sub, skel)
    open(os.path.join(BASE, "main.tex"), "w", encoding="utf-8").write(out)

    # label/ref audit also covers \input-ed files (figures, new math files);
    # main.tex itself keeps the \input lines and tectonic resolves them.
    scan = out
    for name in re.findall(r"\\input\{([^}]*)\}", out):
        ipath = os.path.join(BASE, name + ("" if name.endswith(".tex") else ".tex"))
        if os.path.exists(ipath):
            scan += "\n" + open(ipath, encoding="utf-8").read()

    labels = re.findall(r"\\label\{([^}]*)\}", scan)
    dupes = sorted({l for l in labels if labels.count(l) > 1})
    refs = set(re.findall(r"\\ref\{([^}]*)\}", scan))
    unresolved = sorted(r for r in refs if r not in set(labels) and not r.startswith("fig:"))
    print("bytes:", len(out))
    print("missing inserts:", missing or "none")
    print("duplicate labels:", dupes or "none")
    print("unresolved refs:", unresolved or "none")
    if MACRO_CONFLICTS:
        print("MACRO CONFLICTS (same name, different body — adjudicate):")
        for name_, o1, o2, b1, b2 in MACRO_CONFLICTS:
            print(f"  {name_}: {o1} defines {b1!r} vs {o2} defines {b2!r}")
    else:
        print("macro conflicts: none")


if __name__ == "__main__":
    main()
