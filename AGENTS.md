# Briefing for AI agents

Someone pointed you at this repository because they want you to help with it. This file is the
whole briefing. You do not need further instructions from them, and they may not be a
mathematician or a programmer, so do not ask them to choose the mathematics.

**The project.** An open, source-linked research program toward the Mandelbrot local connectivity
conjecture (MLC). MLC is open and nothing here proves it. The program reduces MLC to a list of
named obligations kept in [`ledger.json`](./ledger.json): 465 rows, each `imported`, `proved` or
`open`, each with its prerequisites. The work is to close open rows, or to show honestly why one
cannot be closed as stated.

**Your job.** Take one open obligation nobody else is working on, make real progress on it, and
deliver it as a pull request that passes the checks. One script carries the whole process.

## The process

You need `git`, Python 3.11 or newer, and the GitHub CLI (`gh`) signed in. Nothing to install
from this repository for a written or computational contribution.

```sh
git clone https://github.com/dovvnloading/loops-research-archive
cd loops-research-archive

python code/contribute.py next                 # 1. open obligations that are ready and unclaimed
python code/contribute.py show ID              # 2. one of them in full: statement, prerequisites, where it is stated
python code/contribute.py start ID short_slug  # 3. creates contributions/short_slug_YYYYMMDD/NOTE.md
python code/contribute.py check                # 4. the same checks CI runs; repeat until RESULT: PASS
python code/contribute.py pr-body              # 5. NOTE.md as the pull request description, then hand over
```

1. **Choose.** `next` ranks the ready obligations by how many others depend on them and hides
   the ones an open pull request already claims. Pick one yourself. Read where it is stated
   (the path `show` prints), the prerequisites, and every file `show` lists under "Earlier
   work" before deciding it is tractable; build on what is there instead of repeating it. If the best
   you can do on any of them is restate it, pick a smaller one; a blocked obligation listed in
   [`OPEN_TARGETS.md`](./OPEN_TARGETS.md) is also fair game for a partial result.
2. **Claim before working.** `start` prints the exact `git` and `gh` commands. Open the pull
   request as a **draft** straight away, titled `[LEDGER_ID] what you intend to show`. The open
   pull request is the claim; that is how two agents avoid doing the same work. Never start on
   an obligation `next` shows as claimed.
3. **Work in your folder.** Everything goes in `contributions/<your folder>/`: `NOTE.md` (the
   argument) and any `check_*.py` or `verify_*.py` that certifies a computation. Commit and
   push as you go, so the work lives in the pull request and not only in your session.
   While the pull request is a draft, an unfinished `NOTE.md` is allowed
   (`python code/contribute.py check --draft` locally).
4. **Check, then hand over.** Run `check` until it prints `RESULT: PASS` and push. Then
   `pr-body` writes the pull request description from your finished `NOTE.md` and prints the two
   closing commands (`gh pr edit --body-file ...` and `gh pr ready`). Run them. Then tell the
   person, in two or three plain sentences, what you worked on, what you showed, what stays
   open, and the pull request link.

## What counts as a contribution

Set `result:` in `NOTE.md` to the one that is true:

| `result` | Meaning |
|---|---|
| `closes` | A complete proof of the obligation exactly as the ledger states it |
| `partial` | A proved subcase, reduction or lemma toward it, with the remaining gap named |
| `counterexample` | The statement as written fails; the construction is given and checked |
| `obstruction` | A named route to the obligation cannot work, with proof |
| `correction` | An error in a source, citation, statement or dependency |
| `evidence` | A reproducible computation. Evidence only, never a proof |

Strength of evidence, strongest first: a Lean theorem compiled in CI; an exact finite certificate
with a script that re-derives it; a complete written proof with every imported theorem cited to
author, paper and theorem number. Floating-point numerics and pictures are `evidence`.

A small result that is fully proved is worth more than a large one that is not. A negative
result is a result: if you find the statement false or a route dead, prove that and submit it.
If you made no real progress, say so to the person and close your draft so the obligation is
free again; do not submit a restatement, a survey, or a plan.

## Rules the checks enforce

- **Never claim MLC, or any of H1 to H4, is proved** unless you have proved it. A finite,
  one-scale, stationary or model result keeps that qualifier everywhere, including the title.
- **Do not edit the status record**: `ledger.json`, `ledger.js`, `ResearchLedger.lean`,
  `README.md`, `RESEARCH_MAP.md`, `OPEN_TARGETS.md`, `CONTRIBUTING.md`, this file, or anything
  under `.github/`. If a row's status should change, say so under `## Boundary` in `NOTE.md`.
  The maintainer records status after review.
- **One obligation per pull request**, and its ID in the title.
- **`## Boundary` is mandatory**: state what your work does not establish. A theorem about a
  model says nothing about the actual dynamical object until the identification is proved; if
  you did not prove it, the result is `partial` and the identification is named as open.
- **No new workflow files.** CI finds your `check_*.py` and `verify_*.py` and runs them from
  the repository root with the libraries in [`requirements.txt`](./requirements.txt). Each must
  exit 0 in under 15 minutes and print what it verified.
- **Disclose yourself**: `ai:` names the system and model; `human_review:` says what a person
  checked, or `none`.
- Contributions are released under [CC0](./LICENSE). Do not paste copyrighted text; cite it.

## Lean

Lean is the strongest form a result can take here, and the build is strict.

- Toolchain: the version in [`lean-toolchain`](./lean-toolchain). Files in the repository root
  use core Lean only. Files in `formalization/weighted/` may import Mathlib.
- Put your file in one of those two places, not in your packet folder, then register it:

  ```sh
  python code/contribute.py lean-add formalization/weighted/YourModule.lean --packet contributions/<your folder>
  ```

  That adds the build target, lists every public theorem in the theorem index, and adds the
  source row. Run it again whenever you add or rename a theorem. CI rejects an unregistered
  Lean file or an unlisted theorem.
- Forbidden anywhere in Lean source: `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
  `implemented_by`. The compiled proof may depend only on `propext`, `Classical.choice` and
  `Quot.sound`; CI audits this.
- Build locally if Lean is installed: `lake build YourModule` in the root, or
  `cd formalization/weighted && lake exe cache get && lake build YourModule`. If it is not
  installed, say so in `NOTE.md`; the Lean workflows on the pull request are the judge.
- State theorems about the actual objects whenever you can. A theorem about a stand-in is
  recorded as a model result.

## If you are blocked

- **`gh` is missing or not signed in.** This is the one thing to ask the person for: have them
  run `gh auth login` once (they need a free GitHub account). Then continue.
- **You cannot push or open a pull request at all.** Finish the packet locally, run `check`,
  and give the person `NOTE.md` to submit through
  [the proof issue form](https://github.com/dovvnloading/loops-research-archive/issues/new?template=proof-or-counterexample.yml).
- **You cannot run commands** (a chat without a shell). Read
  [`OPEN_TARGETS.md`](https://raw.githubusercontent.com/dovvnloading/loops-research-archive/main/OPEN_TARGETS.md),
  check the [open pull requests](https://github.com/dovvnloading/loops-research-archive/pulls) for
  the ID you want, write `NOTE.md` following
  [the template](https://raw.githubusercontent.com/dovvnloading/loops-research-archive/main/contributions/NOTE_TEMPLATE.md),
  and have the person submit it through the same issue form.
- **CI has not started on your pull request.** A first pull request from a new account waits
  for the maintainer to approve the run. `python code/contribute.py check` gives the same
  verdict locally.
- **A check you did not cause is red.** Say which in the pull request description and carry on.

## Where things are

| Path | What it holds |
|---|---|
| [`OPEN_TARGETS.md`](./OPEN_TARGETS.md) | Every open obligation, the ready ones in full |
| [`ledger.json`](./ledger.json) | The authority: every obligation, status, prerequisites, evidence pointer |
| [`RESEARCH_MAP.md`](./RESEARCH_MAP.md) | How the papers, gates and obligations fit together |
| [`research/mlc_unified/`](./research/mlc_unified/) | Where most obligations are stated and argued |
| [`formalization/PHYSICAL_BRIDGES.md`](./formalization/PHYSICAL_BRIDGES.md) | Which model results have been tied to actual dynamical objects, and which have not |
| [`papers/README.md`](./papers/README.md) | The three companion papers |
| [`CONTRIBUTING.md`](./CONTRIBUTING.md) | The full scholarly standard this briefing condenses |
| [`contributions/`](./contributions/) | Where contributed work lands |

Fixes to the web application or the documentation are ordinary pull requests and need no
packet; see [`docs/OBSERVATORY.md`](./docs/OBSERVATORY.md).
