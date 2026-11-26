# Contributions

Work contributed through the process in [AGENTS.md](../AGENTS.md) lands here, one folder per
pull request:

```
contributions/
  telescope_degree_count_20261126/
    NOTE.md           the claim, the argument, and what it does not establish
    check_counts.py   optional: a script that re-derives any computation, exits 0
```

`NOTE.md` starts from [NOTE_TEMPLATE.md](./NOTE_TEMPLATE.md); `python code/contribute.py start ID slug`
creates the folder with the ledger statement filled in.

A folder here is a reviewed submission, not a change of status. The ledger records what is
proved. The maintainer updates it, and the indexes that mirror it, after reading the
contribution. Until then the ledger row keeps the status it had.

Lean files are the one exception to "everything in your folder": they are compiled from
`formalization/weighted/` or the repository root, and `python code/contribute.py lean-add`
registers them.
