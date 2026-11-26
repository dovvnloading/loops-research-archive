// Which open obligations can be worked on today, and how much rests on each.
// Mirrors code/contribute.py; tests/targets.test.ts holds the two together.

export interface LedgerRow {
  id: string;
  status: string;
  statement: string;
  deps: string[];
  hyp: string;
}

export interface Target {
  id: string;
  statement: string;
  downstream: number;
}

export const AGENT_BRIEFING =
  'https://raw.githubusercontent.com/dovvnloading/loops-research-archive/main/AGENTS.md';
export const AGENT_LINE = `Read ${AGENT_BRIEFING} and follow it.`;

function prerequisites(row: LedgerRow): string[] {
  const hypotheses =
    !row.hyp || row.hyp === 'none'
      ? []
      : row.hyp.split(',').map((part) => part.replace(/\s+/g, ''));
  return [...new Set([...row.deps, ...hypotheses])];
}

export function openTargets(rows: LedgerRow[]): { open: number; ready: Target[] } {
  const status = new Map(rows.map((row) => [row.id, row.status]));
  const dependants = new Map<string, string[]>();
  for (const row of rows)
    for (const item of prerequisites(row))
      dependants.set(item, [...(dependants.get(item) ?? []), row.id]);
  const downstream = (id: string) => {
    const seen = new Set<string>();
    const pending = [id];
    while (pending.length)
      for (const next of dependants.get(pending.pop()!) ?? [])
        if (!seen.has(next)) {
          seen.add(next);
          pending.push(next);
        }
    return seen.size;
  };
  const open = rows.filter((row) => row.status === 'open');
  const ready = open
    .filter((row) => prerequisites(row).every((item) => status.get(item) !== 'open'))
    .map((row) => ({ id: row.id, statement: row.statement, downstream: downstream(row.id) }))
    .sort((a, b) => b.downstream - a.downstream || (a.id < b.id ? -1 : 1));
  return { open: open.length, ready };
}
