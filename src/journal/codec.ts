import { validateState } from '../lib/session.ts';
import { validateExactView } from '../precision/coordinates.ts';
import type { JournalArchive, JournalEntry, JournalPayload } from './types';

export const MAX_IMPORT_BYTES = 24 * 1024 * 1024;
export const MAX_IMPORT_ENTRIES = 1000;
export const MAX_THUMBNAIL_BYTES = 2 * 1024 * 1024;
const ID = /^[a-zA-Z0-9_-]{1,120}$/;
const ownObject = (value: unknown): value is Record<string, unknown> =>
  !!value && typeof value === 'object' && !Array.isArray(value);

function text(value: unknown, name: string, max: number, optional = false): string {
  if (optional && (value === undefined || value === null)) return '';
  if (typeof value !== 'string' || value.length > max)
    throw new Error(`${name} must be text with at most ${max.toLocaleString()} characters.`);
  return value;
}

function assertJSON(value: unknown, depth = 0, budget = { count: 0 }): void {
  if (depth > 30 || ++budget.count > 100_000)
    throw new Error('The experiment data is too deeply nested or too large.');
  if (value === null || typeof value === 'boolean' || typeof value === 'string') return;
  if (typeof value === 'number' && Number.isFinite(value)) return;
  if (Array.isArray(value)) {
    for (const item of value) assertJSON(item, depth + 1, budget);
    return;
  }
  if (ownObject(value)) {
    for (const [key, item] of Object.entries(value)) {
      if (key === '__proto__' || key === 'prototype' || key === 'constructor')
        throw new Error('The experiment contains an unsupported object key.');
      assertJSON(item, depth + 1, budget);
    }
    return;
  }
  throw new Error('Experiment data must contain finite JSON values.');
}

/** Validate every decimal without a lossy round trip through a JS number. */
export function validateJournalPayload(value: unknown): JournalPayload {
  if (!ownObject(value) || !ownObject(value.engine) || !ownObject(value.exact))
    throw new Error('A snapshot needs both engine settings and an exact view.');
  if (
    !['mandelbulb', 'mandelbox', 'quaternion', 'mandelbrot', 'julia', 'landscape'].includes(
      String(value.engine.scene),
    )
  )
    throw new Error('This snapshot uses an unsupported fractal family.');
  const checkedView = validateExactView(value.exact);
  // Validation may canonicalize decimal formatting. Preserve the user's original
  // spelling in the journal, including scientific notation and trailing digits.
  const exact = value.exact as unknown as JournalPayload['exact'];
  const result: JournalPayload = {
    engine: validateState(value.engine),
    exact: {
      ...checkedView,
      center: { ...exact.center },
      julia: { ...exact.julia },
      span: exact.span,
    },
  };
  if (value.experiment !== undefined) {
    assertJSON(value.experiment);
    const serialized = JSON.stringify(value.experiment);
    if (serialized.length > 4_000_000) throw new Error('An experiment must be smaller than 4 MB.');
    result.experiment = JSON.parse(serialized);
  }
  if (value.sourceRevision !== undefined) {
    const revision = text(value.sourceRevision, 'Source revision', 100);
    if (!/^[a-zA-Z0-9._/-]*$/.test(revision))
      throw new Error('The source revision contains unsupported characters.');
    result.sourceRevision = revision;
  }
  return result;
}

export function normalizeTags(value: unknown): string[] {
  if (value === undefined) return [];
  if (
    !Array.isArray(value) ||
    value.length > 20 ||
    value.some((tag) => typeof tag !== 'string' || tag.length > 48)
  )
    throw new Error('Use at most 20 tags, each with up to 48 characters.');
  return [
    ...new Set((value as string[]).map((tag) => tag.trim().toLocaleLowerCase()).filter(Boolean)),
  ];
}

export function validateJournalEntry(value: unknown): JournalEntry {
  if (!ownObject(value) || value.version !== 2)
    throw new Error('This journal entry uses an unsupported version.');
  if (typeof value.id !== 'string' || !ID.test(value.id))
    throw new Error('A journal entry has an invalid identifier.');
  if (
    value.parentId !== null &&
    value.parentId !== undefined &&
    (typeof value.parentId !== 'string' || !ID.test(value.parentId))
  )
    throw new Error('A journal entry has an invalid parent identifier.');
  if (value.parentId === value.id) throw new Error('A journal entry cannot be its own parent.');
  const title = text(value.title, 'Title', 160).trim();
  if (!title) throw new Error('Give this observation a title.');
  const createdAt = text(value.createdAt, 'Creation date', 40);
  const updatedAt = text(value.updatedAt, 'Update date', 40);
  if (!Number.isFinite(Date.parse(createdAt)) || !Number.isFinite(Date.parse(updatedAt)))
    throw new Error('A journal entry has an invalid date.');
  const entry: JournalEntry = {
    version: 2,
    id: value.id,
    title,
    notes: text(value.notes, 'Notes', 40_000, true),
    tags: normalizeTags(value.tags),
    parentId: typeof value.parentId === 'string' ? value.parentId : null,
    createdAt,
    updatedAt,
    payload: validateJournalPayload(value.payload),
  };
  if (value.thumbnail !== undefined && value.thumbnail !== '') {
    if (
      typeof value.thumbnail !== 'string' ||
      value.thumbnail.length > MAX_THUMBNAIL_BYTES ||
      !/^data:image\/(?:png|jpeg|webp);base64,[A-Za-z0-9+/]+=*$/.test(value.thumbnail)
    )
      throw new Error('A thumbnail must be a PNG, JPEG, or WebP image smaller than 2 MB.');
    entry.thumbnail = value.thumbnail;
  }
  return entry;
}

export function validateParentGraph(entries: JournalEntry[]): void {
  const parents = new Map(entries.map((entry) => [entry.id, entry.parentId]));
  const complete = new Set<string>();
  for (const entry of entries) {
    const visited = new Set<string>();
    let current: string | null | undefined = entry.id;
    while (current && parents.has(current) && !complete.has(current)) {
      if (visited.has(current))
        throw new Error('The journal contains a cycle in its branching history.');
      visited.add(current);
      current = parents.get(current);
    }
    for (const id of visited) complete.add(id);
  }
}

export function parseJournalArchive(raw: string): JournalArchive {
  if (raw.length > MAX_IMPORT_BYTES) throw new Error('Choose a journal export smaller than 24 MB.');
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw);
  } catch {
    throw new Error('This file is not valid JSON.');
  }
  if (
    !ownObject(parsed) ||
    parsed.format !== 'loops-journal' ||
    parsed.version !== 2 ||
    !Array.isArray(parsed.entries)
  )
    throw new Error('Choose a LOOPS journal export (version 2).');
  if (parsed.entries.length > MAX_IMPORT_ENTRIES)
    throw new Error('Import at most 1,000 observations at a time.');
  const entries = parsed.entries.map(validateJournalEntry);
  if (new Set(entries.map((entry) => entry.id)).size !== entries.length)
    throw new Error('The import contains duplicate observation identifiers.');
  validateParentGraph(entries);
  return {
    format: 'loops-journal',
    version: 2,
    exportedAt:
      typeof parsed.exportedAt === 'string' ? parsed.exportedAt : new Date().toISOString(),
    entries,
  };
}

export function serializeJournal(entries: JournalEntry[]): string {
  return JSON.stringify(
    {
      format: 'loops-journal',
      version: 2,
      exportedAt: new Date().toISOString(),
      entries,
    } satisfies JournalArchive,
    null,
    2,
  );
}

/** Conflicts become new branches, so importing cannot overwrite an observation. */
export function mergeImportedEntries(
  existing: JournalEntry[],
  imported: JournalEntry[],
  newId: () => string,
): { entries: JournalEntry[]; added: number; skipped: number } {
  const original = new Map(existing.map((entry) => [entry.id, entry]));
  const used = new Set(original.keys());
  const mapping = new Map<string, string>();
  const unchanged = new Set<string>();
  const uniqueId = () => {
    let id = newId();
    let tries = 0;
    while (used.has(id)) {
      if (++tries > 100) throw new Error('Could not assign a unique observation identifier.');
      id = newId();
    }
    used.add(id);
    return id;
  };
  for (const entry of imported) {
    const match = original.get(entry.id);
    if (match && JSON.stringify(match) === JSON.stringify(entry)) {
      mapping.set(entry.id, entry.id);
      unchanged.add(entry.id);
      continue;
    }
    const id = used.has(entry.id) ? uniqueId() : entry.id;
    used.add(id);
    mapping.set(entry.id, id);
  }
  // A child with identical content still needs a new identity if its imported
  // parent was remapped. Repeat so a whole descendant chain follows that parent.
  let changed = true;
  while (changed) {
    changed = false;
    for (const entry of imported)
      if (
        unchanged.has(entry.id) &&
        entry.parentId &&
        mapping.has(entry.parentId) &&
        mapping.get(entry.parentId) !== entry.parentId
      ) {
        unchanged.delete(entry.id);
        mapping.set(entry.id, uniqueId());
        changed = true;
      }
  }
  const remapped = imported
    .filter((entry) => !unchanged.has(entry.id))
    .map((entry) => ({
      ...entry,
      id: mapping.get(entry.id)!,
      parentId: entry.parentId ? (mapping.get(entry.parentId) ?? entry.parentId) : null,
    }));
  const entries = [...existing, ...remapped];
  validateParentGraph(entries);
  return { entries, added: remapped.length, skipped: unchanged.size };
}

function base64Encode(textValue: string): string {
  const bytes = new TextEncoder().encode(textValue);
  let binary = '';
  for (const byte of bytes) binary += String.fromCharCode(byte);
  return btoa(binary).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}

function base64Decode(value: string): string {
  if (!/^[A-Za-z0-9_-]+$/.test(value)) throw new Error('The snapshot link is malformed.');
  const binary = atob(value.replace(/-/g, '+').replace(/_/g, '/'));
  return new TextDecoder('utf-8', { fatal: true }).decode(
    Uint8Array.from(binary, (c) => c.charCodeAt(0)),
  );
}

/** Share only reproducible view settings; private notes and experiment data stay local. */
export function encodeSnapshot(payload: JournalPayload): string {
  const checked = validateJournalPayload(payload);
  return base64Encode(
    JSON.stringify({
      v: 2,
      engine: checked.engine,
      exact: checked.exact,
      sourceRevision: checked.sourceRevision,
    }),
  );
}

export function decodeSnapshot(value: string): JournalPayload {
  if (value.length > 40_000) throw new Error('This snapshot link is too long.');
  const decoded: unknown = JSON.parse(base64Decode(value));
  if (!ownObject(decoded) || decoded.v !== 2)
    throw new Error('This snapshot link uses an unsupported version.');
  return validateJournalPayload(decoded);
}

export function createSnapshotURL(payload: JournalPayload, base = location.href): string {
  const url = new URL(base);
  url.search = '';
  url.hash = '';
  url.searchParams.set('s', encodeSnapshot(payload));
  return url.toString();
}

export function readSharedSnapshot(base = location.href): JournalPayload | null {
  const value = new URL(base).searchParams.get('s');
  return value ? decodeSnapshot(value) : null;
}

export function journalCSV(entries: JournalEntry[]): string {
  // Imported notes and labels are untrusted spreadsheet text. CSV quoting alone
  // does not prevent formula evaluation. Keep validated numeric columns intact.
  const cell = (value: unknown, index: number) => {
    const raw = String(value ?? '');
    const numericColumn = index >= 5 && index <= 8;
    const formulaLike = /^[\s\uFEFF]*[=+\-@\uFF1D\uFF0B\uFF0D\uFF20]|^[\t\r\n]/.test(raw);
    const safe = !numericColumn && formulaLike ? "'" + raw : raw;
    return `"${safe.replace(/"/g, '""')}"`;
  };
  const rows = entries.map((entry) => [
    entry.id,
    entry.parentId,
    entry.title,
    entry.createdAt,
    entry.payload.engine.scene,
    entry.payload.exact.center.re,
    entry.payload.exact.center.im,
    entry.payload.exact.span,
    entry.payload.exact.iterations,
    entry.payload.exact.palette,
    entry.tags.join('; '),
    entry.notes,
  ]);
  return [
    [
      'id',
      'parent_id',
      'title',
      'created_at',
      'family',
      'center_real_exact',
      'center_imaginary_exact',
      'vertical_span_exact',
      'iteration_budget',
      'palette',
      'tags',
      'notes',
    ],
    ...rows,
  ]
    .map((row) => row.map(cell).join(','))
    .join('\r\n');
}
