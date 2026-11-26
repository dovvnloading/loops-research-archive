import { useEffect, useSyncExternalStore } from 'react';
import { validateState } from '../lib/session.ts';
import {
  mergeImportedEntries,
  normalizeTags,
  parseJournalArchive,
  serializeJournal,
  validateJournalEntry,
  validateJournalPayload,
} from './codec.ts';
import type { JournalEntry, JournalState, NewJournalEntry } from './types';

const DB_NAME = 'loops-exploration-journal';
const STORE_NAME = 'observations';
const LOCAL_KEY = 'loops.journal.v2';
const LEGACY_KEY = 'loops.bookmarks.v1';
const listeners = new Set<() => void>();
let state: JournalState = { entries: [], ready: false, mode: 'loading', error: null };
let database: IDBDatabase | null = null;
let initializing: Promise<void> | null = null;
let mutation = Promise.resolve();
let channel: BroadcastChannel | null = null;

export function journalId(): string {
  return typeof crypto !== 'undefined' && typeof crypto.randomUUID === 'function'
    ? crypto.randomUUID()
    : `${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 12)}`;
}

function publish(next: Partial<JournalState>) {
  state = { ...state, ...next };
  for (const listener of listeners) listener();
}

function message(error: unknown): string {
  return error instanceof Error ? error.message : 'The browser could not save this observation.';
}

function subscribe(listener: () => void) {
  listeners.add(listener);
  return () => {
    listeners.delete(listener);
  };
}
export function getJournalState(): JournalState {
  return state;
}

function openDatabase(): Promise<IDBDatabase> {
  return new Promise((resolve, reject) => {
    if (typeof indexedDB === 'undefined') {
      reject(new Error('IndexedDB is unavailable.'));
      return;
    }
    const request = indexedDB.open(DB_NAME, 1);
    let finished = false;
    const timer = setTimeout(() => {
      finished = true;
      reject(new Error('Journal storage is blocked by another tab.'));
    }, 5000);
    request.onupgradeneeded = () => {
      const db = request.result;
      if (!db.objectStoreNames.contains(STORE_NAME))
        db.createObjectStore(STORE_NAME, { keyPath: 'id' });
    };
    request.onerror = () => {
      clearTimeout(timer);
      finished = true;
      reject(request.error ?? new Error('Journal storage could not open.'));
    };
    request.onsuccess = () => {
      if (finished) {
        request.result.close();
        return;
      }
      clearTimeout(timer);
      finished = true;
      request.result.onversionchange = () => {
        request.result.close();
        database = null;
        publish({
          error: 'Another tab upgraded the journal. Reload this page before saving again.',
        });
      };
      resolve(request.result);
    };
  });
}

function readDatabase(db: IDBDatabase): Promise<unknown[]> {
  return new Promise((resolve, reject) => {
    const request = db.transaction(STORE_NAME, 'readonly').objectStore(STORE_NAME).getAll();
    request.onsuccess = () => resolve(request.result as unknown[]);
    request.onerror = () => reject(request.error ?? new Error('The journal could not be read.'));
  });
}

function writeDatabase(
  db: IDBDatabase,
  next: JournalEntry[],
  previous: JournalEntry[],
): Promise<void> {
  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORE_NAME, 'readwrite');
    const store = transaction.objectStore(STORE_NAME);
    const before = new Map(previous.map((entry) => [entry.id, entry]));
    const after = new Set(next.map((entry) => entry.id));
    for (const entry of previous) if (!after.has(entry.id)) store.delete(entry.id);
    for (const entry of next) if (before.get(entry.id) !== entry) store.put(entry);
    transaction.oncomplete = () => resolve();
    transaction.onabort = () =>
      reject(
        transaction.error ??
          new Error('Browser storage is full. Export the journal before clearing space.'),
      );
    transaction.onerror = () => {
      /* The abort event carries the completed transaction error. */
    };
  });
}

function validateStored(values: unknown[]): { entries: JournalEntry[]; skipped: number } {
  const entries: JournalEntry[] = [];
  let skipped = 0;
  for (const value of values) {
    try {
      entries.push(validateJournalEntry(value));
    } catch {
      skipped++;
    }
  }
  return { entries, skipped };
}

function listenForOtherTabs() {
  if (typeof window === 'undefined') return;
  const refresh = () => {
    void enqueue(async () => {
      try {
        const entries =
          state.mode === 'indexeddb' && database
            ? validateStored(await readDatabase(database)).entries
            : state.mode === 'local'
              ? parseJournalArchive(localStorage.getItem(LOCAL_KEY) ?? serializeJournal([])).entries
              : state.entries;
        publish({ entries: [...entries].sort((a, b) => b.createdAt.localeCompare(a.createdAt)) });
      } catch {
        /* Keep this tab's known-good observations when a peer update fails. */
      }
    });
  };
  if (typeof BroadcastChannel !== 'undefined') {
    try {
      channel = new BroadcastChannel(DB_NAME);
      channel.onmessage = (event) => {
        if (event.data === 'changed') refresh();
      };
    } catch {
      /* Storage events still work for the local fallback. */
    }
  }
  window.addEventListener('storage', (event) => {
    if (state.mode === 'local' && event.key === LOCAL_KEY) refresh();
  });
  window.addEventListener('focus', refresh);
}

function legacyBookmarks(): JournalEntry[] {
  try {
    const parsed: unknown = JSON.parse(localStorage.getItem(LEGACY_KEY) ?? '[]');
    if (!Array.isArray(parsed)) return [];
    return parsed.slice(0, 100).flatMap((value: unknown, index) => {
      if (!value || typeof value !== 'object') return [];
      const old = value as Record<string, unknown>;
      if (typeof old.name !== 'string' || !old.state) return [];
      const engine = validateState(old.state);
      const createdAt =
        typeof old.created === 'string' && Number.isFinite(Date.parse(old.created))
          ? new Date(old.created).toISOString()
          : new Date().toISOString();
      return [
        {
          version: 2 as const,
          id: `legacy-${String(old.id ?? index)
            .replace(/[^a-zA-Z0-9_-]/g, '')
            .slice(0, 70)}`,
          title: old.name.slice(0, 160) || 'Saved view',
          notes: 'Imported from a previous LOOPS bookmark.',
          tags: ['imported'],
          parentId: null,
          createdAt,
          updatedAt: createdAt,
          payload: {
            engine,
            exact: {
              family: engine.scene === 'julia' ? ('julia' as const) : ('mandelbrot' as const),
              center: { re: String(engine.center[0]), im: String(engine.center[1]) },
              span: String(engine.scale),
              julia: { re: String(engine.julia[0]), im: String(engine.julia[1]) },
              iterations: Math.max(64, engine.iterations),
              palette: engine.palette,
            },
          },
        },
      ];
    });
  } catch {
    return [];
  }
}

export function initializeJournal(): Promise<void> {
  if (initializing) return initializing;
  initializing = (async () => {
    let entries: JournalEntry[] = [];
    let warning: string | null = null;
    try {
      database = await openDatabase();
      const validated = validateStored(await readDatabase(database));
      entries = validated.entries;
      if (validated.skipped)
        warning = `${validated.skipped} unreadable observation${validated.skipped === 1 ? '' : 's'} was left untouched in browser storage.`;
      publish({ mode: 'indexeddb' });
    } catch {
      try {
        const raw = localStorage.getItem(LOCAL_KEY);
        entries = raw ? parseJournalArchive(raw).entries : [];
        const probe = `${LOCAL_KEY}.probe`;
        localStorage.setItem(probe, '1');
        localStorage.removeItem(probe);
        publish({ mode: 'local' });
        warning =
          'Using this browser’s smaller local storage. Export regularly to keep a portable backup.';
      } catch {
        publish({ mode: 'memory' });
        warning =
          'Browser storage is unavailable. Observations remain in this tab only; export before closing it.';
      }
    }
    const original = entries;
    // A successful IndexedDB migration removes the fallback copy so deletions cannot reappear.
    let fallbackMigrated = false;
    if (database) {
      try {
        const raw = localStorage.getItem(LOCAL_KEY);
        if (raw) {
          entries = mergeImportedEntries(
            entries,
            parseJournalArchive(raw).entries,
            journalId,
          ).entries;
          fallbackMigrated = true;
        }
      } catch {
        warning = 'A local backup could not be migrated. The backup remains in browser storage.';
      }
    }
    const legacy = legacyBookmarks().filter(
      (entry) => !entries.some((existing) => existing.id === entry.id),
    );
    entries = [...entries, ...legacy];
    try {
      if (database && entries !== original) await writeDatabase(database, entries, original);
      if (state.mode === 'local' && legacy.length)
        localStorage.setItem(LOCAL_KEY, serializeJournal(entries));
      if (fallbackMigrated) localStorage.removeItem(LOCAL_KEY);
      if (legacy.length && state.mode !== 'memory') localStorage.removeItem(LEGACY_KEY);
    } catch {
      warning =
        'Some imported observations could not be saved. Export a backup before closing this tab.';
    }
    publish({
      entries: entries.sort((a, b) => b.createdAt.localeCompare(a.createdAt)),
      ready: true,
      error: warning,
    });
    listenForOtherTabs();
  })();
  return initializing;
}

export function useJournal(): JournalState {
  const snapshot = useSyncExternalStore(subscribe, getJournalState, getJournalState);
  useEffect(() => {
    void initializeJournal();
  }, []);
  return snapshot;
}

async function persist(next: JournalEntry[]): Promise<void> {
  try {
    if (state.mode === 'indexeddb') {
      if (!database) throw new Error('Reload the page to reconnect journal storage.');
      await writeDatabase(database, next, state.entries);
    } else if (state.mode === 'local') {
      localStorage.setItem(LOCAL_KEY, serializeJournal(next));
    }
    publish({
      entries: [...next].sort((a, b) => b.createdAt.localeCompare(a.createdAt)),
      error:
        state.mode === 'memory'
          ? 'This tab is using temporary memory. Export your journal before closing it.'
          : null,
    });
    try {
      channel?.postMessage('changed');
    } catch {
      /* A peer notification cannot undo a completed save. */
    }
  } catch (error) {
    const reason =
      error instanceof DOMException && error.name === 'QuotaExceededError'
        ? 'Browser storage is full. Your previous observations are safe. Export a backup and free some space, then try again.'
        : message(error);
    publish({ error: reason });
    throw new Error(reason);
  }
}

function enqueue<T>(action: () => Promise<T>): Promise<T> {
  const next = mutation.then(async () => {
    await initializeJournal();
    return action();
  });
  mutation = next.then(
    () => undefined,
    () => undefined,
  );
  return next;
}

export function saveEntry(input: NewJournalEntry): Promise<JournalEntry> {
  return enqueue(async () => {
    const timestamp = new Date().toISOString();
    const entry = validateJournalEntry({
      version: 2,
      id: journalId(),
      title: input.title,
      notes: input.notes ?? '',
      tags: normalizeTags(input.tags),
      parentId: input.parentId ?? null,
      createdAt: timestamp,
      updatedAt: timestamp,
      thumbnail: input.thumbnail,
      payload: validateJournalPayload(input.payload),
    });
    await persist([...state.entries, entry]);
    return entry;
  });
}

export function updateEntry(
  id: string,
  update: { title: string; notes: string; tags: string[] },
): Promise<JournalEntry> {
  return enqueue(async () => {
    const current = state.entries.find((entry) => entry.id === id);
    if (!current) throw new Error('This observation no longer exists.');
    const next = validateJournalEntry({
      ...current,
      ...update,
      updatedAt: new Date().toISOString(),
    });
    await persist(state.entries.map((entry) => (entry.id === id ? next : entry)));
    return next;
  });
}

export function removeEntry(id: string): Promise<JournalEntry | null> {
  return enqueue(async () => {
    const current = state.entries.find((entry) => entry.id === id);
    if (!current) return null;
    await persist(state.entries.filter((entry) => entry.id !== id));
    return current;
  });
}

export function restoreEntry(entry: JournalEntry): Promise<void> {
  return enqueue(async () => {
    if (state.entries.some((existing) => existing.id === entry.id))
      throw new Error('This observation is already in the journal.');
    await persist([...state.entries, validateJournalEntry(entry)]);
  });
}

export function importJournal(raw: string): Promise<{ added: number; skipped: number }> {
  const imported = parseJournalArchive(raw);
  return enqueue(async () => {
    const merged = mergeImportedEntries(state.entries, imported.entries, journalId);
    await persist(merged.entries);
    return { added: merged.added, skipped: merged.skipped };
  });
}

export function clearJournalError() {
  publish({ error: null });
}

/** Always download a fresh blob; data URLs are reserved for validated thumbnails. */
export function downloadJournalFile(
  content: string,
  filename: string,
  type = 'application/json',
): void {
  const url = URL.createObjectURL(new Blob([content], { type }));
  const link = document.createElement('a');
  link.href = url;
  link.download = filename;
  link.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}
