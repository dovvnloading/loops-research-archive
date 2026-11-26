import type { EngineState } from '../types';
import type { ExactView } from '../precision/types';

/** A view is portable: no canvas, worker, URL, or device-specific objects. */
export interface JournalPayload {
  engine: EngineState;
  exact: ExactView;
  experiment?: unknown;
  sourceRevision?: string;
}

export interface JournalEntry {
  version: 2;
  id: string;
  title: string;
  notes: string;
  tags: string[];
  parentId: string | null;
  createdAt: string;
  updatedAt: string;
  thumbnail?: string;
  payload: JournalPayload;
}

export interface NewJournalEntry {
  title: string;
  notes?: string;
  tags?: string[];
  parentId?: string | null;
  thumbnail?: string;
  payload: JournalPayload;
}

export interface JournalArchive {
  format: 'loops-journal';
  version: 2;
  exportedAt: string;
  entries: JournalEntry[];
}

export type JournalStorageMode = 'loading' | 'indexeddb' | 'local' | 'memory';

export interface JournalState {
  entries: JournalEntry[];
  ready: boolean;
  mode: JournalStorageMode;
  error: string | null;
}
