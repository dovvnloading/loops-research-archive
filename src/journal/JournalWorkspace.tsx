import { useEffect, useMemo, useRef, useState } from 'react';
import {
  ArrowDownToLine,
  ArrowLeft,
  ArrowUpRight,
  BookOpen,
  Check,
  CheckSquare,
  ChevronRight,
  Clock3,
  Copy,
  Download,
  GitBranch,
  LayoutGrid,
  List,
  LoaderCircle,
  Plus,
  Search,
  Share2,
  Square,
  Tag,
  Trash2,
  Undo2,
  Upload,
  X,
} from 'lucide-react';
import { createSnapshotURL, journalCSV, MAX_IMPORT_BYTES, serializeJournal } from './codec';
import {
  clearJournalError,
  downloadJournalFile,
  importJournal,
  removeEntry,
  restoreEntry,
  saveEntry,
  updateEntry,
  useJournal,
} from './store';
import type { JournalEntry, JournalPayload } from './types';
import './journal.css';

const familyNames: Record<string, string> = {
  mandelbrot: 'Mandelbrot',
  julia: 'Julia set',
  mandelbulb: 'Mandelbulb',
  mandelbox: 'Mandelbox',
  quaternion: 'Quaternion Julia',
  landscape: 'Escape landscape',
};
const familyName = (entry: JournalEntry) =>
  familyNames[entry.payload.engine.scene] ?? entry.payload.engine.scene;
const shortDate = (value: string) =>
  new Date(value).toLocaleDateString(undefined, { month: 'short', day: 'numeric' });
const fullDate = (value: string) =>
  new Date(value).toLocaleString(undefined, { dateStyle: 'medium', timeStyle: 'short' });
const isPlane = (entry: JournalEntry) =>
  ['mandelbrot', 'julia'].includes(entry.payload.engine.scene);

interface JournalWorkspaceProps {
  onRestore: (payload: JournalPayload, entry?: JournalEntry) => void;
  onNew: () => void;
  onBranch?: (payload: JournalPayload, entry: JournalEntry) => void;
}

async function copyText(value: string) {
  if (navigator.clipboard?.writeText) return navigator.clipboard.writeText(value);
  const field = document.createElement('textarea');
  field.value = value;
  field.style.position = 'fixed';
  field.style.opacity = '0';
  document.body.append(field);
  field.select();
  const success = document.execCommand('copy');
  field.remove();
  if (!success) throw new Error('Clipboard access is unavailable.');
}

function Thumbnail({ entry, className = '' }: { entry: JournalEntry; className?: string }) {
  return (
    <div className={`journal-thumbnail journal-family-${entry.payload.engine.scene} ${className}`}>
      {entry.thumbnail ? (
        <img
          src={entry.thumbnail}
          alt={`${entry.title} — ${familyName(entry)} snapshot`}
          loading="lazy"
        />
      ) : (
        <div className="journal-preview-empty">
          <BookOpen size={26} strokeWidth={1.2} />
          <span>{entry.payload.experiment ? 'Experiment record' : 'Saved coordinates'}</span>
          <code>{isPlane(entry) ? `Δ ${entry.payload.exact.span}` : familyName(entry)}</code>
        </div>
      )}
    </div>
  );
}

function DetailPanel({
  entry,
  entries,
  onClose,
  onRestore,
  onDeleted,
  onBranch,
  notify,
}: {
  entry: JournalEntry;
  entries: JournalEntry[];
  onClose: () => void;
  onRestore: JournalWorkspaceProps['onRestore'];
  onDeleted: (entry: JournalEntry) => void;
  onBranch?: JournalWorkspaceProps['onBranch'];
  notify: (message: string, error?: boolean) => void;
}) {
  const [title, setTitle] = useState(entry.title),
    [notes, setNotes] = useState(entry.notes),
    [tags, setTags] = useState(entry.tags.join(', '));
  const [busy, setBusy] = useState(false),
    [copied, setCopied] = useState(false),
    [showExperiment, setShowExperiment] = useState(false);
  useEffect(() => {
    setTitle(entry.title);
    setNotes(entry.notes);
    setTags(entry.tags.join(', '));
    setShowExperiment(false);
  }, [entry.id]);
  const dirty = title !== entry.title || notes !== entry.notes || tags !== entry.tags.join(', ');
  const parent = entries.find((item) => item.id === entry.parentId);
  const children = entries.filter((item) => item.parentId === entry.id);
  const save = async () => {
    setBusy(true);
    try {
      const saved = await updateEntry(entry.id, {
        title,
        notes,
        tags: tags
          .split(',')
          .map((tag) => tag.trim())
          .filter(Boolean),
      });
      setTitle(saved.title);
      setNotes(saved.notes);
      setTags(saved.tags.join(', '));
      notify('Observation updated.');
    } catch (error) {
      notify(error instanceof Error ? error.message : 'Could not update observation.', true);
    } finally {
      setBusy(false);
    }
  };
  const branch = async () => {
    if (onBranch) {
      onBranch(entry.payload, entry);
      return;
    }
    setBusy(true);
    try {
      const next = await saveEntry({
        title: `${entry.title.slice(0, 145)} · branch`,
        notes: '',
        tags: entry.tags,
        parentId: entry.id,
        thumbnail: entry.thumbnail,
        payload: entry.payload,
      });
      onRestore(next.payload, next);
    } catch (error) {
      notify(error instanceof Error ? error.message : 'Could not create branch.', true);
    } finally {
      setBusy(false);
    }
  };
  const share = async () => {
    try {
      await copyText(createSnapshotURL(entry.payload));
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
      notify('View link copied. Your notes stay private.');
    } catch (error) {
      notify(error instanceof Error ? error.message : 'Could not copy the link.', true);
    }
  };
  const remove = async () => {
    setBusy(true);
    try {
      const removed = await removeEntry(entry.id);
      if (removed) onDeleted(removed);
      onClose();
    } catch (error) {
      notify(error instanceof Error ? error.message : 'Could not delete observation.', true);
    } finally {
      setBusy(false);
    }
  };
  return (
    <aside className="journal-detail" aria-label="Observation details">
      <div className="journal-detail-heading">
        <span>OBSERVATION</span>
        <button
          className="journal-icon-button"
          onClick={onClose}
          aria-label="Close observation details"
        >
          <X size={18} />
        </button>
      </div>
      <Thumbnail entry={entry} className="journal-detail-image" />
      <div className="journal-detail-body">
        <div className="journal-detail-meta">
          <span>{familyName(entry)}</span>
          <time dateTime={entry.createdAt}>{fullDate(entry.createdAt)}</time>
        </div>
        <label className="journal-field">
          <span>Title</span>
          <input value={title} onChange={(event) => setTitle(event.target.value)} maxLength={160} />
        </label>
        <label className="journal-field">
          <span>Field notes</span>
          <textarea
            value={notes}
            onChange={(event) => setNotes(event.target.value)}
            maxLength={40_000}
            rows={5}
            placeholder="What did you notice? What would you explore next?"
          />
        </label>
        <label className="journal-field">
          <span>
            Tags <small>separate with commas</small>
          </span>
          <input
            value={tags}
            onChange={(event) => setTags(event.target.value)}
            placeholder="spirals, boundary, follow-up"
          />
        </label>
        {dirty && (
          <button
            className="journal-button journal-primary journal-full"
            onClick={() => void save()}
            disabled={busy || !title.trim()}
          >
            {busy ? <LoaderCircle size={15} className="journal-spin" /> : <Check size={15} />} Save
            changes
          </button>
        )}
        <div className="journal-detail-actions">
          <button
            className="journal-button journal-primary"
            onClick={() => onRestore(entry.payload, entry)}
          >
            <ArrowUpRight size={16} /> Open in explorer
          </button>
          <button className="journal-button" onClick={() => void branch()} disabled={busy}>
            <GitBranch size={15} /> Branch
          </button>
        </div>
        <section className="journal-coordinate-section">
          <h3>REPRODUCIBLE VIEW</h3>
          {isPlane(entry) ? (
            <>
              <Coordinate label="Real" value={entry.payload.exact.center.re} notify={notify} />
              <Coordinate label="Imaginary" value={entry.payload.exact.center.im} notify={notify} />
              <Coordinate label="Vertical span" value={entry.payload.exact.span} notify={notify} />
            </>
          ) : (
            <>
              <Coordinate
                label="Camera yaw / pitch"
                value={`${entry.payload.engine.camera.yaw.toPrecision(8)} / ${entry.payload.engine.camera.pitch.toPrecision(8)}`}
                notify={notify}
              />
              <Coordinate
                label="Camera distance"
                value={String(entry.payload.engine.camera.distance)}
                notify={notify}
              />
              {entry.payload.engine.camera.position && (
                <Coordinate
                  label="Flight position"
                  value={entry.payload.engine.camera.position.join(', ')}
                  notify={notify}
                />
              )}
            </>
          )}
          <div className="journal-data-row">
            <span>Iteration budget</span>
            <code>
              {isPlane(entry)
                ? entry.payload.exact.iterations.toLocaleString()
                : entry.payload.engine.iterations}
            </code>
          </div>
          <div className="journal-data-row">
            <span>Palette</span>
            <code>
              {isPlane(entry) ? entry.payload.exact.palette : entry.payload.engine.palette}
            </code>
          </div>
          {entry.payload.sourceRevision && (
            <Coordinate
              label="Research revision"
              value={entry.payload.sourceRevision}
              notify={notify}
            />
          )}
        </section>
        {(entry.parentId || children.length > 0) && (
          <section className="journal-lineage">
            <h3>
              <GitBranch size={14} /> BRANCH HISTORY
            </h3>
            {entry.parentId && (
              <div>
                <span className="journal-lineage-line" />
                <span>From {parent ? parent.title : 'an observation outside this journal'}</span>
              </div>
            )}
            <div className="journal-lineage-current">
              <span className="journal-lineage-dot" />
              <span>{entry.title}</span>
            </div>
            {children.map((child) => (
              <div key={child.id}>
                <span className="journal-lineage-line" />
                <span>{child.title}</span>
              </div>
            ))}
          </section>
        )}
        {entry.payload.experiment !== undefined && (
          <section className="journal-experiment">
            <button
              onClick={() => setShowExperiment((value) => !value)}
              aria-expanded={showExperiment}
            >
              <ChevronRight size={14} className={showExperiment ? 'journal-rotate' : ''} />{' '}
              Experiment manifest
            </button>
            {showExperiment && (
              <>
                <pre>{JSON.stringify(entry.payload.experiment, null, 2)}</pre>
                <button
                  className="journal-button"
                  onClick={() =>
                    downloadJournalFile(
                      JSON.stringify(entry.payload.experiment, null, 2),
                      `loops-experiment-${entry.id.slice(0, 8)}.json`,
                    )
                  }
                >
                  <Download size={14} /> Export manifest
                </button>
              </>
            )}
          </section>
        )}
        <div className="journal-detail-footer">
          <button className="journal-button" onClick={() => void share()}>
            {copied ? <Check size={14} /> : <Share2 size={14} />}{' '}
            {copied ? 'Copied' : 'Copy view link'}
          </button>
          <button
            className="journal-icon-button journal-delete"
            onClick={() => void remove()}
            disabled={busy}
            aria-label={`Delete ${entry.title}`}
            title="Delete observation"
          >
            <Trash2 size={16} />
          </button>
        </div>
      </div>
    </aside>
  );
}

function Coordinate({
  label,
  value,
  notify,
}: {
  label: string;
  value: string;
  notify: (message: string, error?: boolean) => void;
}) {
  return (
    <div className="journal-coordinate">
      <span>{label}</span>
      <div>
        <code>{value}</code>
        <button
          className="journal-icon-button"
          aria-label={`Copy ${label.toLowerCase()}`}
          onClick={() =>
            void copyText(value)
              .then(() => notify(`${label} copied exactly.`))
              .catch(() => notify('Could not access the clipboard.', true))
          }
        >
          <Copy size={12} />
        </button>
      </div>
    </div>
  );
}

function Comparison({
  entries,
  onClose,
  onRestore,
}: {
  entries: [JournalEntry, JournalEntry];
  onClose: () => void;
  onRestore: JournalWorkspaceProps['onRestore'];
}) {
  const dialog = useRef<HTMLDialogElement>(null);
  useEffect(() => {
    const element = dialog.current;
    element?.showModal();
    return () => {
      element?.close();
    };
  }, []);
  const [left, right] = entries;
  const rows = [
    ['Family', familyName(left), familyName(right)],
    ['Real center', left.payload.exact.center.re, right.payload.exact.center.re],
    ['Imaginary center', left.payload.exact.center.im, right.payload.exact.center.im],
    ['Vertical span', left.payload.exact.span, right.payload.exact.span],
    [
      'Iterations',
      String(isPlane(left) ? left.payload.exact.iterations : left.payload.engine.iterations),
      String(isPlane(right) ? right.payload.exact.iterations : right.payload.engine.iterations),
    ],
    [
      'Palette',
      isPlane(left) ? left.payload.exact.palette : left.payload.engine.palette,
      isPlane(right) ? right.payload.exact.palette : right.payload.engine.palette,
    ],
    ['Created', fullDate(left.createdAt), fullDate(right.createdAt)],
  ];
  return (
    <dialog
      className="journal-comparison"
      ref={dialog}
      onCancel={onClose}
      onClick={(event) => {
        if (event.target === event.currentTarget) onClose();
      }}
      aria-labelledby="journal-compare-title"
    >
      <div className="journal-comparison-top">
        <div>
          <span className="journal-eyebrow">SIDE BY SIDE</span>
          <h2 id="journal-compare-title">Two moments of discovery.</h2>
        </div>
        <button className="journal-icon-button" onClick={onClose} aria-label="Close comparison">
          <X size={20} />
        </button>
      </div>
      <div className="journal-comparison-images">
        {entries.map((entry) => (
          <section key={entry.id}>
            <Thumbnail entry={entry} />
            <h3>{entry.title}</h3>
            <p>{entry.notes || 'No field notes yet.'}</p>
            <button
              className="journal-button"
              onClick={() => {
                onClose();
                onRestore(entry.payload, entry);
              }}
            >
              <ArrowUpRight size={14} /> Explore this view
            </button>
          </section>
        ))}
      </div>
      <div className="journal-comparison-table">
        <table>
          <thead>
            <tr>
              <th>Settings</th>
              <th>{left.title}</th>
              <th>{right.title}</th>
            </tr>
          </thead>
          <tbody>
            {rows.map(([label, a, b]) => (
              <tr key={label} className={a !== b ? 'journal-difference' : ''}>
                <th scope="row">{label}</th>
                <td>
                  <code>{a}</code>
                </td>
                <td>
                  <code>{b}</code>
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <p className="journal-compare-note">
        Highlighted rows show different settings. Image resemblance alone does not establish
        mathematical equivalence.
      </p>
    </dialog>
  );
}

export function JournalWorkspace({ onRestore, onNew, onBranch }: JournalWorkspaceProps) {
  const { entries, ready, mode, error } = useJournal();
  const [query, setQuery] = useState(''),
    [tag, setTag] = useState('all'),
    [order, setOrder] = useState('newest'),
    [layout, setLayout] = useState<'grid' | 'list' | 'branches'>('grid');
  const [selectedId, setSelectedId] = useState<string | null>(null),
    [comparisonIds, setComparisonIds] = useState<string[]>([]),
    [comparing, setComparing] = useState(false);
  const [notice, setNotice] = useState<{ message: string; error?: boolean } | null>(null),
    [deleted, setDeleted] = useState<JournalEntry | null>(null),
    [importing, setImporting] = useState(false);
  const fileInput = useRef<HTMLInputElement>(null),
    noticeTimer = useRef<ReturnType<typeof setTimeout> | null>(null);
  const notify = (message: string, isError = false) => {
    if (noticeTimer.current) clearTimeout(noticeTimer.current);
    setNotice({ message, error: isError });
    noticeTimer.current = setTimeout(() => setNotice(null), isError ? 9000 : 5000);
  };
  useEffect(
    () => () => {
      if (noticeTimer.current) clearTimeout(noticeTimer.current);
    },
    [],
  );
  const tags = useMemo(
    () => [...new Set(entries.flatMap((entry) => entry.tags))].sort(),
    [entries],
  );
  const selected = entries.find((entry) => entry.id === selectedId);
  const visible = useMemo(() => {
    const search = query.trim().toLocaleLowerCase();
    return entries
      .filter(
        (entry) =>
          (tag === 'all' || entry.tags.includes(tag)) &&
          (!search ||
            [
              entry.title,
              entry.notes,
              familyName(entry),
              ...entry.tags,
              entry.payload.exact.center.re,
              entry.payload.exact.center.im,
            ]
              .join(' ')
              .toLocaleLowerCase()
              .includes(search)),
      )
      .sort((a, b) =>
        order === 'title'
          ? a.title.localeCompare(b.title)
          : order === 'oldest'
            ? a.createdAt.localeCompare(b.createdAt)
            : b.createdAt.localeCompare(a.createdAt),
      );
  }, [entries, query, tag, order]);
  const families = new Set(entries.map((entry) => entry.payload.engine.scene)).size;
  const branchCount = entries.filter((entry) => entry.parentId).length;
  const comparisonEntries = comparisonIds
    .map((id) => entries.find((entry) => entry.id === id))
    .filter((entry): entry is JournalEntry => !!entry);
  const toggleCompare = (id: string) =>
    setComparisonIds((current) =>
      current.includes(id)
        ? current.filter((item) => item !== id)
        : current.length < 2
          ? [...current, id]
          : [current[1], id],
    );
  const importFile = async (file?: File) => {
    if (!file) return;
    setImporting(true);
    try {
      if (file.size > MAX_IMPORT_BYTES)
        throw new Error('Choose a journal export smaller than 24 MB.');
      const result = await importJournal(await file.text());
      notify(
        `Imported ${result.added} observation${result.added === 1 ? '' : 's'}${result.skipped ? `; ${result.skipped} already present` : ''}.`,
      );
    } catch (reason) {
      notify(reason instanceof Error ? reason.message : 'Could not import the journal.', true);
    } finally {
      setImporting(false);
      if (fileInput.current) fileInput.current.value = '';
    }
  };
  const exportAll = () => {
    downloadJournalFile(
      serializeJournal(entries),
      `loops-journal-${new Date().toISOString().slice(0, 10)}.json`,
    );
    notify('Journal exported with exact coordinates, notes, and thumbnails.');
  };
  const depthOf = (entry: JournalEntry) => {
    let depth = 0;
    let parent = entry.parentId;
    const visited = new Set([entry.id]);
    while (parent && depth < 8 && !visited.has(parent)) {
      visited.add(parent);
      const found = entries.find((item) => item.id === parent);
      if (!found) break;
      depth++;
      parent = found.parentId;
    }
    return depth;
  };
  const branchOrder = useMemo(() => {
    const included = new Set(visible.map((entry) => entry.id)),
      visited = new Set<string>(),
      output: JournalEntry[] = [];
    const visit = (entry: JournalEntry) => {
      if (visited.has(entry.id)) return;
      visited.add(entry.id);
      output.push(entry);
      for (const child of visible.filter((item) => item.parentId === entry.id)) visit(child);
    };
    for (const entry of visible) if (!entry.parentId || !included.has(entry.parentId)) visit(entry);
    for (const entry of visible) visit(entry);
    return output;
  }, [visible]);
  const displayed = layout === 'branches' ? branchOrder : visible;
  return (
    <div className="journal-workspace">
      <header className="journal-header">
        <div>
          <span className="journal-eyebrow">
            <BookOpen size={13} /> YOUR EXPLORATION JOURNAL
          </span>
          <h1>Keep your discoveries.</h1>
          <p>A place for the views, questions, and unexpected turns worth returning to.</p>
        </div>
        <div className="journal-header-actions">
          <button
            className="journal-button"
            onClick={() => fileInput.current?.click()}
            disabled={importing}
          >
            {importing ? <LoaderCircle size={15} className="journal-spin" /> : <Upload size={15} />}{' '}
            Import
          </button>
          <button className="journal-button" onClick={exportAll} disabled={!entries.length}>
            <Download size={15} /> Export
          </button>
          <button className="journal-button journal-primary" onClick={onNew}>
            <Plus size={16} /> New observation
          </button>
        </div>
      </header>
      <input
        ref={fileInput}
        type="file"
        accept="application/json,.json"
        className="journal-hidden"
        aria-label="Import a journal JSON file"
        onChange={(event) => void importFile(event.target.files?.[0])}
      />
      <div className="journal-summary">
        <div>
          <strong>{entries.length.toString().padStart(2, '0')}</strong>
          <span>observations</span>
        </div>
        <div>
          <strong>{families.toString().padStart(2, '0')}</strong>
          <span>fractal families</span>
        </div>
        <div>
          <strong>{branchCount.toString().padStart(2, '0')}</strong>
          <span>branches explored</span>
        </div>
        <span className={`journal-storage journal-storage-${mode}`}>
          <span />{' '}
          {mode === 'indexeddb'
            ? 'Saved in this browser'
            : mode === 'local'
              ? 'Local storage'
              : mode === 'memory'
                ? 'Temporary session'
                : 'Opening journal'}
        </span>
      </div>
      {error && (
        <div className="journal-warning" role="status">
          <span>{error}</span>
          <button
            className="journal-icon-button"
            onClick={clearJournalError}
            aria-label="Dismiss storage notice"
          >
            <X size={16} />
          </button>
        </div>
      )}
      {entries.length > 0 && (
        <div className="journal-toolbar">
          <label className="journal-search">
            <Search size={16} />
            <input
              placeholder="Search observations, notes, coordinates…"
              value={query}
              onChange={(event) => setQuery(event.target.value)}
              aria-label="Search journal"
            />
            {query && (
              <button
                className="journal-icon-button"
                onClick={() => setQuery('')}
                aria-label="Clear search"
              >
                <X size={14} />
              </button>
            )}
          </label>
          <label className="journal-filter">
            <Tag size={14} />
            <select
              value={tag}
              onChange={(event) => setTag(event.target.value)}
              aria-label="Filter by tag"
            >
              <option value="all">All tags</option>
              {tags.map((value) => (
                <option key={value} value={value}>
                  {value}
                </option>
              ))}
            </select>
          </label>
          <select
            className="journal-sort"
            value={order}
            onChange={(event) => setOrder(event.target.value)}
            aria-label="Sort observations"
          >
            <option value="newest">Newest first</option>
            <option value="oldest">Oldest first</option>
            <option value="title">Title A–Z</option>
          </select>
          <div className="journal-layout-switch" role="group" aria-label="Journal layout">
            <button
              aria-label="Grid view"
              aria-pressed={layout === 'grid'}
              onClick={() => setLayout('grid')}
            >
              <LayoutGrid size={16} />
            </button>
            <button
              aria-label="List view"
              aria-pressed={layout === 'list'}
              onClick={() => setLayout('list')}
            >
              <List size={17} />
            </button>
            <button
              aria-label="Branch history"
              aria-pressed={layout === 'branches'}
              onClick={() => setLayout('branches')}
            >
              <GitBranch size={16} />
            </button>
          </div>
        </div>
      )}
      {!ready ? (
        <div className="journal-empty">
          <LoaderCircle size={24} className="journal-spin" />
          <h2>Opening your journal…</h2>
        </div>
      ) : !entries.length ? (
        <div className="journal-empty">
          <div className="journal-empty-icon">
            <BookOpen size={36} strokeWidth={1.1} />
            <span>01</span>
          </div>
          <span className="journal-eyebrow">EVERY EXPLORATION STARTS SOMEWHERE</span>
          <h2>
            Find something you
            <br />
            want to remember.
          </h2>
          <p>
            Save a view from the explorer. Its exact coordinates and settings stay together with
            your notes, so you can always find your way back.
          </p>
          <button className="journal-button journal-primary" onClick={onNew}>
            Begin exploring <ArrowUpRight size={16} />
          </button>
          <div className="journal-empty-footnote">
            <GitBranch size={14} /> Follow a question. Save a branch. See where it leads.
          </div>
        </div>
      ) : (
        <div className={`journal-content ${selected ? 'journal-has-detail' : ''}`}>
          <div className="journal-observations">
            <div className="journal-results-label">
              <span>
                {visible.length === entries.length
                  ? 'ALL OBSERVATIONS'
                  : `${visible.length} MATCHING OBSERVATIONS`}
              </span>
              <button
                onClick={() => {
                  downloadJournalFile(
                    journalCSV(visible),
                    'loops-observations.csv',
                    'text/csv;charset=utf-8',
                  );
                  notify('Visible observations exported as CSV.');
                }}
                title="Export visible observations as a spreadsheet"
              >
                <ArrowDownToLine size={12} /> CSV
              </button>
            </div>
            {!visible.length ? (
              <div className="journal-no-results">
                <Search size={24} />
                <h2>No observations found.</h2>
                <p>Try another phrase or tag.</p>
                <button
                  className="journal-button"
                  onClick={() => {
                    setQuery('');
                    setTag('all');
                  }}
                >
                  Clear filters
                </button>
              </div>
            ) : (
              <div className={`journal-cards journal-${layout}`}>
                {displayed.map((entry) => (
                  <article
                    key={entry.id}
                    className={`journal-card ${selectedId === entry.id ? 'journal-card-selected' : ''}`}
                    style={
                      layout === 'branches'
                        ? ({
                            '--journal-depth': Math.min(depthOf(entry), 4),
                          } as React.CSSProperties)
                        : undefined
                    }
                  >
                    <button
                      className="journal-card-main"
                      onClick={() => setSelectedId(entry.id)}
                      aria-label={`View ${entry.title}`}
                    >
                      <Thumbnail entry={entry} />
                      <div className="journal-card-copy">
                        <div className="journal-card-topline">
                          <span>{familyName(entry)}</span>
                          <span>{shortDate(entry.createdAt)}</span>
                        </div>
                        <h2>{entry.title}</h2>
                        <p>
                          {entry.notes
                            ? entry.notes.slice(0, 110)
                            : isPlane(entry)
                              ? `Span ${entry.payload.exact.span} · ${entry.payload.exact.iterations.toLocaleString()} iterations`
                              : `Power ${entry.payload.engine.power} · ${entry.payload.engine.iterations} iterations`}
                        </p>
                        <div className="journal-card-tags">
                          {entry.parentId && (
                            <span className="journal-branch-tag">
                              <GitBranch size={10} /> Branch
                            </span>
                          )}
                          {entry.tags.slice(0, 3).map((value) => (
                            <span key={value}>{value}</span>
                          ))}
                        </div>
                      </div>
                    </button>
                    <button
                      className={`journal-compare-toggle ${comparisonIds.includes(entry.id) ? 'journal-checked' : ''}`}
                      onClick={() => toggleCompare(entry.id)}
                      aria-label={`${comparisonIds.includes(entry.id) ? 'Deselect' : 'Select'} ${entry.title} for comparison`}
                      aria-pressed={comparisonIds.includes(entry.id)}
                    >
                      {comparisonIds.includes(entry.id) ? (
                        <CheckSquare size={16} />
                      ) : (
                        <Square size={16} />
                      )}
                    </button>
                    <button
                      className="journal-card-open"
                      onClick={() => onRestore(entry.payload, entry)}
                      aria-label={`Explore ${entry.title}`}
                    >
                      <ArrowUpRight size={16} />
                    </button>
                  </article>
                ))}
              </div>
            )}
          </div>
          {selected && (
            <DetailPanel
              key={selected.id}
              entry={selected}
              entries={entries}
              onClose={() => setSelectedId(null)}
              onRestore={onRestore}
              onDeleted={(entry) => {
                setDeleted(entry);
                setComparisonIds((current) => current.filter((id) => id !== entry.id));
                notify('Observation removed. You can undo this deletion.');
              }}
              onBranch={onBranch}
              notify={notify}
            />
          )}
        </div>
      )}
      {comparisonIds.length > 0 && (
        <div className="journal-compare-bar">
          <span>{comparisonEntries.length} of 2 selected</span>
          <button
            className="journal-button journal-primary"
            disabled={comparisonEntries.length !== 2}
            onClick={() => setComparing(true)}
          >
            Compare observations <ArrowUpRight size={14} />
          </button>
          <button
            className="journal-icon-button"
            aria-label="Clear comparison selection"
            onClick={() => setComparisonIds([])}
          >
            <X size={16} />
          </button>
        </div>
      )}
      {deleted && (
        <div className="journal-undo" role="status">
          <span>“{deleted.title.slice(0, 45)}” removed</span>
          <button
            onClick={() =>
              void restoreEntry(deleted)
                .then(() => {
                  setDeleted(null);
                  notify('Observation restored.');
                })
                .catch((reason) =>
                  notify(
                    reason instanceof Error ? reason.message : 'Could not restore observation.',
                    true,
                  ),
                )
            }
          >
            <Undo2 size={14} /> Undo
          </button>
          <button
            className="journal-icon-button"
            onClick={() => setDeleted(null)}
            aria-label="Dismiss undo"
          >
            <X size={14} />
          </button>
        </div>
      )}
      {notice && (
        <div
          className={`journal-toast ${notice.error ? 'journal-toast-error' : ''}`}
          role={notice.error ? 'alert' : 'status'}
        >
          {notice.error ? <X size={15} /> : <Check size={15} />}
          <span>{notice.message}</span>
        </div>
      )}
      {comparing && comparisonEntries.length === 2 && (
        <Comparison
          entries={comparisonEntries as [JournalEntry, JournalEntry]}
          onClose={() => setComparing(false)}
          onRestore={onRestore}
        />
      )}
      <footer className="journal-footer">
        <span>
          <Clock3 size={12} /> Every saved view is a reproducible starting point.
        </span>
        <span>Local to this browser · Export to back up or move between devices.</span>
      </footer>
    </div>
  );
}
