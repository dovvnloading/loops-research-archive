import { useDeferredValue, useEffect, useMemo, useState } from 'react';
import { ArrowUpRight, Search, X } from 'lucide-react';
import {
  DataBoundary,
  DownloadButton,
  localAsset,
  REPO,
  ResearchHeading,
  ScopeNote,
  SourceLink,
  useData,
} from './common';

type RecordStatus = 'open' | 'proved' | 'imported';
type LedgerRecord = {
  id: string;
  status: RecordStatus;
  statement: string;
  deps: string[];
  evidence: string;
  evidence_url: string | null;
  evidence_resolution: string;
  hyp: string;
  clauses: string;
  classification?: string;
  group?: string;
  pr?: number;
  verifier?: string;
  physical_bridges?: string[];
  kind?: 'obligation' | 'update';
};
type Ledger = {
  counts: { imported: number; proved: number; open: number };
  obligations: LedgerRecord[];
  research_updates: LedgerRecord[];
  provenance?: { source_commit: string; status_note: string; mlc_status: string };
};
type CatalogFile = {
  path: string;
  title: string;
  kind: string;
  bytes: number;
  url: string;
  local_url: string;
};
type Catalog = { source_commit: string; files: CatalogFile[] };
type Filter = 'all' | RecordStatus | 'updates';

function Status({ status }: { status: string }) {
  return (
    <span className={`record-status ${status}`}>
      <i />
      {status}
    </span>
  );
}

function DependencyGraph({
  record,
  records,
  onSelect,
}: {
  record: LedgerRecord;
  records: LedgerRecord[];
  onSelect: (id: string) => void;
}) {
  const map = useMemo(() => new Map(records.map((row) => [row.id, row])), [records]);
  const dependencies = record.deps;
  const dependents = records.filter((row) => row.deps.includes(record.id));
  const [expanded, setExpanded] = useState(false);
  useEffect(() => setExpanded(false), [record.id]);
  const before = expanded ? dependencies : dependencies.slice(0, 6),
    after = expanded ? dependents : dependents.slice(0, 6);
  return (
    <section className="dependency-section">
      <div className="detail-section-heading">
        <h3>Dependencies</h3>
        <span>
          {dependencies.length} inputs · {dependents.length} dependents
        </span>
      </div>
      <div className="dependency-neighborhood">
        <div className="dependency-column">
          <span className="column-caption">Depends on</span>
          {before.length ? (
            before.map((id) => (
              <button
                key={id}
                disabled={!map.has(id)}
                onClick={() => onSelect(id)}
                title={map.get(id)?.statement ?? 'Referenced identifier not present in this ledger'}
              >
                <span className={`status-dot ${map.get(id)?.status ?? 'unknown'}`} />
                <code>{id}</code>
              </button>
            ))
          ) : (
            <p className="empty-neighborhood">No recorded dependencies</p>
          )}
        </div>
        <div className="dependency-column">
          <span className="column-caption">Used by</span>
          {after.length ? (
            after.map((row) => (
              <button key={row.id} onClick={() => onSelect(row.id)} title={row.statement}>
                <span className={`status-dot ${row.status}`} />
                <code>{row.id}</code>
              </button>
            ))
          ) : (
            <p className="empty-neighborhood">No recorded dependents</p>
          )}
        </div>
      </div>
      {(dependencies.length > 6 || dependents.length > 6) && (
        <button className="text-action" onClick={() => setExpanded(!expanded)}>
          {expanded
            ? 'Show fewer'
            : `Show all ${dependencies.length + dependents.length} connections`}
        </button>
      )}
    </section>
  );
}

function RecordDetail({
  record,
  records,
  onSelect,
  sourceCommit,
}: {
  record: LedgerRecord;
  records: LedgerRecord[];
  onSelect: (id: string) => void;
  sourceCommit?: string;
}) {
  return (
    <article className="record-detail" aria-label="Selected research record" tabIndex={-1}>
      <div className="record-detail-top">
        <h2 className="record-id">{record.id}</h2>
        <Status status={record.status} />
        <span>{record.kind === 'update' ? 'Research update' : 'Baseline obligation'}</span>
      </div>
      <p className="record-statement">{record.statement}</p>
      {record.classification && (
        <div className="record-classification">
          <span>Source classification</span>
          <strong>{record.classification}</strong>
        </div>
      )}
      <dl className="research-definition record-conditions">
        <div>
          <dt>Hypotheses</dt>
          <dd>
            {record.hyp && record.hyp !== 'none' ? record.hyp : 'None recorded in this entry'}
          </dd>
        </div>
        {record.clauses && (
          <div>
            <dt>Clauses</dt>
            <dd>{record.clauses}</dd>
          </div>
        )}
        {record.group && (
          <div>
            <dt>Research group</dt>
            <dd>{record.group}</dd>
          </div>
        )}
        {record.physical_bridges && (
          <div>
            <dt>Physical bridges</dt>
            <dd>{record.physical_bridges.join(' · ')}</dd>
          </div>
        )}
      </dl>
      <div className="record-evidence">
        <div className="detail-section-heading">
          <h3>Evidence</h3>
        </div>
        <code>{record.evidence || 'No evidence path recorded'}</code>
        <div className="record-evidence-links">
          {record.evidence_url ? (
            <SourceLink href={record.evidence_url} label="Source at this revision" />
          ) : (
            <>
              <span className="missing-source">Source file unavailable in this revision.</span>
              <a
                className="research-source"
                href={`${REPO}/search?q=${encodeURIComponent(record.evidence || record.id)}&type=code`}
                target="_blank"
                rel="noreferrer"
              >
                Search the repository
                <ArrowUpRight size={12} />
              </a>
            </>
          )}
          {record.verifier && (
            <SourceLink
              href={`${REPO}/blob/${sourceCommit ?? 'main'}/${record.verifier}`}
              label="Referenced verifier"
            />
          )}
          {record.pr && (
            <SourceLink href={`${REPO}/pull/${record.pr}`} label={`Pull request #${record.pr}`} />
          )}
        </div>
      </div>
      <DependencyGraph record={record} records={records} onSelect={onSelect} />
      <div className="record-detail-foot">
        <DownloadButton
          data={record}
          name={`loops-${record.id.toLowerCase()}.json`}
          label="Export record"
        />
        <span>Labels are preserved from the source.</span>
      </div>
    </article>
  );
}

function LedgerBrowser() {
  const { data, error, retry } = useData<Ledger>('ledger.json');
  const [query, setQuery] = useState('');
  const deferredQuery = useDeferredValue(query.toLowerCase().trim());
  const [filter, setFilter] = useState<Filter>('all');
  const [selectedId, setSelectedId] = useState('YOCCOZ');
  const [limit, setLimit] = useState(40);
  const records = useMemo<LedgerRecord[]>(
    () =>
      data
        ? [
            ...data.obligations.map((row) => ({ ...row, kind: 'obligation' as const })),
            ...data.research_updates.map((row) => ({ ...row, kind: 'update' as const })),
          ]
        : [],
    [data],
  );
  const filtered = useMemo(() => {
    const terms = deferredQuery.split(/\s+/).filter(Boolean);
    return records.filter(
      (row) =>
        (filter === 'all' ||
          (filter === 'updates' ? row.kind === 'update' : row.status === filter)) &&
        terms.every((term) =>
          `${row.id} ${row.statement} ${row.deps.join(' ')} ${row.hyp} ${row.classification ?? ''} ${row.group ?? ''}`
            .toLowerCase()
            .includes(term),
        ),
    );
  }, [records, filter, deferredQuery]);
  const selected = filtered.find((row) => row.id === selectedId) ?? filtered[0];
  useEffect(() => {
    setLimit(40);
  }, [deferredQuery, filter]);
  const selectRecord = (id: string) => {
    setSelectedId(id);
    if (!filtered.some((row) => row.id === id)) {
      setQuery('');
      setFilter('all');
    }
    window.setTimeout(() => {
      if (window.innerWidth < 800) {
        const detail = document.querySelector<HTMLElement>('.record-detail');
        detail?.focus({ preventScroll: true });
        detail?.scrollIntoView({
          behavior: window.matchMedia('(prefers-reduced-motion: reduce)').matches
            ? 'instant'
            : 'smooth',
          block: 'start',
        });
      }
    }, 0);
  };
  // The counts double as the status filter. Baseline labels and later updates stay separate.
  const filters: { id: Filter; label: string; count: number }[] = [
    { id: 'all', label: 'All records', count: records.length },
    { id: 'open', label: 'Open', count: data?.counts.open ?? 0 },
    { id: 'proved', label: 'Proved, source label', count: data?.counts.proved ?? 0 },
    { id: 'imported', label: 'Imported', count: data?.counts.imported ?? 0 },
    { id: 'updates', label: 'Later updates', count: data?.research_updates.length ?? 0 },
  ];
  return (
    <DataBoundary loading={!data} error={error} retry={retry}>
      <div className="ledger-toolbar">
        <div className="archive-stats" role="group" aria-label="Filter ledger status">
          {filters.map(({ id, label, count }) => (
            <button
              key={id}
              className={filter === id ? 'active' : ''}
              aria-pressed={filter === id}
              onClick={() => setFilter(id)}
            >
              {label} <b>{count}</b>
            </button>
          ))}
        </div>
        <div className="research-search">
          <Search size={14} />
          <input
            type="search"
            aria-label="Search research ledger"
            placeholder="Identifier, statement or dependency"
            value={query}
            onChange={(event) => setQuery(event.target.value)}
          />
          {query && (
            <button aria-label="Clear ledger search" onClick={() => setQuery('')}>
              <X size={14} />
            </button>
          )}
        </div>
      </div>
      <p className="result-count">
        {filtered.length === records.length
          ? `${data?.obligations.length ?? 0} baseline obligations and ${data?.research_updates.length ?? 0} later updates`
          : `${filtered.length} of ${records.length} records`}
      </p>
      <div className="ledger-layout">
        <div className="ledger-list" aria-label="Research records">
          {filtered.length === 0 ? (
            <div className="research-empty">
              <h3>No record matches</h3>
              <p>Nothing with this status contains “{query}”.</p>
              <button
                className="research-button secondary"
                onClick={() => {
                  setQuery('');
                  setFilter('all');
                }}
              >
                Clear the filter
              </button>
            </div>
          ) : (
            filtered.slice(0, limit).map((record) => (
              <button
                key={`${record.kind}:${record.id}`}
                className={`ledger-row ${record.id === selected?.id ? 'selected' : ''}`}
                aria-pressed={record.id === selected?.id}
                onClick={() => selectRecord(record.id)}
              >
                <span className="ledger-row-heading">
                  <code>{record.id}</code>
                  <Status status={record.status} />
                </span>
                <span className="ledger-row-statement">{record.statement}</span>
                <span className="ledger-row-foot">
                  {record.kind === 'update' && <span className="update-label">update</span>}
                  <span>
                    {record.deps.length} {record.deps.length === 1 ? 'dependency' : 'dependencies'}
                  </span>
                  {record.evidence_resolution === 'unresolved' && <span>source unavailable</span>}
                </span>
              </button>
            ))
          )}
          {filtered.length > limit && (
            <button className="ledger-load-more" onClick={() => setLimit((n) => n + 40)}>
              Show {Math.min(40, filtered.length - limit)} more
            </button>
          )}
        </div>
        {selected ? (
          <RecordDetail
            record={selected}
            records={records}
            onSelect={selectRecord}
            sourceCommit={data?.provenance?.source_commit}
          />
        ) : (
          <div className="research-empty">
            <p>Select a record to read its statement, hypotheses and evidence.</p>
          </div>
        )}
      </div>
      <ScopeNote>
        {data?.provenance?.status_note ??
          'A proved ledger entry may be a written or conditional result; it is not automatically kernel-checked.'}{' '}
        The baseline counts and later updates are displayed separately. MLC remains open.
      </ScopeNote>
    </DataBoundary>
  );
}

const bytes = (n: number) =>
  n < 1024
    ? `${n} B`
    : n < 1024 * 1024
      ? `${(n / 1024).toFixed(1)} KB`
      : `${(n / 1048576).toFixed(1)} MB`;

function SourceLibrary() {
  const { data, error, retry } = useData<Catalog>('catalog.json');
  const [query, setQuery] = useState('');
  const [kind, setKind] = useState('all');
  const [limit, setLimit] = useState(60);
  const deferred = useDeferredValue(query.toLowerCase().trim());
  const filtered = useMemo(
    () =>
      data?.files.filter(
        (file) =>
          (kind === 'all' || file.kind === kind) &&
          deferred
            .split(/\s+/)
            .every((term) => `${file.path} ${file.title}`.toLowerCase().includes(term)),
      ) ?? [],
    [data, kind, deferred],
  );
  useEffect(() => {
    setLimit(60);
  }, [kind, deferred]);
  const kinds = ['document', 'certificate', 'formalization', 'verifier', 'paper', 'figure'];
  return (
    <DataBoundary loading={!data} error={error} retry={retry}>
      <div className="ledger-toolbar">
        <div className="archive-stats" role="group" aria-label="Filter source type">
          {['all', ...kinds].map((value) => (
            <button
              key={value}
              className={kind === value ? 'active' : ''}
              aria-pressed={kind === value}
              onClick={() => setKind(value)}
            >
              {value === 'all' ? 'All files' : value[0].toUpperCase() + value.slice(1) + 's'}{' '}
              <b>
                {value === 'all'
                  ? (data?.files.length ?? 0)
                  : (data?.files.filter((file) => file.kind === value).length ?? 0)}
              </b>
            </button>
          ))}
        </div>
        <div className="research-search">
          <Search size={14} />
          <input
            type="search"
            aria-label="Search source library"
            value={query}
            onChange={(event) => setQuery(event.target.value)}
            placeholder="File name or path"
          />
          {query && (
            <button aria-label="Clear source search" onClick={() => setQuery('')}>
              <X size={14} />
            </button>
          )}
        </div>
      </div>
      <p className="result-count library-intro">
        <span>
          {filtered.length === data?.files.length
            ? `${filtered.length.toLocaleString()} files`
            : `${filtered.length.toLocaleString()} of ${data?.files.length.toLocaleString()} files`}
          , pinned to research revision <code>{data?.source_commit.slice(0, 12)}</code>. Links open
          in a new tab.
        </span>
        <SourceLink path="RESEARCH_MAP.md" label="Research map" />
      </p>
      {filtered.length > 0 && (
        <div className="source-table-wrap">
          <table className="source-grid">
            <thead>
              <tr>
                <th scope="col">File</th>
                <th scope="col">Kind</th>
                <th scope="col">Size</th>
                <th scope="col">Open</th>
              </tr>
            </thead>
            <tbody>
              {filtered.slice(0, limit).map((file) => (
                <tr className="source-card" key={file.path}>
                  <td>
                    <strong>{file.title.replaceAll('_', ' ')}</strong>
                    <code title={file.path}>{file.path}</code>
                  </td>
                  <td>{file.kind}</td>
                  <td>{bytes(file.bytes)}</td>
                  <td className="source-card-links">
                    <a href={file.url} target="_blank" rel="noreferrer">
                      Source
                    </a>
                    <a href={localAsset(file.local_url)} target="_blank" rel="noreferrer">
                      File
                    </a>
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      )}
      {filtered.length === 0 && (
        <div className="research-empty">
          <h3>No file matches</h3>
          <p>
            No {kind === 'all' ? 'file' : kind} has “{query}” in its name or path.
          </p>
          <button
            className="research-button secondary"
            onClick={() => {
              setQuery('');
              setKind('all');
            }}
          >
            Clear the filter
          </button>
        </div>
      )}
      {filtered.length > limit && (
        <button
          className="library-load-more research-button secondary"
          onClick={() => setLimit((n) => n + 60)}
        >
          Show {Math.min(60, filtered.length - limit)} more
        </button>
      )}
    </DataBoundary>
  );
}

export function Archive() {
  const [view, setView] = useState<'ledger' | 'library'>('ledger');
  return (
    <div className="research-content archive-workspace">
      <ResearchHeading
        title="Ledger and source library"
        description="Every obligation with its statement, hypotheses, evidence and dependencies, and every file behind them."
      >
        <span className="archive-open-note">
          <span className="status-dot open" /> MLC remains open
        </span>
        <a className="research-button secondary" href={REPO} target="_blank" rel="noreferrer">
          Repository
          <ArrowUpRight size={13} />
        </a>
      </ResearchHeading>
      <nav className="research-tabs" role="tablist" aria-label="Archive views">
        <button
          className={view === 'ledger' ? 'active' : ''}
          role="tab"
          aria-selected={view === 'ledger'}
          onClick={() => setView('ledger')}
        >
          Proof ledger
        </button>
        <button
          className={view === 'library' ? 'active' : ''}
          role="tab"
          aria-selected={view === 'library'}
          onClick={() => setView('library')}
        >
          Source library
        </button>
      </nav>
      {view === 'ledger' ? <LedgerBrowser /> : <SourceLibrary />}
    </div>
  );
}
