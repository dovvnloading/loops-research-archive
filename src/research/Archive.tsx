import { useDeferredValue, useEffect, useMemo, useState } from 'react';
import { ArrowDown, ArrowRight, ArrowUpRight, BookOpen, ChevronDown, FileCode2, FileText, GitBranch, Search, X } from 'lucide-react';
import { DataBoundary, DownloadButton, localAsset, Metric, REPO, ResearchHeading, ScopeNote, SourceLink, useData } from './common';

type RecordStatus = 'open' | 'proved' | 'imported';
type LedgerRecord = { id: string; status: RecordStatus; statement: string; deps: string[]; evidence: string; evidence_url: string | null; evidence_resolution: string; hyp: string; clauses: string; classification?: string; group?: string; pr?: number; verifier?: string; physical_bridges?: string[]; kind?: 'obligation' | 'update' };
type Ledger = { counts: { imported: number; proved: number; open: number }; obligations: LedgerRecord[]; research_updates: LedgerRecord[]; provenance?: { source_commit: string; status_note: string; mlc_status: string } };
type CatalogFile = { path: string; title: string; kind: string; bytes: number; url: string; local_url: string };
type Catalog = { source_commit: string; files: CatalogFile[] };

function Status({ status }: { status: string }) { return <span className={`record-status ${status}`}><i />{status}</span>; }

function DependencyGraph({ record, records, onSelect }: { record: LedgerRecord; records: LedgerRecord[]; onSelect: (id: string) => void }) {
  const map = useMemo(() => new Map(records.map(row => [row.id, row])), [records]);
  const dependencies = record.deps;
  const dependents = records.filter(row => row.deps.includes(record.id));
  const [expanded, setExpanded] = useState(false);
  useEffect(() => setExpanded(false), [record.id]);
  const before = expanded ? dependencies : dependencies.slice(0, 6), after = expanded ? dependents : dependents.slice(0, 6);
  return <section className="dependency-section"><div className="detail-section-heading"><h3><GitBranch size={14} /> Dependency neighborhood</h3><span>{dependencies.length} inputs · {dependents.length} dependents</span></div><div className="dependency-neighborhood"><div className="dependency-column"><span className="column-caption">DEPENDS ON</span>{before.length ? before.map(id => <button key={id} disabled={!map.has(id)} onClick={() => onSelect(id)} title={map.get(id)?.statement ?? 'Referenced identifier not present in this ledger'}><span className={`status-dot ${map.get(id)?.status ?? 'unknown'}`} /><code>{id}</code><ArrowRight size={12} /></button>) : <p className="empty-neighborhood">No recorded dependencies</p>}</div><div className="dependency-focus"><ArrowRight size={18} /><span className={`status-dot ${record.status}`} /><ArrowRight size={18} /></div><div className="dependency-column"><span className="column-caption">USED BY</span>{after.length ? after.map(row => <button key={row.id} onClick={() => onSelect(row.id)} title={row.statement}><span className={`status-dot ${row.status}`} /><code>{row.id}</code><ArrowRight size={12} /></button>) : <p className="empty-neighborhood">No recorded dependents</p>}</div></div>{(dependencies.length > 6 || dependents.length > 6) && <button className="text-action" onClick={() => setExpanded(!expanded)}>{expanded ? 'Show fewer connections' : `Show all ${dependencies.length + dependents.length} connections`}<ChevronDown size={13} /></button>}</section>;
}

function RecordDetail({ record, records, onSelect, sourceCommit }: { record: LedgerRecord; records: LedgerRecord[]; onSelect: (id: string) => void; sourceCommit?: string }) {
  return <article className="record-detail" aria-label="Selected research record" tabIndex={-1}><div className="record-detail-top"><span className="research-eyebrow">{record.kind === 'update' ? 'RESEARCH UPDATE' : 'OBLIGATION RECORD'}</span><Status status={record.status} /></div><h2>{record.id.replaceAll('_', ' ')}</h2><code className="record-id">{record.id}</code><p className="record-statement">{record.statement}</p>{record.classification && <div className="record-classification"><span>Source classification</span><strong>{record.classification}</strong></div>}<dl className="research-definition record-conditions"><div><dt>Hypotheses</dt><dd>{record.hyp && record.hyp !== 'none' ? record.hyp : 'None recorded in this entry'}</dd></div>{record.clauses && <div><dt>Clauses</dt><dd>{record.clauses}</dd></div>}{record.group && <div><dt>Research group</dt><dd>{record.group}</dd></div>}{record.physical_bridges && <div><dt>Physical bridges</dt><dd>{record.physical_bridges.join(' · ')}</dd></div>}</dl><div className="record-evidence"><div className="detail-section-heading"><h3><FileText size={14} /> Source evidence</h3></div><code>{record.evidence || 'No evidence path recorded'}</code>{record.evidence_url ? <SourceLink href={record.evidence_url} label="Read source at this revision" /> : <><p className="missing-source">Source file unavailable in this revision.</p><a className="research-source" href={`${REPO}/search?q=${encodeURIComponent(record.evidence || record.id)}&type=code`} target="_blank" rel="noreferrer">Search the repository<ArrowUpRight size={13} /></a></>}{record.verifier && <SourceLink href={`${REPO}/blob/${sourceCommit ?? 'main'}/${record.verifier}`} label="View referenced verifier" />}{record.pr && <SourceLink href={`${REPO}/pull/${record.pr}`} label={`Research pull request #${record.pr}`} />}</div><DependencyGraph record={record} records={records} onSelect={onSelect} /><div className="record-detail-foot"><DownloadButton data={record} name={`loops-${record.id.toLowerCase()}.json`} label="Export record" /><span>Labels are preserved from the source.</span></div></article>;
}

function LedgerBrowser() {
  const { data, error, retry } = useData<Ledger>('ledger.json');
  const [query, setQuery] = useState('');
  const deferredQuery = useDeferredValue(query.toLowerCase().trim());
  const [filter, setFilter] = useState('all');
  const [selectedId, setSelectedId] = useState('YOCCOZ');
  const [limit, setLimit] = useState(40);
  const records = useMemo<LedgerRecord[]>(() => data ? [...data.obligations.map(row => ({ ...row, kind: 'obligation' as const })), ...data.research_updates.map(row => ({ ...row, kind: 'update' as const }))] : [], [data]);
  const filtered = useMemo(() => {
    const terms = deferredQuery.split(/\s+/).filter(Boolean);
    return records.filter(row => (filter === 'all' || (filter === 'updates' ? row.kind === 'update' : row.status === filter)) && terms.every(term => `${row.id} ${row.statement} ${row.deps.join(' ')} ${row.hyp} ${row.classification ?? ''} ${row.group ?? ''}`.toLowerCase().includes(term)));
  }, [records, filter, deferredQuery]);
  const selected = filtered.find(row => row.id === selectedId) ?? filtered[0];
  useEffect(() => { setLimit(40); }, [deferredQuery, filter]);
  const selectRecord = (id: string) => {
    setSelectedId(id);
    if (!filtered.some(row => row.id === id)) { setQuery(''); setFilter('all'); }
    window.setTimeout(() => {
      if (window.innerWidth < 800) {
        const detail = document.querySelector<HTMLElement>('.record-detail');
        detail?.focus({ preventScroll: true });
        detail?.scrollIntoView({ behavior: window.matchMedia('(prefers-reduced-motion: reduce)').matches ? 'instant' : 'smooth', block: 'start' });
      }
    }, 0);
  };
  return <DataBoundary loading={!data} error={error} retry={retry}>
    <div className="archive-stats"><Metric label="BASELINE OBLIGATIONS" value={data?.obligations.length ?? 0} /><Metric label="SOURCE LABEL: PROVED" value={data?.counts.proved ?? 0} /><Metric label="SOURCE LABEL: OPEN" value={data?.counts.open ?? 0} /><Metric label="IMPORTED" value={data?.counts.imported ?? 0} /><Metric label="LATER UPDATES" value={data?.research_updates.length ?? 0} /></div>
    <div className="ledger-toolbar"><div className="research-search"><Search size={16} /><input aria-label="Search research ledger" placeholder="Search statements, identifiers, dependencies…" value={query} onChange={event => setQuery(event.target.value)} />{query && <button aria-label="Clear ledger search" onClick={() => setQuery('')}><X size={15} /></button>}</div><select className="ledger-filter" aria-label="Filter ledger status" value={filter} onChange={event => setFilter(event.target.value)}><option value="all">All records</option><option value="open">Open</option><option value="proved">Proved · source label</option><option value="imported">Imported</option><option value="updates">Research updates</option></select><span className="result-count">{filtered.length} records</span></div>
    <div className="ledger-layout"><div className="ledger-list" aria-label="Research records">{filtered.length === 0 ? <div className="research-empty"><Search size={22} /><h3>No records found</h3><p>Try another phrase, identifier, or status.</p><button className="research-button secondary" onClick={() => { setQuery(''); setFilter('all'); }}>Clear filters</button></div> : filtered.slice(0, limit).map(record => <button key={`${record.kind}:${record.id}`} className={`ledger-row ${record.id === selected?.id ? 'selected' : ''}`} aria-pressed={record.id === selected?.id} onClick={() => selectRecord(record.id)}><div className="ledger-row-heading"><Status status={record.status} />{record.kind === 'update' && <span className="update-label">UPDATE</span>}<ArrowRight size={13} /></div><code>{record.id}</code><p>{record.statement}</p><span className="ledger-row-foot"><GitBranch size={11} />{record.deps.length} dependencies{record.evidence_resolution === 'unresolved' && <span>Source unavailable</span>}</span></button>)}{filtered.length > limit && <button className="ledger-load-more" onClick={() => setLimit(n => n + 40)}>Load {Math.min(40, filtered.length - limit)} more records<ArrowDown size={14} /></button>}</div>{selected ? <RecordDetail record={selected} records={records} onSelect={selectRecord} sourceCommit={data?.provenance?.source_commit} /> : <div className="research-empty"><BookOpen size={24} /><p>Your research record will appear here.</p></div>}</div>
    <ScopeNote>{data?.provenance?.status_note ?? 'A proved ledger entry may be a written or conditional result; it is not automatically kernel-checked.'} The baseline counts and later updates are displayed separately. MLC remains open.</ScopeNote>
  </DataBoundary>;
}

function SourceLibrary() {
  const { data, error, retry } = useData<Catalog>('catalog.json');
  const [query, setQuery] = useState('');
  const [kind, setKind] = useState('all');
  const [limit, setLimit] = useState(36);
  const deferred = useDeferredValue(query.toLowerCase().trim());
  const filtered = useMemo(() => data?.files.filter(file => (kind === 'all' || file.kind === kind) && deferred.split(/\s+/).every(term => `${file.path} ${file.title}`.toLowerCase().includes(term))) ?? [], [data, kind, deferred]);
  useEffect(() => { setLimit(36); }, [kind, deferred]);
  const kinds = ['document', 'certificate', 'formalization', 'verifier', 'paper', 'figure'];
  return <DataBoundary loading={!data} error={error} retry={retry}><div className="library-intro"><div><h2>The complete source trail.</h2><p>{data?.files.length.toLocaleString()} documents, certificates, verifiers, formalizations, papers, and figures. Original files remain available alongside the engine.</p></div><SourceLink path="RESEARCH_MAP.md" label="Start with the research map" /></div><div className="ledger-toolbar"><div className="research-search"><Search size={16} /><input aria-label="Search source library" value={query} onChange={event => setQuery(event.target.value)} placeholder="Find a paper, verifier, certificate, or Lean module…" />{query && <button aria-label="Clear source search" onClick={() => setQuery('')}><X size={15} /></button>}</div><select aria-label="Filter source type" className="ledger-filter" value={kind} onChange={event => setKind(event.target.value)}><option value="all">All source types</option>{kinds.map(value => <option value={value} key={value}>{value[0].toUpperCase() + value.slice(1)}</option>)}</select><span className="result-count">{filtered.length} files</span></div><div className="source-grid">{filtered.slice(0, limit).map(file => <article className="source-card" key={file.path}><div className="source-card-heading">{['verifier', 'formalization'].includes(file.kind) ? <FileCode2 size={19} /> : file.kind === 'paper' ? <BookOpen size={19} /> : <FileText size={19} />}<span>{file.kind}</span><small>{file.bytes < 1024 ? `${file.bytes} B` : file.bytes < 1024 * 1024 ? `${(file.bytes / 1024).toFixed(1)} KB` : `${(file.bytes / 1048576).toFixed(1)} MB`}</small></div><h3>{file.title.replaceAll('_', ' ')}</h3><code title={file.path}>{file.path}</code><div className="source-card-links"><a href={file.url} target="_blank" rel="noreferrer">View source<ArrowUpRight size={12} /></a><a href={localAsset(file.local_url)} target="_blank" rel="noreferrer">Open file<ArrowRight size={12} /></a></div></article>)}</div>{filtered.length === 0 && <div className="research-empty"><p>No source files match those filters.</p><button className="research-button secondary" onClick={() => { setQuery(''); setKind('all'); }}>Clear filters</button></div>}{filtered.length > limit && <button className="library-load-more research-button secondary" onClick={() => setLimit(n => n + 36)}>Load {Math.min(36, filtered.length - limit)} more files<ArrowDown size={14} /></button>}<p className="archive-revision">Pinned research revision <code>{data?.source_commit.slice(0, 12)}</code>. Files open in a separate tab.</p></DataBoundary>;
}

export function Archive() {
  const [view, setView] = useState<'ledger' | 'library'>('ledger');
  return <div className="research-content archive-workspace"><ResearchHeading index="04 / RESEARCH ARCHIVE" title="Every claim has a trail." description="Explore the proof ledger, follow its dependencies, and read the evidence behind each entry."><a className="research-button secondary" href={REPO} target="_blank" rel="noreferrer">Repository<ArrowUpRight size={14} /></a></ResearchHeading><nav className="research-tabs" aria-label="Archive views"><button className={view === 'ledger' ? 'active' : ''} aria-pressed={view === 'ledger'} onClick={() => setView('ledger')}><GitBranch size={15} />Proof ledger</button><button className={view === 'library' ? 'active' : ''} aria-pressed={view === 'library'} onClick={() => setView('library')}><BookOpen size={15} />Source library</button><span className="archive-open-note"><span className="status-dot open" />MLC remains open</span></nav>{view === 'ledger' ? <LedgerBrowser /> : <SourceLibrary />}</div>;
}
