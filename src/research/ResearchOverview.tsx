import { useMemo, useState } from 'react';
import type { ReactNode } from 'react';
import {
  ArrowRight,
  ArrowUpRight,
  BookOpen,
  Braces,
  Check,
  ChevronDown,
  Copy,
  Database,
  FileCheck2,
  FlaskConical,
  GitBranch,
  Microscope,
  Network,
  Search,
  ShieldCheck,
} from 'lucide-react';
import { REPO, useData } from './common';
import './research-overview.css';

interface Dataset {
  id: string;
  source_path: string;
  source_url: string;
  scope: string;
  sha256: string;
}
interface Manifest {
  source_commit: string;
  input_sha256: string;
  mlc_status: string;
  counts: {
    obligations: number;
    research_updates: number;
    imported: number;
    proved: number;
    open: number;
  };
  datasets: Dataset[];
  archive_files: number;
  unresolved_evidence: { id: string; evidence: string }[];
}
interface Obligation {
  id: string;
  status: string;
  statement: string;
  deps: string[];
  hyp: string;
  evidence_url: string | null;
  evidence_path: string | null;
}
interface Ledger {
  obligations: Obligation[];
  research_updates: unknown[];
  provenance: { source_commit: string; status_note: string };
}
interface CatalogFile {
  path: string;
  title: string;
  kind: string;
  url: string;
  sha256: string;
  bytes: number;
}
interface Catalog {
  source_commit: string;
  files: CatalogFile[];
}
export interface ResearchOverviewProps {
  onBrowse: () => void;
  onAtlas: () => void;
  onLab: () => void;
}

const GATES = [
  {
    key: 'H1_MARKED_CONSTRUCTION',
    short: 'H1',
    title: 'Realize the protected object',
    question: 'Can every required marked carrier be constructed?',
    description:
      'Construct the actual planar carriers, branch maps, protected accesses, and sheet labels throughout the tower. Keep all witnesses on the same parameter and carrier.',
    anchor: 'gate-h1',
  },
  {
    key: 'H2_CALIBRATION',
    short: 'H2',
    title: 'Calibrate and transport',
    question: 'Do the modeled observables control physical quantities?',
    description:
      'Prove the declared width comparisons and error budgets, then establish the backward transition on that same tower with uniform constants.',
    anchor: 'gate-h2',
  },
  {
    key: 'H3_COERCIVITY',
    short: 'H3',
    title: 'Prevent analytic degeneration',
    question: 'Do controlled sequences have admissible limits?',
    description:
      'Preserve nondegenerate domains, maps, protected ends, and response data through a common subsequence in the required marked topology.',
    anchor: 'gate-h3',
  },
  {
    key: 'H4_RIGIDITY',
    short: 'H4',
    title: 'Recover the parameter',
    question: 'Do the limits determine connected parameter neighborhoods?',
    description:
      'Supply rigidity and nested connected relative neighborhoods whose intersection is the marked parameter fiber. Parameter uniqueness alone leaves a further obligation.',
    anchor: 'gate-h4',
  },
];

function External({
  href,
  children,
  className = '',
}: {
  href: string;
  children: ReactNode;
  className?: string;
}) {
  return (
    <a href={href} target="_blank" rel="noreferrer" className={`ro-source ${className}`}>
      {children}
      <ArrowUpRight size={13} />
    </a>
  );
}

export function ResearchOverview({ onBrowse, onAtlas, onLab }: ResearchOverviewProps) {
  const manifest = useData<Manifest>('manifest.json'),
    ledger = useData<Ledger>('ledger.json'),
    catalog = useData<Catalog>('catalog.json');
  const [query, setQuery] = useState(''),
    [copied, setCopied] = useState(false),
    [copyError, setCopyError] = useState('');
  const m = manifest.data,
    l = ledger.data,
    c = catalog.data;
  const revision = m?.source_commit;
  const source = (path: string) => `${REPO}/blob/${revision ?? 'main'}/${path}`;
  const search = useMemo(() => {
    const q = query.trim().toLocaleLowerCase();
    if (q.length < 2)
      return { files: [] as CatalogFile[], obligations: [] as Obligation[], total: 0 };
    const words = q.split(/\s+/),
      files = (c?.files ?? []).filter((f) =>
        words.every((word) => `${f.title} ${f.path} ${f.kind}`.toLocaleLowerCase().includes(word)),
      );
    const obligations = (l?.obligations ?? []).filter((o) =>
      words.every((word) =>
        `${o.id} ${o.statement} ${o.status} ${o.hyp}`.toLocaleLowerCase().includes(word),
      ),
    );
    return {
      files: files.slice(0, 5),
      obligations: obligations.slice(0, 4),
      total: files.length + obligations.length,
    };
  }, [query, c, l]);
  const unresolvedFiles = new Set(
    m?.unresolved_evidence.map((e) => e.evidence.split('#')[0]) ?? [],
  );
  const terminal = l?.obligations.find((o) => o.id === 'UPTCR_IMPLIES_MLC');
  const error = manifest.error || ledger.error || catalog.error;
  const totals = m?.counts;
  return (
    <div className="research-overview">
      <header className="ro-header">
        <div>
          <span className="ro-eyebrow">
            <GitBranch size={13} />
            THE RESEARCH RECORD
          </span>
          <h1>
            Beautiful questions.
            <br />
            <em>Traceable answers.</em>
          </h1>
          <p>
            Follow a claim from the picture that suggested it to the evidence that supports it—and
            the assumptions still waiting to be established.
          </p>
        </div>
        <div className="ro-status-card">
          <span className="ro-status-heading">
            <span />
            CURRENT GLOBAL STATUS
          </span>
          <strong>{m?.mlc_status ?? 'MLC remains open'}</strong>
          <p>
            Finite experiments and formal statements retain their stated scope. The universal
            physical bridge remains an open research program.
          </p>
          <External href={source('RESEARCH_MAP.md')}>Read the research map</External>
        </div>
      </header>
      <div className="ro-source-bar">
        <div>
          <Database size={14} />
          <span>SOURCE REVISION</span>
          {revision ? (
            <a href={`${REPO}/commit/${revision}`} target="_blank" rel="noreferrer">
              <code>{revision.slice(0, 12)}</code>
              <ArrowUpRight size={11} />
            </a>
          ) : (
            <code>Loading…</code>
          )}
        </div>
        <span>
          {m
            ? `${m.datasets.length} instrument datasets · ${m.archive_files.toLocaleString()} indexed source files`
            : 'Loading the evidence inventory…'}
        </span>
        {revision && (
          <button
            aria-label="Copy full research source revision"
            onClick={() => {
              navigator.clipboard
                .writeText(revision)
                .then(() => {
                  setCopied(true);
                  setCopyError('');
                  setTimeout(() => setCopied(false), 1800);
                })
                .catch(() =>
                  setCopyError(
                    'Copy unavailable. Select the revision link to inspect its complete value.',
                  ),
                );
            }}
          >
            {copied ? <Check size={13} /> : <Copy size={13} />}
            {copied ? 'Copied' : 'Copy revision'}
          </button>
        )}
      </div>
      {copyError && (
        <div className="ro-notice" role="status">
          {copyError}
        </div>
      )}
      {error && (
        <div className="ro-load-error" role="alert">
          <span>{error}</span>
          <button
            onClick={() => {
              manifest.retry();
              ledger.retry();
              catalog.retry();
            }}
          >
            Reload research data
          </button>
        </div>
      )}
      <section className="ro-search-section" aria-label="Search research evidence">
        <div className="ro-search-box">
          <Search size={18} />
          <input
            aria-label="Search the research record"
            value={query}
            onChange={(e) => setQuery(e.target.value)}
            placeholder="Search a theorem, obligation, source, or question…"
          />
          <span>{query.trim().length >= 2 ? `${search.total} results` : 'SOURCE + LEDGER'}</span>
        </div>
        {query.trim().length >= 2 && (
          <div className="ro-search-results">
            {search.total === 0 ? (
              <p>No matching record. Try “rigidity”, “period27”, “renewal”, or “H1”.</p>
            ) : (
              <>
                {search.obligations.map((o) => (
                  <div className="ro-search-result" key={o.id}>
                    <div>
                      <span className={`ro-label ro-label-${o.status}`}>
                        {o.status === 'proved' && o.hyp !== 'none'
                          ? 'CONDITIONAL SOURCE CLAIM'
                          : o.status.toUpperCase()}
                      </span>
                      <h3>{o.id.replaceAll('_', ' ')}</h3>
                      <p>{o.statement}</p>
                      {o.hyp !== 'none' && <small>Explicit hypothesis: {o.hyp}</small>}
                    </div>
                    {o.evidence_url ? (
                      <External href={o.evidence_url}>Evidence</External>
                    ) : (
                      <span className="ro-unresolved">Unresolved source pointer</span>
                    )}
                  </div>
                ))}
                {search.files.map((f) => (
                  <a
                    className="ro-file-result"
                    key={f.path}
                    href={f.url}
                    target="_blank"
                    rel="noreferrer"
                  >
                    <BookOpen size={15} />
                    <div>
                      <span>{f.title}</span>
                      <code>{f.path}</code>
                    </div>
                    <span>{f.kind}</span>
                    <ArrowUpRight size={13} />
                  </a>
                ))}
                <button className="ro-search-browse" onClick={onBrowse}>
                  Open the full research archive
                  <ArrowRight size={14} />
                </button>
              </>
            )}
          </div>
        )}
      </section>
      <section className="ro-inventory" aria-label="Original obligation inventory">
        <div className="ro-inventory-heading">
          <span className="ro-eyebrow">ORIGINAL SOURCE LEDGER</span>
          <h2>A record of claims and their status.</h2>
          <p>These are inventory labels, with later updates recorded separately.</p>
        </div>
        <div className="ro-inventory-numbers">
          <div>
            <strong>{totals?.imported.toLocaleString() ?? '—'}</strong>
            <span>Imported results</span>
            <small>External source inputs</small>
          </div>
          <div>
            <strong>{totals?.proved.toLocaleString() ?? '—'}</strong>
            <span>Archive-internal “proved”</span>
            <small>Written or conditional claims</small>
          </div>
          <div>
            <strong>{totals?.open.toLocaleString() ?? '—'}</strong>
            <span>Open obligations</span>
            <small>Explicit unfinished interfaces</small>
          </div>
        </div>
        <div className="ro-inventory-footer">
          <span>
            {totals
              ? `${totals.obligations} canonical obligations · ${totals.research_updates} later research records`
              : 'Loading source counts…'}
          </span>
          <External href={source('formalization/LEDGER_EVIDENCE_CROSSWALK.md')}>
            How to read these labels
          </External>
        </div>
      </section>
      <section className="ro-evidence-section">
        <div className="ro-section-heading">
          <div>
            <span className="ro-eyebrow">FROM EXPLORATION TO EVIDENCE</span>
            <h2>Every transition needs its own argument.</h2>
          </div>
          <span className="ro-section-note">THREE DISTINCT KINDS OF EVIDENCE</span>
        </div>
        <div className="ro-evidence-grid">
          <article className="ro-evidence-card">
            <div className="ro-evidence-icon">
              <Microscope size={22} strokeWidth={1.4} />
            </div>
            <span className="ro-label ro-label-numerical">NUMERICAL OBSERVATION</span>
            <h3>Notice a pattern.</h3>
            <p>
              An orbit approaches a cycle. A miniature resembles a larger structure. An experiment
              isolates a parameter worth investigating.
            </p>
            <div className="ro-example">
              <span>TRY AN EXPERIMENT</span>
              <strong>A period candidate near the airplane</strong>
              <p>
                Retain its coordinates, iteration budget, return tolerance, and numerical residual.
              </p>
            </div>
            <button onClick={onLab}>
              Open the Laboratory
              <ArrowRight size={14} />
            </button>
          </article>
          <article className="ro-evidence-card">
            <div className="ro-evidence-icon">
              <Braces size={22} strokeWidth={1.4} />
            </div>
            <span className="ro-label ro-label-finite">EXACT FINITE CERTIFICATE</span>
            <h3>Check the finite relation.</h3>
            <p>
              Integer and rational arithmetic can verify a precise symbolic statement while
              preserving every digit and assumption.
            </p>
            <div className="ro-example">
              <span>INSPECT A REAL CERTIFICATE</span>
              <strong>Period-27 symbolic marking</strong>
              <p>
                The exact angular and finite symbolic relations have a stated scope. Physical
                parameter-ray landing needs additional input.
              </p>
            </div>
            <button onClick={onAtlas}>
              Explore the exact Atlas
              <ArrowRight size={14} />
            </button>
            <External href={source('results/period27_symbolic_marking.json')}>
              Original certificate
            </External>
          </article>
          <article className="ro-evidence-card">
            <div className="ro-evidence-icon">
              <ShieldCheck size={22} strokeWidth={1.4} />
            </div>
            <span className="ro-label ro-label-formal">FORMAL STATEMENT</span>
            <h3>State what the proof uses.</h3>
            <p>
              A kernel checks a formal theorem in its declared model. Applying it to a physical
              dynamical system requires the named realization bridges.
            </p>
            <div className="ro-example">
              <span>READ THE HYPOTHESES</span>
              <strong>Same-carrier gate composition</strong>
              <p>
                ResearchGates composes supplied inputs on one carrier. Its conditional conclusion
                keeps those inputs visible.
              </p>
            </div>
            <External href={source('ResearchGates.lean')}>Inspect the Lean statement</External>
            <External href={source('formalization/PHYSICAL_BRIDGES_CONTRACTS.md')}>
              Read the physical contracts
            </External>
          </article>
        </div>
        <div className="ro-evidence-connector">
          <span />
          <div>
            <GitBranch size={14} />
            PHYSICAL REALIZATION · THE SAME PARAMETER, CARRIER, MAPS, AND SCOPE
          </div>
          <span />
        </div>
      </section>
      <section className="ro-gates-section">
        <div className="ro-section-heading">
          <div>
            <span className="ro-eyebrow">THE UNIVERSAL BRIDGE</span>
            <h2>Four questions that remain open.</h2>
            <p>
              Each gate must hold on the same physical tower, with the required quantifiers and
              uniform constants.
            </p>
          </div>
          <External
            href={source(
              'formalization/PHYSICAL_BRIDGES_CONTRACTS.md#the-same-parameter-and-carrier-through-the-reduction',
            )}
          >
            Read the bridge register
          </External>
        </div>
        <div className="ro-gates-grid">
          {GATES.map((g) => {
            const obligation = l?.obligations.find((o) => o.id === g.key);
            return (
              <article className="ro-gate" key={g.key}>
                <div className="ro-gate-top">
                  <span>{g.short}</span>
                  <span className="ro-label ro-label-open">
                    {obligation?.status.toUpperCase() ?? 'OPEN'}
                  </span>
                </div>
                <h3>{g.title}</h3>
                <h4>{g.question}</h4>
                <p>{g.description}</p>
                <details>
                  <summary>
                    Inspect the source obligation
                    <ChevronDown size={13} />
                  </summary>
                  <p>{obligation?.statement ?? 'Loading the original ledger statement…'}</p>
                  {obligation && (
                    <span className="ro-gate-deps">
                      {obligation.deps.length} recorded dependencies
                    </span>
                  )}
                  {obligation?.evidence_url && (
                    <External href={obligation.evidence_url}>Ledger evidence</External>
                  )}
                </details>
                <External href={source(`formalization/PHYSICAL_BRIDGES_CONTRACTS.md#${g.anchor}`)}>
                  Physical contract
                </External>
              </article>
            );
          })}
        </div>
        <div className="ro-terminal">
          <div className="ro-terminal-formula">
            <span>H1–H4</span>
            <ArrowRight size={17} />
            <span>Universal package</span>
            <ArrowRight size={17} />
            <span>MLC</span>
          </div>
          <div>
            <span className="ro-label ro-label-conditional">CONDITIONAL COMPOSITION</span>
            <p>
              The archive records an implication from the Universal Protected-Tower Compactness and
              Rigidity package, together with the complementary theorem. Its universal hypothesis
              remains open.
            </p>
            <code>
              {terminal?.id ?? 'UPTCR_IMPLIES_MLC'} · hypothesis:{' '}
              {terminal?.hyp ?? 'UNIVERSAL_PROTECTED_TOWER_CLOSURE'}
            </code>
          </div>
          <External
            href={
              terminal?.evidence_url ?? source('research/mlc_unified/uptcr_cross_validation.md')
            }
          >
            Read the exact implication
          </External>
        </div>
      </section>
      <section className="ro-audit-section">
        <div className="ro-audit-summary">
          <span className="ro-eyebrow">
            <FileCheck2 size={13} />
            RECORDED VERIFICATION AUDIT · 25 NOV 2026
          </span>
          <h2>
            Formal evidence,
            <br />
            with its boundary intact.
          </h2>
          <p>
            The audit records complete source coverage and successful builds at its stated proof
            revision. The final recorded inventory contains 99 Lean files and 880 named public
            theorems and lemmas. Its compiled axiom audit checks 3,112 declarations, including
            private and generated declarations.
          </p>
          <p>
            Those counts describe different inventories. They do not count independent physical
            theorems or measure progress toward MLC.
          </p>
          <External href={source('formalization/LEAN_VERIFICATION_20261125.md')}>
            Read the complete verification audit
          </External>
          <div className="ro-audit-revision">
            <span>VERIFIED PROOF REVISION</span>
            <a
              href={`${REPO}/commit/a9dcbb89f6a6105f36610de0be930002b01f25bb`}
              target="_blank"
              rel="noreferrer"
            >
              a9dcbb89f6a6
              <ArrowUpRight size={11} />
            </a>
          </div>
        </div>
        <div className="ro-audit-items">
          <article>
            <span className="ro-audit-number">01</span>
            <div>
              <h3>Finite native-mark grammar</h3>
              <p>
                The complete 191-state grammar reaches the full circle within five pushes. Physical
                native-action identification retains its imported inputs and geometric obligations.
              </p>
              <External href={source('NativeMarkSaturation.lean')}>
                NativeMarkSaturation.lean
              </External>
            </div>
          </article>
          <article>
            <span className="ro-audit-number">02</span>
            <div>
              <h3>Actual clone characteristic polynomial</h3>
              <p>
                The formalization identifies the actual adjacency matrix’s polynomial, proves root
                simplicity and finite gap nonuniformity. The newer cubic renewal asymptotic remains
                written.
              </p>
              <External href={source('formalization/weighted/FullCloneCharpoly.lean')}>
                FullCloneCharpoly.lean
              </External>
            </div>
          </article>
          <article>
            <span className="ro-audit-number">03</span>
            <div>
              <h3>Declared axiom dependencies</h3>
              <p>
                The recorded compiled audit admits only propext, Classical.choice, and Quot.sound.
                Coverage checks and kernel evidence have separate roles.
              </p>
              <div className="ro-ci-links">
                <External href={`${REPO}/actions/runs/45707763753`}>
                  Root + standalone evidence
                </External>
                <External href={`${REPO}/actions/runs/45707763695`}>
                  Weighted audit evidence
                </External>
              </div>
            </div>
          </article>
        </div>
      </section>
      <section className="ro-next-section">
        <div className="ro-section-heading">
          <div>
            <span className="ro-eyebrow">USEFUL NEXT QUESTIONS</span>
            <h2>Work at a boundary you can name.</h2>
          </div>
        </div>
        <div className="ro-next-grid">
          <a
            href={source('formalization/LEAN_VERIFICATION_20261125.md#4-ranked-next-lean-tasks')}
            target="_blank"
            rel="noreferrer"
          >
            <Network size={20} />
            <h3>Extend the exact formal model</h3>
            <p>
              The audit prioritizes the actual 26-edge real Markov spectrum, return counts, and the
              clone stationary law.
            </p>
            <span>
              Ranked formalization tasks
              <ArrowUpRight size={13} />
            </span>
          </a>
          <a href={source('formalization/PHYSICAL_BRIDGES.md')} target="_blank" rel="noreferrer">
            <GitBranch size={20} />
            <h3>Inspect a realization bridge</h3>
            <p>
              Trace the passage from finite geometry and symbolic data to the actual maps, widths,
              and marked paths.
            </p>
            <span>
              Physical bridge register
              <ArrowUpRight size={13} />
            </span>
          </a>
          <button onClick={onLab}>
            <FlaskConical size={20} />
            <h3>Make a reproducible observation</h3>
            <p>
              Save a precise parameter, test its orbit, and carry the numerical record into the next
              question.
            </p>
            <span>
              Start an experiment
              <ArrowRight size={13} />
            </span>
          </button>
        </div>
      </section>
      <footer className="ro-footer">
        <div>
          <span className="ro-eyebrow">PROVENANCE STAYS VISIBLE</span>
          <p>
            {m
              ? `${m.unresolved_evidence.length} ledger evidence pointers refer to ${unresolvedFiles.size} absent Markdown files in the source inventory.`
              : 'The source manifest records unresolved evidence pointers explicitly.'}{' '}
            The evidence crosswalk records alternative arguments and remaining gaps.
          </p>
          <External href={source('formalization/LEDGER_EVIDENCE_CROSSWALK.md#ledger-evidence')}>
            Inspect the evidence crosswalk
          </External>
        </div>
        <button className="ro-browse-button" onClick={onBrowse}>
          <BookOpen size={16} />
          Browse the complete archive
          <ArrowRight size={15} />
        </button>
      </footer>
    </div>
  );
}
