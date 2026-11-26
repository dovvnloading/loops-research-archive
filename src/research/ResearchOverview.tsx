import { useEffect, useMemo, useState } from 'react';
import type { ReactNode } from 'react';
import { ArrowUpRight, Search } from 'lucide-react';
import { REPO, useData } from './common';
import { AGENT_LINE, openTargets } from './targets';
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
      <ArrowUpRight size={12} />
    </a>
  );
}

export function ResearchOverview({ onBrowse, onAtlas, onLab }: ResearchOverviewProps) {
  const manifest = useData<Manifest>('manifest.json'),
    ledger = useData<Ledger>('ledger.json'),
    catalog = useData<Catalog>('catalog.json');
  const [query, setQuery] = useState(''),
    [copied, setCopied] = useState(false),
    [copyError, setCopyError] = useState(''),
    [lineCopy, setLineCopy] = useState<'idle' | 'copied' | 'failed'>('idle');
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
  const targets = useMemo(() => (l ? openTargets(l.obligations) : null), [l]);
  const living = (path: string) => `${REPO}/blob/main/${path}`;
  const loaded = Boolean(l);
  useEffect(() => {
    // A link to #contribute opens this workspace; bring the section into view once it has its height.
    if (loaded && location.hash.slice(1).split('?')[0] === 'contribute')
      document.getElementById('contribute')?.scrollIntoView({ block: 'start' });
  }, [loaded]);
  const error = manifest.error || ledger.error || catalog.error;
  const totals = m?.counts;
  return (
    <div className="research-overview">
      <header className="ro-header">
        <h1>Research record</h1>
        <p>
          Each claim is listed with the evidence that supports it and the hypotheses it still
          depends on.
        </p>
      </header>
      <dl className="ro-front">
        <div className="ro-status-card">
          <dt>Status</dt>
          <dd>
            <strong>{m?.mlc_status ?? 'MLC remains open'}</strong>
            <p>
              Finite experiments and formal statements retain their stated scope. The universal
              physical bridge remains an open research program.
            </p>
            <External href={source('RESEARCH_MAP.md')}>Research map</External>
          </dd>
        </div>
        <div className="ro-source-bar">
          <dt>Source revision</dt>
          <dd>
            {revision ? (
              <a href={`${REPO}/commit/${revision}`} target="_blank" rel="noreferrer">
                <code>{revision.slice(0, 12)}</code>
              </a>
            ) : (
              <code>Loading…</code>
            )}
            <span>
              {m
                ? `${m.datasets.length} instrument datasets · ${m.archive_files.toLocaleString()} indexed source files`
                : 'Loading the evidence inventory…'}
            </span>
            {revision && (
              <button
                className="ob-link"
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
                {copied ? 'Copied' : 'Copy full revision'}
              </button>
            )}
          </dd>
        </div>
      </dl>
      {copyError && (
        <div className="ro-notice" role="status">
          {copyError}
        </div>
      )}
      {error && (
        <div className="ro-load-error" role="alert">
          <span>{error}</span>
          <button
            className="ob-button"
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
        <label className="ro-search-box">
          <Search size={15} />
          <input
            type="search"
            aria-label="Search the research record"
            value={query}
            onChange={(e) => setQuery(e.target.value)}
            placeholder="Search obligations and source files, for example rigidity, period27, H1"
          />
          <span>{query.trim().length >= 2 ? `${search.total} results` : 'Ledger and sources'}</span>
        </label>
        {query.trim().length >= 2 && (
          <div className="ro-search-results">
            {search.total === 0 ? (
              <p>No obligation or source file matches “{query.trim()}”.</p>
            ) : (
              <>
                {search.obligations.map((o) => (
                  <div className="ro-search-result" key={o.id}>
                    <div>
                      <h3>
                        <code>{o.id}</code>
                        <span className={`ro-label ro-label-${o.status}`}>
                          {o.status === 'proved' && o.hyp !== 'none'
                            ? 'conditional source claim'
                            : o.status}
                        </span>
                      </h3>
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
                    <div>
                      <span>{f.title}</span>
                      <code>{f.path}</code>
                    </div>
                    <span>{f.kind}</span>
                  </a>
                ))}
                <button className="ob-link ro-search-browse" onClick={onBrowse}>
                  All results in the ledger and source library
                </button>
              </>
            )}
          </div>
        )}
      </section>
      <section className="ro-section ro-inventory" aria-labelledby="ro-ledger">
        <div className="ro-section-heading">
          <h2 id="ro-ledger">Obligation ledger</h2>
          <p>Inventory labels at the source lock. Later updates are recorded separately.</p>
        </div>
        <div>
          <table className="ro-inventory-numbers">
            <tbody>
              <tr>
                <td>{totals?.imported.toLocaleString() ?? '—'}</td>
                <th scope="row">Imported results</th>
                <td>External source inputs</td>
              </tr>
              <tr>
                <td>{totals?.proved.toLocaleString() ?? '—'}</td>
                <th scope="row">Archive-internal “proved”</th>
                <td>Written or conditional claims</td>
              </tr>
              <tr>
                <td>{totals?.open.toLocaleString() ?? '—'}</td>
                <th scope="row">Open obligations</th>
                <td>Explicit unfinished interfaces</td>
              </tr>
            </tbody>
          </table>
          <p className="ro-inventory-footer">
            {totals
              ? `${totals.obligations} canonical obligations · ${totals.research_updates} later research records`
              : 'Loading source counts…'}
            <External href={source('formalization/LEDGER_EVIDENCE_CROSSWALK.md')}>
              How to read these labels
            </External>
            <button className="ob-link" onClick={onBrowse}>
              Open the ledger
            </button>
          </p>
        </div>
      </section>
      <section className="ro-section" id="contribute" aria-labelledby="ro-contribute">
        <div className="ro-section-heading">
          <h2 id="ro-contribute">Contribute with an agent</h2>
          <p>One line briefs any coding agent. The repository tells it the rest.</p>
        </div>
        <div className="ro-contribute">
          <div className="ro-agent-line">
            <code>{AGENT_LINE}</code>
            <button
              className="ob-button ob-primary"
              onClick={() => {
                navigator.clipboard
                  .writeText(AGENT_LINE)
                  .then(() => {
                    setLineCopy('copied');
                    setTimeout(() => setLineCopy('idle'), 1800);
                  })
                  .catch(() => setLineCopy('failed'));
              }}
            >
              {lineCopy === 'copied' ? 'Copied' : 'Copy line'}
            </button>
          </div>
          {lineCopy === 'failed' && (
            <p className="ro-notice" role="status">
              Copy unavailable. Click the line to select it, then copy it.
            </p>
          )}
          <p>
            Paste it into Claude Code, Codex, Cursor, Gemini CLI, or another agent that can run
            commands. The agent takes an open obligation nobody has claimed, works in its own
            folder, and opens a pull request that the repository checks. You need a free GitHub
            account. Closing an obligation advances the conditional reduction; MLC remains open.
          </p>
          <p className="ro-contribute-links">
            <External href={living('AGENTS.md')}>Agent briefing</External>
            <External href={living('OPEN_TARGETS.md')}>All open targets</External>
            <External href={living('CONTRIBUTING.md')}>Contribution standard</External>
            <External href={`${REPO}/pulls`}>Work in progress</External>
          </p>
          <h3>
            {targets
              ? `${targets.ready.length} of ${targets.open} open obligations can be started today`
              : 'Loading the open obligations…'}
          </h3>
          <p className="ro-target-note">
            Every prerequisite of these is already proved or imported. Most depended-on first.
          </p>
          <ol className="ro-target-list">
            {targets?.ready.slice(0, 5).map((target) => (
              <li key={target.id}>
                <div>
                  <code>{target.id}</code>
                  <span>{target.downstream} obligations depend on it</span>
                </div>
                <p>{target.statement}</p>
              </li>
            ))}
          </ol>
        </div>
      </section>
      <section className="ro-section" aria-labelledby="ro-evidence">
        <div className="ro-section-heading">
          <h2 id="ro-evidence">Three kinds of evidence</h2>
          <p>
            A picture, a finite certificate and a formal theorem establish different things. Each
            step from one to the next needs its own argument.
          </p>
        </div>
        <div>
          <div className="ro-evidence-grid">
            <article className="ro-evidence-card">
              <h3>Numerical observation</h3>
              <p>
                An orbit approaches a cycle. A miniature resembles a larger structure. An experiment
                isolates a parameter worth investigating.
              </p>
              <div className="ro-example">
                <span>Example</span>
                <strong>A period candidate near the airplane</strong>
                <p>
                  Retain its coordinates, iteration budget, return tolerance, and numerical
                  residual.
                </p>
              </div>
              <button className="ob-link" onClick={onLab}>
                Open the laboratory
              </button>
            </article>
            <article className="ro-evidence-card">
              <h3>Exact finite certificate</h3>
              <p>
                Integer and rational arithmetic can verify a precise symbolic statement while
                preserving every digit and assumption.
              </p>
              <div className="ro-example">
                <span>Example</span>
                <strong>Period-27 symbolic marking</strong>
                <p>
                  The exact angular and finite symbolic relations have a stated scope. Physical
                  parameter-ray landing needs additional input.
                </p>
              </div>
              <button className="ob-link" onClick={onAtlas}>
                Open the mathematical atlas
              </button>
              <External href={source('results/period27_symbolic_marking.json')}>
                Original certificate
              </External>
            </article>
            <article className="ro-evidence-card">
              <h3>Formal statement</h3>
              <p>
                A kernel checks a formal theorem in its declared model. Applying it to a physical
                dynamical system requires the named realization bridges.
              </p>
              <div className="ro-example">
                <span>Example</span>
                <strong>Same-carrier gate composition</strong>
                <p>
                  ResearchGates composes supplied inputs on one carrier. Its conditional conclusion
                  keeps those inputs visible.
                </p>
              </div>
              <External href={source('ResearchGates.lean')}>Lean statement</External>
              <External href={source('formalization/PHYSICAL_BRIDGES_CONTRACTS.md')}>
                Physical contracts
              </External>
            </article>
          </div>
          <p className="ro-evidence-connector">
            Physical realization requires the same parameter, carrier, maps and scope at every step.
          </p>
        </div>
      </section>
      <section className="ro-section" aria-labelledby="ro-gates">
        <div className="ro-section-heading">
          <h2 id="ro-gates">Four open gates</h2>
          <p>
            Each gate must hold on the same physical tower, with the required quantifiers and
            uniform constants.
          </p>
          <External
            href={source(
              'formalization/PHYSICAL_BRIDGES_CONTRACTS.md#the-same-parameter-and-carrier-through-the-reduction',
            )}
          >
            Bridge register
          </External>
        </div>
        <div>
          <div className="ro-gates-grid">
            {GATES.map((g) => {
              const obligation = l?.obligations.find((o) => o.id === g.key);
              return (
                <article className="ro-gate" key={g.key}>
                  <div className="ro-gate-top">
                    <span>{g.short}</span>
                    <span className="ro-label ro-label-open">{obligation?.status ?? 'open'}</span>
                  </div>
                  <div>
                    <h3>{g.title}</h3>
                    <h4>{g.question}</h4>
                    <p>{g.description}</p>
                    <details>
                      <summary>Source obligation</summary>
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
                    <External
                      href={source(`formalization/PHYSICAL_BRIDGES_CONTRACTS.md#${g.anchor}`)}
                    >
                      Physical contract
                    </External>
                  </div>
                </article>
              );
            })}
          </div>
          <div className="ro-terminal">
            <p className="ro-terminal-formula math">H1–H4 ⟹ universal package ⟹ MLC</p>
            <div>
              <span className="ro-label ro-label-conditional">conditional composition</span>
              <p>
                The archive records an implication from the Universal Protected-Tower Compactness
                and Rigidity package, together with the complementary theorem. Its universal
                hypothesis remains open.
              </p>
              <code>
                {terminal?.id ?? 'UPTCR_IMPLIES_MLC'} · hypothesis:{' '}
                {terminal?.hyp ?? 'UNIVERSAL_PROTECTED_TOWER_CLOSURE'}
              </code>
              <External
                href={
                  terminal?.evidence_url ?? source('research/mlc_unified/uptcr_cross_validation.md')
                }
              >
                The exact implication
              </External>
            </div>
          </div>
        </div>
      </section>
      <section className="ro-section ro-audit-section" aria-labelledby="ro-audit">
        <div className="ro-section-heading">
          <h2 id="ro-audit">Verification audit, 25 November 2026</h2>
          <p className="ro-audit-revision">
            Verified proof revision{' '}
            <a
              href={`${REPO}/commit/a9dcbb89f6a6105f36610de0be930002b01f25bb`}
              target="_blank"
              rel="noreferrer"
            >
              <code>a9dcbb89f6a6</code>
            </a>
          </p>
        </div>
        <div>
          <div className="ro-audit-summary">
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
              The complete verification audit
            </External>
          </div>
          <ol className="ro-audit-items">
            <li>
              <h3>Finite native-mark grammar</h3>
              <p>
                The complete 191-state grammar reaches the full circle within five pushes. Physical
                native-action identification retains its imported inputs and geometric obligations.
              </p>
              <External href={source('NativeMarkSaturation.lean')}>
                NativeMarkSaturation.lean
              </External>
            </li>
            <li>
              <h3>Actual clone characteristic polynomial</h3>
              <p>
                The formalization identifies the actual adjacency matrix’s polynomial, proves root
                simplicity and finite gap nonuniformity. The newer cubic renewal asymptotic remains
                written.
              </p>
              <External href={source('formalization/weighted/FullCloneCharpoly.lean')}>
                FullCloneCharpoly.lean
              </External>
            </li>
            <li>
              <h3>Declared axiom dependencies</h3>
              <p>
                The recorded compiled audit admits only propext, Classical.choice, and Quot.sound.
                Coverage checks and kernel evidence have separate roles.
              </p>
              <span className="ro-ci-links">
                <External href={`${REPO}/actions/runs/45707763753`}>
                  Root and standalone evidence
                </External>
                <External href={`${REPO}/actions/runs/45707763695`}>
                  Weighted audit evidence
                </External>
              </span>
            </li>
          </ol>
        </div>
      </section>
      <section className="ro-section" aria-labelledby="ro-next">
        <div className="ro-section-heading">
          <h2 id="ro-next">Open work</h2>
          <p>Three places where the next step is already named.</p>
        </div>
        <div className="ro-next-grid">
          <a
            href={source('formalization/LEAN_VERIFICATION_20261125.md#4-ranked-next-lean-tasks')}
            target="_blank"
            rel="noreferrer"
          >
            <h3>Extend the exact formal model</h3>
            <p>
              The audit prioritizes the actual 26-edge real Markov spectrum, return counts, and the
              clone stationary law.
            </p>
            <span>Ranked formalization tasks</span>
          </a>
          <a href={source('formalization/PHYSICAL_BRIDGES.md')} target="_blank" rel="noreferrer">
            <h3>Inspect a realization bridge</h3>
            <p>
              Trace the passage from finite geometry and symbolic data to the actual maps, widths,
              and marked paths.
            </p>
            <span>Physical bridge register</span>
          </a>
          <button onClick={onLab}>
            <h3>Make a reproducible observation</h3>
            <p>
              Save a precise parameter, test its orbit, and carry the numerical record into the next
              question.
            </p>
            <span>Laboratory</span>
          </button>
        </div>
      </section>
      <footer className="ro-footer">
        <p>
          {m
            ? `${m.unresolved_evidence.length} ledger evidence pointers refer to ${unresolvedFiles.size} absent Markdown files in the source inventory.`
            : 'The source manifest records unresolved evidence pointers explicitly.'}{' '}
          The evidence crosswalk records alternative arguments and remaining gaps.{' '}
          <External href={source('formalization/LEDGER_EVIDENCE_CROSSWALK.md#ledger-evidence')}>
            Evidence crosswalk
          </External>
        </p>
        <button className="ob-button ro-browse-button" onClick={onBrowse}>
          Browse the ledger and source library
        </button>
      </footer>
    </div>
  );
}
