import { lazy, Suspense, useState, useEffect } from 'react';
import { Search } from 'lucide-react';
import type { EngineState } from '../types';
import { CATALOG, TOURS, catalogNumber } from './destinations';
import type { Destination } from './destinations';
import { Loading } from './UI';
const ResearchWorkspace = lazy(() =>
  import('../research/ResearchWorkspace').then((m) => ({ default: m.ResearchWorkspace })),
);
const CATEGORIES = ['All', 'Volumes', 'Complex plane', 'Research'] as const;
export function AtlasWorkspace({
  initialMode = 'places',
  onSelect,
  onTour,
  state,
  onChange,
  onExplore,
}: {
  initialMode?: 'places' | 'mathematics';
  onSelect: (d: Destination) => void;
  onTour: (id: string) => void;
  state: EngineState;
  onChange: (p: Partial<EngineState>) => void;
  onExplore: () => void;
}) {
  const [mode, setMode] = useState<'places' | 'mathematics'>(initialMode);
  const [category, setCategory] = useState<(typeof CATEGORIES)[number]>('All');
  const [query, setQuery] = useState('');
  useEffect(() => setMode(initialMode), [initialMode]);
  const visible = CATALOG.filter(
    (d) =>
      (category === 'All' || d.category === category) &&
      `${d.title} ${d.subtitle} ${d.description}`.toLowerCase().includes(query.toLowerCase()),
  );
  return (
    <div className="ob-atlas">
      <div className="ob-workspace-subnav">
        <button className={mode === 'places' ? 'active' : ''} onClick={() => setMode('places')}>
          Places and tours
        </button>
        <button
          className={mode === 'mathematics' ? 'active' : ''}
          onClick={() => setMode('mathematics')}
        >
          Mathematical atlas
        </button>
      </div>
      {mode === 'mathematics' ? (
        <Suspense fallback={<Loading />}>
          <ResearchWorkspace
            workspace="atlas"
            state={state}
            onChange={onChange}
            onExplore={onExplore}
          />
        </Suspense>
      ) : (
        <div className="ob-page-content">
          <header className="ob-page-header">
            <h1>Atlas</h1>
            <p>
              {CATALOG.length} starting views and {TOURS.length} guided tours. Each one opens in the
              live renderer, where it can be moved, re-parameterised and saved.
            </p>
          </header>
          <section className="ob-journeys" aria-labelledby="journey-title">
            <div className="ob-section-heading">
              <h2 id="journey-title">Guided tours</h2>
              <span>Stepped through at your own pace</span>
            </div>
            {TOURS.map((tour, i) => (
              <button key={tour.id} className="ob-journey-card" onClick={() => onTour(tour.id)}>
                <span className="ob-journey-number">{i + 1}</span>
                <h3>{tour.title}</h3>
                <p>{tour.description}</p>
                <small>{tour.duration}</small>
              </button>
            ))}
          </section>
          <div className="ob-atlas-toolbar">
            <div className="ob-filter-pills" role="group" aria-label="Filter destinations">
              {CATEGORIES.map((c) => (
                <button
                  key={c}
                  className={category === c ? 'active' : ''}
                  aria-pressed={category === c}
                  onClick={() => setCategory(c)}
                >
                  {c}
                </button>
              ))}
            </div>
            <label className="ob-search-field">
              <Search size={14} />
              <input
                type="search"
                aria-label="Search destinations"
                value={query}
                onChange={(e) => setQuery(e.target.value)}
                placeholder="Filter by name"
              />
            </label>
          </div>
          <div className="ob-destination-grid">
            {visible.map((d) => (
              <button className="ob-destination-card" key={d.id} onClick={() => onSelect(d)}>
                <div className="ob-destination-image">
                  <img
                    src={d.image}
                    alt={`${d.title}, computed from its fractal equation`}
                    loading="lazy"
                  />
                </div>
                <div className="ob-destination-copy">
                  <small>
                    <b>{catalogNumber(d)}</b>
                    {d.subtitle}
                  </small>
                  <h2>{d.title}</h2>
                  <p>{d.description}</p>
                </div>
              </button>
            ))}
          </div>
          {!visible.length && (
            <div className="ob-empty">
              <h2>No destination matches</h2>
              <p>Nothing in this category contains “{query}”.</p>
              <button
                className="ob-button"
                onClick={() => {
                  setQuery('');
                  setCategory('All');
                }}
              >
                Clear the filter
              </button>
            </div>
          )}
          <section className="ob-atlas-research-callout">
            <p>
              The mathematical atlas holds the exact angle portraits, puzzle pullbacks, Markov data
              and renewal experiments recorded in the research archive.
            </p>
            <button className="ob-button" onClick={() => setMode('mathematics')}>
              Open the mathematical atlas
            </button>
          </section>
        </div>
      )}
    </div>
  );
}
