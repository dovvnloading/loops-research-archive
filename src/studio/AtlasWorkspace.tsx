import { lazy, Suspense, useState, useEffect } from 'react';
import { ArrowRight, ArrowUpRight, Search, Compass, Route, Network } from 'lucide-react';
import type { EngineState } from '../types';
import { DESTINATIONS, TOURS } from './destinations';
import type { Destination } from './destinations';
import { Loading } from './UI';
const ResearchWorkspace = lazy(() =>
  import('../research/ResearchWorkspace').then((m) => ({ default: m.ResearchWorkspace })),
);
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
  const [category, setCategory] = useState('All places');
  const [query, setQuery] = useState('');
  useEffect(() => setMode(initialMode), [initialMode]);
  const visible = DESTINATIONS.filter(
    (d) =>
      (category === 'All places' || d.category === category) &&
      `${d.title} ${d.subtitle} ${d.description}`.toLowerCase().includes(query.toLowerCase()),
  );
  return (
    <div className="ob-atlas">
      <div className="ob-workspace-subnav">
        <button className={mode === 'places' ? 'active' : ''} onClick={() => setMode('places')}>
          <Compass size={15} />
          Places & journeys
        </button>
        <button
          className={mode === 'mathematics' ? 'active' : ''}
          onClick={() => setMode('mathematics')}
        >
          <Network size={15} />
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
            <div>
              <span className="ob-eyebrow">THE EXPLORER’S ATLAS</span>
              <h1>
                There is always
                <br />
                <em>somewhere further.</em>
              </h1>
              <p>
                A collection of starting points, unexpected connections, and questions worth
                following. Every place opens a live mathematical world.
              </p>
            </div>
            <div className="ob-atlas-seal">
              <span>∞</span>
              <small>
                ONE RULE
                <br />
                ENDLESS POSSIBILITY
              </small>
            </div>
          </header>
          <section className="ob-journeys" aria-labelledby="journey-title">
            <div className="ob-section-heading">
              <h2 id="journey-title">
                <Route size={17} />
                Take the scenic route
              </h2>
              <span>Self-paced guided journeys</span>
            </div>
            <div className="ob-journey-grid">
              {TOURS.map((tour, i) => (
                <button key={tour.id} className="ob-journey-card" onClick={() => onTour(tour.id)}>
                  <span className="ob-journey-number">0{i + 1}</span>
                  <div>
                    <small>{tour.duration}</small>
                    <h3>{tour.title}</h3>
                    <p>{tour.description}</p>
                  </div>
                  <ArrowUpRight size={19} />
                </button>
              ))}
            </div>
          </section>
          <div className="ob-atlas-toolbar">
            <div className="ob-filter-pills">
              {['All places', 'Volumes', 'Complex plane', 'Research'].map((c) => (
                <button
                  key={c}
                  className={category === c ? 'active' : ''}
                  onClick={() => setCategory(c)}
                >
                  {c}
                </button>
              ))}
            </div>
            <label className="ob-search-field">
              <Search size={15} />
              <input
                aria-label="Search destinations"
                value={query}
                onChange={(e) => setQuery(e.target.value)}
                placeholder="Find a place…"
              />
            </label>
          </div>
          <div className="ob-destination-grid">
            {visible.map((d, i) => (
              <button className="ob-destination-card" key={d.id} onClick={() => onSelect(d)}>
                <div className="ob-destination-image">
                  <img
                    src={d.image}
                    alt={`${d.title}, computed from its fractal equation`}
                    loading="lazy"
                  />
                  <span>{d.category}</span>
                  <i>
                    <ArrowUpRight size={19} />
                  </i>
                </div>
                <div className="ob-destination-copy">
                  <div>
                    <small>
                      {String(DESTINATIONS.indexOf(d) + 1).padStart(2, '0')} / {d.subtitle}
                    </small>
                    <h2>{d.title}</h2>
                  </div>
                  <p>{d.description}</p>
                  <span className="ob-card-link">
                    Explore this world <ArrowRight size={14} />
                  </span>
                </div>
              </button>
            ))}
          </div>
          {!visible.length && (
            <div className="ob-empty">
              <Search size={25} />
              <h2>No places found</h2>
              <p>Try a different name or reset your filters.</p>
              <button
                className="ob-button"
                onClick={() => {
                  setQuery('');
                  setCategory('All places');
                }}
              >
                Show every place
              </button>
            </div>
          )}
          <section className="ob-atlas-research-callout">
            <div>
              <span className="ob-eyebrow">GO FROM SEEING TO UNDERSTANDING</span>
              <h2>Follow the mathematics.</h2>
              <p>
                Exact angle portraits, puzzle pullbacks, Markov dynamics, and spectral experiments
                connected to the LOOPS research archive.
              </p>
            </div>
            <button className="ob-button" onClick={() => setMode('mathematics')}>
              Open mathematical atlas
              <ArrowRight size={16} />
            </button>
          </section>
        </div>
      )}
    </div>
  );
}
