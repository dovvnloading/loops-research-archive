import {
  ArrowRight,
  BookOpen,
  ExternalLink,
  FlaskConical,
  GitBranch,
  ScanSearch,
} from 'lucide-react';
import type { EngineState } from '../types';
import type { ExactView } from '../precision/types';
import type { Destination } from './destinations';
import { Dialog } from './UI';
import { useData } from '../research/common';
const REPO = 'https://github.com/dovvnloading/loops-research-archive';
export function FieldGuide({
  destination,
  state,
  exact,
  onClose,
  onLab,
  onAtlas,
  onResearch,
  onLink,
}: {
  destination: Destination;
  state: EngineState;
  exact: ExactView;
  onClose: () => void;
  onLab: () => void;
  onAtlas: () => void;
  onResearch: () => void;
  onLink: () => void;
}) {
  const { data } = useData<{ source_commit: string }>('manifest.json');
  const revision = data?.source_commit ?? 'main';
  const plane = state.scene === 'mandelbrot' || state.scene === 'julia';
  return (
    <Dialog
      title="Follow your curiosity."
      kicker="THE LOOPS FIELD GUIDE"
      onClose={onClose}
      className="ob-guide-dialog"
    >
      <p className="ob-dialog-intro">{destination.description}</p>
      <div className="ob-guide-question">
        <BookOpen size={20} />
        <h3>{destination.question}</h3>
      </div>
      <div className="ob-guide-sections">
        <section>
          <span className="ob-eyebrow">01 / WHAT YOU ARE SEEING</span>
          <h3>
            {plane
              ? 'A picture of an experiment'
              : state.scene === 'landscape'
                ? 'Escape time as a landscape'
                : 'A surface defined by iteration'}
          </h3>
          <p>
            {plane
              ? 'Each pixel follows a repeated quadratic map. Escaping trajectories receive a color based on their escape time. A dark point has not escaped within your current budget; the image alone does not establish its eventual behavior.'
              : state.scene === 'landscape'
                ? 'The height encodes a finite escape-time diagnostic. It offers another way to see the parameter plane, but height is a display choice rather than another dimension of the Mandelbrot set.'
                : 'The renderer marches a ray toward an estimated fractal surface, then uses its local shape to calculate light. More iterations and finer detail reveal more structure, at a greater computational cost.'}
          </p>
        </section>
        <section>
          <span className="ob-eyebrow">02 / A USEFUL NEXT STEP</span>
          <h3>{plane ? 'Keep one thing fixed' : 'Change one variable'}</h3>
          <p>
            {plane
              ? 'Compare a parameter with its Julia set, then examine the orbit of zero. Look for return patterns, escaping trajectories, and changes in the estimated attracting period.'
              : 'Save this view first. Change the power, slice, or fold scale while keeping the camera fixed. Save the result as a branch and compare both views in your journal.'}
          </p>
          <div className="ob-guide-actions">
            {plane ? (
              <>
                <button className="ob-button" onClick={onLink}>
                  <GitBranch size={15} />
                  Link parameter & Julia views
                </button>
                <button className="ob-button ob-subtle" onClick={onLab}>
                  <FlaskConical size={15} />
                  Examine the orbit
                </button>
              </>
            ) : (
              <button className="ob-button ob-subtle" onClick={onClose}>
                Return to the inspector
                <ArrowRight size={15} />
              </button>
            )}
          </div>
        </section>
        <section>
          <span className="ob-eyebrow">03 / CONNECT TO THE RESEARCH</span>
          <h3>From a picture to a statement.</h3>
          <p>
            The archive distinguishes numerical observations, finite symbolic certificates, imported
            results, and open mathematical obligations. Follow a claim to its source and hypotheses.
          </p>
          <div className="ob-guide-actions">
            <button className="ob-button ob-subtle" onClick={onAtlas}>
              <ScanSearch size={15} />
              Trace exact angles
            </button>
            <button className="ob-button ob-subtle" onClick={onResearch}>
              <BookOpen size={15} />
              Open the research
            </button>
          </div>
          <a
            className="ob-source"
            href={`${REPO}/blob/${revision}/README.md`}
            target="_blank"
            rel="noreferrer"
          >
            Read the archive’s scope at this revision
            <ExternalLink size={12} />
          </a>
        </section>
      </div>
      <div className="ob-guide-foot">
        <span>Current model</span>
        <code>
          {plane
            ? `${exact.family} · ${exact.iterations.toLocaleString()} iterations`
            : `${state.scene} · ${state.iterations} iterations`}
        </code>
        <p>This field guide is a curated explanation with source links. MLC remains open.</p>
      </div>
    </Dialog>
  );
}
