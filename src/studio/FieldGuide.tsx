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
      title={`Field guide · ${destination.title}`}
      onClose={onClose}
      className="ob-guide-dialog"
    >
      <p className="ob-dialog-intro">{destination.description}</p>
      <div className="ob-guide-question">
        <span>A question to work on</span>
        <h3>{destination.question}</h3>
      </div>
      <div className="ob-guide-sections">
        <section>
          <h3>What the image shows</h3>
          <p>
            {plane
              ? 'Each pixel follows a repeated quadratic map. Escaping trajectories receive a color based on their escape time. A dark point has not escaped within the current budget; the image alone does not establish its eventual behavior.'
              : state.scene === 'landscape'
                ? 'The height encodes a finite escape-time diagnostic. It is another way to see the parameter plane; height is a display choice, not another dimension of the Mandelbrot set.'
                : 'The renderer marches a ray toward an estimated fractal surface, then uses its local shape to calculate light. More iterations and finer detail reveal more structure, at a greater computational cost.'}
          </p>
        </section>
        <section>
          <h3>{plane ? 'Next: hold one thing fixed' : 'Next: change one variable'}</h3>
          <p>
            {plane
              ? 'Compare a parameter with its Julia set, then examine the orbit of zero. Look for return patterns, escaping trajectories, and changes in the estimated attracting period.'
              : 'Save this view first. Change the power, slice, or fold scale while keeping the camera fixed. Save the result as a branch and compare both views in the journal.'}
          </p>
          <div className="ob-guide-actions">
            {plane ? (
              <>
                <button className="ob-button ob-primary" onClick={onLink}>
                  Link parameter and Julia views
                </button>
                <button className="ob-button" onClick={onLab}>
                  Examine the orbit in the laboratory
                </button>
              </>
            ) : (
              <button className="ob-button" onClick={onClose}>
                Back to the inspector
              </button>
            )}
          </div>
        </section>
        <section>
          <h3>How it connects to the research</h3>
          <p>
            The archive distinguishes numerical observations, finite symbolic certificates, imported
            results, and open mathematical obligations. Follow a claim to its source and hypotheses.
          </p>
          <div className="ob-guide-actions">
            <button className="ob-button" onClick={onAtlas}>
              Mathematical atlas
            </button>
            <button className="ob-button" onClick={onResearch}>
              Research record
            </button>
          </div>
          <a
            className="ob-source"
            href={`${REPO}/blob/${revision}/README.md`}
            target="_blank"
            rel="noreferrer"
          >
            The archive’s stated scope at this revision
          </a>
        </section>
      </div>
      <p className="ob-guide-foot">
        Current model:{' '}
        <code>
          {plane
            ? `${exact.family} · ${exact.iterations.toLocaleString()} iterations`
            : `${state.scene} · ${state.iterations} iterations`}
        </code>
        . This guide is written explanation with source links. MLC remains open.
      </p>
    </Dialog>
  );
}
