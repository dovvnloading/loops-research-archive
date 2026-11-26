import type { EngineState } from '../types';
import type { ExactView } from '../precision/types';
import { DEFAULT_STATE, CURATED, PRESETS, applyPreset } from '../presets';
import { exactViewFromEngine } from '../precision/coordinates';

export type DestinationCategory = 'Volumes' | 'Complex plane' | 'Research';
export interface Destination {
  id: string;
  title: string;
  subtitle: string;
  category: DestinationCategory;
  description: string;
  question: string;
  formula: string;
  image: string;
  engine: EngineState;
  exact: ExactView;
  color: string;
}
function place(
  id: string,
  title: string,
  subtitle: string,
  category: DestinationCategory,
  description: string,
  question: string,
  formula: string,
  patch: Partial<EngineState>,
  exact?: Partial<ExactView>,
): Destination {
  const engine = applyPreset({
    id,
    name: title,
    subtitle,
    kind: '3D FRACTAL',
    state: patch,
    description,
    formula,
  });
  return {
    id,
    title,
    subtitle,
    category,
    description,
    question,
    formula,
    engine,
    exact: { ...exactViewFromEngine(engine), ...exact },
    image: `exhibits/${id}.webp`,
    color:
      engine.palette === 'ember' ? '#e6af77' : engine.palette === 'violet' ? '#b7a0f3' : '#a5caff',
  };
}
export const DESTINATIONS: Destination[] = [
  place(
    'eightfold',
    'Eightfold',
    'Mandelbulb · power 8',
    'Volumes',
    'A single repeated operation builds a world of intricate cavities, spires, and eightfold symmetry.',
    'What changes when the power is no longer an integer?',
    'zₙ₊₁ = sphericalPower₈(zₙ) + c',
    { ...CURATED.find((p) => p.id === 'eightfold')!.state, showGrid: false, detail: 0.8 },
  ),
  place(
    'seahorse',
    'Seahorse valley',
    'Mandelbrot · boundary study',
    'Complex plane',
    'Follow the delicate spirals where the main cardioid meets its period-two neighbor. Every point describes another dynamical system.',
    'Choose a point along a filament. What happens to its Julia set?',
    'z₀ = 0  ·  zₙ₊₁ = zₙ² + c',
    {
      scene: 'mandelbrot',
      center: [-0.7435, 0.1314],
      scale: 0.006,
      iterations: 960,
      palette: 'ember',
      showGrid: false,
    },
  ),
  place(
    'folded',
    'Folded space',
    'Mandelbox · scale −2',
    'Volumes',
    'Box folds and sphere folds create recursive chambers that seem architectural, yet emerge entirely from iteration.',
    'Fly toward one corner. Can you recognize the same arrangement again?',
    'zₙ₊₁ = −2 · sphereFold(boxFold(zₙ)) + c',
    { ...PRESETS[1].state, palette: 'glacier', showGrid: false, detail: 0.8 },
  ),
  place(
    'julia',
    'The connected world',
    'Julia · a fixed parameter',
    'Complex plane',
    'Fix c and watch the fate of every initial point. Connected strands and scattered dust reveal very different dynamics.',
    'Change only the imaginary part of c and compare the boundary.',
    'zₙ₊₁ = zₙ² + (−0.74543 + 0.11301i)',
    {
      scene: 'julia',
      center: [0, 0],
      scale: 3.1,
      julia: [-0.74543, 0.11301],
      iterations: 768,
      palette: 'violet',
      showGrid: false,
    },
  ),
  place(
    'airplane',
    'The airplane cascade',
    'Period 3 → 9 → 27',
    'Research',
    'Explore the neighborhood behind the archive’s exact symbolic portraits, then trace the angle-doubling data in the mathematical atlas.',
    'How does the 3 → 9 → 27 tuning appear in the symbolic portrait?',
    'fᵨ(0) = 0  ·  p = 27',
    {
      scene: 'mandelbrot',
      center: [-1.786429858055761, 0],
      scale: 0.0012,
      iterations: 1536,
      palette: 'glacier',
      showGrid: false,
    },
    { center: { re: '-1.786429858055761', im: '0' } },
  ),
  place(
    'coral',
    'Coral bloom',
    'Mandelbulb · power 5',
    'Volumes',
    'Lower the power and the eightfold world becomes an organic arrangement of branching lobes. Light brings out its fine ridges.',
    'Compare powers 5 and 8 with the same camera and lighting.',
    'zₙ₊₁ = sphericalPower₅(zₙ) + c',
    { ...CURATED.find((p) => p.id === 'coral')!.state, showGrid: false, detail: 0.8 },
  ),
  place(
    'deep-spiral',
    'Beyond the decimal',
    'Mandelbrot · deep zoom',
    'Complex plane',
    'A finely specified center opens a much smaller window. Exact decimal coordinates survive every pan, saved view, and shared link.',
    'Increase the iteration budget. Which dark regions begin to resolve?',
    'z₀ = 0  ·  zₙ₊₁ = zₙ² + c',
    { scene: 'mandelbrot', iterations: 2400, palette: 'glacier', scale: 1e-7, showGrid: false },
    {
      center: {
        re: '-0.743643887037151007923796441120318475',
        im: '0.131825904205311970493132056385139818',
      },
      span: '0.000000000003',
      iterations: 2400,
    },
  ),
  place(
    'imaginary-gateway',
    'The imaginary gateway',
    'Mandelbrot · 120 decimal scales',
    'Complex plane',
    'An exact parameter, c = i, opens a numerically resolved window far below ordinary floating-point coordinates. Follow the same orbit across radically smaller scales.',
    'Why does this critical orbit repeat while nearby pixels eventually escape?',
    '0 → i → −1 + i → −i → −1 + i',
    {
      scene: 'mandelbrot',
      center: [0, 1],
      scale: 1e-7,
      iterations: 2048,
      palette: 'glacier',
      showGrid: false,
    },
    { center: { re: '0', im: '1' }, span: '1e-120', iterations: 2048, palette: 'aurora' },
  ),
  place(
    'quaternion',
    'Fourth dimension',
    'Quaternion Julia · slice 0.2',
    'Volumes',
    'A three-dimensional section through a four-dimensional iteration. Move the slice to watch surfaces appear, merge, and disappear.',
    'Which features persist as the fourth coordinate changes?',
    'qₙ₊₁ = qₙ² + c  ·  q ∈ ℍ',
    { ...PRESETS[2].state, palette: 'violet', slice: 0.2, showGrid: false, detail: 0.8 },
  ),
  place(
    'mandelbrot',
    'The whole map',
    'Mandelbrot · parameter plane',
    'Complex plane',
    'The familiar silhouette is a map of bounded critical orbits. Its boundary contains infinitely rich structure.',
    'Where does an attracting period change? Run an expedition to investigate.',
    'z₀ = 0  ·  zₙ₊₁ = zₙ² + c',
    {
      scene: 'mandelbrot',
      center: [-0.5, 0],
      scale: 3.2,
      iterations: 768,
      palette: 'glacier',
      showGrid: false,
    },
  ),
  place(
    'cathedral',
    'Cathedral',
    'Mandelbulb · power 12',
    'Volumes',
    'Higher power draws a dense crown of repeated forms. Use a low light angle to reveal their surface detail.',
    'What happens to the apparent symmetry at power 11.5?',
    'zₙ₊₁ = sphericalPower₁₂(zₙ) + c',
    { ...CURATED.find((p) => p.id === 'cathedral')!.state, showGrid: false, detail: 0.9 },
  ),
  place(
    'dendrite',
    'Dendritic shore',
    'Julia · c = i',
    'Complex plane',
    'A branching Julia set at a parameter whose critical orbit eventually reaches a repelling cycle.',
    'Follow the critical orbit in the laboratory. Does it repeat?',
    'zₙ₊₁ = zₙ² + i',
    {
      scene: 'julia',
      center: [0, 0],
      scale: 3.2,
      julia: [0, 1],
      iterations: 1024,
      palette: 'ember',
      showGrid: false,
    },
  ),
  place(
    'landscape',
    'Contours of escape',
    'Escape time · height field',
    'Complex plane',
    'An escape-time rendering lifted into a height field. Ridges visualize changes in a finite numerical diagnostic.',
    'How do the contours change as the iteration budget increases?',
    'h(c) = log-scaled escape time',
    { ...PRESETS[5].state, palette: 'glacier', showGrid: true },
  ),
];
export const STARTING_DESTINATION = DESTINATIONS[0];
export const INITIAL_ENGINE = { ...DEFAULT_STATE, ...STARTING_DESTINATION.engine };
export const TOURS = [
  {
    id: 'first-light',
    title: 'First light',
    description: 'Five stops from a single equation to a mathematical question.',
    duration: '5 stops',
    stops: ['eightfold', 'folded', 'mandelbrot', 'seahorse', 'airplane'],
  },
  {
    id: 'boundary',
    title: 'Along the boundary',
    description: 'Parameters, Julia sets, filaments, and smaller scales.',
    duration: '4 stops',
    stops: ['mandelbrot', 'seahorse', 'julia', 'deep-spiral'],
  },
  {
    id: 'dimensions',
    title: 'Another dimension',
    description: 'Compare power, folds, and a slice of four-dimensional space.',
    duration: '4 stops',
    stops: ['eightfold', 'coral', 'folded', 'quaternion'],
  },
];
