import { lazy, Suspense, useCallback, useEffect, useMemo, useRef, useState } from 'react';
import {
  ArrowDownToLine,
  Columns2,
  Expand,
  Link2,
  Minus,
  PanelLeft,
  Pause,
  Play,
  Plus,
  Redo2,
  RotateCcw,
  Search,
  Undo2,
  X,
} from 'lucide-react';
import type { EngineState, EngineStats } from './types';
import { isPlane } from './presets';
import { validateState, readSession } from './lib/session';
import { FractalViewport } from './components/FractalViewport';
import type { ViewportHandle } from './components/FractalViewport';
import { PrecisionViewport, exactViewFromEngine, validateExactView, viewDepth } from './precision';
import type { ExactComplex, ExactView, PrecisionStats, PrecisionViewportHandle } from './precision';
import {
  JournalWorkspace,
  createSnapshotURL,
  readSharedSnapshot,
  saveEntry,
  useJournal,
  validateJournalPayload,
} from './journal';
import type { JournalEntry, JournalPayload } from './journal';
import { useData } from './research/common';
import {
  CATALOG,
  DESTINATIONS,
  STARTING_DESTINATION,
  TOURS,
  catalogNumber,
} from './studio/destinations';
import type { Destination } from './studio/destinations';
import { Dialog, Formula, IconButton, Loading, MOD, Wordmark } from './studio/UI';
import { Inspector } from './studio/Inspector';
import { AtlasWorkspace } from './studio/AtlasWorkspace';
import { CommandPalette } from './studio/CommandPalette';
import type { StudioWorkspace } from './studio/CommandPalette';
import { FieldGuide } from './studio/FieldGuide';
import { ExportDialog } from './studio/ExportDialog';
import { useViewHistory } from './studio/useHistory';
import './studio/studio.css';
const Laboratory = lazy(() =>
  import('./laboratory/Laboratory').then((m) => ({ default: m.Laboratory })),
);
const ResearchWorkspace = lazy(() =>
  import('./research/ResearchWorkspace').then((m) => ({ default: m.ResearchWorkspace })),
);
const ResearchOverview = lazy(() =>
  import('./research/ResearchOverview').then((m) => ({ default: m.ResearchOverview })),
);
const MotionStudio = lazy(() =>
  import('./studio/MotionStudio').then((m) => ({ default: m.MotionStudio })),
);

type NavigationIntent = {
  instrument?: 'discovery' | 'orbit' | 'comparison';
  atlas?: 'places' | 'mathematics';
  replay?: unknown;
};
type Modal = 'save' | 'export' | 'command' | 'guide' | 'help' | 'about' | 'motion' | null;
const NAV: { id: StudioWorkspace; label: string }[] = [
  { id: 'explore', label: 'Explore' },
  { id: 'atlas', label: 'Atlas' },
  { id: 'laboratory', label: 'Laboratory' },
  { id: 'journal', label: 'Journal' },
  { id: 'research', label: 'Research' },
];
const SESSION_KEY = 'loops.observatory.session.v2';
/** A long exact decimal, shortened for a status readout; the full string stays in the title. */
const brief = (value: string, digits = 18) =>
  value.length > digits ? `${value.slice(0, digits)}…` : value;
function destinationForView(
  value: Pick<JournalPayload, 'engine' | 'exact'>,
  title?: string,
): Destination {
  const known = DESTINATIONS.find(
    (d) =>
      JSON.stringify(d.engine) === JSON.stringify(value.engine) &&
      JSON.stringify(d.exact) === JSON.stringify(value.exact),
  );
  if (known && !title) return known;
  const related =
    DESTINATIONS.find((d) => d.engine.scene === value.engine.scene) ?? STARTING_DESTINATION;
  const names: Record<EngineState['scene'], string> = {
    mandelbulb: 'Mandelbulb',
    mandelbox: 'Mandelbox',
    quaternion: 'Quaternion Julia',
    mandelbrot: 'Mandelbrot set',
    julia: 'Julia set',
    landscape: 'Escape landscape',
  };
  return {
    ...related,
    id: `custom-${value.engine.scene}`,
    title: title?.trim() || names[value.engine.scene],
    subtitle: title
      ? `${names[value.engine.scene]} · saved observation`
      : isPlane(value.engine.scene)
        ? 'Your exact exploration window'
        : 'Your starting view',
    description:
      'This view has its own starting coordinates and rendering settings. Change one variable, save an observation, and compare what happens. Reset returns to this starting view.',
    question: isPlane(value.engine.scene)
      ? 'Which structures persist as you change the scale or iteration budget?'
      : 'Which features change when you vary the model while keeping the camera fixed?',
    engine: structuredClone(value.engine),
    exact: structuredClone(value.exact),
  };
}
const safeWorkspace = (): StudioWorkspace => {
  const hash =
    new URLSearchParams(location.search).get('workspace') || location.hash.slice(1).split('?')[0];
  const aliases: Record<string, StudioWorkspace> = {
    lab: 'laboratory',
    dynamics: 'laboratory',
    archive: 'research',
    papers: 'research',
    formal: 'research',
    ledger: 'research',
    problems: 'research',
  };
  return NAV.some((n) => n.id === hash) ? (hash as StudioWorkspace) : (aliases[hash] ?? 'explore');
};
function initialState(): { payload: JournalPayload; message: string } {
  try {
    const shared = readSharedSnapshot();
    if (shared) return { payload: shared, message: 'Shared view restored with exact coordinates.' };
  } catch (e) {
    return {
      payload: {
        engine: structuredClone(STARTING_DESTINATION.engine),
        exact: structuredClone(STARTING_DESTINATION.exact),
      },
      message: (e as Error).message,
    };
  }
  try {
    if (new URLSearchParams(location.search).has('view')) {
      const legacy = readSession();
      return {
        payload: { engine: legacy.state, exact: exactViewFromEngine(legacy.state) },
        message: 'Your previous LOOPS view has been restored.',
      };
    }
    const previous = sessionStorage.getItem(SESSION_KEY);
    if (previous) return { payload: validateJournalPayload(JSON.parse(previous)), message: '' };
  } catch {}
  return {
    payload: {
      engine: structuredClone(STARTING_DESTINATION.engine),
      exact: structuredClone(STARTING_DESTINATION.exact),
    },
    message: '',
  };
}
function snapshotThumbnail(src: string): Promise<string | undefined> {
  return new Promise((resolve) => {
    if (!src) {
      resolve(undefined);
      return;
    }
    const img = new Image();
    img.onload = () => {
      const canvas = document.createElement('canvas');
      const ratio = Math.min(1, 480 / img.naturalWidth, 320 / img.naturalHeight);
      canvas.width = Math.round(img.naturalWidth * ratio);
      canvas.height = Math.round(img.naturalHeight * ratio);
      canvas.getContext('2d')?.drawImage(img, 0, 0, canvas.width, canvas.height);
      resolve(canvas.toDataURL('image/webp', 0.82));
    };
    img.onerror = () => resolve(undefined);
    img.src = src;
  });
}

export default function App() {
  const initial = useMemo(initialState, []);
  const [engine, setEngine] = useState<EngineState>(initial.payload.engine),
    [exact, setExact] = useState<ExactView>(initial.payload.exact),
    [workspace, setWorkspace] = useState<StudioWorkspace>(safeWorkspace);
  const [originDestination, setOriginDestination] = useState<Destination>(() =>
      destinationForView(initial.payload),
    ),
    [modal, setModal] = useState<Modal>(null),
    [libraryOpen, setLibraryOpen] = useState(() => innerWidth > 1150),
    [inspectorOpen, setInspectorOpen] = useState(() => innerWidth > 960),
    [focus, setFocus] = useState(false);
  const [stats, setStats] = useState<EngineStats>({
      fps: 0,
      resolution: 'Preparing',
      precision: 'Adaptive',
      renderer: 'Initializing',
    }),
    [precisionStats, setPrecisionStats] = useState<PrecisionStats | null>(null),
    [renderError, setRenderError] = useState(''),
    [engineRevision, setEngineRevision] = useState(0);
  const [linked, setLinked] = useState(false),
    [linkedView, setLinkedView] = useState<ExactView>({
      ...STARTING_DESTINATION.exact,
      family: 'julia',
      center: { re: '0', im: '0' },
      span: '3.2',
      iterations: 768,
    });
  const [notice, setNotice] = useState(initial.message),
    [parentId, setParentId] = useState<string | null>(null),
    [saving, setSaving] = useState(false),
    [saveTitle, setSaveTitle] = useState(''),
    [saveNotes, setSaveNotes] = useState(''),
    [saveTags, setSaveTags] = useState(''),
    [saveError, setSaveError] = useState('');
  const [replay, setReplay] = useState<unknown>(undefined);
  const [labInstrument, setLabInstrument] = useState<'discovery' | 'orbit' | 'comparison'>(
    'discovery',
  );
  const [atlasMode, setAtlasMode] = useState<'places' | 'mathematics'>('places');
  const [tour, setTour] = useState<{ id: string; step: number } | null>(null),
    [researchTab, setResearchTab] = useState<'overview' | 'archive' | 'dynamics' | 'precision'>(
      'overview',
    ),
    [learnOpen, setLearnOpen] = useState(false);
  const viewport = useRef<ViewportHandle>(null),
    precisionViewport = useRef<PrecisionViewportHandle>(null),
    stage = useRef<HTMLDivElement>(null),
    fileInput = useRef<HTMLInputElement>(null),
    toastTimer = useRef<ReturnType<typeof setTimeout> | undefined>(undefined),
    cachedCapture = useRef<{ image: string; key: string } | null>(null);
  const journal = useJournal();
  const manifest = useData<{ source_commit: string; archive_files: number }>('manifest.json');
  const plane = isPlane(engine.scene),
    volume = ['mandelbulb', 'mandelbox', 'quaternion'].includes(engine.scene);
  const destination = useMemo(
    () =>
      originDestination.engine.scene === engine.scene
        ? originDestination
        : destinationForView({ engine, exact }),
    [originDestination, engine, exact],
  );
  const payload = useMemo<JournalPayload>(
    () => ({
      engine,
      exact,
      sourceRevision: manifest.data?.source_commit ?? initial.payload.sourceRevision,
    }),
    [engine, exact, manifest.data, initial],
  );
  const notify = useCallback((message: string) => {
    setNotice(message);
    clearTimeout(toastTimer.current);
    toastTimer.current = setTimeout(() => setNotice(''), 5500);
  }, []);
  const captureKey = useMemo(() => JSON.stringify({ engine, exact }), [engine, exact]);
  const capture = useCallback(() => {
    const image = plane ? precisionViewport.current?.capture() : viewport.current?.capture();
    return image || (cachedCapture.current?.key === captureKey ? cachedCapture.current.image : '');
  }, [plane, captureKey]);
  const restore = useCallback((value: JournalPayload, entry?: JournalEntry) => {
    const p = validateJournalPayload(value);
    setEngine(p.engine);
    setExact(p.exact);
    setOriginDestination(destinationForView(p, entry?.title));
    setLinkedView((v) => ({ ...v, julia: p.exact.julia }));
    setRenderError('');
    setPrecisionStats(null);
    if (entry) setParentId(entry.id);
  }, []);
  const viewHistory = useViewHistory(payload, restore);
  const navigate = useCallback(
    (next: StudioWorkspace, intent?: NavigationIntent) => {
      if (next === 'laboratory') {
        setReplay(intent?.replay);
        setLabInstrument(intent?.instrument ?? 'discovery');
      }
      if (next === 'atlas') setAtlasMode(intent?.atlas ?? 'places');
      if (workspace === 'explore') cachedCapture.current = { image: capture(), key: captureKey };
      setWorkspace(next);
      setFocus(false);
      setModal(null);
      const url = new URL(location.href);
      url.searchParams.delete('workspace');
      url.hash = next === 'explore' ? '' : next;
      if (url.href !== location.href) history.pushState(null, '', url);
    },
    [workspace, capture, captureKey],
  );
  const changeEngine = useCallback((patch: Partial<EngineState>) => {
    setEngine((s) => validateState({ ...s, ...patch }));
    if (patch.julia)
      setExact((v) => ({
        ...v,
        julia: { re: String(patch.julia![0]), im: String(patch.julia![1]) },
      }));
  }, []);
  const changeExact = useCallback(
    (value: ExactView) => {
      try {
        const next = validateExactView(value);
        setExact(next);
        setEngine((s) => ({
          ...s,
          scene: next.family,
          center: [Number(next.center.re), Number(next.center.im)],
          scale: Math.max(1e-7, Number(next.span)),
          julia: [Number(next.julia.re), Number(next.julia.im)],
          iterations: Math.min(4096, next.iterations),
          palette: next.palette === 'aurora' ? 'glacier' : next.palette,
        }));
        setRenderError('');
      } catch (e) {
        notify((e as Error).message);
      }
    },
    [notify],
  );
  const researchChange = useCallback(
    (patch: Partial<EngineState>) => {
      const next = validateState({ ...engine, ...patch });
      setEngine(next);
      const nextExact = exactViewFromEngine(next);
      setExact(nextExact);
      setOriginDestination(destinationForView({ engine: next, exact: nextExact }));
      setLinked(false);
      setRenderError('');
    },
    [engine],
  );
  const choose = useCallback(
    (d: Destination) => {
      setEngine(structuredClone(d.engine));
      setExact(structuredClone(d.exact));
      setOriginDestination(d);
      setLinkedView((v) => ({ ...v, julia: d.exact.julia }));
      setLinked(false);
      setPrecisionStats(null);
      setRenderError('');
      setParentId(null);
      setTour(null);
      navigate('explore');
      if (innerWidth < 960) {
        setLibraryOpen(false);
        setInspectorOpen(false);
      }
    },
    [navigate],
  );
  const reset = useCallback(() => {
    setEngine(structuredClone(destination.engine));
    setExact(structuredClone(destination.exact));
    setRenderError('');
    notify('Returned to the starting view.');
  }, [destination, notify]);
  const zoom = useCallback(
    (amount: number) => {
      if (plane) precisionViewport.current?.zoom(amount);
      else viewport.current?.zoom(amount);
    },
    [plane],
  );
  const selectParameter = useCallback(
    (point: ExactComplex) => {
      setExact((v) => ({ ...v, julia: point }));
      setEngine((s) => ({ ...s, julia: [Number(point.re), Number(point.im)] }));
      setLinkedView((v) => ({ ...v, julia: point }));
      setLinked(true);
      notify('Julia view linked. Shift-click another parameter to compare.');
    },
    [notify],
  );
  const openLinked = useCallback(() => {
    if (!plane) {
      choose(DESTINATIONS.find((d) => d.id === 'mandelbrot')!);
      setLinked(true);
      return;
    }
    if (exact.family === 'julia') {
      setLinkedView({ ...exact, family: 'julia' });
      changeExact({ ...exact, family: 'mandelbrot', center: { re: '-0.5', im: '0' }, span: '3.2' });
      setOriginDestination(DESTINATIONS.find((d) => d.id === 'mandelbrot')!);
    } else setLinkedView((v) => ({ ...v, julia: exact.julia, palette: exact.palette }));
    setLinked(true);
  }, [plane, choose, exact, changeExact]);
  const toggleLinked = useCallback(() => {
    if (linked) setLinked(false);
    else openLinked();
  }, [linked, openLinked]);
  const startTour = useCallback(
    (id: string) => {
      const journey = TOURS.find((t) => t.id === id);
      if (!journey) return;
      choose(DESTINATIONS.find((d) => d.id === journey.stops[0])!);
      setTour({ id, step: 0 });
    },
    [choose],
  );
  const stepTour = (step: number) => {
    if (!tour) return;
    const journey = TOURS.find((t) => t.id === tour.id)!;
    if (step < 0 || step >= journey.stops.length) {
      setTour(null);
      notify('Tour finished.');
      return;
    }
    choose(DESTINATIONS.find((d) => d.id === journey.stops[step])!);
    setTour({ id: journey.id, step });
  };
  const openSave = useCallback(() => {
    setSaveTitle(destination.title);
    setSaveNotes('');
    setSaveTags('');
    setSaveError('');
    setModal('save');
  }, [destination]);
  const save = async () => {
    if (saving) return;
    setSaving(true);
    setSaveError('');
    try {
      const thumbnail = await snapshotThumbnail(capture());
      const entry = await saveEntry({
        title: saveTitle.trim() || destination.title,
        notes: saveNotes,
        tags: saveTags
          .split(',')
          .map((t) => t.trim())
          .filter(Boolean),
        parentId,
        thumbnail,
        payload,
      });
      setParentId(entry.id);
      setModal(null);
      notify(
        journal.mode === 'memory'
          ? 'View saved for this session. Export your journal to keep it.'
          : 'View saved to your journal.',
      );
    } catch (e) {
      setSaveError((e as Error).message);
    } finally {
      setSaving(false);
    }
  };
  const copyLink = useCallback(async () => {
    try {
      await navigator.clipboard.writeText(createSnapshotURL(payload));
      notify('Reproducible view link copied.');
    } catch {
      setModal('export');
      notify('Copy the link from the Share link tab.');
    }
  }, [payload, notify]);
  const fullscreen = async () => {
    try {
      if (document.fullscreenElement) await document.exitFullscreen();
      else await document.documentElement.requestFullscreen();
    } catch {
      setFocus((v) => !v);
    }
  };
  const importSession = async (file: File) => {
    try {
      if (file.size > 24 * 1024 * 1024)
        throw new Error('Choose a session file smaller than 24 MB.');
      const data = JSON.parse(await file.text());
      let p: JournalPayload;
      if (data.format === 'loops-session' && data.version === 2)
        p = validateJournalPayload(data.payload);
      else if (data.v === 2 || data.exact) p = validateJournalPayload(data);
      else if (data.v === 1 || data.state) {
        const engine = validateState(data.state);
        p = { engine, exact: exactViewFromEngine(engine) };
      } else
        throw new Error(
          'This file is not a supported LOOPS session. Import journals from the Journal workspace.',
        );
      restore(p);
      navigate('explore');
      setParentId(null);
      notify('Session imported with its exact coordinates.');
    } catch (e) {
      notify((e as Error).message);
    } finally {
      if (fileInput.current) fileInput.current.value = '';
    }
  };
  const action = useCallback(
    (id: string) => {
      if (id === 'save') openSave();
      else if (id === 'tour') startTour('first-light');
      else if (id === 'inspector') {
        navigate('explore');
        setInspectorOpen((v) => !v);
      } else if (['guide', 'help', 'export'].includes(id)) setModal(id as Modal);
    },
    [openSave, startTour, navigate],
  );
  const labNavigate = (target: {
    re: string;
    im: string;
    span: string;
    family?: 'mandelbrot' | 'julia';
    iterations?: number;
    title?: string;
  }) => {
    const nextExact: ExactView = {
      ...exact,
      family: target.family ?? 'mandelbrot',
      center: { re: target.re, im: target.im },
      span: target.span,
      iterations: target.iterations ?? 1024,
    };
    changeExact(nextExact);
    const nextEngine = validateState({
      ...engine,
      scene: nextExact.family,
      center: [Number(target.re), Number(target.im)],
      scale: Math.max(1e-7, Number(target.span)),
      julia: [Number(nextExact.julia.re), Number(nextExact.julia.im)],
      iterations: Math.min(4096, nextExact.iterations),
      palette: nextExact.palette === 'aurora' ? 'glacier' : nextExact.palette,
    });
    setOriginDestination(destinationForView({ engine: nextEngine, exact: nextExact }));
    setLinked(false);
    navigate('explore');
    if (target.title) notify(target.title);
  };
  const saveExperiment = async (experiment: { title: string; notes: string; data: unknown }) => {
    try {
      const entry = await saveEntry({
        title: experiment.title,
        notes: experiment.notes,
        tags: ['experiment'],
        parentId,
        payload: { ...payload, experiment: experiment.data },
      });
      setParentId(entry.id);
      notify('Experiment saved to your journal with its settings and results.');
    } catch (e) {
      notify((e as Error).message);
      throw e;
    }
  };
  useEffect(() => {
    const timer = setTimeout(() => {
      try {
        sessionStorage.setItem(SESSION_KEY, JSON.stringify(payload));
      } catch {}
    }, 750);
    return () => clearTimeout(timer);
  }, [payload]);
  useEffect(() => {
    const sync = () => setWorkspace(safeWorkspace());
    window.addEventListener('popstate', sync);
    window.addEventListener('hashchange', sync);
    return () => {
      window.removeEventListener('popstate', sync);
      window.removeEventListener('hashchange', sync);
    };
  }, []);
  useEffect(() => {
    const handle = (e: KeyboardEvent) => {
      const el = e.target as HTMLElement;
      const typing = el?.closest('input,textarea,select,[contenteditable=true]');
      if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'k') {
        e.preventDefault();
        setModal((m) => (m === 'command' ? null : 'command'));
        return;
      }
      if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 's') {
        e.preventDefault();
        if (modal === 'save')
          document.querySelector<HTMLFormElement>('.ob-save-dialog form')?.requestSubmit();
        else if (!modal) openSave();
        return;
      }
      if (typing || modal) return;
      if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'z') {
        e.preventDefault();
        e.shiftKey ? viewHistory.redo() : viewHistory.undo();
        return;
      }
      if (e.key === '?') {
        e.preventDefault();
        setModal('help');
        return;
      }
      if (e.key === 'Escape') {
        setFocus(false);
        setLibraryOpen(false);
        setInspectorOpen(false);
        return;
      }
      if (workspace !== 'explore') return;
      if (e.altKey || e.metaKey || e.ctrlKey) return;
      if (el?.closest('button,a,[role=switch]') && (e.key === ' ' || e.key === 'Enter')) return;
      if (volume && ['w', 'a', 's', 'd', 'q', 'e'].includes(e.key.toLowerCase())) {
        e.preventDefault();
        viewport.current?.fly(e.key.toLowerCase());
        return;
      }
      if (e.key === 'f') {
        e.preventDefault();
        setFocus((v) => !v);
      }
      if (e.key === 'r') {
        reset();
      }
      if (e.key === 'b') {
        openSave();
      }
      if (e.key === 'l') {
        toggleLinked();
      }
      if (e.key === 'g') {
        setModal('guide');
      }
      if (e.key === ' ' && volume) {
        e.preventDefault();
        changeEngine({
          autoRotate: !engine.autoRotate,
          camera: {
            yaw: engine.camera.yaw,
            pitch: engine.camera.pitch,
            distance: engine.camera.distance,
          },
        });
      }
      if ((e.key === '+' || e.key === '=') && !plane) zoom(0.8);
      if (e.key === '-' && !plane) zoom(1.25);
    };
    window.addEventListener('keydown', handle);
    return () => window.removeEventListener('keydown', handle);
  }, [
    modal,
    workspace,
    volume,
    plane,
    engine,
    reset,
    openSave,
    toggleLinked,
    changeEngine,
    zoom,
    viewHistory,
  ]);
  useEffect(() => () => clearTimeout(toastTimer.current), []);
  const displayStats = plane && precisionStats ? precisionStats : stats;
  const activeTour = tour ? TOURS.find((t) => t.id === tour.id) : null;
  const selectedPoint: [number, number] = [Number(exact.julia.re), Number(exact.julia.im)];
  const plateNumber = catalogNumber(destination);
  const toggleOrbit = () =>
    changeEngine({
      autoRotate: !engine.autoRotate,
      camera: {
        yaw: engine.camera.yaw,
        pitch: engine.camera.pitch,
        distance: engine.camera.distance,
      },
    });
  return (
    <div
      className={`observatory ${focus ? 'ob-focus' : ''} ${workspace !== 'explore' ? 'ob-reading' : ''}`}
    >
      <a
        className="ob-skip-link"
        href="#main-workspace"
        onClick={(e) => {
          e.preventDefault();
          document.getElementById('main-workspace')?.focus();
        }}
      >
        Skip to workspace
      </a>
      <header className="ob-header">
        <button className="ob-brand" aria-label="LOOPS home" onClick={() => navigate('explore')}>
          <Wordmark />
        </button>
        <nav aria-label="Main navigation">
          {NAV.map(({ id, label }) => (
            <button
              key={id}
              className={workspace === id ? 'active' : ''}
              onClick={() => navigate(id)}
              aria-current={workspace === id ? 'page' : undefined}
            >
              <span>{label}</span>
              {id === 'journal' && journal.entries.length > 0 && <i>{journal.entries.length}</i>}
            </button>
          ))}
        </nav>
        <div className="ob-header-actions">
          <button
            className="ob-command-trigger"
            onClick={() => setModal('command')}
            aria-label="Search places and commands"
          >
            <Search size={14} />
            <span>Search</span>
            <kbd>{MOD} K</kbd>
          </button>
          <IconButton label="Export image or session" onClick={() => setModal('export')}>
            <ArrowDownToLine size={16} />
          </IconButton>
          <button className="ob-button ob-record ob-save-button" onClick={openSave}>
            Save view
          </button>
        </div>
      </header>
      <main id="main-workspace" className="ob-main" tabIndex={-1}>
        {workspace === 'explore' ? (
          <>
            <div
              className={`ob-explorer ${libraryOpen ? 'has-library' : ''} ${inspectorOpen ? 'has-inspector' : ''}`}
            >
              {libraryOpen && (
                <aside className="ob-world-library" aria-label="Index of destinations">
                  <div className="ob-panel-top">
                    <h2>Index</h2>
                    <IconButton label="Hide index" onClick={() => setLibraryOpen(false)}>
                      <X size={15} />
                    </IconButton>
                  </div>
                  <div className="ob-world-list">
                    {(['Volumes', 'Complex plane', 'Research'] as const).map((category) => (
                      <section key={category}>
                        <h3>{category}</h3>
                        {CATALOG.filter((d) => d.category === category).map((d) => (
                          <button
                            key={d.id}
                            className={destination.id === d.id ? 'selected' : ''}
                            onClick={() => choose(d)}
                            aria-pressed={destination.id === d.id}
                          >
                            <img src={d.image} alt="" loading="lazy" />
                            <span>
                              <strong>{d.title}</strong>
                              <small>
                                <b>{catalogNumber(d)}</b>
                                {d.subtitle}
                              </small>
                            </span>
                          </button>
                        ))}
                      </section>
                    ))}
                  </div>
                  <div className="ob-library-foot">
                    <h3>Guided tours</h3>
                    {TOURS.map((t) => (
                      <button
                        key={t.id}
                        className="ob-journey-entry"
                        onClick={() => startTour(t.id)}
                      >
                        <span>{t.title}</span>
                        <small>{t.duration}</small>
                      </button>
                    ))}
                    <button className="ob-library-atlas" onClick={() => navigate('atlas')}>
                      Open the atlas
                    </button>
                  </div>
                </aside>
              )}
              <section
                className={`ob-stage ${linked && plane ? 'ob-stage-linked' : ''}`}
                ref={stage}
                aria-label="Live fractal explorer"
              >
                <div className="ob-platebar">
                  <div className="ob-plate-caption">
                    {!libraryOpen && (
                      <button
                        className="ob-bar-button"
                        aria-label="Show index"
                        aria-expanded={false}
                        onClick={() => {
                          setLibraryOpen(true);
                          if (innerWidth < 960) setInspectorOpen(false);
                        }}
                      >
                        <PanelLeft size={15} />
                        <span>Index</span>
                      </button>
                    )}
                    {plateNumber && <span className="ob-plate-no">{plateNumber}</span>}
                    <h1 className="ob-context-active">{destination.title}</h1>
                    <span className="ob-plate-kind">{destination.subtitle}</span>
                    <Formula scene={plane ? exact.family : engine.scene} power={engine.power} />
                    {parentId && <span className="ob-branch-label">branch</span>}
                  </div>
                  <div className="ob-canvas-tools" role="toolbar" aria-label="View tools">
                    <IconButton label="Zoom in" onClick={() => zoom(0.65)}>
                      <Plus size={16} />
                    </IconButton>
                    <IconButton label="Zoom out" onClick={() => zoom(1.5)}>
                      <Minus size={16} />
                    </IconButton>
                    <IconButton label="Reset view (R)" onClick={reset}>
                      <RotateCcw size={15} />
                    </IconButton>
                    <span />
                    <IconButton
                      label="Undo view change"
                      onClick={viewHistory.undo}
                      disabled={!viewHistory.canUndo}
                    >
                      <Undo2 size={15} />
                    </IconButton>
                    <IconButton
                      label="Redo view change"
                      onClick={viewHistory.redo}
                      disabled={!viewHistory.canRedo}
                    >
                      <Redo2 size={15} />
                    </IconButton>
                    <span />
                    {plane ? (
                      <IconButton
                        label={
                          exact.family === 'julia'
                            ? 'Link parameter plane (L)'
                            : 'Link Julia view (L)'
                        }
                        onClick={toggleLinked}
                        active={linked}
                      >
                        <Columns2 size={15} />
                      </IconButton>
                    ) : (
                      <IconButton
                        label={engine.autoRotate ? 'Pause orbit' : 'Animate orbit'}
                        onClick={toggleOrbit}
                        active={engine.autoRotate}
                      >
                        {engine.autoRotate ? <Pause size={15} /> : <Play size={15} />}
                      </IconButton>
                    )}
                    <IconButton label="Copy exact view link" onClick={() => void copyLink()}>
                      <Link2 size={15} />
                    </IconButton>
                    <IconButton
                      label="Focus mode (F)"
                      onClick={() => setFocus((v) => !v)}
                      active={focus}
                    >
                      <Expand size={15} />
                    </IconButton>
                  </div>
                  <div className="ob-plate-panels">
                    <button className="ob-bar-button" onClick={() => setModal('guide')}>
                      Field guide
                    </button>
                    {!inspectorOpen && (
                      <button
                        className="ob-bar-button"
                        aria-label="Show inspector"
                        aria-expanded={false}
                        onClick={() => {
                          setInspectorOpen(true);
                          if (innerWidth < 960) setLibraryOpen(false);
                        }}
                      >
                        Inspector
                      </button>
                    )}
                  </div>
                </div>
                <div className="ob-plates">
                  <div className="ob-main-viewport">
                    {plane ? (
                      <PrecisionViewport
                        key={`precision-${engineRevision}`}
                        ref={precisionViewport}
                        view={exact}
                        onViewChange={changeExact}
                        onStats={setPrecisionStats}
                        onInspect={exact.family === 'mandelbrot' ? selectParameter : undefined}
                        onError={setRenderError}
                        className="ob-fractal-canvas"
                        quality={engine.quality}
                        exposure={engine.exposure}
                      />
                    ) : (
                      <FractalViewport
                        key={`volume-${engineRevision}`}
                        ref={viewport}
                        state={engine}
                        hooks={{
                          onChange: changeEngine,
                          onStats: setStats,
                          onError: (message) => {
                            if (
                              /Using the Float64|Float64 worker is rendering|CPU Mandelbrot view is available/i.test(
                                message,
                              )
                            ) {
                              setRenderError('');
                              notify(message);
                            } else setRenderError(message);
                          },
                          onSelectParameter: (c) =>
                            selectParameter({ re: String(c[0]), im: String(c[1]) }),
                        }}
                        className="ob-fractal-canvas"
                      />
                    )}
                    {plane &&
                      precisionStats &&
                      precisionStats.phase !== 'complete' &&
                      precisionStats.phase !== 'error' && (
                        <div className="ob-refinement" role="status">
                          <progress value={precisionStats.progress} max={1} />
                          <span>
                            {precisionStats.phase === 'preview'
                              ? 'Resolving preview'
                              : precisionStats.phase === 'repairing'
                                ? 'Refining precision'
                                : 'Resolving detail'}
                          </span>
                          <small>{Math.round(precisionStats.progress * 100)}%</small>
                        </div>
                      )}
                    {renderError && (
                      <div className="ob-render-error" role="alert">
                        <h3>Rendering stopped</h3>
                        <p>{renderError}</p>
                        <div>
                          <button
                            className="ob-button ob-primary"
                            onClick={() => {
                              setRenderError('');
                              setEngineRevision((n) => n + 1);
                            }}
                          >
                            Restart renderer
                          </button>
                          <button
                            className="ob-button"
                            onClick={() => choose(DESTINATIONS.find((d) => d.id === 'mandelbrot')!)}
                          >
                            Open the Mandelbrot plane
                          </button>
                        </div>
                      </div>
                    )}
                  </div>
                  {linked && plane && (
                    <div className="ob-linked-viewport">
                      <PrecisionViewport
                        view={{ ...linkedView, julia: exact.julia, palette: exact.palette }}
                        onViewChange={setLinkedView}
                        quality="balanced"
                        exposure={engine.exposure}
                        onError={(message) => notify(message)}
                        className="ob-fractal-canvas"
                      />
                      <div className="ob-linked-header">
                        <h2>Julia set</h2>
                        <span className="ob-linked-parameter">
                          <span className="math">
                            <i>c</i> =
                          </span>{' '}
                          <code>
                            {Number(exact.julia.re).toPrecision(7)}{' '}
                            {Number(exact.julia.im) < 0 ? '−' : '+'}{' '}
                            {Math.abs(Number(exact.julia.im)).toPrecision(7)}i
                          </code>
                        </span>
                        <button
                          className="ob-bar-button"
                          aria-label="Reset linked Julia view"
                          onClick={() => {
                            setLinkedView((v) => ({
                              ...v,
                              center: { re: '0', im: '0' },
                              span: '3.2',
                            }));
                          }}
                        >
                          Reset
                        </button>
                        <button
                          className="ob-bar-button ob-linked-lab"
                          onClick={() => navigate('laboratory', { instrument: 'orbit' })}
                        >
                          Orbit in laboratory
                        </button>
                        <IconButton label="Close linked view" onClick={() => setLinked(false)}>
                          <X size={15} />
                        </IconButton>
                      </div>
                    </div>
                  )}
                </div>
                {tour && activeTour && (
                  <div className="ob-tour-card">
                    <div className="ob-tour-top">
                      <span>
                        {activeTour.title} · stop {tour.step + 1} of {activeTour.stops.length}
                      </span>
                      <IconButton label="End journey" onClick={() => setTour(null)}>
                        <X size={14} />
                      </IconButton>
                    </div>
                    <h3>{destination.title}</h3>
                    <p>{destination.description}</p>
                    <p className="ob-tour-question">{destination.question}</p>
                    <div className="ob-tour-actions">
                      <button
                        className="ob-button"
                        onClick={() => stepTour(tour.step - 1)}
                        disabled={tour.step === 0}
                      >
                        Previous
                      </button>
                      <button
                        className="ob-button ob-primary"
                        onClick={() => stepTour(tour.step + 1)}
                      >
                        {tour.step === activeTour.stops.length - 1 ? 'Finish' : 'Next stop'}
                      </button>
                    </div>
                  </div>
                )}
              </section>
              {inspectorOpen && (
                <Inspector
                  state={engine}
                  exact={exact}
                  destination={destination}
                  onChange={changeEngine}
                  onExact={(v) => {
                    if (plane) changeExact(v);
                    else setExact(v);
                  }}
                  onReset={reset}
                  onFly={(key) => viewport.current?.fly(key)}
                  onGuide={() => setModal('guide')}
                  onMotion={() => setModal('motion')}
                  onClose={() => setInspectorOpen(false)}
                />
              )}
            </div>
            <footer className="ob-statusbar">
              <div className="ob-status-render">
                <strong>{displayStats.renderer}</strong>
                <span>{displayStats.resolution}</span>
                <span>{displayStats.precision}</span>
              </div>
              <div className="ob-status-view">
                {plane ? (
                  <>
                    <span title={exact.center.re}>
                      Re <b>{brief(exact.center.re)}</b>
                    </span>
                    <span title={exact.center.im}>
                      Im <b>{brief(exact.center.im)}</b>
                    </span>
                    <span>
                      Span <code title={exact.span}>{Number(exact.span).toExponential(3)}</code>
                    </span>
                    <span>
                      <b>{exact.iterations.toLocaleString()}</b> iterations
                    </span>
                  </>
                ) : (
                  <>
                    <span>
                      <b>{stats.fps ? stats.fps : '–'}</b> fps
                    </span>
                    <span>
                      <b>{engine.iterations}</b> iterations
                    </span>
                    <span>{engine.camera.position ? 'Free flight' : 'Orbit camera'}</span>
                  </>
                )}
              </div>
              <div className="ob-status-help">
                <span className="ob-interaction-hint">
                  {plane
                    ? exact.family === 'mandelbrot'
                      ? 'Drag to pan · scroll to zoom · shift-click for a Julia set'
                      : 'Drag to pan · scroll to zoom · L links the parameter plane'
                    : 'Drag to orbit · scroll to approach · W A S D to fly'}
                </span>
                <button onClick={() => setModal('help')}>Shortcuts</button>
                <button onClick={() => setModal('about')} aria-label="About LOOPS">
                  About
                </button>
              </div>
            </footer>
          </>
        ) : workspace === 'atlas' ? (
          <AtlasWorkspace
            initialMode={atlasMode}
            onSelect={choose}
            onTour={startTour}
            state={engine}
            onChange={researchChange}
            onExplore={() => navigate('explore')}
          />
        ) : workspace === 'laboratory' ? (
          <Suspense fallback={<Loading label="Loading the laboratory…" />}>
            <Laboratory
              parameter={selectedPoint}
              replay={replay}
              initialInstrument={labInstrument}
              onNavigate={labNavigate}
              onSaveExperiment={saveExperiment}
            />
          </Suspense>
        ) : workspace === 'journal' ? (
          <JournalWorkspace
            onRestore={(p, entry) => {
              restore(p, entry);
              if (p.experiment) {
                navigate('laboratory', { replay: p.experiment });
                notify('Experiment restored. Run its instrument to reproduce the result.');
              } else {
                navigate('explore');
                notify('Saved view restored. The next save will branch from it.');
              }
            }}
            onNew={() => {
              navigate('explore');
              openSave();
            }}
            onBranch={(p, entry) => {
              restore(p, entry);
              if (p.experiment) {
                navigate('laboratory', { replay: p.experiment });
                notify('Branch started. Adjust the settings and save the next result.');
              } else {
                navigate('explore');
                notify('Branch started. Change the view, then save it.');
              }
            }}
          />
        ) : (
          <div className="ob-research">
            <div className="ob-workspace-subnav">
              {(
                [
                  { id: 'overview', label: 'Overview' },
                  { id: 'archive', label: 'Ledger & source library' },
                  { id: 'dynamics', label: 'Dynamics workbench' },
                  { id: 'precision', label: 'Precision studies' },
                ] as const
              ).map(({ id, label }) => (
                <button
                  key={id}
                  className={researchTab === id ? 'active' : ''}
                  onClick={() => setResearchTab(id)}
                >
                  {label}
                </button>
              ))}
            </div>
            <Suspense fallback={<Loading label="Loading the research archive…" />}>
              {researchTab === 'overview' ? (
                <ResearchOverview
                  onBrowse={() => setResearchTab('archive')}
                  onAtlas={() => navigate('atlas', { atlas: 'mathematics' })}
                  onLab={() => navigate('laboratory')}
                />
              ) : (
                <ResearchWorkspace
                  workspace={researchTab === 'precision' ? 'lab' : researchTab}
                  state={engine}
                  onChange={researchChange}
                  onExplore={() => navigate('explore')}
                />
              )}
            </Suspense>
          </div>
        )}
      </main>
      {focus && (
        <button className="ob-exit-focus" onClick={() => setFocus(false)}>
          Exit focus <kbd>F</kbd>
        </button>
      )}
      <input
        type="file"
        accept="application/json,.json"
        hidden
        ref={fileInput}
        onChange={(e) => {
          const file = e.target.files?.[0];
          if (file) void importSession(file);
        }}
      />
      {modal === 'command' && (
        <CommandPalette
          onClose={() => setModal(null)}
          onSelect={choose}
          onNavigate={navigate}
          onAction={action}
        />
      )}
      {modal === 'guide' && (
        <FieldGuide
          destination={destination}
          state={engine}
          exact={exact}
          onClose={() => setModal(null)}
          onLab={() => navigate('laboratory', { instrument: 'orbit' })}
          onAtlas={() => navigate('atlas', { atlas: 'mathematics' })}
          onResearch={() => navigate('research')}
          onLink={() => {
            navigate('explore');
            openLinked();
          }}
        />
      )}
      {modal === 'export' && (
        <ExportDialog
          payload={payload}
          capture={capture}
          aspect={(() => {
            const box = stage.current?.querySelector('.ob-main-viewport')?.getBoundingClientRect();
            return box && box.height > 0 ? box.width / box.height : 1.5;
          })()}
          onClose={() => setModal(null)}
        />
      )}
      {modal === 'motion' && (
        <Suspense fallback={<Loading />}>
          <MotionStudio
            state={engine}
            onChange={changeEngine}
            capture={capture}
            getCanvas={() =>
              stage.current?.querySelector<HTMLCanvasElement>(
                '.ob-main-viewport > canvas.ob-fractal-canvas',
              ) ?? null
            }
            onClose={() => setModal(null)}
            notify={notify}
          />
        </Suspense>
      )}
      {modal === 'save' && (
        <Dialog
          title="Save view"
          onClose={() => {
            if (!saving) setModal(null);
          }}
          className="ob-save-dialog"
        >
          <p className="ob-dialog-intro">
            The journal entry keeps the exact coordinates, the render settings and a thumbnail.
          </p>
          <form
            onSubmit={(e) => {
              e.preventDefault();
              void save();
            }}
          >
            <label className="ob-field">
              <span>Title</span>
              <input
                name="title"
                autoFocus
                required
                maxLength={160}
                value={saveTitle}
                onChange={(e) => setSaveTitle(e.target.value)}
              />
            </label>
            <label className="ob-field">
              <span>
                Notes <small>optional</small>
              </span>
              <textarea
                name="notes"
                rows={4}
                maxLength={20000}
                value={saveNotes}
                onChange={(e) => setSaveNotes(e.target.value)}
                placeholder="What you observed, and what to check next"
              />
            </label>
            <label className="ob-field">
              <span>
                Tags <small>comma-separated</small>
              </span>
              <input
                name="tags"
                value={saveTags}
                onChange={(e) => setSaveTags(e.target.value)}
                placeholder="boundary, period 3"
              />
            </label>
            {parentId && (
              <div className="ob-save-branch">
                <span>Saved as a branch of the previous entry.</span>
                <button type="button" className="ob-link" onClick={() => setParentId(null)}>
                  Save as a new root
                </button>
              </div>
            )}
            {saveError && (
              <p role="alert" className="ob-inline-error">
                {saveError}
              </p>
            )}
            <button type="submit" className="ob-button ob-record ob-wide" disabled={saving}>
              {saving ? 'Saving…' : 'Save to journal'}
            </button>
            <p className="ob-micro">
              Stored in this browser only. Export the journal for a portable copy.
            </p>
          </form>
        </Dialog>
      )}
      {modal === 'help' && (
        <Dialog
          title="Controls and shortcuts"
          onClose={() => setModal(null)}
          className="ob-help-dialog"
        >
          <dl className="ob-shortcuts">
            {[
              ['Drag', 'Orbit a volume, pan a plane'],
              ['Scroll, pinch', 'Zoom about the pointer'],
              ['Shift + click', 'Pick the parameter for the linked Julia set'],
              ['W A S D, Q E', 'Fly forward, sideways, down and up'],
              ['+ −', 'Zoom in and out'],
              ['Arrow keys', 'Pan a focused plane, rotate a focused volume'],
              ['Space', 'Start or pause the orbit animation'],
              ['F', 'Focus mode'],
              ['R', 'Reset to the starting view'],
              [`B, ${MOD} S`, 'Save the view to the journal'],
              ['L', 'Link or unlink the Julia view'],
              ['G', 'Field guide'],
              [`${MOD} K`, 'Search destinations, commands and sources'],
              [`${MOD} Z`, 'Undo a view change; add Shift to redo'],
              ['?', 'This list'],
            ].map(([key, meaning]) => (
              <div key={key}>
                <dt>{key}</dt>
                <dd>{meaning}</dd>
              </div>
            ))}
          </dl>
          <div className="ob-help-actions">
            <button
              className="ob-button"
              onClick={() => {
                setModal(null);
                fileInput.current?.click();
              }}
            >
              Import a session
            </button>
            <button className="ob-button" onClick={() => void fullscreen()}>
              Full screen
            </button>
            <button className="ob-button" onClick={() => startTour('first-light')}>
              Start the First light tour
            </button>
          </div>
        </Dialog>
      )}
      {modal === 'about' && (
        <Dialog title="About LOOPS" onClose={() => setModal(null)} className="ob-about-dialog">
          <p className="ob-dialog-intro">
            LOOPS renders fractal volumes and the complex plane, runs numerical experiments on
            quadratic dynamics, keeps a journal of exact views, and presents the research archive
            those views belong to.
          </p>
          <dl className="ob-about-grid">
            <div>
              <dt>Explore</dt>
              <dd>
                Six families. GPU and Float64 rendering, with exact decimal coordinates on the plane
                down to a span of 10⁻²⁰⁰.
              </dd>
            </div>
            <div>
              <dt>Laboratory</dt>
              <dd>
                Parameter surveys, critical-orbit analysis and window comparison, each at a stated
                precision and budget.
              </dd>
            </div>
            <div>
              <dt>Journal</dt>
              <dd>
                Saved views and experiments with notes and branches. Kept in this browser,
                exportable as JSON.
              </dd>
            </div>
            <div>
              <dt>Research</dt>
              <dd>
                The obligation ledger, the source library and the Lean formalization, pinned to one
                revision.
              </dd>
            </div>
          </dl>
          <p className="ob-micro">
            Images and experiments are numerical observations. Finite certificates and formal
            results keep their original scope. The Mandelbrot local connectivity conjecture remains
            open.
          </p>
          <p className="ob-about-revision">
            {manifest.data && (
              <>
                Research revision <code>{manifest.data.source_commit.slice(0, 12)}</code> ·{' '}
                {manifest.data.archive_files.toLocaleString()} source files ·{' '}
              </>
            )}
            <a
              href="https://github.com/dovvnloading/loops-research-archive"
              target="_blank"
              rel="noreferrer"
            >
              Source repository
            </a>
          </p>
        </Dialog>
      )}
      {notice && (
        <div className="ob-toast" role="status">
          <span>{notice}</span>
          <button aria-label="Dismiss notification" onClick={() => setNotice('')}>
            <X size={14} />
          </button>
        </div>
      )}
    </div>
  );
}
