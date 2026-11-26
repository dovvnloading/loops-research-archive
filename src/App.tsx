import { lazy, Suspense, useCallback, useEffect, useMemo, useRef, useState } from 'react';
import {
  ArrowDownToLine,
  ArrowLeft,
  ArrowRight,
  ArrowUpRight,
  Bookmark,
  BookOpen,
  Box,
  Check,
  ChevronDown,
  ChevronLeft,
  ChevronRight,
  CircleHelp,
  Compass,
  Copy,
  Crosshair,
  Expand,
  ExternalLink,
  FlaskConical,
  Focus,
  GitBranch,
  Globe2,
  History,
  Keyboard,
  Layers3,
  Link2,
  Maximize2,
  Minus,
  MoreHorizontal,
  Network,
  PanelLeftClose,
  PanelRightClose,
  Pause,
  Play,
  Plus,
  Redo2,
  RotateCcw,
  Route,
  Search,
  Settings2,
  SlidersHorizontal,
  Sparkles,
  Undo2,
  Upload,
  Video,
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
import { DESTINATIONS, STARTING_DESTINATION, TOURS } from './studio/destinations';
import type { Destination } from './studio/destinations';
import { Dialog, IconButton, Loading, Logo } from './studio/UI';
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
const NAV: { id: StudioWorkspace; label: string; Icon: typeof Compass }[] = [
  { id: 'explore', label: 'Explore', Icon: Compass },
  { id: 'atlas', label: 'Atlas', Icon: Globe2 },
  { id: 'laboratory', label: 'Laboratory', Icon: FlaskConical },
  { id: 'journal', label: 'Journal', Icon: Bookmark },
  { id: 'research', label: 'Research', Icon: BookOpen },
];
const SESSION_KEY = 'loops.observatory.session.v2';
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
  const [destinationId, setDestinationId] = useState(
      () =>
        DESTINATIONS.find((d) => d.engine.scene === initial.payload.engine.scene)?.id ??
        'eightfold',
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
  const destination =
    DESTINATIONS.find((d) => d.id === destinationId && d.engine.scene === engine.scene) ??
    DESTINATIONS.find((d) => d.engine.scene === engine.scene) ??
    STARTING_DESTINATION;
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
      setExact(exactViewFromEngine(next));
      setLinked(false);
      setRenderError('');
    },
    [engine],
  );
  const choose = useCallback(
    (d: Destination) => {
      setEngine(structuredClone(d.engine));
      setExact(structuredClone(d.exact));
      setDestinationId(d.id);
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
      setDestinationId('mandelbrot');
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
      notify('Journey complete. Where will you go next?');
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
      notify('Open the Share link tab to copy your view.');
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
    changeExact({
      ...exact,
      family: target.family ?? 'mandelbrot',
      center: { re: target.re, im: target.im },
      span: target.span,
      iterations: target.iterations ?? 1024,
    });
    setDestinationId('mandelbrot');
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
          <Logo />
          <span>
            LOOPS<small>AN ATLAS OF INFINITY</small>
          </span>
        </button>
        <nav aria-label="Main navigation">
          {NAV.map(({ id, label, Icon }) => (
            <button
              key={id}
              className={workspace === id ? 'active' : ''}
              onClick={() => navigate(id)}
              aria-current={workspace === id ? 'page' : undefined}
            >
              <Icon size={15} />
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
            <Search size={16} />
            <span>Search</span>
            <kbd>⌘ K</kbd>
          </button>
          <span className="ob-header-divider" />
          <IconButton label="Export image or session" onClick={() => setModal('export')}>
            <ArrowDownToLine size={17} />
          </IconButton>
          <button className="ob-button ob-save-button" onClick={openSave}>
            <Plus size={15} />
            <span>Save view</span>
          </button>
        </div>
      </header>
      <main id="main-workspace" className="ob-main" tabIndex={-1}>
        {workspace === 'explore' ? (
          <>
            <div className="ob-contextbar">
              <div>
                <button
                  onClick={() => setLibraryOpen((v) => !v)}
                  aria-label={libraryOpen ? 'Hide world library' : 'Show world library'}
                  aria-expanded={libraryOpen}
                >
                  <Layers3 size={14} />
                </button>
                <span>EXPLORER</span>
                <ChevronRight size={12} />
                <span className="ob-context-active">{destination.title}</span>
                {parentId && (
                  <span className="ob-branch-label">
                    <GitBranch size={12} />
                    Branch
                  </span>
                )}
              </div>
              <div>
                <span className="ob-live-indicator">
                  <i />
                  LIVE MATHEMATICS
                </span>
                <button onClick={() => setModal('guide')}>
                  <BookOpen size={13} />
                  <span>Field guide</span>
                </button>
                <button
                  onClick={() => setInspectorOpen((v) => !v)}
                  aria-label={inspectorOpen ? 'Hide inspector' : 'Show inspector'}
                  aria-expanded={inspectorOpen}
                >
                  <SlidersHorizontal size={14} />
                  <span>Inspector</span>
                </button>
              </div>
            </div>
            <div
              className={`ob-explorer ${libraryOpen ? 'has-library' : ''} ${inspectorOpen ? 'has-inspector' : ''}`}
            >
              {libraryOpen && (
                <aside className="ob-world-library" aria-label="World library">
                  <div className="ob-panel-top">
                    <span className="ob-eyebrow">WORLDS TO EXPLORE</span>
                    <IconButton label="Close world library" onClick={() => setLibraryOpen(false)}>
                      <PanelLeftClose size={14} />
                    </IconButton>
                  </div>
                  <div className="ob-world-list">
                    {(['Volumes', 'Complex plane', 'Research'] as const).map((category) => (
                      <section key={category}>
                        <h2>{category}</h2>
                        {DESTINATIONS.filter(
                          (d) =>
                            d.category === category &&
                            !['coral', 'cathedral', 'deep-spiral', 'dendrite'].includes(d.id),
                        ).map((d) => (
                          <button
                            key={d.id}
                            className={destination.id === d.id ? 'selected' : ''}
                            onClick={() => choose(d)}
                            aria-pressed={destination.id === d.id}
                          >
                            <img src={d.image} alt="" loading="lazy" />
                            <span>
                              <strong>{d.title}</strong>
                              <small>{d.subtitle.split(' · ')[0]}</small>
                            </span>
                            <ChevronRight size={12} />
                          </button>
                        ))}
                      </section>
                    ))}
                  </div>
                  <div className="ob-library-foot">
                    <button className="ob-journey-entry" onClick={() => startTour('first-light')}>
                      <Route size={17} />
                      <span>
                        <strong>A little guidance?</strong>
                        <small>Take the first-light journey</small>
                      </span>
                      <ArrowUpRight size={15} />
                    </button>
                    <button className="ob-library-atlas" onClick={() => navigate('atlas')}>
                      Discover the full atlas
                      <ArrowRight size={14} />
                    </button>
                  </div>
                </aside>
              )}
              <section
                className={`ob-stage ${linked && plane ? 'ob-stage-linked' : ''}`}
                ref={stage}
                aria-label="Live fractal explorer"
              >
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
                  <div className="ob-stage-vignette" />
                  <div className="ob-stage-title">
                    <span className="ob-eyebrow">
                      {plane
                        ? exact.family === 'mandelbrot'
                          ? 'THE PARAMETER PLANE'
                          : 'THE DYNAMICAL PLANE'
                        : engine.scene === 'landscape'
                          ? 'ESCAPE-TIME TOPOGRAPHY'
                          : 'MATHEMATICS IN THREE DIMENSIONS'}{' '}
                      <span>
                        / {String(DESTINATIONS.indexOf(destination) + 1).padStart(2, '0')}
                      </span>
                    </span>
                    <h1>
                      {destination.title}
                      <span>.</span>
                    </h1>
                    <p>{destination.subtitle}</p>
                  </div>
                  <div className="ob-stage-badge">
                    <span className="ob-status-dot" />
                    <span>{plane ? exact.family : engine.scene}</span>
                    <ChevronDown size={12} />
                    <button
                      aria-label="Choose another destination"
                      onClick={() => setLibraryOpen((v) => !v)}
                    />
                  </div>
                  <div className="ob-stage-equation">
                    <code>
                      {plane
                        ? 'zₙ₊₁ = zₙ² + c'
                        : engine.scene === 'mandelbulb'
                          ? `zₙ₊₁ = sphericalPower${engine.power}(zₙ) + c`
                          : engine.scene === 'mandelbox'
                            ? `zₙ₊₁ = −${engine.power} · fold(zₙ) + c`
                            : engine.scene === 'quaternion'
                              ? 'qₙ₊₁ = qₙ² + c,  q ∈ ℍ'
                              : 'h(c) = log-scaled escape time'}
                    </code>
                    <span>
                      {plane
                        ? `${exact.iterations.toLocaleString()} iterations · ${viewDepth(exact) > 0 ? `10⁻${viewDepth(exact)} window scale` : 'parameter space'}`
                        : `${engine.iterations} iterations · ${engine.camera.position ? 'free flight' : 'orbital camera'}`}
                    </span>
                  </div>
                  {plane &&
                    precisionStats &&
                    precisionStats.phase !== 'complete' &&
                    precisionStats.phase !== 'error' && (
                      <div className="ob-refinement" role="status">
                        <span>
                          {precisionStats.phase === 'preview'
                            ? 'Resolving preview'
                            : precisionStats.phase === 'repairing'
                              ? 'Refining precision'
                              : 'Resolving detail'}
                        </span>
                        <progress value={precisionStats.progress} max={1} />
                        <small>{Math.round(precisionStats.progress * 100)}%</small>
                      </div>
                    )}
                  <div className="ob-canvas-tools">
                    <div>
                      <IconButton label="Zoom in" onClick={() => zoom(0.65)}>
                        <Plus size={18} />
                      </IconButton>
                      <IconButton label="Zoom out" onClick={() => zoom(1.5)}>
                        <Minus size={18} />
                      </IconButton>
                      <span />
                      <IconButton label="Reset view (R)" onClick={reset}>
                        <RotateCcw size={16} />
                      </IconButton>
                    </div>
                    <div>
                      <IconButton
                        label="Undo view change"
                        onClick={viewHistory.undo}
                        disabled={!viewHistory.canUndo}
                      >
                        <Undo2 size={16} />
                      </IconButton>
                      <IconButton
                        label="Redo view change"
                        onClick={viewHistory.redo}
                        disabled={!viewHistory.canRedo}
                      >
                        <Redo2 size={16} />
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
                          <GitBranch size={17} />
                        </IconButton>
                      ) : (
                        <IconButton
                          label={engine.autoRotate ? 'Pause orbit' : 'Animate orbit'}
                          onClick={() =>
                            changeEngine({
                              autoRotate: !engine.autoRotate,
                              camera: {
                                yaw: engine.camera.yaw,
                                pitch: engine.camera.pitch,
                                distance: engine.camera.distance,
                              },
                            })
                          }
                          active={engine.autoRotate}
                        >
                          <Play size={16} />
                        </IconButton>
                      )}
                      <IconButton label="Save view (B)" onClick={openSave}>
                        <Bookmark size={16} />
                      </IconButton>
                      <IconButton label="Copy exact view link" onClick={() => void copyLink()}>
                        <Link2 size={16} />
                      </IconButton>
                      <span />
                      <IconButton
                        label="Focus mode (F)"
                        onClick={() => setFocus((v) => !v)}
                        active={focus}
                      >
                        <Expand size={17} />
                      </IconButton>
                    </div>
                  </div>
                  <div className="ob-interaction-hint">
                    <span>{plane ? 'Drag to pan' : 'Drag to orbit'}</span>
                    <i />
                    <span>Scroll to explore</span>
                    <i />
                    <span>
                      {plane
                        ? exact.family === 'mandelbrot'
                          ? 'Shift-click to link a Julia set'
                          : 'L · link the parameter plane'
                        : 'W A S D · fly'}
                    </span>
                  </div>
                  <div className="ob-axis" aria-hidden="true">
                    <i />
                    <span>y</span>
                    <b>x</b>
                    <em>z</em>
                  </div>
                  {renderError && (
                    <div className="ob-render-error" role="alert">
                      <h3>The renderer needs a moment.</h3>
                      <p>{renderError}</p>
                      <button
                        className="ob-button"
                        onClick={() => {
                          setRenderError('');
                          setEngineRevision((n) => n + 1);
                        }}
                      >
                        Restart renderer
                        <RotateCcw size={14} />
                      </button>
                      <button
                        className="ob-button ob-subtle"
                        onClick={() => choose(DESTINATIONS.find((d) => d.id === 'mandelbrot')!)}
                      >
                        Open the complex plane
                      </button>
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
                      <div>
                        <span className="ob-eyebrow">LINKED DYNAMICAL PLANE</span>
                        <h2>Its Julia set.</h2>
                      </div>
                      <IconButton label="Close linked view" onClick={() => setLinked(false)}>
                        <X size={17} />
                      </IconButton>
                    </div>
                    <div className="ob-linked-parameter">
                      <span>c =</span>
                      <code>
                        {Number(exact.julia.re).toPrecision(7)}{' '}
                        {Number(exact.julia.im) < 0 ? '−' : '+'}{' '}
                        {Math.abs(Number(exact.julia.im)).toPrecision(7)}i
                      </code>
                      <button
                        onClick={() => {
                          setLinkedView((v) => ({
                            ...v,
                            center: { re: '0', im: '0' },
                            span: '3.2',
                          }));
                        }}
                        aria-label="Reset linked Julia view"
                      >
                        <RotateCcw size={14} />
                      </button>
                    </div>
                    <button
                      className="ob-linked-lab"
                      onClick={() => navigate('laboratory', { instrument: 'orbit' })}
                    >
                      Examine this orbit
                      <ArrowUpRight size={13} />
                    </button>
                  </div>
                )}
                {tour && activeTour && (
                  <div className="ob-tour-card">
                    <div className="ob-tour-top">
                      <span>
                        {activeTour.title} / {tour.step + 1} OF {activeTour.stops.length}
                      </span>
                      <IconButton label="End journey" onClick={() => setTour(null)}>
                        <X size={14} />
                      </IconButton>
                    </div>
                    <h3>{destination.title}</h3>
                    <p>{destination.description}</p>
                    <div className="ob-tour-dots">
                      {activeTour.stops.map((_, i) => (
                        <button
                          aria-label={`Jump to stop ${i + 1}`}
                          key={i}
                          className={i === tour.step ? 'active' : ''}
                          onClick={() => stepTour(i)}
                        />
                      ))}
                    </div>
                    <div className="ob-tour-actions">
                      <IconButton
                        label="Previous stop"
                        onClick={() => stepTour(tour.step - 1)}
                        disabled={tour.step === 0}
                      >
                        <ArrowLeft size={16} />
                      </IconButton>
                      <button className="ob-button" onClick={() => stepTour(tour.step + 1)}>
                        {tour.step === activeTour.stops.length - 1 ? 'Keep exploring' : 'Next stop'}
                        <ArrowRight size={15} />
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
                />
              )}
            </div>
            <section className="ob-discovery-strip" aria-label="Curated starting points">
              <div className="ob-discovery-label">
                <span className="ob-eyebrow">CURIOSITY STARTS HERE</span>
                <strong>Another way in.</strong>
                <button onClick={() => navigate('atlas')}>
                  All destinations
                  <ArrowRight size={12} />
                </button>
              </div>
              <div className="ob-discovery-cards">
                {DESTINATIONS.filter((d) =>
                  [
                    'eightfold',
                    'seahorse',
                    'folded',
                    'airplane',
                    'quaternion',
                    'imaginary-gateway',
                    'deep-spiral',
                    'coral',
                  ].includes(d.id),
                ).map((d) => (
                  <button
                    key={d.id}
                    className={`ob-mini-destination ${destination.id === d.id ? 'selected' : ''}`}
                    onClick={() => choose(d)}
                  >
                    <img src={d.image} alt="" loading="lazy" />
                    <span>
                      <strong>{d.title}</strong>
                      <small>{d.subtitle}</small>
                    </span>
                    <ArrowUpRight size={13} />
                  </button>
                ))}
              </div>
            </section>
            <footer className="ob-statusbar">
              <div>
                <span className="ob-status-dot" />
                <strong>{displayStats.renderer}</strong>
                <span>{displayStats.resolution}</span>
                <span>{displayStats.precision}</span>
              </div>
              <div>
                {plane ? (
                  <span>
                    Span <code title={exact.span}>{Number(exact.span).toExponential(3)}</code>
                  </span>
                ) : (
                  <span>
                    {stats.fps ? `${stats.fps} FPS` : 'Ready'}
                    <i />
                    Adaptive detail
                  </span>
                )}
                <button onClick={() => setModal('help')}>
                  <Keyboard size={13} />
                  <span>Shortcuts</span>
                </button>
                <button onClick={() => setModal('about')} aria-label="About LOOPS">
                  <CircleHelp size={13} />
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
          <Suspense fallback={<Loading label="Preparing the laboratory…" />}>
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
                notify('Experiment restored. Run its instrument to reproduce the observation.');
              } else {
                navigate('explore');
                notify('Saved view restored. Continue exploring to create a new branch.');
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
                notify('Experiment branch ready. Adjust its settings and save the next result.');
              } else {
                navigate('explore');
                notify('Branch ready. Change the view, then save the next discovery.');
              }
            }}
          />
        ) : (
          <div className="ob-research">
            <div className="ob-workspace-subnav">
              {(
                [
                  { id: 'overview', label: 'Research overview', Icon: Network },
                  { id: 'archive', label: 'Ledger & source library', Icon: BookOpen },
                  { id: 'dynamics', label: 'Dynamics workbench', Icon: GitBranch },
                  { id: 'precision', label: 'Precision studies', Icon: Crosshair },
                ] as const
              ).map(({ id, label, Icon }) => (
                <button
                  key={id}
                  className={researchTab === id ? 'active' : ''}
                  onClick={() => setResearchTab(id)}
                >
                  <Icon size={14} />
                  {label}
                </button>
              ))}
            </div>
            <Suspense fallback={<Loading label="Opening the research archive…" />}>
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
          <Focus size={16} />
          Exit focus <kbd>F</kbd>
        </button>
      )}
      {workspace === 'explore' && !focus && (
        <div className="ob-mobile-actions">
          <button
            onClick={() => {
              setLibraryOpen((v) => !v);
              setInspectorOpen(false);
            }}
          >
            <Layers3 size={17} />
            <span>Worlds</span>
          </button>
          <button
            onClick={() => {
              setInspectorOpen((v) => !v);
              setLibraryOpen(false);
            }}
          >
            <SlidersHorizontal size={17} />
            <span>Controls</span>
          </button>
          <button onClick={openSave}>
            <Bookmark size={17} />
            <span>Save</span>
          </button>
        </div>
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
          title="Keep this discovery."
          kicker="YOUR EXPLORATION JOURNAL"
          onClose={() => {
            if (!saving) setModal(null);
          }}
          className="ob-save-dialog"
        >
          <p className="ob-dialog-intro">
            The full view is saved with exact coordinates, rendering settings, and a thumbnail. Add
            a thought to return to.
          </p>
          <form
            onSubmit={(e) => {
              e.preventDefault();
              void save();
            }}
          >
            <label className="ob-field">
              <span>Give it a name</span>
              <input
                autoFocus
                required
                maxLength={160}
                value={saveTitle}
                onChange={(e) => setSaveTitle(e.target.value)}
                placeholder="A place worth remembering"
              />
            </label>
            <label className="ob-field">
              <span>
                Field notes <small>optional</small>
              </span>
              <textarea
                rows={4}
                maxLength={20000}
                value={saveNotes}
                onChange={(e) => setSaveNotes(e.target.value)}
                placeholder="What did you notice? What would you like to investigate?"
              />
            </label>
            <label className="ob-field">
              <span>
                Tags <small>separate with commas</small>
              </span>
              <input
                value={saveTags}
                onChange={(e) => setSaveTags(e.target.value)}
                placeholder="spirals, boundary, curious"
              />
            </label>
            {parentId && (
              <div className="ob-save-branch">
                <GitBranch size={15} />
                <span>Continues from a saved discovery</span>
                <button type="button" onClick={() => setParentId(null)}>
                  Start a new root
                </button>
              </div>
            )}
            {saveError && (
              <p role="alert" className="ob-inline-error">
                {saveError}
              </p>
            )}
            <button type="submit" className="ob-button ob-primary ob-wide" disabled={saving}>
              <Bookmark size={16} />
              {saving ? 'Saving your discovery…' : 'Save to journal'}
            </button>
            <p className="ob-micro">
              Stored in this browser. Export your journal for a portable backup.
            </p>
          </form>
        </Dialog>
      )}
      {modal === 'help' && (
        <Dialog
          title="Make yourself at home."
          kicker="NAVIGATION & SHORTCUTS"
          onClose={() => setModal(null)}
          className="ob-help-dialog"
        >
          <p className="ob-dialog-intro">
            Start with a drag and a scroll. Everything else is a way to follow your curiosity.
          </p>
          <div className="ob-shortcuts">
            {[
              ['Drag', 'Orbit in 3D / pan in 2D'],
              ['Scroll / pinch', 'Zoom toward your pointer'],
              ['Shift + click', 'Choose a parameter for the linked Julia view'],
              ['W A S D · Q E', 'Fly forward, sideways, up, and down'],
              ['+ / −', 'Zoom in / out'],
              ['Arrow keys', 'Pan a focused complex-plane canvas'],
              ['Space', 'Play / pause a 3D orbit'],
              ['F', 'Enter / leave focus mode'],
              ['R', 'Reset this destination'],
              ['B / ⌘ S', 'Save a discovery'],
              ['L', 'Link / unlink a Julia view'],
              ['G', 'Open the field guide'],
              ['⌘ K / Ctrl K', 'Search destinations, tools, and sources'],
              ['⌘ Z / Ctrl Z', 'Undo · add Shift to redo'],
              ['?', 'Open this guide'],
            ].map(([key, meaning]) => (
              <div key={key}>
                <kbd>{key}</kbd>
                <span>{meaning}</span>
              </div>
            ))}
          </div>
          <div className="ob-help-actions">
            <button
              className="ob-button ob-subtle"
              onClick={() => {
                setModal(null);
                fileInput.current?.click();
              }}
            >
              <Upload size={15} />
              Import a session
            </button>
            <button className="ob-button ob-subtle" onClick={() => void fullscreen()}>
              <Maximize2 size={15} />
              Full screen
            </button>
            <button className="ob-button" onClick={() => startTour('first-light')}>
              <Route size={15} />
              Take a guided journey
            </button>
          </div>
        </Dialog>
      )}
      {modal === 'about' && (
        <Dialog
          title="A small window into infinity."
          kicker="ABOUT LOOPS"
          onClose={() => setModal(null)}
          className="ob-about-dialog"
        >
          <Logo />
          <p className="ob-dialog-intro">
            An observatory for mathematical exploration. Move through fractal worlds, follow an
            orbit, preserve a discovery, and connect it to the underlying research.
          </p>
          <div className="ob-about-grid">
            <div>
              <strong>Explore</strong>
              <p>
                Six mathematical families with interactive rendering and precision-aware navigation.
              </p>
            </div>
            <div>
              <strong>Investigate</strong>
              <p>
                Reproducible numerical experiments, exact symbolic data, and a source-linked
                research archive.
              </p>
            </div>
            <div>
              <strong>Remember</strong>
              <p>
                A local journal of exact states, notes, and branches. Export and share what you
                find.
              </p>
            </div>
          </div>
          <p className="ob-micro">
            The renderer and laboratory make numerical observations. Finite certificates and formal
            results retain their original scope. The Mandelbrot local connectivity conjecture
            remains open.
          </p>
          <a
            className="ob-button ob-subtle"
            href="https://github.com/dovvnloading/loops-research-archive"
            target="_blank"
            rel="noreferrer"
          >
            Explore the source repository
            <ArrowUpRight size={15} />
          </a>
          {manifest.data && (
            <p className="ob-about-revision">
              Research {manifest.data.source_commit.slice(0, 12)} ·{' '}
              {manifest.data.archive_files.toLocaleString()} source files
            </p>
          )}
        </Dialog>
      )}
      {notice && (
        <div className="ob-toast" role="status">
          <Check size={16} />
          <span>{notice}</span>
          <button aria-label="Dismiss notification" onClick={() => setNotice('')}>
            <X size={14} />
          </button>
        </div>
      )}
    </div>
  );
}
