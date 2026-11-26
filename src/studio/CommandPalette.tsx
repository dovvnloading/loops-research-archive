import { useEffect, useId, useMemo, useRef, useState } from 'react';
import {
  ArrowUpRight,
  Search,
  Compass,
  FlaskConical,
  BookOpen,
  Bookmark,
  Settings2,
  Image,
  Keyboard,
  Route,
  Network,
} from 'lucide-react';
import { DESTINATIONS } from './destinations';
import type { Destination } from './destinations';
import { Dialog } from './UI';
import { useData } from '../research/common';
export type StudioWorkspace = 'explore' | 'atlas' | 'laboratory' | 'journal' | 'research';
interface Item {
  id: string;
  title: string;
  detail: string;
  group: string;
  icon: typeof Compass;
  run: () => void;
}
export function CommandPalette({
  onClose,
  onSelect,
  onNavigate,
  onAction,
}: {
  onClose: () => void;
  onSelect: (d: Destination) => void;
  onNavigate: (w: StudioWorkspace) => void;
  onAction: (id: string) => void;
}) {
  const listId = useId();
  const [query, setQuery] = useState(''),
    [selected, setSelected] = useState(0);
  const list = useRef<HTMLDivElement>(null);
  const { data } = useData<{ files: { path: string; title: string; kind: string; url: string }[] }>(
    'catalog.json',
  );
  const items = useMemo(() => {
    const actions: Item[] = [
      {
        id: 'explore',
        title: 'Explore',
        detail: 'Return to the live canvas',
        group: 'Workspaces',
        icon: Compass,
        run: () => onNavigate('explore'),
      },
      {
        id: 'atlas',
        title: 'Atlas',
        detail: 'Destinations, guided journeys, and exact mathematics',
        group: 'Workspaces',
        icon: Network,
        run: () => onNavigate('atlas'),
      },
      {
        id: 'laboratory',
        title: 'Laboratory',
        detail: 'Discover, analyze, and compare',
        group: 'Workspaces',
        icon: FlaskConical,
        run: () => onNavigate('laboratory'),
      },
      {
        id: 'journal',
        title: 'Journal',
        detail: 'Saved views, branches, and experiments',
        group: 'Workspaces',
        icon: Bookmark,
        run: () => onNavigate('journal'),
      },
      {
        id: 'research',
        title: 'Research',
        detail: 'Proof ledger and original sources',
        group: 'Workspaces',
        icon: BookOpen,
        run: () => onNavigate('research'),
      },
      {
        id: 'save',
        title: 'Save this view',
        detail: 'Keep the exact state in your journal',
        group: 'Actions',
        icon: Bookmark,
        run: () => onAction('save'),
      },
      {
        id: 'export',
        title: 'Export image or session',
        detail: 'Render a high-resolution image and portable state',
        group: 'Actions',
        icon: Image,
        run: () => onAction('export'),
      },
      {
        id: 'guide',
        title: 'Open field guide',
        detail: 'Understand what you are seeing',
        group: 'Actions',
        icon: BookOpen,
        run: () => onAction('guide'),
      },
      {
        id: 'help',
        title: 'Keyboard shortcuts',
        detail: 'Move around without leaving the canvas',
        group: 'Actions',
        icon: Keyboard,
        run: () => onAction('help'),
      },
      {
        id: 'tour',
        title: 'Start the first-light journey',
        detail: 'Five stops through the world of fractals',
        group: 'Actions',
        icon: Route,
        run: () => onAction('tour'),
      },
      {
        id: 'inspector',
        title: 'Toggle inspector',
        detail: 'Model, material, and camera controls',
        group: 'Actions',
        icon: Settings2,
        run: () => onAction('inspector'),
      },
    ];
    const places: Item[] = DESTINATIONS.map((d) => ({
      id: d.id,
      title: d.title,
      detail: d.subtitle,
      group: 'Destinations',
      icon: Compass,
      run: () => onSelect(d),
    }));
    const q = query.trim().toLowerCase();
    const filter = (i: Item) =>
      q.split(/\s+/).every((t) => `${i.title} ${i.detail}`.toLowerCase().includes(t));
    const source: Item[] =
      q.length < 3
        ? []
        : (data?.files ?? [])
            .filter((f) =>
              q.split(/\s+/).every((t) => `${f.title} ${f.path}`.toLowerCase().includes(t)),
            )
            .slice(0, 10)
            .map((f) => ({
              id: f.path,
              title: f.title || f.path.split('/').pop()!,
              detail: f.path,
              group: 'Research sources',
              icon: BookOpen,
              run: () => {
                window.open(f.url, '_blank', 'noopener,noreferrer');
                onClose();
              },
            }));
    return [...actions.filter(filter), ...places.filter(filter), ...source].slice(0, 35);
  }, [query, data, onNavigate, onSelect, onAction, onClose]);
  useEffect(() => setSelected(0), [query]);
  useEffect(() => {
    list.current
      ?.querySelector<HTMLElement>(`[data-selected="true"]`)
      ?.scrollIntoView({ block: 'nearest' });
  }, [selected]);
  const run = (item: Item) => {
    onClose();
    item.run();
  };
  return (
    <Dialog
      title="Where would you like to go?"
      kicker="QUICK NAVIGATION"
      onClose={onClose}
      className="ob-command"
    >
      <div className="ob-command-input">
        <Search size={20} />
        <input
          autoFocus
          role="combobox"
          aria-expanded="true"
          aria-autocomplete="list"
          aria-controls={listId}
          aria-activedescendant={items[selected] ? `${listId}-${selected}` : undefined}
          aria-label="Search commands, destinations, and research"
          placeholder="Search places, tools, or research…"
          value={query}
          onChange={(e) => setQuery(e.target.value)}
          onKeyDown={(e) => {
            if (e.key === 'ArrowDown') {
              e.preventDefault();
              setSelected((s) => Math.min(items.length - 1, s + 1));
            }
            if (e.key === 'ArrowUp') {
              e.preventDefault();
              setSelected((s) => Math.max(0, s - 1));
            }
            if (e.key === 'Enter' && items[selected]) {
              e.preventDefault();
              run(items[selected]);
            }
          }}
        />
        <kbd>esc</kbd>
      </div>
      <div
        className="ob-command-results"
        ref={list}
        id={listId}
        role="listbox"
        aria-label="Search results"
      >
        {items.map((item, i) => (
          <div key={`${item.group}:${item.id}`}>
            {(i === 0 || items[i - 1].group !== item.group) && <h3>{item.group}</h3>}
            <button
              id={`${listId}-${i}`}
              role="option"
              aria-selected={selected === i}
              data-selected={selected === i}
              className={selected === i ? 'selected' : ''}
              onMouseMove={() => setSelected(i)}
              onClick={() => run(item)}
            >
              <item.icon size={18} />
              <span>
                <strong>{item.title}</strong>
                <small>{item.detail}</small>
              </span>
              <ArrowUpRight size={15} />
            </button>
          </div>
        ))}
        {!items.length && (
          <p className="ob-command-empty">No matches. Try “Julia”, “period”, or “export”.</p>
        )}
      </div>
      <footer>
        <span>
          <kbd>↑</kbd>
          <kbd>↓</kbd> navigate
        </span>
        <span>
          <kbd>↵</kbd> open
        </span>
        <span>Places, instruments, and source documents</span>
      </footer>
    </Dialog>
  );
}
