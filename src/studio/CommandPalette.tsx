import { useEffect, useId, useMemo, useRef, useState } from 'react';
import { Search } from 'lucide-react';
import { DESTINATIONS } from './destinations';
import type { Destination } from './destinations';
import { Dialog, MOD } from './UI';
import { useData } from '../research/common';
export type StudioWorkspace = 'explore' | 'atlas' | 'laboratory' | 'journal' | 'research';
interface Item {
  id: string;
  title: string;
  detail: string;
  group: string;
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
        detail: 'The live renderer',
        group: 'Workspaces',
        run: () => onNavigate('explore'),
      },
      {
        id: 'atlas',
        title: 'Atlas',
        detail: 'Destinations, tours and the mathematical atlas',
        group: 'Workspaces',
        run: () => onNavigate('atlas'),
      },
      {
        id: 'laboratory',
        title: 'Laboratory',
        detail: 'Surveys, orbit analysis, window comparison',
        group: 'Workspaces',
        run: () => onNavigate('laboratory'),
      },
      {
        id: 'journal',
        title: 'Journal',
        detail: 'Saved views, branches and experiments',
        group: 'Workspaces',
        run: () => onNavigate('journal'),
      },
      {
        id: 'research',
        title: 'Research',
        detail: 'Obligation ledger and sources',
        group: 'Workspaces',
        run: () => onNavigate('research'),
      },
      {
        id: 'save',
        title: 'Save this view',
        detail: `Journal entry with exact coordinates · ${MOD} S`,
        group: 'Actions',
        run: () => onAction('save'),
      },
      {
        id: 'export',
        title: 'Export image or session',
        detail: 'PNG, session file or share link',
        group: 'Actions',
        run: () => onAction('export'),
      },
      {
        id: 'guide',
        title: 'Field guide',
        detail: 'What the current view shows · G',
        group: 'Actions',
        run: () => onAction('guide'),
      },
      {
        id: 'help',
        title: 'Keyboard shortcuts',
        detail: 'Controls for the renderer · ?',
        group: 'Actions',
        run: () => onAction('help'),
      },
      {
        id: 'tour',
        title: 'Start the First light tour',
        detail: 'Guided tour, 5 stops',
        group: 'Actions',
        run: () => onAction('tour'),
      },
      {
        id: 'inspector',
        title: 'Toggle inspector',
        detail: 'Model, material and view controls',
        group: 'Actions',
        run: () => onAction('inspector'),
      },
    ];
    const places: Item[] = DESTINATIONS.map((d) => ({
      id: d.id,
      title: d.title,
      detail: d.subtitle,
      group: 'Destinations',
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
    <Dialog title="Search" onClose={onClose} className="ob-command">
      <div className="ob-command-input">
        <Search size={16} />
        <input
          autoFocus
          role="combobox"
          aria-expanded="true"
          aria-autocomplete="list"
          aria-controls={listId}
          aria-activedescendant={items[selected] ? `${listId}-${selected}` : undefined}
          aria-label="Search commands, destinations, and research"
          placeholder="Destination, command or source file"
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
              <strong>{item.title}</strong>
              <small>{item.detail}</small>
            </button>
          </div>
        ))}
        {!items.length && (
          <p className="ob-command-empty">
            Nothing matches. Source files are searched from the third character.
          </p>
        )}
      </div>
      <footer>
        <span>↑ ↓ to move</span>
        <span>Enter to open</span>
        <span>Esc to close</span>
      </footer>
    </Dialog>
  );
}
