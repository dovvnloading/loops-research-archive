import { useEffect, useId, useRef, useState } from 'react';
import type { ReactNode, CSSProperties } from 'react';
import { X, ChevronDown } from 'lucide-react';
import type { EngineState } from '../types';

/** The two loops of the name: used alone as the mark, and as the OO of the wordmark. */
export function Logo() {
  return (
    <svg className="ob-rings" viewBox="0 0 31 20" fill="none" aria-hidden="true">
      <g stroke="currentColor" strokeWidth="3.9">
        <circle cx="10" cy="10" r="8" />
        <circle cx="21" cy="10" r="8" />
      </g>
    </svg>
  );
}
export function Wordmark() {
  return (
    <span className="ob-wordmark" aria-hidden="true">
      L<Logo />
      PS
    </span>
  );
}
/** ⌘ on Apple keyboards, Ctrl elsewhere. */
export const MOD =
  typeof navigator !== 'undefined' && /Mac|iPhone|iPad/.test(navigator.platform) ? '⌘' : 'Ctrl';

/** The iterated map of a scene, set as mathematics rather than as code. */
export function Formula({ scene, power = 2 }: { scene: EngineState['scene']; power?: number }) {
  const n = power.toFixed(power % 1 === 0 ? 0 : 2);
  return (
    <span className="math">
      {scene === 'mandelbulb' ? (
        <>
          <i>z</i> ↦ <i>z</i>
          <sup>{n}</sup> + <i>c</i>
        </>
      ) : scene === 'mandelbox' ? (
        <>
          <i>z</i> ↦ −{n} · fold(<i>z</i>) + <i>c</i>
        </>
      ) : scene === 'quaternion' ? (
        <>
          <i>q</i> ↦ <i>q</i>² + <i>c</i>, <i>q</i> ∈ ℍ
        </>
      ) : scene === 'landscape' ? (
        <>
          <i>h</i>(<i>c</i>) = log escape time
        </>
      ) : (
        <>
          <i>z</i> ↦ <i>z</i>² + <i>c</i>
        </>
      )}
    </span>
  );
}
export function IconButton({
  label,
  children,
  onClick,
  active = false,
  disabled = false,
  expanded,
  className = '',
}: {
  label: string;
  children: ReactNode;
  onClick: () => void;
  active?: boolean;
  disabled?: boolean;
  expanded?: boolean;
  className?: string;
}) {
  return (
    <button
      className={`ob-icon ${active ? 'is-active' : ''} ${className}`}
      aria-label={label}
      title={label}
      aria-pressed={active ? true : undefined}
      aria-expanded={expanded}
      disabled={disabled}
      onClick={onClick}
    >
      {children}
    </button>
  );
}
export function Dialog({
  title,
  onClose,
  children,
  className = '',
}: {
  title: string;
  onClose: () => void;
  children: ReactNode;
  className?: string;
}) {
  const ref = useRef<HTMLDialogElement>(null);
  const id = useId();
  useEffect(() => {
    const dialog = ref.current;
    const prev = document.activeElement as HTMLElement | null;
    dialog?.showModal();
    return () => {
      dialog?.close();
      prev?.focus();
    };
  }, []);
  return (
    <dialog
      ref={ref}
      className={`ob-dialog ${className}`}
      aria-labelledby={id}
      onCancel={(e) => {
        e.preventDefault();
        onClose();
      }}
      onClick={(e) => {
        if (e.target === ref.current) onClose();
      }}
    >
      <header>
        <h2 id={id}>{title}</h2>
        <IconButton label="Close dialog" onClick={onClose}>
          <X size={16} />
        </IconButton>
      </header>
      {children}
    </dialog>
  );
}
export function Range({
  label,
  value,
  min,
  max,
  step = 1,
  onChange,
  format,
  description,
}: {
  label: string;
  value: number;
  min: number;
  max: number;
  step?: number;
  onChange: (value: number) => void;
  format?: (n: number) => string;
  description?: string;
}) {
  const id = useId();
  return (
    <div className="ob-range">
      <div>
        <label htmlFor={id}>{label}</label>
        <output htmlFor={id}>{format ? format(value) : value}</output>
      </div>
      <input
        id={id}
        type="range"
        min={min}
        max={max}
        step={step}
        value={value}
        onChange={(e) => onChange(Number(e.target.value))}
        style={{ '--value': `${(100 * (value - min)) / (max - min)}%` } as CSSProperties}
      />
      {description && <small>{description}</small>}
    </div>
  );
}
export function Switch({
  label,
  checked,
  onChange,
  description,
}: {
  label: string;
  checked: boolean;
  onChange: () => void;
  description?: string;
}) {
  return (
    <button className="ob-switch-row" role="switch" aria-checked={checked} onClick={onChange}>
      <span>
        {label}
        {description && <small>{description}</small>}
      </span>
      <span className={`ob-switch ${checked ? 'on' : ''}`}>
        <i />
      </span>
    </button>
  );
}
export function NumberInput({
  label,
  value,
  onChange,
  min,
  max,
  step = 'any',
}: {
  label: string;
  value: number;
  onChange: (n: number) => void;
  min?: number;
  max?: number;
  step?: number | 'any';
}) {
  const [draft, setDraft] = useState(String(value)),
    [editing, setEditing] = useState(false);
  useEffect(() => {
    if (!editing) setDraft(String(value));
  }, [value, editing]);
  const commit = () => {
    const n = Number(draft);
    if (draft.trim() && Number.isFinite(n))
      onChange(Math.max(min ?? -Infinity, Math.min(max ?? Infinity, n)));
    else setDraft(String(value));
    setEditing(false);
  };
  return (
    <label className="ob-field">
      <span>{label}</span>
      <input
        type="number"
        step={step}
        min={min}
        max={max}
        value={draft}
        onFocus={() => setEditing(true)}
        onChange={(e) => setDraft(e.target.value)}
        onBlur={commit}
        onKeyDown={(e) => {
          if (e.key === 'Enter') e.currentTarget.blur();
          if (e.key === 'Escape') {
            setDraft(String(value));
            setEditing(false);
            e.stopPropagation();
          }
        }}
      />
    </label>
  );
}
export function Disclosure({
  title,
  children,
  open = false,
}: {
  title: string;
  children: ReactNode;
  open?: boolean;
}) {
  return (
    <details className="ob-disclosure" open={open}>
      <summary>
        {title}
        <ChevronDown size={14} />
      </summary>
      <div>{children}</div>
    </details>
  );
}
export function Loading({ label = 'Loading…' }: { label?: string }) {
  return (
    <div className="ob-loading" role="status">
      <Logo />
      <span>{label}</span>
    </div>
  );
}
