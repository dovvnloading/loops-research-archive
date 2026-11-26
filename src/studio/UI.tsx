import { useEffect, useId, useRef, useState } from 'react';
import type { ReactNode, CSSProperties } from 'react';
import { X, ChevronDown } from 'lucide-react';

export function Logo() {
  return (
    <svg viewBox="0 0 40 40" fill="none" aria-hidden="true">
      <g stroke="currentColor" strokeWidth="1.25">
        <ellipse cx="20" cy="20" rx="16" ry="7.5" />
        <ellipse cx="20" cy="20" rx="16" ry="7.5" transform="rotate(60 20 20)" />
        <ellipse cx="20" cy="20" rx="16" ry="7.5" transform="rotate(120 20 20)" />
        <circle cx="20" cy="20" r="3" />
      </g>
    </svg>
  );
}
export function IconButton({
  label,
  children,
  onClick,
  active = false,
  disabled = false,
  className = '',
}: {
  label: string;
  children: ReactNode;
  onClick: () => void;
  active?: boolean;
  disabled?: boolean;
  className?: string;
}) {
  return (
    <button
      className={`ob-icon ${active ? 'is-active' : ''} ${className}`}
      aria-label={label}
      title={label}
      aria-pressed={active ? true : undefined}
      disabled={disabled}
      onClick={onClick}
    >
      {children}
    </button>
  );
}
export function Dialog({
  title,
  kicker,
  onClose,
  children,
  className = '',
}: {
  title: string;
  kicker?: string;
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
        <div>
          {kicker && <span className="ob-eyebrow">{kicker}</span>}
          <h2 id={id}>{title}</h2>
        </div>
        <IconButton label="Close dialog" onClick={onClose}>
          <X size={19} />
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
export function Loading({ label = 'Opening the workspace…' }: { label?: string }) {
  return (
    <div className="ob-loading" role="status">
      <Logo />
      <span>{label}</span>
    </div>
  );
}
