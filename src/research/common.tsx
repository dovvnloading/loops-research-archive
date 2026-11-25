import { createContext, useContext, useEffect, useState } from 'react';
import { ArrowUpRight, Download, RotateCcw } from 'lucide-react';
import type { ReactNode } from 'react';

export const REPO = 'https://github.com/dovvnloading/loops-research-archive';
export const SOURCE = `${REPO}/blob/main/`;
export const SourceRevisionContext = createContext('main');
const cache = new Map<string, unknown>();

export function useData<T>(file: string) {
  const [data, setData] = useState<T | null>(() => (cache.get(file) as T) ?? null);
  const [error, setError] = useState('');
  const [attempt, setAttempt] = useState(0);
  useEffect(() => {
    if (cache.has(file)) { setData(cache.get(file) as T); return; }
    const controller = new AbortController();
    setError('');
    fetch(new URL(`data/${file}`, document.baseURI), { signal: controller.signal })
      .then(response => { if (!response.ok) throw new Error(`The dataset could not be loaded (${response.status}).`); return response.json(); })
      .then(value => { cache.set(file, value); setData(value as T); })
      .catch((cause: Error) => { if (cause.name !== 'AbortError') setError(cause.message); });
    return () => controller.abort();
  }, [file, attempt]);
  return { data, error, retry: () => setAttempt(n => n + 1) };
}

export function DataBoundary({ loading, error, retry, children }: { loading: boolean; error: string; retry: () => void; children: ReactNode }) {
  if (error) return <div className="research-empty" role="alert"><p>{error}</p><button className="research-button" onClick={retry}><RotateCcw size={14} /> Retry dataset</button></div>;
  if (loading) return <div className="research-loading" role="status"><span /> Loading research data…</div>;
  return <>{children}</>;
}

export function ResearchHeading({ index, title, description, children }: { index: string; title: string; description: string; children?: ReactNode }) {
  return <header className="research-heading"><div><div className="research-eyebrow">LOOPS RESEARCH / {index}</div><h1>{title}</h1><p>{description}</p></div>{children && <div className="research-heading-actions">{children}</div>}</header>;
}

export function SourceLink({ path, label = 'View source', href }: { path?: string; label?: string; href?: string }) {
  const revision = useContext(SourceRevisionContext);
  return <a className="research-source" href={href ?? `${REPO}/blob/${revision}/${path}`} target="_blank" rel="noreferrer">{label}<ArrowUpRight size={13} /></a>;
}

export function ScopeNote({ children }: { children: ReactNode }) {
  return <div className="scope-note"><span className="scope-dot" /><p>{children}</p></div>;
}

export function Metric({ label, value, detail }: { label: string; value: ReactNode; detail?: string }) {
  return <div className="research-metric"><span>{label}</span><strong>{value}</strong>{detail && <small>{detail}</small>}</div>;
}

export function exportJSON(data: unknown, filename: string) {
  const url = URL.createObjectURL(new Blob([JSON.stringify(data, null, 2)], { type: 'application/json' }));
  const anchor = document.createElement('a'); anchor.href = url; anchor.download = filename; anchor.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

export function DownloadButton({ data, name = 'loops-data.json', label = 'Export data' }: { data: unknown; name?: string; label?: string }) {
  return <button className="research-button secondary" onClick={() => exportJSON(data, name)}><Download size={14} />{label}</button>;
}

export function formatComplex(re: number, im: number, digits = 6) {
  return `${re.toFixed(digits)} ${im < 0 ? '−' : '+'} ${Math.abs(im).toFixed(digits)}i`;
}

export function localAsset(path: string) { return new URL(path, document.baseURI).href; }
