import { useCallback, useEffect, useRef, useState } from 'react';
import type { JournalPayload } from '../journal/types';

/** Collapse continuous gestures into an undoable view, retaining the original decimal strings. */
export function useViewHistory(payload: JournalPayload, restore: (v: JournalPayload) => void) {
  const history = useRef<JournalPayload[]>([structuredClone(payload)]),
    index = useRef(0),
    timer = useRef<ReturnType<typeof setTimeout> | undefined>(undefined);
  const restoring = useRef(false),
    current = useRef(payload),
    callback = useRef(restore);
  current.current = payload;
  callback.current = restore;
  const [version, setVersion] = useState(0);
  const push = useCallback(() => {
    const next = current.current;
    if (JSON.stringify(next) === JSON.stringify(history.current[index.current])) return;
    history.current = history.current.slice(0, index.current + 1);
    history.current.push(structuredClone(next));
    if (history.current.length > 80) history.current.shift();
    index.current = history.current.length - 1;
    setVersion((n) => n + 1);
  }, []);
  useEffect(() => {
    if (restoring.current) {
      restoring.current = false;
      return;
    }
    clearTimeout(timer.current);
    timer.current = setTimeout(push, 450);
    return () => clearTimeout(timer.current);
  }, [payload.engine, payload.exact, push]);
  const undo = useCallback(() => {
    clearTimeout(timer.current);
    push();
    if (index.current > 0) {
      index.current--;
      restoring.current = true;
      callback.current(structuredClone(history.current[index.current]));
      setVersion((n) => n + 1);
    }
  }, [push]);
  const redo = useCallback(() => {
    clearTimeout(timer.current);
    if (index.current < history.current.length - 1) {
      index.current++;
      restoring.current = true;
      callback.current(structuredClone(history.current[index.current]));
      setVersion((n) => n + 1);
    }
  }, []);
  return {
    undo,
    redo,
    canUndo:
      index.current > 0 ||
      JSON.stringify(current.current) !== JSON.stringify(history.current[index.current]),
    canRedo: index.current < history.current.length - 1,
    version,
  };
}
