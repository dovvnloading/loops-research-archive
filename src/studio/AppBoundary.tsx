import { Component } from 'react';
import type { ReactNode } from 'react';
import { ArrowUpRight, RotateCcw } from 'lucide-react';
import { Logo } from './UI';

/** Keep a recoverable application error from hiding the user's locally saved work. */
export class AppBoundary extends Component<{ children: ReactNode }, { error: string | null }> {
  state: { error: string | null } = { error: null };
  static getDerivedStateFromError(error: unknown) {
    return {
      error: error instanceof Error ? error.message : 'An unexpected application error occurred.',
    };
  }
  render() {
    if (!this.state.error) return this.props.children;
    return (
      <main className="ob-app-recovery">
        <Logo />
        <span className="ob-eyebrow">LOOPS / RECOVER YOUR WORKSPACE</span>
        <h1>A moment to reorient.</h1>
        <p>
          The workspace could not complete its last operation. Reloading leaves your saved journal
          records in place.
        </p>
        <details>
          <summary>Technical detail</summary>
          <code>{this.state.error}</code>
        </details>
        <div>
          <button className="ob-button" onClick={() => location.reload()}>
            <RotateCcw size={16} />
            Reload workspace
          </button>
          <a
            className="ob-button ob-subtle"
            href="https://github.com/dovvnloading/loops-research-archive"
            target="_blank"
            rel="noreferrer"
          >
            Open the source archive
            <ArrowUpRight size={16} />
          </a>
        </div>
      </main>
    );
  }
}
