import { Component } from 'react';
import type { ReactNode } from 'react';
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
        <h1>LOOPS stopped unexpectedly</h1>
        <p>
          The last operation did not complete. Reloading restarts the app; journal entries saved in
          this browser are not affected.
        </p>
        <details>
          <summary>Technical detail</summary>
          <code>{this.state.error}</code>
        </details>
        <div>
          <button className="ob-button ob-primary" onClick={() => location.reload()}>
            Reload
          </button>
          <a
            className="ob-button"
            href="https://github.com/dovvnloading/loops-research-archive"
            target="_blank"
            rel="noreferrer"
          >
            Source archive
          </a>
        </div>
      </main>
    );
  }
}
