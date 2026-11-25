import type { EngineState } from '../types';
import { Archive } from './Archive';
import { Atlas } from './Atlas';
import { Dynamics } from './Dynamics';
import { Lab } from './Lab';
import { SourceRevisionContext, useData } from './common';
import './research.css';

export interface ResearchWorkspaceProps {
  workspace: 'dynamics' | 'atlas' | 'lab' | 'archive';
  state: EngineState;
  onChange: (patch: Partial<EngineState>) => void;
  onExplore: () => void;
}

export function ResearchWorkspace({ workspace, state, onChange, onExplore }: ResearchWorkspaceProps) {
  const { data } = useData<{ source_commit: string }>('manifest.json');
  return <SourceRevisionContext.Provider value={data?.source_commit ?? 'main'}><div className="research-workspace" key={workspace}>
    {workspace === 'dynamics' && <Dynamics state={state} onChange={onChange} onExplore={onExplore} />}
    {workspace === 'atlas' && <Atlas onChange={onChange} onExplore={onExplore} />}
    {workspace === 'lab' && <Lab state={state} onChange={onChange} onExplore={onExplore} />}
    {workspace === 'archive' && <Archive />}
  </div></SourceRevisionContext.Provider>;
}
