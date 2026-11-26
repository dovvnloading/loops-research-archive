import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import '@fontsource-variable/libre-franklin/wght.css';
import '@fontsource-variable/stix-two-text/wght.css';
import '@fontsource-variable/stix-two-text/wght-italic.css';
import '@fontsource-variable/inconsolata/standard.css';
import './design/tokens.css';
import './design/base.css';
import App from './App';
import { AppBoundary } from './studio/AppBoundary';

createRoot(document.getElementById('root')!).render(
  <StrictMode>
    <AppBoundary>
      <App />
    </AppBoundary>
  </StrictMode>,
);
