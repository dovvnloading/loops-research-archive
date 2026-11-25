# LOOPS web application — development and deployment

The public repository site is [dovvnloading.github.io/loops-research-archive](https://dovvnloading.github.io/loops-research-archive/). The application is built with React, TypeScript and Vite and uses a custom WebGL2 renderer. It publishes the **`dist/` build output**, including the research archive, as a static site. No application server, database, account or API key is required.

## Develop and verify

Use Node.js 24 and Python 3.12 or later:

```sh
npm ci
python3 scripts/prepare_data.py
npm run dev
```

To build exactly the artifact intended for publication:

```sh
npm run build
npm test
python3 code/verify_site_integrity.py
npm run preview
```

The build first prepares lossless research datasets, type-checks the application, bundles the local JavaScript and CSS, then copies the scholarly archive. The integrity verifier checks the built artifact, data checksums, unchanged ledger fields, unavailable-source disclosures, lossless dyadic brackets, preserved file hashes and a local HTTP smoke test. Renderer interaction and GPU output still require browser testing; passing these checks is not a rendering or mathematical-proof claim.

Vite uses relative asset URLs (`base: './'`) so the same build works at the repository subpath or a standalone static origin. The application uses hash/session state rather than server routes. `classic.html`, `dossier.html` and `template.html` redirect to `./#archive`.

## GitHub Pages

The workflow [pages.yml](../.github/workflows/pages.yml) builds and verifies every `main` push, uploads `dist/`, then deploys it with the official Pages actions. Deployment uses the standard `github-pages` environment and `pages: write` / `id-token: write` permissions.

For this workflow to publish, the repository's **Settings → Pages → Build and deployment → Source** must be **GitHub Actions**. This replaces the former `main` / `root` branch-publishing configuration. The workflow deliberately does not attempt administrator-only Pages enablement. A successfully built pull request is reviewable code; it is not evidence of a successful public deployment.

After deployment, [pages-live-smoke.yml](../.github/workflows/pages-live-smoke.yml) checks the real public URL. It also runs daily and can be dispatched manually. The same check can target another static deployment:

```sh
SITE_URL=https://example.com/loops/ python3 code/verify_deployed_site.py
```

References: [GitHub's custom-workflow documentation](https://docs.github.com/en/pages/getting-started-with-github-pages/using-custom-workflows-with-github-pages), [deploy-pages action](https://github.com/actions/deploy-pages).

## Data and provenance

`scripts/prepare_data.py` reads the original `ledger.json` and selected `results/` JSON certificates with Python's arbitrary-size integers. Integers outside JavaScript's safe range are serialized as decimal strings. The original files are never rewritten. Browser calculations use `BigInt` for rational angles; shader and orbit drawing coordinates are numerical approximations.

`public/data/manifest.json` records original input hashes, generated dataset hashes, scopes, and the last first-parent commit that touched the ledger, results, research, papers or formalization sources. Application-only commits do not move this research revision. Evidence URLs are pinned to that revision. The source ledger's 465 obligations and 46 later updates retain their statements, dependencies, hypotheses and statuses. A `proved` label may refer to a written or conditional result; it does not automatically mean Lean kernel verification.

At the initial application migration, **26 ledger entries referenced 7 Markdown files that were already absent from the repository**. These remain explicit unresolved evidence records in the manifest and interface. The build never manufactures replacement documents or silently substitutes a similarly named certificate. Evidence anchors are retained from the original ledger; path resolution is not an audit of the mathematical argument or every heading anchor.

`data/catalog.json` indexes the preserved scholarly files, their kinds, sizes and SHA-256 checksums. Repository links in the catalog point to the current `main` branch; packaged local files are checked against the catalog. Source certificates and ledger evidence have separate immutable revision links.

## Preserved and replaced

The new application replaces the old `site-v2.js`, `site-v2.css`, `support.js` and `site.css` presentation layer. These runtimes are excluded from the published artifact. `ledger.js` remains downloadable as an audit mirror required by existing research tooling; the app does not load it as a runtime. The previous frontend remains available in Git history.

The build preserves root Lean files, research Markdown, the original ledger, manuscript PDFs, `papers/`, `docs/`, `research/`, `results/`, `code/`, `formalization/` and `figs/` at their existing relative paths. Existing research validation workflows are separate from the website build and deployment.

## Recovery

- **A raw source page appears:** Pages is probably still publishing the repository root. Select GitHub Actions as the source and run the deployment workflow.
- **Blank application:** Check the module and CSS requests shown in the browser console; all assets should come from the same origin and project subpath. Run the integrity verifier on `dist/`.
- **No WebGL2:** Use the accessible research workspaces and supported fallback shown by the application. A device-specific shader failure must not be mistaken for a failed certificate.
- **A source link is unavailable:** Check its explicit evidence-resolution state and the source revision. Some unavailable references predate this application.
- **Archive assets missing:** Upload the complete `dist/` directory produced by the build, including the copied archive and `data/`.
- **Rollback:** Revert the frontend commits and publishing configuration together, or deploy a previously verified application commit. Mathematical source files do not need to be reverted for a presentation-only rollback.

**Mathematical status:** MLC remains open. Visualizations, numerical orbits, rational-angle experiments and finite certificates do not establish the global conjecture.
